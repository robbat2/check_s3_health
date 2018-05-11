#!/usr/bin/python
# This tool is designed for S3 status checking
# ideally driven by jenkins or nagios
#
# Authors:
# Robin Johnson <robin.johnson@dreamhost.com> (original author)
#
# License: This file is copyright under BSD-2 license:
# Copyright (c) 2016-2018, Robin H. Johnson <robbat2@orbis-terrarum.net>
# Copyright (c) 2016-2018, Dreamhost
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# 1. Redistributions of source code must retain the above copyright notice,
#    this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
#
# pylint: disable=fixme, line-too-long, missing-docstring, invalid-name
from __future__ import print_function
# Extra pieces, done before stock, as they might alter it
import boto
import boto.s3.connection
import boto.s3.key
import boto.s3.bucket
import requests.packages.urllib3.connection
# Stock PY
import argparse
import collections
import ConfigParser
import csv
import errno
import functools
import inspect
import itertools
import math
import os
import random
import re
import signal
import socket
import sys
import textwrap
import time
import traceback
import uuid

NANOSECOND = int(1e9)

# Set up nice calling format table
CALLING_FORMATS = {}
for name in [x for x in dir(boto.s3.connection) if x.endswith('CallingFormat')]:
    klass = getattr(boto.s3.connection, name)
    CALLING_FORMATS[name] = klass
    CALLING_FORMATS[name.replace('CallingFormat', '')] = klass
    CALLING_FORMATS[name.replace('CallingFormat', '').lower()] = klass
CALLING_FORMATS['path'] = boto.s3.connection.OrdinaryCallingFormat # special alias

class CustomHTTPConnection_requests(requests.packages.urllib3.connection.HTTPConnection):
    def __init__(self, *args, **kw):
        self.connect_host = kw.pop('connect_host', None)
        self.connect_port = kw.pop('connect_port', None)
        #print('Spawned %s forced via %s:%s' % (self.__class__, self.connect_host, self.connect_port))
        return super(CustomHTTPConnection_requests, self).__init__(*args, **kw)


class CustomHTTPSConnection_requests(requests.packages.urllib3.connection.HTTPSConnection):
    def __init__(self, *args, **kw):
        self.connect_host = kw.pop('connect_host', None)
        self.connect_port = kw.pop('connect_port', None)
        #print('Spawned %s forced via %s:%s' % (self.__class__, self.connect_host, self.connect_port))
        return super(CustomHTTPSConnection_requests, self).__init__(*args, **kw)

def PATCH_new_conn(self):
    """ Establish a socket connection and set nodelay settings on it

    :return: a new socket connection
    """
    # resolve hostname to an ip address; use your own
    # resolver here, as otherwise the system resolver will be used.
    (host, port) = (self.host, self.port)
    if self.connect_host is not None:
       host = self.connect_host
    if self.connect_port is not None:
       port = self.connect_port
    try:
        conn = socket.create_connection(
            (host, port),
            self.timeout,
            self.source_address,
        )
    except (AttributeError, TypeError) as e: # Python 2.6
        conn = socket.create_connection(
            (host, port),
            self.timeout,
        )
    return conn

CustomHTTPConnection_requests._new_conn = PATCH_new_conn
CustomHTTPSConnection_requests._new_conn = PATCH_new_conn

def HTTPConnectionFactoryFactory(connect_host, connect_port, ssl=False):
    cls = CustomHTTPConnection_requests
    if ssl:
      cls = CustomHTTPSConnection_requests
    def f(*args, **kw):
        #print('Factory: Prepared %s forced via %s:%s' % (cls, connect_host, connect_port))
        (kw['connect_host'], kw['connect_port']) = (connect_host, connect_port)
        return cls(*args, **kw)
    return f

class NagiosStatus(object):
    LEVELS = ['UNKNOWN', 'DEPENDENT', 'OK', 'WARNING', 'CRITICAL']
    EXIT_CODES = {'OK': 0, 'WARNING': 1, 'CRITICAL': 2, 'UNKNOWN': 3, 'DEPENDENT': 4}
    def __init__(self):
        self.status = []

    def set(self, new_status, new_message=None, new_longoutput=None):
        if new_status not in self.EXIT_CODES.keys():
            raise Exception("Invalid Nagios status")
        if new_longoutput is None:
            new_longoutput = new_message
        self.status = [(new_status, new_message, new_longoutput)]

    def add(self, new_status, new_message=None, new_longoutput=None):
        """ We start with an UNKNOWN state, and raise up the problem level as we know of more stuff wrong.
            If you call: obj.critical(msg); obj.warning(msg); the critical level should take priority, and the messages should be combined.
            """
        if new_longoutput is None:
            new_longoutput = new_message
        self.status.append((new_status, new_message, new_longoutput))

    def get_status(self):
        if len(self.status) == 0:
            return 'UNKNOWN'
        i = max([self.LEVELS.index(i[0]) for i in self.status])
        return self.LEVELS[i]

    def get_message(self):
        if len(self.status) == 0:
            return 'No message set'
        return ', '.join([i[1] for i in self.status if i[1] is not None])

    def get_longoutput(self):
        if len(self.status) == 0:
            return 'No long output set'
        return '\n'.join([i[2] for i in self.status if i[2] is not None])

    def get_exit_code(self):
        return self.EXIT_CODES[self.get_status()]

    def fire_exit(self, long_output=True):
        print("{status}: {message}".format(status=self.get_status(), message=self.get_message()))
        if long_output:
            print(self.get_longoutput())
        sys.exit(self.get_exit_code())

class TimeoutError(Exception):
    pass

class TimeoutClass(object): # pylint: disable=too-few-public-methods
    def __init__(self, seconds=1.0, error_message='Timeout'):
        self.seconds = seconds
        self.error_message = error_message

    def handle_timeout(self, signum, frame): # pylint: disable=unused-argument
        raise TimeoutError(self.error_message)

    def __enter__(self):
        signal.signal(signal.SIGALRM, self.handle_timeout)
        #signal.alarm(self.seconds)
        signal.setitimer(signal.ITIMER_REAL, self.seconds)

    def __exit__(self, exit_type, value, traceback): # pylint: disable=unused-argument, redefined-outer-name
        #signal.alarm(0)
        signal.setitimer(signal.ITIMER_REAL, 0)


if sys.version_info[0] > 2 or (sys.version_info[0] == 2 and sys.version_info[1] >= 7):
    def lru_cache(maxsize=100):
        '''Least-recently-used cache decorator.

        Arguments to the cached function must be hashable.
        Cache performance statistics stored in f.hits and f.misses.
        http://en.wikipedia.org/wiki/Cache_algorithms#Least_Recently_Used

        '''
        # http://code.activestate.com/recipes/498245-lru-and-lfu-cache-decorators/
        def decorating_function(user_function):
            cache = collections.OrderedDict()    # order: least recent to most recent

            @functools.wraps(user_function)
            def wrapper(*args, **kwds):
                key = args
                if kwds:
                    key += tuple(sorted(kwds.items()))
                try:
                    result = cache.pop(key)
                    wrapper.hits += 1
                except KeyError:
                    result = user_function(*args, **kwds)
                    wrapper.misses += 1
                    if len(cache) >= maxsize:
                        cache.popitem(0)    # purge least recently used cache entry
                cache[key] = result         # record recent use of this key
                return result
            wrapper.hits = wrapper.misses = 0
            return wrapper
        return decorating_function
else:
    class Counter(dict):
        'Mapping where default values are zero'
        def __missing__(self, key):
            return 0

    def lru_cache(maxsize=100):
        '''Least-recently-used cache decorator.

        Arguments to the cached function must be hashable.
        Cache performance statistics stored in f.hits and f.misses.
        Clear the cache with f.clear().
        http://en.wikipedia.org/wiki/Cache_algorithms#Least_Recently_Used

        '''
        maxqueue = maxsize * 10
        def decorating_function(user_function,
                len=len, iter=iter, tuple=tuple, sorted=sorted, KeyError=KeyError):
            cache = {}                  # mapping of args to results
            queue = collections.deque() # order that keys have been used
            refcount = Counter()        # times each key is in the queue
            sentinel = object()         # marker for looping around the queue
            kwd_mark = object()         # separate positional and keyword args

            # lookup optimizations (ugly but fast)
            queue_append, queue_popleft = queue.append, queue.popleft
            queue_appendleft, queue_pop = queue.appendleft, queue.pop

            @functools.wraps(user_function)
            def wrapper(*args, **kwds):
                # cache key records both positional and keyword args
                key = args
                if kwds:
                    key += (kwd_mark,) + tuple(sorted(kwds.items()))

                # record recent use of this key
                queue_append(key)
                refcount[key] += 1

                # get cache entry or compute if not found
                try:
                    result = cache[key]
                    wrapper.hits += 1
                except KeyError:
                    result = user_function(*args, **kwds)
                    cache[key] = result
                    wrapper.misses += 1

                    # purge least recently used cache entry
                    if len(cache) > maxsize:
                        key = queue_popleft()
                        refcount[key] -= 1
                        while refcount[key]:
                            key = queue_popleft()
                            refcount[key] -= 1
                        del cache[key], refcount[key]

                # periodically compact the queue by eliminating duplicate keys
                # while preserving order of most recent access
                if len(queue) > maxqueue:
                    refcount.clear()
                    queue_appendleft(sentinel)
                    for key in ifilterfalse(refcount.__contains__,
                                            iter(queue_pop, sentinel)):
                        queue_appendleft(key)
                        refcount[key] = 1


                return result

            def clear():
                cache.clear()
                queue.clear()
                refcount.clear()
                wrapper.hits = wrapper.misses = 0

            wrapper.hits = wrapper.misses = 0
            wrapper.clear = clear
            return wrapper
        return decorating_function


sequence = 0
def generate_name(template, **template_vars):
    global sequence # pylint: disable=global-statement
    t = float(time.time())
    template_vars['time'] = "%f" % (t, )
    numhex = 6
    hextime_format = "%08x-%0"+str(numhex)+"x" # use dash instead of period, so we do not go multi-subdomain
    template_vars['hextime'] = hextime_format % (int(t), (math.modf(t)[0]) * (2**(numhex*4)))
    template_vars['uuid1'] = str(uuid.uuid1())
    template_vars['uuid4'] = str(uuid.uuid4())
    template_vars['seq'] = "%04x" % (sequence, )
    template_vars['sequence'] = "%04x" % (sequence, )
    sequence += 1
    return template.format(**template_vars) # pylint: disable=star-args


def test_action(args, action, params):
    funcname = "action_%s" % (action.replace('.', '__'), )
    if funcname not in dir(Actions):
        raise RuntimeError("Unknown action: {action}".format(action=action))
    getattr(Actions, funcname)(args, params)
    args.nagios_object.add('OK', None, action+"=OK")
    if args.debug:
        print(action, 'OK', file=sys.stderr)


def testrunner(args, params=None): # pylint: disable=unused-argument
    conn = connect(vars(args))
    args.conn = conn
    loopcount = 1
    args.last_loop_iterations = loopcount
    for action, params in args.actions:
        # Special handling of loops
        if action == 'LOOP':
            loopcount = int(params)
            continue
        # Check if we are inside the loop now
        if loopcount != 1:
            (old_verbose, old_debug, old_stack_return) = (args.verbose, args.debug, args.stack_return)
            args.verbose = args.debug = old_stack_return = False
            args.last_loop_iterations = loopcount
            for i in xrange(loopcount): # pylint: disable=unused-variable
                test_action(args, action, params)
            (args.verbose, args.debug, args.stack_return) = (old_verbose, old_debug, old_stack_return)
            loopcount = 1
        else:
            test_action(args, action, params)

def connect(conf):
    mapping = dict(
        port='port',
        host='host',
        secure='is_secure',
        access_key='aws_access_key_id',
        secret_key='aws_secret_access_key',
        validate_certs='validate_certs',
        boto_debug='debug',
        )
    kwargs = dict((mapping[k], v) for (k, v) in conf.iteritems() if k in mapping)
    #process calling_format argument
    kwargs['calling_format'] = CALLING_FORMATS['ordinary']
    if conf.has_key('calling_format'):
        raw_calling_format = conf['calling_format']
        try:
            kwargs['calling_format'] = CALLING_FORMATS[raw_calling_format]
        except KeyError:
            raise RuntimeError(
                'calling_format unknown: %r' % raw_calling_format
                )
    kwargs['calling_format'] = (kwargs['calling_format'])()
    # TODO test vhost calling format
    connect_host = conf.get('connect_host', None)
    connect_port = conf.get('connect_port', conf.get('port', None))
    if connect_port is not None:
        connect_port = int(connect_port)
    init_ssl = (connect_port == 443)
    factory = HTTPConnectionFactoryFactory(connect_host, connect_port, ssl=init_ssl)
    kwargs['https_connection_factory'] = (factory, ()) # second tuple element is for error handling
    conn = boto.s3.connection.S3Connection(**kwargs) # pylint: disable=star-args
    return conn

@lru_cache(maxsize=20)
def cached_get_bucket(conn, bucket_name):
    bucket = conn.get_bucket(bucket_name)
    return bucket

cached_buckets = {}
def cached_get_all_buckets(conn):
    global cached_buckets # pylint: disable=global-statement
    if len(cached_buckets) == 0:
        _ = conn.get_all_buckets()
        cached_buckets = dict((b.name, b) for b in _)
    return cached_buckets.values()

def CORSRule_eq(a, b):
    return a.__dict__ == b.__dict__
boto.s3.cors.CORSRule.__eq__ = CORSRule_eq


class Actions(object):
    @staticmethod
    def action_conn__get_all_buckets(args, params=None): # pylint: disable=unused-argument
        """Connection: Get all buckets"""
        buckets = cached_get_all_buckets(args.conn)
        handle_result(args, buckets)

    @staticmethod
    def action_conn__create_bucket(args, params=None): # pylint: disable=unused-argument
        """Connection: Create a new bucket by name"""
        bucket = args.conn.create_bucket(args.bucket_name)
        handle_result(args, bucket)

    @staticmethod
    def action_conn__delete_bucket(args, params=None): # pylint: disable=unused-argument
        """Connection: Delete a bucket by name"""
        bucket = args.conn.delete_bucket(args.bucket_name)
        handle_result(args, bucket)

    @staticmethod
    def action_conn__get_bucket(args, params=None): # pylint: disable=unused-argument
        """Connect: GET bucket"""
        # Do not cache this one!
        bucket = args.conn.get_bucket(args.bucket_name)
        handle_result(args, bucket)

    @staticmethod
    def action_conn__head_bucket(args, params=None): # pylint: disable=unused-argument
        """Connection: HEAD bucket"""
        bucket = args.conn.head_bucket(args.bucket_name)
        handle_result(args, bucket)

    # --------
    @staticmethod
    def action_bucket__enable_versioning(args, params=None): # pylint: disable=unused-argument
        """Bucket: Enable versioning"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        bucket.configure_versioning(True)
        handle_result(args, None)
    @staticmethod
    def action_bucket__disable_versioning(args, params=None): # pylint: disable=unused-argument
        """Bucket: Disable versioning"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        bucket.configure_versioning(False)
        handle_result(args, None)
    @staticmethod
    def action_bucket__delete_all_keys(args, params=None): # pylint: disable=unused-argument
        """Bucket: Iterate all keys and use the bucket.delete_key call to delete all keys.
        Old versions are not touched"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        for key in bucket.list():
            bucket.delete_key(key.name)
        handle_result(args, None)
    @staticmethod
    def action_bucket__delete_all_versions(args, params=None): # pylint: disable=unused-argument
        """Bucket: Iterate all versions and use the bucket.delete_key call to delete all versions (of all keys)"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        for key in bucket.list_versions():
            bucket.delete_key(key.name, version_id=key.version_id)
        handle_result(args, None)
    @staticmethod
    def action_bucket__multidelete_all_keys(args, params=None): # pylint: disable=unused-argument
        """Bucket: Use the bucket.delete_keys call (Multi-Delete) to delete all keys, old versions are not touched
        Performs batch iteration of keys."""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        bucket.delete_keys(bucket.list(), quiet=True)
        handle_result(args, None)
    @staticmethod
    def action_bucket__multidelete_all_versions(args, params=None): # pylint: disable=unused-argument
        """Bucket: Use the bucket.delete_keys call (Multi-Delete) call to delete all versions of all keys
        Performs batch iteration of versions."""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        bucket.delete_keys(bucket.list_versions(), quiet=True)
        handle_result(args, None)

    @staticmethod
    def action_bucket__fill_bucket(args, params=None): # pylint: disable=unused-argument
        """Bucket: Ensure bucket contains at least N items."""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        num = int(params)
        count = 0
        # do not simply do len(bucket.list()) because that will build the
        # entire list!
        count = functools.reduce(lambda x, y: x+1, bucket.list()) # pylint: disable=unused-argument
        # Handle result
        handle_result(args, "Bucket %s had %d items, adding more for %d items total: START" % (args.bucket_name, count, num), override=True)
        for n in range(count, num): # pylint: disable=unused-variable
            Actions.action_SET__KEY(args, None)
            Actions.action_bucket__new_key(args, None)
        handle_result(args, "Bucket %s has %d items total: DONE" % (args.bucket_name, num), override=True)

    @staticmethod
    def action_bucket__ADD_cors(args, params=None): # pylint: disable=unused-argument
        """Bucket: Add CORS with a test rule.
        Does not modify other rules."""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        try:
            cors = bucket.get_cors()
        except boto.s3.connection.S3ResponseError as e:
            #print(e, dir(e), vars(e))
            if e.status != 404 or 'Not Found' not in e.error_code:
                raise e
            cors = boto.s3.cors.CORSConfiguration()

        if not any(rule.id.startswith(args.cors_test_rule_id_prefix) for rule in cors):
            cors.add_rule(id=args.cors_test_rule_id_prefix,
                          allowed_method=['GET'],
                          allowed_origin=['https://example.com'],
                          max_age_seconds=1,
                          allowed_header=['Host', 'Content-*'],
                          expose_header=['ETag'])
            bucket.set_cors(cors)
        handle_result(args, cors)

    @staticmethod
    def action_bucket__CLEAR_cors(args, params=None): # pylint: disable=unused-argument
        """Bucket: Clear the test CORS rule.
        Does not modify other rules.
        This may remove the CORSConfiguration if it was the last rule removed.
        """
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        try:
            cors = bucket.get_cors()
        except boto.s3.connection.S3ResponseError as e:
            if e.status != 404 or 'Not Found' not in e.error_code:
                raise e
            cors = boto.s3.cors.CORSConfiguration()

        for idx, rule in enumerate(cors):
            if rule.id.startswith(args.cors_test_rule_id_prefix):
                del cors[idx]
        if len(cors) > 1:
            bucket.set_cors(cors)
        else:
            bucket.delete_cors()
        handle_result(args, None)

    @staticmethod
    def action_bucket__DEDUPE_cors(args, params=None): # pylint: disable=unused-argument
        """Bucket: Deduplicate CORS rules that are exactly identical"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        try:
            cors = bucket.get_cors()
        except boto.s3.connection.S3ResponseError as e:
            if e.status != 404 or 'Not Found' not in e.error_code:
                raise e
            cors = boto.s3.cors.CORSConfiguration()

        rules = (key for key, _ in itertools.groupby(cors, key=lambda x: x.__dict__))
        cors = boto.s3.cors.CORSConfiguration(rules)
        if len(cors) > 1:
            bucket.set_cors(cors)
        else:
            bucket.delete_cors()
        handle_result(args, None)

    @staticmethod
    def action_bucket__TEST_cors(args, params=None): # pylint: disable=unused-argument
        """Bucket: Perform quick CORS test (add, dedupe, clear)"""
        Actions.action_bucket__ADD_cors(args, params)
        Actions.action_bucket__DEDUPE_cors(args, params)
        Actions.action_bucket__CLEAR_cors(args, params)
        handle_result(args, None)

    # --------
    @staticmethod
    def action_bucket__get_acl(args, params=None): # pylint: disable=unused-argument
        """Bucket: Get ACL"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        if params is None:
            params = {}
        key = bucket.get_acl()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_all_keys(args, params=None): # pylint: disable=unused-argument
        """Bucket: Get all keys"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        if params is None or params == '':
            params = {}
        key = bucket.get_all_keys(**params) # pylint: disable=star-args
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_all_multipart_uploads(args, params=None): # pylint: disable=unused-argument
        """Bucket: Get all multipart uploads"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_all_multipart_uploads()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_all_versions(args, params=None): # pylint: disable=unused-argument
        """Bucket: Get all versions"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_all_versions()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_cors(args, params=None): # pylint: disable=unused-argument
        """Bucket: Get CORS (as object)"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_cors()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_cors_xml(args, params=None): # pylint: disable=unused-argument
        """Bucket: Get CORS (as XML)"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_cors_xml()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_key(args, params=None): # pylint: disable=unused-argument
        """Bucket: Get key by name"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_key(args.key_name)
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_lifecycle_config(args, params=None): # pylint: disable=unused-argument
        """Bucket: Get lifecycle configuration"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_lifecycle_config()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_location(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_location()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_logging_status(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_logging_status()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_policy(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_policy()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_request_payment(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_request_payment()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_tags(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_tags()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_versioning_status(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_versioning_status()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_website_configuration(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_website_configuration()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_website_configuration_obj(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_website_configuration_obj()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_website_configuration_with_xml(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_website_configuration_with_xml()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_website_configuration_xml(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_website_configuration_xml()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_website_endpoint(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_website_endpoint()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_xml_tags(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_xml_tags()
        handle_result(args, key)

    @staticmethod
    def action_bucket__get_xml_acl(args, params=None): # pylint: disable=unused-argument
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_xml_acl(args.key_name)
        handle_result(args, key)

    @staticmethod
    def action_bucket__delete(args, params=None): # pylint: disable=unused-argument
        """Bucket: Delete bucket"""
        global cached_buckets # pylint: disable=global-statement
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.delete()
        if args.bucket_name in cached_buckets:
            del cached_buckets[args.bucket_name]
        handle_result(args, key)

    @staticmethod
    def action_bucket__set_canned_acl(args, params=None): # pylint: disable=unused-argument
        """Set ACL of bucket from canned string."""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        filestr = 'private'
        if isinstance(params, dict):
            filestr = params['str']
        elif isinstance(params, str):
            filestr = params
        rest = bucket.set_canned_acl(filestr)
        handle_result(args, res)

    #----
    @staticmethod
    def action_bucket__new_key(args, params=None): # pylint: disable=unused-argument
        """Bucket: Create new key by name"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.new_key(args.key_name)
        key.set_contents_from_string('')
        key.close()
        handle_result(args, key)

    @staticmethod
    def action_bucket__initiate_multipart_upload(args, params=None): # pylint: disable=unused-argument
        """Bucket: Create new key by multipart upload"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        mp = bucket.initiate_multipart_upload(args.key_name)
        handle_result(args, mp)

    @staticmethod
    def action_multipartupload__complete_upload(args, params=None): # pylint: disable=unused-argument
        """Multipartupload: Complete upload"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        mp = bucket.get_all_multipart_uploads(prefix=args.key_name)[0]
        ret = mp.complete_upload()
        handle_result(args, ret)

    @staticmethod
    def action_multipartupload__cancel_upload(args, params=None): # pylint: disable=unused-argument
        """Multipartupload: Cancel upload"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        mp = bucket.get_all_multipart_uploads(prefix=args.key_name)[0]
        ret = mp.cancel_upload()
        handle_result(args, ret)

    @staticmethod
    def action_bucket__get_multipart_upload(args, params=None): # pylint: disable=unused-argument
        """Bucket: Get multipart upload"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        mp = bucket.get_all_multipart_uploads(prefix=args.key_name)[0]
        handle_result(args, mp)

    @staticmethod
    def action_multipartupload__upload_part_from_file(args, params=None): # pylint: disable=unused-argument
        """Multipartupload: Upload a single part to a multi-part; argument is the part number and defaults to 1."""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        if params is None or params is '':
            params = 1
        mp = bucket.get_all_multipart_uploads(prefix=args.key_name)[0]
        part = mp.upload_part_from_file(fp=args.filesrc, part_num=int(params))
        handle_result(args, part)

    #----
    @staticmethod
    def action_key__delete(args, params=None): # pylint: disable=unused-argument
        """Key: delete key"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_key(args.key_name)
        key.delete()
        handle_result(args, None)

    @staticmethod
    def action_key__get_acl(args, params=None): # pylint: disable=unused-argument
        """Key: get ACL"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_key(args.key_name)
        c = key.get_acl()
        handle_result(args, c)

    @staticmethod
    def action_key__get_contents_to_file(args, params=None): # pylint: disable=unused-argument
        """Key: get contents and store to file object"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_key(args.key_name)
        key.get_contents_to_file(fp=args.filesrc)
        handle_result(args, key)

    @staticmethod
    def action_key__get_contents_to_filename(args, params=None): # pylint: disable=unused-argument
        """Key: get contents and store to file by filename"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_key(args.key_name)
        filename = None
        if isinstance(params, dict):
            filename = params['filename']
        elif isinstance(params, str):
            filename = params
        key.get_contents_to_file(filename=filename)
        handle_result(args, key)

    @staticmethod
    def action_key__get_contents_as_string(args, params=None): # pylint: disable=unused-argument
        """Key: get contents as string"""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_key(args.key_name)
        s = key.get_contents_as_string()
        handle_result(args, s)

    @staticmethod
    def action_key__set_contents_from_file(args, params=None): # pylint: disable=unused-argument
        """Set content of key from a seekable file object.
        This function will read the file TWICE to build the MD5.
        """
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_key(args.key_name)
        key.set_contents_from_file(fp=args.filesrc, rewind=True)
        key.close()
        handle_result(args, key)

    @staticmethod
    def action_key__set_contents_from_filename(args, params=None): # pylint: disable=unused-argument
        """Set content of key from a filename."""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_key(args.key_name)
        filename = None
        if isinstance(params, dict):
            filename = params['filename']
        elif isinstance(params, str):
            filename = params
        # TODO: support other options to function
        key.set_contents_from_file(filename=filename)
        key.close()
        handle_result(args, key)

    @staticmethod
    def action_key__set_contents_from_stream(args, params=None): # pylint: disable=unused-argument
        """Set content of key from a non-seekable file object.
        This function will only read the file ONCE.
        """
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        key = bucket.get_key(args.key_name)
        key.set_contents_from_file(fp=args.filesrc, rewind=True)
        key.close()
        handle_result(args, key)

    @staticmethod
    def action_key__set_contents_from_string(args, params=None): # pylint: disable=unused-argument
        """Set content of key from a string."""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        filestr = 'foobar'
        if isinstance(params, dict):
            filestr = params['str']
        elif isinstance(params, str):
            filestr = params
        key = bucket.get_key(args.key_name)
        key.set_contents_from_string(filestr)
        handle_result(args, key)

    @staticmethod
    def action_key__set_canned_acl(args, params=None): # pylint: disable=unused-argument
        """Set ACL of key from canned string."""
        bucket = cached_get_bucket(args.conn, args.bucket_name)
        filestr = 'private'
        if isinstance(params, dict):
            filestr = params['str']
        elif isinstance(params, str):
            filestr = params
        key = bucket.get_key(args.key_name)
        res = key.set_canned_acl(filestr)
        handle_result(args, res)

    # ----
    @staticmethod
    def action_SET__BUCKET(args, params=None): # pylint: disable=unused-argument
        """Update the bucket name in use."""
        if params is None or params is '':
            params = generate_name(template=args.bucket_name_template, template_vars=vars(args))
        args.bucket_name = params

    @staticmethod
    def action_SET__KEY(args, params=None): # pylint: disable=unused-argument
        """Update the key name in use."""
        if params is None or params is '':
            params = generate_name(template=args.key_name_template, template_vars=vars(args))
        args.key_name = params

    @staticmethod
    def action_SET__FILENAME(args, params=None): # pylint: disable=unused-argument
        """Update the local filename in use."""
        if params is None or params is '':
            params = generate_name(template=args.file_name_template, template_vars=vars(args))
        args.file_name = params

    @staticmethod
    def action_SET__FILE_WRITE(args, params=None): # pylint: disable=unused-argument
        """Update the local file object from the filename, writing"""
        args.filesrc = open(args.file_name, 'w')

    @staticmethod
    def action_SET__FILE_READ(args, params=None): # pylint: disable=unused-argument
        """Update the local file object from the filename, reading"""
        args.filesrc = open(args.file_name, 'r')

    @staticmethod
    def action_SET__BUCKET__FIND(args, params=None): # pylint: disable=unused-argument
        """Set bucket to the first existing bucket matching the regex; bucket cleared on failure!"""
        if params is None or params is '':
            params = ''
        buckets = cached_get_all_buckets(args.conn) # Ensure it's built, but discard the result for now.
        global cached_buckets # pylint: disable=global-statement
        bucket_name = None
        bucket_re = re.compile(params)
        for bn in cached_buckets.keys():
            if bucket_re.search(bn):
                bucket_name = bn
                break
        args.bucket_name = bucket_name

    @staticmethod
    def action_SET__FILE__RANDOM(args, params=None): # pylint: disable=unused-argument
        """Update the local file to a random sourced file, optional params: file_size & seed"""
        if params is None or params is '':
            params = {}
        params['file_size'] = int(params.get('file_size', 1024*1024))
        params['seed'] = int(params.get('seed', random.getrandbits(32)))
        args.filesrc = fakefile.Fakefile(**params) # pylint: disable=star-args

    @staticmethod
    def action_PRINT__ALL(args, params=None): # pylint: disable=unused-argument
        """Print the complete contents of deque. """
        print("\n".join([str(s) for s in args.deque]))

    @staticmethod
    def action_PRINT__LAST(args, params=None): # pylint: disable=unused-argument
        """Print the last item of the deque. """
        print(args.deque[-1])

    @staticmethod
    def action_PRINT__BUCKETNAME(args, params=None): # pylint: disable=unused-argument
        """Print the bucket name."""
        print(args.bucket_name)

    @staticmethod
    def action_PUSH(args, params=None): # pylint: disable=unused-argument
        """Push the parameter onto the deque."""
        handle_result(args, params)

    @staticmethod
    def action_POP(args, params=None): # pylint: disable=unused-argument
        """Pop the last item from the deque."""
        if params is not None:
            args.deque.pop(params)
        else:
            args.deque.pop()

    @staticmethod
    def action_CLEAR(args, params=None): # pylint: disable=unused-argument
        """Clear the deque."""
        args.deque.clear()

    @staticmethod
    def action_TIMER__START(args, params=None): # pylint: disable=unused-argument
        """Start the timer."""
        t0 = time.time()
        args.timer.append(t0)

    @staticmethod
    def action_TIMER__STOP(args, params=None): # pylint: disable=unused-argument
        """Stop the timer."""
        t1 = time.time()
        t0 = args.timer.pop()
        elapsed = t1-t0
        s = "Elapsed: %10f" % (elapsed, )
        if args.last_loop_iterations > 1:
            s += ", per-iteration: %10f" % (elapsed/args.last_loop_iterations, )
        args.last_loop_iterations = 1
        handle_result(args, s, override=True)

    @staticmethod
    def action_LOOP(args, params=None): # pylint: disable=unused-argument
        """Loop the next action, N times"""
        # Special case, this is handled in the test runner!
        pass

    @staticmethod
    def action_HIDDEN_TEST_SLEEP_TIMEOUT(args, params=None): # pylint: disable=unused-argument
        """Hidden action: This action is for testing timeouts."""
        time.sleep(args.timeout + 1)

    @staticmethod
    def action_HIDDEN_TEST_EXCEPTION(args, params=None): # pylint: disable=unused-argument
        """Hidden action: This action is for testing Exceptions"""
        raise Exception("Testing exceptions")

# ----
def param_str_to_dict(paramstr):
    # http://stackoverflow.com/a/186873/1583179
    return dict(csv.reader([item], delimiter='=', quotechar="'").next() for item in csv.reader([paramstr], delimiter=';', quotechar="'").next())

def handle_result(args, result, override=None):
    if (override is True) or (override is None and args.stack_return):
        #print("Appending deque override={override}, stack_return={stack_return}".format(override=override, stack_return=args.stack_return))
        args.deque.append(result)
    else:
        pass

# START: fakefile block
import fakefile


# END s3-tests/s3tests/realistic.py
def print_actionhelp():
    rawmethods = list(itertools.chain.from_iterable([dir(Actions)]))
    methods = [_ for _ in rawmethods if _.startswith('action_') and 'HIDDEN' not in _]
    wrapper = textwrap.TextWrapper(initial_indent=' '*4, subsequent_indent=' '*4)
    help_order = ["conn__", "bucket__", "key__", "multipartupload__", "[A-Z]+"]
    help_order = (re.compile("^action_"+_) for _ in help_order)
    sorted_methods = []
    for help_order_element in help_order:
        methods_subset = sorted(_ for _ in methods if help_order_element.match(_))
        sorted_methods = itertools.chain(sorted_methods, methods_subset)

    print("Known actions:")
    #for method in sorted(methods):
    for method in sorted_methods:
        action = method.replace('action_', '').replace('__', '.')
        helpstr = inspect.getdoc(getattr(Actions, method))
        if helpstr is None:
            helpstr = "Undocumented!"
        helpstr = wrapper.fill(textwrap.dedent(helpstr))
        print("--action=%s\n%s" % (action, helpstr))
    print()

def main(argv=None):
    # pylint: disable=bad-continuation
    initial_parser = argparse.ArgumentParser(description='Nagios S3 Health Checks',
                        epilog='run via nrpe agent or Jenkins',
                        add_help=False)
    initial_parser.add_argument("--boto-config-file", type=file, required=False,
                        help="Specify config file in Boto format", metavar="FILE")
    initial_parser.add_argument("--s3test-config-file", type=file, required=False,
                        help="Specify config file in Ceph s3-test format", metavar="FILE")
    initial_parser.add_argument("--s3cmd-config-file", '--s3cfg-config-file', type=file, required=False,
                        help="Specify config file in s3cmd format", metavar="FILE")
    initial_parser.add_argument('--actions', action='append', required=False,
                        help='Actions to test (see --action=HELP for a list)')
    initial_parser.set_defaults(actions=[])
    initial_args = initial_parser.parse_known_args(argv)[0]

    defaults = {}
    if initial_args.boto_config_file:
        config = ConfigParser.RawConfigParser()
        config.readfp(initial_args.boto_config_file)
        if config.has_section('Defaults'):
            defaults.update(dict(config.items("Defaults")))
        if config.has_section('S3'):
            defaults.update(dict(config.items("S3")))
    if initial_args.s3cmd_config_file:
        config = ConfigParser.RawConfigParser()
        config.readfp(initial_args.s3cmd_config_file)
        if config.has_section('default'):
            defaults.update(dict(config.items("default")))
        if config.has_section('s3'):
            defaults.update(dict(config.items("s3")))
    if initial_args.s3test_config_file:
        pass

    complete_parser = argparse.ArgumentParser(parents=[initial_parser])
    complete_parser.add_argument('--host', '-H', type=str, help='Hostname', required=False)
    complete_parser.add_argument('--port', type=int, help='Port', required=False)
    complete_parser.add_argument('--connect-host', type=str, help='Host to override connection with', required=False)
    complete_parser.add_argument('--connect-port', type=str, help='Port to override connection with', required=False)
    complete_parser.add_argument('--access-key', type=str, required=False,
                        help='S3 Access key')
    complete_parser.add_argument('--secret-key', type=str, required=False,
                        help='S3 Secret key')
    complete_parser.add_argument('--deque', action='append', required=False,
                        default=collections.deque([]),
                        help='Initial deque state')
    complete_parser.add_argument('--calling-format', type=str, default='ordinary',
                        choices=CALLING_FORMATS.keys(),
                        help='S3 calling format')
    complete_parser.add_argument('--validate-certs', dest='validate_certs', action='store_true',
                        help='Validate SSL certs')
    complete_parser.add_argument('--no-validate-certs', dest='validate_certs', action='store_false',
                        help='Validate SSL certs')
    complete_parser.set_defaults(validate_certs=False)
    complete_parser.add_argument('--debug', action='store_true',
                        help='Enable check debuging')
    complete_parser.add_argument('--boto-debug', type=int, required=False, default=0,
                        help='Enable Boto debug on connection')
    complete_parser.add_argument('--timeout', type=float, required=False, default=60,
                        help='Timeout for test')
    complete_parser.add_argument('--secure', dest='secure', action='store_true', help='Use SSL')
    complete_parser.add_argument('--no-secure', dest='secure', action='store_false', help='Use SSL')
    complete_parser.set_defaults(secure=False)
    complete_parser.add_argument('--stack-return', dest='stack_return', action='store_true', help='Put results into stack (default)')
    complete_parser.add_argument('--no-stack-return', dest='stack_return', action='store_false', help='Do NOT put results into stack')
    complete_parser.set_defaults(stack_return=True)
    complete_parser.add_argument('--very-insecure', dest='very_insecure', action='store_true', help='Disable ALL SSL validation (for self-signed certs)')
    complete_parser.add_argument('--allow-selfsigned-cert', dest='very_insecure', action='store_true', help='Disable ALL SSL validation (for self-signed certs)')
    # --
    complete_parser.add_argument('--bucket-name-template', type=str, required=False,
                        #default='{uuid1}-s3-health-bucket-{time}',
                        default='{hextime}-s3-health-bucket',
                        help='Template for S3 Bucket Name')
    complete_parser.add_argument('--bucket-name', type=str, required=False,
                        help='Specific S3 Bucket Name')
    complete_parser.add_argument('--key-name-template', type=str, required=False,
                        #default='{uuid1}-s3-health-key-{time}',
                        default='{hextime}-s3-health-key-{seq}',
                        help='Template for S3 filename')
    complete_parser.add_argument('--key-name', type=str, required=False,
                        help='Specific S3 filename')
    complete_parser.add_argument('--file-name-template', type=str, required=False,
                        #default='file-s3-health-{uuid1}-{time}',
                        default='{hextime}-file-s3-health',
                        help='Template for local filename')
    complete_parser.add_argument('--file-name', type=str, required=False,
                        help='Specific local filename')
    complete_parser.add_argument('--cors-test-rule-id-prefix', type=str, required=False,
                        default='s3-cors-health',
                        help='Set name used for CORS rule test')
    # --
    complete_parser.add_argument('--nagios', action='store_true',
                        help='Use nagios-style exit')
    complete_parser.add_argument('--verbose', action='store_true',
                        help='Print each action as it happens (Also enables nagios longdesc)')
    # -- Hidden options
    #complete_parser.add_argument('--nagios-object', help=argparse.SUPPRESS)

    # --actions=HELP is a special case
    if initial_args.actions and 'HELP' in (action.upper() for action in initial_args.actions):
        print_actionhelp()
        complete_parser.print_usage()
        sys.exit(1)

    parser_args = argparse.Namespace()
    default_args = ["--%s=%s" % (k.replace('_', '-'), v) for k,v in defaults.items()]
    # Put it all together
    # Ignore stuff we don't know
    complete_parser.parse_known_args(default_args, namespace=parser_args)
    complete_parser.parse_args(argv, namespace=parser_args)
    # We have to handle the required options ourselves, because we cannot disable the required handling for just default_args
    for opt in ['host', 'access_key', 'secret_key']:
        if getattr(parser_args, opt, None) is None:
            complete_parser.error('option --%s is required' % (opt, ))

    if not parser_args.bucket_name:
        parser_args.bucket_name = generate_name(template=parser_args.bucket_name_template, template_vars=vars(parser_args))
    if not parser_args.file_name:
        parser_args.file_name = generate_name(template=parser_args.file_name_template, template_vars=vars(parser_args))
    if not parser_args.key_name:
        parser_args.key_name = generate_name(template=parser_args.key_name_template, template_vars=vars(parser_args))
    # No data source file by default
    parser_args.filesrc = None

    if parser_args.very_insecure:
        # http://stackoverflow.com/questions/27835619/ssl-certificate-verify-failed-error
        import ssl
        if getattr(ssl, 'SSLContext', None) and getattr(ssl, '_https_verify_certificates', None):
            # Added in Python 2.7.12
            # https://github.com/python/cpython/commit/6cdc1f12b8c6054009ccd449f2d5cedf9d2a7ad8
            ssl._https_verify_certificates(enable=False)
        elif getattr(ssl, '_create_default_https_context', None) and getattr(ssl, '_create_unverified_context', None):
            # Added in Python 2.7.9
            # https://github.com/python/cpython/commit/ae5b953dca859b2b78727d6a895b0c5d16c73904
            ssl._create_default_https_context = ssl._create_unverified_context
        else:
            if parser_args.debug:
                print('DEBUG: Could not disable SSL verification, neither _https_verify_certificates not _create_unverified_context available')

    if not parser_args.port:
        if parser_args.secure:
            parser_args.port = 443
        else:
            parser_args.port = 80

    if parser_args.boto_debug and int(parser_args.boto_debug) > 0:
        boto.set_stream_logger('s3-health', level=parser_args.boto_debug)

    new_actions = []
    for raw_action in parser_args.actions:
        action, params = (raw_action.split('=', 1) + ['']*2)[0:2]
        if '=' in params:
            params = param_str_to_dict(params)
        new_actions.append((action, params))
    parser_args.actions = new_actions

    parser_args.conn = None
    parser_args.timer = []
    parser_args.nagios_object = NagiosStatus()

    try:
        with TimeoutClass(parser_args.timeout, os.strerror(errno.ETIMEDOUT)):
            testrunner(parser_args)
            parser_args.nagios_object.add('OK', 'All good!')
    except TimeoutError as e:
        exc_string = traceback.format_exc()
        parser_args.nagios_object.add('WARNING', str(e), str(e)+"\n"+exc_string)
    except Exception as e:
        exc_string = str(e) + "\n" + traceback.format_exc()
        if not parser_args.nagios:
            print(exc_string)
            raise
        parser_args.nagios_object.add('CRITICAL', str(e), exc_string)

    if parser_args.nagios:
        parser_args.nagios_object.fire_exit(long_output=parser_args.verbose)


if __name__ == "__main__":
    main(argv=sys.argv[1:])

#vim: sts=4 ts=4 sw=4 ft=python:
