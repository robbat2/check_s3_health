#!/usr/bin/python
#
# A determinisic fake file object with low memory growth
#
# Authors:
# Robin Johnson <robin.johnson@dreamhost.com> (original author)
#
# License: This file is copyright under BSD-2 license:
# Copyright (c) 2016, Robin H. Johnson <robbat2@orbis-terrarum.net>
# Copyright (c) 2016, Dreamhost
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
# Notes on ideas that were tried and did not help:
# - XorShift128+ PRNG is actually SLOWER than Python's random.Random(), by a
#   factor of 3x.
#
# pylint: disable=line-too-long, missing-docstring, abstract-class-not-used
# xpylint: disable=fixme, line-too-long, missing-docstring, invalid-name
from __future__ import print_function
import collections
import os
import random
import sys
import struct
# Debugging
#import guppy

class Fakefile(object):
    """Fake file generator.
    Returns chunks with a known header, and determinisic data based on the
    header of each chunk.
    - Seekable with zero latency.
    - Very slow memory growth (~56 bytes per chunk)
    - High data rate
      - Random: ~20MB/sec (Core i7 2600K @ 3.40GHz)
      - Zeros: ~3.5GB/sec (Core i7 2600K @ 3.40GHz)
    """
    CHUNK_HEADER_TEMPLATE = 'pos:0x%016x seed:0x%08x size:0x%08x'
    CHUNK_HEADER_PADSIZE = 64
    CHUNK_SIZE = 64*1024
    CHUNK_DATA_STYLE_NULL = 1L
    CHUNK_DATA_STYLE_RANDOM = 2L
    FAKEFILE_DEFAULT_SIZE = 1024*1024
    FAKEFILE_DEFAULT_RNG = random.Random

    def __init__(self, file_size=FAKEFILE_DEFAULT_SIZE, chunk_size=CHUNK_SIZE, seed=random.randint(0, 2**31), chunk_data_style=CHUNK_DATA_STYLE_RANDOM, rng_class=FAKEFILE_DEFAULT_RNG):
        self._seed = seed
        self._file_size = file_size
        self._chunk_size = chunk_size
        self._chunk_seed_rng = rng_class()
        self._chunk_seed_rng.seed(seed)
        self._chunk_data_rng = rng_class()
        self._chunkseeds = collections.defaultdict(lambda: self._chunk_seed_rng.getrandbits(32))
        self._current_chunk = None
        self._chunk_data_style = chunk_data_style
        self._pos = 0
        # These are required properties for files
        self.closed = False
        self.encoding = 'ascii'

    @staticmethod
    def _generate_chunk_header(chunk_offset, chunk_seed, chunk_size):
        header = Fakefile.CHUNK_HEADER_TEMPLATE % (chunk_offset, chunk_seed, chunk_size)
        return header.ljust(Fakefile.CHUNK_HEADER_PADSIZE, '\0')

    @staticmethod
    def _generate_chunk_data_null(data_size):
        return '\0' * data_size

    @staticmethod
    def _generate_chunk_data_random(data_size, rng):
        """This is the actual data generator function that needs to be fast."""
        # +1 so we have one extra block that we can truncate from
        # yes; this will have a side effect of losing some of the PRNG output bits
        # but we require that it is reseeded after this anyway.
        num_64i = data_size/8 + 1
        randdata = [rng.getrandbits(64) for _ in range(num_64i)]
        randdata = struct.pack(str(num_64i) + 'Q', *randdata) # pylint: disable=star-args
        return randdata[:data_size]

    @staticmethod
    def _generate_chunk(offset, numbytes, seed, style, chunk_data_rng):
        assert numbytes >= Fakefile.CHUNK_HEADER_PADSIZE
        hdr = Fakefile._generate_chunk_header(chunk_offset=offset, chunk_size=numbytes, chunk_seed=seed)

        chunk_data_size = numbytes - Fakefile.CHUNK_HEADER_PADSIZE
        if style is Fakefile.CHUNK_DATA_STYLE_NULL:
            data = Fakefile._generate_chunk_data_null(data_size=chunk_data_size)
        elif style is Fakefile.CHUNK_DATA_STYLE_RANDOM:
            chunk_data_rng.seed(seed)
            data = Fakefile._generate_chunk_data_random(data_size=chunk_data_size, rng=chunk_data_rng)
        else:
            raise NotImplementedError("Unknown chunk_style") # pylint: disable=abstract-class-not-used

        chunk = hdr+data
        #print("Requested", Fakefile.CHUNK_HEADER_PADSIZE, chunk_data_size)
        #print("Actual", len(hdr), len(data))
        assert len(chunk) == numbytes
        return chunk

    def get_chunk_seed_by_idx(self, idx):
        if self._chunk_data_style is Fakefile.CHUNK_DATA_STYLE_NULL:
            return 0
        elif self._chunk_data_style is Fakefile.CHUNK_DATA_STYLE_RANDOM:
            return self._chunkseeds[idx]

    def get_chunk_by_index(self, idx):
        # This has a side-effect of generating & storing the seed if unknown!
        seed = self.get_chunk_seed_by_idx(idx)
        # Return the chunk now
        return Fakefile._generate_chunk(offset=idx*self._chunk_size, numbytes=self._chunk_size, seed=seed, chunk_data_rng=self._chunk_data_rng, style=self._chunk_data_style)

    def get_chunk_by_offset(self, offset):
        return self.get_chunk_by_index(int(offset/self._chunk_size))

    # File methods:
    def next(self):
        return self

    def seek(self, offset, whence=os.SEEK_SET):
        if self.closed:
            raise IOError
        if whence is os.SEEK_SET:
            self._pos = offset
        elif whence is os.SEEK_CUR:
            self._pos = self._pos + offset
        elif whence is os.SEEK_END and self._file_size >= 0:
            self._pos = self._file_size + offset
        elif whence is os.SEEK_END:
            raise NotImplementedError(self.__class__.__name__+".seek(): whence=SEEK_END unsupported on infinite file!") # pylint: disable=abstract-class-not-used
        else:
            raise NotImplementedError(self.__class__.__name__+".seek(): Unknown whence") # pylint: disable=abstract-class-not-used
        # Now discard the cached chunk, we will regenerate as needed
        self._current_chunk = None

    def tell(self):
        if self.closed:
            raise IOError
        return self._pos

    def read(self, size=-1):
        if self.closed:
            raise IOError
        # Cannot read to the END of a file if the file is an infinite stream
        if size < 0 and not self._file_size > 0:
            raise NotImplementedError(self.__class__.__name__+".read(): read size must be non-zero for an infinite file") # pylint: disable=abstract-class-not-used
        # If we are given a negative input; or we want to read past the end of the file
        # adjust size down so it just returns the remaining bytes
        if size < 0 or (self._file_size and size+self.tell() > self._file_size):
            size = self._file_size - self.tell()
        data = []
        bytes_left = size
        while bytes_left > 0:
            chunk_data, read_size = self.chunk_read(bytes_left)
            data.append(chunk_data)
            bytes_left -= read_size
        return ''.join(data)

    def chunk_read(self, size=-1):
        """Read at most one chunk."""
        if size > self._chunk_size:
            size = self._chunk_size

        offset_in_chunk = self.tell() % self._chunk_size
        remaining_in_chunk = self._chunk_size - offset_in_chunk
        if size > remaining_in_chunk:
            size = remaining_in_chunk

        if self._current_chunk is None:
            self._current_chunk = self.get_chunk_by_offset(self.tell())

        new_offset_in_chunk = offset_in_chunk + size

        self._pos += size
        data = self._current_chunk[offset_in_chunk:new_offset_in_chunk]

        # Discard the chunk if we are done
        assert new_offset_in_chunk <= self._chunk_size
        if new_offset_in_chunk == self._chunk_size:
            self._current_chunk = None

        return data, size

    def write(self, data):
        raise NotImplementedError(self.__class__.__name__+": Read-only file source!") # pylint: disable=abstract-class-not-used

    def close(self):
        self.closed = True

    def __enter__(self):
        return self
    def __exit__(self, type, value, traceback):
        pass

def fakefile_timeit():
    sys.argv = [None, 1024*1024, random.getrandbits(32), 0]
    fakefile_main()

def fakefile_main():
    firstseed = random.getrandbits(32)
    filesize = 1024*1024*128
    readsize = 0
    #print(sys.argv)
    if len(sys.argv) > 1:
        filesize = int(sys.argv[1])
    if len(sys.argv) > 2:
        firstseed = int(sys.argv[2])
    if len(sys.argv) > 3:
        readsize = int(sys.argv[3])

    #randfile = Fakefile(filesize, seed=firstseed, chunk_data_style=Fakefile.CHUNK_DATA_STYLE_NULL)
    randfile = Fakefile(filesize, seed=firstseed, chunk_data_style=Fakefile.CHUNK_DATA_STYLE_RANDOM)

    #b = f.read(readsize)
    #hp = guppy.hpy()
    #hp.setrelheap()
    #print(hp.heap(), file=sys.stderr)

    #f.seek(16)
    if readsize > 0:
        block = randfile.read(readsize)
        #print(block, end='')
    else:
        while True:
            block = randfile.read(1024*1024)
            if block is '':
                break
            print(block, end='')
            #print(randfile.tell(), hp.heap(), file=sys.stderr)
    #print(randfile.tell(), hp.heap(), file=sys.stderr)

if __name__ == '__main__':
    fakefile_main()
