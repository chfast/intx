#!/usr/bin/env python3

import os
import sys

ops_filter = ('<<', '>>')

ops = ('/', '*', '<<', '>>')


def decode_file(file):
    with open(file, 'rb') as f:
        decode_data(f.read())


def decode_data(data):
    arg_size = (len(data) - 1) // 2
    if arg_size not in (32, 64):
        return

    op_index = int(data[0])
    if op_index >= len(ops):
        return
    op = ops[op_index]

    if ops_filter and op not in ops_filter:
        return

    x = int.from_bytes(data[1:1 + arg_size], byteorder='big')
    y = int.from_bytes(data[1 + arg_size:], byteorder='big')

    print(x, op, y)


assert len(sys.argv) > 1

corpus_dir = sys.argv[1]

for root, _, files in os.walk(corpus_dir):
    for file in files:
        decode_file(os.path.join(root, file))
