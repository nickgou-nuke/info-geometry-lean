import re
import sys

def process_file(path):
    with open(path, 'r') as f:
        content = f.read()

    # Find structures that end in Interface and convert them
    # This is a bit tricky to do purely with regex if they are complex.
    # It might be easier to use a script specifically tailored to the known files,
    # or I will just write a simple multi-replace.
    pass
