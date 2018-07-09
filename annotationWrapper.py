""" 
	Parses the files for annotations to extract the information and do some transformations on the code.
	On return the Annotation information is used to change mythrils output regarding the changes code pieces

"""

from glob import glob
import re, sys
import json

newlines = ["\r\n", "\r", "\n"]

def find_all(a_str, sub):
    start = 0
    while True:
        start = a_str.find(sub, start)
        if start == -1:
            return
        yield start
        start += len(sub)

def count_elements(source, elements):
    ret = 0
    for element in elements:
        ret += source.count(element)
    return ret


def replace_index(text, toReplace, replacement, index):
    return text[:index] + replacement + text[(index + len(toReplace)):]

"""
    Here it might be better to split annotations into the containing constraint an the prefix and sufix
"""
def parse_annotation_info(filedata):
    annotations = []
    for inv in re.findall(r'//invariant\(([^\)]+)\)(\r\n|\r|\n)', filedata):
        match_inv = "//invariant(" + inv[0] + ")"
        for pos in find_all(filedata, match_inv + inv[1]):
            line = count_elements(filedata[:pos], newlines) + 1
            col = pos - max(map(lambda x: filedata[:pos].rfind(x), newlines))
            annotations.append((pos, line, col, '//invariant(', inv[0], ")", inv[1]))
    return set(annotations)


def read_write_file(filename):
    with open(filename, 'r') as file :
        filedata = file.read()

    annotations = parse_annotation_info(filedata)

    annotations = sorted(list(annotations), key=lambda x: x[0], reverse=True)
    for annotation in annotations:
        filedata = replace_index(filedata, annotation[3] + annotation[4] + annotation[5] + annotation[6],  "assert("
                                 + annotation[4] + ");" + annotation[6], annotation[0])
    # Replace the target string
    # filedata = filedata.replace('@ensure', '@invariant')
    # filedata = filedata.replace('@invariant', '@ensure')

    with open(filename, 'w') as file:
       file.write(filedata)
    return annotations

annot_map = {}

for sol_file in glob("./*.sol"):
    annot_map[sol_file] = read_write_file(sol_file)
json.dump(annot_map, sys.stdout)
print("#end annotations#")
