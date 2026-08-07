import re

content = open("lean/InfoGeometry/Canonical/HestenesBivectorCarrier.lean", "r").read()

test_lemmas = [
    "lemma test_01",
    "lemma test_02",
    "lemma test_03",
    "lemma test_23",
    "lemma test_31",
    "lemma test_12",
]

for t in test_lemmas:
    start_idx = content.find(t)
    # find next empty line or next lemma
    next_lemma_idx = content.find("lemma", start_idx + 10)
    if next_lemma_idx == -1:
        next_lemma_idx = content.find("def ", start_idx + 10)
    
print("ok")
