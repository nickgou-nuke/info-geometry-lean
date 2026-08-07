import re

content = open("lean/InfoGeometry/Canonical/HestenesBivectorCarrier.lean").read()

# Fix h13
content = content.replace("HasSpacetimeBasis.orthogonal 3 1", "HasSpacetimeBasis.orthogonal 1 3")

# We will just write a python script to find each case block and replace it.
# It's safer to just do it interactively with `multi_replace_file_content`

open("lean/InfoGeometry/Canonical/HestenesBivectorCarrier.lean", "w").write(content)
