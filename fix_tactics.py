import re

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

# Replace `apply Quaternion.ext <;>` with `try apply Quaternion.ext <;>`
content = content.replace('apply Quaternion.ext <;>', 'try apply Quaternion.ext <;>')

# For chiralStar_coordinates_eq, it ends with `ring`. We can add `<;> try trivial` to the end of that block.
content = content.replace('        ring\n', '        ring <;> try trivial\n')

# For the others, they end with `entryOne]` or `imK_mul]`. We can add `<;> try trivial`
content = content.replace('        Quaternion.imK_mul, entryOne]\n', '        Quaternion.imK_mul, entryOne] <;> try trivial\n')
content = content.replace('        Quaternion.imK_mul]\n', '        Quaternion.imK_mul] <;> try trivial\n')

with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
