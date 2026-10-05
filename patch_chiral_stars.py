with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'r') as f:
    content = f.read()

content = content.replace(
    "    simpa [rightChiralStar] using leftChiralStar_add_left X Z Y",
    "    simpa [rightChiralStar] using chiralStar_add_left X Z Y"
)
content = content.replace(
    "    simpa [rightChiralStar] using leftChiralStar_smul_left a X Y",
    "    simpa [rightChiralStar] using chiralStar_smul_left a X Y"
)
with open('lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean', 'w') as f:
    f.write(content)
