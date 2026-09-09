from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
cells_file = root / "lean/InfoGeometry/Algebra/Zorn/G2FlagWordCertificate.lean"
out = root / "lean/InfoGeometry/Algebra/Zorn/G2GAPFlagWitnessRows.lean"
text = cells_file.read_text()
body = text.split("def flagCells", 1)[1].split("/- GAP orbit order", 1)[0]
rows = re.findall(r"\{([^{}]*)\}", body)
cells = [[int(x) for x in re.findall(r"\d+", row)] for row in rows]
if len(cells) != 12 or sum(map(len, cells)) != 189:
    raise SystemExit("unexpected flag partition")
lines = [
    "import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessReadback", "",
    "namespace InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessRows", "",
    "open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessReadback",
    "open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate",
    "",
]
for k, cell in enumerate(cells):
    for i in cell:
        lines += [
            "set_option maxRecDepth 100000 in",
            "@[simp]",
            f"theorem row_{k}_{i} : gapWitnessMatrixSound {k} {i} := by",
            "  unfold gapWitnessMatrixSound", "  decide", "",
        ]
lines += ["end InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessRows", ""]
out.write_text("\n".join(lines).rstrip() + "\n")
