import re
from pathlib import Path

DECL_HEADER_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:partial\s+)?(?:private\s+|protected\s+|local\s+)?"
    r"(theorem|lemma|example|def|abbrev|structure|class|instance|axiom|postulate|inductive)\b"
    r"\s+([A-Za-z0-9_'.]+)",
    re.M,
)

text = Path("lean/InfoGeometry/Singular/MoorePenrose.lean").read_text()
for m in DECL_HEADER_RE.finditer(text):
    print(f"{m.group(1)} {m.group(2)} at {text[:m.start()].count('\n') + 1}")
