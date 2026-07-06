import re

with open('.lake/packages/Paperproof/lakefile.lean', 'r') as f:
    text = f.read()

# Replace require mathlib from git "..." @ "..." with require mathlib from "../mathlib"
text = re.sub(r'require\s+mathlib\s+from\s+git\s+"[^"]+"(\s*@\s*"[^"]+")?', 'require mathlib from "../mathlib"', text)

with open('.lake/packages/Paperproof/lakefile.lean', 'w') as f:
    f.write(text)
