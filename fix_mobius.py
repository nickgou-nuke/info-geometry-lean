import re

with open("sandbox/MobiusGeometry_subagent.lean", "r") as f:
    content = f.read()

# Extract mobius_algebraic_decomposition
thm_match = re.search(r'(/-- Alternative algebraic representation of the decomposition:.*?\n  rw \[h_final\]\n)', content, re.DOTALL)
if not thm_match:
    print("Could not find theorem to move")
    exit(1)
thm_str = thm_match.group(1)

# Remove it from its original place
content = content.replace(thm_str, '')

# Insert it before mobius_decomposition
insert_match = re.search(r'(/-- Any Möbius transformation with c ≠ 0 can be decomposed into:)', content)
if not insert_match:
    print("Could not find insertion point")
    exit(1)

insert_idx = insert_match.start()
content = content[:insert_idx] + thm_str + "\n" + content[insert_idx:]

# Fix the rw [hz_eq, hz, h_div] issue
content = content.replace("rw [hz_eq, hz, h_div]", "rw [hz_eq, h_div, hz]")

with open("sandbox/MobiusGeometry_subagent.lean", "w") as f:
    f.write(content)

print("Fix applied")
