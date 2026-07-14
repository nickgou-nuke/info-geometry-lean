with open("make_proof.py", "r") as f:
    lines = f.read()

lines = lines.replace(
    "entry_separated R q 0 1 1 0 (by decide) (by decide)",
    "(entry_separated R q 0 1 1 0 (by decide) (by decide)).symm"
)
lines = lines.replace(
    "entry_separated R q 0 1 2 0 (by decide) (by decide)",
    "(entry_separated R q 0 1 2 0 (by decide) (by decide)).symm"
)
lines = lines.replace(
    "entry_separated R q 0 1 3 0 (by decide) (by decide)",
    "(entry_separated R q 0 1 3 0 (by decide) (by decide)).symm"
)
lines = lines.replace(
    "entry_separated R q 0 1 2 1 (by decide) (by decide)",
    "(entry_separated R q 0 1 2 1 (by decide) (by decide)).symm"
)
lines = lines.replace(
    "entry_separated R q 0 1 3 1 (by decide) (by decide)",
    "(entry_separated R q 0 1 3 1 (by decide) (by decide)).symm"
)
lines = lines.replace(
    "entry_separated R q 0 1 3 2 (by decide) (by decide)",
    "(entry_separated R q 0 1 3 2 (by decide) (by decide)).symm"
)

with open("make_proof.py", "w") as f:
    f.write(lines)
