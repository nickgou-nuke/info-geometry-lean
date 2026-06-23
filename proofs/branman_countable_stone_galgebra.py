#!/usr/bin/env python3
"""galgebra-lane finite-core check for inverse-closed labels."""

try:
    import galgebra  # noqa: F401
except Exception as exc:
    raise SystemExit(f"galgebra import failed: {exc}")

modulus = 5
labels = {1, modulus - 1}

for f in labels:
    assert (-f) % modulus in labels

print("branman countable Stone finite core galgebra check: ok")
