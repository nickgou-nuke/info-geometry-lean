"""Derive the correctedT action on the exact Lean CAS point order.

This is a carrier-alignment artifact.  It parses the literal ``casPointFull``
table from the Lean owner, applies the exact 8x8 GF(2) matrix used for
``correctedT``, and emits the resulting Fin 63 permutation.  No group order
or quotient assertion is imported into Lean by this script.
"""

from pathlib import Path
import re


OWNER = Path("lean/InfoGeometry/Algebra/Zorn/G2CASNativePointEnumeration.lean")


def bits(text):
    return tuple(int(x) & 1 for x in re.findall(r"[01]", text))


def parse_points():
    text = OWNER.read_text()
    rows = {}
    for m in re.finditer(r"\|\s*(\d+)\s*=>\s*!\[([^\]]+)\]", text):
        rows[int(m.group(1))] = bits(m.group(2))
    expected = set(range(63))
    if set(rows) != expected:
        raise RuntimeError(f"point table indices are {sorted(rows)}, expected 0..62")
    if any(len(rows[i]) != 8 for i in expected):
        raise RuntimeError("point table is not 8-dimensional")
    return [rows[i] for i in range(63)]


def mat(rows):
    return tuple(tuple(1 if j in support else 0 for j in range(8)) for support in rows)


# correctedT = cycle^2 * swap01Aut * swapCartanAut in the GAP matrix order.
# The row convention is the same one used by diagnose_lean_t_carrier.py.
cycle = mat(((0,), (1,), (3,), (4,), (2,), (6,), (7,), (5,)))
swap = mat(((0,), (1,), (3,), (2,), (4,), (6,), (5,), (7,)))
cartan = mat(((0,), (1,), (5,), (6,), (7,), (2,), (3,), (4,)))


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(8)) & 1
                       for j in range(8)) for i in range(8))


def mv(a, v):
    return tuple(sum(a[i][j] * v[j] for j in range(8)) & 1 for i in range(8))


def main():
    points = parse_points()
    corrected_t = mm(mm(mm(cycle, cycle), swap), cartan)
    index = {p: i for i, p in enumerate(points)}
    image = [index.get(mv(corrected_t, p)) for p in points]
    if any(i is None for i in image):
        raise RuntimeError("correctedT does not preserve the parsed 63-point carrier")
    if len(set(image)) != 63:
        raise RuntimeError("correctedT image is not a permutation")
    print("CORRECTED_T_POINT_ACTION=PASS")
    print("CORRECTED_T_POINT_PERM=[" + ", ".join(map(str, image)) + "]")


if __name__ == "__main__":
    main()
