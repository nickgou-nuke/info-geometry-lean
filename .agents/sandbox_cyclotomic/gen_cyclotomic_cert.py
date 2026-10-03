#!/usr/bin/env python3
"""Generate CAS certificates for CyclotomicExplicitMatrixBridge.

Emits exact integer power certificates for the 8x8 companion matrix of
X^8 - X^4 + 1 (= Phi_24), so the Lean proof is a chain of small kernel-checked
equalities instead of one huge `decide` over A^24.

Reproduce with:  python3 .agents/sandbox_cyclotomic/gen_cyclotomic_cert.py
"""

from __future__ import annotations


def mat_mul(A: list[list[int]], B: list[list[int]]) -> list[list[int]]:
    n = len(A)
    m = len(B)
    p = len(B[0])
    assert m == n, (n, m)
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)] for i in range(n)]


def mat_pow(A: list[list[int]], e: int) -> list[list[int]]:
    n = len(A)
    R = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    for _ in range(e):
        R = mat_mul(R, A)
    return R


def emit(name: str, A: list[list[int]]) -> str:
    n = len(A)
    lines = []
    for i, row in enumerate(A):
        cells = ", ".join(str(v) for v in row)
        if i == 0:
            lines.append(f"  !![{cells};")
        elif i == n - 1:
            lines.append(f"    {cells}]")
        else:
            lines.append(f"    {cells};")
    return f"def {name} : M{n} :=\n" + "\n".join(lines) + "\n"


PHI24 = [
    [0, 0, 0, 0, 0, 0, 0, -1],
    [1, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 1],
    [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0],
]


def main() -> None:
    out = []
    A2 = mat_pow(PHI24, 2)
    A4 = mat_pow(PHI24, 4)
    A8 = mat_pow(PHI24, 8)
    A16 = mat_pow(PHI24, 16)
    A24 = mat_pow(PHI24, 24)

    # The defining relation of the companion matrix: A^8 - A^4 + 1 = 0.
    rel = [[A8[i][j] - A4[i][j] + (1 if i == j else 0) for j in range(8)] for i in range(8)]
    assert all(all(v == 0 for v in row) for row in rel), "A^8 - A^4 + 1 != 0"

    # A^16 * A^8 = A^24 must be the identity.
    prod = mat_mul(A16, A8)
    ident = [[1 if i == j else 0 for j in range(8)] for i in range(8)]
    assert prod == ident, "A^16 * A^8 != 1"
    assert A24 == ident, "A^24 != 1"

    out.append(emit("phi24Companion_sq", A2))
    out.append(emit("phi24Companion_fourth", A4))
    out.append(emit("phi24Companion_eighth", A8))
    out.append(emit("phi24Companion_sixteenth", A16))
    print("\n".join(out))

    # Cross-check the smaller stages too, so the whole file is CAS-verified.
    tripotent = [[1, 0, 0], [0, -1, 0], [0, 0, 0]]
    assert mat_pow(tripotent, 3) == tripotent, "tripotent^3 != tripotent"

    complexStage = [[0, -1, 0], [1, 0, 0], [0, 0, 0]]
    assert mat_pow(complexStage, 3) == [[-v for v in row] for row in complexStage], \
        "complexStage^3 != -complexStage"

    phi6 = [[0, -1], [1, 1]]
    assert mat_pow(phi6, 6) == [[1, 0], [0, 1]], "phi6^6 != 1"

    phi8 = [
        [0, 0, 0, -1],
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
    ]
    assert mat_pow(phi8, 4) == [[-1 if i == j else 0 for j in range(4)] for i in range(4)], \
        "phi8^4 != -1"

    phi12 = [
        [0, 0, 0, -1],
        [1, 0, 0, 0],
        [0, 1, 0, 1],
        [0, 0, 1, 0],
    ]
    assert mat_pow(phi12, 12) == [[1 if i == j else 0 for j in range(4)] for i in range(4)], \
        "phi12^12 != 1"

    print("---\n-- all CAS cross-checks passed ---\n---")


if __name__ == "__main__":
    main()
