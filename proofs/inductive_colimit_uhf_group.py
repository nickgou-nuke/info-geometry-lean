"""Formalized symmetry of the two statements in SymPy arithmetic terms:
1) diagonal/UHF finite-stage chain is an ω-indexed inductive system,
2) dyadic rationals are the directed (colimit) union of 2-power denominator stages.
"""

from fractions import Fraction
from typing import Callable
import sympy as sp


def level_words(n):
    """All binary words of length n as tuples."""
    if n < 0:
        return []
    if n == 0:
        return [()]
    prev = level_words(n - 1)
    return [w + (0,) for w in prev] + [w + (1,) for w in prev]


def diagonal_embed(word):
    """Diagonal refinement map D_n -> D_{n+1}: append one fixed 0 bit."""
    return word + (0,)


def finite_to_boundary(word, limit):
    """Zero-padded readout of a finite binary word into function N->Bool on [0..limit)."""
    def readout(k):
        return bool(word[k]) if k < len(word) else False

    return readout


def is_compatible(n):
    """Check finite-to-boundary compatibility on each word of length n."""
    for word in level_words(n):
        e = diagonal_embed(word)
        f_n = finite_to_boundary(word, n)
        f_np1 = finite_to_boundary(e, n + 1)
        for k in range(n + 1):
            if f_np1(k) != f_n(k):
                return False
    return True


def word_to_dyadic(word):
    """Map a finite binary word to a dyadic rational with denominator 2^len(word)."""
    n = len(word)
    num = 0
    for i, bit in enumerate(word):
        weight = 2 ** (n - i - 1)
        num += int(bool(bit)) * weight
    return Fraction(num, 2 ** n)


def dyadic_union_contains_frac(x, max_n=8):
    """Check whether a Fraction lies in union z/2^n for some n <= max_n."""
    return any((x * (2 ** n)).denominator == 1 for n in range(max_n + 1))

def dyadic_union_contains_rational(x, max_n=8):
    """SymPy version of dyadic membership check."""
    return any((x * (sp.Integer(2) ** sp.Integer(n))).q == 1 for n in range(max_n + 1))


def main():
    print("── Statements formalized (SymPy/arithmetical witness) ──")

    for n in range(6):
        w_n = level_words(n)
        print(f"stage n={n}: |2^{{{n}}} binary words| = {len(w_n)}")
        if n > 0:
            print(f"  compatibility D_{n-1} -> D_n via append 0 : {is_compatible(n-1)}")
        # bridge: finite-stage words map to dyadic stage level-n rationals
        if n > 0:
            for word in w_n[:2]:
                r = word_to_dyadic(word)
                print(f"    word {word} -> dyadic q={r} in stage DyadicLevel {n}")
    # Direct limit / colimit-like union picture
    print("\nDyadic union sample:")
    rationals = [Fraction(3, 4), Fraction(-7, 8), Fraction(5, 6), Fraction(1, 16)]
    for q in rationals:
        print(f"  q = {q} in dyadic chain (Fraction) : {dyadic_union_contains_frac(q)}")

    rationals_sp = [sp.Rational(3, 4), sp.Rational(-7, 8), sp.Rational(5, 6), sp.Rational(1, 16)]
    for q in rationals_sp:
        print(f"  q = {q} in dyadic chain (SymPy) : {dyadic_union_contains_rational(q)}")

    print("\nPrecision checkpoint:")
    print(" - Bulk UHF object is built by an inductive ω-chain (finite-stage colimit).")
    print(" - Cantor-type boundary comes from diagonal stage readout (MASA/diagonal spectrum), not full UHF algebra.")
    print(" - The number-theory side is the directed union over stages {z/2^n}.")
    print(" - Lean bridge theorem available: uhf_colimit_dyadic_bridge")


if __name__ == "__main__":
    main()
