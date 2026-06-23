#!/usr/bin/env python3
"""Finite witness for the rank-32 boundary carrier.

This mirrors `AmplituhedronBoundaryRank32.lean`: the carrier is the set
`{0, ..., 31}`, split into a chiral half `{0, ..., 15}` and an anti-chiral half
`{16, ..., 31}`.

It does not compute de Rham cohomology, amplituhedron volume, or an `N=4`
state-count theorem.
"""

from __future__ import annotations


def main() -> None:
    states = list(range(32))
    chiral = [s for s in states if s < 16]
    anti_chiral = [s for s in states if 16 <= s]

    assert len(states) == 32
    assert len(chiral) == 16
    assert len(anti_chiral) == 16
    assert set(chiral).isdisjoint(anti_chiral)
    assert sorted(chiral + anti_chiral) == states

    print("Amplituhedron rank-32 finite carrier witness")
    print(f"states={len(states)}")
    print(f"chiral={len(chiral)}")
    print(f"anti_chiral={len(anti_chiral)}")
    print("partition=disjoint_exhaustive")
    print("status=ok")


if __name__ == "__main__":
    main()
