#!/usr/bin/env python3
"""Exact automorphism-tower sandbox for S3.

The purpose is intentionally bounded and foundational:
* enumerate S3 as permutations of {0,1,2};
* enumerate all group automorphisms by brute force over all 6! bijections fixing
  the identity;
* enumerate inner automorphisms;
* verify Aut(S3)=Inn(S3) and |Aut(S3)|=|S3|=6;
* write a JSON certificate consumed by readback lanes.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

Perm = tuple[int, ...]


def compose(p: Perm, q: Perm) -> Perm:
    return tuple(p[i] for i in q)  # p ∘ q


def inv(p: Perm) -> Perm:
    r = [0, 0, 0]
    for i, v in enumerate(p):
        r[v] = i
    return tuple(r)


S3 = list(itertools.permutations(range(3)))
E = (0, 1, 2)
assert E in S3
MULT = {(p, q): compose(p, q) for p in S3 for q in S3}


def is_hom(f: dict[Perm, Perm]) -> bool:
    return all(f[MULT[p, q]] == MULT[f[p], f[q]] for p in S3 for q in S3)


def all_automorphisms() -> list[dict[Perm, Perm]]:
    rest = [g for g in S3 if g != E]
    out = []
    for images in itertools.permutations(rest):
        f = {E: E, **dict(zip(rest, images))}
        if is_hom(f):
            out.append(f)
    return out


def inner_automorphism(g: Perm) -> dict[Perm, Perm]:
    gi = inv(g)
    return {x: MULT[MULT[g, x], gi] for x in S3}


def canonical_aut(f: dict[Perm, Perm]) -> tuple[Perm, ...]:
    return tuple(f[x] for x in S3)


def main() -> None:
    auts = all_automorphisms()
    inners = [inner_automorphism(g) for g in S3]
    aut_set = {canonical_aut(f) for f in auts}
    inner_set = {canonical_aut(f) for f in inners}
    center = [g for g in S3 if all(MULT[g, x] == MULT[x, g] for x in S3)]
    certificate = {
        "group": "S3 = Equiv.Perm(Fin 3)",
        "order": len(S3),
        "automorphism_count": len(auts),
        "inner_automorphism_count": len(inner_set),
        "center_count": len(center),
        "center_trivial": center == [E],
        "all_automorphisms_inner": aut_set == inner_set,
        "complete_group_certificate_bounded": center == [E] and aut_set == inner_set,
        "bounded_tower_cardinals": [len(S3), len(auts), len(auts)],
        "claim_boundary": "Finite S3 complete-group sandbox only; no general/transfinite automorphism-tower theorem claimed.",
    }
    assert certificate["order"] == 6
    assert certificate["automorphism_count"] == 6
    assert certificate["inner_automorphism_count"] == 6
    assert certificate["center_trivial"]
    assert certificate["all_automorphisms_inner"]
    out = Path(__file__).resolve().parent / "artifacts" / "automorphism_tower_s3_certificate.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
    print("SYMPY_AUTOMORPHISM_TOWER_S3_COMPLETE_OK")
    print(json.dumps(certificate, sort_keys=True))


if __name__ == "__main__":
    main()
