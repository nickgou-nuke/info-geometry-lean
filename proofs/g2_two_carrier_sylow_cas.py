"""Extract a concrete order-64 subgroup from the verified F2 Zorn carrier.

This is a CAS source artifact only.  It uses the same generator-image
constraints as ``tools/sympy/g2_2_automorphism_theorem.py`` and exports the
actual 8-coordinate images needed by the Lean owner.  It does not assert a
BN-pair or identify the subgroup with a Borel until those relations are
checked separately.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "g2_verified", ROOT / "tools/sympy/g2_2_automorphism_theorem.py"
)
g2 = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(g2)

Vec8 = g2.Vec8


def enc(x: Vec8) -> int:
    return sum(bit << i for i, bit in enumerate(x))


def dec(x: int) -> Vec8:
    return tuple((x >> i) & 1 for i in range(8))  # type: ignore[return-value]


def linear(images: tuple[int, ...], x: int) -> int:
    out = 0
    for i in range(8):
        if (x >> i) & 1:
            out ^= images[i]
    return out


IDENTITY = tuple(1 << i for i in range(8))


def compose(f: tuple[int, ...], h: tuple[int, ...]) -> tuple[int, ...]:
    """Composition f ∘ h, represented by images of the coordinate basis."""
    return tuple(linear(f, x) for x in h)


def enumerate_automorphisms() -> list[tuple[int, ...]]:
    nilpotents = [x for x in g2.ALL if g2.mul(x, x) == g2.ZERO]
    pairs = []
    for a in nilpotents:
        for c in nilpotents:
            e = g2.mul(a, c)
            f = g2.mul(c, a)
            if g2.add(e, f) == g2.ONE and g2.mul(e, e) == e and g2.mul(f, f) == f:
                pairs.append((a, c, e, f))

    result = []
    for a, c, e, f in pairs:
        for b in nilpotents:
            d2 = g2.mul(a, b)
            if d2 == g2.ZERO or g2.mul(b, a) != d2:
                continue
            if not (g2.mul(e, b) == b and g2.mul(b, f) == b
                    and g2.mul(f, b) == g2.ZERO and g2.mul(b, e) == g2.ZERO):
                continue
            for d in nilpotents:
                if g2.mul(b, d) != e or g2.mul(d, b) != f:
                    continue
                if g2.mul(a, d) != g2.ZERO or g2.mul(d, a) != g2.ZERO:
                    continue
                u2 = g2.mul(c, d)
                if u2 == g2.ZERO or g2.mul(d, c) != u2:
                    continue
                if not (g2.mul(f, d) == d and g2.mul(d, e) == d
                        and g2.mul(e, d) == g2.ZERO and g2.mul(d, f) == g2.ZERO):
                    continue
                images = (e, f, a, b, u2, c, d, d2)
                if g2.rank(images) != 8:
                    continue
                if all(
                    dec(linear(tuple(enc(v) for v in images), enc(g2.mul(x, y))))
                    == g2.mul(dec(linear(tuple(enc(v) for v in images), enc(x))),
                              dec(linear(tuple(enc(v) for v in images), enc(y))))
                    for x in g2.BASIS for y in g2.BASIS
                ):
                    result.append(tuple(enc(v) for v in images))
    assert len(result) == 12096
    assert len(set(result)) == 12096
    return result


def closure(gens: list[tuple[int, ...]], limit: int = 65) -> set[tuple[int, ...]]:
    seen = {IDENTITY}
    frontier = [IDENTITY]
    while frontier:
        x = frontier.pop()
        for y in gens:
            z = compose(x, y)
            if z not in seen:
                seen.add(z)
                if len(seen) >= limit:
                    return seen
                frontier.append(z)
    return seen


def main() -> None:
    auts = enumerate_automorphisms()
    aset = set(auts)
    involutions = [g for g in auts if compose(g, g) == IDENTITY and g != IDENTITY]
    generators: list[tuple[int, ...]] = []
    current = {IDENTITY}
    for candidate in involutions:
        trial = closure(generators + [candidate], 65)
        if len(trial) > len(current) and len(trial) <= 64:
            generators.append(candidate)
            current = trial
            if len(current) == 64:
                break
    if len(current) != 64:
        raise RuntimeError(f"greedy involution extraction reached {len(current)}")
    assert current <= aset
    print(f"automorphism_count={len(auts)}")
    print(f"sylow_candidate_order={len(current)}")
    print(f"generator_count={len(generators)}")
    for i, gen in enumerate(generators):
        print(f"generator_{i}=" + ",".join(map(str, gen)))


if __name__ == "__main__":
    main()
