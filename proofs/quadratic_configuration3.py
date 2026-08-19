#!/usr/bin/env python3
"""Symbolic audit for the arity-3 complex quadric configuration presentation.

This is not a de Rham proof.  It checks the finite bookkeeping mirrored in
`QuadraticConfiguration3.lean`: edge generators, degrees, and the arity-three
cooperad edge maps for a two-point cluster plus one external point.
"""

from dataclasses import dataclass
from enum import Enum
from typing import Tuple


class Edge(str, Enum):
    e12 = "12"
    e13 = "13"
    e23 = "23"


class Kind(str, Enum):
    alpha = "alpha"
    beta = "beta"


class Block(str, Enum):
    pair12_3 = "(12)|3"
    pair13_2 = "(13)|2"
    pair23_1 = "(23)|1"


class Factor(str, Enum):
    outer = "outer"
    internal = "internal"


@dataclass(frozen=True)
class Gen:
    edge: Edge
    kind: Kind


def degree(D: int, g: Gen) -> int:
    if g.kind is Kind.alpha:
        return 1
    return D - 1


def cooperad_edge(block: Block, edge: Edge) -> Factor:
    internal = {
        Block.pair12_3: Edge.e12,
        Block.pair13_2: Edge.e13,
        Block.pair23_1: Edge.e23,
    }[block]
    return Factor.internal if edge is internal else Factor.outer


def cooperad_gen(block: Block, gen: Gen) -> Tuple[Factor, Kind]:
    return cooperad_edge(block, gen.edge), gen.kind


def main() -> None:
    D = 6
    assert D % 2 == 0
    gens = [Gen(e, k) for e in Edge for k in Kind]

    # Degree audit: α has degree 1, β has degree D-1 on every edge.
    for e in Edge:
        assert degree(D, Gen(e, Kind.alpha)) == 1
        assert degree(D, Gen(e, Kind.beta)) == D - 1

    # Cooperad audit: each two-point cluster has one internal edge and two outer edges.
    for b in Block:
        factors = [cooperad_edge(b, e) for e in Edge]
        assert factors.count(Factor.internal) == 1
        assert factors.count(Factor.outer) == 2

    # Label preservation audit.
    for b in Block:
        for g in gens:
            _, kind = cooperad_gen(b, g)
            assert kind is g.kind

    # The example discussed in the notes: collapse/insert the pair (23).
    assert cooperad_gen(Block.pair23_1, Gen(Edge.e23, Kind.alpha)) == (Factor.internal, Kind.alpha)
    assert cooperad_gen(Block.pair23_1, Gen(Edge.e23, Kind.beta)) == (Factor.internal, Kind.beta)
    assert cooperad_gen(Block.pair23_1, Gen(Edge.e12, Kind.alpha)) == (Factor.outer, Kind.alpha)
    assert cooperad_gen(Block.pair23_1, Gen(Edge.e13, Kind.alpha)) == (Factor.outer, Kind.alpha)

    print("quadratic_configuration3.py: finite arity-3 quadric configuration contracts passed")
    print("Analytic de Rham comparison, quadric angular class, Arnold relations, and full cooperad remain deferred_interfaces.")


if __name__ == "__main__":
    main()
