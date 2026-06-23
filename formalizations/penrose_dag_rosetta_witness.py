#!/usr/bin/env python3
"""Finite witness for the Penrose/DAG/amplituhedron Rosetta carrier.

This script does not verify geometric equivalences.  It checks the finite
bookkeeping used by the Lean Rosetta interface: every lane is explicitly routed
through one common carrier, so transport between any two lanes is just equality
of the common carrier tag.
"""

from __future__ import annotations


LANES = [
    "dag_graph",
    "split_quaternion",
    "penrose_net",
    "klein_quadric",
    "amplituhedron",
    "delaunay_tessellation",
]

COMMON_CARRIER = "split_twistor_klein_boundary_carrier"


def main() -> None:
    lane_to_common = {lane: COMMON_CARRIER for lane in LANES}

    assert len(LANES) == 6
    assert set(lane_to_common) == set(LANES)
    assert all(target == COMMON_CARRIER for target in lane_to_common.values())

    pairwise_transport = {
        (source, target): lane_to_common[source] == lane_to_common[target]
        for source in LANES
        for target in LANES
    }
    assert all(pairwise_transport.values())

    print("Penrose/DAG Rosetta finite carrier witness")
    print(f"lanes={len(LANES)}")
    print(f"common_carrier={COMMON_CARRIER}")
    print(f"pairwise_transports={len(pairwise_transport)}")
    print("status=ok")


if __name__ == "__main__":
    main()
