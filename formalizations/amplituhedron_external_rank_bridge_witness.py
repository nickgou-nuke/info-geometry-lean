#!/usr/bin/env python3
"""Finite witness for external rank data matching the rank-32 carrier.

This mirrors `AmplituhedronBoundaryExternalRankBridge.lean`.
It checks only arithmetic:

    sum([1,2,1,1,2,1,0,0,0]) = 8
    8 * 4 = 32
    len(range(32)) = 32

It does not certify that the vector is the actual de Rham cohomology of a
quadric complement.
"""

from __future__ import annotations


def main() -> None:
    betti_numbers = [1, 2, 1, 1, 2, 1, 0, 0, 0]
    ambient_dim = 8
    spin_tiling_multiplicity = 4
    boundary_carrier = list(range(32))

    local_rank = sum(betti_numbers)
    spin_tiled_rank = local_rank * spin_tiling_multiplicity

    assert ambient_dim == 8
    assert local_rank == 8
    assert spin_tiled_rank == 32
    assert len(boundary_carrier) == 32
    assert spin_tiled_rank == len(boundary_carrier)

    print("External rank to boundary carrier witness")
    print(f"ambient_dim={ambient_dim}")
    print(f"local_rank={local_rank}")
    print(f"spin_tiling_multiplicity={spin_tiling_multiplicity}")
    print(f"spin_tiled_rank={spin_tiled_rank}")
    print(f"boundary_carrier={len(boundary_carrier)}")
    print("status=ok")


if __name__ == "__main__":
    main()
