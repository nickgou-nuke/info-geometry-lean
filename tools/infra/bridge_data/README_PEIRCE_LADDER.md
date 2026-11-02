# Peirce projectors and ladder research packet

The original owner for this packet is
[Peirce/PeirceLadderOperators.lean](../../../lean/InfoGeometry/Peirce/PeirceLadderOperators.lean),
in namespace `PeirceLadder`. It contains a concrete real 2×2 complex structure
and complementary matrix projectors, alongside scalar and dimension metadata.
Its current types do not establish three fermionic modes, an SU(3) group action,
or a Standard Model representation.

Source reviewed on 2026-11-03 at commit
`214f7bcf733eaf4720913bc2c082936f2480d3fc`. The related owner paths below were
also inspected for the stated declarations. No fresh backend runs are recorded.
Follow the [repository search protocol](../../../docs/REPO_DEEP_SEARCH_PROTOCOL.md)
to distinguish this packet's scope from other noncommutative owners.

## Original owner's actual contents

| Surface | Current content and boundary |
|---|---|
| `ComplexStructure`, `standardComplexStructure` | A real 2×2 matrix `J` with `J * J = -1`, using `standardJ = [[0,-1],[1,0]]`. |
| `OP1`, `OP2` | The diagonal real matrix projectors onto the two coordinate axes. |
| `OP1_idempotent`, `OP2_idempotent`, `OP1_OP2_orthogonal`, `OP1_OP2_complete` | Concrete matrix proofs of idempotence, orthogonality, and sum equal to the identity. |
| `NilpotentLadder` | A record requiring real scalars `u`, `d` with `u² = d² = 0` and `u*d + d*u = 1`; no inhabitant is supplied. Over the reals these requirements are inconsistent, since square-zero real scalars are zero. This is not a noncommutative ladder witness. |
| `complexLadder` | The scalar expression `(u + J*d) / sqrt 2`; its scalar `J` is not the preceding matrix complex structure. |
| `fermionicFockDim`, `colorTripletDim` | Natural-number definitions `2^3` and `3`, without a Fock-space or representation construction. |
| `SU3ColorAction`, `standardSU3Color` | A type-and-dimension record whose supplied `gaugeGroup` is `Unit`; it has no group action or SU(3) laws. |
| `TripotentEigenvalue`, `tripotentToProjector` | A finite label type and a map to the named projectors. |
| `sandwichColorIsolation` | Ordinary matrix multiplication `OP1 * X * OP2`; no Zorn multiplication is used in this definition. |

The projector identities are concrete algebraic results. The scalar ladder
record and dimension labels do not extend them to the physical interpretation
of the original narrative.

## Related noncommutative owners

There are more substantial algebraic constructions elsewhere in the repository.
Use their carriers and hypotheses directly rather than inferring a global gap
from the original packet.

| Owner | Reviewed scope |
|---|---|
| [Algebra/PeirceLadderOperators.lean](../../../lean/InfoGeometry/Algebra/PeirceLadderOperators.lean) | Clifford-algebra expressions over `Cl(1,1)`, including a `J` with square `-1`, and ladder square-zero identities under explicit hypotheses. Its header explicitly limits split-octonion and particle-representation interpretations. |
| [OperatorAlgebra/LieJordanPeirceColimit.lean](../../../lean/InfoGeometry/OperatorAlgebra/LieJordanPeirceColimit.lean) | Native stage-one Witt creation/annihilation elements; `witt_pair_noncommutative_reflexive` proves square-zero, reflexive-pair identities, and noncommutation. It transports associated support, involution, and Casimir identities to the algebraic matrix-tower limit. |
| [Core/SuperGrassmannianSusy.lean](../../../lean/InfoGeometry/Core/SuperGrassmannianSusy.lean) | Conditional supercolor and color-boson identities over a ring, with explicit Moore–Penrose, cross-annihilation, or star-duality assumptions as required. These types do not by themselves construct a physical supersymmetry representation. |

For the wider owner map, see [REPOCONTENT.md](../../../REPOCONTENT.md).

## Tracked companion files

| File | Role |
|---|---|
| [peirce_ladder_formalization.py](../peirce_ladder_formalization.py) | Python research companion. |
| [galgebra_clifford_peirce.py](../galgebra_clifford_peirce.py) | GaAlgebra/Clifford computation companion. |
| [peirce_ladder_bridge.json](peirce_ladder_bridge.json) | Stored bridge data. |
| [PeirceLadder.v](PeirceLadder.v) | Coq source companion. |
| [PeirceLadderOperators.thy](PeirceLadderOperators.thy) | Isabelle/HOL source companion. |
| [peirce_dmodule.m2](peirce_dmodule.m2) | Macaulay2 source companion. |

The inventory does not certify matching semantics or successful execution in
every backend.

## Historical research goals

The original packet proposed connecting Peirce decomposition, nilpotent
ladders, Clifford/split-octonion expressions, and a color representation with
dimensions `1 + 3 + 3 + 1`. These remain research motivations. A fermionic CAR
statement uses an **anticommutator** and needs an actual operator carrier,
adjoint, and the requisite relations. A color interpretation needs a defined
group and representation action, not only the number three.

The complete earlier narrative remains in the
[historical packet](https://github.com/nickgou-nuke/info-geometry-lean/blob/214f7bcf733eaf4720913bc2c082936f2480d3fc/tools/infra/bridge_data/README_PEIRCE_LADDER.md).
Its full cross-system and physical completion claims are not current proof
status.

## Targeted verification

From the repository root, after dependency setup:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Peirce.PeirceLadderOperators
```

Build related owners separately if they are part of the intended change. See
the [root build guide](../../../README.md); do not equate a successful build of
this limited owner with a proof of the broader research goals.
