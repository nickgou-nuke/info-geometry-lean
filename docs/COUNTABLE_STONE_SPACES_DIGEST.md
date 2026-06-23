# Countable Stone Spaces Digest

Source PDF:
`/home/goutev/Downloads/collection_for_formalization/Bulletin of London Math Soc - 2025 - Branman - Graphical models for topological groups  A case study on countable Stone.pdf`

This digest records the theorem-honest part of the paper that the repository
already formalizes.

## What the paper uses

The paper studies homeomorphism groups of countable Stone spaces and uses the
countable Stone-space structure as a 0-dimensional topological substrate.

The part that matches the existing repository owner layer is the product
topology on binary streams:

* the carrier is `ι → Bool`, specialized in the repo to `ℕ → Bool`;
* a basic open set is agreement on a finite coordinate set;
* these finite-coordinate cylinders form a neighborhood basis;
* intersecting all finite cylinders through a point isolates that point;
* principal ultrafilter evaluation is exact coordinate agreement.

## Existing Lean owner files

The following files already prove the canonical Mathlib-level facts:

* `lean/InfoGeometry/Canonical/PiCylinderMathlib.lean`
* `lean/InfoGeometry/Canonical/CantorCylinderTopology.lean`
* `lean/InfoGeometry/Canonical/StoneBridgeMathlib.lean`
* `lean/InfoGeometry/Canonical/StoneCantorMathlib.lean`
* `lean/InfoGeometry/Canonical/StoneDualityBooleanEval.lean`

The exact statements already verified include:

* `PiCylinderMathlib.nhds_hasBasis_canonicalCylinder`
* `PiCylinderMathlib.iInter_finset_canonicalCylinder`
* `CantorCylinderTopology.nhds_hasBasis_canonicalCylinder`
* `CantorCylinderTopology.iInter_finset_canonicalCylinder`
* `StoneBridgeMathlib.stonePointEquivBooleanHom`
* `StoneCantorMathlib.principalUltrafilter_prefixCylinder_eval`
* `StoneDualityBooleanEval.cantor_eval_true_iff_pointStoneFilter`

## What is not claimed

The paper’s group-theoretic classification of homeomorphism groups of countable
Stone spaces is not yet formalized in Lean in this repository.
No de Rham, symplectic, or Kaluza-Klein layer is attributed to this paper.

