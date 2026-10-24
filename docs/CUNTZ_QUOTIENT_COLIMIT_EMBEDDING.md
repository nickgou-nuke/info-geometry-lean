# Corrected quotient embedding of the algebraic matrix colimit

Contract: construct an injective complex star-algebra homomorphism from the
existing `CuntzMatrixAlgebraicStarColimit.Carrier` to `ComplexStarCuntzAlg Bool`.
Its restriction to a finite stage is `stageHom n` composed with the inverse
of `BitWordComplexCStarTowerNaturalityBridge.stageStarAlgEquiv n`.

Source facts: `stageHom_bond` proves right-extension compatibility;
`stageStarAlgEquiv_bond` transports that same bond to `concreteStep`.
`CuntzMatrixTraceTower.map_succ` supplies arbitrary-stage compatibility.
Mathlib `DirectLimit.Algebra.lift` constructs the actual algebra map.
Star preservation and injectivity descend by direct-limit induction from
the finite star maps and `stageHom_injective`.

The image theorem identifies the linear range with the existing
`CuntzComplexStarBinaryCoreProjection.core`, the span of equal-length word
pairs. Finite matrix expansions give containment; individual matrix units
give all span generators, and the linear range is a submodule.

This is an algebraic colimit claim. It does not assert norm completion,
positivity or KMS.
The parent locked audit build passed (9402 jobs, exit 0), including all 13
selected declaration reports with standard foundational axioms only.
All three new Lean files pass the strict trap screen. The independent
mathematical review passed both the lift and exact-image proofs.
Independent QA accepted this limited scope after its own locked build
(9402 jobs, exit 0). Both logs contain 13 axiom reports, with union exactly
`[propext, Classical.choice, Quot.sound]`, and no warnings in these new owners.
Logs: `/tmp/cuntz-colimit-audit.log` and `/tmp/cuntz-colimit-qa.log`.
