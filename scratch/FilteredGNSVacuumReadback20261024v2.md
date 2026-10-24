# Filtered GNS vacuum readback v2

Uncompiled source candidate. V1 retained; use v2 instead, not both together.
No tests/builds/CAS/live edits. Independent AA and locked QA remain necessary.

Retains the native global vacuum norm-one, stage-independence, stage expectation,
bounded continuous functional, normalization and star-square positivity proofs.
Adds representedVacuumPositiveFunctional and representedVacuumState on the
existing representedCStarClosure, with representedVacuumState_stage readback.

The previously identified order boundary is addressed by genuine local instances:
CStarAlgebra.spectralOrder and CStarAlgebra.spectralOrderedRing from Mathlib
Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic. These use the closure's
existing native CStarAlgebra; no PartialOrder/StarOrderedRing or positivity
hypotheses are added. Local instance choice remains encoded in the State's type;
consumers should use the same spectral order when necessary.

PositiveLinearMap.mk₀ uses nonneg_iff_eq_star_mul_self to reduce positivity to
already-proved vector-functional positivity on star b * b, obtained by the
actual bounded operator adjoint inner-product identity. Normalization is proved
from the isometric stage vacuum norm, not supplied as a witness.

No faithfulness, traciality, modular dynamics, or new colimit carrier is claimed.
Source feasibility only: instance elaboration and all proofs await QA.
