import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge

/-!
# Altland-Zirnbauer symmetry-class index

This module defines only the ten symmetry-class labels.  It does not define
Hamiltonians, antiunitary symmetries, stable phases, `KO` groups, or a
classification theorem.

The remaining theorem targets are independent:

* define the class-D Pfaffian bulk invariant and identify it with the signs of
  the Pfaffians at the particle-hole invariant momenta;
* construct stable gapped phases and prove the one-dimensional class-D
  homotopy classification;
* define the half-space boundary index and prove bulk-boundary equality;
* construct real `KO` groups and prove the genuine degree-eight Bott
  equivalence.

No spectral sequence or Fredholm model is part of the bare Bott-equivalence
statement; either may later be used as proof machinery or a realization.
-/

/-- The ten Altland-Zirnbauer symmetry-class labels. -/
inductive AZClass : Type
  | A
  | AIII
  | AI
  | BDI
  | D
  | DIII
  | AII
  | CII
  | C
  | CI

end InfoGeometry.Quantum.AltlandZirnbauerKTheoryBridge
