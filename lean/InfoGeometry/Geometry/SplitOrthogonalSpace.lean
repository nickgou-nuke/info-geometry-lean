/-
InfoGeometry/Geometry/SplitOrthogonalSpace.lean

Explicit split-orthogonal chart carriers for the Narain / O(n,n) tower.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Algebra.Module.Basic
import InfoGeometry.Algebraic.SplitQuadraticForm

noncomputable section

namespace InfoGeometry.Geometry.Cartan

open InfoGeometry.Algebraic.SplitSignature

/--
Concrete matrix chart for the split-orthogonal Cartan symmetric-space lane.

The actual quotient `O(n,n)/(O(n) × O(n))` is not postulated here as an abstract
carrier.  Downstream finite computations use the canonical mathlib matrix chart
`Matrix (Fin n) (Fin n) ℝ`; quotient-level structure should be added only by a
module that constructs the relevant group action.
-/
abbrev SplitOrthogonalCartanSpace (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℝ

/--
Concrete finite boundary chart for split-orthogonal degeneration.

This is a mathlib-grounded coordinate carrier, not an opaque boundary type.
-/
abbrev SplitOrthogonalBoundary (n : ℕ) : Type :=
  Fin n → ℝ

/-- The zero Cartan chart. -/
def zeroCartanChart (n : ℕ) : SplitOrthogonalCartanSpace n :=
  0

/-- The zero boundary chart. -/
def zeroBoundaryChart (n : ℕ) : SplitOrthogonalBoundary n :=
  0

@[simp] theorem zeroCartanChart_apply (n : ℕ) (i j : Fin n) :
    zeroCartanChart n i j = 0 :=
  rfl

@[simp] theorem zeroBoundaryChart_apply (n : ℕ) (i : Fin n) :
    zeroBoundaryChart n i = 0 :=
  rfl

end InfoGeometry.Geometry.Cartan
