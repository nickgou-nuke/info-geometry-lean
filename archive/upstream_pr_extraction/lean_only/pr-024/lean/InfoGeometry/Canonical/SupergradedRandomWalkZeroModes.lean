import Mathlib

/-!
# InfoGeometry.Canonical.SupergradedRandomWalkZeroModes

Finite supertrace and Drazin-Hodge zero-mode readbacks.
-/

noncomputable section

namespace InfoGeometry.Canonical.SupergradedRandomWalkZeroModes

open scoped BigOperators

/-- Supergraded finite state space. -/
structure SuperLattice (V : Type*) where
  parity : V → Bool

/-- Even states have sign `1`, odd states have sign `-1`. -/
def paritySign {V : Type*} (S : SuperLattice V) (v : V) : ℝ :=
  if S.parity v then -1 else 1

/-- Finite supertrace. -/
def superTrace {V : Type*} [Fintype V] (S : SuperLattice V) (M : Matrix V V ℝ) : ℝ :=
  Finset.univ.sum fun v : V => paritySign S v * M v v

/-- Supertrace of the zero matrix is zero. -/
theorem superTrace_zero {V : Type*} [Fintype V] (S : SuperLattice V) :
    superTrace S (0 : Matrix V V ℝ) = 0 := by
  simp [superTrace]

/-- Drazin-Hodge projector data. -/
structure DrazinHodgeProjector (V : Type*) [Fintype V] [DecidableEq V] where
  L : Matrix V V ℝ
  LD : Matrix V V ℝ
  H : Matrix V V ℝ
  H_def : H = 1 - L * LD
  H_idempotent : H * H = H

/-- Zero-mode index is the supertrace of `H`. -/
def zeroModeIndex {V : Type*} [Fintype V] [DecidableEq V] (S : SuperLattice V)
    (D : DrazinHodgeProjector V) : ℝ :=
  superTrace S D.H

/-- Readback theorem for the zero-mode index. -/
theorem zeroModeIndex_eq_superTrace {V : Type*} [Fintype V] [DecidableEq V] (S : SuperLattice V)
    (D : DrazinHodgeProjector V) :
    zeroModeIndex S D = superTrace S D.H := by
  rfl

end InfoGeometry.Canonical.SupergradedRandomWalkZeroModes
