/-
InfoGeometry/Optics/FiniteJonesErlanger.lean

Erlanger invariance for the finite Jones model.

This module proves that the Brewster/Drazin core projector is fixed by
phase-linear Jones transports that preserve the Fresnel `s/p` splitting.

General Jones transports need not fix the `s` projector; they transport it
covariantly to another projector. The fixed-projector theorem belongs to the
diagonal phase-centralizer subgroup.
-/

import Mathlib
import InfoGeometry.Optics.FiniteJonesModel

noncomputable section

namespace InfoGeometry.Optics.FiniteJonesErlanger

open InfoGeometry.Optics.FiniteJonesModel

/-! ## 1. Invertible transport and conjugation -/

/--
A lightweight invertible transport.
-/
structure InvertibleTransport
    (Op : Type*) [Monoid Op] where
  val : Op
  inv : Op
  val_inv : val * inv = 1
  inv_val : inv * val = 1

namespace InvertibleTransport

variable {Op : Type*} [Monoid Op]

/-- Conjugation by an invertible transport. -/
def conjugate
    (U : InvertibleTransport Op)
    (T : Op) : Op :=
  U.val * T * U.inv

/-- If an operator commutes with the transport, it is fixed by conjugation. -/
theorem conjugate_fixed_of_commute
    (U : InvertibleTransport Op)
    (P : Op)
    (hcomm : U.val * P = P * U.val) :
    U.conjugate P = P := by
  dsimp [conjugate]
  calc
    U.val * P * U.inv
        = P * U.val * U.inv := by rw [hcomm]
    _ = P * (U.val * U.inv) := by rw [mul_assoc]
    _ = P * 1 := by rw [U.val_inv]
    _ = P := by simp

/--
Conjugation transports projectors to projectors.
This is the covariance theorem for general invertible Jones transports.
-/
theorem conjugate_preserves_idempotent
    (U : InvertibleTransport Op)
    {P : Op}
    (hP : P * P = P) :
    U.conjugate P * U.conjugate P = U.conjugate P := by
  dsimp [conjugate]
  calc
    (U.val * P * U.inv) * (U.val * P * U.inv)
        = U.val * P * (U.inv * U.val) * P * U.inv := by
            simp only [mul_assoc]
    _ = U.val * P * 1 * P * U.inv := by
            rw [U.inv_val]
    _ = U.val * (P * P) * U.inv := by
            simp only [mul_assoc, mul_one]
    _ = U.val * P * U.inv := by
            rw [hP]

end InvertibleTransport

/-! ## 2. Diagonal Jones phase transports -/

/--
A diagonal Jones transport in the `s/p` basis.

For physical phase gates one usually has `|a| = |b| = 1`, but the algebraic
conjugation theorem only needs `a` and `b` to be nonzero.
-/
def diagonalJonesTransport
    (a b : ℂ)
    (ha : a ≠ 0)
    (hb : b ≠ 0) :
    InvertibleTransport JonesMat where
  val := diagJones a b
  inv := diagJones a⁻¹ b⁻¹
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagJones, Matrix.mul_apply, ha, hb]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagJones, Matrix.mul_apply, ha, hb]

/-- Product of diagonal Jones matrices. -/
theorem diagJones_mul
    (a b c d : ℂ) :
    diagJones a b * diagJones c d =
      diagJones (a * c) (b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagJones, Matrix.mul_apply]

/-- Diagonal Jones transports commute with the `s` projector. -/
theorem diagJones_commutes_sProjector
    (a b : ℂ) :
    diagJones a b * sProjector =
      sProjector * diagJones a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagJones, sProjector, Matrix.mul_apply]

/-- Diagonal Jones transports commute with the `p` projector. -/
theorem diagJones_commutes_pProjector
    (a b : ℂ) :
    diagJones a b * pProjector =
      pProjector * diagJones a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagJones, pProjector, Matrix.mul_apply]

/-! ## 3. Phase axis and phase-linearity -/

/-- The finite `s/p` phase axis, `χ = P_s - P_p`. -/
def spPhaseAxis : JonesMat :=
  sProjector - pProjector

/-- Phase-linearity relative to the `s/p` phase axis. -/
def IsSPPhaseLinear
    (T : JonesMat) : Prop :=
  T * spPhaseAxis = spPhaseAxis * T

/-- Diagonal Jones transports are phase-linear relative to the `s/p` axis. -/
theorem diagJones_isSPPhaseLinear
    (a b : ℂ) :
    IsSPPhaseLinear (diagJones a b) := by
  unfold IsSPPhaseLinear spPhaseAxis
  calc
    diagJones a b * (sProjector - pProjector)
        = diagJones a b * sProjector - diagJones a b * pProjector := by
            rw [mul_sub]
    _ = sProjector * diagJones a b - pProjector * diagJones a b := by
            rw [diagJones_commutes_sProjector, diagJones_commutes_pProjector]
    _ = (sProjector - pProjector) * diagJones a b := by
            rw [sub_mul]

/-! ## 4. Invariance and covariance -/

/--
Under an arbitrary invertible Jones transport, the Brewster core is transported
covariantly to another projector.
-/
theorem conjugated_sProjector_is_projector
    (U : InvertibleTransport JonesMat) :
    U.conjugate sProjector * U.conjugate sProjector =
      U.conjugate sProjector :=
  InvertibleTransport.conjugate_preserves_idempotent U sProjector_idem

/--
The Brewster/Drazin core projector `P_s` is strictly invariant under diagonal
phase-linear Jones transports.
-/
theorem sProjector_invariant_under_diagonalJonesTransport
    (a b : ℂ)
    (ha : a ≠ 0)
    (hb : b ≠ 0) :
    (diagonalJonesTransport a b ha hb).conjugate sProjector =
      sProjector := by
  apply InvertibleTransport.conjugate_fixed_of_commute
  exact diagJones_commutes_sProjector a b

/--
The killed `p` projector is also strictly invariant under diagonal phase-linear
Jones transports.
-/
theorem pProjector_invariant_under_diagonalJonesTransport
    (a b : ℂ)
    (ha : a ≠ 0)
    (hb : b ≠ 0) :
    (diagonalJonesTransport a b ha hb).conjugate pProjector =
      pProjector := by
  apply InvertibleTransport.conjugate_fixed_of_commute
  exact diagJones_commutes_pProjector a b

/--
The Brewster reflection matrix itself is invariant under diagonal phase-linear
Jones transports.
-/
theorem brewsterMatrix_invariant_under_diagonalJonesTransport
    (a b rs : ℂ)
    (ha : a ≠ 0)
    (hb : b ≠ 0) :
    (diagonalJonesTransport a b ha hb).conjugate (brewsterMatrix rs) =
      brewsterMatrix rs := by
  dsimp [InvertibleTransport.conjugate, diagonalJonesTransport]
  rw [brewsterMatrix, diagJones_mul, diagJones_mul]
  have hs : (a * rs) * a⁻¹ = rs := by
    calc
      (a * rs) * a⁻¹ = rs * (a * a⁻¹) := by ring
      _ = rs * 1 := by rw [mul_inv_cancel₀ ha]
      _ = rs := by ring
  simp [hs]

/-! ## 5. Owner target -/

/--
Owner target for the finite Jones Erlanger layer.
-/
def FiniteJonesErlangerOwnerTarget : Prop :=
  (∀ a b : ℂ, IsSPPhaseLinear (diagJones a b))
  ∧
  (∀ (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0),
    (diagonalJonesTransport a b ha hb).conjugate sProjector =
      sProjector)
  ∧
  (∀ (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0),
    (diagonalJonesTransport a b ha hb).conjugate pProjector =
      pProjector)
  ∧
  (∀ (a b rs : ℂ) (ha : a ≠ 0) (hb : b ≠ 0),
    (diagonalJonesTransport a b ha hb).conjugate (brewsterMatrix rs) =
      brewsterMatrix rs)

/-- The finite Jones Erlanger owner target. -/
theorem finiteJonesErlangerOwnerTarget :
    FiniteJonesErlangerOwnerTarget := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    exact diagJones_isSPPhaseLinear a b
  · intro a b ha hb
    exact sProjector_invariant_under_diagonalJonesTransport a b ha hb
  · intro a b ha hb
    exact pProjector_invariant_under_diagonalJonesTransport a b ha hb
  · intro a b rs ha hb
    exact brewsterMatrix_invariant_under_diagonalJonesTransport a b rs ha hb

end InfoGeometry.Optics.FiniteJonesErlanger
