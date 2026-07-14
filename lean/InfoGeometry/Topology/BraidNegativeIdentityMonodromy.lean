import Mathlib
import InfoGeometry.Topology.MajoranaBraidGroup

open Matrix Complex

/-!
# Braid full twists as negative-identity spinor monodromy

This file connects the existing Pauli/biquaternion root equation `X^k = -I`
to an Artin-braid stepping stone.  The local spinor half-twist gate is the real
form of `iσ₂`; it squares to `-I`.  Mapping braid generators uniformly to this
phase channel satisfies the Artin relation, and the B₂/B₃ central full twists
act by negative identity.
-/

noncomputable section

namespace BraidNegativeIdentityMonodromy

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Real form of `iσ₂`, used as a spinor half-twist gate. -/
def spinorHalfTwist : M2C := !![0, 1; -1, 0]

/-- A local spinor half twist squares to the negative identity. -/
theorem spinorHalfTwist_sq : spinorHalfTwist * spinorHalfTwist = -(1 : M2C) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [spinorHalfTwist]

/-- Therefore four half twists return to the positive identity. -/
theorem spinorHalfTwist_fourth : spinorHalfTwist ^ 4 = (1 : M2C) := by
  have h2 : spinorHalfTwist ^ 2 = -(1 : M2C) := by
    simpa [pow_two] using spinorHalfTwist_sq
  rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, h2]
  simp

/-- Uniform spinor representation of an Artin generator. -/
def ρσ (_i : ℕ) : M2C := spinorHalfTwist

/-- The uniform spinor phase channel satisfies the adjacent Artin relation. -/
theorem spinor_adjacent_artin (i : ℕ) :
    ρσ i * ρσ (i + 1) * ρσ i = ρσ (i + 1) * ρσ i * ρσ (i + 1) := by
  simp [ρσ]

/-- B₂: the central full twist `σ₁²` acts by `-I`. -/
theorem B2_full_twist_negative : ρσ 0 * ρσ 0 = -(1 : M2C) := by
  simpa [ρσ] using spinorHalfTwist_sq

/-- B₃ Garside half twist `Δ = σ₁σ₂σ₁` in the uniform spinor channel. -/
def DeltaB3 : M2C := ρσ 0 * ρσ 1 * ρσ 0

/-- The B₃ central full twist `Δ²` acts by `-I`. -/
theorem B3_full_twist_negative : DeltaB3 * DeltaB3 = -(1 : M2C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [DeltaB3, ρσ, spinorHalfTwist, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-- Algebraic root stepping stone: if a matrix has `d`-th power `-I`, then its `2d`-th power is `I`. -/
theorem negative_root_doubles_to_identity (A : M2C) (d : ℕ) (h : A ^ d = -(1 : M2C)) :
    A ^ (2 * d) = (1 : M2C) := by
  rw [show 2 * d = d + d by rw [two_mul], pow_add, h]
  simp

/-- The imported finite Majorana bivectors give an 8×8 integer negative-identity law. -/
theorem majorana_bivectors_negative_identity_bridge :
    InfoGeometry.GrandUnification.MajoranaBraidGroup.bivector12 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.bivector12 =
      -(1 : InfoGeometry.GrandUnification.MajoranaBraidGroup.M8Z) ∧
    InfoGeometry.GrandUnification.MajoranaBraidGroup.bivector23 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.bivector23 =
      -(1 : InfoGeometry.GrandUnification.MajoranaBraidGroup.M8Z) := by
  exact InfoGeometry.GrandUnification.MajoranaBraidGroup.majorana_bivector_squares

/-- The imported finite Majorana braid gates have projective inverse numerators. -/
theorem majorana_projective_inverse_bridge :
    InfoGeometry.GrandUnification.MajoranaBraidGroup.braid12 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.braid12InvNumerator =
      (2 : ℤ) • (1 : InfoGeometry.GrandUnification.MajoranaBraidGroup.M8Z) ∧
    InfoGeometry.GrandUnification.MajoranaBraidGroup.braid23 *
        InfoGeometry.GrandUnification.MajoranaBraidGroup.braid23InvNumerator =
      (2 : ℤ) • (1 : InfoGeometry.GrandUnification.MajoranaBraidGroup.M8Z) := by
  exact InfoGeometry.GrandUnification.MajoranaBraidGroup.majorana_projective_inverses

#check spinorHalfTwist_sq
#check B2_full_twist_negative
#check B3_full_twist_negative
#check negative_root_doubles_to_identity

end BraidNegativeIdentityMonodromy
