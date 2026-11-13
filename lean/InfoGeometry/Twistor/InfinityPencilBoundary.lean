/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealInfinityMatrixPencil
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentDefect
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Tripotency and the zero-mode boundary of the real infinity pencil

The existing four-dimensional real pencil satisfies `N(Λ)² = -Λ • 1`.
Its only tripotent member has `Λ = -1`, so its zero-color polynomial is zero.
The flat member is nonzero and square-zero; its zero-color polynomial is the
identity, whose range is not its kernel. These statements obstruct treating
the pencil itself as a tripotent with a nonzero third spectral sector;
they do not exclude a separately constructed operator with additional data.

The polynomial theorem is inherited from the arbitrary noncommutative
algebra owner. No complex scalar, spacetime horizon, or cosmological
interpretation of the pencil parameter is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.InfinityPencilBoundary

open InfoGeometry.Twistor.RealInfinityMatrixPencil
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Quantum.NeutralKreinMajoranaFrame

theorem raisedInfinityMatrix_cube (Λ : ℝ) :
    raisedInfinityMatrix Λ * raisedInfinityMatrix Λ * raisedInfinityMatrix Λ =
      (-Λ) • raisedInfinityMatrix Λ := by
  rw [raisedInfinityMatrix_sq, smul_mul_assoc, one_mul]

/-- Exact tripotency criterion for the existing pencil. -/
theorem raisedInfinityMatrix_tripotent_iff (Λ : ℝ) :
    raisedInfinityMatrix Λ * raisedInfinityMatrix Λ * raisedInfinityMatrix Λ =
      raisedInfinityMatrix Λ ↔ Λ = -1 := by
  have h := tripotentDefect_eq_zero_iff_scalar_one
    (raisedInfinityMatrix_sq Λ) (raisedInfinityMatrix_ne_zero Λ)
  simpa only [tripotentDefect, sub_eq_zero, neg_eq_iff_eq_neg] using h

theorem raisedInfinityMatrix_zeroColor (Λ : ℝ) :
    triProj0 (raisedInfinityMatrix Λ) = (1 + Λ) • (1 : DoubledMat4R) := by
  simpa only [sub_neg_eq_add] using
    triProj0_of_square_eq_smul_one (raisedInfinityMatrix_sq Λ)

/-- Tripotency in this pencil forces the putative third sector to vanish. -/
theorem raisedInfinityMatrix_tripotent_zeroColor (Λ : ℝ)
    (htri : raisedInfinityMatrix Λ * raisedInfinityMatrix Λ * raisedInfinityMatrix Λ =
      raisedInfinityMatrix Λ) : triProj0 (raisedInfinityMatrix Λ) = 0 := by
  rw [(raisedInfinityMatrix_tripotent_iff Λ).mp htri, raisedInfinityMatrix_zeroColor]
  simp

theorem no_tripotent_with_nonzero_zeroColor :
    ¬ ∃ Λ : ℝ,
      raisedInfinityMatrix Λ * raisedInfinityMatrix Λ * raisedInfinityMatrix Λ =
        raisedInfinityMatrix Λ ∧ triProj0 (raisedInfinityMatrix Λ) ≠ 0 := by
  rintro ⟨Λ, htri, hnonzero⟩
  exact hnonzero (raisedInfinityMatrix_tripotent_zeroColor Λ htri)

theorem flat_not_tripotent :
    raisedInfinityMatrix 0 * raisedInfinityMatrix 0 * raisedInfinityMatrix 0 ≠
      raisedInfinityMatrix 0 := by
  rw [ne_eq, raisedInfinityMatrix_tripotent_iff]
  norm_num

theorem flat_zeroColor_eq_one : triProj0 (raisedInfinityMatrix 0) = 1 := by
  simp [raisedInfinityMatrix_zeroColor]

/-- The existing matrix acts on its actual native real vector carrier. -/
def pencilEnd (Λ : ℝ) : Module.End ℝ (Carrier 2 → ℝ) :=
  Matrix.toLin' (raisedInfinityMatrix Λ)

@[simp] theorem pencilEnd_apply (Λ : ℝ) (v : Carrier 2 → ℝ) :
    pencilEnd Λ v = (raisedInfinityMatrix Λ).mulVec v := rfl

theorem pencilEnd_sq (Λ : ℝ) :
    pencilEnd Λ * pencilEnd Λ = (-Λ) • (1 : Module.End ℝ (Carrier 2 → ℝ)) := by
  apply LinearMap.ext
  intro v
  exact raisedInfinityMatrix_mulVec_twice Λ v

theorem pencilEnd_ne_zero (Λ : ℝ) : pencilEnd Λ ≠ 0 := by
  intro h
  apply raisedInfinityMatrix_ne_zero Λ
  have h' := congrArg (Matrix.toLin' : DoubledMat4R ≃ₗ[ℝ]
    Module.End ℝ (Carrier 2 → ℝ)).symm h
  simpa [pencilEnd] using h'

/-- Square-zero gives an inclusion, not a direct-sum decomposition. -/
theorem flat_range_le_ker : LinearMap.range (pencilEnd 0) ≤ LinearMap.ker (pencilEnd 0) := by
  rw [LinearMap.range_le_ker_iff]
  change pencilEnd 0 * pencilEnd 0 = 0
  simpa using pencilEnd_sq 0

/-- The naive zero-color polynomial fails the actual kernel characterization. -/
theorem flat_zeroColor_range_ne_ker :
    LinearMap.range (1 - pencilEnd 0 * pencilEnd 0) ≠ LinearMap.ker (pencilEnd 0) := by
  have hs : pencilEnd 0 * pencilEnd 0 = 0 := by simpa using pencilEnd_sq 0
  rw [hs, sub_zero]
  intro h
  apply pencilEnd_ne_zero 0
  apply LinearMap.ext
  intro v
  have hv : v ∈ LinearMap.range (1 : Module.End ℝ (Carrier 2 → ℝ)) := ⟨v, rfl⟩
  rw [h] at hv
  exact hv

/-- Nonzero parameters have a trivial kernel, using the owned square law. -/
theorem pencilEnd_ker_eq_bot (Λ : ℝ) (hΛ : Λ ≠ 0) :
    LinearMap.ker (pencilEnd Λ) = ⊥ := by
  apply le_antisymm
  · intro v hv
    change pencilEnd Λ v = 0 at hv
    have htwice := raisedInfinityMatrix_mulVec_twice Λ v
    change pencilEnd Λ (pencilEnd Λ v) = (-Λ) • v at htwice
    rw [hv, map_zero] at htwice
    have hz := (smul_eq_zero.mp htwice.symm).resolve_left (neg_ne_zero.mpr hΛ)
    exact hz
  · exact bot_le

end InfoGeometry.Twistor.InfinityPencilBoundary
