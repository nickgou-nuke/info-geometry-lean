/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PerjesConventions
import InfoGeometry.Twistor.PerjesNullLineCorrespondence

/-! # Incoming Perjes pairing results on the existing convention owners

The signed incidence map is injective. Its Witt pairing at distinct spacetime
matrices retains the ordered Hermitian difference and factor i. Helicity is
invariant under unit-norm phase scaling, not arbitrary projective scaling.
-/
noncomputable section
namespace InfoGeometry.Twistor.PerjesIncidencePairing
open PenroseIncidence PerjesConventions
open PerjesNullLineCorrespondence
open scoped Matrix

theorem paperIncidence_injective (X : ComplexSpacetime) :
    Function.Injective (paperIncidence X) :=
  incidenceSign.injective.comp (incidenceLinearMap_injective X)

theorem paperHelicity_phase_invariant (c : ℂ) (hc : c * star c = 1)
    (Z : Twistor4) : paperHelicity (c • Z) = paperHelicity Z := by
  have hc' : star c * c = 1 := by rwa [mul_comm]
  simp only [paperHelicity, wittPair_smul, hc', one_mul]

/-- The two-point pairing before any Hermitian or coincident-point specialization. -/
theorem paperIncidence_pairing (X Y : ComplexSpacetime) (pi rho : Spinor2) :
    wittPair (paperIncidence X pi) (paperIncidence Y rho) =
      Complex.I * (∑ i, star (pi i) * ((Xᴴ - Y).mulVec rho) i) := by
  simp [paperIncidence_apply, wittPair, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, smul_eq_mul]
  ring

/-- Equal incidence is exactly the kernel condition on the matrix difference. -/
theorem paperIncidence_equal_iff (X Y : ComplexSpacetime) (p : Spinor2) :
    paperIncidence X p = paperIncidence Y p ↔ (X - Y).mulVec p = 0 := by
  constructor
  · intro h
    have he := congrArg (fun Z : Twistor4 => Complex.I • Z.1) h
    simp [paperIncidence_apply, smul_smul] at he
    rw [Matrix.sub_mulVec, he, sub_self]
  · intro h
    have he : X.mulVec p = Y.mulVec p := by
      exact sub_eq_zero.mp (by simpa [Matrix.sub_mulVec] using h)
    simp [paperIncidence_apply, he]

/-- The affine fibre can be based at any Hermitian incident point. -/
theorem real_incidence_fiber (X Y : ComplexSpacetime) (hX : Xᴴ = X)
    (p : Spinor2) (hp : p ≠ 0) :
    (Yᴴ = Y ∧ paperIncidence Y p = paperIncidence X p) ↔
      ∃ t : ℝ, Y = X + t • PerjesNullLineCorrespondence.lineDirection p := by
  constructor
  · rintro ⟨hY, hinc⟩
    have hd : (Y - X)ᴴ = Y - X := by simp [hY, hX]
    have he := hermitian_kernel_line (Y - X) p hp hd
      ((paperIncidence_equal_iff Y X p).mp hinc)
    exact ⟨(Matrix.trace (Y - X)).re / spinorNormSq p,
      (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)⟩
  · rintro ⟨t, rfl⟩
    constructor
    · simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hX,
        lineDirection_hermitian]
    · apply (paperIncidence_equal_iff _ _ p).mpr
      simp [Matrix.smul_mulVec, lineDirection_mulVec]

end InfoGeometry.Twistor.PerjesIncidencePairing
