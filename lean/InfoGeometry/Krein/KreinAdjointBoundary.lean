/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.KreinAdjointCommutantBridge

/-!
# Krein Gram operators and positive-adjoint compatibility

These statements use the existing real Hilbert/Krein carrier and its bounded
noncommutative operator algebra. They apply in arbitrary Hilbert dimension.
The Krein Gram operator vanishes precisely when the operator range is totally
isotropic. On the fundamental-symmetry commutant it instead has the Hilbert
zero-detection property. The doubled diagonal projector separates these cases.

No physical state-space identification or exceptional-group classification is
asserted. In particular, an idempotent with isotropic range is not a nonzero
Krein-self-adjoint projection.
-/

noncomputable section

namespace InfoGeometry.Krein.KreinAdjointBoundary

open KreinSpace KreinAdjointCommutantBridge
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [KreinSpace H]

/-- Zero Krein Gram operator means that the entire range is totally isotropic. -/
theorem kreinGram_eq_zero_iff (A : H →L[ℝ] H) :
    (kreinAdjoint A).comp A = 0 ↔
      ∀ u v : H, kreinInner (A u) (A v) = 0 := by
  constructor
  · intro h u v
    rw [kreinInner_kreinAdjoint]
    change kreinInner u (((kreinAdjoint A).comp A) v) = 0
    rw [h]
    simp [kreinInner]
  · intro h
    ext v
    apply ext_inner_left ℝ
    intro u
    have hu := h ((KreinSpace.J : H ≃ₗᵢ[ℝ] H) u) v
    rw [kreinInner_kreinAdjoint, kreinInner_def, KreinSpace.J_invol] at hu
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      inner_zero_right] using hu

/-- Equality of the two adjoints is exactly commutation with the fundamental
symmetry; this is an operator statement, not a group classification. -/
theorem kreinAdjoint_eq_adjoint_iff (A : H →L[ℝ] H) :
    kreinAdjoint A = ContinuousLinearMap.adjoint A ↔
      CommutesWithFundamentalSymmetry A := by
  constructor
  · intro h
    have hh := congrArg ContinuousLinearMap.adjoint h
    simp only [kreinAdjoint, ContinuousLinearMap.adjoint_comp, adjoint_jCLM,
      ContinuousLinearMap.adjoint_adjoint] at hh
    change A.comp jCLM = jCLM.comp A
    calc
      A.comp jCLM = ((jCLM.comp A).comp jCLM).comp jCLM := by rw [hh]
      _ = jCLM.comp A := by simp [ContinuousLinearMap.comp_assoc]
  · intro h
    exact kreinAdjoint_eq_adjoint_of_adjoint_commutes A
      (adjoint_commutes_of_commutes A h)

/-- For a Krein-skew operator, Hilbert skew-adjointness is precisely the
fundamental-symmetry commutation condition. -/
theorem hilbert_skew_iff_commutes (A : H →L[ℝ] H)
    (hA : IsKreinSkewAdjoint A) :
    ContinuousLinearMap.adjoint A = -A ↔
      CommutesWithFundamentalSymmetry A := by
  change kreinAdjoint A = -A at hA
  constructor
  · intro h
    exact (kreinAdjoint_eq_adjoint_iff A).mp (hA.trans h.symm)
  · intro h
    rw [← (kreinAdjoint_eq_adjoint_iff A).mpr h, hA]

/-- On the symmetry commutant the Krein Gram operator detects zero exactly. -/
theorem kreinGram_eq_zero_iff_of_commutes (A : H →L[ℝ] H)
    (hA : CommutesWithFundamentalSymmetry A) :
    (kreinAdjoint A).comp A = 0 ↔ A = 0 := by
  rw [(kreinAdjoint_eq_adjoint_iff A).mpr hA]
  exact ContinuousLinearMap.adjoint_comp_self_eq_zero_iff

section Doubled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The diagonal projector `(x,y) ↦ ((x+y)/2,(x+y)/2)` on the existing doubled
Hilbert carrier. Its range is isotropic for the diagonal split Krein form. -/
def diagonalProjector : DoubledSpace E →L[ℝ] DoubledSpace E :=
  InfoGeometry.GrandUnification.ArchetypeDictionary.peircePlus (R := ℝ)
    (modular_j (E := E))

/-- The projector averages the two sheet coordinates and copies the result to
both sheets. -/
theorem diagonalProjector_apply (u : DoubledSpace E) :
    diagonalProjector u =
      to_doubled ((1 / 2 : ℝ) • (WithLp.fst u + WithLp.snd u))
        ((1 / 2 : ℝ) • (WithLp.fst u + WithLp.snd u)) := by
  apply DoubledSpace.ext
  · simp [diagonalProjector,
      InfoGeometry.GrandUnification.ArchetypeDictionary.peircePlus, modular_j,
      to_doubled, add_comm]
  · simp [diagonalProjector,
      InfoGeometry.GrandUnification.ArchetypeDictionary.peircePlus, modular_j,
      to_doubled, add_comm]

theorem diagonalProjector_idempotent :
    (diagonalProjector (E := E)).comp diagonalProjector = diagonalProjector := by
  ext u
  · rw [ContinuousLinearMap.comp_apply, diagonalProjector_apply,
      diagonalProjector_apply]
    simp only [fst_to_doubled, snd_to_doubled]
    module
  · rw [ContinuousLinearMap.comp_apply, diagonalProjector_apply,
      diagonalProjector_apply]
    simp only [fst_to_doubled, snd_to_doubled]
    module

theorem diagonalProjector_fst_eq_snd (u : DoubledSpace E) :
    WithLp.fst (diagonalProjector u) = WithLp.snd (diagonalProjector u) := by
  simp [diagonalProjector,
    InfoGeometry.GrandUnification.ArchetypeDictionary.peircePlus,
    modular_j, add_comm]

theorem diagonalProjector_fixes_diagonal (x : E) :
    diagonalProjector (to_doubled x x) = to_doubled x x := by
  apply DoubledSpace.ext <;>
    simp [diagonalProjector,
      InfoGeometry.GrandUnification.ArchetypeDictionary.peircePlus,
      modular_j, to_doubled, invOf_eq_inv, ← two_smul ℝ, smul_smul]

/-- The null Gram identity holds on arbitrary doubled real Hilbert spaces. -/
theorem diagonalProjector_kreinGram :
    (kreinAdjoint (diagonalProjector (E := E))).comp diagonalProjector = 0 := by
  apply (kreinGram_eq_zero_iff _).mpr
  intro u v
  rw [krein_inner_prod_l2]
  change ⟪WithLp.fst (diagonalProjector u), WithLp.fst (diagonalProjector v)⟫_ℝ -
    ⟪WithLp.snd (diagonalProjector u), WithLp.snd (diagonalProjector v)⟫_ℝ = 0
  rw [diagonalProjector_fst_eq_snd, diagonalProjector_fst_eq_snd, sub_self]

theorem diagonalProjector_ne_zero [Nontrivial E] :
    diagonalProjector (E := E) ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  intro h
  have he := congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E =>
    WithLp.fst (T (to_doubled x x))) h
  rw [diagonalProjector_fixes_diagonal] at he
  exact hx (by simpa using he)

theorem diagonalProjector_not_kreinSelfAdjoint [Nontrivial E] :
    ¬ IsKreinSelfAdjoint (diagonalProjector (E := E)) := by
  intro h
  have hg := diagonalProjector_kreinGram (E := E)
  rw [h, diagonalProjector_idempotent] at hg
  exact diagonalProjector_ne_zero hg

/-- The same nonzero operator has a nonzero Hilbert Gram operator. -/
theorem diagonalProjector_hilbertGram_ne_zero [Nontrivial E] :
    (ContinuousLinearMap.adjoint (diagonalProjector (E := E))).comp
      diagonalProjector ≠ 0 := by
  intro h
  exact diagonalProjector_ne_zero
    (ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp h)

end Doubled
end InfoGeometry.Krein.KreinAdjointBoundary
