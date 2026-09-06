import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic
import InfoGeometry.QuantumGeometry.Projective.Basic
import InfoGeometry.QuantumGeometry.Projective.QGT

/-!
# Complex Projective Hilbert Space ℙ(H) and Descended Quantum Geometric Tensor

This module formalizes the genuine quotient construction of the complex projective
Hilbert space:

$$\mathbb{P}(H) = S(H) / U(1)$$

and proves that the Quantum Geometric Tensor, Fubini–Study metric, Berry curvature 2-form,
and Quantum Fisher Information (QFI) metric descend canonically to $\mathbb{P}(H)$,
satisfying the full Cauchy–Schwarz and Robertson–Schrödinger inequalities on the quotient.

## Main Declarations
1. `U1Rel`: The $U(1)$ phase equivalence relation on normalized Hilbert states `NormalizedState H`.
2. `projectiveSetoid`: Proof that `U1Rel` is an equivalence relation.
3. `ProjectiveSpace H`: The quotient type `Quotient (projectiveSetoid H)`.
4. `toProjective`: Canonical projection $\pi : S(H) \to \mathbb{P}(H)$.
5. `QGT_projective`: The descended tensor $Q : \mathbb{P}(H) \times \operatorname{End}(H) \times \operatorname{End}(H) \to \mathbb{C}$.
6. `fubiniStudyMetric_projective` & `berryCurvature_projective`: Descended metric and symplectic forms.
7. `qfiMetric_projective`: Pure-state QFI metric normalized as $4 \cdot g_{\mathrm{FS}}$.
8. `QGT_cauchy_schwarz_projective` & `robertson_schrodinger_qgt_bound_projective`:
   Universal geometric uncertainty relations on $\mathbb{P}(H)$.
-/

noncomputable section

namespace InfoGeometry.QuantumGeometry.Projective

open scoped InnerProductSpace
open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-!
=============================================================================
PART 1: The U(1) Phase Equivalence Relation and Setoid
=============================================================================
-/

/-- The U(1) phase equivalence relation on normalized states. -/
def U1Rel (ψ₁ ψ₂ : NormalizedState H) : Prop :=
  ∃ (c : ℂ) (hc : starRingEnd ℂ c * c = 1), ψ₂.vec = c • ψ₁.vec

theorem U1Rel.refl (ψ : NormalizedState H) : U1Rel ψ ψ :=
  ⟨1, by simp, by simp⟩

theorem U1Rel.symm {ψ₁ ψ₂ : NormalizedState H} (h : U1Rel ψ₁ ψ₂) : U1Rel ψ₂ ψ₁ := by
  rcases h with ⟨c, hc, hvec⟩
  refine ⟨starRingEnd ℂ c, ?_, ?_⟩
  · show star (star c) * star c = 1
    rw [star_star, mul_comm]
    exact hc
  · rw [hvec, smul_smul]
    have hc_cancel : starRingEnd ℂ c * c = 1 := hc
    rw [hc_cancel, one_smul]

theorem U1Rel.trans {ψ₁ ψ₂ ψ₃ : NormalizedState H}
    (h12 : U1Rel ψ₁ ψ₂) (h23 : U1Rel ψ₂ ψ₃) : U1Rel ψ₁ ψ₃ := by
  rcases h12 with ⟨c1, hc1, hvec1⟩
  rcases h23 with ⟨c2, hc2, hvec2⟩
  refine ⟨c2 * c1, ?_, ?_⟩
  · show star (c2 * c1) * (c2 * c1) = 1
    have hc2' : star c2 * c2 = 1 := hc2
    have hc1' : star c1 * c1 = 1 := hc1
    rw [star_mul, mul_assoc (star c1), ← mul_assoc (star c2), hc2', one_mul, hc1']
  · rw [hvec2, hvec1, smul_smul]

/-- Setoid of U(1) phase equivalence on normalized Hilbert states. -/
def projectiveSetoid (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Setoid (NormalizedState H) where
  r := U1Rel
  iseqv := ⟨U1Rel.refl, U1Rel.symm, U1Rel.trans⟩

/-!
=============================================================================
PART 2: Complex Projective Space ℙ(H) and Canonical Projection
=============================================================================
-/

/-- The Complex Projective Hilbert Space ℙ(H) as the quotient S(H) / U(1). -/
def ProjectiveSpace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Type _ :=
  Quotient (projectiveSetoid H)

/-- Canonical projection from a normalized state representative to the projective point. -/
def toProjective (ψ : NormalizedState H) : ProjectiveSpace H :=
  Quotient.mk (projectiveSetoid H) ψ

@[simp]
theorem toProjective_phaseRotate (ψ : NormalizedState H) (c : ℂ) (hc : starRingEnd ℂ c * c = 1) :
    toProjective (phaseRotate ψ c hc) = toProjective ψ := by
  apply Quotient.sound
  exact U1Rel.symm ⟨c, hc, rfl⟩

/-!
=============================================================================
PART 3: Descended Quantum Geometric Tensor and Metrics
=============================================================================
-/

/-- 
  The descended Quantum Geometric Tensor on the complex projective space ℙ(H).
-/
def QGT_projective (p : ProjectiveSpace H) (X Y : EndH) : ℂ :=
  Quotient.lift (fun ψ : NormalizedState H => QGT ψ X Y)
    (by
      intro ψ₁ ψ₂ h
      rcases h with ⟨c, hc, _hvec⟩
      have h_rot : ψ₂ = phaseRotate ψ₁ c hc := by
        cases ψ₁; cases ψ₂
        dsimp [phaseRotate] at *
        congr
      rw [h_rot]
      exact (QGT_phase_invariant ψ₁ X Y c hc).symm)
    p

@[simp]
theorem QGT_projective_toProjective (ψ : NormalizedState H) (X Y : EndH) :
    QGT_projective (toProjective ψ) X Y = QGT ψ X Y :=
  rfl

/-- Descended Fubini–Study metric on ℙ(H). -/
def fubiniStudyMetric_projective (p : ProjectiveSpace H) (X Y : EndH) : ℝ :=
  (QGT_projective p X Y).re

@[simp]
theorem fubiniStudyMetric_projective_toProjective (ψ : NormalizedState H) (X Y : EndH) :
    fubiniStudyMetric_projective (toProjective ψ) X Y = fubiniStudyMetric ψ X Y :=
  rfl

/-- Descended Berry curvature 2-form on ℙ(H). -/
def berryCurvature_projective (p : ProjectiveSpace H) (X Y : EndH) : ℝ :=
  -2 * (QGT_projective p X Y).im

@[simp]
theorem berryCurvature_projective_toProjective (ψ : NormalizedState H) (X Y : EndH) :
    berryCurvature_projective (toProjective ψ) X Y = berryCurvature ψ X Y :=
  rfl

/-- Pure-state Quantum Fisher Information (QFI) Metric on ℙ(H), normalized as 4 • g_FS. -/
def qfiMetric_projective (p : ProjectiveSpace H) (X Y : EndH) : ℝ :=
  4 * fubiniStudyMetric_projective p X Y

@[simp]
theorem qfiMetric_projective_toProjective (ψ : NormalizedState H) (X Y : EndH) :
    qfiMetric_projective (toProjective ψ) X Y = 4 * fubiniStudyMetric ψ X Y :=
  rfl

/-!
=============================================================================
PART 4: Universal Geometric Inequalities on Projective Space
=============================================================================
-/

/-- Cauchy–Schwarz on Projective Space ℙ(H). -/
theorem QGT_cauchy_schwarz_projective (p : ProjectiveSpace H) (X Y : EndH) :
    Complex.normSq (QGT_projective p X Y) ≤
      fubiniStudyMetric_projective p X X * fubiniStudyMetric_projective p Y Y := by
  induction p using Quotient.ind
  simpa using QGT_cauchy_schwarz _ X Y

/-- Full Geometric Robertson–Schrödinger Inequality on ℙ(H). -/
theorem robertson_schrodinger_qgt_bound_projective (p : ProjectiveSpace H) (X Y : EndH) :
    fubiniStudyMetric_projective p X X * fubiniStudyMetric_projective p Y Y ≥
      (fubiniStudyMetric_projective p X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature_projective p X Y) ^ 2 := by
  induction p using Quotient.ind
  simpa using robertson_schrodinger_qgt_bound _ X Y

/-- Projective Berry Curvature Uncertainty Bound on ℙ(H). -/
theorem berry_curvature_uncertainty_bound_projective (p : ProjectiveSpace H) (X Y : EndH) :
    fubiniStudyMetric_projective p X X * fubiniStudyMetric_projective p Y Y ≥
      (1 / 4 : ℝ) * (berryCurvature_projective p X Y) ^ 2 := by
  induction p using Quotient.ind
  simpa using berry_curvature_uncertainty_bound _ X Y

/-- Projective Master Lie Representation Uncertainty Bound on ℙ(H). -/
theorem lie_rep_uncertainty_bound_projective
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (ρ : SkewAdjointLieRep (H := H) 𝔤)
    (p : ProjectiveSpace H) (X Y : 𝔤) :
    fubiniStudyMetric_projective p (ρ.toLieHom X) (ρ.toLieHom X) *
        fubiniStudyMetric_projective p (ρ.toLieHom Y) (ρ.toLieHom Y) ≥
      (1 / 4 : ℝ) * (berryCurvature_projective p (ρ.toLieHom X) (ρ.toLieHom Y)) ^ 2 := by
  induction p using Quotient.ind
  simpa using berry_curvature_uncertainty_bound _ (ρ.toLieHom X) (ρ.toLieHom Y)

/-- Berry curvature commutator evaluation at any projective point representative. -/
theorem berryCurvature_projective_eq_commutator
    (ψ : NormalizedState H) (X Y : EndH)
    (hX : ContinuousLinearMap.adjoint X = -X)
    (hY : ContinuousLinearMap.adjoint Y = -Y) :
    (berryCurvature_projective (toProjective ψ) X Y : ℂ) * Complex.I =
      inner (𝕜 := ℂ) ψ.vec ((opCommutator X Y) ψ.vec) := by
  simpa using berryCurvature_eq_commutator ψ X Y hX hY

/-- Representative form of projective Lie representation uncertainty bound. -/
theorem lie_rep_uncertainty_bound_representative
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    (ρ : SkewAdjointLieRep (H := H) 𝔤)
    (ψ : NormalizedState H) (X Y : 𝔤) :
    fubiniStudyMetric_projective (toProjective ψ) (ρ.toLieHom X) (ρ.toLieHom X) *
        fubiniStudyMetric_projective (toProjective ψ) (ρ.toLieHom Y) (ρ.toLieHom Y) ≥
      (1 / 4 : ℝ) * Complex.normSq (inner (𝕜 := ℂ) ψ.vec (ρ.toLieHom ⁅X, Y⁆ ψ.vec)) := by
  simpa using lie_rep_uncertainty_bound ρ ψ X Y

end InfoGeometry.QuantumGeometry.Projective

end noncomputable section
