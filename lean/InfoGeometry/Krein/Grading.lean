import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Cartan.Involution
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Krein

open InfoGeometry.Cartan
variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Commutator bracket on doubled-space endomorphisms. -/
def clmComm (A B : DoubledSpace E →L[ℝ] DoubledSpace E) : DoubledSpace E →L[ℝ] DoubledSpace E := A.comp B - B.comp A
lemma clmComm_eq_lie (A B : DoubledSpace E →L[ℝ] DoubledSpace E) : clmComm A B = ⁅A, B⁆ := rfl

/-- Jordan product from the associative product on doubled-space endomorphisms. -/
noncomputable def jordanProd
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (A.comp B + B.comp A)

/-- Even operators commute with the grading involution `J`. -/
def isEven (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = A.comp (modularJ (E := E))

/-- Backward-compatible alias for even operators. -/
abbrev isGradeZero (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  isEven (E := E) A

/-- Odd operators anticommute with the grading involution `J`. -/
def isOdd (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = -(A.comp (modularJ (E := E)))

lemma jordanProd_comm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    jordanProd A B = jordanProd B A := by
  simp [jordanProd, add_comm]

lemma even_closed_comm
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isEven (E := E) A)
    (hB : isEven (E := E) B) :
    isEven (E := E) (clmComm A B) := by
  unfold isEven at *
  calc
    (modularJ (E := E)).comp (clmComm A B)
        = (modularJ (E := E)).comp (A.comp B) - (modularJ (E := E)).comp (B.comp A) := by
            simp [clmComm, ContinuousLinearMap.comp_sub]
    _ = ((modularJ (E := E)).comp A).comp B - ((modularJ (E := E)).comp B).comp A := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (A.comp (modularJ (E := E))).comp B - (B.comp (modularJ (E := E))).comp A := by
          rw [hA, hB]
    _ = A.comp ((modularJ (E := E)).comp B) - B.comp ((modularJ (E := E)).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = A.comp (B.comp (modularJ (E := E))) - B.comp (A.comp (modularJ (E := E))) := by
          rw [hB, hA]
    _ = (A.comp B).comp (modularJ (E := E)) - (B.comp A).comp (modularJ (E := E)) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (clmComm A B).comp (modularJ (E := E)) := by
          simp [clmComm, ContinuousLinearMap.sub_comp]

def inGradePlus (v : DoubledSpace E) : Prop := modularJ (E := E) v = v
def inGradeMinus (v : DoubledSpace E) : Prop := modularJ (E := E) v = -v

noncomputable def gradePlusPart (v : DoubledSpace E) : DoubledSpace E := CartanInvolution.Pplus (C := instCartanInvolutionDoubled) v
noncomputable def gradeMinusPart (v : DoubledSpace E) : DoubledSpace E := CartanInvolution.Pminus (C := instCartanInvolutionDoubled) v

noncomputable def gradePlusProj : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + modularJ (E := E))
noncomputable def spectralPlusProj : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectralEpsilon (E := E))

@[simp] lemma gradePlusProj_apply (v : DoubledSpace E) : gradePlusProj (E := E) v = gradePlusPart (E := E) v := by simp [gradePlusPart, gradePlusProj, CartanInvolution.Pplus, smul_add]



lemma projector_commutator_gradePlus_spectralPlus_eq_half_complexI :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E)) = ((2 : ℝ)⁻¹) • complexI (E := E) := by
  apply ContinuousLinearMap.ext; intro v
  simp only [clmComm, gradePlusProj, spectralPlusProj, complexI, ContinuousLinearMap.coe_sub,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_smul, ContinuousLinearMap.id_apply,
    Pi.smul_apply, Pi.sub_apply, Function.comp_apply, smul_add, modularJ_apply,
    spectralEpsilon_apply, smul_smul]
  -- (1/2) • (1/2) • (v + J v + ε v + J (ε v)) - (1/2) • (1/2) • (v + ε v + J v + ε (J v))
  -- = (1/4) • (J (ε v) - ε (J v))
  have h_anti : spectralEpsilon (E := E) (modularJ (E := E) v) = -(modularJ (E := E) (spectralEpsilon (E := E) v)) := by
    have h := modularJ_spectralEpsilon_anticommute (E := E)
    have h_eval := ContinuousLinearMap.congr_fun h v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.neg_apply] at h_eval
    rw [h_eval, neg_neg]
  -- Wait, modularJ_spectralEpsilon_anticommute says J ∘ ε = -(ε ∘ J).
  -- So J(ε v) = -ε(J v).
  -- Thus J(ε v) - ε(J v) = -ε(J v) - ε(J v) = -2 ε(J v).
  -- Or ε(J v) = -J(ε v).
  -- J(ε v) - ε(J v) = J(ε v) - (-J(ε v)) = 2 J(ε v).
  have h_anti' : modularJ (E := E).comp (spectralEpsilon (E := E)) = - (spectralEpsilon (E := E).comp (modularJ (E := E))) :=
    modularJ_spectralEpsilon_anticommute (E := E)
  have h_eval := ContinuousLinearMap.congr_fun h_anti' v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.neg_apply] at h_eval
  -- h_eval : J (ε v) = - ε (J v)
  simp only [h_eval, sub_eq_add_neg, neg_add, add_assoc]
  -- Now simplify the sum
  -- (1/4) • (v + J v + ε v + J (ε v)) + (1/4) • (-v - ε v - J v - ε (J v))
  -- = (1/4) • (J (ε v) - ε (J v))
  -- = (1/4) • (J (ε v) + J (ε v)) = (1/2) • J (ε v)
  -- Which is (1/2) • complexI v.
  rw [← smul_add]
  abel
  -- Goal: (2⁻¹ * 2⁻¹) • (J (ε v) - ε (J v)) = 2⁻¹ • J (ε v)
  rw [← h_eval, sub_neg_eq_add, ← two_smul ℝ]
  rw [smul_smul]
  norm_num
  
end InfoGeometry.Krein
