import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Krein

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

noncomputable def gradePlusPart (v : DoubledSpace E) : DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (v + modularJ (E := E) v)

noncomputable def gradeMinusPart (v : DoubledSpace E) : DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (v - modularJ (E := E) v)

noncomputable def gradePlusProj : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + modularJ (E := E))
noncomputable def spectralPlusProj : DoubledSpace E →L[ℝ] DoubledSpace E := ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectralEpsilon (E := E))

@[simp] lemma gradePlusProj_apply (v : DoubledSpace E) :
    gradePlusProj (E := E) v = gradePlusPart (E := E) v := by
  simp [gradePlusPart, gradePlusProj, smul_add]



lemma projector_commutator_gradePlus_spectralPlus_eq_half_complexI :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E)) = ((2 : ℝ)⁻¹) • complexI (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, ξ⟩
  ext <;>
    simp [clmComm, gradePlusProj, spectralPlusProj, complexI, modularJ, spectralEpsilon]
  
end InfoGeometry.Krein
