import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Krein

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Commutator bracket on doubled-space endomorphisms. -/
def clmComm (A B : DoubledSpace E →L[ℝ] DoubledSpace E) : DoubledSpace E →L[ℝ] DoubledSpace E := A.comp B - B.comp A
lemma clmComm_eq_lie (A B : DoubledSpace E →L[ℝ] DoubledSpace E) : clmComm A B = ⁅A, B⁆ := by
  ext v <;> simp [clmComm, Ring.lie_def]

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

lemma spectralEpsilon_isOdd :
    isOdd (E := E) (spectralEpsilon (E := E)) := by
  unfold isOdd
  simpa using modularJ_spectralEpsilon_anticommute (E := E)

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

lemma projector_commutator_gradePlus_spectralPlus :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E))
      = ((4 : ℝ)⁻¹) • clmComm (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [clmComm, gradePlusProj, spectralPlusProj, sub_eq_add_neg,
    smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
  have hscalar : ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) = (4 : ℝ)⁻¹ := by norm_num
  simp [hscalar]

lemma projector_commutator_gradePlus_spectralPlus_eq_half_complexI :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E))
      = ((2 : ℝ)⁻¹) • complexI (E := E) := by
  rw [projector_commutator_gradePlus_spectralPlus (E := E)]
  have hanti := modularJ_spectralEpsilon_anticommute (E := E)
  calc
    ((4 : ℝ)⁻¹) • clmComm (modularJ (E := E)) (spectralEpsilon (E := E))
        = ((4 : ℝ)⁻¹) •
            ((modularJ (E := E)).comp (spectralEpsilon (E := E))
              - (spectralEpsilon (E := E)).comp (modularJ (E := E))) := by
              rfl
    _ = ((4 : ℝ)⁻¹) •
          ((modularJ (E := E)).comp (spectralEpsilon (E := E))
            + (modularJ (E := E)).comp (spectralEpsilon (E := E))) := by
          rw [hanti]
          simp [sub_eq_add_neg]
    _ = ((4 : ℝ)⁻¹) • ((2 : ℝ) • ((modularJ (E := E)).comp (spectralEpsilon (E := E)))) := by
          let X : DoubledSpace E →L[ℝ] DoubledSpace E :=
            (modularJ (E := E)).comp (spectralEpsilon (E := E))
          change ((4 : ℝ)⁻¹) • (X + X) = ((4 : ℝ)⁻¹) • ((2 : ℝ) • X)
          calc
            ((4 : ℝ)⁻¹) • (X + X) = ((4 : ℝ)⁻¹ • X + (4 : ℝ)⁻¹ • X) := by
              rw [smul_add]
            _ = (((4 : ℝ)⁻¹ + (4 : ℝ)⁻¹) : ℝ) • X := by
              simpa using (add_smul ((4 : ℝ)⁻¹) ((4 : ℝ)⁻¹) X).symm
            _ = ((2 : ℝ) * (4 : ℝ)⁻¹) • X := by
              have htwo : (((4 : ℝ)⁻¹ + (4 : ℝ)⁻¹) : ℝ) = ((2 : ℝ) * (4 : ℝ)⁻¹) := by ring
              rw [htwo]
            _ = ((4 : ℝ)⁻¹ * (2 : ℝ)) • X := by
              ring_nf
            _ = ((4 : ℝ)⁻¹) • ((2 : ℝ) • X) := by
              simp [smul_smul]
    _ = ((2 : ℝ)⁻¹) • complexI (E := E) := by
          have hscalar : ((4 : ℝ)⁻¹ * (2 : ℝ)) = (2 : ℝ)⁻¹ := by norm_num
          simp [complexI, smul_smul, hscalar]

end InfoGeometry.Krein
