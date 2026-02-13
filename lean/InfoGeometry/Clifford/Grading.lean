import InfoGeometry.Clifford.Cl11
import Mathlib

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Commutator bracket on doubled-space endomorphisms. -/
def clmComm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  A.comp B - B.comp A

/-- Jordan product from the associative product on doubled-space endomorphisms. -/
noncomputable def jordanProd
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (A.comp B + B.comp A)

/-- Jordan-closed families of endomorphisms. -/
def isJordan
    (S : Set (DoubledSpace E →L[ℝ] DoubledSpace E)) : Prop :=
  ∀ {A B}, A ∈ S → B ∈ S → jordanProd A B ∈ S

/-- Derivations of the Jordan product. -/
def isDerivation
    (D : (DoubledSpace E →L[ℝ] DoubledSpace E) →
      (DoubledSpace E →L[ℝ] DoubledSpace E)) : Prop :=
  ∀ A B,
    D (jordanProd A B) = jordanProd (D A) B + jordanProd A (D B)

/-- Grade-0 (structure) operators commute with the grading involution `J`. -/
def isGradeZero (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = A.comp (modularJ (E := E))

lemma jordanProd_comm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    jordanProd A B = jordanProd B A := by
  simp [jordanProd, add_comm]

lemma comp_eq_jordan_add_half_comm
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    A.comp B
      = jordanProd A B + ((2 : ℝ)⁻¹) • clmComm A B := by
  have hhalf : (((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) = 1 := by norm_num
  have hsplit (x : E) : x = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by
    calc
      x = (1 : ℝ) • x := by simp
      _ = ((((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹)) : ℝ) • x := by simp [hhalf]
      _ = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by simp [add_smul]
  apply ContinuousLinearMap.ext
  intro v
  ext <;>
    simp [jordanProd, clmComm, sub_eq_add_neg, smul_add, add_assoc, add_left_comm]
  · exact hsplit ((A (B v)).1)
  · exact hsplit ((A (B v)).2)

lemma gradeZero_closed_comm
    {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isGradeZero (E := E) A)
    (hB : isGradeZero (E := E) B) :
    isGradeZero (E := E) (clmComm A B) := by
  unfold isGradeZero at *
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

/-- `+1` eigenspace predicate for the grading involution `J`. -/
def inGradePlus (v : DoubledSpace E) : Prop := modularJ (E := E) v = v

/-- `-1` eigenspace predicate for the grading involution `J`. -/
def inGradeMinus (v : DoubledSpace E) : Prop := modularJ (E := E) v = -v

/-- Grade `+` projector `(Id + J)/2`. -/
noncomputable def gradePlusPart (v : DoubledSpace E) : DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (v + modularJ (E := E) v)

/-- Grade `-` projector `(Id - J)/2`. -/
noncomputable def gradeMinusPart (v : DoubledSpace E) : DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (v - modularJ (E := E) v)

lemma gradePlusPart_in_plus (v : DoubledSpace E) :
    inGradePlus (E := E) (gradePlusPart (E := E) v) := by
  ext <;> simp [gradePlusPart, modularJ, add_comm]

lemma gradeMinusPart_in_minus (v : DoubledSpace E) :
    inGradeMinus (E := E) (gradeMinusPart (E := E) v) := by
  ext <;> simp [gradeMinusPart, modularJ, sub_eq_add_neg, add_comm]

lemma grade_decomposition (v : DoubledSpace E) :
    v = gradePlusPart (E := E) v + gradeMinusPart (E := E) v := by
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = 1 := by norm_num
  ext <;> simp [gradePlusPart, gradeMinusPart, modularJ, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc, smul_add]
  · calc
      v.1 = (1 : ℝ) • v.1 := by simp
      _ = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • v.1 := by simp [hhalf]
      _ = (2 : ℝ)⁻¹ • v.1 + (2 : ℝ)⁻¹ • v.1 := by simp [add_smul]
  · calc
      v.2 = (1 : ℝ) • v.2 := by simp
      _ = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • v.2 := by simp [hhalf]
      _ = (2 : ℝ)⁻¹ • v.2 + (2 : ℝ)⁻¹ • v.2 := by simp [add_smul]

lemma spectralEpsilon_swaps_grades_plus_to_minus
    {v : DoubledSpace E}
    (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (spectralEpsilon (E := E) v) := by
  rcases v with ⟨x, y⟩
  have hpair : (y, x) = (x, y) := by simpa [inGradePlus, modularJ] using hv
  have hxy : y = x := by simpa using congrArg Prod.fst hpair
  subst hxy
  simp [inGradeMinus, modularJ, spectralEpsilon]

lemma spectralEpsilon_swaps_grades_minus_to_plus
    {v : DoubledSpace E}
    (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) (spectralEpsilon (E := E) v) := by
  rcases v with ⟨x, y⟩
  have hpair : (y, x) = (-x, -y) := by simpa [inGradeMinus, modularJ] using hv
  have hxy : y = -x := by simpa using congrArg Prod.fst hpair
  subst hxy
  simp [inGradePlus, modularJ, spectralEpsilon]

/-- Even operators commute with the grading involution `J`. -/
def isEven (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = A.comp (modularJ (E := E))

/-- Odd operators anticommute with the grading involution `J`. -/
def isOdd (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = -(A.comp (modularJ (E := E)))

lemma isEven_iff_gradeZero (A : DoubledSpace E →L[ℝ] DoubledSpace E) :
    isEven (E := E) A ↔ isGradeZero (E := E) A := Iff.rfl

/-- Chirality/grade projectors as endomorphisms `(Id ± J)/2`. -/
noncomputable def gradePlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) + modularJ (E := E))

noncomputable def gradeMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) - modularJ (E := E))

/-- Spectral projector `(Id + ε)/2`. -/
noncomputable def spectralPlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectralEpsilon (E := E))

/-- Spectral projector `(Id - ε)/2`. -/
noncomputable def spectralMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) •
    (ContinuousLinearMap.id ℝ (DoubledSpace E) - spectralEpsilon (E := E))

lemma gradePlusProj_apply (v : DoubledSpace E) :
    gradePlusProj (E := E) v = gradePlusPart (E := E) v := by
  simp [gradePlusProj, gradePlusPart]

lemma gradeMinusProj_apply (v : DoubledSpace E) :
    gradeMinusProj (E := E) v = gradeMinusPart (E := E) v := by
  simp [gradeMinusProj, gradeMinusPart]

lemma projector_commutator_gradePlus_spectralPlus :
    clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E))
      = ((4 : ℝ)⁻¹) • clmComm (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [clmComm, gradePlusProj, spectralPlusProj, sub_eq_add_neg,
    smul_add, smul_smul, add_assoc, add_left_comm, add_comm]
  abel_nf
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
          simp [two_smul]
    _ = ((2 : ℝ)⁻¹) • complexI (E := E) := by
          have hscalar : ((4 : ℝ)⁻¹ * (2 : ℝ)) = (2 : ℝ)⁻¹ := by norm_num
          simp [complexI, smul_smul, hscalar]

/-- Incompatibility of geometric and spectral splittings at projector level. -/
def splittingIncompatible : Prop :=
  clmComm (gradePlusProj (E := E)) (spectralPlusProj (E := E)) ≠ 0

lemma splittingIncompatible_iff_nonzero_clifford_comm :
    splittingIncompatible (E := E)
      ↔ clmComm (modularJ (E := E)) (spectralEpsilon (E := E)) ≠ 0 := by
  unfold splittingIncompatible
  rw [projector_commutator_gradePlus_spectralPlus (E := E)]
  constructor
  · intro h hComm
    apply h
    simp [hComm]
  · intro h hProj
    apply h
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    exact smul_eq_zero.mp hProj |>.resolve_left (inv_ne_zero h4)

/-- CAR-style dictionary entry: creation-like projector (grade `+`). -/
noncomputable def creationLike : DoubledSpace E →L[ℝ] DoubledSpace E :=
  gradePlusProj (E := E)

/-- CAR-style dictionary entry: annihilation-like projector (grade `-`). -/
noncomputable def annihilationLike : DoubledSpace E →L[ℝ] DoubledSpace E :=
  gradeMinusProj (E := E)

lemma creationLike_apply (v : DoubledSpace E) :
    creationLike (E := E) v = gradePlusPart (E := E) v := by
  simp [creationLike, gradePlusProj_apply]

lemma annihilationLike_apply (v : DoubledSpace E) :
    annihilationLike (E := E) v = gradeMinusPart (E := E) v := by
  simp [annihilationLike, gradeMinusProj_apply]

lemma modularJ_comp_creationLike :
    (modularJ (E := E)).comp (creationLike (E := E)) = creationLike (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [creationLike, gradePlusProj, modularJ, add_comm]

lemma modularJ_comp_annihilationLike :
    (modularJ (E := E)).comp (annihilationLike (E := E)) =
      -(annihilationLike (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [annihilationLike, gradeMinusProj, modularJ, sub_eq_add_neg, add_comm]

lemma creationLike_inGradePlus (v : DoubledSpace E) :
    inGradePlus (E := E) (creationLike (E := E) v) := by
  simpa [creationLike_apply] using gradePlusPart_in_plus (E := E) v

lemma annihilationLike_inGradeMinus (v : DoubledSpace E) :
    inGradeMinus (E := E) (annihilationLike (E := E) v) := by
  simpa [annihilationLike_apply] using gradeMinusPart_in_minus (E := E) v

lemma creation_annihilation_decomposition (v : DoubledSpace E) :
    v = creationLike (E := E) v + annihilationLike (E := E) v := by
  simpa [creationLike_apply, annihilationLike_apply] using grade_decomposition (E := E) v

lemma spectralEpsilon_isOdd :
    isOdd (E := E) (spectralEpsilon (E := E)) := by
  simpa [isOdd] using modularJ_spectralEpsilon_anticommute (E := E)

end KreinClifford
