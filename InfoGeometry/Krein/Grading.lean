import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Cartan.Involution
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Krein

open InfoGeometry.Cartan

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev EndE := (DoubledSpace E →L[ℝ] DoubledSpace E)

/-- Commutator bracket on doubled-space endomorphisms. -/
def clmComm (A B : EndE (E := E)) : EndE (E := E) :=
  A * B - B * A

lemma clmComm_eq_lie (A B : EndE (E := E)) :
    clmComm (E := E) A B = ⁅A, B⁆ := rfl

noncomputable def jordanProd (A B : EndE (E := E)) : EndE (E := E) :=
  ((2 : ℝ)⁻¹) • (A * B + B * A)

def isDerivation (D : EndE (E := E) → EndE (E := E)) : Prop :=
  ∀ A B, D (jordanProd (E := E) A B) =
    jordanProd (E := E) (D A) B + jordanProd (E := E) A (D B)

def isEven (A : EndE (E := E)) : Prop :=
  (modularJ (E := E)) * A = A * (modularJ (E := E))

abbrev isGradeZero (A : EndE (E := E)) : Prop :=
  isEven (E := E) A

def isOdd (A : EndE (E := E)) : Prop :=
  (modularJ (E := E)) * A = -(A * (modularJ (E := E)))

lemma jordanProd_comm (A B : EndE (E := E)) :
    jordanProd (E := E) A B = jordanProd (E := E) B A := by
  simp [jordanProd, add_comm]

lemma even_closed_comm {A B : EndE (E := E)}
    (hA : isEven (E := E) A) (hB : isEven (E := E) B) :
    isEven (E := E) (clmComm (E := E) A B) := by
  unfold isEven clmComm at *
  -- J(AB-BA)=(AB-BA)J using associativity and hA/hB.
  calc
    modularJ (E := E) * (A * B - B * A)
        = modularJ (E := E) * (A * B) - modularJ (E := E) * (B * A) := by
            simp [mul_sub, sub_eq_add_neg, add_assoc]
    _ = (A * B) * modularJ (E := E) - (B * A) * modularJ (E := E) := by
            simp [mul_assoc, hA, hB]
    _ = (A * B - B * A) * modularJ (E := E) := by
            simp [sub_mul, sub_eq_add_neg, add_assoc, mul_assoc]

lemma gradeZero_closed_comm {A B : EndE (E := E)}
    (hA : isGradeZero (E := E) A) (hB : isGradeZero (E := E) B) :
    isGradeZero (E := E) (clmComm (E := E) A B) :=
  even_closed_comm (E := E) hA hB

def inGradePlus (v : DoubledSpace E) : Prop := modularJ (E := E) v = v
def inGradeMinus (v : DoubledSpace E) : Prop := modularJ (E := E) v = -v

/-! Lifted projectors using the generic Cartan involution instance. -/
noncomputable def gradePlusPart (v : DoubledSpace E) : DoubledSpace E :=
  CartanInvolution.Pplus (C := (inferInstance : CartanInvolution (DoubledSpace E))) v

noncomputable def gradeMinusPart (v : DoubledSpace E) : DoubledSpace E :=
  CartanInvolution.Pminus (C := (inferInstance : CartanInvolution (DoubledSpace E))) v

lemma gradePlusPart_in_plus (v : DoubledSpace E) :
    inGradePlus (E := E) (gradePlusPart (E := E) v) := by
  have := CartanInvolution.theta_Pplus
    (C := (inferInstance : CartanInvolution (DoubledSpace E))) v
  simpa [inGradePlus, gradePlusPart, CartanInvolution.Pplus] using this

lemma gradeMinusPart_in_minus (v : DoubledSpace E) :
    inGradeMinus (E := E) (gradeMinusPart (E := E) v) := by
  have := CartanInvolution.theta_Pminus
    (C := (inferInstance : CartanInvolution (DoubledSpace E))) v
  simpa [inGradeMinus, gradeMinusPart, CartanInvolution.Pminus] using this

lemma grade_decomposition (v : DoubledSpace E) :
    v = gradePlusPart (E := E) v + gradeMinusPart (E := E) v := by
  have := CartanInvolution.decompose
    (C := (inferInstance : CartanInvolution (DoubledSpace E))) v
  simpa [gradePlusPart, gradeMinusPart] using this

lemma spectralEpsilon_swaps_grades_plus_to_minus {v : DoubledSpace E}
    (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (spectralEpsilon (E := E) v) := by
  rcases v with ⟨x, y⟩
  have hpair : (y, x) = (x, y) := by
    simpa [inGradePlus, modularJ] using hv
  have hxy : y = x := by simpa using congrArg Prod.fst hpair
  subst hxy
  simp [inGradeMinus, modularJ, spectralEpsilon]

lemma spectralEpsilon_swaps_grades_minus_to_plus {v : DoubledSpace E}
    (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) (spectralEpsilon (E := E) v) := by
  rcases v with ⟨x, y⟩
  have hpair : (y, x) = (-x, -y) := by
    simpa [inGradeMinus, modularJ] using hv
  have hxy : y = -x := by simpa using congrArg Prod.fst hpair
  subst hxy
  simp [inGradePlus, modularJ, spectralEpsilon]

def gradeConj (A : EndE (E := E)) : EndE (E := E) :=
  modularJ (E := E) * A * modularJ (E := E)

def evenLieSubalgebra : LieSubalgebra ℝ (EndE (E := E)) where
  carrier := {A | isEven (E := E) A}
  zero_mem' := by
    unfold isEven
    simp
  add_mem' := by
    intro A B hA hB
    unfold isEven at *
    simp [mul_add, add_mul, hA, hB]
  smul_mem' := by
    intro a A hA
    unfold isEven at *
    simp [hA, mul_assoc]
  lie_mem' := by
    intro A B hA hB
    exact even_closed_comm (E := E) hA hB

def oddSubmodule : Submodule ℝ (EndE (E := E)) where
  carrier := {A | isOdd (E := E) A}
  zero_mem' := by
    unfold isOdd
    simp
  add_mem' := by
    intro A B hA hB
    unfold isOdd at *
    simp [mul_add, add_mul, hA, hB, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  smul_mem' := by
    intro a A hA
    unfold isOdd at *
    simp [hA, mul_assoc]

lemma bracket_even_even_mem_even {A B : EndE (E := E)}
    (hA : isEven (E := E) A) (hB : isEven (E := E) B) :
    isEven (E := E) (clmComm (E := E) A B) :=
  even_closed_comm (E := E) hA hB

lemma bracket_even_odd_mem_odd {A B : EndE (E := E)}
    (hA : isEven (E := E) A) (hB : isOdd (E := E) B) :
    isOdd (E := E) (clmComm (E := E) A B) := by
  unfold isEven isOdd clmComm at *
  -- J(AB-BA) = -(AB-BA)J using J*A=A*J and J*B=-(B*J)
  calc
    modularJ (E := E) * (A * B - B * A)
        = (A * (modularJ (E := E))) * B - (-(B * modularJ (E := E))) * A := by
            simp [mul_assoc, hA, hB, mul_sub, sub_eq_add_neg]
    _ = -((A * B - B * A) * modularJ (E := E)) := by
            simp [mul_assoc, sub_mul, mul_sub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

lemma bracket_odd_odd_mem_even {A B : EndE (E := E)}
    (hA : isOdd (E := E) A) (hB : isOdd (E := E) B) :
    isEven (E := E) (clmComm (E := E) A B) := by
  unfold isEven isOdd clmComm at *
  calc
    modularJ (E := E) * (A * B - B * A)
        = (-(A * modularJ (E := E))) * B - (-(B * modularJ (E := E))) * A := by
            simp [mul_assoc, hA, hB, mul_sub, sub_eq_add_neg]
    _ = (A * B - B * A) * modularJ (E := E) := by
            simp [mul_assoc, sub_mul, mul_sub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

def oddTriple (A B C : EndE (E := E)) : EndE (E := E) :=
  clmComm (E := E) (clmComm (E := E) A B) C

lemma odd_triple_mem_odd {A B C : EndE (E := E)}
    (hA : isOdd (E := E) A) (hB : isOdd (E := E) B) (hC : isOdd (E := E) C) :
    isOdd (E := E) (oddTriple (E := E) A B C) := by
  unfold oddTriple
  exact bracket_even_odd_mem_odd (E := E)
    (bracket_odd_odd_mem_even (E := E) hA hB) hC

noncomputable def gradePlusProj : EndE (E := E) :=
  ((2 : ℝ)⁻¹) • ((1 : EndE (E := E)) + modularJ (E := E))

noncomputable def gradeMinusProj : EndE (E := E) :=
  ((2 : ℝ)⁻¹) • ((1 : EndE (E := E)) - modularJ (E := E))

noncomputable def spectralPlusProj : EndE (E := E) :=
  ((2 : ℝ)⁻¹) • ((1 : EndE (E := E)) + spectralEpsilon (E := E))

noncomputable def spectralMinusProj : EndE (E := E) :=
  ((2 : ℝ)⁻¹) • ((1 : EndE (E := E)) - spectralEpsilon (E := E))

@[simp] lemma gradePlusProj_apply (v : DoubledSpace E) :
    gradePlusProj (E := E) v = gradePlusPart (E := E) v := by
  simp [gradePlusProj, gradePlusPart, CartanInvolution.Pplus, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc]

@[simp] lemma gradeMinusProj_apply (v : DoubledSpace E) :
    gradeMinusProj (E := E) v = gradeMinusPart (E := E) v := by
  simp [gradeMinusProj, gradeMinusPart, CartanInvolution.Pminus, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc]

@[simp] lemma spectralPlusProj_apply (v : DoubledSpace E) :
    spectralPlusProj (E := E) v = (v.1, 0) := by
  rcases v with ⟨x, y⟩
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
  ext
  · calc
      (spectralPlusProj (E := E) (x, y)).1
          = ((2 : ℝ)⁻¹) • x + ((2 : ℝ)⁻¹) • x := by
              simp [spectralPlusProj, spectralEpsilon, add_smul, smul_add]
      _ = x := by
              simp [←add_smul, hhalf]
  · simp [spectralPlusProj, spectralEpsilon, add_smul, smul_add]

@[simp] lemma spectralMinusProj_apply (v : DoubledSpace E) :
    spectralMinusProj (E := E) v = (0, v.2) := by
  rcases v with ⟨x, y⟩
  have hhalf : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
  ext
  · simp [spectralMinusProj, spectralEpsilon, sub_eq_add_neg, add_smul, smul_add]
  · calc
      (spectralMinusProj (E := E) (x, y)).2
          = ((2 : ℝ)⁻¹) • y + ((2 : ℝ)⁻¹) • y := by
              simp [spectralMinusProj, spectralEpsilon, sub_eq_add_neg, add_smul, smul_add]
      _ = y := by
              simp [←add_smul, hhalf]

lemma gradePlusProj_idempotent :
    (gradePlusProj (E := E)) * (gradePlusProj (E := E)) = gradePlusProj (E := E) := by
  ext v
  -- direct computation on vectors using J^2 = 1
  rcases v with ⟨x, y⟩
  simp [gradePlusProj, modularJ, mul_assoc, add_assoc, add_comm, add_left_comm, smul_add,
        add_smul, sub_eq_add_neg, modularJ_involution, one_mul, mul_one]

lemma projector_commutator_gradePlus_spectralPlus :
    clmComm (E := E) (gradePlusProj (E := E)) (spectralPlusProj (E := E))
      = ((4 : ℝ)⁻¹) • clmComm (E := E) (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  ext v
  simp [clmComm, gradePlusProj, spectralPlusProj, sub_eq_add_neg, smul_add, smul_smul, mul_add,
        add_mul, mul_assoc, add_assoc, add_left_comm, add_comm]
  have hscalar : ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) = (4 : ℝ)⁻¹ := by norm_num
  simp [hscalar]

lemma projector_commutator_gradePlus_spectralPlus_eq_half_complexI :
    clmComm (E := E) (gradePlusProj (E := E)) (spectralPlusProj (E := E))
      = ((2 : ℝ)⁻¹) • complexI (E := E) := by
  -- reduce to the previous lemma + anticommute relation, then simplify
  rw [projector_commutator_gradePlus_spectralPlus (E := E)]
  have hanti := modularJ_spectralEpsilon_anticommute (E := E)
  -- clmComm(J,ε) = Jε - εJ = Jε - (-(Jε)) = 2(Jε)
  have hcomm : clmComm (E := E) (modularJ (E := E)) (spectralEpsilon (E := E))
      = (2 : ℝ) • ((modularJ (E := E)) * (spectralEpsilon (E := E))) := by
    simp [clmComm, hanti, two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  calc
    ((4 : ℝ)⁻¹) • clmComm (E := E) (modularJ (E := E)) (spectralEpsilon (E := E))
        = ((4 : ℝ)⁻¹) • ((2 : ℝ) • ((modularJ (E := E)) * (spectralEpsilon (E := E)))) := by
            simp [hcomm]
    _ = ((2 : ℝ)⁻¹) • complexI (E := E) := by
            have hscalar : ((4 : ℝ)⁻¹ * (2 : ℝ)) = (2 : ℝ)⁻¹ := by norm_num
            -- complexI = J * ε as multiplication/comp
            simp [complexI, smul_smul, hscalar, mul_assoc]

def splittingIncompatible : Prop :=
  clmComm (E := E) (gradePlusProj (E := E)) (spectralPlusProj (E := E)) ≠ 0

lemma complexI_ne_zero [Nontrivial E] : complexI (E := E) ≠ 0 := by
  intro hI
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  have hAt : complexI (E := E) (x, 0) = (0 : DoubledSpace E) := by
    simpa using congrArg (fun T => T (x, 0)) hI
  have hx0 : x = 0 := by
    simpa [complexI, modularJ, spectralEpsilon] using congrArg Prod.snd hAt
  exact hx hx0

lemma splittingIncompatible_of_nontrivial [Nontrivial E] :
    splittingIncompatible (E := E) := by
  intro hSplit
  have hsmul0 : ((2 : ℝ)⁻¹) • complexI (E := E) = 0 := by
    -- rewrite mismatch as (1/2)•I, then use hSplit
    have : clmComm (E := E) (gradePlusProj (E := E)) (spectralPlusProj (E := E))
        = ((2 : ℝ)⁻¹) • complexI (E := E) :=
      projector_commutator_gradePlus_spectralPlus_eq_half_complexI (E := E)
    simpa [this] using congrArg (fun T => ((2 : ℝ)⁻¹) • complexI (E := E)) (by rfl)
  have hhalf : ((2 : ℝ)⁻¹) ≠ 0 := by norm_num
  exact (complexI_ne_zero (E := E)) ((smul_eq_zero.mp hsmul0).resolve_left hhalf)

noncomputable def creationLike : EndE (E := E) := gradePlusProj (E := E)
noncomputable def annihilationLike : EndE (E := E) := gradeMinusProj (E := E)

lemma creationLike_apply (v : DoubledSpace E) :
    creationLike (E := E) v = gradePlusPart (E := E) v := by
  simp [creationLike, gradePlusProj_apply]

lemma annihilationLike_apply (v : DoubledSpace E) :
    annihilationLike (E := E) v = gradeMinusPart (E := E) v := by
  simp [annihilationLike, gradeMinusProj_apply]

lemma spectralEpsilon_isOdd : isOdd (E := E) (spectralEpsilon (E := E)) := by
  simpa [isOdd] using modularJ_spectralEpsilon_anticommute (E := E)

end InfoGeometry.Krein
