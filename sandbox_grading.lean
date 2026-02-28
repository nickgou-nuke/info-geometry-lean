import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic
import InfoGeometry.Cartan.Involution
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Krein

open InfoGeometry.Cartan

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Commutator bracket on doubled-space endomorphisms. -/
def clmComm (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  A.comp B - B.comp A

lemma clmComm_eq_lie (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    clmComm A B = ⁅A, B⁆ := rfl

noncomputable def jordanProd (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (A.comp B + B.comp A)

def isDerivation
    (D :
      (DoubledSpace E →L[ℝ] DoubledSpace E) →
      (DoubledSpace E →L[ℝ] DoubledSpace E)) : Prop :=
  ∀ A B, D (jordanProd A B) = jordanProd (D A) B + jordanProd A (D B)

/-- Even operators commute with the grading involution `J`. -/
def isEven (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = A.comp (modularJ (E := E))

/-- Backward-compatible alias for even operators. -/
abbrev isGradeZero (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  isEven (E := E) A

lemma jordanProd_comm (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    jordanProd A B = jordanProd B A := by
  simp [jordanProd, add_comm]

lemma comp_eq_jordan_add_half_comm (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    A.comp B = jordanProd A B + ((2 : ℝ)⁻¹) • clmComm A B := by
  apply ContinuousLinearMap.ext
  intro v
  simp [jordanProd, clmComm]
  have h2 : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  calc
    (2 : ℝ)⁻¹ • (A (B v) + B (A v)) + (2 : ℝ)⁻¹ • (A (B v) - B (A v))
        = (2 : ℝ)⁻¹ • (A (B v) + B (A v) + (A (B v) - B (A v))) := by rw [smul_add]
    _ = (2 : ℝ)⁻¹ • (A (B v) + A (B v)) := by abel_nf
    _ = ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) • A (B v) := by rw [add_smul]; abel_nf
    _ = (1 : ℝ) • A (B v) := by rw [h2]
    _ = A (B v) := by rw [one_smul]

lemma even_closed_comm {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isEven (E := E) A) (hB : isEven (E := E) B) :
    isEven (E := E) (clmComm A B) := by
  unfold isEven at *
  rw [clmComm, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  rw [ContinuousLinearMap.comp_assoc, hA, ← ContinuousLinearMap.comp_assoc]
  rw [ContinuousLinearMap.comp_assoc, hB, ← ContinuousLinearMap.comp_assoc]
  rw [ContinuousLinearMap.comp_assoc, hB, ← ContinuousLinearMap.comp_assoc]
  rw [ContinuousLinearMap.comp_assoc, hA, ← ContinuousLinearMap.comp_assoc]

lemma gradeZero_closed_comm {A B : DoubledSpace E →L[ℝ] DoubledSpace E}
    (hA : isGradeZero (E := E) A) (hB : isGradeZero (E := E) B) :
    isGradeZero (E := E) (clmComm A B) :=
  even_closed_comm (E := E) hA hB

def inGradePlus (v : DoubledSpace E) : Prop := modularJ (E := E) v = v
def inGradeMinus (v : DoubledSpace E) : Prop := modularJ (E := E) v = -v

/-! LIFTED PROJECTORS using generic Cartan Involution -/
noncomputable def gradePlusPart (v : DoubledSpace E) : DoubledSpace E :=
  CartanInvolution.Pplus (C := instCartanInvolutionDoubled) v

noncomputable def gradeMinusPart (v : DoubledSpace E) : DoubledSpace E :=
  CartanInvolution.Pminus (C := instCartanInvolutionDoubled) v

lemma gradePlusPart_in_plus (v : DoubledSpace E) :
    inGradePlus (E := E) (gradePlusPart (E := E) v) := by
  have h := CartanInvolution.theta_Pplus (C := instCartanInvolutionDoubled) v
  simpa [inGradePlus, gradePlusPart, instCartanInvolutionDoubled] using h

lemma gradeMinusPart_in_minus (v : DoubledSpace E) :
    inGradeMinus (E := E) (gradeMinusPart (E := E) v) := by
  have h := CartanInvolution.theta_Pminus (C := instCartanInvolutionDoubled) v
  simpa [inGradeMinus, gradeMinusPart, instCartanInvolutionDoubled] using h

lemma grade_decomposition (v : DoubledSpace E) :
    v = gradePlusPart (E := E) v + gradeMinusPart (E := E) v := by
  have h := CartanInvolution.decompose (C := instCartanInvolutionDoubled) v
  simpa [gradePlusPart, gradeMinusPart] using h

def isOdd (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modularJ (E := E)).comp A = -(A.comp (modularJ (E := E)))

noncomputable def gradePlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + modularJ (E := E))

noncomputable def gradeMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) - modularJ (E := E))

noncomputable def spectralPlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectralEpsilon (E := E))

noncomputable def spectralMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) - spectralEpsilon (E := E))

@[simp] lemma gradePlusProj_apply (v : DoubledSpace E) :
    gradePlusProj (E := E) v = gradePlusPart (E := E) v := by
  simp [gradePlusPart, gradePlusProj, CartanInvolution.Pplus, instCartanInvolutionDoubled]

@[simp] lemma gradeMinusProj_apply (v : DoubledSpace E) :
    gradeMinusProj (E := E) v = gradeMinusPart (E := E) v := by
  simp [gradeMinusPart, gradeMinusProj, CartanInvolution.Pminus, instCartanInvolutionDoubled]

/-- No-`sorry` idempotence: `P₊ ∘ P₊ = P₊` for `P₊ = (1/2)(Id + J)`. -/
lemma gradePlusProj_idempotent :
    (gradePlusProj (E := E)).comp (gradePlusProj (E := E)) = gradePlusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  simp [gradePlusProj, modularJ]
  have h2 : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  apply Prod.ext
  · abel_nf
    calc
      (2 : ℝ)⁻¹ • (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • (2 : ℝ)⁻¹ • y + ((2 : ℝ)⁻¹ • (2 : ℝ)⁻¹ • y + (2 : ℝ)⁻¹ • (2 : ℝ)⁻¹ • x)
          = ((2:ℝ)⁻¹ * (2:ℝ)⁻¹) • (x + y + (y + x)) := by simp only [smul_add, smul_smul, add_assoc, add_left_comm]; abel_nf
      _ = ((2:ℝ)⁻¹ * (2:ℝ)⁻¹) • (2 • (x + y)) := by abel_nf; simp [two_smul]
      _ = (((2:ℝ)⁻¹ + (2:ℝ)⁻¹) * (2:ℝ)⁻¹) • (x + y) := by simp [smul_smul]; norm_num
      _ = (1 * (2:ℝ)⁻¹) • (x + y) := by rw [h2]
      _ = (2:ℝ)⁻¹ • (x + y) := by rw [one_mul]
  · abel_nf
    calc
      (2 : ℝ)⁻¹ • (2 : ℝ)⁻¹ • y + (2 : ℝ)⁻¹ • (2 : ℝ)⁻¹ • x + ((2 : ℝ)⁻¹ • (2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • (2 : ℝ)⁻¹ • y)
          = ((2:ℝ)⁻¹ * (2:ℝ)⁻¹) • (y + x + (x + y)) := by simp only [smul_add, smul_smul, add_assoc, add_left_comm]; abel_nf
      _ = ((2:ℝ)⁻¹ * (2:ℝ)⁻¹) • (2 • (y + x)) := by abel_nf; simp [two_smul]
      _ = (((2:ℝ)⁻¹ + (2:ℝ)⁻¹) * (2:ℝ)⁻¹) • (y + x) := by simp [smul_smul]; norm_num
      _ = (1 * (2:ℝ)⁻¹) • (y + x) := by rw [h2]
      _ = (2:ℝ)⁻¹ • (y + x) := by rw [one_mul]

end InfoGeometry.Krein
