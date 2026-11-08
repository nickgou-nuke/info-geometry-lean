import InfoGeometry.Krein.Clifford
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Module

open scoped InnerProductSpace

namespace InfoGeometry.Krein

namespace KreinGradedModule

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]

/-- Endomorphism algebra on a graded Krein carrier. -/
abbrev EndH (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] := H →L[ℝ] H

/-- Ordinary commutator `[A,B] = AB - BA`. -/
noncomputable def comm (A B : EndH H) : EndH H := A * B - B * A

/-- Ordinary anticommutator `{A,B} = AB + BA`. -/
noncomputable def anticomm (A B : EndH H) : EndH H := A * B + B * A

omit [CompleteSpace H] [KreinSpace H] [KreinGradedModule H] in
/-- Ordinary commutator `⁅A, B⁆` in `LieAlgebra`. -/
lemma comm_eq_lie (A B : EndH H) : comm A B = ⁅A, B⁆ := rfl

@[simp] lemma gradeConj_zero :
    gradeConj (H := H) 0 = 0 := by
  unfold gradeConj
  simp

@[simp] lemma gradeConj_add (A B : EndH H) :
    gradeConj (H := H) (A + B) = gradeConj (H := H) A + gradeConj (H := H) B := by
  unfold gradeConj
  simp

@[simp] lemma gradeConj_neg (A : EndH H) :
    gradeConj (H := H) (-A) = -gradeConj (H := H) A := by
  unfold gradeConj
  simp

@[simp] lemma gradeConj_sub (A B : EndH H) :
    gradeConj (H := H) (A - B) = gradeConj (H := H) A - gradeConj (H := H) B := by
  simp [sub_eq_add_neg]

@[simp] lemma gradeConj_smul (r : ℝ) (A : EndH H) :
    gradeConj (H := H) (r • A) = r • gradeConj (H := H) A := by
  unfold gradeConj
  simp

lemma gradeConj_involutive (A : EndH H) :
    gradeConj (H := H) (gradeConj (H := H) A) = A := by
  ext x
  simp [gradeConj, ContinuousLinearMap.comp_assoc, KreinGradedModule.grade_invol]

/-- Even projection in the `Γ`-conjugation splitting. -/
noncomputable def evenPart (A : EndH H) : EndH H :=
  ((2 : ℝ)⁻¹) • (A + gradeConj (H := H) A)

/-- Odd projection in the `Γ`-conjugation splitting. -/
noncomputable def oddPart (A : EndH H) : EndH H :=
  ((2 : ℝ)⁻¹) • (A - gradeConj (H := H) A)

lemma evenPart_add_oddPart (A : EndH H) :
    evenPart (H := H) A + oddPart (H := H) A = A := by
  ext x
  simp [evenPart, oddPart, sub_eq_add_neg, smul_add]
  module

lemma evenPart_isEven (A : EndH H) :
    IsEven (H := H) (evenPart (H := H) A) := by
  unfold IsEven evenPart
  simp [gradeConj_involutive, add_comm]

lemma oddPart_isOdd (A : EndH H) :
    IsOdd (H := H) (oddPart (H := H) A) := by
  unfold IsOdd oddPart
  simp [gradeConj_involutive, sub_eq_add_neg]

lemma evenPart_eq_of_isEven {A : EndH H} (hA : IsEven (H := H) A) :
    evenPart (H := H) A = A := by
  unfold evenPart IsEven at *
  rw [hA]
  have hsum : A + A = (2 : ℝ) • A := by simp [two_smul]
  rw [hsum]
  simp [smul_smul]

lemma oddPart_eq_zero_of_isEven {A : EndH H} (hA : IsEven (H := H) A) :
    oddPart (H := H) A = 0 := by
  unfold oddPart IsEven at *
  rw [hA]
  simp

lemma evenPart_eq_zero_of_isOdd {A : EndH H} (hA : IsOdd (H := H) A) :
    evenPart (H := H) A = 0 := by
  unfold evenPart IsOdd at *
  rw [hA]
  simp

lemma oddPart_eq_of_isOdd {A : EndH H} (hA : IsOdd (H := H) A) :
    oddPart (H := H) A = A := by
  unfold oddPart IsOdd at *
  rw [hA]
  have hsum : A - -A = (2 : ℝ) • A := by simp [two_smul]
  rw [hsum]
  simp [smul_smul]

/--
Graded commutator assembled from the `Γ`-even/odd decomposition.
For homogeneous operators this reduces to commutator/anticommutator.
-/
noncomputable def superComm (A B : EndH H) : EndH H :=
  comm (evenPart (H := H) A) (evenPart (H := H) B)
    + comm (evenPart (H := H) A) (oddPart (H := H) B)
    + comm (oddPart (H := H) A) (evenPart (H := H) B)
    + anticomm (oddPart (H := H) A) (oddPart (H := H) B)

lemma superComm_even_even
    {A B : EndH H}
    (hA : IsEven (H := H) A)
    (hB : IsEven (H := H) B) :
    superComm (H := H) A B = comm (H := H) A B := by
  unfold superComm
  rw [evenPart_eq_of_isEven (H := H) hA, evenPart_eq_of_isEven (H := H) hB]
  rw [oddPart_eq_zero_of_isEven (H := H) hA, oddPart_eq_zero_of_isEven (H := H) hB]
  simp [comm, anticomm]

lemma superComm_even_odd
    {A B : EndH H}
    (hA : IsEven (H := H) A)
    (hB : IsOdd (H := H) B) :
    superComm (H := H) A B = comm (H := H) A B := by
  unfold superComm
  rw [evenPart_eq_of_isEven (H := H) hA, oddPart_eq_zero_of_isEven (H := H) hA]
  rw [evenPart_eq_zero_of_isOdd (H := H) hB, oddPart_eq_of_isOdd (H := H) hB]
  simp [comm, anticomm]

lemma superComm_odd_even
    {A B : EndH H}
    (hA : IsOdd (H := H) A)
    (hB : IsEven (H := H) B) :
    superComm (H := H) A B = comm (H := H) A B := by
  unfold superComm
  rw [evenPart_eq_zero_of_isOdd (H := H) hA, oddPart_eq_of_isOdd (H := H) hA]
  rw [evenPart_eq_of_isEven (H := H) hB, oddPart_eq_zero_of_isEven (H := H) hB]
  simp [comm, anticomm]

lemma superComm_odd_odd
    {A B : EndH H}
    (hA : IsOdd (H := H) A)
    (hB : IsOdd (H := H) B) :
    superComm (H := H) A B = anticomm (H := H) A B := by
  unfold superComm
  rw [evenPart_eq_zero_of_isOdd (H := H) hA, oddPart_eq_of_isOdd (H := H) hA]
  rw [evenPart_eq_zero_of_isOdd (H := H) hB, oddPart_eq_of_isOdd (H := H) hB]
  simp [comm, anticomm]

@[simp] lemma superComm_zero_left (B : EndH H) :
    superComm (H := H) 0 B = 0 := by
  unfold superComm evenPart oddPart comm anticomm
  simp

end KreinGradedModule

end InfoGeometry.Krein
