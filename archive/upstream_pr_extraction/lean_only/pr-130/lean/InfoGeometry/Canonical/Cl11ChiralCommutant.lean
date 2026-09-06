import InfoGeometry.Canonical.SplitCliffordFiniteCAR

/-!
# The chiral-preserving commutant in the native finite `M₄(ℝ)` carrier

The full dyadic stage is not a product of two matrix algebras.  This owner
isolates the honest even sector: the commutant of the fixed sheet grading.
The complementary odd sector is characterized by the corresponding
anti-commutation equation.
-/

namespace InfoGeometry.Canonical.Cl11ChiralCommutant

open InfoGeometry.Canonical.SplitCliffordFiniteCAR

abbrev M4R := SplitCliffordFiniteCAR.M4R

def grading : M4R := !![(1 : ℝ), 0, 0, 0;
  0, 1, 0, 0;
  0, 0, -1, 0;
  0, 0, 0, -1]

def ChiralEven (M : M4R) : Prop := M * grading = grading * M

def ChiralOdd (M : M4R) : Prop := M * grading = -(grading * M)

/-! The canonical even/odd projections for the fixed grading. -/

noncomputable def chiralEvenPart (M : M4R) : M4R :=
  (1 / 2 : ℝ) • (M + grading * M * grading)

noncomputable def chiralOddPart (M : M4R) : M4R :=
  (1 / 2 : ℝ) • (M - grading * M * grading)

@[simp] theorem grading_sq : grading * grading = (1 : M4R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [grading, Matrix.mul_apply, Fin.sum_univ_four]

theorem chiralEven_add {M N : M4R}
    (hM : ChiralEven M) (hN : ChiralEven N) :
    ChiralEven (M + N) := by
  unfold ChiralEven at hM hN ⊢
  simp only [add_mul, mul_add, hM, hN]

theorem chiralOdd_add {M N : M4R}
    (hM : ChiralOdd M) (hN : ChiralOdd N) :
    ChiralOdd (M + N) := by
  unfold ChiralOdd at hM hN ⊢
  simp only [add_mul, mul_add, hM, hN, neg_add]

theorem chiralEven_neg {M : M4R}
    (hM : ChiralEven M) :
    ChiralEven (-M) := by
  unfold ChiralEven at hM ⊢
  simp only [neg_mul, mul_neg, hM]

theorem chiralOdd_neg {M : M4R}
    (hM : ChiralOdd M) :
    ChiralOdd (-M) := by
  unfold ChiralOdd at hM ⊢
  simp only [neg_mul, mul_neg, hM, neg_neg]

theorem chiralEven_mul_even {M N : M4R}
    (hM : ChiralEven M) (hN : ChiralEven N) :
    ChiralEven (M * N) := by
  unfold ChiralEven at hM hN ⊢
  calc
    M * N * grading = M * (N * grading) := by rw [Matrix.mul_assoc]
    _ = M * (grading * N) := by rw [hN]
    _ = (M * grading) * N := by rw [Matrix.mul_assoc]
    _ = (grading * M) * N := by rw [hM]
    _ = grading * (M * N) := by rw [Matrix.mul_assoc]

theorem chiralEven_mul_odd {M N : M4R}
    (hM : ChiralEven M) (hN : ChiralOdd N) :
    ChiralOdd (M * N) := by
  unfold ChiralEven at hM
  unfold ChiralOdd at hN ⊢
  calc
    M * N * grading = M * (N * grading) := by rw [Matrix.mul_assoc]
    _ = M * (-(grading * N)) := by rw [hN]
    _ = -(M * (grading * N)) := by simp
    _ = -((M * grading) * N) := by rw [Matrix.mul_assoc]
    _ = -((grading * M) * N) := by rw [hM]
    _ = -(grading * (M * N)) := by rw [Matrix.mul_assoc]

theorem chiralOdd_mul_even {M N : M4R}
    (hM : ChiralOdd M) (hN : ChiralEven N) :
    ChiralOdd (M * N) := by
  unfold ChiralOdd at hM ⊢
  unfold ChiralEven at hN
  calc
    M * N * grading = M * (N * grading) := by rw [Matrix.mul_assoc]
    _ = M * (grading * N) := by rw [hN]
    _ = (M * grading) * N := by rw [Matrix.mul_assoc]
    _ = (-(grading * M)) * N := by rw [hM]
    _ = -(grading * M * N) := by simp [Matrix.mul_assoc]
    _ = -(grading * (M * N)) := by rw [Matrix.mul_assoc]

theorem chiralOdd_mul_odd {M N : M4R}
    (hM : ChiralOdd M) (hN : ChiralOdd N) :
    ChiralEven (M * N) := by
  unfold ChiralOdd at hM hN
  unfold ChiralEven
  calc
    M * N * grading = M * (N * grading) := by rw [Matrix.mul_assoc]
    _ = M * (-(grading * N)) := by rw [hN]
    _ = -(M * (grading * N)) := by simp
    _ = -((M * grading) * N) := by rw [Matrix.mul_assoc]
    _ = -((-(grading * M)) * N) := by rw [hM]
    _ = (grading * M) * N := by simp
    _ = grading * (M * N) := by rw [Matrix.mul_assoc]

theorem chiralEvenPart_add_chiralOddPart (M : M4R) :
    chiralEvenPart M + chiralOddPart M = M := by
  unfold chiralEvenPart chiralOddPart
  module

theorem chiralEvenPart_is_even (M : M4R) :
    ChiralEven (chiralEvenPart M) := by
  unfold ChiralEven chiralEvenPart
  simp only [smul_mul_assoc, mul_smul_comm]
  change (1 / 2 : ℝ) • ((M + grading * M * grading) * grading) =
    (1 / 2 : ℝ) • (grading * (M + grading * M * grading))
  congr 1
  calc
    (M + grading * M * grading) * grading =
        M * grading + (grading * M) * (grading * grading) := by
          simp only [add_mul, Matrix.mul_assoc]
    _ = grading * (M + grading * M * grading) := by
          simp [mul_add, Matrix.mul_assoc, grading_sq]
          rw [← Matrix.mul_assoc grading grading (M * grading),
            grading_sq, one_mul]
          abel

theorem chiralOddPart_is_odd (M : M4R) :
    ChiralOdd (chiralOddPart M) := by
  unfold ChiralOdd chiralOddPart
  simp only [smul_mul_assoc, mul_smul_comm]
  change (1 / 2 : ℝ) • ((M - grading * M * grading) * grading) =
    -((1 / 2 : ℝ) • (grading * (M - grading * M * grading)))
  rw [show -((1 / 2 : ℝ) • (grading * (M - grading * M * grading))) =
      (1 / 2 : ℝ) • (-(grading * (M - grading * M * grading))) by module]
  congr 1
  calc
    (M - grading * M * grading) * grading =
        M * grading - (grading * M) * (grading * grading) := by
          simp only [sub_mul, Matrix.mul_assoc]
    _ = -(grading * (M - grading * M * grading)) := by
          simp [mul_sub, Matrix.mul_assoc, grading_sq]
          rw [← Matrix.mul_assoc grading grading (M * grading),
            grading_sq, one_mul]

theorem chiralEvenPart_of_even {M : M4R}
    (hM : ChiralEven M) :
    chiralEvenPart M = M := by
  have hconj : grading * M * grading = M := by
    calc
      grading * M * grading = (M * grading) * grading := by rw [hM]
      _ = M * (grading * grading) := by rw [Matrix.mul_assoc]
      _ = M := by rw [grading_sq, mul_one]
  unfold chiralEvenPart
  rw [hconj]
  module

theorem chiralOddPart_of_odd {M : M4R}
    (hM : ChiralOdd M) :
    chiralOddPart M = M := by
  have hconj : grading * M * grading = -M := by
    have hM' : grading * M = -(M * grading) := by
      have h := congrArg Neg.neg hM
      simpa only [neg_neg] using h.symm
    calc
      grading * M * grading = -(M * grading) * grading := by rw [hM']
      _ = -(M * (grading * grading)) := by
        rw [neg_mul, Matrix.mul_assoc]
      _ = -M := by rw [grading_sq, mul_one]
  unfold chiralOddPart
  rw [hconj]
  module

end InfoGeometry.Canonical.Cl11ChiralCommutant
