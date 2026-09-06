import Mathlib

/-!
# Real `(4,4)` carrier for the split-octonion Jordan layer

The carrier is the explicit real coordinate space `Fin 8 → ℝ`.  This owner
records the normalized form and its positive/negative Witt-coordinate basis.
It does not assert a structure-algebra or TKK equivalence.
-/

namespace InfoGeometry.Canonical.SplitOctonionJordanForm

abbrev MiddleCarrier := Fin 8 → ℝ

/-- The normalized diagonal `(4,4)` bilinear form. -/
def beta44 (x y : MiddleCarrier) : ℝ :=
  ∑ i : Fin 8, (if i.val < 4 then x i * y i else -(x i * y i))

@[simp] theorem beta44_apply (x y : MiddleCarrier) :
    beta44 x y =
      x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 -
        (x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7) := by
  simp [beta44, Fin.sum_univ_succ]
  ring

theorem beta44_symmetric (x y : MiddleCarrier) :
    beta44 x y = beta44 y x := by
  simp [beta44, mul_comm]

theorem beta44_add_left (x y z : MiddleCarrier) :
    beta44 (x + y) z = beta44 x z + beta44 y z := by
  simp only [beta44, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i.val < 4 <;> simp [h] <;> ring

theorem beta44_smul_left (r : ℝ) (x y : MiddleCarrier) :
    beta44 (r • x) y = r * beta44 x y := by
  simp only [beta44, Pi.smul_apply]
  calc
    (∑ i : Fin 8,
        if i.val < 4 then (r • x i) * y i else -((r • x i) * y i)) =
      ∑ i : Fin 8, r * (if i.val < 4 then x i * y i else -(x i * y i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : i.val < 4 <;> simp [h] <;> ring
    _ = r * ∑ i : Fin 8, (if i.val < 4 then x i * y i else -(x i * y i)) := by
         rw [Finset.mul_sum]

theorem beta44_add_right (x y z : MiddleCarrier) :
    beta44 x (y + z) = beta44 x y + beta44 x z := by
  rw [beta44_symmetric x, beta44_add_left, beta44_symmetric y x,
    beta44_symmetric z x]

theorem beta44_smul_right (r : ℝ) (x y : MiddleCarrier) :
    beta44 x (r • y) = r * beta44 x y := by
  rw [beta44_symmetric x, beta44_smul_left, beta44_symmetric y x]

/-- Positive coordinate basis vectors. -/
def positiveBasis (i : Fin 4) : MiddleCarrier :=
  Pi.single ⟨i.val, by omega⟩ 1

/-- Negative coordinate basis vectors. -/
def negativeBasis (i : Fin 4) : MiddleCarrier :=
  Pi.single ⟨i.val + 4, by omega⟩ 1

@[simp] theorem beta44_positiveBasis (i j : Fin 4) :
    beta44 (positiveBasis i) (positiveBasis j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [beta44, positiveBasis, Pi.single_apply, Fin.sum_univ_succ]

@[simp] theorem beta44_negativeBasis (i j : Fin 4) :
    beta44 (negativeBasis i) (negativeBasis j) = if i = j then -1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [beta44, negativeBasis, Pi.single_apply, Fin.sum_univ_succ]

@[simp] theorem beta44_positive_negative (i j : Fin 4) :
    beta44 (positiveBasis i) (negativeBasis j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [beta44, positiveBasis, negativeBasis, Pi.single_apply,
      Fin.sum_univ_succ]

theorem beta44_nondegenerate_left (x : MiddleCarrier)
    (hx : ∀ y, beta44 x y = 0) : x = 0 := by
  funext i
  fin_cases i
  · have h := hx (positiveBasis 0)
    simpa [beta44, positiveBasis, Pi.single_apply, Fin.sum_univ_succ] using h
  · have h := hx (positiveBasis 1)
    simpa [beta44, positiveBasis, Pi.single_apply, Fin.sum_univ_succ] using h
  · have h := hx (positiveBasis 2)
    simpa [beta44, positiveBasis, Pi.single_apply, Fin.sum_univ_succ] using h
  · have h := hx (positiveBasis 3)
    simpa [beta44, positiveBasis, Pi.single_apply, Fin.sum_univ_succ] using h
  · have h := hx (negativeBasis 0)
    simpa [beta44, negativeBasis, Pi.single_apply, Fin.sum_univ_succ] using h
  · have h := hx (negativeBasis 1)
    simpa [beta44, negativeBasis, Pi.single_apply, Fin.sum_univ_succ] using h
  · have h := hx (negativeBasis 2)
    simpa [beta44, negativeBasis, Pi.single_apply, Fin.sum_univ_succ] using h
  · have h := hx (negativeBasis 3)
    simpa [beta44, negativeBasis, Pi.single_apply, Fin.sum_univ_succ] using h

theorem beta44_nondegenerate_right (y : MiddleCarrier)
    (hy : ∀ x, beta44 x y = 0) : y = 0 := by
  apply beta44_nondegenerate_left y
  intro x
  rw [beta44_symmetric]
  exact hy x

theorem beta44_signature_packet :
    (∀ i : Fin 4, beta44 (positiveBasis i) (positiveBasis i) = 1) ∧
      (∀ i : Fin 4, beta44 (negativeBasis i) (negativeBasis i) = -1) ∧
      (∀ i j : Fin 4, beta44 (positiveBasis i) (negativeBasis j) = 0) := by
  exact ⟨fun i => by simpa using beta44_positiveBasis i i,
    fun i => by simpa using beta44_negativeBasis i i,
    fun i j => beta44_positive_negative i j⟩

/-! ## Rank-two skew operators -/

def W (xi eta : MiddleCarrier) (z : MiddleCarrier) : MiddleCarrier :=
  beta44 eta z • xi - beta44 xi z • eta

theorem W_apply (xi eta z : MiddleCarrier) :
    W xi eta z = beta44 eta z • xi - beta44 xi z • eta := rfl

theorem W_skew (xi eta z w : MiddleCarrier) :
    beta44 (W xi eta z) w + beta44 z (W xi eta w) = 0 := by
  simp [W, beta44, Fin.sum_univ_succ]
  ring

end InfoGeometry.Canonical.SplitOctonionJordanForm
