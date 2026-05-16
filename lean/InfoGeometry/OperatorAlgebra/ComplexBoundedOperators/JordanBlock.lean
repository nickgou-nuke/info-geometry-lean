import Mathlib

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanBlock

Lean-native AFP `Jordan_Normal_Form.Jordan_Normal_Form` block layer.

This module starts the native Jordan-block corridor needed by the spectral-radius
growth bounds.  It provides the finite matrix definition of an AFP Jordan block,
its entry equations, upper-triangularity, and characteristic polynomial.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanBlock

open scoped BigOperators
open Polynomial

/-- AFP `jordan_block n a`: diagonal `a`, superdiagonal `1`, zero elsewhere. -/
def jordanBlock {R : Type*} [Zero R] [One R] (n : Nat) (a : R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then a else if i.val + 1 = j.val then 1 else 0

@[simp]
theorem jordanBlock_apply {R : Type*} [Zero R] [One R] {n : Nat} (a : R)
    (i j : Fin n) :
    jordanBlock n a i j = if i = j then a else if i.val + 1 = j.val then 1 else 0 :=
  rfl

@[simp]
theorem jordanBlock_apply_diag {R : Type*} [Zero R] [One R] {n : Nat} (a : R)
    (i : Fin n) :
    jordanBlock n a i i = a := by
  simp [jordanBlock]

@[simp]
theorem jordanBlock_apply_superdiag {R : Type*} [Zero R] [One R] {n : Nat} (a : R)
    {i j : Fin n} (hij : i.val + 1 = j.val) :
    jordanBlock n a i j = if i = j then a else 1 := by
  by_cases h : i = j
  · simp [jordanBlock, h]
  · simp [jordanBlock, h, hij]

/-- The nilpotent superdiagonal shift underlying a Jordan block. -/
def jordanShift {R : Type*} [Zero R] [One R] (n : Nat) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if i.val + 1 = j.val then 1 else 0

@[simp]
theorem jordanShift_apply {R : Type*} [Zero R] [One R] {n : Nat}
    (i j : Fin n) :
    jordanShift (R := R) n i j = if i.val + 1 = j.val then 1 else 0 :=
  rfl

/-- A Jordan block is the scalar diagonal plus the superdiagonal shift. -/
theorem jordanBlock_eq_scalar_add_shift {R : Type*} [Semiring R] {n : Nat} (a : R) :
    jordanBlock n a = (Matrix.scalar (Fin n)) a + jordanShift (R := R) n := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [jordanBlock, jordanShift, Matrix.scalar]
  · have hdiag : Matrix.diagonal (fun _ : Fin n => a) i j = 0 := by
      simp [Matrix.diagonal, hij]
    simp [jordanBlock, jordanShift, Matrix.scalar, hij]

/-- Closed formula for powers of the superdiagonal shift. -/
theorem jordanShift_pow_apply {R : Type*} [Semiring R] {n : Nat}
    (k : Nat) (i j : Fin n) :
    ((jordanShift (R := R) n) ^ k) i j =
      if i.val + k = j.val then 1 else 0 := by
  revert i j
  induction k with
  | zero =>
      intro i j
      by_cases hij : i = j
      · subst hij
        simp
      · have hval : i.val ≠ j.val := by
          intro h
          exact hij (Fin.ext h)
        simp [hval, hij]
  | succ k ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      by_cases htarget : i.val + (k + 1) = j.val
      · let x : Fin n := ⟨i.val + k, by omega⟩
        have hx_target : x.val + 1 = j.val := by
          simpa [x, Nat.add_assoc] using htarget
        have hix : i.val + k = x.val := by rfl
        have hsum :
            (∑ y : Fin n,
                ((jordanShift (R := R) n) ^ k) i y * jordanShift (R := R) n y j) =
              ((jordanShift (R := R) n) ^ k) i x * jordanShift (R := R) n x j := by
          refine Finset.sum_eq_single x ?_ ?_
          · intro y _ hyx
            have hnot_both : ¬ (i.val + k = y.val ∧ y.val + 1 = j.val) := by
              intro hboth
              apply hyx
              exact Fin.ext (by
                dsimp [x]
                exact hboth.1.symm)
            by_cases hiy : i.val + k = y.val
            · have hyj : ¬ y.val + 1 = j.val := by
                intro hyj
                exact hnot_both ⟨hiy, hyj⟩
              rw [ih i y]
              simp [hiy, jordanShift, hyj]
            · rw [ih i y]
              simp [hiy]
          · intro hxmem
            exact False.elim (hxmem (Finset.mem_univ x))
        rw [hsum, ih i x]
        simp [hix, jordanShift, hx_target, htarget]
      · have hsum_zero :
            (∑ y : Fin n,
                ((jordanShift (R := R) n) ^ k) i y * jordanShift (R := R) n y j) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro y _
          by_cases hiy : i.val + k = y.val
          · have hyj : ¬ y.val + 1 = j.val := by
              intro hyj
              apply htarget
              omega
            rw [ih i y]
            simp [hiy, jordanShift, hyj]
          · rw [ih i y]
            simp [hiy]
        rw [hsum_zero]
        simp [htarget]

/-- Binomial expansion of powers of a Jordan block into scalar and shift parts. -/
theorem jordanBlock_pow_expansion {R : Type*} [CommSemiring R] {n : Nat} (a : R)
    (k : Nat) :
    (jordanBlock n a) ^ k =
      ∑ m ∈ Finset.range (k + 1),
        ((Matrix.scalar (Fin n)) a) ^ m *
          (jordanShift (R := R) n) ^ (k - m) *
          (Nat.choose k m : Matrix (Fin n) (Fin n) R) := by
  rw [jordanBlock_eq_scalar_add_shift]
  exact
    (Matrix.scalar_commute (n := Fin n) a (fun _ => Commute.all _ _) (jordanShift (R := R) n)).add_pow k

/-- Entrywise form of one summand in the Jordan-block binomial expansion. -/
theorem jordanBlock_pow_expansion_term_apply {R : Type*} [CommSemiring R] {n : Nat}
    (a : R) (k m : Nat) (i j : Fin n) :
    (((Matrix.scalar (Fin n)) a) ^ m * (jordanShift (R := R) n) ^ (k - m) *
        (Nat.choose k m : Matrix (Fin n) (Fin n) R)) i j =
      (if i.val + (k - m) = j.val then a ^ m * (Nat.choose k m : R) else 0) := by
  rw [← map_pow (Matrix.scalar (Fin n)) a m]
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · by_cases h : i.val + (k - m) = j.val
      · simp [Matrix.scalar, jordanShift_pow_apply, Matrix.natCast_apply, h]
      · simp [Matrix.scalar, jordanShift_pow_apply, Matrix.natCast_apply, h]
    · intro b _ hb
      have hib : i ≠ b := fun h => hb h.symm
      simp [Matrix.scalar, Matrix.diagonal, hib]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  · intro b _ hb
    simp [Matrix.natCast_apply, hb]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/--
AFP `jordan_block_pow`, entrywise native Lean version.

For a Jordan block with eigenvalue `a`, the `(i,j)` entry of the `k`-th power is
the binomial coefficient on the `j - i` superdiagonal times the corresponding
power of `a`; entries below the diagonal are zero.
-/
theorem jordanBlock_pow_apply {R : Type*} [CommSemiring R] {n : Nat} (a : R)
    (k : Nat) (i j : Fin n) :
    ((jordanBlock n a) ^ k) i j =
      if i.val ≤ j.val then
        (Nat.choose k (j.val - i.val) : R) * a ^ (k + i.val - j.val)
      else 0 := by
  rw [jordanBlock_pow_expansion]
  rw [Finset.sum_apply, Finset.sum_apply]
  simp_rw [jordanBlock_pow_expansion_term_apply]
  by_cases hij : i.val ≤ j.val
  · let d := j.val - i.val
    have hd_eq : i.val + d = j.val := by omega
    by_cases hdk : d ≤ k
    · let m0 := k - d
      have hm0_mem : m0 ∈ Finset.range (k + 1) := by
        simp [m0]
      have hsingle :
          (∑ x ∈ Finset.range (k + 1),
              (if i.val + (k - x) = j.val then a ^ x * (Nat.choose k x : R) else 0)) =
            (if i.val + (k - m0) = j.val then a ^ m0 * (Nat.choose k m0 : R) else 0) := by
        refine Finset.sum_eq_single_of_mem m0 hm0_mem ?_
        intro m hm hne
        have hcond : ¬ i.val + (k - m) = j.val := by
          intro hc
          have hmk : m ≤ k := Nat.lt_succ_iff.mp (by simpa using hm)
          apply hne
          dsimp [m0, d]
          omega
        simp [hcond]
      rw [hsingle]
      have hcond0 : i.val + (k - m0) = j.val := by
        dsimp [m0, d]
        omega
      simp [hij, hcond0]
      have hchoose : Nat.choose k m0 = Nat.choose k d := by
        dsimp [m0]
        exact Nat.choose_symm hdk
      have hexp : m0 = k + i.val - j.val := by
        dsimp [m0, d]
        omega
      rw [hchoose, hexp]
      ring
    · have hzero_sum :
          (∑ x ∈ Finset.range (k + 1),
              (if i.val + (k - x) = j.val then a ^ x * (Nat.choose k x : R) else 0)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro m hm
        have hcond : ¬ i.val + (k - m) = j.val := by
          intro hc
          have hmk : m ≤ k := by
            simpa using (Nat.lt_succ_iff.mp (by simpa using hm))
          apply hdk
          dsimp [d]
          omega
        simp [hcond]
      rw [hzero_sum]
      have hchoose0 : Nat.choose k d = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hdk)
      simp [hij, d, hchoose0]
  · have hzero_sum :
        (∑ x ∈ Finset.range (k + 1),
            (if i.val + (k - x) = j.val then a ^ x * (Nat.choose k x : R) else 0)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro m hm
      have hcond : ¬ i.val + (k - m) = j.val := by
        intro hc
        apply hij
        omega
      simp [hcond]
    rw [hzero_sum]
    simp [hij]

/-- The superdiagonal shift is nilpotent once the exponent reaches the dimension. -/
theorem jordanShift_pow_eq_zero_of_card_le {R : Type*} [Semiring R] {n : Nat}
    {k : Nat} (hk : n ≤ k) :
    (jordanShift (R := R) n) ^ k = 0 := by
  ext i j
  rw [jordanShift_pow_apply]
  have hne : ¬ i.val + k = j.val := by
    intro h
    have hj_lt : j.val < n := j.isLt
    omega
  simp [hne]

/-- The dimension-th power of the superdiagonal shift is zero. -/
theorem jordanShift_pow_eq_zero_self {R : Type*} [Semiring R] (n : Nat) :
    (jordanShift (R := R) n) ^ n = 0 :=
  jordanShift_pow_eq_zero_of_card_le (R := R) (n := n) (k := n) (le_rfl)

/-- Entrywise upper-triangular predicate for ordered finite index types. -/
def UpperTriangular {R ι : Type*} [Zero R] [LT ι] (A : Matrix ι ι R) : Prop :=
  ∀ ⦃i j : ι⦄, j < i → A i j = 0

/-- A Jordan block is upper triangular. -/
theorem jordanBlock_upperTriangular {R : Type*} [Zero R] [One R] {n : Nat} (a : R) :
    UpperTriangular (jordanBlock n a) := by
  intro i j hji
  have hne : i ≠ j := by
    intro h
    subst h
    exact (lt_self_iff_false i).mp hji
  have hnot : ¬ i.val + 1 = j.val := by
    intro h
    omega
  simp [jordanBlock, hne, hnot]

/-- A Jordan block is block-triangular in mathlib's upper-triangular sense. -/
theorem jordanBlock_blockTriangular {R : Type*} [Zero R] [One R] {n : Nat} (a : R) :
    Matrix.BlockTriangular (jordanBlock n a) id := by
  intro i j hji
  exact jordanBlock_upperTriangular (R := R) a hji

/-- Powers of a Jordan block remain upper triangular. -/
theorem jordanBlock_pow_blockTriangular {R : Type*} [Semiring R] {n : Nat} (a : R)
    (k : Nat) :
    Matrix.BlockTriangular ((jordanBlock n a) ^ k) id := by
  induction k with
  | zero =>
      simpa using Matrix.blockTriangular_one (R := R) (m := Fin n) (b := id)
  | succ k ih =>
      rw [pow_succ]
      exact ih.mul (jordanBlock_blockTriangular (R := R) a)

/-- Powers of a Jordan block remain upper triangular, in the local AFP-style predicate. -/
theorem jordanBlock_pow_upperTriangular {R : Type*} [Semiring R] {n : Nat} (a : R)
    (k : Nat) :
    UpperTriangular ((jordanBlock n a) ^ k) := by
  intro i j hji
  exact jordanBlock_pow_blockTriangular (R := R) a k hji

/-- Diagonal entries of powers of a Jordan block. -/
theorem jordanBlock_pow_diag {R : Type*} [Semiring R] {n : Nat} (a : R)
    (k : Nat) (i : Fin n) :
    ((jordanBlock n a) ^ k) i i = a ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      have hsum :
          (∑ x : Fin n, ((jordanBlock n a) ^ k) i x * jordanBlock n a x i) =
            ((jordanBlock n a) ^ k) i i * jordanBlock n a i i := by
        refine Finset.sum_eq_single i ?_ ?_
        · intro x _ hx
          rcases lt_or_gt_of_ne hx with hxi | hix
          · have hleft : ((jordanBlock n a) ^ k) i x = 0 :=
              jordanBlock_pow_upperTriangular (R := R) a k hxi
            simp [hleft]
          · have hright : jordanBlock n a x i = 0 :=
              jordanBlock_upperTriangular (R := R) a hix
            have hnot : ¬ x.val + 1 = i.val := by omega
            simp [jordanBlock, hx, hnot]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      rw [hsum, ih]
      simp [pow_succ]

/-- The diagonal of a Jordan block is constantly its eigenvalue. -/
theorem jordanBlock_diag (R : Type*) [Zero R] [One R] {n : Nat} (a : R) :
    (fun i : Fin n => jordanBlock n a i i) = fun _ => a := by
  funext i
  simp

/-- Characteristic polynomial of a Jordan block. -/
theorem jordanBlock_charpoly {R : Type*} [CommRing R] {n : Nat} (a : R) :
    (jordanBlock n a).charpoly = (X - C a) ^ n := by
  classical
  calc
    (jordanBlock n a).charpoly =
        ∏ i : Fin n, (X - C (jordanBlock n a i i)) :=
      Matrix.charpoly_of_upperTriangular (jordanBlock n a) (by
        intro i j hji
        exact jordanBlock_upperTriangular (R := R) a hji)
    _ = ∏ _i : Fin n, (X - C a) := by simp
    _ = (X - C a) ^ n := by simp

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.JordanBlock
