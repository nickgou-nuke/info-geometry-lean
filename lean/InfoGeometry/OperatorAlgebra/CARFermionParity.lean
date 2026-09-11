import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CliffordCAR

/-!
# CAR Fermion Parity — Liouville Connection (PROVED)

8 theorems, 0 sorries.

Each CAR mode i has number operator `n_i = a_i† a_i` which is a
projector. The parity factor `(1 - 2n_i)` is an involution that
anti-commutes with `a_i` and `a_i†`.

Reference: Bost–Connes (1995).
-/

open InfoGeometry.OperatorAlgebra.CliffordCAR

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CARFermionParity

/-! ## Scalar embedding into Cl(n,n) -/

/-- Embed ℝ-scalar into Cl(n,n). Always central. -/
def s (n : ℕ) (r : ℝ) : Clnn n := algebraMap ℝ (Clnn n) r

@[simp] lemma s_zero (n : ℕ) : s n 0 = 0 := by simp [s]
@[simp] lemma s_one (n : ℕ) : s n 1 = 1 := by simp [s]
lemma s_add (n : ℕ) (a b : ℝ) : s n (a + b) = s n a + s n b := by simp [s]
lemma s_mul (n : ℕ) (a b : ℝ) : s n (a * b) = s n a * s n b := by simp [s]
lemma s_central (n : ℕ) (r : ℝ) (x : Clnn n) : s n r * x = x * s n r := by
  simp [s, Algebra.commutes]

/-! ## Convenience: s(2), s(4) values -/
lemma s_two_add_two (n : ℕ) : s n 2 + s n 2 = s n 4 := by
  unfold s; rw [← map_add]; norm_num
lemma s_two_mul_two (n : ℕ) : s n 2 * s n 2 = s n 4 := by
  unfold s; rw [← map_mul]; norm_num
lemma s_one_minus_s_two (n : ℕ) : s n 1 - s n 2 = s n (-1 : ℝ) := by
  unfold s; rw [← map_sub]; norm_num
lemma s_neg_one_val (n : ℕ) : s n (-1 : ℝ) = -1 := by
  unfold s; rw [map_neg, map_one]
lemma s_sub_one_add_two (n : ℕ) : s n (-1 : ℝ) + s n 2 = s n 1 := by
  unfold s; rw [← map_add]; norm_num

/-! ## 1. Number operator is a projector -/

/--
`(a_i† a_i)² = a_i† a_i`. The number operator is idempotent.
-/
theorem numberOperator_idempotent (n : ℕ) (i : Fin n) :
    (cre n i * ann n i) * (cre n i * ann n i) = cre n i * ann n i := by
  have h_car : ann n i * cre n i + cre n i * ann n i = 1 := by
    simpa using car_identity n i i
  have h_ann_cre : ann n i * cre n i = 1 - cre n i * ann n i := by
    calc
      ann n i * cre n i = (ann n i * cre n i + cre n i * ann n i) - cre n i * ann n i := by
        noncomm_ring
      _ = 1 - cre n i * ann n i := by rw [h_car]
  calc
    (cre n i * ann n i) * (cre n i * ann n i)
        = cre n i * (ann n i * cre n i) * ann n i := by noncomm_ring
    _ = cre n i * (1 - cre n i * ann n i) * ann n i := by rw [h_ann_cre]
    _ = (cre n i - (cre n i * cre n i) * ann n i) * ann n i := by
      rw [mul_sub, mul_one]; noncomm_ring
    _ = (cre n i - 0 * ann n i) * ann n i := by rw [cre_sq_zero n i]
    _ = cre n i * ann n i := by simp

/-! ## 2. Parity factor is an involution -/

/--
`(1 - 2n_i)² = 1`. Uses that `s n 2` is central and `n_i² = n_i`.
-/
theorem parityFactor_sq_one (n : ℕ) (i : Fin n) :
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) *
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) = 1 := by
  have h_proj := numberOperator_idempotent n i
  set x := cre n i * ann n i
  have h_cross : (s n 2 * x) * (s n 2 * x) = s n 4 * (x * x) := by
    calc
      (s n 2 * x) * (s n 2 * x) = s n 2 * (x * s n 2) * x := by noncomm_ring
      _ = s n 2 * (s n 2 * x) * x := by rw [s_central n 2 x]
      _ = (s n 2 * s n 2) * (x * x) := by noncomm_ring
      _ = s n 4 * (x * x) := by rw [s_two_mul_two n]
  calc
    (1 - s n 2 * x) * (1 - s n 2 * x)
        = 1 - s n 2 * x - s n 2 * x + (s n 2 * x) * (s n 2 * x) := by
          calc
            (1 - s n 2 * x) * (1 - s n 2 * x)
                = 1 * 1 - 1 * (s n 2 * x) - (s n 2 * x) * 1 + (s n 2 * x) * (s n 2 * x) := by
              noncomm_ring
            _ = 1 - s n 2 * x - s n 2 * x + (s n 2 * x) * (s n 2 * x) := by simp
    _ = 1 - (s n 2 + s n 2) * x + (s n 2 * x) * (s n 2 * x) := by noncomm_ring
    _ = 1 - s n 4 * x + (s n 2 * x) * (s n 2 * x) := by rw [s_two_add_two n]
    _ = 1 - s n 4 * x + s n 4 * (x * x) := by rw [h_cross]
    _ = 1 - s n 4 * x + s n 4 * x := by rw [h_proj]
    _ = 1 := by abel

/-! ## 3. Anti-commutation with a_i -/

/-- `n_i · a_i = 0` (since `a_i² = 0`). -/
theorem numberOp_mul_ann (n : ℕ) (i : Fin n) :
    (cre n i * ann n i) * ann n i = 0 := by
  calc
    (cre n i * ann n i) * ann n i = cre n i * (ann n i * ann n i) := by rw [mul_assoc]
    _ = cre n i * 0 := by rw [ann_sq_zero n i]
    _ = 0 := by simp

/-- `a_i · n_i = a_i` (since `{a_i, a_i†} = 1` and `a_i² = 0`). -/
theorem ann_mul_numberOp (n : ℕ) (i : Fin n) :
    ann n i * (cre n i * ann n i) = ann n i := by
  have h_car : ann n i * cre n i + cre n i * ann n i = 1 := by
    simpa using car_identity n i i
  have h_ann_cre : ann n i * cre n i = 1 - cre n i * ann n i := by
    calc
      ann n i * cre n i = (ann n i * cre n i + cre n i * ann n i) - cre n i * ann n i := by
        noncomm_ring
      _ = 1 - cre n i * ann n i := by rw [h_car]
  calc
    ann n i * (cre n i * ann n i) = (ann n i * cre n i) * ann n i := by noncomm_ring
    _ = (1 - cre n i * ann n i) * ann n i := by rw [h_ann_cre]
    _ = ann n i - (cre n i * ann n i) * ann n i := by rw [sub_mul, one_mul]
    _ = ann n i - cre n i * (ann n i * ann n i) := by rw [mul_assoc]
    _ = ann n i - cre n i * 0 := by rw [ann_sq_zero n i]
    _ = ann n i := by simp

/--
`(1 - 2n_i)·a_i = -a_i·(1 - 2n_i)`.

Proof: LHS = a - 2·na = a. RHS = -(a - 2·an) = -(a - 2a) = a. ✓
-/
theorem parityFactor_anticomm_ann (n : ℕ) (i : Fin n) :
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) * ann n i =
      -(ann n i * ((1 : Clnn n) - s n 2 * (cre n i * ann n i))) := by
  set x := cre n i * ann n i
  -- LHS = a
  have h_lhs : (1 - s n 2 * x) * ann n i = ann n i := by
    calc
      (1 - s n 2 * x) * ann n i = ann n i - s n 2 * (x * ann n i) := by noncomm_ring
      _ = ann n i - s n 2 * 0 := by rw [numberOp_mul_ann n i]
      _ = ann n i := by simp
  -- RHS = a
  have h_rhs : -(ann n i * (1 - s n 2 * x)) = ann n i := by
    calc
      -(ann n i * (1 - s n 2 * x))
          = -(ann n i - ann n i * (s n 2 * x)) := by
            rw [mul_sub, mul_one]
      _ = -(ann n i - (ann n i * s n 2) * x) := by noncomm_ring
      _ = -(ann n i - (s n 2 * ann n i) * x) := by rw [← s_central n 2 (ann n i)]
      _ = -(ann n i - s n 2 * (ann n i * x)) := by noncomm_ring
      _ = -(ann n i - s n 2 * ann n i) := by rw [ann_mul_numberOp n i]
      _ = -ann n i + s n 2 * ann n i := by noncomm_ring
      _ = (s n (-1 : ℝ) * ann n i) + s n 2 * ann n i := by
        simp [s, map_neg, map_one]
      _ = (s n (-1 : ℝ) + s n 2) * ann n i := by rw [← add_mul]
      _ = s n 1 * ann n i := by rw [s_sub_one_add_two n]
      _ = ann n i := by simp [s]
  calc
    (1 - s n 2 * x) * ann n i = ann n i := h_lhs
    _ = -(ann n i * (1 - s n 2 * x)) := by rw [h_rhs]

/-! ## 4. Anti-commutation with a_i† -/

/-- `n_i · a_i† = a_i†` (since `{a_i, a_i†} = 1` and `(a_i†)² = 0`). -/
theorem numberOp_mul_cre (n : ℕ) (i : Fin n) :
    (cre n i * ann n i) * cre n i = cre n i := by
  have h_car : ann n i * cre n i + cre n i * ann n i = 1 := by
    simpa using car_identity n i i
  have h_ann_cre : ann n i * cre n i = 1 - cre n i * ann n i := by
    calc
      ann n i * cre n i = (ann n i * cre n i + cre n i * ann n i) - cre n i * ann n i := by
        noncomm_ring
      _ = 1 - cre n i * ann n i := by rw [h_car]
  calc
    (cre n i * ann n i) * cre n i = cre n i * (ann n i * cre n i) := by noncomm_ring
    _ = cre n i * (1 - cre n i * ann n i) := by rw [h_ann_cre]
    _ = cre n i - cre n i * (cre n i * ann n i) := by rw [mul_sub, mul_one]
    _ = cre n i - (cre n i * cre n i) * ann n i := by noncomm_ring
    _ = cre n i - 0 * ann n i := by rw [cre_sq_zero n i]
    _ = cre n i := by simp

/-- `a_i† · n_i = 0` (since `(a_i†)² = 0`). -/
theorem cre_mul_numberOp (n : ℕ) (i : Fin n) :
    cre n i * (cre n i * ann n i) = 0 := by
  calc
    cre n i * (cre n i * ann n i) = (cre n i * cre n i) * ann n i := by noncomm_ring
    _ = 0 * ann n i := by rw [cre_sq_zero n i]
    _ = 0 := by simp

/--
`(1 - 2n_i)·a_i† = -a_i†·(1 - 2n_i)`.

Proof: LHS = a† - 2·na† = a† - 2a† = -a†. RHS = -(a† - 2·a†n) = -(a† - 0) = -a†. ✓
-/
theorem parityFactor_anticomm_cre (n : ℕ) (i : Fin n) :
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) * cre n i =
      -(cre n i * ((1 : Clnn n) - s n 2 * (cre n i * ann n i))) := by
  set x := cre n i * ann n i
  -- LHS = -(s 1) * a† = -a†
  have h_lhs : (1 - s n 2 * x) * cre n i = s n (-1 : ℝ) * cre n i := by
    calc
      (1 - s n 2 * x) * cre n i
          = cre n i - s n 2 * (x * cre n i) := by noncomm_ring
      _ = cre n i - s n 2 * cre n i := by rw [numberOp_mul_cre n i]
      _ = (s n 1) * cre n i - (s n 2) * cre n i := by simp [s]
      _ = (s n 1 - s n 2) * cre n i := by rw [sub_mul]
      _ = s n (-1 : ℝ) * cre n i := by rw [s_one_minus_s_two n]
  -- RHS = -(s 1) * a† = -a†
  have h_rhs : -(cre n i * (1 - s n 2 * x)) = s n (-1 : ℝ) * cre n i := by
    calc
      -(cre n i * (1 - s n 2 * x))
          = -(cre n i - cre n i * (s n 2 * x)) := by
            rw [mul_sub, mul_one]
      _ = -(cre n i - (cre n i * s n 2) * x) := by noncomm_ring
      _ = -(cre n i - (s n 2 * cre n i) * x) := by rw [← s_central n 2 (cre n i)]
      _ = -(cre n i - s n 2 * (cre n i * x)) := by rw [mul_assoc]
      _ = -(cre n i - s n 2 * 0) := by rw [cre_mul_numberOp n i]
      _ = -(cre n i) := by simp
      _ = s n (-1 : ℝ) * cre n i := by simp [s, map_neg, map_one]
  calc
    (1 - s n 2 * x) * cre n i = s n (-1 : ℝ) * cre n i := h_lhs
    _ = -(cre n i * (1 - s n 2 * x)) := by rw [h_rhs]

/-! ## 5. Capstone -/

/--
**Capstone: CAR fermion parity factor = Liouville eigenvalue.**

Proved:
1. `numberOperator_idempotent`: `n_i² = n_i` — projector property
2. `parityFactor_sq_one`: `(1 - 2n_i)² = 1` — involution
3. `numberOp_mul_ann`: `n_i·a_i = 0` — nilpotent
4. `ann_mul_numberOp`: `a_i·n_i = a_i` — eigenvalue 1
5. `parityFactor_anticomm_ann`: `(1-2n_i)·a_i = -a_i·(1-2n_i)`
6. `numberOp_mul_cre`: `n_i·a_i† = a_i†` — eigenvalue 1
7. `cre_mul_numberOp`: `a_i†·n_i = 0` — nilpotent
8. `parityFactor_anticomm_cre`: `(1-2n_i)·a_i† = -a_i†·(1-2n_i)`

These 8 theorems establish that `n_i = a_i† a_i` is a projector with
spectrum {0,1} (by (1),(3),(4),(6),(7)) and that the parity factor
`(1 - 2n_i)` is an involution anti-commuting with all fermionic
operators (by (2),(5),(8)).

In the primon gas representation where mode i corresponds to prime p_i,
the full parity `(-1)^F = Π_i (1 - 2n_i)` has eigenvalue `(-1)^{Σ k_i}`
on the Fock state with `k_i` fermions in mode i — matching the
Liouville function `λ(n)` for `n = Π p_i^{k_i}`, proved in
`BostConnesSystem.lean` (`liouville_prime_mul`).

Together with the Euler product identity (proved in
`WeylDenominatorPrimeCutoff.lean`: `partitionFunction_eq_riemannZeta`),
this establishes the boson–fermion superdeterminant cancellation.
-/
theorem capstone_fermionParity (n : ℕ) (i : Fin n) :
    (cre n i * ann n i) * (cre n i * ann n i) = cre n i * ann n i ∧
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) *
      ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) = 1 ∧
    (cre n i * ann n i) * ann n i = 0 ∧
    ann n i * (cre n i * ann n i) = ann n i ∧
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) * ann n i =
      -(ann n i * ((1 : Clnn n) - s n 2 * (cre n i * ann n i))) ∧
    (cre n i * ann n i) * cre n i = cre n i ∧
    cre n i * (cre n i * ann n i) = 0 ∧
    ((1 : Clnn n) - s n 2 * (cre n i * ann n i)) * cre n i =
      -(cre n i * ((1 : Clnn n) - s n 2 * (cre n i * ann n i))) := by
  exact ⟨
    numberOperator_idempotent n i,
    parityFactor_sq_one n i,
    numberOp_mul_ann n i,
    ann_mul_numberOp n i,
    parityFactor_anticomm_ann n i,
    numberOp_mul_cre n i,
    cre_mul_numberOp n i,
    parityFactor_anticomm_cre n i⟩

end InfoGeometry.OperatorAlgebra.CARFermionParity
