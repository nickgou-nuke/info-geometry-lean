import Mathlib.Tactic

namespace Audit

/-!
BUCKET 1: CLOSED FINITE THEOREMS
- O2_P_hyp
- O2_P_ell
- tri_facet_pow_odd
- tri_facet_pow_even

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- All inductive spectral power theorems are conditional on the explicit property hO : O ^ 3 = O
  and the field characteristic property h2 : (2 : A) ≠ 0.

BUCKET 3: OPEN CLOSURE DEBT
- None.
-/

variable {A : Type*} [Field A]

def P_hyp (O : A) : A := (1 / 2 : A) * (O ^ 2 + O)

def P_ell (O : A) : A := (1 / 2 : A) * (O ^ 2 - O)

def P_par (O : A) : A := 1 - O ^ 2

theorem tri_facet_eigenspace_hyp (_h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) :
    O * P_hyp O = P_hyp O := by
  unfold P_hyp
  have h_calc : O * ((1 / 2 : A) * (O ^ 2 + O)) = (1 / 2 : A) * (O ^ 3 + O ^ 2) := by ring
  rw [h_calc, hO]
  ring

theorem tri_facet_eigenspace_ell (_h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) :
    O * P_ell O = - P_ell O := by
  unfold P_ell
  have h_calc : O * ((1 / 2 : A) * (O ^ 2 - O)) = (1 / 2 : A) * (O ^ 3 - O ^ 2) := by ring
  rw [h_calc, hO]
  ring

theorem tri_facet_spectral_reconstruction (_h2 : (2 : A) ≠ 0) (O : A) :
    P_hyp O - P_ell O = O := by
  unfold P_hyp P_ell
  field_simp [_h2]
  ring

lemma O2_P_hyp (_h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) :
    O ^ 2 * P_hyp O = P_hyp O := by
  have h1 : O ^ 2 * P_hyp O = O * (O * P_hyp O) := by ring
  rw [h1]
  rw [tri_facet_eigenspace_hyp _h2 hO]
  exact tri_facet_eigenspace_hyp _h2 hO

lemma O2_P_ell (_h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) :
    O ^ 2 * P_ell O = P_ell O := by
  have h1 : O ^ 2 * P_ell O = O * (O * P_ell O) := by ring
  rw [h1]
  rw [tri_facet_eigenspace_ell _h2 hO]
  have h2_neg : O * (- P_ell O) = - (O * P_ell O) := by ring
  rw [h2_neg]
  rw [tri_facet_eigenspace_ell _h2 hO]
  ring

theorem tri_facet_pow_odd (h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) (k : ℕ) :
    O ^ (2 * k + 1) = P_hyp O - P_ell O := by
  induction k with
  | zero =>
    have h_pow1 : O ^ (2 * 0 + 1) = O := by ring
    rw [h_pow1]
    exact (tri_facet_spectral_reconstruction h2 O).symm
  | succ k ih =>
    have h_step : O ^ (2 * (k + 1) + 1) = O ^ (2 * k + 1) * O ^ 2 := by ring
    rw [h_step, ih]
    have h_expand : (P_hyp O - P_ell O) * O ^ 2 = (O ^ 2 * P_hyp O) - (O ^ 2 * P_ell O) := by ring
    rw [h_expand]
    rw [O2_P_hyp h2 hO, O2_P_ell h2 hO]

theorem tri_facet_pow_even (h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) (k : ℕ) :
    O ^ (2 * k + 2) = P_hyp O + P_ell O := by
  induction k with
  | zero =>
    have h_pow2 : O ^ (2 * 0 + 2) = O ^ 2 := by ring
    rw [h_pow2]
    unfold P_hyp P_ell
    field_simp [h2]
    ring
  | succ k ih =>
    have h_step : O ^ (2 * (k + 1) + 2) = O ^ (2 * k + 2) * O ^ 2 := by ring
    rw [h_step, ih]
    have h_expand : (P_hyp O + P_ell O) * O ^ 2 = (O ^ 2 * P_hyp O) + (O ^ 2 * P_ell O) := by ring
    rw [h_expand]
    rw [O2_P_hyp h2 hO, O2_P_ell h2 hO]

section MultiFacetGeneralization

variable {R : Type*} [Ring R] (O : R) (m : ℕ) (h_deg : O^m = O)

theorem O_pow_reduction (h_deg : O^m = O) (k : ℕ) : O^(m + k) = O^(k + 1) := by
  induction k with
  | zero =>
    have h0 : m + 0 = m := by rfl
    have h1 : 0 + 1 = 1 := by rfl
    rw [h0, h1, h_deg]
    rw [pow_one]
  | succ k ih =>
    have h_step1 : m + (k + 1) = (m + k) + 1 := by ring
    rw [h_step1]
    rw [pow_succ]
    rw [ih]
    rw [← pow_succ]

end MultiFacetGeneralization

end Audit
