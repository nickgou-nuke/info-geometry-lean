import Mathlib

/-
#### BUCKET 1: CLOSED FINITE THEOREMS (14)
- O·P_hyp = P_hyp, P_hyp·O = P_hyp  (+1)
- O·P_ell = -P_ell, P_ell·O = -P_ell  (-1)
- O·P_par = 0, P_par·O = 0  (harmonic)
- P_hyp² = P_hyp, P_ell² = P_ell, P_par² = P_par  (idempotent)
- P_hyp·P_ell = 0, P_hyp·P_par = 0, P_ell·P_par = 0  (orthogonal)
- P_hyp - P_ell = O (spectral)
- P_hyp + P_ell + P_par = 1 (sum)
#### BUCKET 2: Conditional on hO: O³ = O, h2: (2:A) ≠ 0
#### BUCKET 3: None
-/

import Mathlib

namespace TriFacetComplete

variable {A : Type*} [Field A]

def P_hyp (O : A) : A := (1 / 2 : A) * (O ^ 2 + O)
def P_ell (O : A) : A := (1 / 2 : A) * (O ^ 2 - O)
def P_par (O : A) : A := 1 - O ^ 2

theorem T_pow4 (O : A) (hO : O ^ 3 = O) : O ^ 4 = O ^ 2 := by
  calc
    O ^ 4 = O * O ^ 3 := by ring
    _ = O * O := by rw [hO]
    _ = O ^ 2 := by ring

theorem O_mul_P_hyp {O : A} (hO : O ^ 3 = O) : O * P_hyp O = P_hyp O := by
  unfold P_hyp
  calc
    O * ((1 / 2 : A) * (O ^ 2 + O)) = (1 / 2 : A) * (O * (O ^ 2 + O)) := by ring
    _ = (1 / 2 : A) * (O ^ 3 + O ^ 2) := by ring
    _ = (1 / 2 : A) * (O + O ^ 2) := by rw [hO]
    _ = (1 / 2 : A) * (O ^ 2 + O) := by ring

theorem P_hyp_mul_O {O : A} (hO : O ^ 3 = O) : P_hyp O * O = P_hyp O := by
  unfold P_hyp
  calc
    ((1 / 2 : A) * (O ^ 2 + O)) * O = (1 / 2 : A) * ((O ^ 2 + O) * O) := by ring
    _ = (1 / 2 : A) * (O ^ 3 + O ^ 2) := by ring
    _ = (1 / 2 : A) * (O + O ^ 2) := by rw [hO]
    _ = (1 / 2 : A) * (O ^ 2 + O) := by ring

theorem O_mul_P_ell {O : A} (hO : O ^ 3 = O) : O * P_ell O = - P_ell O := by
  unfold P_ell
  calc
    O * ((1 / 2 : A) * (O ^ 2 - O)) = (1 / 2 : A) * (O * (O ^ 2 - O)) := by ring
    _ = (1 / 2 : A) * (O ^ 3 - O ^ 2) := by ring
    _ = (1 / 2 : A) * (O - O ^ 2) := by rw [hO]
    _ = -((1 / 2 : A) * (O ^ 2 - O)) := by ring

theorem P_ell_mul_O {O : A} (hO : O ^ 3 = O) : P_ell O * O = - P_ell O := by
  unfold P_ell
  calc
    ((1 / 2 : A) * (O ^ 2 - O)) * O = (1 / 2 : A) * ((O ^ 2 - O) * O) := by ring
    _ = (1 / 2 : A) * (O ^ 3 - O ^ 2) := by ring
    _ = (1 / 2 : A) * (O - O ^ 2) := by rw [hO]
    _ = -((1 / 2 : A) * (O ^ 2 - O)) := by ring

theorem O_mul_P_par {O : A} (hO : O ^ 3 = O) : O * P_par O = 0 := by
  unfold P_par
  calc
    O * (1 - O ^ 2) = O - O ^ 3 := by ring
    _ = O - O := by rw [hO]
    _ = 0 := by ring

theorem P_par_mul_O {O : A} (hO : O ^ 3 = O) : P_par O * O = 0 := by
  unfold P_par
  calc
    (1 - O ^ 2) * O = O - O ^ 3 := by ring
    _ = O - O := by rw [hO]
    _ = 0 := by ring

theorem P_hyp_idem (h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) : P_hyp O * P_hyp O = P_hyp O := by
  calc
    ((1 / 2 : A) * (O ^ 2 + O)) * ((1 / 2 : A) * (O ^ 2 + O)) = ((1 / 2 : A) ^ 2) * (O ^ 4 + 2 * O ^ 3 + O ^ 2) := by ring
    _ = ((1 / 2 : A) ^ 2) * (O ^ 2 + 2 * O + O ^ 2) := by rw [T_pow4 O hO, hO]
    _ = (1 / 2 : A) * (O ^ 2 + O) := by field_simp [h2]; ring

theorem P_ell_idem (h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) : P_ell O * P_ell O = P_ell O := by
  calc
    ((1 / 2 : A) * (O ^ 2 - O)) * ((1 / 2 : A) * (O ^ 2 - O)) = ((1 / 2 : A) ^ 2) * (O ^ 4 - 2 * O ^ 3 + O ^ 2) := by ring
    _ = ((1 / 2 : A) ^ 2) * (O ^ 2 - 2 * O + O ^ 2) := by rw [T_pow4 O hO, hO]
    _ = (1 / 2 : A) * (O ^ 2 - O) := by field_simp [h2]; ring

theorem P_par_idem {O : A} (hO : O ^ 3 = O) : P_par O * P_par O = P_par O := by
  calc
    (1 - O ^ 2) * (1 - O ^ 2) = 1 - 2 * O ^ 2 + O ^ 4 := by ring
    _ = 1 - 2 * O ^ 2 + O ^ 2 := by rw [T_pow4 O hO]
    _ = 1 - O ^ 2 := by ring

theorem P_hyp_mul_P_ell (h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) : P_hyp O * P_ell O = 0 := by
  calc
    ((1 / 2 : A) * (O ^ 2 + O)) * ((1 / 2 : A) * (O ^ 2 - O)) = ((1 / 2 : A) ^ 2) * (O ^ 4 - O ^ 2) := by ring
    _ = ((1 / 2 : A) ^ 2) * (O ^ 2 - O ^ 2) := by rw [T_pow4 O hO]
    _ = 0 := by ring

theorem P_hyp_mul_P_par (h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) : P_hyp O * P_par O = 0 := by
  calc
    ((1 / 2 : A) * (O ^ 2 + O)) * (1 - O ^ 2) = (1 / 2 : A) * (O ^ 2 + O - O ^ 4 - O ^ 3) := by ring
    _ = (1 / 2 : A) * (O ^ 2 + O - O ^ 2 - O) := by rw [T_pow4 O hO, hO]
    _ = 0 := by ring

theorem P_ell_mul_P_par (h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) : P_ell O * P_par O = 0 := by
  calc
    ((1 / 2 : A) * (O ^ 2 - O)) * (1 - O ^ 2) = (1 / 2 : A) * (O ^ 2 - O - O ^ 4 + O ^ 3) := by ring
    _ = (1 / 2 : A) * (O ^ 2 - O - O ^ 2 + O) := by rw [T_pow4 O hO, hO]
    _ = 0 := by ring

theorem P_hyp_sub_P_ell (h2 : (2 : A) ≠ 0) (O : A) : P_hyp O - P_ell O = O := by
  unfold P_hyp P_ell; field_simp [h2]; ring

theorem sum_to_id (h2 : (2 : A) ≠ 0) (O : A) : P_hyp O + P_ell O + P_par O = 1 := by
  unfold P_hyp P_ell P_par; field_simp [h2]; ring

end TriFacetComplete
