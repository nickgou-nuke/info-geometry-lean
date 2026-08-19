import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

open CliffordAlgebra
open QuadraticMap

noncomputable section

namespace Cl11Fermions

def q11 : QuadraticForm ℚ (Fin 2 → ℚ) := proj 0 0 - proj 1 1
def e₀ : CliffordAlgebra q11 := ι q11 (fun i => if i = 0 then 1 else 0)
def e₁ : CliffordAlgebra q11 := ι q11 (fun i => if i = 1 then 1 else 0)

theorem e₀_sq : e₀ * e₀ = 1 := by
  calc
    e₀ * e₀ = algebraMap ℚ (CliffordAlgebra q11) (q11 (fun i => if i = 0 then 1 else 0)) := ι_sq_scalar _ _
    _ = 1 := by norm_num [q11, proj_apply]

theorem e₁_sq : e₁ * e₁ = -1 := by
  calc
    e₁ * e₁ = algebraMap ℚ (CliffordAlgebra q11) (q11 (fun i => if i = 1 then 1 else 0)) := ι_sq_scalar _ _
    _ = -1 := by norm_num [q11, proj_apply]

theorem orth : q11.IsOrtho (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0) := by
  norm_num [q11, IsOrtho, proj_apply]

theorem anticomm : e₀ * e₁ + e₁ * e₀ = 0 := by
  have h := ι_mul_ι_add_swap_of_isOrtho orth
  simpa [e₀, e₁] using h

/-- Scalar 1/2. -/
def a : CliffordAlgebra q11 := algebraMap ℚ (CliffordAlgebra q11) (1/2 : ℚ)

lemma a_comm (x : CliffordAlgebra q11) : a * x = x * a := by
  calc
    a * x = (algebraMap ℚ (CliffordAlgebra q11) (1/2 : ℚ)) * x := rfl
    _ = x * (algebraMap ℚ (CliffordAlgebra q11) (1/2 : ℚ)) := Algebra.commutes (1/2 : ℚ) x
    _ = x * a := rfl

lemma a_mul_mul (x y : CliffordAlgebra q11) : (a*x)*(a*y) = (a*a)*(x*y) := by
  calc
    (a*x)*(a*y) = (a*x)*a*y := by simp [mul_assoc]
    _ = a*(x*a)*y := by simp [mul_assoc]
    _ = a*(a*x)*y := by rw [a_comm x]
    _ = (a*a)*(x*y) := by simp [mul_assoc]

def b : CliffordAlgebra q11 := a * (e₀ + e₁)
def bdag : CliffordAlgebra q11 := a * (e₀ - e₁)

theorem b_sq : b * b = 0 := by
  have h_expand : (e₀+e₁)*(e₀+e₁) = e₀*e₁ + e₁*e₀ := by
    calc
      (e₀+e₁)*(e₀+e₁) = e₀*e₀ + e₀*e₁ + e₁*e₀ + e₁*e₁ := by noncomm_ring
      _ = 1 + e₀*e₁ + e₁*e₀ + (-1) := by simp [e₀_sq, e₁_sq]
      _ = e₀*e₁ + e₁*e₀ := by abel
  calc
    b * b = (a*a)*((e₀+e₁)*(e₀+e₁)) := by simp [b, a_mul_mul]
    _ = (a*a)*(e₀*e₁ + e₁*e₀) := by rw [h_expand]
    _ = (a*a)*0 := by rw [anticomm]
    _ = 0 := by simp

theorem bdag_sq : bdag * bdag = 0 := by
  have h_expand : (e₀-e₁)*(e₀-e₁) = -(e₀*e₁ + e₁*e₀) := by
    calc
      (e₀-e₁)*(e₀-e₁) = e₀*e₀ - e₀*e₁ - e₁*e₀ + e₁*e₁ := by noncomm_ring
      _ = 1 - e₀*e₁ - e₁*e₀ + (-1) := by simp [e₀_sq, e₁_sq]
      _ = -(e₀*e₁ + e₁*e₀) := by abel
  calc
    bdag * bdag = (a*a)*((e₀-e₁)*(e₀-e₁)) := by simp [bdag, a_mul_mul]
    _ = (a*a)*(-(e₀*e₁ + e₁*e₀)) := by rw [h_expand]
    _ = (a*a)*0 := by simp [anticomm]
    _ = 0 := by simp

theorem anticomm_bbdag : b * bdag + bdag * b = 1 := by
  have h_cross : (e₀+e₁)*(e₀-e₁) + (e₀-e₁)*(e₀+e₁) = 4 := by
    have h_expr : (e₀+e₁)*(e₀-e₁) + (e₀-e₁)*(e₀+e₁) = 2*e₀*e₀ - 2*e₁*e₁ := by
      noncomm_ring
    calc
      (e₀+e₁)*(e₀-e₁) + (e₀-e₁)*(e₀+e₁) = 2*e₀*e₀ - 2*e₁*e₁ := h_expr
      _ = 2*1 - 2*(-1) := by
        calc
          2*e₀*e₀ - 2*e₁*e₁ = (2*e₀)*e₀ - (2*e₁)*e₁ := rfl
          _ = 2*(e₀*e₀) - 2*(e₁*e₁) := by simp [mul_assoc]
          _ = 2*1 - 2*(-1) := by rw [e₀_sq, e₁_sq]
      _ = 4 := by norm_num
  calc
    b * bdag + bdag * b = (a*a)*(((e₀+e₁)*(e₀-e₁) + (e₀-e₁)*(e₀+e₁))) := by
      dsimp [b, bdag]
      calc
        (a*(e₀+e₁))*(a*(e₀-e₁)) + (a*(e₀-e₁))*(a*(e₀+e₁)) = (a*a)*((e₀+e₁)*(e₀-e₁)) + (a*a)*((e₀-e₁)*(e₀+e₁)) := by
          rw [a_mul_mul (e₀+e₁) (e₀-e₁), a_mul_mul (e₀-e₁) (e₀+e₁)]
        _ = (a*a)*(((e₀+e₁)*(e₀-e₁) + (e₀-e₁)*(e₀+e₁))) := by rw [← mul_add]
    _ = (a*a)*4 := by rw [h_cross]
    _ = 1 := by
      have hcalc : (a*a)*4 = 1 := by
        have h4 : (4 : CliffordAlgebra q11) = algebraMap ℚ (CliffordAlgebra q11) (4 : ℚ) := by
          simpa using (map_natCast (algebraMap ℚ (CliffordAlgebra q11)) 4).symm
        calc
          (a*a)*4 = (a*a)*(algebraMap ℚ (CliffordAlgebra q11) (4 : ℚ)) := by rw [h4]
          _ = algebraMap ℚ (CliffordAlgebra q11) ((1/2 : ℚ) * (1/2 : ℚ) * (4 : ℚ)) := by simp [a, map_mul]
          _ = algebraMap ℚ (CliffordAlgebra q11) (1 : ℚ) := by
            have : (1/2 : ℚ) * (1/2 : ℚ) * (4 : ℚ) = (1 : ℚ) := by ring
            rw [this]
          _ = 1 := by simp
      exact hcalc

/-! ## Cartan bivector and complementary CAR projectors -/

def K : CliffordAlgebra q11 := e₀ * e₁

theorem K_sq : K * K = 1 := by
  unfold K
  calc
    (e₀ * e₁) * (e₀ * e₁) = e₀ * (e₁ * e₀) * e₁ := by noncomm_ring
    _ = e₀ * (-(e₀ * e₁)) * e₁ := by
      rw [show e₁ * e₀ = -(e₀ * e₁) by
        exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using anticomm)]
    _ = -(e₀ * e₀) * (e₁ * e₁) := by noncomm_ring
    _ = 1 := by rw [e₀_sq, e₁_sq]; simp

def occupation : CliffordAlgebra q11 := bdag * b

def holeOccupation : CliffordAlgebra q11 := b * bdag

theorem occupation_add_holeOccupation : occupation + holeOccupation = 1 := by
  unfold occupation holeOccupation
  simpa [add_comm] using anticomm_bbdag

theorem occupation_mul_holeOccupation : occupation * holeOccupation = 0 := by
  unfold occupation holeOccupation
  calc
    (bdag * b) * (b * bdag) = bdag * (b * b) * bdag := by noncomm_ring
    _ = 0 := by rw [b_sq]; simp

theorem holeOccupation_mul_occupation : holeOccupation * occupation = 0 := by
  unfold occupation holeOccupation
  calc
    (b * bdag) * (bdag * b) = b * (bdag * bdag) * b := by noncomm_ring
    _ = 0 := by rw [bdag_sq]; simp

theorem occupation_sq : occupation * occupation = occupation := by
  calc
    occupation * occupation = bdag * (b * bdag) * b := by
      unfold occupation
      noncomm_ring
    _ = bdag * (1 - occupation) * b := by
      rw [show b * bdag = 1 - occupation by
        unfold occupation
        exact eq_sub_iff_add_eq.mpr anticomm_bbdag]
    _ = occupation := by
      unfold occupation
      simp [sub_mul, mul_sub, mul_assoc, b_sq]

theorem holeOccupation_sq : holeOccupation * holeOccupation = holeOccupation := by
  calc
    holeOccupation * holeOccupation = b * (bdag * b) * bdag := by
      unfold holeOccupation
      noncomm_ring
    _ = b * (1 - holeOccupation) * bdag := by
      rw [show bdag * b = 1 - holeOccupation by
        unfold holeOccupation
        exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using anticomm_bbdag)]
    _ = holeOccupation := by
      unfold holeOccupation
      simp [sub_mul, mul_sub, mul_assoc, bdag_sq]

theorem K_eq_occupation_sub_holeOccupation :
    K = occupation - holeOccupation := by
  unfold K occupation holeOccupation b bdag
  calc
    e₀ * e₁ = (a * a) *
        ((e₀ - e₁) * (e₀ + e₁) - (e₀ + e₁) * (e₀ - e₁)) := by
      rw [show (e₀ - e₁) * (e₀ + e₁) - (e₀ + e₁) * (e₀ - e₁) =
          4 * (e₀ * e₁) by
        noncomm_ring
        rw [show e₁ * e₀ = -(e₀ * e₁) by
          exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using anticomm)]
        module]
      simp only [a]
      rw [← map_mul]
      have hfour : (4 : CliffordAlgebra q11) =
          algebraMap ℚ (CliffordAlgebra q11) (4 : ℚ) := by
        simpa using (map_natCast (algebraMap ℚ (CliffordAlgebra q11)) 4).symm
      rw [hfour, ← mul_assoc, ← map_mul]
      norm_num
    _ = (a * (e₀ - e₁)) * (a * (e₀ + e₁)) -
          (a * (e₀ + e₁)) * (a * (e₀ - e₁)) := by
      rw [a_mul_mul, a_mul_mul, mul_sub]

theorem occupation_mul_b : occupation * b = 0 := by
  unfold occupation
  calc
    (bdag * b) * b = bdag * (b * b) := by noncomm_ring
    _ = 0 := by rw [b_sq]; simp

theorem b_mul_occupation : b * occupation = b := by
  unfold occupation
  calc
    b * (bdag * b) = (b * bdag) * b := by noncomm_ring
    _ = (1 - bdag * b) * b := by
      rw [show b * bdag = 1 - bdag * b by
        exact eq_sub_iff_add_eq.mpr anticomm_bbdag]
    _ = b := by
      rw [sub_mul]
      rw [one_mul]
      have h := occupation_mul_b
      simpa [occupation] using h

theorem holeOccupation_mul_b : holeOccupation * b = b := by
  unfold holeOccupation
  calc
    (b * bdag) * b = (1 - bdag * b) * b := by
      rw [show b * bdag = 1 - bdag * b by
        exact eq_sub_iff_add_eq.mpr anticomm_bbdag]
    _ = b := by
      rw [sub_mul]
      rw [one_mul]
      have h := occupation_mul_b
      simpa [occupation] using h

theorem b_mul_holeOccupation : b * holeOccupation = 0 := by
  unfold holeOccupation
  calc
    b * (b * bdag) = (b * b) * bdag := by noncomm_ring
    _ = 0 := by rw [b_sq]; simp

theorem K_mul_b : K * b = -b := by
  rw [K_eq_occupation_sub_holeOccupation]
  rw [sub_mul, occupation_mul_b, holeOccupation_mul_b]
  simp

theorem b_mul_K : b * K = b := by
  rw [K_eq_occupation_sub_holeOccupation]
  rw [mul_sub, b_mul_occupation, b_mul_holeOccupation]
  simp

theorem K_comm_b : K * b - b * K = -2 * b := by
  calc
    K * b - b * K = -b - b := by rw [K_mul_b, b_mul_K]
    _ = -2 * b := by noncomm_ring

theorem bdag_mul_occupation : bdag * occupation = 0 := by
  unfold occupation
  calc
    bdag * (bdag * b) = (bdag * bdag) * b := by noncomm_ring
    _ = 0 := by rw [bdag_sq]; simp

theorem occupation_mul_bdag : occupation * bdag = bdag := by
  unfold occupation
  calc
    (bdag * b) * bdag = bdag * (b * bdag) := by noncomm_ring
    _ = bdag * (1 - occupation) := by
      rw [show b * bdag = 1 - occupation by
        unfold occupation
        exact eq_sub_iff_add_eq.mpr anticomm_bbdag]
    _ = bdag := by
      rw [mul_sub]
      rw [show bdag * occupation = 0 by exact bdag_mul_occupation]
      simp

theorem holeOccupation_mul_bdag : holeOccupation * bdag = 0 := by
  unfold holeOccupation
  calc
    (b * bdag) * bdag = b * (bdag * bdag) := by noncomm_ring
    _ = 0 := by rw [bdag_sq]; simp

theorem bdag_mul_holeOccupation : bdag * holeOccupation = bdag := by
  unfold holeOccupation
  calc
    bdag * (b * bdag) = (bdag * b) * bdag := by noncomm_ring
    _ = occupation * bdag := by rfl
    _ = bdag := occupation_mul_bdag

theorem K_mul_bdag : K * bdag = bdag := by
  rw [K_eq_occupation_sub_holeOccupation]
  rw [sub_mul, occupation_mul_bdag, holeOccupation_mul_bdag]
  simp

theorem bdag_mul_K : bdag * K = -bdag := by
  rw [K_eq_occupation_sub_holeOccupation]
  rw [mul_sub, bdag_mul_occupation, bdag_mul_holeOccupation]
  simp

theorem K_comm_bdag : K * bdag - bdag * K = 2 * bdag := by
  calc
    K * bdag - bdag * K = bdag - (-bdag) := by rw [K_mul_bdag, bdag_mul_K]
    _ = 2 * bdag := by noncomm_ring

theorem K_mul_occupation : K * occupation = occupation := by
  rw [K_eq_occupation_sub_holeOccupation, sub_mul]
  rw [occupation_sq, holeOccupation_mul_occupation]
  simp

theorem occupation_mul_K : occupation * K = occupation := by
  rw [K_eq_occupation_sub_holeOccupation, mul_sub]
  rw [occupation_sq, occupation_mul_holeOccupation]
  simp

theorem K_mul_holeOccupation : K * holeOccupation = -holeOccupation := by
  rw [K_eq_occupation_sub_holeOccupation, sub_mul]
  rw [occupation_mul_holeOccupation, holeOccupation_sq]
  simp

theorem holeOccupation_mul_K : holeOccupation * K = -holeOccupation := by
  rw [K_eq_occupation_sub_holeOccupation, mul_sub]
  rw [holeOccupation_mul_occupation, holeOccupation_sq]
  simp

/-- Direct from Cl(1,1) definition with signature (+,-) -/
theorem cl11_fermion_anticommutation_omega : e₀ * e₁ + e₁ * e₀ = 0 := by exact anticomm

end Cl11Fermions
