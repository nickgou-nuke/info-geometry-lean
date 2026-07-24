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
    _ = 1 := by simp [q11, proj_apply]

theorem e₁_sq : e₁ * e₁ = -1 := by
  calc
    e₁ * e₁ = algebraMap ℚ (CliffordAlgebra q11) (q11 (fun i => if i = 1 then 1 else 0)) := ι_sq_scalar _ _
    _ = -1 := by simp [q11, proj_apply]

theorem orth : q11.IsOrtho (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0) := by
  simp [q11, IsOrtho, proj_apply]

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



/-- Direct from Cl(1,1) definition with signature (+,-) -/
theorem cl11_fermion_anticommutation_omega : e₀ * e₁ + e₁ * e₀ = 0 := by exact anticomm

end Cl11Fermions
