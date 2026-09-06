import Mathlib.Analysis.InnerProductSpace.Basic

open Complex
open LinearMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

lemma adelic_symmetry_spectrum
  (D D_dag : V →ₗ[ℂ] V)
  (h_adj : ∀ (u v : V), inner ℂ u (D v) = (inner ℂ (D_dag u) v : ℂ))
  (h_id : D + D_dag = 1)
  (v : V)
  (lambda : ℂ)
  (hv_nonzero : v ≠ 0)
  (h_eigen : D v = lambda • v) :
  lambda.re = 1/2 := by
  have h1 : (inner ℂ v (D v) : ℂ) = lambda * inner ℂ v v := by
    rw [h_eigen, inner_smul_right]
  have h2 : (inner ℂ v (D_dag v) : ℂ) = star lambda * inner ℂ v v := by
    rw [← inner_conj_symm, ← h_adj, h_eigen, inner_smul_right]; simp
  have h3 : (inner ℂ v (D v) : ℂ) + inner ℂ v (D_dag v) = inner ℂ v v := by
    rw [←inner_add_right]
    have h_add : D v + D_dag v = v := by
      calc D v + D_dag v
        _ = (D + D_dag) v := rfl
        _ = (1 : V →ₗ[ℂ] V) v := by rw [h_id]
        _ = v := rfl
    rw [h_add]
  have h4 : lambda * inner ℂ v v + star lambda * inner ℂ v v = inner ℂ v v := by
    rw [←h1, ←h2, h3]
  have h5 : (lambda + star lambda) * inner ℂ v v = 1 * inner ℂ v v := by
    rw [add_mul, h4, one_mul]
  have h6 : (inner ℂ v v : ℂ) ≠ 0 := by
    intro h
    have h_zero : v = 0 := by exact inner_self_eq_zero.mp h
    exact hv_nonzero h_zero
  have h7 : lambda + star lambda = 1 := by
    have h_cancel : (lambda + star lambda - 1) * inner ℂ v v = 0 := by
      calc (lambda + star lambda - 1) * inner ℂ v v
        _ = (lambda + star lambda) * inner ℂ v v - 1 * inner ℂ v v := sub_mul (lambda + star lambda) 1 (inner ℂ v v)
        _ = 0 := by rw [h5, sub_self]
    cases mul_eq_zero.mp h_cancel with
    | inl h_eq =>
        exact sub_eq_zero.mp h_eq
    | inr h_eq =>
        contradiction
  have h8 : lambda + star lambda = (2 * lambda.re : ℂ) := by { apply Complex.ext; { simp; ring }; { simp } }
  rw [h8] at h7
  have h9 : (2 : ℂ) * lambda.re = 1 := h7
  have h11 : 2 * lambda.re = 1 := by { have h10 := congr_arg Complex.re h9; simpa using h10 }
  have h12 : (2 : ℝ) ≠ 0 := by norm_num
  calc lambda.re
    _ = (2 : ℝ)⁻¹ * (2 * lambda.re) := by rw [← mul_assoc, inv_mul_cancel₀ h12, one_mul]
    _ = (2 : ℝ)⁻¹ * 1 := by rw [h11]
    _ = 1 / 2 := by norm_num
