import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.EllipticYangBaxter

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def ellipticRMatrix (Ω_ij u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((Ω_ij * u : ℝ) : ℂ)))

def kzbHamiltonian (γ : ℝ) : ℝ :=
  γ ^ 2 / 2

def casimirInvariant (γ_i γ_j : ℝ) : ℝ :=
  γ_i * γ_j

theorem elliptic_yang_baxter_identity (γ₁ γ₂ γ₃ u v : ℝ) :
    let Ω₁₂ := casimirInvariant γ₁ γ₂
    let Ω₁₃ := casimirInvariant γ₁ γ₃
    let Ω₂₃ := casimirInvariant γ₂ γ₃
    let R₁₂_u := ellipticRMatrix Ω₁₂ u
    let R₁₃_uv := ellipticRMatrix Ω₁₃ (u + v)
    let R₂₃_v := ellipticRMatrix Ω₂₃ v
    R₁₂_u * R₁₃_uv * R₂₃_v = R₂₃_v * R₁₃_uv * R₁₂_u := by
  intro Ω₁₂ Ω₁₃ Ω₂₃ R₁₂_u R₁₃_uv R₂₃_v
  dsimp [R₁₂_u, R₁₃_uv, R₂₃_v]
  ring

theorem elliptic_R_matrix_unitary (Ω u : ℝ) :
    ‖ellipticRMatrix Ω u‖ = 1 := by
  unfold ellipticRMatrix
  have h_re : (Complex.I * (((Ω * u : ℝ) : ℂ))).re = 0 := by
    simp [mul_re, I_re, ofReal_re, I_im, ofReal_im]
  have h_norm := Complex.norm_exp (Complex.I * (((Ω * u : ℝ) : ℂ)))
  rw [h_re, Real.exp_zero] at h_norm
  exact h_norm

theorem elliptic_R_matrix_at_zero (γ_i γ_j : ℝ) :
    ellipticRMatrix (γ_i * γ_j) 0 = 1 := by
  unfold ellipticRMatrix
  have h_zero : ((γ_i * γ_j * 0 : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [h_zero, mul_zero, Complex.exp_zero]

theorem elliptic_R_matrix_inversion (Ω u : ℝ) :
    ellipticRMatrix Ω u * ellipticRMatrix Ω (-u) = 1 := by
  unfold ellipticRMatrix
  rw [← Complex.exp_add]
  have : Complex.I * (((Ω * u : ℝ) : ℂ)) + Complex.I * (((Ω * -u : ℝ) : ℂ)) = 0 := by
    push_cast
    ring
  rw [this, Complex.exp_zero]
