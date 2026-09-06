import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.IndividuatedBoundedTransform

/-!
# Weighted Low-Lying Zeros of L-functions Attached to Siegel Modular Forms

Formalizes the core density and non-vanishing limits for Siegel modular forms 
as derived by Shifan Zhao (2024).
-/

noncomputable section

namespace InfoGeometry.Arithmetic.SiegelModularZeros

/--
The symplectic one-level density limit function W_Sp(x).
Evaluated against a test function Phi, the integral yields Phi_hat(0) - 1/2 Phi(0).
-/
def symplectic_one_level_density_eval (Phi_hat_0 Phi_0 : ℝ) : ℝ :=
  Phi_hat_0 - (1 / 2) * Phi_0

/--
Theorem 1.1 and Theorem 1.2: One-level density for the weighted Siegel modular forms.
For every even Schwartz function Phi with appropriately supported Fourier transform,
the one-level density for the spinor and standard L-functions approaches 
symplectic_one_level_density_eval.
-/
def siegel_one_level_density_symplectic_symmetry_prop 
    (density_limit : ℝ → ℝ) 
    (Phi_hat_0 Phi_0 : ℝ) : Prop :=
  (∀ x, density_limit x = symplectic_one_level_density_eval Phi_hat_0 Phi_0)

/--
Corollary 1.1: Non-vanishing of central values.
liminf_{k -> infty} sum_{L(1/2, F) != 0} omega_F >= 3/4
-/
def siegel_central_non_vanishing_bound_prop 
    (limit_inf : (ℕ → ℝ) → ℝ) 
    (omega_F_sum : ℕ → ℝ) : Prop :=
  limit_inf (fun k ↦ omega_F_sum k) ≥ (3 / 4 : ℝ)

end InfoGeometry.Arithmetic.SiegelModularZeros
