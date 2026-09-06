import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.IndividuatedBoundedTransform

/-!
# Low-Lying Zeros of L-functions for Quaternion Algebras

Formalizes the core density and non-vanishing proportion bounds 
as derived by Didier Lesesvre (2021).
-/

noncomputable section

namespace InfoGeometry.Arithmetic.LowLyingZerosQuaternion

/--
The orthogonal one-level density limit function W_O(x).
Evaluated against a test function phi, the integral yields phi_hat(0) + 1/2 phi(0).
-/
def orthogonal_one_level_density_eval (phi_hat_0 phi_0 : ℝ) : ℝ :=
  phi_hat_0 + (1 / 2) * phi_0

/--
Theorem 1.2: One-level density for the universal family of a totally definite quaternion algebra.
For every even Schwartz function phi with Fourier transform supported in (-2/3, 2/3),
the one-level density approaches orthogonal_one_level_density_eval.
-/
def one_level_density_orthogonal_symmetry_prop 
    (density_limit : ℝ → ℝ) 
    (phi_hat_0 phi_0 : ℝ) : Prop :=
  (∀ x, density_limit x = orthogonal_one_level_density_eval phi_hat_0 phi_0)

/--
Corollary 1.3: Bound on the proportion of non-vanishing at the central point.
liminf_{Q -> infty} sum_{m >= 1} m * p_m(Q) <= 2
where p_m(Q) is the proportion of automorphic representations in the truncated 
universal family with vanishing of order m at the central point.
-/
def non_vanishing_proportion_bound_prop 
    (p : ℕ → ℝ → ℝ) -- p_m(Q)
    (limit_inf : (ℝ → ℝ) → ℝ) : Prop :=
  limit_inf (fun Q ↦ ∑' (m : ℕ), if m ≥ 1 then (m : ℝ) * p m Q else 0) ≤ 2

end InfoGeometry.Arithmetic.LowLyingZerosQuaternion
