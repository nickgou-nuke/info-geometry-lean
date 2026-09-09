import Mathlib.Tactic

/-!
# p-adic L functions and trivial zeroes

Formalizes the trivial zero derivative conjecture and the filtration structure 
for the p-adic L-function of the symmetric square of an elliptic curve,
as presented by Bernadette Perrin-Riou.
-/

namespace InfoGeometry.Arithmetic.PadicLFunction

/-- 
The components of the trivial zero derivative formula:
- L_p_prime_0: The derivative of the p-adic L-function at s = 0.
- ell_p_M: The Greenberg invariant of M = Sym^2(h^1(E)).
- L_M_0: The complex L-function evaluated at s = 0.
- Omega_inf: The complex period.
-/
structure TrivialZeroConjectureData where
  L_p_prime_0 : ℝ
  ell_p_M : ℝ
  L_M_0 : ℝ
  Omega_inf : ℝ

/--
The Greenberg-Tilouine / Greenberg conjecture for the derivative of the p-adic L-function 
at the trivial zero s = 0.
L_p'(M, 0) = ell_p(M) * (L(M, 0) / Omega_inf)
-/
def trivial_zero_derivative_prop (d : TrivialZeroConjectureData) : Prop :=
  d.L_p_prime_0 = d.ell_p_M * (d.L_M_0 / d.Omega_inf)

/--
The p-adic filtration basis components.
-/
structure PadicFiltrationBasis (V : Type) [AddCommGroup V] [Module ℝ V] where
  e_0 : V
  e_minus1 : V
  e_minus2 : V
  lambda : ℝ

/--
The omega_e vector which spans Fil^0 D_p(V).
omega_e = (lambda / 2) * e_{-2} + e_{-1} + (1 / 2*lambda) * e_0
-/
noncomputable def omega_e {V : Type} [AddCommGroup V] [Module ℝ V] 
    (b : PadicFiltrationBasis V) : V :=
  (b.lambda / 2) • b.e_minus2 + b.e_minus1 + (1 / (2 * b.lambda)) • b.e_0

/--
The second basis vector for Fil^{-1} D_p(V).
e_{-1} + lambda * e_{-2}
-/
def fil_minus1_second_vector {V : Type} [AddCommGroup V] [Module ℝ V] 
    (b : PadicFiltrationBasis V) : V :=
  b.e_minus1 + b.lambda • b.e_minus2

/--
Proposition: The linear combination 2*lambda * omega_e - 2*lambda * (e_{-1} + lambda * e_{-2})
equals e_0 - lambda^2 * e_{-2}.
-/
def padic_filtration_linear_combination_prop {V : Type} [AddCommGroup V] [Module ℝ V] 
    (b : PadicFiltrationBasis V) : Prop :=
  b.lambda ≠ 0 →
  (2 * b.lambda) • omega_e b - (2 * b.lambda) • fil_minus1_second_vector b = 
  b.e_0 - (b.lambda ^ 2) • b.e_minus2

end InfoGeometry.Arithmetic.PadicLFunction
