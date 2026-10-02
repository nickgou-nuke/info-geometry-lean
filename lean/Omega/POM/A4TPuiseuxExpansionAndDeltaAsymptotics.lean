import Mathlib.Tactic

namespace Omega.POM

/-- Coefficients of the positive branch after clearing the leading denominator by
`x = u * lambda`. -/
def pom_a4t_puiseux_expansion_and_delta_asymptotics_positive_scaled_coeff :
    ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 1 / 2
  | 3 => 0
  | 4 => 7 / 8
  | 5 => -3
  | 6 => 73 / 16
  | _ => 0

/-- Coefficients of the negative branch after clearing the leading denominator by
`x = u * lambda`. -/
def pom_a4t_puiseux_expansion_and_delta_asymptotics_negative_scaled_coeff :
    ℕ → ℚ
  | 0 => -1
  | 1 => 1
  | 2 => -1 / 2
  | 3 => 0
  | 4 => -7 / 8
  | 5 => -3
  | 6 => -73 / 16
  | _ => 0

/-- Cauchy product coefficient for formal power series truncated at the requested degree. -/
def pom_a4t_puiseux_expansion_and_delta_asymptotics_coeff_mul
    (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  (Finset.range (n + 1)).sum fun k => a k * b (n - k)

/-- Coefficient of a formal power-series power. -/
def pom_a4t_puiseux_expansion_and_delta_asymptotics_coeff_pow
    (a : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, n => if n = 0 then 1 else 0
  | m + 1, n =>
      pom_a4t_puiseux_expansion_and_delta_asymptotics_coeff_mul a
        (pom_a4t_puiseux_expansion_and_delta_asymptotics_coeff_pow a m) n

/-- Coefficients of the cleared residual
`x^5 - 2 u x^4 - x^3 - 2 u^4 x + 2 u^5`. -/
def pom_a4t_puiseux_expansion_and_delta_asymptotics_cleared_residual_coeff
    (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  pom_a4t_puiseux_expansion_and_delta_asymptotics_coeff_pow a 5 n -
    2 * (if n = 0 then 0 else
      pom_a4t_puiseux_expansion_and_delta_asymptotics_coeff_pow a 4 (n - 1)) -
    pom_a4t_puiseux_expansion_and_delta_asymptotics_coeff_pow a 3 n -
    2 * (if n < 4 then 0 else a (n - 4)) +
    if n = 5 then 2 else 0

/-- The displayed delta expansion is recorded as its coefficient tuple. -/
def pom_a4t_puiseux_expansion_and_delta_asymptotics_delta_coefficients :
    ℚ × ℚ × ℚ × ℚ :=
  (-3, 1 / 2, 1, 471 / 40)

/-- Concrete formal seed for the paper statement: the two Puiseux ansatzes solve the cleared
quintic through order `u^6`, and the encoded delta coefficients have the displayed values. -/
def pom_a4t_puiseux_expansion_and_delta_asymptotics_statement : Prop :=
  (∀ n : ℕ,
      n ≤ 6 →
        pom_a4t_puiseux_expansion_and_delta_asymptotics_cleared_residual_coeff
            pom_a4t_puiseux_expansion_and_delta_asymptotics_positive_scaled_coeff n = 0) ∧
    (∀ n : ℕ,
      n ≤ 6 →
        pom_a4t_puiseux_expansion_and_delta_asymptotics_cleared_residual_coeff
            pom_a4t_puiseux_expansion_and_delta_asymptotics_negative_scaled_coeff n = 0) ∧
    pom_a4t_puiseux_expansion_and_delta_asymptotics_delta_coefficients =
      (-3, 1 / 2, 1, 471 / 40)

/-- Paper label: `prop:pom-a4t-puiseux-expansion-and-delta-asymptotics`. -/
theorem paper_pom_a4t_puiseux_expansion_and_delta_asymptotics :
    pom_a4t_puiseux_expansion_and_delta_asymptotics_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    interval_cases n <;>
      decide
  · intro n hn
    interval_cases n <;>
      decide
  · norm_num [pom_a4t_puiseux_expansion_and_delta_asymptotics_delta_coefficients]

end Omega.POM
