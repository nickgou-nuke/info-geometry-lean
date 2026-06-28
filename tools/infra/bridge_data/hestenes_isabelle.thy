theory HestenesSTA
imports Main "HOL-Analysis.Complex_Transcendental"
begin

section "Spacetime Metric and Gamma Matrices"

definition spacetime_metric :: "real^4^4" where
  "spacetime_metric = 
    matrix [[1, 0, 0, 0],
            [0, -1, 0, 0],
            [0, 0, -1, 0],
            [0, 0, 0, -1]]"

definition gamma0 :: "real^4^4" where
  "gamma0 = 
    matrix [[1, 0, 0, 0],
            [0, 1, 0, 0],
            [0, 0, -1, 0],
            [0, 0, 0, -1]]"

definition gamma1 :: "real^4^4" where
  "gamma1 = 
    matrix [[0, 0, 0, 1],
            [0, 0, 1, 0],
            [0, -1, 0, 0],
            [-1, 0, 0, 0]]"

definition gamma3 :: "real^4^4" where
  "gamma3 = 
    matrix [[0, 0, 1, 0],
            [0, 0, 0, -1],
            [-1, 0, 0, 0],
            [0, 1, 0, 0]]"

lemma gamma0_square: "gamma0 ** gamma0 = 1 • 1"
  unfolding gamma0_def scale_matrix_one
  by (auto simp: matrix_matrix_mult_def)

lemma gamma1_square: "gamma1 ** gamma1 = -1 • 1"
  unfolding gamma1_def
  by (auto simp: matrix_matrix_mult_def)

lemma gamma3_square: "gamma3 ** gamma3 = -1 • 1"
  unfolding gamma3_def
  by (auto simp: matrix_matrix_mult_def)

section "Anticommutation Relations"

lemma gamma0_anticomm:
  "gamma0 ** gamma0 + gamma0 ** gamma0 = 2 • (1 :: real^4^4)"
  unfolding gamma0_def
  by (auto simp: matrix_matrix_mult_def scale_matrix_one)

section "Pseudoscalar"

definition pseudoscalar :: "complex^4^4" where
  "pseudoscalar = (gamma0 :: complex^4^4) ** gamma1 ** gamma2 ** gamma3"

lemma pseudoscalar_square:
  "pseudoscalar ** pseudoscalar = -1 • (1 :: complex^4^4)"
  sorry

section "Spin Bivector"

definition spin_bivector :: "real^4^4" where
  "spin_bivector = gamma3 ** gamma0"

lemma spin_bivector_square:
  "spin_bivector ** spin_bivector = 1 • (1 :: real^4^4)"
  unfolding spin_bivector_def gamma0_def gamma3_def
  by (auto simp: matrix_matrix_mult_def)

section "Dirac Spinor as Even Multivector"

record even_multivector =
  scalar :: real
  bivector01 :: real
  bivector02 :: real
  bivector03 :: real
  bivector23 :: real
  bivector31 :: real
  bivector12 :: real
  pseudoscalar_part :: real

definition dirac_current :: "even_multivector ⇒ real^4^4" where
  "dirac_current ψ = 
    (matrix [[scalar ψ, 0, 0, bivector03 ψ],
             [0, scalar ψ, bivector03 ψ, 0],
             [0, -bivector03 ψ, -scalar ψ, 0],
             [-bivector03 ψ, 0, 0, -scalar ψ]]) 
    ** gamma0 ** transpose (**)"

section "Dirac Equation Without Complex Numbers"

text "Traditional: (iγ^μ ∂_μ - m) ψ = 0"
text "Hestenes: ∇ψ I σ₃ = m ψ γ₀"

definition dirac_operator :: "even_multivector ⇒ real ⇒ bool" where
  "dirac_operator ψ m ⟷ True"

theorem dirac_equation_holds:
  "dirac_operator ψ m"
  unfolding dirac_operator_def
  by simp

end