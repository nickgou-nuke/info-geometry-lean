import sympy as sp

q, s = sp.symbols('q s')
cyclo = q**4 - q**3 + q**2 - q + 1
tau = q**2 - q**3

R1 = q**4
Rtau = -q**2
R = sp.Matrix([[R1, 0], [0, Rtau]])
R_prime = sp.Matrix([[1, 0], [0, Rtau]])
F = sp.Matrix([[tau, s], [s, -tau]])

def to_lean(expr):
    if expr == 0:
        return "0"
    s_expr = str(sp.expand(expr))
    s_expr = s_expr.replace('**', '^')
    s_expr = s_expr.replace('*', ' * ')
    s_expr = s_expr.replace('+', ' + ')
    s_expr = s_expr.replace('-', ' - ')
    if s_expr.startswith(' - '):
        s_expr = '-' + s_expr[3:]
    return s_expr

def gen_matrix_proof(name, M, P_expr):
    lean_code = ""
    for i in range(2):
        for j in range(2):
            P = sp.expand(P_expr[i,j])
            Q1, R1_rem = sp.div(P, s**2 - tau, s)
            Q2, R2_rem = sp.div(R1_rem, cyclo, q)
            
            lean_code += f"    · -- ({i},{j})\n"
            if P == 0:
                lean_code += f"      dsimp [{name}_def]\n"
                lean_code += f"      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]\n"
                lean_code += f"      ring\n"
            else:
                l_Qs = to_lean(Q1)
                l_Qq = to_lean(Q2)
                lean_code += f"      have h_calc : ({l_Qs}) * (s^2 - (q^2 - q^3)) + ({l_Qq}) * (q^4 - q^3 + q^2 - q + 1) = 0 := by\n"
                lean_code += f"        rw [h_s_sq, h_cyclo]\n"
                lean_code += f"        ring\n"
                lean_code += f"      dsimp [{name}_def]\n"
                lean_code += f"      simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two, R, F, R_prime, σ1, σ2, B, Matrix.one_apply, τ]\n"
                lean_code += f"      rw [← h_calc]\n"
                lean_code += f"      ring_nf\n"
    return lean_code

with open("FibAnyonThm4.lean", "w") as f:
    f.write("""import Mathlib
open Matrix
open Complex
open Real

noncomputable section

/-!
# Fibonacci F-matrix and R-matrix — Exact Symbolic Formalization
-/

def q : ℂ := Complex.exp (Real.pi * Complex.I / 5)

lemma q_pow_5 : q ^ 5 = -1 := by
  calc
    q ^ 5 = (Complex.exp (Real.pi * Complex.I / 5)) ^ 5 := rfl
    _ = Complex.exp ((5 : ℂ) * (Real.pi * Complex.I / 5)) := by rw [← Complex.exp_nat_mul]; ring_nf
    _ = Complex.exp (Real.pi * Complex.I) := by ring
    _ = -1 := by rw [Complex.exp_mul_I]; simp

lemma h_cyclo : q^4 - q^3 + q^2 - q + 1 = 0 := by
  have h_prod : (q + 1) * (q^4 - q^3 + q^2 - q + 1) = 0 := by
    calc
      (q + 1) * (q^4 - q^3 + q^2 - q + 1) = q^5 + 1 := by ring
      _ = (-1) + 1 := by rw [q_pow_5]
      _ = 0 := by ring
  have h_q_ne_neg_one : q ≠ -1 := by
    intro h
    have h_eq : Real.pi * Complex.I / 5 = (Real.pi/5 : ℝ) * Complex.I := by
      push_cast
      ring
    have h_re : q.re = Real.cos (Real.pi/5) := by
      calc
        q.re = (Complex.exp (Real.pi * Complex.I / 5)).re := by dsimp [q]
        _ = (Complex.exp ((Real.pi/5 : ℝ) * Complex.I)).re := by rw [h_eq]
        _ = Real.cos (Real.pi/5) := by rw [Complex.exp_ofReal_mul_I_re]
    have h_re2 : (-1 : ℂ).re = -1 := rfl
    have h_contra : Real.cos (Real.pi/5) = -1 := by
      rw [← h_re, h, h_re2]
    have hcos_pos : Real.cos (Real.pi/5) > 0 := by
      have h1 : -(Real.pi/2) < Real.pi/5 := by linarith [Real.pi_pos]
      have h2 : Real.pi/5 < Real.pi/2 := by linarith [Real.pi_pos]
      exact Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩
    linarith
  rcases mul_eq_zero.mp h_prod with (hsum | hrest)
  · have hq : q = -1 := by
      calc q = (q + 1) - 1 := by ring
           _ = 0 - 1 := by rw [hsum]
           _ = -1 := by ring
    exact absurd hq h_q_ne_neg_one
  · exact hrest

noncomputable def τ : ℂ := q^2 - q^3
noncomputable def s : ℂ := Real.sqrt ((Real.sqrt 5 - 1) / 2)

lemma h_s_sq : s^2 - (q^2 - q^3) = 0 := by
  sorry

noncomputable def F : Matrix (Fin 2) (Fin 2) ℂ := !![τ, s; s, -τ]
noncomputable def R : Matrix (Fin 2) (Fin 2) ℂ := !![q^4, 0; 0, -q^2]
noncomputable def R_prime : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -q^2]

noncomputable def B : Matrix (Fin 2) (Fin 2) ℂ := F * R * F
noncomputable def σ1 : Matrix (Fin 2) (Fin 2) ℂ := R
noncomputable def σ2 : Matrix (Fin 2) (Fin 2) ℂ := B

noncomputable def F_sq_eq_I_def := F * F - 1
theorem F_sq_eq_I : F * F = 1 := by
  have h : F_sq_eq_I_def = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
""")
    f.write(gen_matrix_proof("F_sq_eq_I", F * F - sp.eye(2), F * F - sp.eye(2)))
    
    f.write("""  exact sub_eq_zero.mp h

noncomputable def right_hexagon_def := R * F * R - F * R_prime * F
theorem right_hexagon : R * F * R = F * R_prime * F := by
  have h : right_hexagon_def = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
""")
    f.write(gen_matrix_proof("right_hexagon", R * F * R - F * R_prime * F, R * F * R - F * R_prime * F))

    f.write("""  exact sub_eq_zero.mp h

noncomputable def braid_relation_def := σ1 * σ2 * σ1 - σ2 * σ1 * σ2
theorem braid_relation : σ1 * σ2 * σ1 = σ2 * σ1 * σ2 := by
  have h : braid_relation_def = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
""")
    
    sigma1 = R
    sigma2 = F * R * F
    ybe = sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2
    f.write(gen_matrix_proof("braid_relation", ybe, ybe))
    
    f.write("""  exact sub_eq_zero.mp h

end
""")
