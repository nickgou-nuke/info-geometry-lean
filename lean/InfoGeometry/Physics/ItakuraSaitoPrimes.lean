import Mathlib.Tactic

/-!
# Itakura-Saito Divergence and the Prime Log-Generating Potential

This module formalizes the Itakura-Saito (IS) divergence for the prime number 
generating potential (the Riemann Zeta partition function).

We define the regularized Free Energy $F_\epsilon$ using the IS divergence as 
the Bregman generator (Burg entropy) for the prime partition distribution.
-/

namespace InfoGeometry

/-- The Itakura-Saito Divergence between two strictly positive real scalars P and Q. -/
noncomputable def itakura_saito (P Q : ℝ) : ℝ :=
  (P / Q) - Real.log (P / Q) - 1

theorem itakura_saito_common_scale_invariant
    (P Q c : ℝ) (hQ : Q ≠ 0) (hc : c ≠ 0) :
    itakura_saito (c * P) (c * Q) = itakura_saito P Q := by
  have hratio : (c * P) / (c * Q) = P / Q := by
    field_simp
  simp [itakura_saito, hratio]

theorem itakura_saito_exp_log_difference (u v : ℝ) :
    itakura_saito (Real.exp u) (Real.exp v) =
      Real.exp (u - v) - (u - v) - 1 := by
  have hratio : Real.exp u / Real.exp v = Real.exp (u - v) :=
    (Real.exp_sub u v).symm
  simp [itakura_saito, hratio]

theorem itakura_saito_nonneg
    (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) :
    0 ≤ itakura_saito P Q := by
  let r : ℝ := P / Q
  have hr : 0 < r := div_pos hP hQ
  have h := Real.add_one_le_exp (Real.log r)
  have hexp : Real.exp (Real.log r) = r := Real.exp_log hr
  rw [itakura_saito]
  change 0 ≤ r - Real.log r - 1
  linarith

theorem itakura_saito_eq_zero_iff
    (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) :
    itakura_saito P Q = 0 ↔ P = Q := by
  let r : ℝ := P / Q
  have hr : 0 < r := div_pos hP hQ
  constructor
  · intro hzero
    have hlog : Real.log r = r - 1 := by
      rw [itakura_saito] at hzero
      change r - Real.log r - 1 = 0 at hzero
      linarith
    have hlog_zero : Real.log r = 0 := by
      by_contra hne
      have hstrict := Real.add_one_lt_exp hne
      have hexp : Real.exp (Real.log r) = r := Real.exp_log hr
      linarith
    have hr_one : r = 1 := Real.eq_one_of_pos_of_log_eq_zero hr hlog_zero
    dsimp [r] at hr_one
    field_simp at hr_one
    exact hr_one
  · intro hPQ
    subst Q
    simp [itakura_saito, ne_of_gt hP]

/-- 
  The Prime Log-Generating Potential (Riemann Zeta).
  Here we abstract it as a function of the thermodynamic beta.
-/
abbrev PrimeGeneratingPotential :=
  {zeta : ℝ → ℝ // ∀ β, 0 < zeta β}

namespace PrimeGeneratingPotential

abbrev zeta (P : PrimeGeneratingPotential) : ℝ → ℝ := P.1
abbrev zeta_pos (P : PrimeGeneratingPotential) : ∀ β, 0 < P.zeta β := P.2

end PrimeGeneratingPotential

/--
  The Regularized Free Energy.
  F_ε = -log(Z) - ε * D_IS(P || Q)
-/
noncomputable def regularized_free_energy (Z P Q ε : ℝ) : ℝ :=
  -Real.log Z - ε * itakura_saito P Q

/--
  Theorem: The regularized free energy of the prime partition function 
  evaluated against a reference scale Q_ref.
-/
theorem prime_regularized_free_energy (P_gen : PrimeGeneratingPotential) (β Q_ref ε : ℝ) 
    (hQ : 0 < Q_ref) (hZ : 0 < P_gen.zeta β) :
    regularized_free_energy (P_gen.zeta β) (P_gen.zeta β) Q_ref ε =
    -Real.log (P_gen.zeta β) - ε * ((P_gen.zeta β / Q_ref) - Real.log (P_gen.zeta β / Q_ref) - 1) := by
  dsimp [regularized_free_energy, itakura_saito]

/--
  When the reference scale matches the prime potential exactly (Q_ref = P),
  the IS divergence vanishes, and the Free Energy reduces to the unregularized -log(Z).
-/
theorem itakura_saito_self_eq_zero (P : ℝ) (hP : 0 < P) : 
    itakura_saito P P = 0 := by
  dsimp [itakura_saito]
  have h1 : P / P = 1 := div_self (ne_of_gt hP)
  rw [h1, Real.log_one]
  norm_num

theorem prime_regularized_free_energy_matched (P_gen : PrimeGeneratingPotential) (β ε : ℝ) :
    regularized_free_energy (P_gen.zeta β) (P_gen.zeta β) (P_gen.zeta β) ε = 
    -Real.log (P_gen.zeta β) := by
  dsimp [regularized_free_energy]
  rw [itakura_saito_self_eq_zero (P_gen.zeta β) (P_gen.zeta_pos β)]
  ring

end InfoGeometry
