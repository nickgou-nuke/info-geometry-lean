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
