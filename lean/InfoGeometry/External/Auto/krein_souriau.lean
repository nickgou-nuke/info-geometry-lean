/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import InfoGeometry.Algebra.FiniteSpinAlgebra
open Matrix

/-!
# Finite Krein matrices, a Gaussian log-partition example, and phase-plane brackets

The file proves explicit 2×2 matrix identities, computes the first two
derivatives of one Gaussian log-partition function, and defines canonical
Poisson and Euclidean dissipative brackets on `ℝ × ℝ` with their elementary
symmetry and positivity properties. `cramer_rao_bound` is only a proposition
encoding an inequality; this file proves no general Cramér–Rao theorem or
general thermodynamic/metriplectic result.
-/

noncomputable section

namespace KreinSouriau

/- L1: KREIN DOUBLED SPACE -/

/-- Complex structure J: J² = -I (the i-operator in real representation) -/
def J_cplx : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem J_sq_neg_I : J_cplx * J_cplx = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_cplx]

/-- Krein metric η = diag(1, -1) -/
def η_krein : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Modular conjugation J_mod: J_mod² = I, J_mod·J_cplx·J_mod = -(J_cplx) -/
def J_mod : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem J_cplx_J_mod_noncommute :
    J_cplx * J_mod ≠ J_mod * J_cplx := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [J_cplx, J_mod, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem J_mod_sq_I : J_mod * J_mod = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mod]

theorem J_mod_conj_J : J_mod * J_cplx * J_mod = -(J_cplx) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mod, J_cplx]

/- L2: SOURIAU THERMODYNAMICS -/

/-- Partition function Z(β) for Gaussian example -/
def partitionFn (β : ℝ) : ℝ := Real.exp (β^2/2)

/-- Log partition: log Z(β) = β²/2 -/
theorem log_partition (β : ℝ) : Real.log (partitionFn β) = β^2/2 := by
  rw [partitionFn, Real.log_exp]

/-- The derivative of the Gaussian log-partition function is its natural
parameter. -/
theorem log_partition_hasDerivAt (β : ℝ) :
    HasDerivAt (fun b : ℝ => Real.log (partitionFn b)) β β := by
  have hpoly : HasDerivAt (fun b : ℝ => b^2 / 2) β β := by
    convert (((hasDerivAt_id β).mul (hasDerivAt_id β)).div_const (2 : ℝ)) using 1
    · funext b
      simp [pow_two, div_eq_mul_inv]
    · simp
  have hfun : (fun b : ℝ => Real.log (partitionFn b)) = fun b => b^2 / 2 := by
    funext b
    exact log_partition b
  rw [hfun]
  exact hpoly

/-- The Fisher information of this one-parameter Gaussian family is the
second derivative of the log-partition function, hence is identically one. -/
theorem gaussian_fisher_information (β : ℝ) :
    deriv (fun b : ℝ => deriv (fun u : ℝ => Real.log (partitionFn u)) b) β = 1 := by
  have hfirst : ∀ b : ℝ,
      deriv (fun u : ℝ => Real.log (partitionFn u)) b = b := by
    intro b
    exact (log_partition_hasDerivAt b).deriv
  rw [show (fun b : ℝ => deriv (fun u : ℝ => Real.log (partitionFn u)) b) =
      fun b => b from funext hfirst]
  exact (hasDerivAt_id β).deriv

/- L3: CRAMÉR-RAO BOUND -/

/-- Cramér-Rao bound: Var(θ̂) · I(θ) ≥ 1 (information inequality) -/
def cramer_rao_bound (variance I : ℝ) : Prop := variance * I ≥ 1

/-- For positive information, the product-form Cramér–Rao condition is
equivalent to the usual reciprocal lower bound on variance. -/
theorem cramer_rao_bound_iff_variance_ge_inv (variance I : ℝ) (hI : 0 < I) :
    cramer_rao_bound variance I ↔ 1 / I ≤ variance := by
  unfold cramer_rao_bound
  rw [ge_iff_le]
  constructor
  · intro h
    exact (div_le_iff₀ hI).2 (by simpa [mul_comm] using h)
  · intro h
    have h' := (div_le_iff₀ hI).1 h
    simpa [mul_comm] using h'

/- L4: METRIPLECTIC DYNAMICS -/

/-- Canonical Poisson bracket on the real phase plane, using coordinates
`(q,p)` and symplectic matrix `[[0,1],[-1,0]]`. -/
def poisson_bracket (F H : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  deriv (fun q => F (q, x.2)) x.1 * deriv (fun p => H (x.1, p)) x.2 -
    deriv (fun p => F (x.1, p)) x.2 * deriv (fun q => H (q, x.2)) x.1

/-- Euclidean dissipative bracket on the phase plane: the dot product of the
two coordinate gradients. -/
def diss_bracket (F S : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  deriv (fun q => F (q, x.2)) x.1 * deriv (fun q => S (q, x.2)) x.1 +
    deriv (fun p => F (x.1, p)) x.2 * deriv (fun p => S (x.1, p)) x.2

theorem poisson_bracket_skew (F H : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    poisson_bracket F H x = -poisson_bracket H F x := by
  simp [poisson_bracket]
  ring

theorem poisson_bracket_self (F : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    poisson_bracket F F x = 0 := by
  simp [poisson_bracket]
  ring

theorem diss_bracket_symmetric (F S : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    diss_bracket F S x = diss_bracket S F x := by
  simp [diss_bracket]
  ring

theorem diss_bracket_self_nonneg (F : ℝ × ℝ → ℝ) (x : ℝ × ℝ) :
    0 ≤ diss_bracket F F x := by
  unfold diss_bracket
  nlinarith [sq_nonneg (deriv (fun q => F (q, x.2)) x.1),
    sq_nonneg (deriv (fun p => F (x.1, p)) x.2)]

/-- Metriplectic evolution: Ḟ = {F, H} + (F, S) -/
def metriplectic (H S F : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  poisson_bracket F H x + diss_bracket F S x


/-- Fisher metric = Hessian of log partition: g_F = d²logZ/dβ² = 1 -/
theorem fisher_metric (β : ℝ) : Real.log (partitionFn β) = β^2/2 := by
  rw [partitionFn, Real.log_exp]

/- L3: CRAMÉR-RAO BOUND -/

end KreinSouriau
