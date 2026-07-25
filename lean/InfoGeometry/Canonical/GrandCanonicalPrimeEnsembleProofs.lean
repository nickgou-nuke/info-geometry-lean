import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
import InfoGeometry.Arithmetic.PrimeMajoranaCAR
import InfoGeometry.Arithmetic.PrimeSurprisalNormalization
import InfoGeometry.Arithmetic.PrimeSuperalgebra
import InfoGeometry.Canonical.Arithmetic.ZetaEulerProductBridge

/-!
# InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleProofs

Proof-only layer for the finite prime grand-canonical lane.

This file carries formulas as functions and proves the finite identities
directly.  It does not introduce certificates, sockets, axioms, or witness
packets.

The layer closes the finite pieces used by the prime/zeta thermodynamic lane:

* energy is `log(volume)`;
* Boltzmann weights are positive;
* finite partition functions are positive;
* Gibbs probabilities normalize to one;
* finite log-volume products turn into additive sums;
* a two-Majorana Dirac square cancels the cross term;
* the finite prime square-free partition equals its product form;
* the bosonic prime Euler product bridges to `riemannZeta`.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleProofs

open InfoGeometry.Arithmetic.PrimeSurprisalNormalization

/-! ## 1. Log-volume normalization -/

/-- A profile carrying raw multiplicative volume data. -/
structure VolumeProfile (α : Type*) where
  volume : α → ℝ

/-- Energy is the logarithm of the volume. -/
def energy {α : Type*} (P : VolumeProfile α) (x : α) : ℝ :=
  Real.log (P.volume x)

/-- Energy is definitional log-volume. -/
theorem energy_eq_log_volume {α : Type*} (P : VolumeProfile α) (x : α) :
    energy P x = Real.log (P.volume x) :=
  rfl

/-- Boltzmann weight for a finite grand-canonical observable. -/
def boltzmannWeight {α : Type*} (β : ℝ) (energy mu : α → ℝ) (x : α) : ℝ :=
  Real.exp (-β * (energy x - mu x))

/-- Finite partition function. -/
def partitionFunction {α : Type*} [Fintype α]
    (β : ℝ) (energy mu : α → ℝ) : ℝ :=
  ∑ x, boltzmannWeight β energy mu x

/-- Gibbs probability after finite normalization. -/
def gibbsProbability {α : Type*} [Fintype α]
    (β : ℝ) (energy mu : α → ℝ) (x : α) : ℝ :=
  boltzmannWeight β energy mu x / partitionFunction β energy mu

/-- Boltzmann weights are positive. -/
theorem boltzmannWeight_pos {α : Type*}
    (β : ℝ) (energy mu : α → ℝ) (x : α) :
    0 < boltzmannWeight β energy mu x := by
  unfold boltzmannWeight
  exact Real.exp_pos _

/-- The finite partition function is positive when the state space is nonempty. -/
theorem partitionFunction_pos {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy mu : α → ℝ) :
    0 < partitionFunction β energy mu := by
  classical
  unfold partitionFunction
  exact Finset.sum_pos
    (by
      intro x hx
      exact Real.exp_pos _)
    Finset.univ_nonempty

/-- Gibbs probabilities are nonnegative. -/
theorem gibbsProbability_nonneg {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy mu : α → ℝ) (x : α) :
    0 ≤ gibbsProbability β energy mu x := by
  unfold gibbsProbability
  exact div_nonneg (le_of_lt (boltzmannWeight_pos β energy mu x))
    (le_of_lt (partitionFunction_pos β energy mu))

/-- Gibbs probabilities sum to one after normalization. -/
theorem gibbsProbability_sum_eq_one {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy mu : α → ℝ) :
    ∑ x, gibbsProbability β energy mu x = 1 := by
  have hsum :
      ∑ x : α, boltzmannWeight β energy mu x / partitionFunction β energy mu =
        (∑ x : α, boltzmannWeight β energy mu x) /
          partitionFunction β energy mu := by
    exact (Finset.sum_div
      (s := (Finset.univ : Finset α))
      (f := fun x => boltzmannWeight β energy mu x)
      (a := partitionFunction β energy mu)).symm
  rw [show ∑ x : α, gibbsProbability β energy mu x =
      ∑ x : α, boltzmannWeight β energy mu x / partitionFunction β energy mu by
      rfl]
  rw [hsum]
  exact div_self (ne_of_gt (partitionFunction_pos β energy mu))

/-! ## 2. Finite log-volume products -/

/-- Finite log-volume product-to-sum law. -/
theorem finite_log_volume_product
    {α : Type*} (w : α → ℝ) (S : Finset α)
    (hw : ∀ a ∈ S, 0 < w a) :
    -Real.log (S.prod w) = S.sum (fun a => -Real.log (w a)) := by
  have hlog : Real.log (S.prod w) = S.sum (fun a => Real.log (w a)) := by
    simpa using Real.log_prod (s := S) (f := w) (by
      intro a ha
      exact ne_of_gt (hw a ha))
  calc
    -Real.log (S.prod w) = -S.sum (fun a => Real.log (w a)) := by rw [hlog]
    _ = S.sum (fun a => -Real.log (w a)) := by simp [Finset.sum_neg_distrib]

/-! ## 3. Two-Majorana cancellation -/

/--
Minimal two-mode Majorana pair.

This records the algebraic inputs needed for the finite Dirac-square
cancellation.
-/
structure TwoMajoranaPair (Op : Type*) [Ring Op] where
  gamma₁ : Op
  gamma₂ : Op
  gamma₁_sq : gamma₁ * gamma₁ = 1
  gamma₂_sq : gamma₂ * gamma₂ = 1
  anticomm : gamma₁ * gamma₂ + gamma₂ * gamma₁ = 0

namespace TwoMajoranaPair

variable {Op : Type*} [Ring Op]
variable (M : TwoMajoranaPair Op)

/-- The finite two-mode Dirac operator. -/
def dirac : Op :=
  M.gamma₁ + M.gamma₂

/-- The Dirac square cancels the cross term and returns `2`. -/
-- theorem-class: derived
theorem finite_majorana_dirac_square :
    M.dirac * M.dirac = (2 : Op) := by
  unfold dirac
  calc
    (M.gamma₁ + M.gamma₂) * (M.gamma₁ + M.gamma₂)
        = M.gamma₁ * M.gamma₁
          + M.gamma₁ * M.gamma₂
          + M.gamma₂ * M.gamma₁
          + M.gamma₂ * M.gamma₂ := by
            noncomm_ring
    _ = (2 : Op) := by
          rw [M.gamma₁_sq, M.gamma₂_sq]
          have hcross : M.gamma₁ * M.gamma₂ + M.gamma₂ * M.gamma₁ = 0 := M.anticomm
          have hsum :
              1 + M.gamma₁ * M.gamma₂ + M.gamma₂ * M.gamma₁ + 1 =
                1 + (M.gamma₁ * M.gamma₂ + M.gamma₂ * M.gamma₁) + 1 := by
            abel
          rw [hsum, hcross]
          norm_num

end TwoMajoranaPair

/-! ## 4. Prime square-free product and zeta bridge -/

/-- The finite prime square-free partition equals its product form. -/
theorem finite_prime_grand_partition_product
    (P : InfoGeometry.Arithmetic.PrimeSuperalgebra.PrimeCutoff) (β : ℝ) :
    InfoGeometry.Arithmetic.PrimeSuperalgebra.finiteFermionicSquarefreePartition P β =
      InfoGeometry.Arithmetic.PrimeSuperalgebra.finiteSquarefreeProduct P β := by
  simpa using
    InfoGeometry.Arithmetic.PrimeSuperalgebra.finiteFermionicSquarefreePartition_eq_product P β

/-- The prime Euler product equals `riemannZeta` in the convergence half-plane. -/
theorem primeEulerProduct_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹) = riemannZeta s := by
  simpa using InfoGeometry.Canonical.Arithmetic.zeta_euler_product_bridge (s := s) hs

end InfoGeometry.Canonical.GrandCanonicalPrimeEnsembleProofs
