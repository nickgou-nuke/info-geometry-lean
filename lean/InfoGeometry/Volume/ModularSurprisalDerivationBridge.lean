import InfoGeometry.Volume.ConnesInfinitesimal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Information.ExpLogRadonNikodymDerivationBridge
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Relative modular surprisal and derivation-exponential flow

This file records the common generator pattern used by the scalar
Radon--Nikodym and operatorial modular lanes.  The scalar relative surprisal
uses the convention `K = -log Δ`; the operatorial flow is conjugation by the
exponential of its generator.
-/

noncomputable section

namespace InfoGeometry.Volume.ModularSurprisalDerivationBridge

open InfoGeometry.Volume.ConnesInfinitesimal
open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Information.ExpLogRadonNikodymDerivationBridge

/-! ## Scalar relative modular surprisal -/

/-- Relative surprisal associated with a positive scalar RN ratio `rho / sigma`. -/
def relativeModularSurprisal (rho sigma : ℝ) : ℝ :=
  -Real.log (rho / sigma)

theorem relativeModularSurprisal_eq_neg_log_rn (rho sigma : ℝ) :
    relativeModularSurprisal rho sigma = -Real.log (rho / sigma) := rfl

/-- The surprisal of an exponential RN path has constant velocity `-v`. -/
theorem hasDerivAt_relativeModularSurprisal_exp_tilting
    (rho0 v t : ℝ) (h_pos : 0 < rho0) :
    HasDerivAt
      (fun s => relativeModularSurprisal (rho0 * Real.exp (s * v)) 1)
      (-v) t := by
  have h_log :=
    hasDerivAt_log_exp_tilting rho0 v t h_pos
  simpa [relativeModularSurprisal] using h_log.neg

/-! ## Operatorial modular generator -/

/-- The relative modular operator supplies the modular Hamiltonian by `K=-log Δ`.

This is an interface theorem: once an operator `K` has been obtained from a
logarithmic RN construction, its observable flow is the commutator flow below.
-/
theorem modular_flow_generator_is_commutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (K A : AlgebraEnd H) :
    HasDerivAt
      (fun t : ℝ => modularHamiltonianAction (H := H) K A t)
      ⁅K, A⁆ 0 := by
  exact modularHamiltonianAction_hasDerivAt_zero (H := H) K A

/-! ## The two exponentials have the same abstract shape -/

/-- Exponential tilting linearizes the scalar RN potential. -/
theorem rn_log_generator_at_zero
    (rho0 v : ℝ) (h_pos : 0 < rho0) :
    deriv (fun s => Real.log (rho0 * Real.exp (s * v))) 0 = v := by
  exact deriv_log_exp_tilting_zero rho0 v h_pos

end InfoGeometry.Volume.ModularSurprisalDerivationBridge

namespace InfoGeometry.Volume.NoncommutativeRNDerivative

/-! ## The genuinely noncommutative cocycle law -/

variable {A : Type*} [Ring A]

/-- Left logarithmic derivative of a unit in a possibly noncommutative algebra. -/
def noncommDlog (D : A → A) (u : Aˣ) : A :=
  (↑u⁻¹ : A) * D (u : A)

/--
The noncommutative replacement for additive `dlog`:

`dlog(uv) = v⁻¹ dlog(u) v + dlog(v)`.

The conjugation term is essential; it disappears only under suitable
commutation hypotheses.
-/
theorem noncommDlog_mul (D : A → A)
    (hLeibniz : ∀ x y : A, D (x * y) = D x * y + x * D y)
    (u v : Aˣ) :
    noncommDlog D (u * v) =
      (↑v⁻¹ : A) * noncommDlog D u * (v : A) + noncommDlog D v := by
  have hunit : (↑(u * v)⁻¹ : A) = (↑v⁻¹ : A) * (↑u⁻¹ : A) := by
    rw [mul_inv_rev, Units.val_mul]
  have hu : (↑u⁻¹ : A) * (↑u : A) = 1 := Units.inv_mul u
  dsimp [noncommDlog]
  rw [hunit, hLeibniz (u : A) (v : A)]
  calc
    (↑v⁻¹ * ↑u⁻¹) * (D ↑u * ↑v + ↑u * D ↑v)
        = (↑v⁻¹ * ↑u⁻¹ * (D ↑u * ↑v)) + (↑v⁻¹ * ↑u⁻¹ * (↑u * D ↑v)) := by
          rw [mul_add]
      _ = (↑v⁻¹ * (↑u⁻¹ * D ↑u) * ↑v) + (↑v⁻¹ * (((↑u⁻¹ : A) * (↑u : A)) * D ↑v)) := by
          simp only [mul_assoc]
      _ = (↑v⁻¹ * (↑u⁻¹ * D ↑u) * ↑v) + (↑v⁻¹ * (1 * D ↑v)) := by
          rw [hu]
      _ = ↑v⁻¹ * (↑u⁻¹ * D ↑u) * ↑v + ↑v⁻¹ * D ↑v := by
          rw [one_mul]

end InfoGeometry.Volume.NoncommutativeRNDerivative
