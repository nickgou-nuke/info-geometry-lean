import Mathlib.RingTheory.Derivation.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Probability.DerivationBridge
import Mathlib.Tactic

namespace InfoGeometry.Information.ExpLogRadonNikodymDerivationBridge

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The algebraic logarithmic derivative of an invertible element (unit) with respect to a derivation `D`. -/
def dlog (D : Derivation R A A) (u : Aˣ) : A :=
  (↑u⁻¹ : A) * D (u : A)

/-- Derivation of the inverse of a unit in a commutative algebra:
    `D(u⁻¹) = - (u⁻¹)² * D(u)`. Wired to the canonical owner lemma via
    `InfoGeometry.Probability.DerivationBridge.derivation_inv_comm_ofMathlib`. -/
theorem derivation_unit_inv (D : Derivation R A A) (u : Aˣ) :
    D (↑u⁻¹ : A) = - ((↑u⁻¹ : A) ^ 2) * D (u : A) :=
  InfoGeometry.Probability.DerivationBridge.derivation_inv_comm_ofMathlib D u

/-- 🏆 THEOREM: The Logarithmic Derivative is a Group Homomorphism on Units:
    `dlog_D(u * v) = dlog_D(u) + dlog_D(v)`.
    This algebraically converts multiplicative Radon–Nikodym cocycles into additive potentials. -/
theorem dlog_mul (D : Derivation R A A) (u v : Aˣ) :
    dlog D (u * v) = dlog D u + dlog D v := by
  dsimp [dlog]
  have h_leib := D.leibniz (u : A) (v : A)
  simp only [smul_eq_mul] at h_leib
  have h_inv : (↑(u * v)⁻¹ : A) = (↑u⁻¹ : A) * (↑v⁻¹ : A) := by
    rw [mul_inv, Units.val_mul, mul_comm]
  rw [h_inv, h_leib]
  have h_u : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  have h_v : (↑v⁻¹ : A) * (v : A) = 1 := Units.inv_mul v
  calc
    (↑u⁻¹ * ↑v⁻¹) * (↑u * D ↑v + ↑v * D ↑u)
        = (↑u⁻¹ * ↑u) * (↑v⁻¹ * D ↑v) + (↑v⁻¹ * ↑v) * (↑u⁻¹ * D ↑u) := by ring
      _ = 1 * (↑v⁻¹ * D ↑v) + 1 * (↑u⁻¹ * D ↑u) := by rw [h_u, h_v]
      _ = ↑u⁻¹ * D ↑u + ↑v⁻¹ * D ↑v := by ring

/-- 🏆 THEOREM: Logarithmic Derivative Cocycle Inversion:
    `dlog_D(u⁻¹) = - dlog_D(u)`. -/
theorem dlog_inv (D : Derivation R A A) (u : Aˣ) :
    dlog D u⁻¹ = - dlog D u := by
  dsimp [dlog]
  have h_u_inv : (u⁻¹ : Aˣ)⁻¹ = u := inv_inv u
  rw [h_u_inv, derivation_unit_inv]
  have h_ui : (u : A) * (↑u⁻¹ : A) ^ 2 = (↑u⁻¹ : A) := by
    calc (u : A) * (↑u⁻¹ : A) ^ 2 = ((u : A) * (↑u⁻¹ : A)) * (↑u⁻¹ : A) := by ring
      _ = 1 * (↑u⁻¹ : A) := by rw [Units.mul_inv u]
      _ = (↑u⁻¹ : A) := by rw [one_mul]
  calc
    (u : A) * (-((↑u⁻¹ : A) ^ 2) * D (u : A))
        = - ((u : A) * (↑u⁻¹ : A) ^ 2 * D (u : A)) := by ring
      _ = - ((↑u⁻¹ : A) * D (u : A)) := by rw [h_ui]

/-- Logarithmic derivative of identity is zero. -/
@[simp]
theorem dlog_one (D : Derivation R A A) :
    dlog D 1 = 0 := by
  dsimp [dlog]
  simp

/-- Powers in the logarithmic derivative scale linearly: `dlog_D(u^n) = n • dlog_D(u)`. -/
theorem dlog_pow (D : Derivation R A A) (u : Aˣ) (n : ℕ) :
    dlog D (u ^ n) = n • dlog D u := by
  induction n with
  | zero =>
    simp [dlog_one]
  | succ n ih =>
    rw [pow_succ, dlog_mul, ih, succ_nsmul, add_comm]

/-!
=============================================================================
PART 2: Smooth Analysis & Exponential Flow of the Radon–Nikodym Derivative
=============================================================================
-/

/-- 🏆 THEOREM: The Infinitesimal Logarithmic Derivative of a Smooth Density Curve:
    `d/dt [log ρ(t)] = ρ'(t) / ρ(t)`. -/
theorem hasDerivAt_log_density
    (rho : ℝ → ℝ) (rho' : ℝ) (t : ℝ)
    (h_diff : HasDerivAt rho rho' t)
    (h_pos : 0 < rho t) :
    HasDerivAt (fun s => Real.log (rho s)) (rho' / rho t) t := by
  exact HasDerivAt.log h_diff (ne_of_gt h_pos)

/-- 🏆 THEOREM: Exponential Flow of the Radon–Nikodym Derivative:
    For an exponential tilting `ρ(t) = ρ₀ * exp(t * v)` with `0 < ρ₀`,
    the logarithmic derivative (score function) is identically the velocity generator `v`:
    `d/dt [log (ρ₀ * exp(t * v))] = v`. -/
theorem hasDerivAt_log_exp_tilting
    (rho0 v t : ℝ) (h_pos : 0 < rho0) :
    HasDerivAt (fun s => Real.log (rho0 * Real.exp (s * v))) v t := by
  have h_log_split : (fun s => Real.log (rho0 * Real.exp (s * v))) = (fun s => Real.log rho0 + s * v) := by
    ext s
    rw [Real.log_mul (ne_of_gt h_pos) (ne_of_gt (Real.exp_pos (s * v))), Real.log_exp]
  rw [h_log_split]
  have h_const : HasDerivAt (fun _ : ℝ => Real.log rho0) 0 t := hasDerivAt_const t (Real.log rho0)
  have h_lin : HasDerivAt (fun s => s * v) v t := by
    have h_id := (hasDerivAt_id t).mul_const v
    simpa using h_id
  have h_add := h_const.add h_lin
  rw [zero_add] at h_add
  exact h_add

/-- The score derivative for an exponential family at time zero is exactly the generator. -/
theorem deriv_log_exp_tilting_zero
    (rho0 v : ℝ) (h_pos : 0 < rho0) :
    deriv (fun s => Real.log (rho0 * Real.exp (s * v))) 0 = v := by
  exact (hasDerivAt_log_exp_tilting rho0 v 0 h_pos).deriv

/-- 🏆 THEOREM: Product Rule for Logarithmic Density Curves:
    `d/dt [log(ρ₁(t) * ρ₂(t))] = ρ₁'(t)/ρ₁(t) + ρ₂'(t)/ρ₂(t)`. -/
theorem hasDerivAt_log_density_mul
    (rho1 rho2 : ℝ → ℝ) (rho1' rho2' : ℝ) (t : ℝ)
    (h_diff1 : HasDerivAt rho1 rho1' t)
    (h_diff2 : HasDerivAt rho2 rho2' t)
    (h_pos1 : 0 < rho1 t)
    (h_pos2 : 0 < rho2 t) :
    HasDerivAt (fun s => Real.log (rho1 s * rho2 s)) (rho1' / rho1 t + rho2' / rho2 t) t := by
  have h_mul_diff : HasDerivAt (fun s => rho1 s * rho2 s) (rho1' * rho2 t + rho1 t * rho2') t :=
    h_diff1.mul h_diff2
  have h_mul_pos : 0 < rho1 t * rho2 t := mul_pos h_pos1 h_pos2
  have h_log := HasDerivAt.log h_mul_diff (ne_of_gt h_mul_pos)
  have h_alg : (rho1' * rho2 t + rho1 t * rho2') / (rho1 t * rho2 t) = rho1' / rho1 t + rho2' / rho2 t := by
    have h1 : rho1 t ≠ 0 := ne_of_gt h_pos1
    have h2 : rho2 t ≠ 0 := ne_of_gt h_pos2
    field_simp
  rw [h_alg] at h_log
  exact h_log

/-- 🏆 THEOREM: Score Energy and Fisher Information Metric Element:
    The squared logarithmic derivative matches the Fisher–Rao metric density element:
    `ρ(t) * (d/dt log ρ(t))² = (ρ'(t))² / ρ(t)`. -/
theorem fisher_score_energy_eq
    (rho_val rho' : ℝ) (h_pos : 0 < rho_val) :
    let score := rho' / rho_val
    rho_val * (score ^ 2) = (rho' ^ 2) / rho_val := by
  dsimp
  have h_ne : rho_val ≠ 0 := ne_of_gt h_pos
  field_simp

end InfoGeometry.Information.ExpLogRadonNikodymDerivationBridge
