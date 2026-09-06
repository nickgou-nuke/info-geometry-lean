import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Spectral.WeilPositivityGNSBridge

/-!
# Finite Weil positivity kernels and GNS source boundary

This owner contains only finite algebraic statements.  The spectral energy and
prime-power comb are finite sums, while the global Weil criterion is represented
by an explicit typed source structure.  No analytic continuation, zero trace,
or RH equivalence is inferred from these finite shadows.
-/

noncomputable section

namespace InfoGeometry.WeilPositivity

open Complex

/-! ## Finite spectral energy kernel -/

structure SpectralEvaluation where
  eval : ℝ → ℂ

def finiteSpectralEnergy (ordinates : List ℝ) (f : SpectralEvaluation) : ℝ :=
  (ordinates.map (fun γ => ‖f.eval γ‖ ^ 2)).sum

theorem finiteSpectralEnergy_nonneg (ordinates : List ℝ) (f : SpectralEvaluation) :
    0 ≤ finiteSpectralEnergy ordinates f := by
  dsimp [finiteSpectralEnergy]
  induction ordinates with
  | nil => simp
  | cons γ rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (sq_nonneg _) ih

@[simp]
theorem finiteSpectralEnergy_zero (ordinates : List ℝ) :
    finiteSpectralEnergy ordinates ⟨fun _ => 0⟩ = 0 := by
  dsimp [finiteSpectralEnergy]
  induction ordinates with
  | nil => simp
  | cons γ rest ih =>
      simpa [List.map_cons, List.sum_cons] using ih

/-! ## Finite arithmetic prime comb -/

structure PrimePowerData where
  prime : ℕ
  power : ℕ
  logPrime : ℝ
  weight : ℝ

def finitePrimeComb (entries : List PrimePowerData) (f : ℝ → ℝ) : ℝ :=
  (entries.map (fun p =>
    p.weight * (f (p.power * p.logPrime) +
      f (-(p.power * p.logPrime))))).sum

theorem finitePrimeComb_add (entries : List PrimePowerData) (f g : ℝ → ℝ) :
    finitePrimeComb entries (fun x => f x + g x) =
      finitePrimeComb entries f + finitePrimeComb entries g := by
  induction entries with
  | nil => simp [finitePrimeComb]
  | cons p entries ih =>
      simp [finitePrimeComb, ih, add_mul, mul_add, add_assoc, add_left_comm,
        add_comm]

/-! ## Native quadratic positivity -/

theorem quadratic_readout_nonneg
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (weilFunctional : A →ₗ[ℝ] ℝ)
    (h_positive : ∀ a : A, 0 ≤ weilFunctional (star a * a))
    (a : A) :
    0 ≤ weilFunctional (star a * a) :=
  h_positive a

end InfoGeometry.WeilPositivity

end noncomputable section
