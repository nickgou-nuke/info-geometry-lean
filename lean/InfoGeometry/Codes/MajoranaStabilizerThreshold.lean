import InfoGeometry.Algebra.SupermatrixKoszul
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.KoszulFoundation
import InfoGeometry.Clifford.DiscreteMoebiusGroup
import InfoGeometry.Clifford.MonodromyFlowAdapter
import Mathlib.Analysis.Complex.Basic

noncomputable section

/-!
# MajoranaStabilizerThreshold

Fault-tolerance readout for a Majorana-style stabilizer threshold model.

The module deliberately treats the parabolic flow as an abelian accumulated
Dehn-twist/noise sector, not as a non-abelian braid generator.  Its job is to
extract the deterministic ceiling: repeated nilpotent shear perturbations
accumulate linearly.
-/

namespace InfoGeometry.Codes.MajoranaStabilizerThreshold

open Matrix
open Complex
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Clifford.MonodromyFlowAdapter

/-- A logical two-state Majorana code carrier. -/
abbrev MajoranaCodeSpace := InfoGeometry.Algebra.FiniteSpin.Vec2C

/-- Logical parity readout for the two-state carrier. -/
def fermionParityOperator : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/--
The protected error-flow step is exactly the LCFT parabolic flow already
verified in the logarithmic monodromy lane.
-/
def errorFlowStep (δ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  lcftParabolicFlowStep δ

/-- Composition of protected error-flow steps is additive in the shear budget. -/
theorem errorFlow_composition (δ₁ δ₂ : ℂ) :
    errorFlowStep δ₁ * errorFlowStep δ₂ = errorFlowStep (δ₁ + δ₂) := by
  exact lcftParabolicFlow_composition δ₁ δ₂

/-- Repeated identical perturbations accumulate as one perturbation of size `nδ`. -/
theorem error_threshold_linear_induction (δ : ℂ) (n : ℕ) :
    errorFlowStep δ ^ n = errorFlowStep ((n : ℂ) * δ) := by
  exact lcftParabolicFlow_pow δ n

/-- The accumulated off-diagonal shear after `n` operations is exactly `nδ`. -/
theorem majorana_accumulated_shear (δ : ℂ) (n : ℕ) :
    ((errorFlowStep δ) ^ n) 0 1 = (n : ℂ) * δ := by
  rw [error_threshold_linear_induction]
  simp [errorFlowStep, lcftParabolicFlowStep, infinitesimalNullGenerator,
    epsilon, jordanNilpotent]

/--
Norm-based threshold condition: if the deterministic noise budget
`n * ‖δ‖` is below the ceiling `Λ`, then the actual accumulated shear entry is
also below `Λ`.
-/
theorem threshold_condition (δ : ℂ) (n : ℕ) (Λ : ℝ)
    (h_budget : (n : ℝ) * ‖δ‖ ≤ Λ) :
    ‖(((errorFlowStep δ) ^ n) 0 1)‖ ≤ Λ := by
  rw [majorana_accumulated_shear, norm_mul]
  simpa using h_budget

/--
A deterministic analytic proxy for a logical-failure budget under a fixed
per-step real noise strength.
-/
def analyticalFailureBound (n : ℕ) (ε : ℝ) : ℝ :=
  (n : ℝ) * ε

/-- The proxy failure budget is linear in the number of operations. -/
theorem analyticalFailureBound_eq (n : ℕ) (ε : ℝ) :
    analyticalFailureBound n ε = (n : ℝ) * ε := rfl

/-- If the proxy budget is below threshold, the same scalar bound is available. -/
theorem analyticalFailureBound_le_threshold {n : ℕ} {ε Λ : ℝ}
    (h_budget : analyticalFailureBound n ε ≤ Λ) :
    (n : ℝ) * ε ≤ Λ := by
  simpa [analyticalFailureBound] using h_budget

/-- Real-part dephasing drift is also strictly linear. -/
theorem dephasing_drift_is_linear (δ : ℂ) (n : ℕ) :
    (((errorFlowStep δ) ^ n) 0 1).re = (n : ℝ) * δ.re := by
  rw [majorana_accumulated_shear]
  simp

/--
Dimension-free square-zero unipotent power law.

This is the ring-only version of the protection mechanism: it uses no matrix
dimension and no scalar field action.  The coefficient is therefore the natural
additive multiple `n • x`; specialized matrix/algebra lanes can rewrite that
multiple as real or complex scalar multiplication when the relevant scalar
structure is present.
-/
theorem square_zero_unipotent_pow {A : Type _} [Ring A] {x : A}
    (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n • x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hnx : (n • x) * x = 0 := by
        rw [nsmul_eq_mul, mul_assoc, hx, mul_zero]
      rw [pow_succ, ih]
      calc
        (1 + n • x) * (1 + x) = 1 + n • x + (x + (n • x) * x) := by
          rw [mul_add, mul_one, add_mul, one_mul]
        _ = 1 + n • x + x := by
          rw [hnx, add_zero]
        _ = 1 + (n • x + x) := by
          rw [add_assoc]
        _ = 1 + (Nat.succ n) • x := by
          rw [succ_nsmul]

end InfoGeometry.Codes.MajoranaStabilizerThreshold
