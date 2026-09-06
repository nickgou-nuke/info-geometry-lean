import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.CantorCylinderHomeomorph
import InfoGeometry.Canonical.CantorColimitProjectiveBoundaryBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace InfoGeometry.Canonical.CantorRuellePerronFrobeniusBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.StoneCantorMathlib
open InfoGeometry.Canonical.CantorBoundaryCuntzShift
open InfoGeometry.Canonical.CantorCylinderTopology
open InfoGeometry.Canonical.CantorColimitProjectiveBoundaryBridge

/-- 1. Preimage Extensions of a Cantor Stream under the Bernoulli Shift Operator σ:
    (0 ⌢ x) and (1 ⌢ x) -/
def prependedStream (b : Fin 2) (x : CantorStream) : CantorStream :=
  fun k => if k = 0 then b else x (k - 1)

/-- 2. Ruelle-Perron-Frobenius (RPF) Transfer Operator ℒ_f(g)(x) = ∑_{y: σ(y)=x} e^{f(y)} g(y) -/
noncomputable def ruellePerronFrobeniusOp (f g : CantorStream → ℝ) (x : CantorStream) : ℝ :=
  Real.exp (f (prependedStream 0 x)) * g (prependedStream 0 x) +
  Real.exp (f (prependedStream 1 x)) * g (prependedStream 1 x)

/-- 🏆 THEOREM 1: Positivity Preservation under RPF Transfer Operator: g ≥ 0 ⇒ ℒ_f(g) ≥ 0 -/
theorem rpf_operator_positivity (f g : CantorStream → ℝ) (hg : ∀ y, 0 ≤ g y) (x : CantorStream) :
    0 ≤ ruellePerronFrobeniusOp f g x := by
  dsimp [ruellePerronFrobeniusOp]
  have h1 : 0 ≤ Real.exp (f (prependedStream 0 x)) * g (prependedStream 0 x) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (hg _)
  have h2 : 0 ≤ Real.exp (f (prependedStream 1 x)) * g (prependedStream 1 x) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (hg _)
  linarith

theorem rpf_operator_add (f g h : CantorStream → ℝ) (x : CantorStream) :
    ruellePerronFrobeniusOp f (fun y => g y + h y) x =
      ruellePerronFrobeniusOp f g x + ruellePerronFrobeniusOp f h x := by
  dsimp [ruellePerronFrobeniusOp]
  ring

theorem rpf_operator_smul (f : CantorStream → ℝ) (c : ℝ)
    (g : CantorStream → ℝ) (x : CantorStream) :
    ruellePerronFrobeniusOp f (fun y => c * g y) x =
      c * ruellePerronFrobeniusOp f g x := by
  dsimp [ruellePerronFrobeniusOp]
  ring

/-- 🏆 THEOREM 2: Shift Preimage Involution Identity: σ(b ⌢ x) = x -/
theorem shift_prependedStream (b : Fin 2) (x : CantorStream) :
    cantorShiftMap (prependedStream b x) = x := by
  ext k
  simp [cantorShiftMap, prependedStream]

/-- 🏆 THEOREM 3: Unweighted RPF Transfer Operator Fixed-Point Eigenstate:
    ℒ₀(1) = 2 · 1 -/
theorem rpf_bernoulli_eigenstate (x : CantorStream) :
    ruellePerronFrobeniusOp (fun _ => 0) (fun _ => 1) x = 2 := by
  dsimp [ruellePerronFrobeniusOp]
  rw [Real.exp_zero]
  ring

end InfoGeometry.Canonical.CantorRuellePerronFrobeniusBridge
