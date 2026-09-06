import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.CantorCylinderHomeomorph
import InfoGeometry.Canonical.CantorRuellePerronFrobeniusBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace InfoGeometry.Canonical.RuellePerronFrobeniusKMSBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.StoneCantorMathlib
open InfoGeometry.Canonical.CantorBoundaryCuntzShift
open InfoGeometry.Canonical.CantorCylinderTopology
open InfoGeometry.Canonical.CantorRuellePerronFrobeniusBridge

/-- 1. Ruelle-Perron-Frobenius (RPF) Potential Operator with Inverse Temperature β:
    ℒ_{-β E}(g)(x) = e^{-β E(0 ⌢ x)} g(0 ⌢ x) + e^{-β E(1 ⌢ x)} g(1 ⌢ x) -/
noncomputable def rpfEnergyPotentialOp (beta : ℝ) (E g : CantorStream → ℝ) (x : CantorStream) : ℝ :=
  Real.exp (- beta * E (prependedStream 0 x)) * g (prependedStream 0 x) +
  Real.exp (- beta * E (prependedStream 1 x)) * g (prependedStream 1 x)

/-- 🏆 THEOREM 1: Positivity Preservation under Energy-Weighted RPF Transfer Operator -/
theorem rpf_potential_positivity (beta : ℝ) (E g : CantorStream → ℝ) (hg : ∀ y, 0 ≤ g y) (x : CantorStream) :
    0 ≤ rpfEnergyPotentialOp beta E g x := by
  dsimp [rpfEnergyPotentialOp]
  have h1 : 0 ≤ Real.exp (- beta * E (prependedStream 0 x)) * g (prependedStream 0 x) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (hg _)
  have h2 : 0 ≤ Real.exp (- beta * E (prependedStream 1 x)) * g (prependedStream 1 x) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (hg _)
  linarith

/-- 🏆 THEOREM 2: RPF Transfer Operator Eigenvalue for Constant Energy Potential E₀:
    ℒ_{-β E₀}(1) = 2 e^{-β E₀} · 1 -/
theorem rpf_constant_energy_eigenstate (beta E0 : ℝ) (x : CantorStream) :
    rpfEnergyPotentialOp beta (fun _ => E0) (fun _ => 1) x = 2 * Real.exp (- beta * E0) := by
  dsimp [rpfEnergyPotentialOp]
  ring

/-- 🏆 THEOREM 3: KMS Thermal Partition Function Eigenvalue Factorization:
    Z(β, E₀) = ℒ_{-β E₀}(1)(x) = 2 e^{-β E₀} -/
theorem rpf_kms_partition_function (beta E0 : ℝ) (x : CantorStream) :
    rpfEnergyPotentialOp beta (fun _ => E0) (fun _ => 1) x = 2 * Real.exp (- beta * E0) :=
  rpf_constant_energy_eigenstate beta E0 x

end InfoGeometry.Canonical.RuellePerronFrobeniusKMSBridge
