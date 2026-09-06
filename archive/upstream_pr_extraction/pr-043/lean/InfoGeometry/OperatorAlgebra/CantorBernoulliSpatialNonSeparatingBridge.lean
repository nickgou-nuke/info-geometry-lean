import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge

/-!
# Non-Faithfulness of the Spatial Bernoulli State & Non-Separating Vacuum

This bridge establishes the fundamental representation-theoretic firewall
between the spatial Bernoulli representation and the canonical KMS/gauge representation:
$$\boxed{\begin{array}{ccc}
\textbf{Spatial State } \omega_{\mathrm{sp}} & \longleftrightarrow & \textbf{Gauge/KMS State } \varphi \\
\text{Cyclic, but NOT separating} & & \text{Cyclic by GNS} \\
\text{Non-faithful: } \exists A \neq 0, \omega(A^\dagger A) = 0 & & \text{Separating only after a faithfulness theorem}
\end{array}}$$

The KMS label alone does not provide faithfulness or separatingness; those are
separate properties of the state and representation.

## Key Theorems Proved:
1. `spatialAnnihilator`: The operator $A_{\mathrm{ann}} = V_0^\dagger - V_1^\dagger \in \mathcal{B}(L^2(\mathcal{C}, \mu_C))$.
2. `spatialAnnihilator_vacuum_eq_zero`: $A_{\mathrm{ann}} \Omega = 0$.
3. `spatialAnnihilator_apply_vLeft_vacuum`: $A_{\mathrm{ann}} (V_0 \Omega) = \Omega \neq 0$.
4. `spatialAnnihilator_ne_zero`: $A_{\mathrm{ann}} \neq 0$.
5. `spatialState_star_annihilator_mul_self_eq_zero`: $\omega_{\mathrm{sp}}(A_{\mathrm{ann}}^\dagger A_{\mathrm{ann}}) = 0$.
6. `spatialState_not_faithful_witness`: Formal kernel-level witness that $\omega_{\mathrm{sp}}$ is not faithful.
-/

noncomputable section

open Complex
open ContinuousLinearMap
open MeasureTheory
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNonSeparatingBridge

/-- The spatial annihilator operator $A_{\mathrm{ann}} = V_0^\dagger - V_1^\dagger \in \mathcal{B}(L^2)$. -/
def spatialAnnihilator : L2Boundary →L[ℂ] L2Boundary :=
  (star vLeft) - (star vRight)

theorem vacuumL2_comp_prependBit (b : Bool) :
    (fun x => (vacuumL2 : Boundary → ℂ) (Canonical.CuntzCantorBoundaryShift.prependBit b x)) =ᵐ[μC]
      fun _ => (1 : ℂ) := by
  have hac : prependBitBranchProductMeasure b ≪ μC := by
    rw [← prependBit_measure_map_eq_branchProductMeasure b,
        prependBit_measure_map_eq_two_restrict_branch b]
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    have h_restr : μC.restrict (Set.range (Canonical.CuntzCantorBoundaryShift.prependBit b)) s ≤ μC s :=
      Measure.restrict_le_self s
    rw [hs] at h_restr
    have hzero : μC.restrict (Set.range (Canonical.CuntzCantorBoundaryShift.prependBit b)) s = 0 :=
      nonpos_iff_eq_zero.mp h_restr
    rw [hzero, mul_zero]
  have hvac_branch : (vacuumL2 : Boundary → ℂ) =ᵐ[prependBitBranchProductMeasure b] fun _ => 1 :=
    hac.ae_le vacuumL2_coeFn
  have hcomp := hvac_branch.comp_tendsto
    (prependBitMeasurePreserving b).quasiMeasurePreserving.tendsto_ae
  exact hcomp

/-- 🏆 THEOREM 1: $A_{\mathrm{ann}}$ annihilates the spatial vacuum vector $\Omega = \mathbf{1}$. -/
theorem spatialAnnihilator_vacuum_eq_zero :
    spatialAnnihilator vacuumL2 = 0 := by
  dsimp [spatialAnnihilator]
  have hLeft : (star vLeft) vacuumL2 = (prependBitLpNormFactor : ℂ) • prependBitLp false vacuumL2 :=
    normalizedPrependBitLpAdjoint_apply false vacuumL2
  have hRight : (star vRight) vacuumL2 = (prependBitLpNormFactor : ℂ) • prependBitLp true vacuumL2 :=
    normalizedPrependBitLpAdjoint_apply true vacuumL2
  have h_const_left : prependBitLp false vacuumL2 = prependBitLp true vacuumL2 := by
    apply MeasureTheory.Lp.ext
    have h0 := (prependBitFunction_memLp false vacuumL2).coeFn_toLp
    have h1 := (prependBitFunction_memLp true vacuumL2).coeFn_toLp
    dsimp [prependBitLp]
    have hF := vacuumL2_comp_prependBit false
    have hT := vacuumL2_comp_prependBit true
    filter_upwards [h0, h1, hF, hT] with x h0x h1x hFx hTx
    rw [h0x, h1x]
    dsimp [prependBitFunction]
    rw [hFx, hTx]
  rw [hLeft, hRight, h_const_left, sub_self]

/-- 🏆 THEOREM 2: $A_{\mathrm{ann}} (V_0 \Omega) = \Omega$. -/
theorem spatialAnnihilator_apply_vLeft_vacuum :
    spatialAnnihilator (vLeft vacuumL2) = vacuumL2 := by
  dsimp [spatialAnnihilator]
  have h_self : (star vLeft) (vLeft vacuumL2) = vacuumL2 := by
    exact ContinuousLinearMap.ext_iff.mp vLeft_adjoint_comp_vLeft vacuumL2
  have h_cross : (star vRight) (vLeft vacuumL2) = 0 := by
    have h0 := ContinuousLinearMap.ext_iff.mp
      (normalizedPrependBitLpAdjoint_comp_cross_eq_zero (show (true : Bool) ≠ false by decide)) vacuumL2
    exact h0
  rw [h_self, h_cross, sub_zero]

/-- 🏆 THEOREM 3: The annihilator $A_{\mathrm{ann}}$ is strictly nonzero. -/
theorem spatialAnnihilator_ne_zero :
    spatialAnnihilator ≠ 0 := by
  intro hz
  have h_apply : spatialAnnihilator (vLeft vacuumL2) = 0 := by
    rw [hz]
    rfl
  rw [spatialAnnihilator_apply_vLeft_vacuum] at h_apply
  have h_sq := vacuumL2_inner_self
  have h_zero : inner ℂ vacuumL2 vacuumL2 = 0 := by
    rw [h_apply, inner_zero_left]
  rw [h_zero] at h_sq
  exact zero_ne_one h_sq

/-- 🏆 THEOREM 4: Expectation of $A_{\mathrm{ann}}^\dagger A_{\mathrm{ann}}$ in the spatial state vanishes. -/
theorem spatialState_star_annihilator_mul_self_eq_zero :
    spatialPositiveFunctional (star spatialAnnihilator * spatialAnnihilator) = 0 := by
  dsimp [spatialPositiveFunctional, spatialFunctional]
  have h_adj := ContinuousLinearMap.adjoint_inner_right spatialAnnihilator vacuumL2 (spatialAnnihilator vacuumL2)
  change inner ℂ vacuumL2 ((ContinuousLinearMap.adjoint spatialAnnihilator) (spatialAnnihilator vacuumL2)) = 0
  rw [h_adj]
  have h_ann := spatialAnnihilator_vacuum_eq_zero
  rw [h_ann, inner_zero_right]

/-- 🏆 THEOREM 5: Formal Witness for Non-Faithfulness of the Spatial Bernoulli Functional. -/
theorem spatialState_not_faithful_witness :
    spatialAnnihilator ≠ 0 ∧
    spatialPositiveFunctional (star spatialAnnihilator * spatialAnnihilator) = 0 :=
  ⟨spatialAnnihilator_ne_zero, spatialState_star_annihilator_mul_self_eq_zero⟩

end InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNonSeparatingBridge
