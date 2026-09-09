import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.Algebra.CuntzModularAutomorphism
import InfoGeometry.Algebra.CuntzKMSCondition
import InfoGeometry.Algebra.CuntzKMSState

/-!
# Cantor Bernoulli Spatial Modular-Weight Readout

This file records concrete generator-level modular-weight readouts for the
Bernoulli Cuntz operators on $L^2(\mathcal{C}, \mu_C)$.  It does not claim a
Tomita--Takesaki construction or a full C*-algebraic KMS state on the operator
closure; those require the conditional-expectation/GNS completion layer.

## Mathematical Blueprint

1. **Spatial vector functional**: The constant 1 function on the Cantor space is in
   $L^2(\mu_C)$ with unit norm, inducing the spatial functional
   $\omega(A) = \langle 1, A 1 \rangle$.  This is not asserted to be the
   canonical gauge-KMS state or a faithful Tomita vector.
2. **Generator scaling readout**: The algebraic scalar modular-weight law
   $\sigma_z(V_b) = 2^{iz} V_b$ and $\sigma_z(V_b^\dagger) = 2^{-iz} V_b^\dagger$.
3. **Cylinder invariance**: Proves that cylinder projections are invariant under
   the corresponding scalar factors for all complex times $z \in \mathbb{C}$.
4. **Critical finite weights**: Proves that the parameter $\beta = 1$
   (corresponding numerically to $\beta_{\mathrm{phys}} = \ln 2$) yields the exact Boltzmann weights
   $2^{-\beta} = 1/2$ and the binary two-mode sum is $1$.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliKMSState

open MeasureTheory
open Complex
open ContinuousLinearMap
open InfoGeometry.Analysis.FractalMeasure.Basic
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.Algebra.CuntzKMSCondition
open InfoGeometry.Algebra.CuntzKMSState

abbrev BoundedL2Operator := InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.BoundedL2Operator

/-- The constant 1 function is square-integrable with respect to the probability measure μC. -/
theorem vacuum_memLp : MemLp (fun _ : Boundary => (1 : ℂ)) 2 μC :=
  memLp_const (1 : ℂ)

/-- The canonical vacuum state vector 1 ∈ L²(Boundary, μC). -/
def vacuum : L2Boundary :=
  vacuum_memLp.toLp (fun _ => 1)

/-- The vacuum state functional ω(A) = ⟪1, A 1⟫ on bounded boundary operators. -/
def vacuumState (A : BoundedL2Operator) : ℂ :=
  inner ℂ vacuum (A vacuum)

/-- Complex-time modular scaling factor for the binary alphabet (p = 2). -/
def binaryModularFactor (z : ℂ) : ℂ :=
  modularPhaseComplex 2 z

/-- Inverse complex-time modular scaling factor. -/
def binaryModularFactorInv (z : ℂ) : ℂ :=
  modularPhaseComplexInv 2 z

/-- Complex-time modular flow on generator V_b: σ_z(V_b) = 2^{iz} V_b. -/
def modularFlowGen (z : ℂ) (b : Bool) : BoundedL2Operator :=
  binaryModularFactor z • InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.branchOperator b

/-- Complex-time modular flow on adjoint generator V_b†: σ_z(V_b†) = 2^{-iz} V_b†. -/
def modularFlowGenDag (z : ℂ) (b : Bool) : BoundedL2Operator :=
  binaryModularFactorInv z • star (InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.branchOperator b)

/-- At z = 0, the modular flow is the identity on generators. -/
theorem modularFlowGen_zero (b : Bool) :
    modularFlowGen 0 b = InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.branchOperator b := by
  dsimp [modularFlowGen, binaryModularFactor, modularPhaseComplex]
  simp

/-- The modular flow satisfies the additive one-parameter group law. -/
theorem modularFlowGen_add (z w : ℂ) (b : Bool) :
    modularFlowGen (z + w) b =
      binaryModularFactor z • modularFlowGen w b := by
  dsimp [modularFlowGen, binaryModularFactor]
  rw [InfoGeometry.Algebra.CuntzKMSCondition.modularPhaseComplex_add, mul_smul]

/-- Cylinder projection P_b = V_b V_b† is strictly invariant under modular flow for all z ∈ ℂ. -/
theorem modularFlow_projection_invariant (z : ℂ) (b : Bool) :
    (modularFlowGen z b).comp (modularFlowGenDag z b) =
      InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorCylinderProjection [b] := by
  dsimp [modularFlowGen, modularFlowGenDag,
    InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorCylinderProjection,
    InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWord,
    InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge.operatorWordDag]
  simp only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_smul, smul_smul]
  have hmul : binaryModularFactor z * binaryModularFactorInv z = 1 :=
    InfoGeometry.Algebra.CuntzKMSCondition.modularPhaseComplex_mul_inv 2 z
  rw [hmul, one_smul]

/-- The Boltzmann factor at critical parameter β = 1 is 1/2. -/
theorem binary_kms_boltzmann_weight_at_one :
    boltzmannFactor 2 (1 : ℂ) = (1 / 2 : ℂ) := by
  dsimp [boltzmannFactor]
  rw [Complex.cpow_neg_one]
  ring

/-- The binary mode partition sum at critical parameter β = 1 is exactly 1. -/
theorem binary_kms_partition_at_critical_temp :
    (boltzmannFactor 2 (1 : ℂ)) + (boltzmannFactor 2 (1 : ℂ)) = 1 := by
  rw [binary_kms_boltzmann_weight_at_one]
  ring

/-- Normalized KMS weights for both binary branches false and true equal 1/2. -/
theorem binary_kms_weights :
    boltzmannFactor 2 (1 : ℂ) / ((boltzmannFactor 2 (1 : ℂ)) + (boltzmannFactor 2 (1 : ℂ))) = (1 / 2 : ℂ) := by
  rw [binary_kms_boltzmann_weight_at_one]
  ring

/-- At imaginary time i·β with β = 1, the modular phase scales generators by 1/2 on adjoints. -/
theorem modularFlow_imaginary_generator_scaling :
    modularPhaseComplex 2 (-(I * (1 : ℂ))) = (2 : ℂ) := by
  have himag := modularPhaseComplex_neg_imag 2 (by decide) 1
  simpa using himag

end InfoGeometry.OperatorAlgebra.CantorBernoulliKMSState
