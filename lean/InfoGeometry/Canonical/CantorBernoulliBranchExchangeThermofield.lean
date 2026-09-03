import Mathlib.Tactic
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
import InfoGeometry.Canonical.SpinorCantorL2ConcreteIntertwiner
import InfoGeometry.Canonical.ThermofieldMobiusResonator
import InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner

/-
# Cantor branch exchange and the twin thermofield carrier

The binary Bernoulli boundary already has a concrete Hilbert carrier
L2Boundary = Lp ℂ 2 μC and a normalized Cuntz pair vLeft, vRight.
This file adds the missing finite-channel operator layer on top of those
owners.

The exchange operator is
  vLeft vRight† + vRight vLeft†.
It is proved to exchange the two first-level branch vectors, to square to the
identity on the full concrete L2 carrier, and to intertwine the effective
two-channel generator with its Cantor-boundary realization.

No new Cantor space, measure, completion, O₂ automorphism, or ODE theorem is
introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliBranchExchangeThermofield

open Complex
open ContinuousLinearMap
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.Canonical.SpinorCantorL2ConcreteIntertwiner
open InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge
open InfoGeometry.Canonical.ThermofieldBidirectionalResonator
open InfoGeometry.Canonical.ThermofieldMobiusResonator

/-- The already existing concrete Cantor L2 carrier. -/
abbrev L2Carrier := L2Boundary

/-- The already existing bounded-operator carrier on Cantor L2. -/
abbrev BoundaryOperator := BoundedL2Operator

/-- The first-level Cuntz branch-exchange operator
V_L V_R† + V_R V_L†. -/
def branchExchangeOp : BoundaryOperator :=
  vLeft.comp (normalizedPrependBitLpAdjoint true) +
    vRight.comp (normalizedPrependBitLpAdjoint false)

/-- The exchange operator sends the left first-level branch vector to the
right first-level branch vector. -/
theorem branchExchangeOp_apply_branchVector_false :
    branchExchangeOp (branchVector false) = branchVector true := by
  have hcross :
      normalizedPrependBitLpAdjoint true (vLeft vacuumL2) = 0 := by
    exact ContinuousLinearMap.ext_iff.mp vRight_adjoint_comp_vLeft vacuumL2
  have hself :
      normalizedPrependBitLpAdjoint false (vLeft vacuumL2) = vacuumL2 := by
    exact ContinuousLinearMap.ext_iff.mp vLeft_adjoint_comp_vLeft vacuumL2
  change
    vLeft (normalizedPrependBitLpAdjoint true (vLeft vacuumL2)) +
        vRight (normalizedPrependBitLpAdjoint false (vLeft vacuumL2)) =
      vRight vacuumL2
  rw [hcross, map_zero, hself]
  simp

/-- The exchange operator sends the right first-level branch vector to the
left first-level branch vector. -/
theorem branchExchangeOp_apply_branchVector_true :
    branchExchangeOp (branchVector true) = branchVector false := by
  have hcross :
      normalizedPrependBitLpAdjoint false (vRight vacuumL2) = 0 := by
    exact ContinuousLinearMap.ext_iff.mp vLeft_adjoint_comp_vRight vacuumL2
  have hself :
      normalizedPrependBitLpAdjoint true (vRight vacuumL2) = vacuumL2 := by
    exact ContinuousLinearMap.ext_iff.mp vRight_adjoint_comp_vRight vacuumL2
  change
    vLeft (normalizedPrependBitLpAdjoint true (vRight vacuumL2)) +
        vRight (normalizedPrependBitLpAdjoint false (vRight vacuumL2)) =
      vLeft vacuumL2
  rw [hself, hcross, map_zero]
  simp

/-- The two branch-vector actions in one indexed statement. -/
theorem branchExchangeOp_apply_branchVector (b : Bool) :
    branchExchangeOp (branchVector b) =
      branchVector (match b with | false => true | true => false) := by
  cases b
  · exact branchExchangeOp_apply_branchVector_false
  · exact branchExchangeOp_apply_branchVector_true

/-- The exchange operator is an involution on the whole concrete boundary
carrier. This uses only the four Cuntz adjoint relations and the already
proved partition of unity. -/
theorem branchExchangeOp_comp_self :
    branchExchangeOp.comp branchExchangeOp =
      ContinuousLinearMap.id ℂ L2Carrier := by
  apply ContinuousLinearMap.ext
  intro f
  have hTL (x : L2Carrier) :
      normalizedPrependBitLpAdjoint true (vLeft x) = 0 := by
    exact ContinuousLinearMap.ext_iff.mp vRight_adjoint_comp_vLeft x
  have hTR (x : L2Carrier) :
      normalizedPrependBitLpAdjoint true (vRight x) = x := by
    exact ContinuousLinearMap.ext_iff.mp vRight_adjoint_comp_vRight x
  have hFL (x : L2Carrier) :
      normalizedPrependBitLpAdjoint false (vLeft x) = x := by
    exact ContinuousLinearMap.ext_iff.mp vLeft_adjoint_comp_vLeft x
  have hFR (x : L2Carrier) :
      normalizedPrependBitLpAdjoint false (vRight x) = 0 := by
    exact ContinuousLinearMap.ext_iff.mp vLeft_adjoint_comp_vRight x
  change
    vLeft (normalizedPrependBitLpAdjoint true
      (vLeft (normalizedPrependBitLpAdjoint true f) +
       vRight (normalizedPrependBitLpAdjoint false f))) +
      vRight (normalizedPrependBitLpAdjoint false
        (vLeft (normalizedPrependBitLpAdjoint true f) +
         vRight (normalizedPrependBitLpAdjoint false f))) = f
  simp only [map_add, hTL, hTR, hFL, hFR, map_zero, zero_add, add_zero]
  exact ContinuousLinearMap.ext_iff.mp
    normalizedPrependBitLp_partition f

/-- A two-channel amplitude embedded into the first-level Cantor branch
sector. -/
def twinAmplitudeToCantor (a : TwinAmplitude) : L2Carrier :=
  a.aPlus • branchVector false + a.aMinus • branchVector true

/-- The preceding embedding as a native LinearMap. -/
def twinAmplitudeToCantorLinear : TwinAmplitude →ₗ[ℂ] L2Carrier where
  toFun := twinAmplitudeToCantor
  map_add' := by
    intro a b
    change
      (a.aPlus + b.aPlus) • branchVector false +
          (a.aMinus + b.aMinus) • branchVector true =
        (a.aPlus • branchVector false + a.aMinus • branchVector true) +
          (b.aPlus • branchVector false + b.aMinus • branchVector true)
    rw [add_smul, add_smul]
    abel
  map_smul' := by
    intro c a
    change
      (c * a.aPlus) • branchVector false +
          (c * a.aMinus) • branchVector true =
        c • (a.aPlus • branchVector false + a.aMinus • branchVector true)
    rw [mul_smul, mul_smul, smul_add]

/-- Channel exchange on the finite twin-amplitude carrier. -/
def twinAmplitudeSwapLinear : TwinAmplitude →ₗ[ℂ] TwinAmplitude where
  toFun a := ⟨a.aMinus, a.aPlus⟩
  map_add' := by
    intro a b
    rfl
  map_smul' := by
    intro c a
    rfl

/-- The Cuntz exchange operator acts on the embedded two-channel carrier as
the finite channel swap. -/
theorem branchExchangeOp_twinAmplitude (a : TwinAmplitude) :
    branchExchangeOp (twinAmplitudeToCantorLinear a) =
      twinAmplitudeToCantorLinear (twinAmplitudeSwapLinear a) := by
  change
    branchExchangeOp
        (a.aPlus • branchVector false + a.aMinus • branchVector true) =
      a.aMinus • branchVector false + a.aPlus • branchVector true
  rw [map_add, map_smul, map_smul,
    branchExchangeOp_apply_branchVector_false,
    branchExchangeOp_apply_branchVector_true]
  abel

/-- The effective two-channel generator
((ω - iγ) I + g σₓ) on TwinAmplitude. -/
def twinEffectiveGenerator (ω γ g : ℝ) : TwinAmplitude →ₗ[ℂ] TwinAmplitude :=
  ((ω : ℂ) - Complex.I * (γ : ℂ)) •
      (LinearMap.id : TwinAmplitude →ₗ[ℂ] TwinAmplitude) +
    (g : ℂ) • twinAmplitudeSwapLinear

/-- The same effective generator lifted to the full concrete Cantor L2
carrier. -/
def cantorEffectiveGenerator (ω γ g : ℝ) : BoundaryOperator :=
  ((ω : ℂ) - Complex.I * (γ : ℂ)) •
      (ContinuousLinearMap.id ℂ L2Carrier) +
    (g : ℂ) • branchExchangeOp

/-- Exact generator-level intertwining between the existing twin amplitude
owner and the concrete Cantor branch carrier. -/
theorem cantorEffectiveGenerator_intertwines
    (ω γ g : ℝ) (a : TwinAmplitude) :
    cantorEffectiveGenerator ω γ g (twinAmplitudeToCantorLinear a) =
      twinAmplitudeToCantorLinear (twinEffectiveGenerator ω γ g a) := by
  change
    ((ω : ℂ) - Complex.I * (γ : ℂ)) •
        twinAmplitudeToCantorLinear a +
      (g : ℂ) • branchExchangeOp (twinAmplitudeToCantorLinear a) =
      twinAmplitudeToCantorLinear
        (((ω : ℂ) - Complex.I * (γ : ℂ)) • a +
          (g : ℂ) • twinAmplitudeSwapLinear a)
  rw [branchExchangeOp_twinAmplitude]
  simp only [map_add, map_smul]

/-- The explicit thermofield solution from the existing Möbius resonator,
embedded into the concrete Cantor carrier. -/
def cantorThermofieldAmplitude (β E γ ω g t : ℝ) : L2Carrier :=
  twinAmplitudeToCantorLinear (thermofieldAmplitude β E γ ω g t)

/-- The branch-exchange readout of the existing twin thermofield wave. -/
theorem branchExchangeOp_cantorThermofieldAmplitude
    (β E γ ω g t : ℝ) :
    branchExchangeOp (cantorThermofieldAmplitude β E γ ω g t) =
      twinAmplitudeToCantorLinear
        (twinAmplitudeSwapLinear (thermofieldAmplitude β E γ ω g t)) := by
  exact branchExchangeOp_twinAmplitude
    (thermofieldAmplitude β E γ ω g t)

/-!
### Hierarchical cylinder propagation

The same finite exchange can be transported to every finite cylinder by
conjugating it with the existing Cuntz word operator.  This is a passive
hierarchical embedding; it is not an assertion of a global automorphism of
the universal Cuntz algebra.
-/

/-- Exchange localized to the cylinder indexed by a finite binary word w. -/
def prefixExchangeOp (w : List Bool) : BoundaryOperator :=
  (operatorWord w).comp (branchExchangeOp.comp (operatorWordDag w))

/-- Conjugating by a Cuntz word transports the branch exchange to that
cylinder. -/
theorem prefixExchangeOp_apply_prefix (w : List Bool) (x : L2Carrier) :
    prefixExchangeOp w (operatorWord w x) =
      operatorWord w (branchExchangeOp x) := by
  change
    operatorWord w
        (branchExchangeOp
          (operatorWordDag w (operatorWord w x))) =
      operatorWord w (branchExchangeOp x)
  have hcancel :
      operatorWordDag w (operatorWord w x) = x := by
    exact ContinuousLinearMap.ext_iff.mp
      (operatorWordDag_comp_operatorWord w) x
  rw [hcancel]

/-- The localized operator exchanges the two children of every finite
cylinder. -/
theorem prefixExchangeOp_apply_branch
    (w : List Bool) (b : Bool) :
    prefixExchangeOp w (operatorWord w (branchVector b)) =
      operatorWord w
        (branchVector (match b with | false => true | true => false)) := by
  rw [prefixExchangeOp_apply_prefix, branchExchangeOp_apply_branchVector]

/-- The existing thermofield solution embedded in an arbitrary finite
cylinder. -/
def prefixThermofieldAmplitude
    (w : List Bool) (β E γ ω g t : ℝ) : L2Carrier :=
  operatorWord w (cantorThermofieldAmplitude β E γ ω g t)

/-- The localized exchange readout of the thermofield solution. -/
theorem prefixExchangeOp_apply_thermofield
    (w : List Bool) (β E γ ω g t : ℝ) :
    prefixExchangeOp w (prefixThermofieldAmplitude w β E γ ω g t) =
      operatorWord w
        (twinAmplitudeToCantorLinear
          (twinAmplitudeSwapLinear
            (thermofieldAmplitude β E γ ω g t))) := by
  calc
    prefixExchangeOp w (prefixThermofieldAmplitude w β E γ ω g t) =
        operatorWord w
          (branchExchangeOp (cantorThermofieldAmplitude β E γ ω g t)) := by
      exact prefixExchangeOp_apply_prefix w
        (cantorThermofieldAmplitude β E γ ω g t)
    _ = operatorWord w
        (twinAmplitudeToCantorLinear
          (twinAmplitudeSwapLinear
            (thermofieldAmplitude β E γ ω g t))) := by
      rw [branchExchangeOp_cantorThermofieldAmplitude]

/-- The Cantor carrier map used here agrees with the repository's existing
spinor-to-Cantor map on the two-channel realization of a twin amplitude. -/
def twinAmplitudeToSpinor (a : TwinAmplitude) : SpinorSpace :=
  a.aPlus • spinorBasis 0 + a.aMinus • spinorBasis 1

theorem spinorToCantorL2_twinAmplitudeToSpinor (a : TwinAmplitude) :
    spinorToCantorL2 (twinAmplitudeToSpinor a) =
      twinAmplitudeToCantorLinear a := by
  change
    spinorToCantorL2
        (a.aPlus • spinorBasis 0 + a.aMinus • spinorBasis 1) =
      a.aPlus • branchVector false + a.aMinus • branchVector true
  rw [map_add, map_smul, map_smul,
    spinorToCantorL2_basis_0, spinorToCantorL2_basis_1]

/-- The existing Pauli matrix owner sends the two-channel spinor to its
swapped channel. -/
theorem pauliSigma1_on_twinAmplitude (a : TwinAmplitude) :
    Matrix.toEuclideanLin
        InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1
        (twinAmplitudeToSpinor a) =
      twinAmplitudeToSpinor (twinAmplitudeSwapLinear a) := by
  ext i
  fin_cases i <;>
    simp [twinAmplitudeToSpinor, twinAmplitudeSwapLinear,
      Matrix.toEuclideanLin, Matrix.vecHead, Matrix.vecTail,
      InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1] <;>
    ring_nf

/-- On the already existing first-level carrier, the Cuntz exchange is the
same operator action as the repository's Pauli sigma-one representation. -/
theorem branchExchangeOp_eq_pauliSigma1_on_twinAmplitude
    (a : TwinAmplitude) :
    branchExchangeOp (twinAmplitudeToCantorLinear a) =
      InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner
        .pauliCuntzMatrixRepresentation
        InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1
        (twinAmplitudeToCantorLinear a) := by
  calc
    branchExchangeOp (twinAmplitudeToCantorLinear a) =
        twinAmplitudeToCantorLinear (twinAmplitudeSwapLinear a) :=
      branchExchangeOp_twinAmplitude a
    _ = spinorToCantorL2 (twinAmplitudeToSpinor (twinAmplitudeSwapLinear a)) :=
      (spinorToCantorL2_twinAmplitudeToSpinor
        (twinAmplitudeSwapLinear a)).symm
    _ = spinorToCantorL2
        (Matrix.toEuclideanLin
          InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1
          (twinAmplitudeToSpinor a)) := by
      rw [pauliSigma1_on_twinAmplitude]
    _ = InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner
        .pauliCuntzMatrixRepresentation
        InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1
        (spinorToCantorL2 (twinAmplitudeToSpinor a)) := by
      symm
      exact InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner
        .pauliCuntzMatrixRepresentation_intertwines
        InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1
        (twinAmplitudeToSpinor a)
    _ = InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner
        .pauliCuntzMatrixRepresentation
        InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1
        (twinAmplitudeToCantorLinear a) := by
      rw [spinorToCantorL2_twinAmplitudeToSpinor]

/-- The effective generator intertwining can therefore be read as a Pauli
sigma-one/Cuntz intertwining on the finite channel sector. -/
theorem cantorEffectiveGenerator_exchange_part_pauli
    (a : TwinAmplitude) (g : ℝ) :
    (g : ℂ) • branchExchangeOp (twinAmplitudeToCantorLinear a) =
      (g : ℂ) •
        InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner
          .pauliCuntzMatrixRepresentation
          InfoGeometry.Physics.ChiralPoincareSouriauBridge.σ1
          (twinAmplitudeToCantorLinear a) := by
  rw [branchExchangeOp_eq_pauliSigma1_on_twinAmplitude]

end InfoGeometry.Canonical.CantorBernoulliBranchExchangeThermofield
