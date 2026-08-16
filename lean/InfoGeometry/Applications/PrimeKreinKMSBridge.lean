import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Arithmetic.PrimonKMSKreinBridge
import InfoGeometry.Krein.LiouvilleanDynamics
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Canonical.BoundedModularFlowCalibration

/-!
# InfoGeometry.Applications.PrimeKreinKMSBridge

Positive primon Gibbs/KMS state versus Krein--Möbius supertrace.

This application-level bridge separates:

* positive Hilbert/KMS thermodynamics, where `Z(β) = ζ(β)`;
* thermofield/GNS purification, which lives on a tensor-product carrier
  `H ⊗ Hbar`;
* direct-sum Krein signature doubling, which lives on a carrier `H ⊕ H`;
* the Möbius/Krein supertrace sector, whose inverse-zeta-labelled value is
  stored only through an explicit calibration field;
* modular Hamiltonian normalization, where the scalar `log Z(β)` normalizes the
  state and does not itself create the modular flow.

No claim is made that the Krein metric is a positive state.  No unbounded
Hamiltonian `H e_n = log n e_n` is represented as a bounded `Module.End`.  No
Type III completion, Tomita--Takesaki theorem, Euler product, analytic
continuation, or zeta-zero statement is proved here.
-/

noncomputable section

namespace InfoGeometry.Applications.PrimeKreinKMSBridge

/-! ## 1. Positive primon Gibbs/KMS sector -/

/-- Supplied positive Gibbs/KMS data, including its normalizability gate. -/
structure PositivePrimonGibbsGate
    (State Observable : Type*) [Ring Observable] where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Normalizability / trace-class gate. -/
  beta_gt_one : 1 < beta
  /-- Supplied positive partition readout. -/
  partition : ℝ
  /-- Positivity of the positive partition. -/
  partition_pos : 0 < partition
  /-- Positive Gibbs-state carrier. -/
  gibbsState : State
  /-- Supplied modular flow datum on the observable algebra. -/
  modularFlow :
    InfoGeometry.OperatorAlgebra.Thermodynamics.FlowDatum Observable
  /-- KMS-state datum for `modularFlow` at inverse temperature `beta`. -/
  kmsState :
    InfoGeometry.OperatorAlgebra.Thermodynamics.KMSState
      Observable modularFlow beta

namespace PositivePrimonGibbsGate

variable {State Observable : Type*} [Ring Observable]

/-- Complex-valued observable expectation supplied by the KMS datum. -/
def expectation
    (G : PositivePrimonGibbsGate State Observable) :
    Observable → ℂ :=
  G.kmsState.state.eval

/-- The boundary-condition proposition carried by the supplied KMS datum. -/
def KMSCondition
    (G : PositivePrimonGibbsGate State Observable) : Prop :=
  G.kmsState.kms.boundaryCondition

end PositivePrimonGibbsGate

/-- Supplied thermofield-style tensor-product doubling data. -/
structure ThermofieldGNSGate
    (ThermofieldVector Observable : Type*)
    [NormedAddCommGroup ThermofieldVector] where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Positive normalizability domain. -/
  beta_gt_one : 1 < beta
  /-- Supplied thermofield vector. -/
  psi_beta : ThermofieldVector
  /-- Partition readout calibrated by the thermofield norm square. -/
  partition : ℝ
  /-- Positivity of the partition in the normalizable regime. -/
  partition_pos : 0 < partition
  /-- Genuine norm-square/partition calibration. -/
  normSq_eq_partition : ‖psi_beta‖ ^ 2 = partition
  /-- Supplied positive expectation readout. -/
  expectation : Observable → ℝ

namespace ThermofieldGNSGate

variable
    {ThermofieldVector Observable : Type*}
    [NormedAddCommGroup ThermofieldVector]

/-- Normalizability is the positive finite norm-square relation. -/
def Normalizable
    (T : ThermofieldGNSGate ThermofieldVector Observable) : Prop :=
  0 < ‖T.psi_beta‖ ^ 2

/-- Partition positivity and the calibration equation imply normalizability. -/
theorem normalizable
    (T : ThermofieldGNSGate ThermofieldVector Observable) :
    T.Normalizable := by
  rw [Normalizable, T.normSq_eq_partition]
  exact T.partition_pos

end ThermofieldGNSGate

/--
Tomita--Takesaki modular data.

This is abstract because the concrete implementation depends on the
operator-algebraic model.  In particular, no Type-III claim is derived here.
-/
abbrev TomitaModularGate
    (Algebra : Type*) [Ring Algebra] :=
  InfoGeometry.OperatorAlgebra.Thermodynamics.TomitaKMSDatum Algebra

namespace TomitaModularGate

variable {Algebra : Type*} [Ring Algebra]

/-- The Tomita flow is a genuine one-parameter family of ring equivalences. -/
def modular_automorphism_group
    (T : TomitaModularGate Algebra) :
    InfoGeometry.OperatorAlgebra.Thermodynamics.ModularFlow Algebra :=
  T.modularFlow

/-- The supplied Tomita datum satisfies its stored KMS boundary condition. -/
theorem KMS_in_modular_time
    (T : TomitaModularGate Algebra) :
    T.toKMSState.kms.boundaryCondition :=
  T.toKMSState_is_KMS

end TomitaModularGate

/-! ## 4. Abstract real Krein carrier -/

/--
A fundamental symmetry on a real carrier.

Interpretation: `J² = 1`, and in a concrete Hilbert model the indefinite form
is represented by `[x,y]_J = ⟨x, J y⟩`.  This abstract structure does not assert
positivity.
-/
structure FundamentalSymmetry
    (K : Type*) [AddCommGroup K] [Module ℝ K] where
  /-- Fundamental symmetry. -/
  J : Module.End ℝ K
  /-- Involution law. -/
  J_sq : J.comp J = 1

namespace FundamentalSymmetry

variable {K : Type*} [AddCommGroup K] [Module ℝ K]

@[simp]
theorem J_sq_apply
    (S : FundamentalSymmetry K)
    (x : K) :
    S.J (S.J x) = x := by
  have h := congrArg (fun f : Module.End ℝ K => f x) S.J_sq
  simpa using h

end FundamentalSymmetry

/--
Direct-sum real Krein doubling gate.

This is the `H ⊕ H` carrier with signature operator `η = diag(1,-1)` or, in
the Möbius sector, `Γ ⊕ (-Γ)`.
-/
structure DirectSumKreinDoubling
    (K : Type*) [AddCommGroup K] [Module ℝ K] where
  /-- Fundamental symmetry of the direct-sum Krein carrier. -/
  symmetry : FundamentalSymmetry K

/-! The underlying direct-sum carrier is the typed product `K × K`; semantic
labels are not stored as data. -/
abbrev DirectSumKreinCarrier (K : Type*) := K × K

/-! ## 4. Möbius / fermionic square-free Krein index sector -/

/-- Supplied signed/supertrace data for a finite or square-free index sector.

The structure stores the parity and zeta-side readouts as data; it does not
construct an operator trace or an analytic Dirichlet series.
-/
structure MobiusKreinIndexGate
    (FermionSpace Operator : Type*) where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Supplied convergence-domain hypothesis for the calibration. -/
  beta_gt_one : 1 < beta
  /-- Supplied fermion/parity operator. -/
  parityOperator : Operator
  /-- Signed trace / Krein trace readout. -/
  signedTrace : ℝ
  /-- Supplied inverse-zeta-labelled readout. -/
  inverseZetaReadout : ℝ
  /-- Supplied signed trace / inverse-zeta calibration. -/
  signedTrace_eq_inverseZeta :
    signedTrace = inverseZetaReadout

namespace MobiusKreinIndexGate

variable {FermionSpace Operator : Type*}

/-- The Möbius signed readout uses the supertrace backend, not a state backend. -/
def backendKind
    (_M : MobiusKreinIndexGate FermionSpace Operator) :
    InfoGeometry.OperatorAlgebra.IntegrationBackendKind :=
  .superTrace

/-- The historical index-not-state guardrail is now a concrete backend classification. -/
theorem is_index_not_state
    (M : MobiusKreinIndexGate FermionSpace Operator) :
    M.backendKind = InfoGeometry.OperatorAlgebra.IntegrationBackendKind.superTrace :=
  rfl

end MobiusKreinIndexGate

/--
Krein-self-adjoint Liouvillean gate.

Interpretation:

`L = H ⊕ (-H)` and `L^× = J L* J = L`.

At this abstract level, adjoints are model-dependent, so Krein-self-adjointness
is stored as a gate.
-/
structure KreinLiouvilleanGate
    (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] [InfoGeometry.Krein.KreinSpace K] where
  /-- Native bounded Krein-self-adjoint Liouvillean. -/
  liouvillean :
    InfoGeometry.Krein.KreinSelfAdjointLiouvillean (H := K)
  /-- Native Krein-skew generator of the canonical exponential flow. -/
  flowGenerator :
    InfoGeometry.Krein.KreinSkewGenerator (H := K)

namespace KreinLiouvilleanGate

open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace

variable
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] [KreinSpace K]

/-- Krein self-adjointness is carried by the native operator subtype. -/
theorem krein_self_adjoint (L : KreinLiouvilleanGate K) :
    IsKreinSelfAdjoint (L.liouvillean : K →L[ℝ] K) :=
  L.liouvillean.2

/-- The canonical flow generated by `flowGenerator` preserves the Krein form. -/
theorem eta_unitary_flow (L : KreinLiouvilleanGate K) (t : ℝ) :
    IsKreinIsometry (L.flowGenerator.modularFlow.flow t) :=
  L.flowGenerator.flow_isKreinIsometry t

/-- The generated flow satisfies the one-parameter composition law. -/
theorem flow_add (L : KreinLiouvilleanGate K) (s t : ℝ) :
    L.flowGenerator.modularFlow.flow (s + t) =
      L.flowGenerator.modularFlow.flow s *
        L.flowGenerator.modularFlow.flow t :=
  L.flowGenerator.flow_add s t

end KreinLiouvilleanGate

/-! ## 6. Modular Hamiltonian normalization -/

/--
Positive modular Hamiltonian gate for a Gibbs state.

Interpretation:

`Kβ = -log ρβ = βH + log Z(β) · 1`.

The scalar `log Z(β)` normalizes the state and does not affect the modular
automorphism flow.
-/
abbrev GibbsModularHamiltonianGate
    (E LieAlgebra : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddMonoid LieAlgebra] :=
  InfoGeometry.Canonical.BoundedModularFlowCalibration.Calibration
    (E := E) (LieAlgebra := LieAlgebra)

namespace GibbsModularHamiltonianGate

open InfoGeometry.Canonical.BoundedModularFlowCalibration

variable
    {E LieAlgebra : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [AddMonoid LieAlgebra]

/-- The normalized modular Hamiltonian is the Souriau generator plus its
Massieu/partition-potential identity shift. -/
theorem normalization_formula
    (G : GibbsModularHamiltonianGate E LieAlgebra) :
    G.souriau.family.modularHamiltonian =
      G.souriau.superBridge.Ksur +
        G.souriau.family.partitionPotential • (1 : E →L[ℝ] E) :=
  G.modularHamiltonian_eq_Ksur_add_partitionPotential_one

/-- The bounded implementing flow is generated by the same Souriau operator
that owns the modular Hamiltonian normalization. -/
theorem modular_time_generated_by_Khat_beta
    (G : GibbsModularHamiltonianGate E LieAlgebra)
    (t : ℝ) :
    G.flow t = NormedSpace.exp (t • G.souriau.family.Khat_beta) :=
  G.flow_eq_exp_Khat_beta t

end GibbsModularHamiltonianGate

/-! ## 7. Optional Type-III thermodynamic-limit gate -/

/--
Operator-algebraic thermodynamic-limit gate.

Use this only when a concrete completion/limit model supplies a Type-III factor
or KMS phase structure.  It is not automatic for the trace-class `β > 1`
Hilbert-space Gibbs model.
-/
structure OperatorAlgebraicLimitGate
    (Algebra Core FactorType State : Type*)
    [AddCommMonoid Algebra] [Mul Core] where
  /-- Operator algebra carrier. -/
  algebra : Algebra
  /-- State/readout carrier for the limit model. -/
  state : State
  /-- Claimed factor type carrier. -/
  factorType : FactorType
  /-- Genuine modular-weight and continuous-core integration owner. -/
  integration :
    InfoGeometry.OperatorAlgebra.TypeIIIIntegrationDatum Algebra Core

namespace OperatorAlgebraicLimitGate

variable
    {Algebra Core FactorType State : Type*}
    [AddCommMonoid Algebra] [Mul Core]

/-- Type-III base integration is definitionally routed through a modular weight. -/
theorem is_typeIII_claim
    (L : OperatorAlgebraicLimitGate Algebra Core FactorType State) :
    L.integration.typeIII =
      InfoGeometry.OperatorAlgebra.IntegrationBackendKind.modularWeight :=
  rfl

/-- The KMS/modular phase owner is the installed modular-weight datum itself. -/
def KMS_phase_structure
    (L : OperatorAlgebraicLimitGate Algebra Core FactorType State) :
    InfoGeometry.OperatorAlgebra.ModularWeightDatum Algebra :=
  L.integration.modularWeight

end OperatorAlgebraicLimitGate

/-! ## 8. Positive/Krein comparison gate -/

/--
A comparison between the positive TFD expectation and a signed Krein index.

This is intentionally a gate, not a definitional equality.  The positive
Hilbert/GNS state and the indefinite Krein index live in different semantic
layers.
-/
structure PositiveKreinReadoutComparison
    (Observable IndexReadout : Type*) where
  /-- Positive expectation readout. -/
  positiveExpectation : Observable → ℝ
  /-- Signed Krein/Möbius index readout. -/
  kreinIndex : IndexReadout → ℝ

/-! ## 9. Full bridge package -/

/--
Full positive/Krein primon bridge.

This is the precise contract:

* `positiveGibbs` is the positive Hilbert/KMS sector;
* `thermofield` is the tensor-product purification sector;
* `mobiusIndex` is the signed Krein/supertrace sector;
* `kreinLiouvillean` is the direct-sum doubled indefinite sector;
* `modularHamiltonian` records the Gibbs modular normalization.

The positive state and the Krein index are not identified.
-/
structure PrimeKreinKMSBridgeData
    (State Observable ThermofieldVector Algebra FermionSpace Operator K
      LieAlgebra : Type*)
    [AddMonoid LieAlgebra]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [InfoGeometry.Krein.KreinSpace K]
    [NormedAddCommGroup ThermofieldVector] [Ring Observable] [Ring Algebra] where
  /-- Positive Hilbert/Gibbs/KMS sector. -/
  positiveGibbs :
    PositivePrimonGibbsGate State Observable
  /-- Tensor-product thermofield/GNS purification sector. -/
  thermofield :
    ThermofieldGNSGate ThermofieldVector Observable
  /-- Abstract Tomita modular sector. -/
  tomita :
    TomitaModularGate Algebra
  /-- Signed Möbius/Krein index sector. -/
  mobiusIndex :
    MobiusKreinIndexGate FermionSpace Operator
  /-- Direct-sum doubled Krein Liouvillean sector. -/
  kreinLiouvillean :
    KreinLiouvilleanGate K
  /-- Positive Gibbs modular Hamiltonian normalization sector. -/
  modularHamiltonian :
    GibbsModularHamiltonianGate K LieAlgebra
  /--
  Consistency of inverse temperatures across the positive, thermofield,
  Möbius, and modular readouts.
  -/
  beta_consistency :
    positiveGibbs.beta = thermofield.beta ∧
    positiveGibbs.beta = mobiusIndex.beta ∧
    positiveGibbs.beta = modularHamiltonian.beta

namespace PrimeKreinKMSBridgeData

variable
    {State Observable ThermofieldVector Algebra FermionSpace Operator K
      LieAlgebra : Type*}
    [AddMonoid LieAlgebra]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [InfoGeometry.Krein.KreinSpace K]
    [NormedAddCommGroup ThermofieldVector]
    [Ring Observable] [Ring Algebra]

end PrimeKreinKMSBridgeData

/-! ## 8. Link to the finite arithmetic bridge -/

/--
The application bridge is compatible with the finite arithmetic bridge:
finite positive Gibbs weights are nonnegative.
-/
theorem finite_positiveGibbsWeight_nonneg
    {State : Type*}
    (energy : State → ℝ)
    (β : ℝ)
    (s : State) :
    0 ≤ InfoGeometry.Arithmetic.PrimonKMSKreinBridge.positiveGibbsWeight energy β s :=
  InfoGeometry.Arithmetic.PrimonKMSKreinBridge.positiveGibbsWeight_nonneg energy β s

end InfoGeometry.Applications.PrimeKreinKMSBridge
