import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Arithmetic.PrimonKMSKreinBridge

/-!
# InfoGeometry.Applications.PrimeKreinKMSBridge

Positive primon Gibbs/KMS state versus Krein--Möbius supertrace.

This application-level bridge separates:

* positive Hilbert/KMS thermodynamics, where `Z(β) = ζ(β)`;
* thermofield/GNS purification, which lives on a tensor-product carrier
  `H ⊗ Hbar`;
* direct-sum Krein signature doubling, which lives on a carrier `H ⊕ H`;
* the Möbius/Krein supertrace index, where the signed readout is `1 / ζ(β)`;
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

/--
Positive Gibbs data for the bosonic primon Hamiltonian.

Interpretation:

* `H e_n = log n e_n`;
* `Z(β) = Tr(exp(-βH)) = ζ(β)`;
* `beta_gt_one` is the normalizability / trace-class gate.
-/
structure PositivePrimonGibbsGate
    (State Observable : Type*) where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Normalizability / trace-class gate. -/
  beta_gt_one : 1 < beta
  /-- Positive partition function, intended to be `ζ(β)`. -/
  partition : ℝ
  /-- Positivity of the positive partition. -/
  partition_pos : 0 < partition
  /-- Positive Gibbs/KMS state carrier. -/
  gibbsState : State
  /-- Observable expectation map. -/
  expectation : Observable → ℝ
  /--
  The KMS condition for the positive Gibbs state.

  This is a gate because the concrete analytic KMS condition depends on the
  operator-algebra model.
  -/
  KMS_condition : Prop

/-- The convergence half-plane is the positive normalization gate. -/
theorem positivePrimon_beta_gt_one
    {State Observable : Type*}
    (G : PositivePrimonGibbsGate State Observable) :
    1 < G.beta :=
  G.beta_gt_one

/-- Re-export of the positive partition positivity. -/
theorem positivePrimon_partition_pos
    {State Observable : Type*}
    (G : PositivePrimonGibbsGate State Observable) :
    0 < G.partition :=
  G.partition_pos

/-! ## 2. Thermofield / purification sector -/

/--
Thermofield purification gate.

This is the tensor-product/GNS-style doubling:

`Ψβ ∈ H ⊗ Hbar`.

It is not the same object as the direct-sum Krein carrier.
-/
structure ThermofieldGNSGate
    (ThermofieldVector Observable : Type*) where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Positive normalizability domain. -/
  beta_gt_one : 1 < beta
  /-- Unnormalized or normalized thermofield vector. -/
  psi_beta : ThermofieldVector
  /-- Norm-square readout, intended to be `ζ(β)` for the unnormalized vector. -/
  normSq : ℝ
  /-- Norm-square/partition calibration, supplied by the concrete model. -/
  normSq_eq_partition : Prop
  /-- Positive expectation readout, intended as `Tr(ρβ A)`. -/
  expectation : Observable → ℝ
  /-- Normalizability gate. -/
  normalizable : Prop
  /-- Certificate that `β > 1` supplies normalizability in the chosen model. -/
  normalizable_of_beta_gt_one : normalizable

/-- Re-export of the supplied thermofield normalizability certificate. -/
theorem thermofield_normalizable
    {ThermofieldVector Observable : Type*}
    (T : ThermofieldGNSGate ThermofieldVector Observable) :
    T.normalizable :=
  T.normalizable_of_beta_gt_one

/-! ## 3. Tomita modular data -/

/--
Tomita--Takesaki modular data.

This is abstract because the concrete implementation depends on the
operator-algebraic model.  In particular, no Type-III claim is derived here.
-/
structure TomitaModularGate
    (Algebra ModularOperator ModularConjugation : Type*) where
  /-- Modular operator `Δ`. -/
  modularOperator : ModularOperator
  /-- Modular conjugation `J_T`, not to be confused with a Krein metric. -/
  modularConjugation : ModularConjugation
  /-- `J_T M J_T = M'`, recorded as a model-dependent gate. -/
  commutant_mirror : Prop
  /-- `Δ^{it} M Δ^{-it} = M`, recorded as a model-dependent gate. -/
  modular_automorphism_group : Prop
  /-- KMS condition in normalized modular time. -/
  KMS_in_modular_time : Prop

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
  /-- Semantic label: thermal copies, ghosts, or Möbius signature copies. -/
  interpretation : String

/-! ## 4. Möbius / fermionic square-free Krein index sector -/

/--
Möbius/Krein signature gate on the square-free fermionic sector.

Interpretation:

* `Γ ψ_n = μ(n) ψ_n` on square-free states;
* `Tr(Γ exp(-βH)) = Σ μ(n)n^{-β} = 1 / ζ(β)`.

This is an index/supertrace, not a positive partition function.
-/
structure MobiusKreinIndexGate
    (FermionSpace Operator : Type*) where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Positive convergence domain used by the analytic calibration. -/
  beta_gt_one : 1 < beta
  /-- Fermion/Möbius parity operator, intended as `Γ = (-1)^F`. -/
  parityOperator : Operator
  /-- Signed trace / Krein trace readout. -/
  signedTrace : ℝ
  /-- Intended zeta-side readout, usually `(ζ(β))⁻¹`. -/
  inverseZetaReadout : ℝ
  /-- Supplied signed trace / inverse-zeta calibration. -/
  signedTrace_eq_inverseZeta :
    signedTrace = inverseZetaReadout
  /-- Explicit warning gate: this readout is not a positive Gibbs state. -/
  is_index_not_state : Prop

/-- Re-export of the signed-trace / inverse-zeta calibration. -/
theorem mobius_signedTrace_eq_inverseZeta
    {FermionSpace Operator : Type*}
    (M : MobiusKreinIndexGate FermionSpace Operator) :
    M.signedTrace = M.inverseZetaReadout :=
  M.signedTrace_eq_inverseZeta

/-! ## 5. Doubled Krein Liouvillean sector -/

/--
Krein-self-adjoint Liouvillean gate.

Interpretation:

`L = H ⊕ (-H)` and `L^× = J L* J = L`.

At this abstract level, adjoints are model-dependent, so Krein-self-adjointness
is stored as a gate.
-/
structure KreinLiouvilleanGate
    (K Operator : Type*) [AddCommGroup K] [Module ℝ K] where
  /-- Direct-sum Krein carrier. -/
  krein : DirectSumKreinDoubling K
  /-- Doubled Liouvillean, intended as `H ⊕ (-H)`. -/
  liouvillean : Operator
  /-- Krein-self-adjointness gate. -/
  krein_self_adjoint : Prop
  /-- The induced flow preserves the indefinite form. -/
  eta_unitary_flow : Prop

/-! ## 6. Modular Hamiltonian normalization -/

/--
Positive modular Hamiltonian gate for a Gibbs state.

Interpretation:

`Kβ = -log ρβ = βH + log Z(β) · 1`.

The scalar `log Z(β)` normalizes the state and does not affect the modular
automorphism flow.
-/
structure GibbsModularHamiltonianGate
    (Hamiltonian ModularHamiltonian : Type*) where
  /-- Inverse temperature. -/
  beta : ℝ
  /-- Positive partition readout. -/
  partition : ℝ
  /-- Hamiltonian carrier. -/
  H : Hamiltonian
  /-- Modular Hamiltonian carrier. -/
  K_beta : ModularHamiltonian
  /-- Symbolic statement of `Kβ = βH + log Z · 1`. -/
  normalization_formula : Prop
  /-- Modular time rescales physical time by `β`. -/
  modular_time_rescaling : Prop

/-! ## 7. Optional Type-III thermodynamic-limit gate -/

/--
Operator-algebraic thermodynamic-limit gate.

Use this only when a concrete completion/limit model supplies a Type-III factor
or KMS phase structure.  It is not automatic for the trace-class `β > 1`
Hilbert-space Gibbs model.
-/
structure OperatorAlgebraicLimitGate
    (Algebra FactorType State : Type*) where
  /-- Operator algebra carrier. -/
  algebra : Algebra
  /-- State/readout carrier for the limit model. -/
  state : State
  /-- Claimed factor type carrier. -/
  factorType : FactorType
  /-- Type-III claim, supplied by the limit model. -/
  is_typeIII_claim : Prop
  /-- KMS phase structure, supplied by the limit model. -/
  KMS_phase_structure : Prop

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
  /-- Supplied comparison law. -/
  comparison_True : Prop

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
    (State Observable ThermofieldVector Algebra ModularOperator ModularConjugation
      FermionSpace Operator K Hamiltonian ModularHamiltonian : Type*)
    [AddCommGroup K] [Module ℝ K] where
  /-- Positive Hilbert/Gibbs/KMS sector. -/
  positiveGibbs :
    PositivePrimonGibbsGate State Observable
  /-- Tensor-product thermofield/GNS purification sector. -/
  thermofield :
    ThermofieldGNSGate ThermofieldVector Observable
  /-- Abstract Tomita modular sector. -/
  tomita :
    TomitaModularGate Algebra ModularOperator ModularConjugation
  /-- Signed Möbius/Krein index sector. -/
  mobiusIndex :
    MobiusKreinIndexGate FermionSpace Operator
  /-- Direct-sum doubled Krein Liouvillean sector. -/
  kreinLiouvillean :
    KreinLiouvilleanGate K Operator
  /-- Positive Gibbs modular Hamiltonian normalization sector. -/
  modularHamiltonian :
    GibbsModularHamiltonianGate Hamiltonian ModularHamiltonian
  /--
  Consistency of inverse temperatures across the positive, thermofield,
  Möbius, and modular readouts.
  -/
  beta_consistency :
    positiveGibbs.beta = thermofield.beta ∧
    positiveGibbs.beta = mobiusIndex.beta ∧
    positiveGibbs.beta = modularHamiltonian.beta
  /-- Guardrail: `H ⊗ Hbar` and `H ⊕ H` are not identified. -/
  tensorPurification_not_directSumKreinWitness : Type*
  /-- Guardrail: the Krein metric is not a positive KMS state. -/
  kreinMetric_not_positiveStateWitness : Type*
  /-- Guardrail: no unbounded Hamiltonian is represented as a bounded endomorphism here. -/
  noBoundedUnboundedHamiltonianClaim : Type*

namespace PrimeKreinKMSBridgeData

variable
    {State Observable ThermofieldVector Algebra ModularOperator ModularConjugation
      FermionSpace Operator K Hamiltonian ModularHamiltonian : Type*}
    [AddCommGroup K] [Module ℝ K]

/-- The positive Gibbs/KMS sector supplies the convergence gate. -/
theorem beta_gt_one
    (D : PrimeKreinKMSBridgeData
      State Observable ThermofieldVector Algebra ModularOperator ModularConjugation
      FermionSpace Operator K Hamiltonian ModularHamiltonian) :
    1 < D.positiveGibbs.beta :=
  D.positiveGibbs.beta_gt_one

/-- The thermofield vector is normalizable by its supplied gate. -/
theorem thermofield_normalizable
    (D : PrimeKreinKMSBridgeData
      State Observable ThermofieldVector Algebra ModularOperator ModularConjugation
      FermionSpace Operator K Hamiltonian ModularHamiltonian) :
    D.thermofield.normalizable :=
  D.thermofield.normalizable_of_beta_gt_one

/-- The Möbius/Krein signed trace equals the supplied inverse-zeta readout. -/
theorem mobius_index_eq_inverseZeta
    (D : PrimeKreinKMSBridgeData
      State Observable ThermofieldVector Algebra ModularOperator ModularConjugation
      FermionSpace Operator K Hamiltonian ModularHamiltonian) :
    D.mobiusIndex.signedTrace = D.mobiusIndex.inverseZetaReadout :=
  D.mobiusIndex.signedTrace_eq_inverseZeta

/-- Readback of temperature consistency between the positive and thermofield lanes. -/
theorem positive_beta_eq_thermofield_beta
    (D : PrimeKreinKMSBridgeData
      State Observable ThermofieldVector Algebra ModularOperator ModularConjugation
      FermionSpace Operator K Hamiltonian ModularHamiltonian) :
    D.positiveGibbs.beta = D.thermofield.beta :=
  D.beta_consistency.1

/-- Readback of temperature consistency between the positive and Möbius lanes. -/
theorem positive_beta_eq_mobius_beta
    (D : PrimeKreinKMSBridgeData
      State Observable ThermofieldVector Algebra ModularOperator ModularConjugation
      FermionSpace Operator K Hamiltonian ModularHamiltonian) :
    D.positiveGibbs.beta = D.mobiusIndex.beta :=
  D.beta_consistency.2.1

/-- Readback of temperature consistency between the positive and modular lanes. -/
theorem positive_beta_eq_modular_beta
    (D : PrimeKreinKMSBridgeData
      State Observable ThermofieldVector Algebra ModularOperator ModularConjugation
      FermionSpace Operator K Hamiltonian ModularHamiltonian) :
    D.positiveGibbs.beta = D.modularHamiltonian.beta :=
  D.beta_consistency.2.2

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
