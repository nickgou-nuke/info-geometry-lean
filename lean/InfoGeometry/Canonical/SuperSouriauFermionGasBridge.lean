import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Canonical.GrandCanonicalFockNumberBridge
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SuperSouriauFermionGasBridge

Supergraded Souriau/Fock bridge for the ideal fermion-gas prose.

The module keeps three claims separate:

- super-moment/stress/supercurrent data are explicit projections;
- grand-canonical Fock dynamics is the existing operator `H - mu N_B`, with an
  optional odd source term;
- Fermi/Pauli behavior is carried only by a genuine CAR hypothesis or by the
  concrete split-`Cl(1,1)` CAR construction.  It is not inferred from the
  doubled-projector super branch.
-/

namespace InfoGeometry.Canonical.SuperSouriauFermionGasBridge

open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.GrandCanonicalFockNumberBridge
open InfoGeometry.Canonical.SuperchargeCARCCRBridge

universe u v w

/--
Super-moment map data split into even and odd lanes.

The even lane carries stress/charge readouts; the odd lane carries supercurrent
readouts.  This is an interface, not a claim that a concrete supermanifold or
stress-energy variation has already been constructed.
-/
@[rep_depth transport]
structure SuperMomentMapData (State : Type u) (EvenMoment : Type v) (OddMoment : Type w) where
  evenMoment : State → EvenMoment
  oddMoment : State → OddMoment
  stressTensorReadout : EvenMoment → ℝ
  chargeReadout : EvenMoment → ℝ
  supercurrentReadout : OddMoment → ℝ

namespace SuperMomentMapData

variable {State : Type u} {EvenMoment : Type v} {OddMoment : Type w}
variable (J : SuperMomentMapData State EvenMoment OddMoment)

/-- Stress tensor readout is an even-sector projection of the super-moment map. -/
@[rep_depth transport]
def stressTensor (x : State) : ℝ :=
  J.stressTensorReadout (J.evenMoment x)

/-- Bosonic charge readout is an even-sector projection of the super-moment map. -/
@[rep_depth transport]
def bosonicCharge (x : State) : ℝ :=
  J.chargeReadout (J.evenMoment x)

/-- Supercurrent readout is an odd-sector projection of the super-moment map. -/
@[rep_depth transport]
def supercurrent (x : State) : ℝ :=
  J.supercurrentReadout (J.oddMoment x)

@[rep_depth transport]
theorem stressTensor_eq_even_readout (x : State) :
    J.stressTensor x = J.stressTensorReadout (J.evenMoment x) := rfl

@[rep_depth transport]
theorem supercurrent_eq_odd_readout (x : State) :
    J.supercurrent x = J.supercurrentReadout (J.oddMoment x) := rfl

/--
Projection packet for the super-moment map.

This is the Lean-facing normalization of the prose statement that stress,
bosonic charge, and supercurrent are different readouts of the same
super-moment data.
-/
@[rep_depth transport]
theorem projection_readout_packet (x : State) :
    J.stressTensor x = J.stressTensorReadout (J.evenMoment x) ∧
    J.bosonicCharge x = J.chargeReadout (J.evenMoment x) ∧
    J.supercurrent x = J.supercurrentReadout (J.oddMoment x) := by
  exact ⟨rfl, rfl, rfl⟩

end SuperMomentMapData

/-- Even/odd Souriau temperature parameters for a supergraded ensemble. -/
@[rep_depth thermo]
structure SuperGeometricTemperature where
  betaEven : ℝ
  betaOdd : ℝ

/--
Scalarized even/odd Souriau action pairing.

The real analytic pairing with a genuine superalgebra dual is deliberately kept
as data.  This is the finite/operator bridge used by the Fock generator below.
-/
@[rep_depth thermo]
structure SuperSouriauPairing
    (State : Type u) (EvenMoment : Type v) (OddMoment : Type w) where
  J : SuperMomentMapData State EvenMoment OddMoment
  beta : SuperGeometricTemperature
  evenEnergy : State → ℝ
  oddSource : State → ℝ

namespace SuperSouriauPairing

variable {State : Type u} {EvenMoment : Type v} {OddMoment : Type w}
variable (P : SuperSouriauPairing State EvenMoment OddMoment)

/-- Supergraded Souriau action: even thermal part plus odd source part. -/
@[rep_depth thermo]
def action (x : State) : ℝ :=
  P.beta.betaEven * P.evenEnergy x + P.beta.betaOdd * P.oddSource x

@[rep_depth thermo]
theorem action_eq_even_add_odd (x : State) :
    P.action x =
      P.beta.betaEven * P.evenEnergy x + P.beta.betaOdd * P.oddSource x := rfl

@[rep_depth thermo]
theorem action_zero_odd_beta (x : State) (h : P.beta.betaOdd = 0) :
    P.action x = P.beta.betaEven * P.evenEnergy x := by
  simp [action, h]

end SuperSouriauPairing

section FockOperatorBridge

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Even grand-canonical Fock generator, the operator `H - mu N_B`. -/
@[rep_depth krein]
noncomputable def evenGrandCanonicalFockGenerator
    (B : BogoliubovMixingParams) (H : FockEndomorphism E) (mu : ℝ) :
    FockEndomorphism E :=
  grandCanonicalFockGenerator (E := E) B H mu

/-- Odd source coupling in the supergraded Fock generator. -/
@[rep_depth krein]
noncomputable def oddFockSourceCoupling
    (betaOdd : ℝ) (Qodd : FockEndomorphism E) : FockEndomorphism E :=
  betaOdd • Qodd

/--
Super grand-canonical Fock generator:
the even grand-canonical generator plus an explicit odd source.
-/
@[rep_depth krein]
noncomputable def superGrandCanonicalFockGenerator
    (B : BogoliubovMixingParams) (H : FockEndomorphism E) (mu betaOdd : ℝ)
    (Qodd : FockEndomorphism E) : FockEndomorphism E :=
  evenGrandCanonicalFockGenerator (E := E) B H mu
    + oddFockSourceCoupling (E := E) betaOdd Qodd

@[rep_depth krein]
theorem superGrandCanonicalFockGenerator_eq_even_add_odd
    (B : BogoliubovMixingParams) (H : FockEndomorphism E) (mu betaOdd : ℝ)
    (Qodd : FockEndomorphism E) :
    superGrandCanonicalFockGenerator (E := E) B H mu betaOdd Qodd =
      evenGrandCanonicalFockGenerator (E := E) B H mu
        + oddFockSourceCoupling (E := E) betaOdd Qodd := rfl

/-- With zero odd temperature/source coefficient, the super generator reduces to the even one. -/
@[rep_depth krein]
theorem superGrandCanonicalFockGenerator_zero_odd_beta
    (B : BogoliubovMixingParams) (H Qodd : FockEndomorphism E) (mu : ℝ) :
    superGrandCanonicalFockGenerator (E := E) B H mu 0 Qodd =
      evenGrandCanonicalFockGenerator (E := E) B H mu := by
  unfold superGrandCanonicalFockGenerator oddFockSourceCoupling
  have hzero : (0 : ℝ) • Qodd = (0 : FockEndomorphism E) := by
    apply ContinuousLinearMap.ext
    intro x
    simp
  simp [hzero]

/--
At zero chemical potential the even grand-canonical part collapses to `H`,
leaving only the explicit odd source coupling.
-/
@[rep_depth krein]
theorem superGrandCanonicalFockGenerator_zero_mu
    (B : BogoliubovMixingParams) (H Qodd : FockEndomorphism E) (betaOdd : ℝ) :
    superGrandCanonicalFockGenerator (E := E) B H 0 betaOdd Qodd =
      H + oddFockSourceCoupling (E := E) betaOdd Qodd := by
  simp [superGrandCanonicalFockGenerator, evenGrandCanonicalFockGenerator,
    grandCanonicalFockGenerator_zero_mu]

/-- Odd-odd superbracket is exactly the CAR/anticommutator channel. -/
@[rep_depth krein]
theorem odd_odd_superBracket_eq_CARBracket
    (A B : FockEndomorphism E) :
    fockSuperBracket (E := E) SuperParity.odd SuperParity.odd A B =
      CARBracket (E := E) A B := rfl

/-- Even-even superbracket is exactly the CCR/commutator channel. -/
@[rep_depth krein]
theorem even_even_superBracket_eq_CCRBracket
    (A B : FockEndomorphism E) :
    fockSuperBracket (E := E) SuperParity.even SuperParity.even A B =
      CCRBracket (E := E) A B := rfl

/--
Fermionic CAR gas package.

This is the operator-level replacement for prose claims about Pauli/Fermi
statistics.  The CAR identities are hypotheses unless supplied by a concrete
Clifford/Majorana construction.
-/
@[rep_depth krein]
structure FermionicCAROperatorPair where
  annihilation : FockEndomorphism E
  creation : FockEndomorphism E
  car : IsCARPair (E := E) annihilation creation

namespace FermionicCAROperatorPair

variable (F : FermionicCAROperatorPair (E := E))

/-- Pauli nilpotence for the annihilation operator: `{a,a}=0`. -/
@[rep_depth krein]
theorem annihilation_anticommutator_self_zero :
    fockAnticommutator (E := E) F.annihilation F.annihilation = 0 := by
  exact F.car.1

/-- Pauli nilpotence for the creation operator: `{a†,a†}=0`. -/
@[rep_depth krein]
theorem creation_anticommutator_self_zero :
    fockAnticommutator (E := E) F.creation F.creation = 0 := by
  exact F.car.2.1

/-- Canonical mixed CAR identity: `{a,a†}=1`. -/
@[rep_depth krein]
theorem annihilation_creation_anticommutator_id :
    fockAnticommutator (E := E) F.annihilation F.creation =
      ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  exact F.car.2.2

end FermionicCAROperatorPair

/--
Concrete split-`Cl(1,1)` null-mode construction of a genuine fermionic CAR
pair on the doubled Fock/Krein carrier.
-/
@[rep_depth krein]
noncomputable def cliffordConcreteFermionicCAROperatorPair :
    FermionicCAROperatorPair (E := E) where
  annihilation := cliffordConcreteAnnihilation (E := E)
  creation := cliffordConcreteCreation (E := E)
  car := cliffordConcreteIsCARPair (E := E)

/--
Concrete CAR packet supplied by the split-`Cl(1,1)` construction.

This replaces the abstract Pauli/Fermi hypothesis with the existing
dimension-agnostic doubled real Krein construction.
-/
@[rep_depth krein]
theorem cliffordConcreteFermionicCARPacket :
    fockAnticommutator (E := E)
        (cliffordConcreteAnnihilation (E := E))
        (cliffordConcreteAnnihilation (E := E)) = 0 ∧
    fockAnticommutator (E := E)
        (cliffordConcreteCreation (E := E))
        (cliffordConcreteCreation (E := E)) = 0 ∧
    fockAnticommutator (E := E)
        (cliffordConcreteAnnihilation (E := E))
        (cliffordConcreteCreation (E := E)) =
      ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  let F := cliffordConcreteFermionicCAROperatorPair (E := E)
  exact ⟨
    FermionicCAROperatorPair.annihilation_anticommutator_self_zero (E := E) F,
    FermionicCAROperatorPair.creation_anticommutator_self_zero (E := E) F,
    FermionicCAROperatorPair.annihilation_creation_anticommutator_id (E := E) F⟩

/--
Constructive super-Fock fermion-gas packet.

It combines the even grand-canonical generator, the explicit odd source, and
the concrete CAR/Pauli identities without passing through a finite-dimensional
toy model.
-/
@[rep_depth krein]
theorem superFockConcreteFermionGasPacket
    (B : BogoliubovMixingParams) (H Qodd : FockEndomorphism E) (mu betaOdd : ℝ) :
    superGrandCanonicalFockGenerator (E := E) B H mu betaOdd Qodd =
      evenGrandCanonicalFockGenerator (E := E) B H mu
        + oddFockSourceCoupling (E := E) betaOdd Qodd ∧
    fockSuperBracket (E := E) SuperParity.odd SuperParity.odd
        (cliffordConcreteAnnihilation (E := E))
        (cliffordConcreteCreation (E := E)) =
      CARBracket (E := E)
        (cliffordConcreteAnnihilation (E := E))
        (cliffordConcreteCreation (E := E)) ∧
    fockAnticommutator (E := E)
        (cliffordConcreteAnnihilation (E := E))
        (cliffordConcreteAnnihilation (E := E)) = 0 ∧
    fockAnticommutator (E := E)
        (cliffordConcreteCreation (E := E))
        (cliffordConcreteCreation (E := E)) = 0 ∧
    fockAnticommutator (E := E)
        (cliffordConcreteAnnihilation (E := E))
        (cliffordConcreteCreation (E := E)) =
      ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  have hcar := cliffordConcreteFermionicCARPacket (E := E)
  exact ⟨rfl, rfl, hcar.1, hcar.2.1, hcar.2.2⟩

/--
Honesty bridge: the canonical doubled-projector ladder surface gives a
projector-super pair, not a CAR pair.
-/
@[rep_depth krein]
theorem projector_super_pair_is_not_claimed_as_CAR :
    IsProjectorSuperPair (E := E)
      (InfoGeometry.Quantum.annihilationOp (E := E))
      (InfoGeometry.Quantum.creationOp (E := E)) :=
  projectorSuperPair_base (E := E)

end FockOperatorBridge

/--
Abstract conformal/Weyl supertrace-free stress package.

The supertrace-free and Weyl-invariant claims are explicit hypotheses here; a
future concrete supermanifold/stress-variation construction can instantiate
this structure.
-/
@[rep_depth transport]
structure WeylSupertraceFreeStressContext (Stress : Type u) where
  stress : Stress
  superTrace : Stress → ℝ
  weylInvariant : Prop
  stress_supertrace_free : superTrace stress = 0
  weyl_invariant : weylInvariant

namespace WeylSupertraceFreeStressContext

variable {Stress : Type u} (C : WeylSupertraceFreeStressContext Stress)

/-- The conformal/supertrace-free stress statement as a projection theorem. -/
@[rep_depth transport]
theorem superTrace_stress_eq_zero :
    C.superTrace C.stress = 0 :=
  C.stress_supertrace_free

/-- The Weyl invariance statement carried by this context. -/
@[rep_depth transport]
theorem is_weyl_invariant :
    C.weylInvariant :=
  C.weyl_invariant

end WeylSupertraceFreeStressContext

end InfoGeometry.Canonical.SuperSouriauFermionGasBridge
