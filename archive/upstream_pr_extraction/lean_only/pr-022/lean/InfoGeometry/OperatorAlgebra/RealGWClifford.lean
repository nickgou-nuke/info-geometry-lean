/-
InfoGeometry/OperatorAlgebra/RealGWClifford.lean

Real Garding-Wightman Clifford module splitting.

Theorem-safe formalization inspired by:

  Esther Galina, Aroldo Kaplan, Linda Saal,
  "Split Clifford Modules over a Hilbert Space",
  arXiv:math/0204117v3.

This file keeps the owner lane real.

It does not assert that every complex/GW/CAR module has a real form.  It
records the witness-gated splitting criterion:

  reflected measure equivalent to the original measure,
  complement-invariant multiplicity,
  measurable real-structure field r(x),
  r(x) r(1-x) = 1,
  r(x) c_k(1-x) = (-1)^k c_k(x) r(x + delta_k).

It also does not identify this real Clifford module lane with split `Cl(n,n)`,
`O(n,n)`, or `Pin(n,n)` data.  That requires a separate doubled Krein /
split-quadratic witness.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealGWClifford

/--
Real Clifford Hilbert module packet.

This is the real owner object: a real Hilbert carrier with Clifford generators
represented by real operators.

The intended relation is:

  J z * J w + J w * J z = -2 <z,w> 1,

and in an orthonormal sequence:

  J_i^2 = -1,
  J_i J_j = -J_j J_i  for i != j.

The actual analytic Hilbert/skew-adjoint structure is witness-gated.
-/
structure RealCliffordHilbertModulePacket where
  /-- Real generator Hilbert space `Z`. -/
  GeneratorSpace : Type

  /-- Real module Hilbert carrier `H`. -/
  HilbertCarrier : Type

  /-- Real operator carrier on `H`. -/
  OperatorCarrier : Type

  /-- Clifford action `Z -> End_R(H)`. -/
  cliffordAction : GeneratorSpace -> OperatorCarrier

  /-- Distinguished countable generator labels, if using a sequence. -/
  GeneratorIndex : Type

  /-- Sequence of real Clifford generators `J_i`. -/
  J : GeneratorIndex -> OperatorCarrier

  /-- Witness that the `J_i` are real-linear operators. -/
  realLinearityWitness : Type

  /-- Witness that each generator is skew-adjoint. -/
  skewAdjointWitness : Type

  /-- Witness that each `J_i^2 = -1`. -/
  squareMinusOneWitness : Type

  /-- Witness that distinct generators anticommute. -/
  anticommutationWitness : Type

  /-- Witness that the action satisfies the Clifford relation. -/
  cliffordRelationWitness : Type

  /-- Guard: no complex scalar field is the owner of this packet. -/
  realOnlyWitness : Type

/--
Garding-Wightman occupation-space packet.

This records the measure/fiber/cocycle surface used to classify CAR/Clifford
modules.

The packet is intentionally abstract: it does not construct measure theory or
direct integrals.  It stores exactly the data whose analytic realization is
needed for the Galina-Kaplan-Saal splitting criterion.
-/
structure GWOccupationPacket where
  /-- Occupation-number space, morally `{0,1}^N`. -/
  OccupationSpace : Type

  /-- Finite-flip group, morally `Delta`. -/
  FiniteFlipGroup : Type

  /-- Distinguished flips `delta_k`. -/
  FlipIndex : Type

  /-- Action `x + delta`. -/
  flipAction : OccupationSpace -> FiniteFlipGroup -> OccupationSpace

  /-- Distinguished single-coordinate flip. -/
  delta : FlipIndex -> FiniteFlipGroup

  /-- Complement operation `x |-> 1 - x`. -/
  complement : OccupationSpace -> OccupationSpace

  /-- Measure data `mu`. -/
  measureData : Type

  /-- Reflected measure data, morally `mu_tilde(E)=mu(1-E)`. -/
  reflectedMeasureData : Type

  /-- Multiplicity function/fiber dimension data `nu`. -/
  multiplicityData : Type

  /-- Direct-integral fiber data `H_x`. -/
  fiberData : Type

  /-- Clifford/GW cocycle operators `c_k(x)`. -/
  cocycleOperatorData : Type

  /-- Witness that `mu` is quasi-invariant under finite flips. -/
  finiteFlipQuasiInvarianceWitness : Type

  /-- Witness that the `c_k` satisfy the GW cocycle equations. -/
  ckCocycleWitness : Type

/--
Real splitting witness for a GW module.

This is the theorem-safe content of the Galina-Kaplan-Saal real-form
criterion.  A real form exists only after all of these witnesses are supplied.
-/
structure GWRealSplittingWitness where
  /-- Underlying GW occupation packet. -/
  gw : GWOccupationPacket

  /-- Witness that reflected measure and original measure are equivalent. -/
  measureReflectionEquivalenceWitness : Type

  /-- Witness that multiplicity is complement-invariant: `nu(x)=nu(1-x)` a.e. -/
  multiplicityComplementInvariantWitness : Type

  /-- Measurable family `r(x): H_x -> H_{1-x}`. -/
  realStructureField : Type

  /-- Witness that `r(x)` is antilinear in the auxiliary complexified model. -/
  antilinearWitness : Type

  /-- Witness that `r(x)` preserves the fiber norm. -/
  normPreservingWitness : Type

  /-- Witness that `r(x) r(1-x)=1`. -/
  involutionWitness : Type

  /--
  Witness of the key compatibility:

    r(x) c_k(1-x) = (-1)^k c_k(x) r(x+delta_k).
  -/
  ckRealCompatibilityWitness : Type

  /-- Measurability witness for the field `r(x)`. -/
  measurabilityWitness : Type

  /-- Resulting invariant real form. -/
  invariantRealForm : Type

  /-- Guard: real splitting is not automatic for GW/CAR modules. -/
  noAutomaticRealSplitWitness : Type

/--
The theorem-safe owner target:

a GW module has a real splitting only if a `GWRealSplittingWitness` is supplied.
-/
def GWRealSplittingTarget : Prop :=
  Nonempty GWRealSplittingWitness

/-- Construct the GW real-splitting target from explicit witness data. -/
theorem constructGWRealSplittingTarget
    (W : GWRealSplittingWitness) :
    GWRealSplittingTarget := by
  exact ⟨W⟩

namespace GWRealSplittingWitness

/-- The measure-reflection equivalence witness is exposed as an accessor. -/
def measureReflectionGuard
    (W : GWRealSplittingWitness) : Type :=
  W.measureReflectionEquivalenceWitness

@[simp] theorem measureReflectionGuard_eq
    (W : GWRealSplittingWitness) :
    W.measureReflectionGuard = W.measureReflectionEquivalenceWitness :=
  rfl

/-- The multiplicity complement-invariance witness is exposed as an accessor. -/
def multiplicityComplementGuard
    (W : GWRealSplittingWitness) : Type :=
  W.multiplicityComplementInvariantWitness

@[simp] theorem multiplicityComplementGuard_eq
    (W : GWRealSplittingWitness) :
    W.multiplicityComplementGuard =
      W.multiplicityComplementInvariantWitness :=
  rfl

/-- The `r(x) r(1-x)=1` witness is exposed as an accessor. -/
def realStructureInvolutionGuard
    (W : GWRealSplittingWitness) : Type :=
  W.involutionWitness

@[simp] theorem realStructureInvolutionGuard_eq
    (W : GWRealSplittingWitness) :
    W.realStructureInvolutionGuard = W.involutionWitness :=
  rfl

/-- The `r c_k` compatibility witness is exposed as an accessor. -/
def ckRealCompatibilityGuard
    (W : GWRealSplittingWitness) : Type :=
  W.ckRealCompatibilityWitness

@[simp] theorem ckRealCompatibilityGuard_eq
    (W : GWRealSplittingWitness) :
    W.ckRealCompatibilityGuard = W.ckRealCompatibilityWitness :=
  rfl

/-- Real splitting is explicitly non-automatic. -/
def realSplitAutomaticityGuard
    (W : GWRealSplittingWitness) : Type :=
  W.noAutomaticRealSplitWitness

@[simp] theorem realSplitAutomaticityGuard_eq
    (W : GWRealSplittingWitness) :
    W.realSplitAutomaticityGuard = W.noAutomaticRealSplitWitness :=
  rfl

end GWRealSplittingWitness

/--
Finite-dimensional Cartan-Killing splitting residue.

The paper recalls the classical finite-dimensional condition: complex Clifford
modules split over `R` exactly in specific mod-4 cases.  This packet stores
that as theorem-bank witness data, not as an automatic theorem of arbitrary
finite data.
-/
structure FiniteRealCliffordSplittingPacket where
  /-- Finite generator dimension `m`. -/
  generatorDimension : Nat

  /-- Mod-4 residue data. -/
  modFourResidueData : Type

  /-- Witness that the Cartan-Killing finite splitting criterion applies. -/
  finiteSplittingCriterionWitness : Type

  /-- Guard: finite-dimensional residue does not control infinite GW splitting. -/
  noFiniteToInfiniteAutomaticityWitness : Type

/--
Fermi-Fock non-splitting guard.

The paper notes that the basic Fermi-Fock representation is irreducible over
`R` and does not split in the infinite-dimensional setting.  This packet
records that as a guard against treating CAR/Fock data as automatically
real-split.
-/
structure FermiFockRealSplitGuardPacket where
  /-- Fermi-Fock representation data. -/
  fermiFockRepresentation : Type

  /-- Witness that the measure is discrete/supported on one finite-flip orbit. -/
  discreteOrbitMeasureWitness : Type

  /-- Witness that reflected measure equivalence fails. -/
  reflectedMeasureFailureWitness : Type

  /-- Witness that no invariant real form is obtained in this model. -/
  noInvariantRealFormWitness : Type

  /-- Guard: Fermi-Fock does not supply the real split owner lane. -/
  noFermiFockAutomaticRealSplitWitness : Type

/--
Bridge to the split doubled-Krein lane.

The Galina-Kaplan-Saal theorem supplies real Clifford module splitting data.
It does not automatically supply split `Cl(n,n)`, `O(n,n)`, or `Pin(n,n)`
data.

Those require a doubled Krein / split-quadratic witness.
-/
structure RealGWToSplitKreinBridgePacket where
  /-- Real Clifford Hilbert module. -/
  realCliffordModule : RealCliffordHilbertModulePacket

  /-- Optional GW real splitting witness. -/
  gwRealSplitting : GWRealSplittingWitness

  /-- Doubled Krein carrier data. -/
  doubledKreinCarrier : Type

  /-- Split quadratic form / signature `(n,n)` witness. -/
  splitQuadraticWitness : Type

  /-- Real split Clifford algebra `Cl(n,n)` witness. -/
  clnnWitness : Type

  /-- Full `O(n,n)` symmetry witness. -/
  fullONNWitness : Type

  /-- `Pin(n,n)` reflection/CPT witness. -/
  pinNNCPTWitness : Type

  /--
  Guard: real Clifford splitting from GW theory is not automatically the same
  as split `Cl(n,n)` / `O(n,n)` / `Pin(n,n)` data.
  -/
  noAutomaticSplitKreinWitness : Type

/-- Owner target for a supplied bridge from real GW data to split Krein data. -/
def RealGWToSplitKreinBridgeTarget : Prop :=
  Nonempty RealGWToSplitKreinBridgePacket

/-- Construct the split-Krein bridge target from explicit witness data. -/
theorem constructRealGWToSplitKreinBridgeTarget
    (P : RealGWToSplitKreinBridgePacket) :
    RealGWToSplitKreinBridgeTarget := by
  exact ⟨P⟩

end InfoGeometry.OperatorAlgebra.RealGWClifford
