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

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import InfoGeometry.Krein.Clifford
import InfoGeometry.Krein.OrthogonalGroup
import InfoGeometry.OperatorAlgebra.O44PinMobiusProjective

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealGWClifford

open InfoGeometry.Krein
open CliffordAlgebra
open MeasureTheory

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
  /-- Real generator module and its quadratic form. -/
  GeneratorSpace : Type*
  [generatorAddCommGroup : AddCommGroup GeneratorSpace]
  [generatorModule : Module ℝ GeneratorSpace]
  quadraticForm : QuadraticForm ℝ GeneratorSpace

  /-- Complete real Hilbert carrier for the bounded operator representation. -/
  HilbertCarrier : Type*
  [carrierNorm : NormedAddCommGroup HilbertCarrier]
  [carrierInner : InnerProductSpace ℝ HilbertCarrier]
  [carrierComplete : CompleteSpace HilbertCarrier]
  [carrierKrein : KreinSpace HilbertCarrier]
  [carrierGrading : KreinGradedModule HilbertCarrier]

  /-- Existing native Mathlib-backed Clifford representation owner. -/
  representation : SymmetricCliffordModule GeneratorSpace HilbertCarrier quadraticForm

attribute [instance] RealCliffordHilbertModulePacket.generatorAddCommGroup
  RealCliffordHilbertModulePacket.generatorModule
  RealCliffordHilbertModulePacket.carrierNorm
  RealCliffordHilbertModulePacket.carrierInner
  RealCliffordHilbertModulePacket.carrierComplete
  RealCliffordHilbertModulePacket.carrierKrein
  RealCliffordHilbertModulePacket.carrierGrading

namespace RealCliffordHilbertModulePacket

variable (P : RealCliffordHilbertModulePacket)

/-- The generator action is the representation restricted along `iota`. -/
def cliffordAction (z : P.GeneratorSpace) :
    P.HilbertCarrier →L[ℝ] P.HilbertCarrier :=
  P.representation.ρ (CliffordAlgebra.ι P.quadraticForm z)

/-- Mathlib's Clifford relation transported through the representation. -/
theorem cliffordAction_sq (z : P.GeneratorSpace) :
    P.cliffordAction z * P.cliffordAction z =
      algebraMap ℝ (P.HilbertCarrier →L[ℝ] P.HilbertCarrier)
        (P.quadraticForm z) := by
  letI := P.carrierKrein
  letI := P.carrierGrading
  letI := P.representation
  exact SymmetricCliffordModule.rho_ι_sq_scalar z

end RealCliffordHilbertModulePacket

/--
An actual conjugate-linear involutive isometry on a complex Hilbert space,
represented as a real-linear equivalence.  This is the native carrier for the
real-structure part of the GW splitting criterion.
-/
structure RealStructureData where
  Carrier : Type*
  [carrierNorm : NormedAddCommGroup Carrier]
  [carrierMeasurableSpace : MeasurableSpace Carrier]
  [carrierComplex : NormedSpace ℂ Carrier]
  [carrierInner : InnerProductSpace ℂ Carrier]
  [carrierComplete : CompleteSpace Carrier]
  r : Carrier ≃ₗ[ℝ] Carrier
  antilinear : ∀ (a : ℂ) (x : Carrier),
    r (a • x) = star a • r x
  normPreserving : ∀ x : Carrier, ‖r x‖ = ‖x‖
  involution : ∀ x : Carrier, r (r x) = x

attribute [instance] RealStructureData.carrierNorm
  RealStructureData.carrierMeasurableSpace
  RealStructureData.carrierComplex
  RealStructureData.carrierInner
  RealStructureData.carrierComplete

/-- A multiplicative one-cocycle over an explicit monoid action. -/
structure GWCocycleData
    (X G : Type*) [Monoid G]
    (action : X → G → X) where
  Operator : Type*
  [operatorMonoid : Monoid Operator]
  c : G → X → Operator
  cocycle_law :
    ∀ g h x,
      c (g * h) x = c g x * c h (action x g)

attribute [instance] GWCocycleData.operatorMonoid

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
  [occupationMeasurableSpace : MeasurableSpace OccupationSpace]

  /-- Finite-flip group, morally `Delta`. -/
  FiniteFlipGroup : Type
  [finiteFlipMonoid : Monoid FiniteFlipGroup]

  /-- Distinguished flips `delta_k`. -/
  FlipIndex : Type

  /-- Action `x + delta`. -/
  flipAction : OccupationSpace -> FiniteFlipGroup -> OccupationSpace

  /-- Distinguished single-coordinate flip. -/
  delta : FlipIndex -> FiniteFlipGroup

  /-- Complement operation `x |-> 1 - x`. -/
  complement : OccupationSpace -> OccupationSpace

  /-- Reference measure on the occupation space. -/
  measureData : Measure OccupationSpace

  /-- Reflected measure on the occupation space. -/
  reflectedMeasureData : Measure OccupationSpace

  /-- Multiplicity/fiber-dimension function `nu`. -/
  multiplicity : OccupationSpace → ℕ

  /-- Direct-integral fiber family `H_x` over the occupation space. -/
  fiberData : OccupationSpace → Type

  /-- Clifford/GW operators with their native multiplicative cocycle law. -/
  cocycleOperatorData :
    GWCocycleData OccupationSpace FiniteFlipGroup flipAction

  /-- Every distinguished finite flip is non-singular for the reference measure.

  This is the native Mathlib measure-theoretic contract replacing the former
  untyped witness socket. -/
  finiteFlipQuasiInvarianceWitness :
    ∀ g : FiniteFlipGroup,
      MeasureTheory.Measure.QuasiMeasurePreserving
        (fun x => flipAction x g) measureData measureData

attribute [instance] GWOccupationPacket.occupationMeasurableSpace
  GWOccupationPacket.finiteFlipMonoid

/--
Real splitting witness for a GW module.

This is the theorem-safe content of the Galina-Kaplan-Saal real-form
criterion.  A real form exists only after all of these witnesses are supplied.
-/
structure GWRealSplittingWitness where
  /-- Underlying GW occupation packet. -/
  gw : GWOccupationPacket

  /-- The reference and reflected measures are mutually absolutely continuous. -/
  measureReflectionEquivalenceWitness :
    gw.measureData ≪ gw.reflectedMeasureData ∧
      gw.reflectedMeasureData ≪ gw.measureData

  /-- Multiplicity is complement-invariant almost everywhere. -/
  multiplicityComplementInvariantWitness :
    ∀ᵐ x ∂gw.measureData,
      gw.multiplicity x = gw.multiplicity (gw.complement x)

  /-- Conjugate-linear involutive isometry supplying the real structure. -/
  realStructure : RealStructureData

  /--
  Action of the cocycle operators on the real-structure carrier.

  This is kept explicit because the occupation-space cocycle and the Hilbert
  carrier live at different levels; no untyped direct-integral placeholder is
  used in their place.
  -/
  operatorAction :
    gw.cocycleOperatorData.Operator →
      realStructure.Carrier → realStructure.Carrier

  /-- Parity degree of a distinguished Clifford generator. -/
  degree : gw.FlipIndex → ℕ

  /--
  Explicit real-structure compatibility for each distinguished generator:

    r c_k(1-x) = (-1)^(degree k) c_k(x) r.

  The operator action makes this an equation in the actual carrier, rather
  than a bare type-valued witness.
  -/
  ckRealCompatibility :
    ∀ (x : gw.OccupationSpace) (k : gw.FlipIndex)
      (v : realStructure.Carrier),
      realStructure.r
          (operatorAction
            (gw.cocycleOperatorData.c (gw.delta k) (gw.complement x)) v) =
        (-1 : ℂ) ^ degree k •
          operatorAction
            (gw.cocycleOperatorData.c (gw.delta k) x)
            (realStructure.r v)

  /-- The supplied real structure is measurable. -/
  measurabilityWitness : Measurable realStructure.r

  

def invariantRealForm (W : GWRealSplittingWitness) : Set W.realStructure.Carrier :=
  {v | W.realStructure.r v = v}

/--
Finite-dimensional Cartan-Killing splitting residue.

The paper recalls the classical finite-dimensional condition: complex Clifford
modules split over `R` exactly in specific mod-4 cases.  This packet stores
that as theorem-bank witness data, not as an automatic theorem of arbitrary
finite data.
-/
structure FiniteRealCliffordSplittingPacket where
  /-- Finite-dimensional real generator module and its quadratic form. -/
  GeneratorSpace : Type*
  [generatorAddCommGroup : AddCommGroup GeneratorSpace]
  [generatorModule : Module ℝ GeneratorSpace]
  [generatorFiniteDimensional : FiniteDimensional ℝ GeneratorSpace]
  quadraticForm : QuadraticForm ℝ GeneratorSpace

attribute [instance] FiniteRealCliffordSplittingPacket.generatorAddCommGroup
  FiniteRealCliffordSplittingPacket.generatorModule
  FiniteRealCliffordSplittingPacket.generatorFiniteDimensional

def FiniteRealCliffordSplittingPacket.generatorDimension
    (P : FiniteRealCliffordSplittingPacket) : ℕ :=
  Module.finrank ℝ P.GeneratorSpace

def FiniteRealCliffordSplittingPacket.modFourResidue
    (P : FiniteRealCliffordSplittingPacket) : ZMod 4 :=
  P.generatorDimension

abbrev FiniteRealCliffordSplittingPacket.cliffordAlgebra
    (P : FiniteRealCliffordSplittingPacket) :=
  CliffordAlgebra P.quadraticForm

theorem FiniteRealCliffordSplittingPacket.modFourResidue_eq_cast
    (P : FiniteRealCliffordSplittingPacket) :
    P.modFourResidue = (P.generatorDimension : ZMod 4) := rfl

/-! ## Split quadratic carrier for the bridge layer -/

/--
An actual analytic carrier for a split `(4,4)` quadratic model.

The quadratic form and its signature are supplied by the owner
`SplitQuadratic44`; the normed/Hilbert structure is included because the
orthogonal-group owner acts on a continuous carrier.  This is a bundled
mathematical model, not an untyped signature witness.
-/
structure SplitQuadraticModel where
  V : Type*
  [norm : NormedAddCommGroup V]
  [module : Module ℝ V]
  [inner : InnerProductSpace ℝ V]
  [complete : CompleteSpace V]
  Q : InfoGeometry.OperatorAlgebra.SplitQuadratic44 V

attribute [instance] SplitQuadraticModel.norm SplitQuadraticModel.module
  SplitQuadraticModel.inner SplitQuadraticModel.complete


/--
Fermi-Fock non-splitting guard.

The paper notes that the basic Fermi-Fock representation is irreducible over
`R` and does not split in the infinite-dimensional setting.  This packet
records that as a guard against treating CAR/Fock data as automatically
real-split.
-/
structure FermiFockRealSplitGuardPacket where
  /-- The represented real Clifford/Fock carrier. -/
  fermiFockRepresentation : RealCliffordHilbertModulePacket

  /-- Occupation-space measure data used by the splitting criterion. -/
  occupation : GWOccupationPacket

  /-- Representative of the finite-flip orbit carrying the discrete sector. -/
  orbitRepresentative : occupation.OccupationSpace

  /-- The finite-flip orbit is genuinely finite. -/
  discreteOrbit_finite :
    Set.Finite
      {y : occupation.OccupationSpace |
        ∃ g : occupation.FiniteFlipGroup,
          occupation.flipAction orbitRepresentative g = y}

  /-- The reflected measure is not equivalent to the reference measure. -/
  reflectedMeasure_not_equivalent :
    ¬ (occupation.measureData ≪ occupation.reflectedMeasureData ∧
      occupation.reflectedMeasureData ≪ occupation.measureData)

  /-- No GW real splitting witness exists for this occupation packet. -/
  noInvariantRealForm :
    ¬ Nonempty {W : GWRealSplittingWitness // W.gw = occupation}


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

  /-- Genuine split quadratic carrier and signature model. -/
  splitQuadraticWitness : SplitQuadraticModel

/-!
The doubled carrier and the Clifford algebra are not independent witnesses:
both are determined by the real Clifford module already stored above.  Keep
their public names as computed owner definitions rather than duplicating them
as opaque type-valued fields.
-/

def RealGWToSplitKreinBridgePacket.doubledKreinCarrier
    (P : RealGWToSplitKreinBridgePacket) : Type _ :=
  InfoGeometry.Krein.DoubledSpace P.realCliffordModule.HilbertCarrier

def RealGWToSplitKreinBridgePacket.clnnWitness
    (P : RealGWToSplitKreinBridgePacket) : Type _ :=
  CliffordAlgebra P.realCliffordModule.quadraticForm

def RealGWToSplitKreinBridgePacket.fullONNWitness
    (P : RealGWToSplitKreinBridgePacket) : Type _ :=
  InfoGeometry.Krein.HessianOrthogonalGroup
    P.splitQuadraticWitness.V

def RealGWToSplitKreinBridgePacket.pinNNCPTWitness
    (P : RealGWToSplitKreinBridgePacket) : Type _ :=
  _root_.pinGroup P.splitQuadraticWitness.Q.q


end InfoGeometry.OperatorAlgebra.RealGWClifford
