import InfoGeometry.Geometry.BilingualUpperHalfPlane
import InfoGeometry.OperatorAlgebra.FiniteJonesOptics
import InfoGeometry.OperatorAlgebra.FiniteJonesErlangerBridge
import InfoGeometry.OperatorAlgebra.VerifiedCasimir
import InfoGeometry.OperatorAlgebra.ConformalCyclicCosmology
import InfoGeometry.OperatorAlgebra.KapustinWittenDualitySocket
import InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy
import InfoGeometry.OperatorAlgebra.KleinianReturn
import InfoGeometry.OperatorAlgebra.SelfDualChiralConeBoundary
import InfoGeometry.Automorphic.AutomorphicKreinBridge
import InfoGeometry.Automorphic.LFunctionResonance
import InfoGeometry.Automorphic.ProjectedLFunction
import InfoGeometry.Automorphic.RoelckeSelbergSpectral
import InfoGeometry.Automorphic.LanglandsSugawaraBridge
import InfoGeometry.Automorphic.LanglandsPrimeResonance
import InfoGeometry.Automorphic.HeckePurification
import InfoGeometry.Arithmetic.LFunctionPotential
import InfoGeometry.Canonical.KleinBottleOrientifold
import InfoGeometry.Canonical.BerryRotorBridge

/-!
Operator–Erlangen / Langlands lane entrypoint.

This file wires the strongest theorem-bearing modules into a single source-order
spine for the research program you sketched:

1. Geometry of the doubled upper half-plane.
2. Finite operator-Erlangen optics.
3. Automorphic and spectral projection layers.
4. Langlands/Sugawara/Hecke synthesis.
5. Physical Kapustin–Witten / holonomy instantiation.
6. Klein/topology and zeta-trace companions.

Keep this as a dependency anchor so future packets can import one lane file
instead of manually assembling the full chain.
-/

noncomputable section

namespace InfoGeometry

namespace ErlangenLanglandsLane

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.FiniteJonesErlangerBridge
open InfoGeometry.OperatorAlgebra.KapustinWittenDualitySocket
open InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy
open InfoGeometry.Automorphic
open InfoGeometry.Automorphic.LanglandsPrimeResonance
open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.Geometry
open InfoGeometry.Quantum

/--
Arithmetic-and-duality packet for one step of the Erlangen/Langlands lane.

This is the concrete property payload that the lane uses to transport from
projected automorphic data to Sugawara calibration and duality transport.
-/
structure LanglandsLaneArithmeticPacket
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (P : ProjectedAutomorphicLFunctionWitness W)
    {FiniteSet AffineSet Vir State : Type*}
    [AddCommGroup FiniteSet] [Module ℝ FiniteSet]
    [AddCommGroup AffineSet] [Module ℝ AffineSet]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    where
  eulerProduct : EulerProductWitness P.L
  completedLFunction : CompletedLFunctionWitness P.L
  sugawara : LanglandsSugawaraBridge P FiniteSet AffineSet Vir State

/-!
An arithmetic intertwiner encoding how a Möbius datum acts on arithmetic
state spaces while preserving the Siegel-cuspidal decomposition.
-/
structure LanglandsGeometryArithmeticIntertwiner
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary) where
  /-- Arithmetic transport on bulk observables. -/
  bulkTransport : Bulk →ₗ[ℝ] Bulk

  /-- Arithmetic transport on boundary observables. -/
  boundaryTransport : Boundary →ₗ[ℝ] Boundary

  /-- Compatibility with Siegel constant-term transport. -/
  siegel_transport :
    W.siegel.comp bulkTransport = boundaryTransport.comp W.siegel

  /-- Compatibility with the boundary-projector decomposition. -/
  boundaryProjector_transport :
    W.boundaryProjector.comp bulkTransport = bulkTransport.comp W.boundaryProjector

/-!
Socket interface from geometric Möbius data to arithmetic transport data.

For each Möbius action on the bilingual upper-half-plane, the correspondence
returns a Siegel-compatible arithmetic intertwiner.
-/
def LanglandsGeometryToArithmetic
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (D : Quantum.ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (Z : BilingualUpperHalfPlane D)
    (W : SiegelEisensteinWitness Bulk Boundary)
    {FiniteSet AffineSet Vir State : Type*}
    [AddCommGroup FiniteSet] [Module ℝ FiniteSet]
    [AddCommGroup AffineSet] [Module ℝ AffineSet]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (P : ProjectedAutomorphicLFunctionWitness W)
    (_packet : LanglandsLaneArithmeticPacket
      (W := W) (P := P)
      (FiniteSet := FiniteSet) (AffineSet := AffineSet) (Vir := Vir) (State := State)) :
    Type _ :=
  BilingualUpperHalfPlane.MoebiusActionDatum Z →
    LanglandsGeometryArithmeticIntertwiner (W := W)

/--
Core owner-level output target assembled by the Erlangen/Langlands lane.

Factored out as a `Prop` so geometry-enhanced constructors can reuse the
target without turning a theorem proof term into a proposition.
-/
def LanglandsLaneCoreTarget
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (P : ProjectedAutomorphicLFunctionWitness W)
    {FiniteSet AffineSet Vir State : Type*}
    [AddCommGroup FiniteSet] [Module ℝ FiniteSet]
    [AddCommGroup AffineSet] [Module ℝ AffineSet]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (packet :
      LanglandsLaneArithmeticPacket
        (W := W)
        (P := P)
        (FiniteSet := FiniteSet) (AffineSet := AffineSet) (Vir := Vir) (State := State))
    {ElectricState MagneticState DualCharge : Type*}
    (S : SDualityDatum ElectricState MagneticState DualCharge)
    {GState GdualState GLoop GdualLoop Scalar : Type*}
    (Wr : WilsonReadoutDatum GState GLoop Scalar)
    (Tr : THooftReadoutDatum GdualState GdualLoop Scalar)
    (D : LanglandsDualPair GState GdualState GLoop GdualLoop)
    (_K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar Wr Tr D) :
    Prop :=
  FiniteJonesErlangerBridgeOwnerTarget ∧
    (∀ s : ℂ, P.L s = P.functional s (W.cuspidalProjector P.bulkState)) ∧
    HasEulerProduct P.L packet.eulerProduct.PrimeIndex packet.eulerProduct.localFactor
      packet.eulerProduct.convergenceRegion ∧
    HasCompletedFunctionalEquation P.L packet.completedLFunction.completedL ∧
    (∃ R : InfoGeometry.Automorphic.SiegelResonance.LanglandsPrimeResonanceWitness P,
      R.eulerProduct = packet.eulerProduct.toEulerProductData ∧
      R.completedL = packet.completedLFunction.completedL) ∧
    (packet.sugawara.affineVirasoro.centralChargeReadout
        packet.sugawara.state =
      packet.sugawara.completedL packet.sugawara.spectralPoint) ∧
    (∀ {ψ : ElectricState} {χ : DualCharge},
      IsWilsonEigen S.electric ψ χ →
        IsTHooftEigen S.magnetic (S.dualize ψ) χ) ∧
    (∀ γ : GLoop, ∀ s : GState,
      Wr.wilson γ s = Tr.thooft (D.loopDual γ) (D.stateDual s))

/--
Constructive lane pipeline from explicit witnesses.

Given explicit arithmetic and Sugawara duality data, this theorem assembles the
non-toy owner-level outputs used by the broader owners module:

* finite-Jones Erlanger owner target,
* arithmetic package nonemptiness,
* weak Langlands-prime resonance property packaging,
* Sugawara calibration statement,
* S-duality transport of Wilson eigenconditions,
* physical Langlands holonomy transport of Wilson readout to dual `'t Hooft` readout.
-/
theorem constructLanglandsLanePacket
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (P : ProjectedAutomorphicLFunctionWitness W)
    {FiniteSet AffineSet Vir State : Type*}
    [AddCommGroup FiniteSet] [Module ℝ FiniteSet]
    [AddCommGroup AffineSet] [Module ℝ AffineSet]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (packet :
      LanglandsLaneArithmeticPacket
        (W := W)
        (P := P)
        (FiniteSet := FiniteSet) (AffineSet := AffineSet) (Vir := Vir) (State := State))
    {ElectricState MagneticState DualCharge : Type*}
    (S : SDualityDatum ElectricState MagneticState DualCharge)
    {GState GdualState GLoop GdualLoop Scalar : Type*}
    (Wr : WilsonReadoutDatum GState GLoop Scalar)
    (Tr : THooftReadoutDatum GdualState GdualLoop Scalar)
    (D : LanglandsDualPair GState GdualState GLoop GdualLoop)
    (K : KWPhysicalDualityWitness GState GdualState GLoop GdualLoop Scalar Wr Tr D) :
    LanglandsLaneCoreTarget
      W P packet S Wr Tr D K :=
by
  let Rcompat :
      ∃ R : InfoGeometry.Automorphic.SiegelResonance.LanglandsPrimeResonanceWitness P,
      R.eulerProduct = packet.eulerProduct.toEulerProductData ∧
      R.completedL = packet.completedLFunction.completedL :=
    ⟨
      {
        eulerProduct := packet.eulerProduct.toEulerProductData
        completedL := packet.completedLFunction.completedL
        completedFunctionalEquation := packet.completedLFunction.toHasCompletedFunctionalEquation
      },
      rfl,
      rfl
    ⟩
  refine
    ⟨
      finiteJonesErlangerBridgeOwnerTarget,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_
    ⟩

  · intro s
    exact P.eval_eq_projected s

  · exact packet.eulerProduct.euler_product_law

  · exact packet.completedLFunction.completed_functional_equation_law

  · exact Rcompat

  · exact packet.sugawara.centralCharge_eq_completedL

  · intro ψ χ hψ
    exact @operatorSDualityOwnerTarget ElectricState MagneticState DualCharge S ψ χ hψ

  · intro γ s
    exact @physicalLanglandsHolonomyOwnerTarget GState GdualState GLoop GdualLoop Scalar Wr Tr D K γ s

/--
Geometry-to-arithmetic correspondence for one lane step.

This property packages a geometric Möbius datum on the bilingual upper
half-plane together with explicit arithmetic transports on
`Bulk` and `Boundary`, together with Siegel projector compatibility.
-/
abbrev LanglandsGeometryCorrespondence
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (D : Quantum.ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (W : SiegelEisensteinWitness Bulk Boundary)
    {FiniteSet AffineSet Vir State : Type*}
    [AddCommGroup FiniteSet] [Module ℝ FiniteSet]
    [AddCommGroup AffineSet] [Module ℝ AffineSet]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (P : ProjectedAutomorphicLFunctionWitness W)
    (packet : LanglandsLaneArithmeticPacket (W := W) (P := P)
      (FiniteSet := FiniteSet) (AffineSet := AffineSet) (Vir := Vir) (State := State))
    (Z : BilingualUpperHalfPlane D) :=
  LanglandsGeometryToArithmetic D Z W P packet


/--
Second lane constructor with an explicit geometric property.

This extends `constructLanglandsLanePacket` by exposing the geometric/
arithmetic correspondence data alongside the core lane target.
-/
theorem constructLanglandsLanePacket_withGeometry
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (D : Quantum.ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (Z : BilingualUpperHalfPlane D)
    (W : SiegelEisensteinWitness Bulk Boundary)
    (P : ProjectedAutomorphicLFunctionWitness W)
    {FiniteSet AffineSet Vir State : Type*}
    [AddCommGroup FiniteSet] [Module ℝ FiniteSet]
    [AddCommGroup AffineSet] [Module ℝ AffineSet]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (packet : LanglandsLaneArithmeticPacket (W := W) (P := P)
      (FiniteSet := FiniteSet) (AffineSet := AffineSet) (Vir := Vir) (State := State))
    (C : LanglandsGeometryCorrespondence D W P packet Z)
    {ElectricState MagneticState DualCharge : Type*}
    (S : SDualityDatum ElectricState MagneticState DualCharge)
    {GState GdualState GLoop GdualLoop Scalar : Type*}
    (Wr : WilsonReadoutDatum GState GLoop Scalar)
    (Tr : THooftReadoutDatum GdualState GdualLoop Scalar)
    (G : LanglandsDualPair GState GdualState GLoop GdualLoop)
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar Wr Tr G) :
    BilingualUpperHalfPlane.MoebiusActionDatum Z →
    LanglandsLaneCoreTarget
      W P packet S Wr Tr G K ∧
    ∃ I : LanglandsGeometryArithmeticIntertwiner (W := W),
      W.siegel.comp I.bulkTransport = I.boundaryTransport.comp W.siegel ∧
      W.boundaryProjector.comp I.bulkTransport = I.bulkTransport.comp W.boundaryProjector :=
  by
    intro m
    exact ⟨
      constructLanglandsLanePacket (W := W) (P := P) (packet := packet)
        S Wr Tr G K,
      let I : LanglandsGeometryArithmeticIntertwiner (W := W) := C m
      ⟨I, I.siegel_transport, I.boundaryProjector_transport⟩
    ⟩

end ErlangenLanglandsLane

end InfoGeometry
