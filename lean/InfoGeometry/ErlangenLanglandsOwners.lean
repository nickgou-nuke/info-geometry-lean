import InfoGeometry.ErlangenLanglandsGeometryLane

noncomputable section

namespace InfoGeometry.ErlangenLanglandsOwners

open InfoGeometry.Automorphic
open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.OperatorAlgebra.FiniteJonesErlangerBridge
open InfoGeometry.OperatorAlgebra.KapustinWittenDualitySocket
open InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy
open InfoGeometry.ErlangenLanglandsLane
open InfoGeometry.Geometry

/--
Concrete constructive owner pipeline for the Erlangen/Langlands lane.

The theorem below composes:

1. a supplied projected automorphic L-property, then arithmetic witnessing
   of Euler/product + completed functional-equation data,
2. a supplied Langlands–Sugawara bridge, yielding hidden-memory calibrated
   completion data,
3. supplied S-duality and physical KW witnesses, yielding concrete duality
   transport statements.

This keeps each step explicit: every duality claim is produced by a supplied
property plus an owner-target constructor, not by hidden assumptions.
-/
abbrev constructRealisticErlangenLanglandsOwnerChainTarget
    {Bulk Boundary : Type*} [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (P : ProjectedAutomorphicLFunctionWitness W)
    (Eul : EulerProductWitness P.L)
    (Ccompleted : CompletedLFunctionWitness P.L)
    {FiniteSet AffineSet Vir State : Type*}
    [AddCommGroup FiniteSet] [Module ℝ FiniteSet]
    [AddCommGroup AffineSet] [Module ℝ AffineSet]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (B : InfoGeometry.Automorphic.LanglandsSugawaraBridge P FiniteSet AffineSet Vir State)
    {ElectricState MagneticState DualCharge : Type*}
    (S : SDualityDatum ElectricState MagneticState DualCharge)
    {GState GdualState GLoop GdualLoop Scalar : Type*}
    (Wr : WilsonReadoutDatum GState GLoop Scalar)
    (Tr : THooftReadoutDatum GdualState GdualLoop Scalar)
    (D : LanglandsDualPair GState GdualState GLoop GdualLoop)
    (K :
      KWPhysicalDualityWitness
        GState GdualState GLoop GdualLoop Scalar Wr Tr D) :
    Prop :=
  LanglandsLaneCoreTarget
    (W := W)
    (P := P)
    (packet :=
      ({
        eulerProduct := Eul
        completedLFunction := Ccompleted
        sugawara := B
      } :
          LanglandsLaneArithmeticPacket
            (W := W) (P := P)
          (FiniteSet := FiniteSet) (AffineSet := AffineSet)
          (Vir := Vir) (State := State)))
    S
    Wr
    Tr
    D
    K

theorem constructRealisticErlangenLanglandsOwnerChain
    {Bulk Boundary : Type*} [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (P : ProjectedAutomorphicLFunctionWitness W)

    (Eul : EulerProductWitness P.L)
    (Ccompleted : CompletedLFunctionWitness P.L)

    {FiniteSet AffineSet Vir State : Type*}
    [AddCommGroup FiniteSet] [Module ℝ FiniteSet]
    [AddCommGroup AffineSet] [Module ℝ AffineSet]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (B : InfoGeometry.Automorphic.LanglandsSugawaraBridge P FiniteSet AffineSet Vir State)

    {ElectricState MagneticState DualCharge : Type*}
    (S : SDualityDatum ElectricState MagneticState DualCharge)

    {GState GdualState GLoop GdualLoop Scalar : Type*}
    (Wr : WilsonReadoutDatum GState GLoop Scalar)
    (Tr : THooftReadoutDatum GdualState GdualLoop Scalar)
    (D : LanglandsDualPair GState GdualState GLoop GdualLoop)
    (K :
      KWPhysicalDualityWitness
        GState GdualState GLoop GdualLoop Scalar Wr Tr D) :
    constructRealisticErlangenLanglandsOwnerChainTarget
      (W := W) (P := P) Eul Ccompleted (FiniteSet := FiniteSet) (AffineSet := AffineSet)
      (Vir := Vir) (State := State) B (S := S)
      (Wr := Wr) (Tr := Tr) (D := D) (K := K) :=
  by
    simpa [constructRealisticErlangenLanglandsOwnerChainTarget] using
      constructLanglandsLanePacket
        (W := W)
        (P := P)
        (packet :=
          LanglandsLaneArithmeticPacket.mk
            (W := W) (P := P)
            (FiniteSet := FiniteSet) (AffineSet := AffineSet)
            (Vir := Vir) (State := State)
            Eul Ccompleted B)
        S Wr Tr D K

/--
User-facing geometric-arithmetic owner-chain target as a full lane target alias.
-/
abbrev constructRealisticErlangenLanglandsOwnerChainWithGeometryTarget
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (D : InfoGeometry.Quantum.ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (Z : BilingualUpperHalfPlane D)
    (W : SiegelEisensteinWitness Bulk Boundary)
    (P : ProjectedAutomorphicLFunctionWitness W)
    {Finite Affine Vir State : Type*}
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (Full :
      LanglandsLaneFullPacket
        (E := E) D Z W P
        (Finite := Finite) (Affine := Affine) (Vir := Vir) (State := State))
    {ElectricState MagneticState DualCharge : Type*}
    (S : SDualityDatum ElectricState MagneticState DualCharge)
    {GState GdualState GLoop GdualLoop Scalar : Type*}
    (Wr : WilsonReadoutDatum GState GLoop Scalar)
    (Tr : THooftReadoutDatum GdualState GdualLoop Scalar)
    (D' : LanglandsDualPair GState GdualState GLoop GdualLoop)
    (K : KWPhysicalDualityWitness
      GState GdualState GLoop GdualLoop Scalar Wr Tr D') :
    Prop :=
  LanglandsLaneFullTarget
    (E := E) D Z W P Full
    S Wr Tr D' K

/--
Geometry-first owner constructor through the full lane packet.
-/
theorem constructRealisticErlangenLanglandsOwnerChainWithGeometry
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (D : InfoGeometry.Quantum.ProjectivePolarizedBigradedBogoliubovDatum (E := E))
    (Z : BilingualUpperHalfPlane D)
    (W : SiegelEisensteinWitness Bulk Boundary)
    (P : ProjectedAutomorphicLFunctionWitness W)
    {Finite Affine Vir State : Type*}
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    (Full : LanglandsLaneFullPacket
      (E := E) D Z W P
      (Finite := Finite) (Affine := Affine) (Vir := Vir) (State := State))
    {ElectricState MagneticState DualCharge : Type*}
    (S : SDualityDatum ElectricState MagneticState DualCharge)
    {GState GdualState GLoop GdualLoop Scalar : Type*}
    (Wr : WilsonReadoutDatum GState GLoop Scalar)
    (Tr : THooftReadoutDatum GdualState GdualLoop Scalar)
    (G : LanglandsDualPair GState GdualState GLoop GdualLoop)
    (K :
      KWPhysicalDualityWitness
        GState GdualState GLoop GdualLoop Scalar Wr Tr G) :
    constructRealisticErlangenLanglandsOwnerChainWithGeometryTarget
      (E := E) D Z W P
      (Finite := Finite) (Affine := Affine) (Vir := Vir) (State := State)
      Full (S := S) (Wr := Wr) (Tr := Tr) (D' := G) (K := K) :=
  by
    exact
      constructFullLanglandsLanePacket
        (E := E) D Z W P
        Full S Wr Tr G K

end InfoGeometry.ErlangenLanglandsOwners
