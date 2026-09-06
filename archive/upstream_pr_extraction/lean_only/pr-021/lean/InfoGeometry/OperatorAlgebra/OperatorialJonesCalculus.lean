/-
InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus.lean

Operatorial Jones calculus sockets.

Ordinary Jones transformations need not be J-unitary: lossless optical
elements are unitary up to phase, projective Jones maps act on rays, and
polarizers may be non-unitary.  The Krein/CPT branch is therefore recorded as
an optional calibration rather than a global requirement.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

/-! ## 1. Basic projective/operatorial predicates -/

/-- Algebraic projector. -/
def IsProjector
    {Op : Type*} [Mul Op]
    (P : Op) : Prop :=
  P * P = P

/--
A Jones transport acts projectively if it sends projectors/rays to
projectors/rays.
-/
def ActsProjectively
    {Op : Type*} [Mul Op]
    (T : Op → Op) : Prop :=
  ∀ P : Op, IsProjector P → IsProjector (T P)

/--
A transport preserves the chiral/polarization axis on the left.
-/
def PreservesChirality
    {Op : Type*} [Mul Op]
    (chi : Op)
    (T : Op → Op) : Prop :=
  ∀ x : Op, T (chi * x) = chi * T x

/--
A transport reverses the chiral/polarization axis on the left.
-/
def FlipsChirality
    {Op : Type*} [Mul Op] [Neg Op]
    (chi : Op)
    (T : Op → Op) : Prop :=
  ∀ x : Op, T (chi * x) = -(chi * T x)

/--
Optional classification of surface/operator type.
-/
inductive JonesSurfaceKind where
  | dielectricReflection
  | brewsterProjection
  | totalInternalReflection
  | metalMirror
  | chiralMedium
  | roughDepolarizingSurface
  | metasurface
  | abstractTransport
deriving DecidableEq, Repr

/-! ## 2. Base operatorial Jones datum -/

/--
An operatorial Jones datum.

This is the generic socket: it only requires projective action. More restrictive
branches, such as chirality-preserving or J-unitary Jones transports, are
separate structures.
-/
structure OperatorialJonesDatum
    (Op : Type*) [Mul Op] where
  /-- Chiral grading or polarization axis. -/
  chi : Op

  /-- Jones transport on the operator algebra. -/
  transform : Op → Op

  /-- Projective action proof. -/
  acts_projectively :
    ActsProjectively transform

  /-- Surface/transport classification. -/
  kind : JonesSurfaceKind

  /-- Coherence certificate: if false in a concrete model, use Mueller/Stokes data. -/
  coherence_law : Prop

  /-- Proof of the coherence certificate. -/
  coherent : coherence_law

namespace OperatorialJonesDatum

variable {Op : Type*} [Mul Op]

/-- Apply the Jones transport to an operator. -/
def apply
    (J : OperatorialJonesDatum Op)
    (x : Op) : Op :=
  J.transform x

/-- Re-export projective action. -/
theorem maps_projectors
    (J : OperatorialJonesDatum Op)
    (P : Op)
    (hP : IsProjector P) :
    IsProjector (J.apply P) :=
  J.acts_projectively P hP

/--
Composition of two Jones transports with the same chiral axis.
-/
def compose
    (J₂ J₁ : OperatorialJonesDatum Op)
    (_hchi : J₂.chi = J₁.chi) :
    OperatorialJonesDatum Op where
  chi := J₁.chi
  transform := fun x => J₂.transform (J₁.transform x)
  acts_projectively := by
    intro P hP
    exact J₂.acts_projectively (J₁.transform P) (J₁.acts_projectively P hP)
  kind := JonesSurfaceKind.abstractTransport
  coherence_law := J₁.coherence_law ∧ J₂.coherence_law
  coherent := ⟨J₁.coherent, J₂.coherent⟩

end OperatorialJonesDatum

/-! ## 3. Branch datums -/

/--
Jones transport that preserves the chiral/polarization axis.

Examples include ordinary diagonal dielectric reflection away from
sector-mixing interfaces.
-/
structure ChiralityPreservingJonesDatum
    (Op : Type*) [Mul Op] where
  base : OperatorialJonesDatum Op
  preserves_chirality :
    PreservesChirality base.chi base.transform

namespace ChiralityPreservingJonesDatum

variable {Op : Type*} [Mul Op]

/-- Re-export chirality preservation as a theorem-usable proof. -/
theorem preserves_apply
    (J : ChiralityPreservingJonesDatum Op)
    (x : Op) :
    J.base.transform (J.base.chi * x) = J.base.chi * J.base.transform x :=
  J.preserves_chirality x

end ChiralityPreservingJonesDatum

/--
Jones transport that flips the chiral/polarization axis.

This is the socket for mirror/CPT-type or propagation-handedness flips.
-/
structure ChiralityFlippingJonesDatum
    (Op : Type*) [Mul Op] [Neg Op] where
  base : OperatorialJonesDatum Op
  flips_chirality :
    FlipsChirality base.chi base.transform

namespace ChiralityFlippingJonesDatum

variable {Op : Type*} [Mul Op] [Neg Op]

/-- Re-export chirality flipping as a theorem-usable proof. -/
theorem flips_apply
    (J : ChiralityFlippingJonesDatum Op)
    (x : Op) :
    J.base.transform (J.base.chi * x) = -(J.base.chi * J.base.transform x) :=
  J.flips_chirality x

end ChiralityFlippingJonesDatum

/--
Jones transport with a Krein/J-unitary calibration.

This should be used only for the CPT/Krein branch. Ordinary polarizers and
lossy mirrors should not be forced into this structure.
-/
structure JUnitaryCalibratedJonesDatum
    (Op : Type*) [Mul Op] where
  base : OperatorialJonesDatum Op
  junitary_law : Prop
  junitary_calibration : junitary_law

namespace JUnitaryCalibratedJonesDatum

variable {Op : Type*} [Mul Op]

/-- Re-export the supplied J-unitary calibration certificate. -/
theorem calibration_holds
    (J : JUnitaryCalibratedJonesDatum Op) :
    J.junitary_law :=
  J.junitary_calibration

end JUnitaryCalibratedJonesDatum

/-! ## 4. Surface operators -/

/--
A Brewster surface is projective but non-unitary: it collapses to a sector.
-/
structure BrewsterSurfaceDatum
    (Op : Type*) [Mul Op] where
  base : ChiralityPreservingJonesDatum Op
  rank_collapse_law : Prop
  rank_collapse : rank_collapse_law

namespace BrewsterSurfaceDatum

variable {Op : Type*} [Mul Op]

/-- Re-export the supplied rank-collapse certificate. -/
theorem rank_collapse_holds
    (B : BrewsterSurfaceDatum Op) :
    B.rank_collapse_law :=
  B.rank_collapse

end BrewsterSurfaceDatum

/--
Total internal reflection is a lossless phase-retarder branch.
-/
structure TotalInternalReflectionDatum
    (Op : Type*) [Mul Op] where
  base : JUnitaryCalibratedJonesDatum Op
  phase_retarder_law : Prop
  phase_retarder : phase_retarder_law

namespace TotalInternalReflectionDatum

variable {Op : Type*} [Mul Op]

/-- Re-export the supplied phase-retarder certificate. -/
theorem phase_retarder_holds
    (T : TotalInternalReflectionDatum Op) :
    T.phase_retarder_law :=
  T.phase_retarder

end TotalInternalReflectionDatum

/--
Metal mirrors are generally lossy complex retarders: not automatically
J-unitary and not automatically chirality-preserving.
-/
structure MetalMirrorDatum
    (Op : Type*) [Mul Op] where
  base : OperatorialJonesDatum Op
  lossy_retarder_law : Prop
  lossy_retarder : lossy_retarder_law

namespace MetalMirrorDatum

variable {Op : Type*} [Mul Op]

/-- Re-export the supplied lossy-retarder certificate. -/
theorem lossy_retarder_holds
    (M : MetalMirrorDatum Op) :
    M.lossy_retarder_law :=
  M.lossy_retarder

end MetalMirrorDatum

/--
Chiral media are Cartan-diagonal in the circular basis, with possible
birefringence or dichroism.
-/
structure ChiralMediumDatum
    (Op : Type*) [Mul Op] where
  base : OperatorialJonesDatum Op
  circular_cartan_law : Prop
  circular_cartan : circular_cartan_law

namespace ChiralMediumDatum

variable {Op : Type*} [Mul Op]

/-- Re-export the supplied circular-Cartan certificate. -/
theorem circular_cartan_holds
    (C : ChiralMediumDatum Op) :
    C.circular_cartan_law :=
  C.circular_cartan

end ChiralMediumDatum

end InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus
