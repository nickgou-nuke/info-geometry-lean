import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

/-! ## Projective Jones transports -/

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

/-- Optional classification of surface/operator type. -/
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

/--
Generic operatorial Jones transport.

This interface only carries the actual projective action proof. Coherence,
unitarity, or metric admissibility must be supplied by a concrete owner layer,
not by an arbitrary proof field on the generic transport.
-/
structure OperatorialJonesDatum
    (Op : Type*) [Mul Op] where
  /-- Chiral grading or polarization axis. -/
  chi : Op
  /-- Jones transport on the operator algebra. -/
  transform : Op → Op
  /-- Projective action proof. -/
  acts_projectively : ActsProjectively transform
  /-- Surface/transport classification. -/
  kind : JonesSurfaceKind

namespace OperatorialJonesDatum

variable {Op : Type*} [Mul Op]

/-- Apply the Jones transport to an operator. -/
def apply
    (J : OperatorialJonesDatum Op)
    (x : Op) : Op :=
  J.transform x

/-- Projective transports map projectors to projectors. -/
theorem maps_projectors
    (J : OperatorialJonesDatum Op)
    (P : Op)
    (hP : IsProjector P) :
    IsProjector (J.apply P) :=
  J.acts_projectively P hP

/-- Composition of two Jones transports with the same chiral axis. -/
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

end OperatorialJonesDatum

/-- Jones transport that preserves the chiral/polarization axis. -/
structure ChiralityPreservingJonesDatum
    (Op : Type*) [Mul Op] where
  base : OperatorialJonesDatum Op
  preserves_chirality : PreservesChirality base.chi base.transform

namespace ChiralityPreservingJonesDatum

variable {Op : Type*} [Mul Op]

/-- Re-export chirality preservation as a theorem-usable proof. -/
theorem preserves_apply
    (J : ChiralityPreservingJonesDatum Op)
    (x : Op) :
    J.base.transform (J.base.chi * x) = J.base.chi * J.base.transform x :=
  J.preserves_chirality x

end ChiralityPreservingJonesDatum

/-- Jones transport that flips the chiral/polarization axis. -/
structure ChiralityFlippingJonesDatum
    (Op : Type*) [Mul Op] [Neg Op] where
  base : OperatorialJonesDatum Op
  flips_chirality : FlipsChirality base.chi base.transform

namespace ChiralityFlippingJonesDatum

variable {Op : Type*} [Mul Op] [Neg Op]

/-- Re-export chirality flipping as a theorem-usable proof. -/
theorem flips_apply
    (J : ChiralityFlippingJonesDatum Op)
    (x : Op) :
    J.base.transform (J.base.chi * x) = -(J.base.chi * J.base.transform x) :=
  J.flips_chirality x

end ChiralityFlippingJonesDatum

end InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus
