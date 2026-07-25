/-
InfoGeometry/Geometry/OperatorialJonesConnection.lean

Operatorial Jones calculus.

Jones calculus is lifted from vector transport to projective-operator transport:

  P ↦ U P U†.

This is the low-dimensional CP1 / polarization connection layer.  It is not
itself the Poincare metric or the KMS theorem.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Geometry.OperatorialJonesConnection

/-! ## 1. Abstract adjoint and projectors -/

/-- Minimal adjoint datum on an operator algebra. -/
structure AdjointDatum
    (Op : Type*) [Monoid Op] where
  /-- Abstract adjoint operation. -/
  adj : Op → Op

/-- Algebraic projector. -/
def IsProjector
    {Op : Type*} [Monoid Op]
    (P : Op) : Prop :=
  P * P = P

/-- Conjugation action `P ↦ U P U†`. -/
def conjugationAction
    {Op : Type*} [Monoid Op]
    (Adj : AdjointDatum Op)
    (U : Units Op)
    (P : Op) : Op :=
  U.val * P * Adj.adj U.val

/-! ## 2. Chiral/Cartan projectors -/

/--
A chiral Cartan projector datum.

`chi` is the Cartan eigenoperator.  `PL` and `PR` are the two pole projectors.
-/
structure ChiralCartanProjectors
    (Op : Type*) [Ring Op] where
  /-- Cartan/chiral eigenoperator. -/
  chi : Op

  /-- Left/north-pole projector. -/
  PL : Op

  /-- Right/south-pole projector. -/
  PR : Op

  /-- `chi² = 1`. -/
  chi_square :
    chi * chi = 1

  /-- Left projector is idempotent. -/
  PL_idem :
    IsProjector PL

  /-- Right projector is idempotent. -/
  PR_idem :
    IsProjector PR

  /-- The two pole projectors are complementary. -/
  complementary :
    PL + PR = 1

  /-- Left then right vanishes. -/
  disjoint_left :
    PL * PR = 0

  /-- Right then left vanishes. -/
  disjoint_right :
    PR * PL = 0

/-- A transport preserves the Cartan/chiral axis if it commutes with `chi`. -/
def PreservesCartanAxis
    {Op : Type*} [Monoid Op]
    (chi U : Op) : Prop :=
  U * chi = chi * U

/-- A transport reverses the Cartan/chiral axis if it anticommutes with `chi`. -/
def ReversesCartanAxis
    {Op : Type*} [Monoid Op] [Neg Op]
    (chi U : Op) : Prop :=
  U * chi = -(chi * U)

/-! ## 3. Operatorial Jones transport -/

/--
Operatorial Jones transport.

This packages a Jones-like unit `U` acting on polarization projectors by
conjugation.

For ordinary lossless optics, `U` may be unitary.  For the doubled Krein layer,
one should supply a separate `J`-unitarity certificate.
-/
structure OperatorialJonesTransport
    (Op : Type*) [Ring Op]
    (Adj : AdjointDatum Op)
    (C : ChiralCartanProjectors Op) where
  /-- Jones transport unit. -/
  U : Units Op

  /-- Transport preserves projectors. -/
  maps_projectors_to_projectors :
    ∀ P : Op,
      IsProjector P →
        IsProjector (conjugationAction Adj U P)

  /-- The Jones transport either preserves or reverses the Cartan axis. -/
  cartan_behavior :
    PreservesCartanAxis C.chi U.val ∨
    ReversesCartanAxis C.chi U.val

/-- A Jones transport is sector-preserving when it commutes with the Cartan axis. -/
structure SectorPreservingJonesTransport
    (Op : Type*) [Ring Op]
    (Adj : AdjointDatum Op)
    (C : ChiralCartanProjectors Op)
    extends OperatorialJonesTransport Op Adj C where
  /-- Sector-preserving branch certificate. -/
  preserves_axis :
    PreservesCartanAxis C.chi U.val

/-- A Jones transport is sector-flipping when it anticommutes with the Cartan axis. -/
structure SectorFlippingJonesTransport
    (Op : Type*) [Ring Op]
    (Adj : AdjointDatum Op)
    (C : ChiralCartanProjectors Op)
    extends OperatorialJonesTransport Op Adj C where
  /-- Sector-flipping branch certificate. -/
  reverses_axis :
    ReversesCartanAxis C.chi U.val

namespace OperatorialJonesTransport

variable {Op : Type*} [Ring Op]
variable {Adj : AdjointDatum Op}
variable {C : ChiralCartanProjectors Op}
variable (J : OperatorialJonesTransport Op Adj C)

/-- Re-export projective preservation by Jones conjugation. -/
theorem maps_projector
    {P : Op}
    (hP : IsProjector P) :
    IsProjector (conjugationAction Adj J.U P) :=
  J.maps_projectors_to_projectors P hP

end OperatorialJonesTransport

end InfoGeometry.Geometry.OperatorialJonesConnection
