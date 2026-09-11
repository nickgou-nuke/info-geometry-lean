/-
InfoGeometry/Geometry/OperatorialJonesConnection.lean

Operatorial Jones calculus.

Jones calculus is lifted from vector transport to projective-operator transport:

  P ↦ U P U⁻¹.

This is the low-dimensional CP1 / polarization connection layer.  It is not
itself the Poincare metric or the KMS theorem.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Geometry.OperatorialJonesConnection

/-! ## 1. Inner conjugation and projectors -/

/-- Algebraic projector. -/
def IsProjector
    {Op : Type*} [Monoid Op]
    (P : Op) : Prop :=
  P * P = P

/-- The inner conjugation action `P ↦ U P U⁻¹`. -/
def conjugationAction
    {Op : Type*} [Monoid Op]
    (U : Units Op)
    (P : Op) : Op :=
  U.val * P * (U⁻¹ : Units Op).val

/-- Inner conjugation carries products to products. -/
theorem conjugationAction_mul
    {Op : Type*} [Monoid Op]
    (U : Units Op) (P Q : Op) :
    conjugationAction U (P * Q) =
      conjugationAction U P * conjugationAction U Q := by
  simp [conjugationAction, mul_assoc]

/-- Idempotents are preserved by inner automorphisms. -/
theorem isProjector_conjugationAction
    {Op : Type*} [Monoid Op]
    (U : Units Op) {P : Op} (hP : IsProjector P) :
    IsProjector (conjugationAction U P) := by
  rw [IsProjector, ← conjugationAction_mul, hP]

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

/-- Preserve-or-reverse normalizer relation for the Cartan axis. -/
def NormalizesCartanAxis
    {Op : Type*} [Monoid Op] [Neg Op]
    (chi U : Op) : Prop :=
  PreservesCartanAxis chi U ∨ ReversesCartanAxis chi U

/-! ## 3. Operatorial Jones transport -/

/--
Operatorial Jones transport.

This packages a Jones-like unit `U` acting on polarization projectors by
conjugation.

For ordinary lossless optics, `U` may be unitary.  For the doubled Krein layer,
one should supply a separate `J`-unitarity certificate.
-/
abbrev OperatorialJonesTransport
    (Op : Type*) [Ring Op]
    (C : ChiralCartanProjectors Op) :=
  {U : Units Op // NormalizesCartanAxis C.chi U.val}

/-- A Jones transport is sector-preserving when it commutes with the Cartan axis. -/
abbrev SectorPreservingJonesTransport
    (Op : Type*) [Ring Op]
    (C : ChiralCartanProjectors Op) :=
  {U : Units Op // PreservesCartanAxis C.chi U.val}

/-- A Jones transport is sector-flipping when it anticommutes with the Cartan axis. -/
abbrev SectorFlippingJonesTransport
    (Op : Type*) [Ring Op]
    (C : ChiralCartanProjectors Op) :=
  {U : Units Op // ReversesCartanAxis C.chi U.val}

namespace OperatorialJonesTransport

variable {Op : Type*} [Ring Op]
variable {C : ChiralCartanProjectors Op}
variable (J : OperatorialJonesTransport Op C)

/-- Underlying invertible Jones operator. -/
def U : Units Op :=
  J.1

/-- The Jones unit normalizes the Cartan axis. -/
theorem cartan_behavior :
    PreservesCartanAxis C.chi J.U.val ∨
      ReversesCartanAxis C.chi J.U.val :=
  J.2

/-- Re-export projective preservation by Jones conjugation. -/
theorem maps_projector
    {P : Op}
    (hP : IsProjector P) :
    IsProjector (conjugationAction J.U P) :=
  isProjector_conjugationAction J.U hP

end OperatorialJonesTransport

end InfoGeometry.Geometry.OperatorialJonesConnection
