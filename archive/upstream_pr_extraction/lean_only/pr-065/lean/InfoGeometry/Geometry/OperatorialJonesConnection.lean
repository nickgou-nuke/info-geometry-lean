/-
InfoGeometry/Geometry/OperatorialJonesConnection.lean

Operatorial Jones calculus.

Jones calculus is lifted from vector transport to projective-operator transport:

  P ↦ U P U⁻¹.

This is the low-dimensional CP1 / polarization connection layer.  It is not
itself the Poincare metric or the KMS theorem.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Geometry.OperatorialJonesConnection

/-! ## 1. Inner conjugation and projectors -/

/-- Algebraic projector. -/
abbrev IsProjector
    {Op : Type*} [Monoid Op]
    (P : Op) : Prop :=
  IsIdempotentElem P

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
  change conjugationAction U P * conjugationAction U P = conjugationAction U P
  rw [← conjugationAction_mul, hP]

/-! ## 2. Chiral/Cartan projectors -/

/--
A chiral Cartan projector datum.

`chi` is the Cartan eigenoperator.  `PL` and `PR` are the two pole projectors.
-/
abbrev ChiralCartanProjectors
    (Op : Type*) [Ring Op] :=
  {p : Op × (Op × Op) //
    p.1 * p.1 = 1 ∧
      IsProjector p.2.1 ∧
      IsProjector p.2.2 ∧
      p.2.1 + p.2.2 = 1 ∧
      p.2.1 * p.2.2 = 0 ∧
      p.2.2 * p.2.1 = 0}

namespace ChiralCartanProjectors

variable {Op : Type*} [Ring Op]

abbrev chi (C : ChiralCartanProjectors Op) : Op := C.1.1
abbrev PL (C : ChiralCartanProjectors Op) : Op := C.1.2.1
abbrev PR (C : ChiralCartanProjectors Op) : Op := C.1.2.2
abbrev chi_square (C : ChiralCartanProjectors Op) : C.chi * C.chi = 1 := C.2.1
abbrev PL_idem (C : ChiralCartanProjectors Op) : IsProjector C.PL := C.2.2.1
abbrev PR_idem (C : ChiralCartanProjectors Op) : IsProjector C.PR := C.2.2.2.1
abbrev complementary (C : ChiralCartanProjectors Op) : C.PL + C.PR = 1 := C.2.2.2.2.1
abbrev disjoint_left (C : ChiralCartanProjectors Op) : C.PL * C.PR = 0 := C.2.2.2.2.2.1
abbrev disjoint_right (C : ChiralCartanProjectors Op) : C.PR * C.PL = 0 := C.2.2.2.2.2.2

end ChiralCartanProjectors

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
one should supply a separate `J`-unitarity property.
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
