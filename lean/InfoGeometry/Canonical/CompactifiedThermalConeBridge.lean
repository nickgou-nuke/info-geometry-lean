import InfoGeometry.Canonical.StandardFormNaturalConeBridge
import InfoGeometry.Canonical.ThermalCompactRecurrence
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.CompactifiedThermalConeBridge

Witness-gated carrier for compactified thermal operators on the standard-form
natural cone.

This file does not construct a Type III factor, a Tomita--Takesaki standard
form, or an actual functional-calculus Cayley transform.  It packages the exact
cone-preservation statement the compactified operator must satisfy once such a
carrier is supplied.
-/

namespace CompactifiedThermalConeBridge

open InfoGeometry.Canonical.StandardFormNaturalConeBridge

/--
A compactified thermal operator acting on the standard-form natural cone.

The operator is intentionally abstract.  The only theorem-facing requirement is
that it preserve the supplied natural cone.
-/
@[rep_depth operator]
structure CompactifiedThermalConeCarrier
    (Alg Hilb NormalPositive : Type*) where
  /-- Standard-form natural-cone carrier. -/
  standardForm : NaturalConeStandardFormInterface Alg Hilb NormalPositive

  /-- Compactified thermal operator acting on the Hilbert carrier. -/
  compactifiedOperator : Hilb → Hilb

  /-- Cone preservation witness for the compactified thermal operator. -/
  compactifiedOperator_preserves_cone :
    ∀ ξ : Hilb, ξ ∈ standardForm.cone → compactifiedOperator ξ ∈ standardForm.cone

namespace CompactifiedThermalConeCarrier

variable {Alg Hilb NormalPositive : Type*}
variable (C : CompactifiedThermalConeCarrier Alg Hilb NormalPositive)

/--
The compactified thermal operator preserves the cone-vector representative of
any normal positive functional.
-/
@[rep_depth operator]
theorem compactifiedOperator_coneVector
    (ω : NormalPositive)
    (hω : C.standardForm.isNormalPositive ω) :
    C.compactifiedOperator (C.standardForm.coneVector ω) ∈ C.standardForm.cone := by
  exact
    C.compactifiedOperator_preserves_cone
      (C.standardForm.coneVector ω)
      (NaturalConeStandardFormInterface.coneVector_mem_of_normal C.standardForm ω hω)

/--
The Tomita reflection still fixes the cone-vector representative.
-/
@[rep_depth operator]
theorem J_fixes_coneVector
    (ω : NormalPositive)
    (hω : C.standardForm.isNormalPositive ω) :
    C.standardForm.J (C.standardForm.coneVector ω) = C.standardForm.coneVector ω :=
  NaturalConeStandardFormInterface.J_fixes_coneVector C.standardForm ω hω

end CompactifiedThermalConeCarrier

end CompactifiedThermalConeBridge
