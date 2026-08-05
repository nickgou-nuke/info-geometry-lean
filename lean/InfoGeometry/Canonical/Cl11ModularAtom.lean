import InfoGeometry.Canonical.Cl11LorentzAction
import InfoGeometry.Canonical.TransportLieDerivative
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.Cl11ModularAtom

Split `Cl(1,1)` modular atom on the doubled real carrier.

This file packages the existing modular-CPT compatibility surface as a thin
compatibility wrapper:

* the underlying operator atom is `ModularCPTChiralAtom`;
* the derived axis is the typed `KAxis`;
* CPT invariance, scale/shape split compatibility, and related package-level
  properties are named as theorem-level obligations, not proof fields.

It does not assert any prime-number, Lee--Yang, xi, or RH theorem.
-/

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.Cl11ModularAtomPacket

open InfoGeometry.Canonical

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Compatibility wrapper for the split `Cl(1,1)` modular atom.

The underlying algebraic core is the existing `ModularCPTChiralAtom`.  This
packet names the modular/CPT propositions used by the scale/shape and
wavelet-lane bridges.  Their certificates live in separate theorems.
-/
@[rep_depth transport]
abbrev Cl11ModularAtom (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  ModularCPTChiralAtom E

namespace Cl11ModularAtom

abbrev atom (A : Cl11ModularAtom E) : ModularCPTChiralAtom E := A

/-- The axis is derived from the canonical modular atom, not stored as a
separate evidence field. -/
abbrev axis (A : Cl11ModularAtom E) : KAxis E :=
  A.toKAxis

@[simp] theorem axis_eq (A : Cl11ModularAtom E) :
    A.axis = A.toKAxis :=
  rfl

/-- The derived typed `K`-axis is the one extracted from the modular atom. -/
@[rep_depth transport]
theorem axis_eq_toKAxis
    (A : Cl11ModularAtom E) :
    A.axis = A.toKAxis :=
  A.axis_eq

/-- The modular atom carries a square-minus-one axis. -/
@[rep_depth transport]
theorem axis_square_neg_one
    (A : Cl11ModularAtom E) :
    A.axis.K * A.axis.K =
      -(1 : InfoGeometry.Krein.NeutralSpace E →L[ℝ] InfoGeometry.Krein.NeutralSpace E) := by
  rw [A.axis_eq]
  exact A.K_sq_neg_one_eq

end Cl11ModularAtom

end Core

end InfoGeometry.Canonical.Cl11ModularAtomPacket
