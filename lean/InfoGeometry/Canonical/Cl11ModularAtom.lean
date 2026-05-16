import InfoGeometry.Canonical.Cl11LorentzAction
import InfoGeometry.Canonical.TransportLieDerivative
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.Cl11ModularAtom

Split `Cl(1,1)` modular atom on the doubled real carrier.

This file packages the existing modular-CPT witness surface as a thin
compatibility wrapper:

* the underlying operator atom is `ModularCPTChiralAtom`;
* the derived axis is the typed `KAxis`;
* CPT invariance, scale/shape split compatibility, and related package-level
  properties remain explicit witnesses.

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
packet adds explicit witness fields for the modular/CPT interpretation used by
the scale/shape and wavelet-lane bridges.
-/
@[rep_depth transport]
structure Cl11ModularAtom (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  atom : ModularCPTChiralAtom E
  axis : KAxis E
  axis_eq : axis = atom.toKAxis

  /-- CPT invariance of the modular atom, stored as a witness field. -/
  cptInvariant : Prop
  cptInvariant_certificate : cptInvariant

  /-- Scale/shape compatibility of the modular atom, stored as a witness field. -/
  scaleShapeSplit : Prop
  scaleShapeSplit_certificate : scaleShapeSplit

/-- Re-export of the CPT-invariance witness. -/
@[rep_depth transport]
theorem cptInvariant_law
    (A : Cl11ModularAtom E) :
    A.cptInvariant :=
  A.cptInvariant_certificate

/-- Re-export of the scale/shape compatibility witness. -/
@[rep_depth transport]
theorem scaleShapeSplit_law
    (A : Cl11ModularAtom E) :
    A.scaleShapeSplit :=
  A.scaleShapeSplit_certificate

/-- The derived typed `K`-axis is the one extracted from the modular atom. -/
@[rep_depth transport]
theorem axis_eq_toKAxis
    (A : Cl11ModularAtom E) :
    A.axis = A.atom.toKAxis :=
  A.axis_eq

/-- The modular atom carries a square-minus-one axis. -/
@[rep_depth transport]
theorem axis_square_neg_one
    (A : Cl11ModularAtom E) :
    A.axis.K * A.axis.K =
      -(1 : InfoGeometry.Krein.NeutralSpace E →L[ℝ] InfoGeometry.Krein.NeutralSpace E) := by
  rw [A.axis_eq]
  exact A.atom.K_sq_neg_one_eq

end Core

end InfoGeometry.Canonical.Cl11ModularAtomPacket
