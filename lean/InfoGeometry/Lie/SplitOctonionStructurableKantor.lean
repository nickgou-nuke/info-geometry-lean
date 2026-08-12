import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension
import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import InfoGeometry.Algebra.Zorn.CanonicalKantorOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option maxHeartbeats 3000000

/-!
# Native structurable/Kantor polynomial operators on the Zorn carrier

This file records the concrete operators used in the structurable-to-Kantor
construction.  It does not assume that the canonical Zorn product is already
structurable, and it does not package Kantor identities as fields.  Those
identities remain obligations for a later direct computation.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionStructurableKantor

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.CanonicalKantorOperators
open InfoGeometry.Lie.SplitOctonionImaginaryAction

abbrev CZ := CanonicalZorn

/-! ## The native conjugation facts used by the polynomial operators -/

@[simp] theorem canonicalConj_involutive (X : CZ) :
    canonicalConj (canonicalConj X) = X := by
  apply canonicalVectorEquiv.injective
  rw [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_canonicalConj,
    InfoGeometry.Algebra.ZornVectorMatrix.conj_conj]

theorem canonicalConj_mul (X Y : CZ) :
    canonicalConj (X * Y) = canonicalConj Y * canonicalConj X := by
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_mul]
  rw [InfoGeometry.Algebra.ZornVectorMatrix.conj_mul]

@[simp] theorem canonicalConj_one :
    canonicalConj (1 : CZ) = 1 := by
  apply canonicalVectorEquiv.injective
  rw [canonicalVectorEquiv_canonicalConj, canonicalVectorEquiv_one]
  ext i <;>
    simp [InfoGeometry.Algebra.ZornVectorMatrix.one,
      InfoGeometry.Algebra.ZornVectorMatrix.conj]

/-! ## The actual structurable/Kantor polynomial operators -/

/-- The structurable operator polynomial

`V x y z = (x * conj y) * z + (z * conj y) * x -
  (z * conj x) * y`.

The definition is intentionally literal: no structurable identity is assumed.
-/
noncomputable def canonicalV (x y z : CZ) : CZ :=
  (x * canonicalConj y) * z + (z * canonicalConj y) * x -
    (z * canonicalConj x) * y

/-- The associated Kantor `K` polynomial, with the convention
`K x y z = V x z y - V y z x`. -/
noncomputable def canonicalK (x y z : CZ) : CZ :=
  canonicalV x z y - canonicalV y z x

/-! The two concrete owners use the same native polynomial source.  These
bridges keep the older `canonicalV`/`canonicalK` names available while making
the equality with the canonical operator owner explicit. -/

theorem canonicalV_eq_nativeV (x y z : CZ) :
    canonicalV x y z = V x y z :=
  rfl

theorem canonicalK_eq_nativeK (x y z : CZ) :
    canonicalK x y z = K x y z :=
  rfl

theorem canonicalK_swap (x y z : CZ) :
    canonicalK y x z = -canonicalK x y z := by
  unfold canonicalK
  module

theorem canonicalK_self (x z : CZ) :
    canonicalK x x z = 0 := by
  unfold canonicalK
  module

end InfoGeometry.Lie.SplitOctonionStructurableKantor
