import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyParityKleinComparisonBridge

/-!
# Native action of endomorphism units on the coordinate carrier

The units of `Module.End ℝ Coord` act on `Coord` by evaluation of their
underlying endomorphism.  This is the genuine `MulAction` layer used by the
two Klein subgroup packets.  It is purely algebraic and makes no claim about
continuity, Hilbert completion, or physical symmetry.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyUnitActionBridge

abbrev Coord :=
  InfoGeometry.Canonical.CayleyPeirceKleinFourBridge.Coord
abbrev CoordEnd :=
  InfoGeometry.Canonical.CayleyPeirceKleinFourBridge.CoordEnd

instance : SMul CoordEndˣ Coord where
  smul u x := u.val x

instance : MulAction CoordEndˣ Coord where
  one_smul x := by rfl
  mul_smul u v x := by rfl

@[simp] theorem unit_smul_eq_val (u : CoordEndˣ) (x : Coord) :
    u • x = u.val x := rfl

theorem parityKleinSubgroup_smul_def
    (u : InfoGeometry.Canonical.CayleyParityUnitsBridge.parityKleinSubgroup)
    (x : Coord) :
    u • x = (u : CoordEndˣ).val x := rfl

theorem cayleyDualityKleinSubgroup_smul_def
    (u : InfoGeometry.Canonical.CayleyDualityUnitsBridge.cayleyDualityKleinSubgroup)
    (x : Coord) :
    u • x = (u : CoordEndˣ).val x := rfl

/-!
The subgroup actions below are restrictions of the ambient unit action.  They
do not introduce a second operator action: the subtype coercion is the only
transport, so the multiplication and identity laws are inherited directly
from `CoordEndˣ`.
-/

instance : SMul
    InfoGeometry.Canonical.CayleyParityUnitsBridge.parityKleinSubgroup Coord where
  smul u x := (u : CoordEndˣ) • x

instance : MulAction
    InfoGeometry.Canonical.CayleyParityUnitsBridge.parityKleinSubgroup Coord where
  one_smul x := by rfl
  mul_smul u v x := by rfl

instance : SMul
    InfoGeometry.Canonical.CayleyDualityUnitsBridge.cayleyDualityKleinSubgroup Coord where
  smul u x := (u : CoordEndˣ) • x

instance : MulAction
    InfoGeometry.Canonical.CayleyDualityUnitsBridge.cayleyDualityKleinSubgroup Coord where
  one_smul x := by rfl
  mul_smul u v x := by rfl

@[simp] theorem parity_subgroup_smul_eq_ambient
    (u : InfoGeometry.Canonical.CayleyParityUnitsBridge.parityKleinSubgroup)
    (x : Coord) :
    u • x = (u : CoordEndˣ) • x := rfl

@[simp] theorem cayley_duality_subgroup_smul_eq_ambient
    (u : InfoGeometry.Canonical.CayleyDualityUnitsBridge.cayleyDualityKleinSubgroup)
    (x : Coord) :
    u • x = (u : CoordEndˣ) • x := rfl

end InfoGeometry.Canonical.CayleyUnitActionBridge
