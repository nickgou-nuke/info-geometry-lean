import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.SpecialLinearGroup
import InfoGeometry.Physics.LorentzChiralCuntzBridge

/-!
# Realification of the finite chiral Lorentz representation

The existing Lorentz owner uses `SL(2,ℂ)` as the spin group.  This file
realifies its canonical two-component complex spinor action, landing in the
native Mathlib general linear group, which is definitionally a group of units
of `Module.End ℝ`.
-/

noncomputable section

namespace InfoGeometry.Physics.RealSpinorLorentzRepresentation

open InfoGeometry.Physics.LorentzChiralCuntzBridge

abbrev Spinor := InfoGeometry.Algebra.FiniteSpin.Vec2C
abbrev RealSpinorUnits := LinearMap.GeneralLinearGroup ℝ Spinor

def realSpinorRepresentation : SL2C →* RealSpinorUnits where
  toFun g :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv
      ((Matrix.SpecialLinearGroup.toLin' g).restrictScalars ℝ)
  map_one' := by
    ext v i
    simp
  map_mul' := by
    intro g h
    ext v i
    simp [Matrix.SpecialLinearGroup.toLin']

@[simp] theorem realSpinorRepresentation_apply (g : SL2C) (v : Spinor) :
    (realSpinorRepresentation g : Spinor → Spinor) v =
      Matrix.mulVec (spinMatrix g) v := by
  rfl

end InfoGeometry.Physics.RealSpinorLorentzRepresentation
