import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.Pin55TopologicalGroups

/-!
# The topological compatibility of the two split Pin carriers

The algebra equivalence between the two Clifford presentations induces a
homeomorphism between the corresponding subgroup carriers.  This file keeps
that topological statement separate from the algebraic `MulEquiv` and from
the (different) `pinGroup` submonoids in Mathlib.
-/

noncomputable section

namespace InfoGeometry.Topology.Pin55TopologicalGroups

open CliffordAlgebra
open InfoGeometry.Clifford.Clifford55

theorem continuous_oppositeToPlus :
    Continuous (oppositeToPlus : Cl55Opposite → CliffordAlgebra Q55) :=
  oppositeToPlus.toLinearMap.continuous_of_finiteDimensional

theorem continuous_plusToOpposite :
    Continuous (oppositeToPlus.symm : CliffordAlgebra Q55 → Cl55Opposite) :=
  oppositeToPlus.symm.toLinearMap.continuous_of_finiteDimensional

theorem continuous_oppositeUnitsToPlus :
    Continuous (fun g : Cl55Oppositeˣ => oppositeUnitsToPlus g) := by
  have hbase : Continuous
      (oppositeToPlus.toRingEquiv.toMonoidHom :
        Cl55Opposite → CliffordAlgebra Q55) := by
    exact continuous_oppositeToPlus
  simpa [oppositeUnitsToPlus] using Units.continuous_map hbase

theorem continuous_plusUnitsToOpposite :
    Continuous
      (fun g : (CliffordAlgebra Q55)ˣ =>
        Units.map oppositeToPlus.symm.toRingEquiv.toMonoidHom g) := by
  have hbase : Continuous
      (oppositeToPlus.symm.toRingEquiv.toMonoidHom :
        CliffordAlgebra Q55 → Cl55Opposite) := by
    exact continuous_plusToOpposite
  exact Units.continuous_map hbase

theorem continuous_pinMinus55ToPlus :
    Continuous (pinMinus55ToPlus : PinMinus55 → PinPlus55) := by
  apply Continuous.subtype_mk
  exact continuous_oppositeUnitsToPlus.comp continuous_subtype_val

theorem continuous_pinPlus55ToMinus :
    Continuous (pinPlus55ToMinus : PinPlus55 → PinMinus55) := by
  apply Continuous.subtype_mk
  exact continuous_plusUnitsToOpposite.comp continuous_subtype_val

noncomputable def pinMinus55HomeomorphPlus : PinMinus55 ≃ₜ PinPlus55 where
  toFun := pinMinus55ToPlus
  invFun := pinPlus55ToMinus
  left_inv := pinMinus55ToPlus_leftInverse
  right_inv := pinMinus55ToPlus_rightInverse
  continuous_toFun := continuous_pinMinus55ToPlus
  continuous_invFun := continuous_pinPlus55ToMinus

@[simp] theorem pinMinus55HomeomorphPlus_apply (g : PinMinus55) :
    pinMinus55HomeomorphPlus g = pinMinus55ToPlus g :=
  rfl

theorem pinMinus55HomeomorphPlus_mul (g h : PinMinus55) :
    pinMinus55HomeomorphPlus (g * h) =
      pinMinus55HomeomorphPlus g * pinMinus55HomeomorphPlus h := by
  exact map_mul pinMinus55ToPlus g h

theorem pinMinus55HomeomorphPlus_one :
    pinMinus55HomeomorphPlus (1 : PinMinus55) = 1 := by
  exact map_one pinMinus55ToPlus

theorem pinMinus55HomeomorphPlus_eq_mulEquiv (g : PinMinus55) :
    pinMinus55HomeomorphPlus g = pinMinus55EquivPlus g := by
  rfl

end InfoGeometry.Topology.Pin55TopologicalGroups
