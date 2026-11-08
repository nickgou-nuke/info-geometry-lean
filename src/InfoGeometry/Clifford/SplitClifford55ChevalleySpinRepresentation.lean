import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55ChevalleySpinorActionBridge

/-!
# Native spin representation on the split Chevalley carrier

This owner restricts the already constructed algebra representation of the
split vector/covector Clifford algebra to Mathlib's native `spinGroup`.
The carrier is `ExteriorAlgebra ℝ (Fin 5 → ℝ)`, so its dimension is the
expected finite exterior-spinor dimension.  The construction is a genuine
group representation obtained with `Units.map` and `spinGroup.toUnits`.

The split quadratic form here is the Chevalley vector/covector form
`splitQ`; this file deliberately does not identify it with the separate
coordinate definition `Q55`, nor with a particular 32×32 matrix basis.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55ChevalleySpinRepresentation

open InfoGeometry.Lie.ChevalleySpinor
open InfoGeometry.Clifford.Cl55ChevalleySpinorActionBridge

abbrev W5 := InfoGeometry.Algebra.FiniteSpin.Vec5R
abbrev SplitCarrier55 := SplitV ℝ W5
abbrev SpinorCarrier55 := SpinorSpace ℝ W5
abbrev CliffordCarrier55 := CliffordAlgebra (splitQ (R := ℝ) (W := W5))
abbrev Spin55 := spinGroup (splitQ (R := ℝ) (W := W5))
abbrev SpinorEnd55 := Module.End ℝ SpinorCarrier55

/-! The algebra representation used to construct the group action. -/

noncomputable abbrev chevalleyRepresentation :
    CliffordCarrier55 →ₐ[ℝ] SpinorEnd55 :=
  chevalleySpinorRep

/-! Restriction to the native spin group. -/

noncomputable def spinorRepresentation :
    Spin55 →* LinearMap.GeneralLinearGroup ℝ SpinorCarrier55 :=
  (Units.map chevalleyRepresentation.toRingHom.toMonoidHom).comp
    spinGroup.toUnits

theorem spinorRepresentation_val (g : Spin55) :
    ((spinorRepresentation g : LinearMap.GeneralLinearGroup ℝ SpinorCarrier55) :
        SpinorEnd55) =
      chevalleyRepresentation (g : CliffordCarrier55) := by
  rfl

theorem spinorRepresentation_mul (g h : Spin55) :
    spinorRepresentation (g * h) =
      spinorRepresentation g * spinorRepresentation h := by
  exact map_mul (spinorRepresentation) g h

theorem spinorRepresentation_inv (g : Spin55) :
    spinorRepresentation g⁻¹ = (spinorRepresentation g)⁻¹ := by
  exact map_inv (spinorRepresentation) g

theorem spinorRepresentation_one :
    spinorRepresentation (1 : Spin55) = 1 := by
  exact map_one (spinorRepresentation)

theorem chevalleyRepresentation_vector_action (v : SplitCarrier55) :
    chevalleyRepresentation
        (CliffordAlgebra.ι (splitQ (R := ℝ) (W := W5)) v) =
      spinorAction (R := ℝ) (W := W5) v := by
  exact chevalleySpinorRep_vector_action v

theorem chevalleyRepresentation_vector_square (v : SplitCarrier55) :
    chevalleyRepresentation
        (CliffordAlgebra.ι (splitQ (R := ℝ) (W := W5)) v) *
        chevalleyRepresentation
          (CliffordAlgebra.ι (splitQ (R := ℝ) (W := W5)) v) =
      (splitQ (R := ℝ) (W := W5) v) • (1 : SpinorEnd55) := by
  exact chevalleySpinorAction_square v

end InfoGeometry.Clifford.SplitClifford55ChevalleySpinRepresentation
