import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import InfoGeometry.Lie.ChevalleySpinorBlueprint

/-!
# Chevalley spinor action for the split 10-dimensional Clifford carrier

This owner records the strongest spinor statement currently supplied by the
native Clifford layer.  The Chevalley construction gives an algebra
representation of the split Clifford algebra on the exterior-algebra carrier
`Λ* (Fin 5 → ℝ)`.  Since an algebra hom is also a Lie hom for commutator
brackets, this yields a kernel-checked Lie action on the spinor carrier.

No identification with a particular `so(5,5)` matrix model is asserted here;
that comparison is a separate transport theorem.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55ChevalleySpinorActionBridge

open InfoGeometry.Lie.ChevalleySpinor

abbrev W5 := InfoGeometry.Algebra.FiniteSpin.Vec5R
abbrev SplitCarrier55 := SplitV ℝ W5
abbrev SpinorCarrier55 := SpinorSpace ℝ W5
abbrev CliffordCarrier55 := CliffordAlgebra (splitQ (R := ℝ) (W := W5))
abbrev SpinorEnd55 := Module.End ℝ SpinorCarrier55

noncomputable def chevalleySpinorRep : CliffordCarrier55 →ₐ[ℝ] SpinorEnd55 :=
  abstractSpinorRep (R := ℝ) (W := W5)

noncomputable def chevalleySpinorLieRep :
    CliffordCarrier55 →ₗ⁅ℝ⁆ SpinorEnd55 :=
  chevalleySpinorRep.toLieHom

@[simp] theorem chevalleySpinorLieRep_apply (x : CliffordCarrier55) :
    chevalleySpinorLieRep x = chevalleySpinorRep x := rfl

theorem chevalleySpinorLieRep_map_lie (x y : CliffordCarrier55) :
    chevalleySpinorLieRep ⁅x, y⁆ =
      ⁅chevalleySpinorLieRep x, chevalleySpinorLieRep y⁆ := by
  exact chevalleySpinorLieRep.map_lie x y

theorem chevalleySpinorRep_vector_action (v : SplitCarrier55) :
    chevalleySpinorRep (CliffordAlgebra.ι (splitQ (R := ℝ) (W := W5)) v) =
      spinorAction (R := ℝ) (W := W5) v := by
  simp [chevalleySpinorRep, abstractSpinorRep]

theorem chevalleySpinorAction_square (v : SplitCarrier55) :
    chevalleySpinorRep (CliffordAlgebra.ι (splitQ (R := ℝ) (W := W5)) v) *
        chevalleySpinorRep (CliffordAlgebra.ι (splitQ (R := ℝ) (W := W5)) v) =
      (splitQ (R := ℝ) (W := W5) v) • (1 : SpinorEnd55) := by
  rw [chevalleySpinorRep_vector_action]
  exact spinorAction_sq (R := ℝ) (W := W5) v

end InfoGeometry.Clifford.Cl55ChevalleySpinorActionBridge
