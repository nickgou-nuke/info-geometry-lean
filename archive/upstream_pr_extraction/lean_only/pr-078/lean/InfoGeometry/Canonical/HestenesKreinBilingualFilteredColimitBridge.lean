import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Tactic
import InfoGeometry.Physics.HestenesKreinBilingualCarrier

/-!
# Bilingual left/right actions on a filtered module colimit

This owner is the categorical replacement for an analytic two-sided
completion claim.  Compatible left and right endomorphisms of a filtered
`ModuleCat ℝ` diagram descend to the colimit, and their commutation is proved
by the colimit universal property.  No norm completion or Morita equivalence
is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge

open CategoryTheory CategoryTheory.Limits

variable {F : ℕ ⥤ ModuleCat ℝ}

abbrev ColimitCarrier (F : ℕ ⥤ ModuleCat ℝ) := colimit F
abbrev ColimitEnd (F : ℕ ⥤ ModuleCat ℝ) :=
  Module.End ℝ (ColimitCarrier F)

structure Datum where
  left : F ⟶ F
  right : F ⟶ F
  commute : left ≫ right = right ≫ left

def leftColimit (D : Datum (F := F)) : ColimitEnd F :=
  (colim.map D.left).hom

def rightColimit (D : Datum (F := F)) : ColimitEnd F :=
  (colim.map D.right).hom

theorem leftColimit_on_stage (D : Datum (F := F)) (j : ℕ) (x : F.obj j) :
    leftColimit D ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom ((D.left.app j).hom x) := by
  exact congrArg (fun f => f x) (colimit.ι_map D.left j)

theorem rightColimit_on_stage (D : Datum (F := F)) (j : ℕ) (x : F.obj j) :
    rightColimit D ((colimit.ι F j).hom x) =
      (colimit.ι F j).hom ((D.right.app j).hom x) := by
  exact congrArg (fun f => f x) (colimit.ι_map D.right j)

theorem colimit_left_right_commute (D : Datum (F := F)) :
    leftColimit D * rightColimit D = rightColimit D * leftColimit D := by
  have hcat : colim.map D.right ≫ colim.map D.left =
      colim.map D.left ≫ colim.map D.right := by
    apply colimit.hom_ext
    intro j
    apply ModuleCat.hom_ext
    ext x
    change leftColimit D (rightColimit D ((colimit.ι F j).hom x)) =
      rightColimit D (leftColimit D ((colimit.ι F j).hom x))
    rw [leftColimit_on_stage, rightColimit_on_stage,
      rightColimit_on_stage, leftColimit_on_stage]
    have h := congrArg (fun η : F ⟶ F => η.app j) D.commute
    simpa [leftColimit, rightColimit, ModuleCat.comp_apply] using
      congrArg (fun f => (colimit.ι F j).hom (f.hom x)) h.symm
  simpa [leftColimit, rightColimit, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hcat

theorem colimit_bilingual_stage_readback (D : Datum (F := F)) (j : ℕ)
    (x : F.obj j) :
    ((leftColimit D) ((colimit.ι F j).hom x),
      (rightColimit D) ((colimit.ι F j).hom x)) =
      ((colimit.ι F j).hom ((D.left.app j).hom x),
        (colimit.ι F j).hom ((D.right.app j).hom x)) := by
  rw [leftColimit_on_stage, rightColimit_on_stage]

end InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge
