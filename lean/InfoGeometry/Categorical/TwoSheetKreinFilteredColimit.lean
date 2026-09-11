import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.Filtered
import InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge

/-!
# Two-sheet Krein transport through a filtered colimit

This is the categorical lift of the finite two-sheet exchange law.  The stage
diagram and its natural transformations are parameters; no particular tower
is invented here.  The colimit is the native carrier supplied by `ModuleCat`.
-/

noncomputable section

namespace InfoGeometry.Categorical.TwoSheetKreinFilteredColimit

open CategoryTheory CategoryTheory.Limits

variable {F : ℕ ⥤ ModuleCat ℝ} [HasColimit F]

abbrev Carrier (F : ℕ ⥤ ModuleCat ℝ) := colimit F

/-- The endomorphism induced on the filtered colimit by a stage transformation. -/
def colimitEnd (s : F ⟶ F) : Module.End ℝ (Carrier F) :=
  (colim.map s).hom

@[simp] theorem colimitEnd_on_stage
    (s : F ⟶ F) (n : ℕ) (x : F.obj n) :
    colimitEnd s ((colimit.ι F n).hom x) =
      (colimit.ι F n).hom ((s.app n).hom x) := by
  exact congrArg (fun f => f x) (colimit.ι_map s n)

/-- Krein involutivity descends from the finite stages to the colimit. -/
theorem colimitEnd_involutive
    (eta : F ⟶ F)
    (hη : eta ≫ eta = 𝟙 F) :
    colimitEnd eta * colimitEnd eta = LinearMap.id := by
  have hmap : colim.map eta ≫ colim.map eta = 𝟙 (colimit F) := by
    rw [← colim.map_comp]
    rw [hη, colim.map_id]
    rfl
  simpa [colimitEnd, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hmap

/-- Exchange of the two sheet projectors descends through the colimit. -/
theorem colimitEnd_exchange
    (eta fplus fminus : F ⟶ F)
    (hex : eta ≫ fplus ≫ eta = fminus) :
    colimitEnd eta * colimitEnd fplus * colimitEnd eta =
      colimitEnd fminus := by
  have hmap :
      colim.map eta ≫ colim.map fplus ≫ colim.map eta =
        colim.map fminus := by
    rw [← colim.map_comp, ← colim.map_comp]
    exact congrArg colim.map hex
  simpa [colimitEnd, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hmap

/-- Stage readback for the descended sheet exchange. -/
theorem colimitEnd_exchange_on_stage
    (eta fplus fminus : F ⟶ F)
    (hex : eta ≫ fplus ≫ eta = fminus)
    (n : ℕ) (x : F.obj n) :
    (colimitEnd eta * colimitEnd fplus * colimitEnd eta)
        ((colimit.ι F n).hom x) =
      (colimit.ι F n).hom ((fminus.app n).hom x) := by
  rw [colimitEnd_exchange eta fplus fminus hex]
  exact colimitEnd_on_stage fminus n x

end InfoGeometry.Categorical.TwoSheetKreinFilteredColimit
