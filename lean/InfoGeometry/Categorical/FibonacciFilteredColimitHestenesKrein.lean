import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.Filtered
import InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge

/-!
# Fibonacci braid transport through a native filtered colimit

This is the categorical owner for transporting a finite braid action through
`CategoryTheory.Limits.colimit`.  The diagram and its two braid generators are
supplied as genuine natural transformations of a filtered `ModuleCat ℂ`
diagram.  Consequently the construction uses only the native colimit object,
its injections, and `colim.map`; it introduces no second carrier and no
analytic or completion layer.

The Hestenes--Krein reformulation is kept on its existing real filtered-module
owner.  In particular, commuting left/right transports are descended by the
universal property and are not identified with the generally noncommuting
Fibonacci braid generators.
-/

noncomputable section

namespace InfoGeometry.Categorical.FibonacciFilteredColimitHestenesKrein

open CategoryTheory CategoryTheory.Limits

universe u

variable {F : ℕ ⥤ ModuleCat ℂ} [HasColimit F]

/-- The native filtered-colimit carrier of the Fibonacci stage diagram. -/
abbrev Carrier (F : ℕ ⥤ ModuleCat ℂ) := colimit F

/-- A braid-generator natural transformation on the filtered stage diagram. -/
abbrev StageOperator (F : ℕ ⥤ ModuleCat ℂ) := F ⟶ F

/-- The induced endomorphism on the native colimit carrier. -/
def colimitOperator (s : StageOperator F) : Module.End ℂ (Carrier F) :=
  (colim.map s).hom

omit [HasColimit F] in
theorem colimitOperator_comp (s t : StageOperator F) :
    colimitOperator (s ≫ t) = colimitOperator t * colimitOperator s := by
  change (colim.map (s ≫ t)).hom = _
  rw [colim.map_comp]
  ext x
  simp [colimitOperator, Module.End.mul_apply]

omit [HasColimit F] in
theorem colimitOperator_id :
    colimitOperator (𝟙 F) = LinearMap.id := by
  change (colim.map (𝟙 F)).hom = _
  rw [colim.map_id]
  rfl

@[simp] theorem colimitOperator_on_stage
    (s : StageOperator F) (n : ℕ) (x : F.obj n) :
    colimitOperator s ((colimit.ι F n).hom x) =
      (colimit.ι F n).hom ((s.app n).hom x) := by
  exact congrArg (fun f => f x) (colimit.ι_map s n)

/-! ## Artin transport -/

/-- The finite-stage Artin law, stated at the categorical owner boundary. -/
def StageArtin (s₀ s₁ : StageOperator F) : Prop :=
  s₀ ≫ s₁ ≫ s₀ = s₁ ≫ s₀ ≫ s₁

omit [HasColimit F] in
/- The Artin law descends through the native filtered colimit. -/
theorem colimit_artin_of_stageArtin
    {s₀ s₁ : StageOperator F}
    (h : StageArtin s₀ s₁) :
    colimitOperator s₀ * colimitOperator s₁ * colimitOperator s₀ =
      colimitOperator s₁ * colimitOperator s₀ * colimitOperator s₁ := by
  have hmap : colim.map s₀ ≫ colim.map s₁ ≫ colim.map s₀ =
      colim.map s₁ ≫ colim.map s₀ ≫ colim.map s₁ := by
    rw [← colim.map_comp, ← colim.map_comp, ← colim.map_comp, ← colim.map_comp]
    exact congrArg colim.map h
  simpa [colimitOperator, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hmap

/-- Stage readback of the descended Artin law. -/
theorem colimit_artin_on_stage
    {s₀ s₁ : StageOperator F}
    (h : StageArtin s₀ s₁) (n : ℕ) (x : F.obj n) :
    (colimitOperator s₀ * colimitOperator s₁ * colimitOperator s₀)
        ((colimit.ι F n).hom x) =
      (colimitOperator s₁ * colimitOperator s₀ * colimitOperator s₁)
        ((colimit.ι F n).hom x) := by
  exact congrArg (fun f : Module.End ℂ (Carrier F) =>
      f ((colimit.ι F n).hom x))
    (colimit_artin_of_stageArtin h)

/-! ## Hestenes--Krein bilateral transport on the same categorical boundary -/

variable {G : ℕ ⥤ ModuleCat ℝ} [HasColimit G]

omit [HasColimit G] in
/- The Hestenes/Krein left-right commutation law on the filtered carrier. -/
theorem hestenes_krein_colimit_bilateral_commute
    (D : InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge.Datum
      (F := G)) :
    InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge.leftColimit D *
        InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge.rightColimit D =
      InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge.rightColimit D *
        InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge.leftColimit D :=
  InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge.colimit_left_right_commute D

end InfoGeometry.Categorical.FibonacciFilteredColimitHestenesKrein
