import InfoGeometry.Canonical.CStarCuntzCompletionTopology
import InfoGeometry.Canonical.CStarCuntzFamilyTopology

/-!
# Bundled topological isomorphism for a C⋆ Cuntz completion

The completion owner already supplies the two continuous inverse maps between
the closed generated subalgebra and the ambient carrier.  This file packages
those maps as a native `TopCat` isomorphism and records its action on the
generators.
-/

noncomputable section

namespace InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzCompletionTopCatIso

open CategoryTheory
open InfoGeometry.Physics.CStarCuntzTensorQuotient
open InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzCompletion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def generatedToCarrierTopCatIso (U : CStarCuntzCompletion ι) :
    TopCat.of U.family.generatedCStarSubalgebra ≅ TopCat.of U.carrier where
  hom := U.generatedToCarrierTopCatHom
  inv := U.carrierToGeneratedTopCatHom
  hom_inv_id := by
    apply TopCat.hom_ext
    ext a
    rw [TopCat.comp_app, TopCat.id_app]
    simp [generatedToCarrierTopCatHom, carrierToGeneratedTopCatHom,
      TopCat.ofHom]
    rw [← generatedToCarrierHomeomorph_apply U a]
    exact U.generatedToCarrierHomeomorph.symm_apply_apply a
  inv_hom_id := by
    apply TopCat.hom_ext
    ext a
    rw [TopCat.comp_app, TopCat.id_app]
    simp [generatedToCarrierTopCatHom, carrierToGeneratedTopCatHom,
      TopCat.ofHom]
    rw [← generatedToCarrierHomeomorph_apply U
      (U.generatedToCarrierHomeomorph.symm a)]
    exact U.generatedToCarrierHomeomorph.apply_symm_apply a

theorem generatedToCarrierTopCatIso_comp_leftGeneratorAction
    (U : CStarCuntzCompletion ι) (i : ι) :
    (generatedToCarrierTopCatIso U).hom ≫
        U.family.leftGeneratorActionTopCatHom i =
      U.family.generatedFamily.leftGeneratorActionTopCatHom i ≫
        (generatedToCarrierTopCatIso U).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  rfl

theorem generatedToCarrierTopCatIso_comp_leftAdjointGeneratorAction
    (U : CStarCuntzCompletion ι) (i : ι) :
    (generatedToCarrierTopCatIso U).hom ≫
        U.family.leftAdjointGeneratorActionTopCatHom i =
      U.family.generatedFamily.leftAdjointGeneratorActionTopCatHom i ≫
        (generatedToCarrierTopCatIso U).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  rfl

theorem generatedToCarrierTopCatIso_comp_rightAdjointGeneratorAction
    (U : CStarCuntzCompletion ι) (i : ι) :
    (generatedToCarrierTopCatIso U).hom ≫
        U.family.rightAdjointGeneratorActionTopCatHom i =
      U.family.generatedFamily.rightAdjointGeneratorActionTopCatHom i ≫
        (generatedToCarrierTopCatIso U).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  rfl

@[simp] theorem generatedToCarrierTopCatIso_generator
    (U : CStarCuntzCompletion ι) (i : ι) :
    (generatedToCarrierTopCatIso U).hom
        (⟨U.family.S i, U.family.S_mem_generatedCStarSubalgebra i⟩ :
          U.family.generatedCStarSubalgebra) = U.family.S i :=
  rfl

@[simp] theorem generatedToCarrierTopCatIso_star_generator
    (U : CStarCuntzCompletion ι) (i : ι) :
    (generatedToCarrierTopCatIso U).hom
        (star (⟨U.family.S i, U.family.S_mem_generatedCStarSubalgebra i⟩ :
          U.family.generatedCStarSubalgebra)) = star (U.family.S i) :=
  rfl

@[simp] theorem generatedToCarrierTopCatIso_inv_generator
    (U : CStarCuntzCompletion ι) (i : ι) :
    (generatedToCarrierTopCatIso U).inv (U.family.S i) =
      (⟨U.family.S i, U.family.S_mem_generatedCStarSubalgebra i⟩ :
        U.family.generatedCStarSubalgebra) := by
  exact carrierToGeneratedTopCatHom_generator U i

@[simp] theorem generatedToCarrierTopCatIso_inv_star_generator
    (U : CStarCuntzCompletion ι) (i : ι) :
    (generatedToCarrierTopCatIso U).inv (star (U.family.S i)) =
      star (⟨U.family.S i, U.family.S_mem_generatedCStarSubalgebra i⟩ :
        U.family.generatedCStarSubalgebra) := by
  exact carrierToGeneratedTopCatHom_star_generator U i

theorem generatedToCarrierTopCatIso_inv_naturality_leftGeneratorAction
    (U : CStarCuntzCompletion ι) (i : ι) :
    U.family.leftGeneratorActionTopCatHom i ≫
        (generatedToCarrierTopCatIso U).inv =
      (generatedToCarrierTopCatIso U).inv ≫
        U.family.generatedFamily.leftGeneratorActionTopCatHom i := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  rfl

theorem generatedToCarrierTopCatIso_inv_naturality_leftAdjointGeneratorAction
    (U : CStarCuntzCompletion ι) (i : ι) :
    U.family.leftAdjointGeneratorActionTopCatHom i ≫
        (generatedToCarrierTopCatIso U).inv =
      (generatedToCarrierTopCatIso U).inv ≫
        U.family.generatedFamily.leftAdjointGeneratorActionTopCatHom i := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  rfl

theorem generatedToCarrierTopCatIso_inv_naturality_rightAdjointGeneratorAction
    (U : CStarCuntzCompletion ι) (i : ι) :
    U.family.rightAdjointGeneratorActionTopCatHom i ≫
        (generatedToCarrierTopCatIso U).inv =
      (generatedToCarrierTopCatIso U).inv ≫
        U.family.generatedFamily.rightAdjointGeneratorActionTopCatHom i := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  rfl

end InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzCompletionTopCatIso
