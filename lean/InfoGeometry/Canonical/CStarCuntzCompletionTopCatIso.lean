import InfoGeometry.Canonical.CStarCuntzCompletionTopology

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

@[simp] theorem generatedToCarrierTopCatIso_generator
    (U : CStarCuntzCompletion ι) (i : ι) :
    (generatedToCarrierTopCatIso U).hom
        (⟨U.family.S i, U.family.S_mem_generatedCStarSubalgebra i⟩ :
          U.family.generatedCStarSubalgebra) = U.family.S i :=
  rfl

end InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzCompletionTopCatIso
