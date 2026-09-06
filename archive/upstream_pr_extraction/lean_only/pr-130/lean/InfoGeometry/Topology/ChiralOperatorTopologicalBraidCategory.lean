import InfoGeometry.Topology.ChiralOperatorTopologicalBraidHomeomorph

/-!
# Categorical braid transport for the chiral latent carriers

The pointwise intertwining laws are bundled as genuine `TopCat` morphisms.
The resulting squares are the categorical form of the operator-to-feature
readout transport; the quotient remains a topological quotient carrier.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

noncomputable def chiralOperatorTensorR12TopCatIso :
    TopCat.of (ChiralOperatorTensor3 A) ≅
      TopCat.of (ChiralOperatorTensor3 A) :=
  TopCat.isoOfHomeo (chiralOperatorTensorR12Homeomorph (A := A))

noncomputable def chiralOperatorTensorR23TopCatIso :
    TopCat.of (ChiralOperatorTensor3 A) ≅
      TopCat.of (ChiralOperatorTensor3 A) :=
  TopCat.isoOfHomeo (chiralOperatorTensorR23Homeomorph (A := A))

theorem chiralOperatorTensorR12TopCatIso_yang_baxter :
    (chiralOperatorTensorR12TopCatIso (A := A)).hom ≫
        (chiralOperatorTensorR23TopCatIso (A := A)).hom ≫
        (chiralOperatorTensorR12TopCatIso (A := A)).hom =
      (chiralOperatorTensorR23TopCatIso (A := A)).hom ≫
        (chiralOperatorTensorR12TopCatIso (A := A)).hom ≫
        (chiralOperatorTensorR23TopCatIso (A := A)).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  simpa only [TopCat.comp_app] using
    chiralOperatorTensorR12_yang_baxter p

theorem chiralOperatorTensorR12TopCatIso_quadratic :
    (chiralOperatorTensorR12TopCatIso (A := A)).hom ≫
        (chiralOperatorTensorR12TopCatIso (A := A)).hom =
      𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  simpa only [TopCat.comp_app, TopCat.id_app] using
    chiralOperatorTensorR12_quadratic p

theorem chiralOperatorTensorR23TopCatIso_quadratic :
    (chiralOperatorTensorR23TopCatIso (A := A)).hom ≫
        (chiralOperatorTensorR23TopCatIso (A := A)).hom =
      𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  simpa only [TopCat.comp_app, TopCat.id_app] using
    chiralOperatorTensorR23_quadratic p

theorem continuous_operatorSageFeatureTripleMap :
    Continuous (operatorSageFeatureTripleMap (A := A)) := by
  exact
    (continuous_operatorSageObservationMap.comp continuous_fst).prodMk
      ((continuous_operatorSageObservationMap.comp
          (continuous_fst.comp continuous_snd)).prodMk
        (continuous_operatorSageObservationMap.comp
          (continuous_snd.comp continuous_snd)))

noncomputable def operatorSageFeatureTripleTopCatHom :
    TopCat.of (ChiralOperatorTensor3 A) ⟶
      TopCat.of (OperatorSageFeatureTensor3 A) :=
  TopCat.ofHom
    { toFun := operatorSageFeatureTripleMap
      continuous_toFun := continuous_operatorSageFeatureTripleMap }

noncomputable def operatorSageFeatureTensorR12TopCatIso :
    TopCat.of (OperatorSageFeatureTensor3 A) ≅
      TopCat.of (OperatorSageFeatureTensor3 A) :=
  TopCat.isoOfHomeo (operatorSageFeatureTensorR12Homeomorph (A := A))

noncomputable def operatorSageFeatureTensorR23TopCatIso :
    TopCat.of (OperatorSageFeatureTensor3 A) ≅
      TopCat.of (OperatorSageFeatureTensor3 A) :=
  TopCat.isoOfHomeo (operatorSageFeatureTensorR23Homeomorph (A := A))

theorem operatorSageFeatureTripleTopCatHom_R12_naturality :
    operatorSageFeatureTripleTopCatHom (A := A) ≫
        (operatorSageFeatureTensorR12TopCatIso (A := A)).hom =
      (chiralOperatorTensorR12TopCatIso (A := A)).hom ≫
        operatorSageFeatureTripleTopCatHom (A := A) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  simpa only [TopCat.comp_app] using
    operatorSageFeatureTriple_R12_intertwines p

theorem operatorSageFeatureTripleTopCatHom_R23_naturality :
    operatorSageFeatureTripleTopCatHom (A := A) ≫
        (operatorSageFeatureTensorR23TopCatIso (A := A)).hom =
      (chiralOperatorTensorR23TopCatIso (A := A)).hom ≫
        operatorSageFeatureTripleTopCatHom (A := A) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  simpa only [TopCat.comp_app] using
    operatorSageFeatureTriple_R23_intertwines p

theorem operatorSageFeatureTensorR12TopCatIso_yang_baxter :
    (operatorSageFeatureTensorR12TopCatIso (A := A)).hom ≫
        (operatorSageFeatureTensorR23TopCatIso (A := A)).hom ≫
        (operatorSageFeatureTensorR12TopCatIso (A := A)).hom =
      (operatorSageFeatureTensorR23TopCatIso (A := A)).hom ≫
        (operatorSageFeatureTensorR12TopCatIso (A := A)).hom ≫
        (operatorSageFeatureTensorR23TopCatIso (A := A)).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  simpa only [TopCat.comp_app] using
    operatorSageFeatureTensorR12_yang_baxter p

noncomputable def chiralOperatorQuotientTensorR12TopCatIso :
    TopCat.of (ChiralOperatorQuotientTensor3 A) ≅
      TopCat.of (ChiralOperatorQuotientTensor3 A) :=
  TopCat.isoOfHomeo (chiralOperatorQuotientTensorR12Homeomorph (A := A))

noncomputable def chiralOperatorQuotientTensorR23TopCatIso :
    TopCat.of (ChiralOperatorQuotientTensor3 A) ≅
      TopCat.of (ChiralOperatorQuotientTensor3 A) :=
  TopCat.isoOfHomeo (chiralOperatorQuotientTensorR23Homeomorph (A := A))

theorem chiralOperatorQuotientTensorR12TopCatIso_yang_baxter :
    (chiralOperatorQuotientTensorR12TopCatIso (A := A)).hom ≫
        (chiralOperatorQuotientTensorR23TopCatIso (A := A)).hom ≫
        (chiralOperatorQuotientTensorR12TopCatIso (A := A)).hom =
      (chiralOperatorQuotientTensorR23TopCatIso (A := A)).hom ≫
        (chiralOperatorQuotientTensorR12TopCatIso (A := A)).hom ≫
        (chiralOperatorQuotientTensorR23TopCatIso (A := A)).hom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  simpa only [TopCat.comp_app] using
    chiralOperatorQuotientTensorR12_yang_baxter p

end
end InfoGeometry.Topology
