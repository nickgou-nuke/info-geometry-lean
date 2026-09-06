import InfoGeometry.Algebra.Zorn.G2CartanParameterSpan
import InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional
import InfoGeometry.Lie.LieEquivEigenvectorTransport
import InfoGeometry.Lie.EigenRootSpaceTransport
import InfoGeometry.Lie.RootLineScalarCocycle
import InfoGeometry.Algebra.Zorn.G2SignedRootNativeEmbedding
import InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteWeightBridge
import InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
import InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceMembership
import InfoGeometry.Algebra.Zorn.G2NativeRootPairWitnesses

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylStructuralBridges

open InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

theorem root_representation_has_scaled_inner_witness
    (r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    ∃ (a : ℝ) (x y : ZornVectorMatrix ℝ),
      zornDerivationRootRepresentation r =
        a • NativeStanDerivationBilinear.innerDerivation x y :=
  InfoGeometry.Algebra.Zorn.G2NativeRootPairWitnesses.root_representation_exists_scaled_inner_witness r

theorem cycle_conjugates_root_to_scaled_inner_pair
    (r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    ∃ (a : ℝ) (x y : ZornVectorMatrix ℝ),
      conjugateNativeDerivation realWeylCycle
          (zornDerivationRootRepresentation r) =
        a • NativeStanDerivationBilinear.innerDerivation
          (nativeAut realWeylCycle x) (nativeAut realWeylCycle y) :=
  InfoGeometry.Algebra.Zorn.G2NativeRootPairWitnesses.cycle_maps_root_to_scaled_inner_pair r

theorem reflection_conjugates_root_to_scaled_inner_pair
    (r : InfoGeometry.Algebra.Zorn.G2TwoRootSystem.G2Root) :
    ∃ (a : ℝ) (x y : ZornVectorMatrix ℝ),
      conjugateNativeDerivation realWeylReflection
          (zornDerivationRootRepresentation r) =
        a • NativeStanDerivationBilinear.innerDerivation
          (nativeAut realWeylReflection x) (nativeAut realWeylReflection y) :=
  InfoGeometry.Algebra.Zorn.G2NativeRootPairWitnesses.reflection_maps_root_to_scaled_inner_pair r

noncomputable def cycleCartanParameterActionNative : Params →ₗ[ℝ] Params where
  toFun p :=
    (-p 6 - p 13) • parameterUnit 6 + p 6 • parameterUnit 13
  map_add' p q := by
    ext i
    fin_cases i <;> simp [parameterUnit] <;> ring
  map_smul' a p := by
    ext i
    fin_cases i <;> simp [parameterUnit] <;> ring


noncomputable def reflectionCartanParameterActionNative : Params →ₗ[ℝ] Params where
  toFun p :=
    ((p 6 - 4 * p 13) / 3) • parameterUnit 6 +
      ((-2 * p 6 - p 13) / 3) • parameterUnit 13
  map_add' p q := by
    ext i
    fin_cases i <;> simp [parameterUnit] <;> ring
  map_smul' a p := by
    ext i
    fin_cases i <;> simp [parameterUnit] <;> ring

noncomputable def cartanParameterRestrictionLocal
    (L : Params ≃ₗ[ℝ] Params)
    (hL : G2NativeWeylRootSpaceTransport.cartanParameterPlane.map L.toLinearMap = G2NativeWeylRootSpaceTransport.cartanParameterPlane) :
    G2NativeWeylRootSpaceTransport.cartanParameterPlane ≃ₗ[ℝ] G2NativeWeylRootSpaceTransport.cartanParameterPlane := by
  let f : G2NativeWeylRootSpaceTransport.cartanParameterPlane →ₗ[ℝ] G2NativeWeylRootSpaceTransport.cartanParameterPlane :=
    { toFun := fun p => ⟨L p, by
        have hp : L p ∈ G2NativeWeylRootSpaceTransport.cartanParameterPlane.map L.toLinearMap :=
          ⟨p, p.property, rfl⟩
        rw [hL] at hp
        exact hp⟩
      map_add' := by intro p q; apply Subtype.ext; exact L.map_add p q
      map_smul' := by intro a p; apply Subtype.ext; exact L.map_smul a p }
  apply LinearEquiv.ofBijective f
  constructor
  · intro p q h
    apply Subtype.ext
    simpa [f] using congrArg (fun z : G2NativeWeylRootSpaceTransport.cartanParameterPlane => (z : Params)) h
  · intro q
    have hq : (q : Params) ∈ G2NativeWeylRootSpaceTransport.cartanParameterPlane.map L.toLinearMap := by
      rw [hL]
      exact q.property
    rcases hq with ⟨p, hp, hpeq⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    exact hpeq

noncomputable def cycleCartanParameterEquiv :
    G2NativeWeylRootSpaceTransport.cartanParameterPlane ≃ₗ[ℝ] G2NativeWeylRootSpaceTransport.cartanParameterPlane :=
  cartanParameterRestrictionLocal (conjugatedParameterLieEquiv realWeylCycle)
    (InfoGeometry.Algebra.Zorn.G2CartanParameterSpan.conjugatedParameterLieEquiv_map_cartanParameterPlane_eq_of_pair_generators
      realWeylCycle (by
        rw [← U0V0_parameter_readback]
        change conjugatedParameterLinearMap realWeylCycle _ ∈ G2NativeWeylRootSpaceTransport.cartanParameterPlane
        exact conjugatedParameterLinearMap_cycle_U0V0_mem_cartanParameterPlane)
      (by
        rw [← U1V1_parameter_readback]
        change conjugatedParameterLinearMap realWeylCycle _ ∈ cartanParameterPlane
        exact conjugatedParameterLinearMap_cycle_U1V1_mem_cartanParameterPlane))

noncomputable def reflectionCartanParameterEquiv :
    G2NativeWeylRootSpaceTransport.cartanParameterPlane ≃ₗ[ℝ] G2NativeWeylRootSpaceTransport.cartanParameterPlane :=
  cartanParameterRestrictionLocal (conjugatedParameterLieEquiv realWeylReflection)
    (InfoGeometry.Algebra.Zorn.G2CartanParameterSpan.conjugatedParameterLieEquiv_map_cartanParameterPlane_eq_of_pair_generators
      realWeylReflection (by
        rw [← U0V0_parameter_readback]
        change conjugatedParameterLinearMap realWeylReflection _ ∈ G2NativeWeylRootSpaceTransport.cartanParameterPlane
        rw [conjugatedParameterLinearMap_apply]
        change parameterLinearEquiv.symm
          (conjugateNativeDerivation realWeylReflection
            (parameterLinearEquiv (parameterLinearEquiv.symm _))) ∈ _
        rw [parameterLinearEquiv.apply_symm_apply]
        exact realWeylReflection_cartanPair_zero_mem_cartanParameterPlane)
      (by
        rw [← U1V1_parameter_readback]
        change conjugatedParameterLinearMap realWeylReflection _ ∈ cartanParameterPlane
        rw [conjugatedParameterLinearMap_apply]
        change parameterLinearEquiv.symm
          (conjugateNativeDerivation realWeylReflection
            (parameterLinearEquiv (parameterLinearEquiv.symm _))) ∈ _
        rw [parameterLinearEquiv.apply_symm_apply]
        exact realWeylReflection_cartanPair_one_mem_cartanParameterPlane))


noncomputable def parameterCanonicalCartanPlaneEquiv :
    G2NativeWeylRootSpaceTransport.cartanParameterPlane ≃ₗ[ℝ]
      G2NativeWeylRootSpaceTransport.canonicalCartanParameterPlane := by
  let f : G2NativeWeylRootSpaceTransport.cartanParameterPlane →ₗ[ℝ]
      G2NativeWeylRootSpaceTransport.canonicalCartanParameterPlane :=
    { toFun := fun p => ⟨parameterCanonicalLieEquiv p,
        mem_canonicalParameterSubmodule p.property⟩
      map_add' := by intro p q; apply Subtype.ext; exact parameterCanonicalLieEquiv.map_add p q
      map_smul' := by intro a p; apply Subtype.ext; exact parameterCanonicalLieEquiv.map_smul a p }
  apply LinearEquiv.ofBijective f
  constructor
  · intro p q h
    apply Subtype.ext
    simpa [f] using congrArg
      (fun z : G2NativeWeylRootSpaceTransport.canonicalCartanParameterPlane => (z : _)) h
  · intro q
    rcases q.property with ⟨p, hp, hq⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    exact hq

@[simp] theorem parameterCanonicalCartanPlaneEquiv_symm_apply
    (p : G2NativeWeylRootSpaceTransport.cartanParameterPlane) :
    parameterCanonicalCartanPlaneEquiv.symm
        ⟨parameterCanonicalLieEquiv p,
          mem_canonicalParameterSubmodule p.property⟩ = p := by
  apply parameterCanonicalCartanPlaneEquiv.injective
  simp [parameterCanonicalCartanPlaneEquiv]

noncomputable def realWeylCycle_canonicalCartanParameterPlaneEquiv :
    G2NativeWeylRootSpaceTransport.canonicalCartanParameterPlane ≃ₗ[ℝ]
      G2NativeWeylRootSpaceTransport.canonicalCartanParameterPlane :=
  parameterCanonicalCartanPlaneEquiv.symm.trans
    (cycleCartanParameterEquiv.trans parameterCanonicalCartanPlaneEquiv)

noncomputable def realWeylReflection_canonicalCartanParameterPlaneEquiv :
    G2NativeWeylRootSpaceTransport.canonicalCartanParameterPlane ≃ₗ[ℝ]
      G2NativeWeylRootSpaceTransport.canonicalCartanParameterPlane :=
  parameterCanonicalCartanPlaneEquiv.symm.trans
    (reflectionCartanParameterEquiv.trans parameterCanonicalCartanPlaneEquiv)

end InfoGeometry.Algebra.Zorn.G2NativeWeylStructuralBridges


/-!
# Stable structural bridges for native Weyl transport

This module collects the carrier-safe interfaces used by the Weyl-adjoint
development.  Concrete generator readbacks remain separate; this import point
exposes only the proved Cartan, eigenvector, root-line, and scalar interfaces.
-/
