import InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction
import InfoGeometry.Algebra.Zorn.G2NativeWeylReflectionCartanSpan
import InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction

open G2ZornDerivationRootRepresentation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

def canonicalCartanPlane : Submodule ℝ canonicalZornDerivations :=
  Submodule.span ℝ ({vectorCanonicalLieEquiv (cartanDerivation 0),
    vectorCanonicalLieEquiv (cartanDerivation 1)} : Set canonicalZornDerivations)

theorem vectorCanonicalLieEquiv_cartanDerivation_zero_mem_canonicalCartanPlane :
    vectorCanonicalLieEquiv (cartanDerivation 0) ∈ canonicalCartanPlane := by
  change vectorCanonicalLieEquiv (cartanDerivation 0) ∈ canonicalCartanPlane
  exact Submodule.subset_span (by simp [canonicalCartanPlane])

theorem vectorCanonicalLieEquiv_cartanDerivation_one_mem_canonicalCartanPlane :
    vectorCanonicalLieEquiv (cartanDerivation 1) ∈ canonicalCartanPlane := by
  change vectorCanonicalLieEquiv (cartanDerivation 1) ∈ canonicalCartanPlane
  exact Submodule.subset_span (by simp [canonicalCartanPlane])

theorem vectorCanonicalLieEquiv_map_nativeCartanSpan_le_canonicalCartanPlane :
    nativeCartanSpan.map vectorCanonicalLieEquiv.toLinearMap ≤ canonicalCartanPlane := by
  rintro _ ⟨D, hD, rfl⟩
  refine Submodule.span_induction
    (p := fun D _ => vectorCanonicalLieEquiv D ∈ canonicalCartanPlane) ?_ ?_ ?_ ?_ hD
  · intro D hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact vectorCanonicalLieEquiv_cartanDerivation_zero_mem_canonicalCartanPlane
    · exact vectorCanonicalLieEquiv_cartanDerivation_one_mem_canonicalCartanPlane
  · exact canonicalCartanPlane.zero_mem
  · intro D E _ _ hD hE
    simpa only [map_add] using canonicalCartanPlane.add_mem hD hE
  · intro a D _ hD
    simpa only [map_smul] using canonicalCartanPlane.smul_mem a hD

theorem vectorCanonicalLieEquiv_map_nativeCartanSpan_eq_canonicalCartanPlane :
    nativeCartanSpan.map vectorCanonicalLieEquiv.toLinearMap = canonicalCartanPlane := by
  apply le_antisymm
  · exact vectorCanonicalLieEquiv_map_nativeCartanSpan_le_canonicalCartanPlane
  · apply Submodule.span_le.2
    intro D hD
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · exact ⟨cartanDerivation 0, Submodule.subset_span (by simp [nativeCartanSpan]), rfl⟩
    · exact ⟨cartanDerivation 1, Submodule.subset_span (by simp [nativeCartanSpan]), rfl⟩

theorem realWeylCycle_nativeCartanSpan_map_eq :
    nativeCartanSpan.map
        (conjugateNativeDerivationLieEquiv realWeylCycle).toLinearMap =
      nativeCartanSpan := by
  letI : Module.Finite ℝ InfoGeometry.Lie.CanonicalZornDerivationDimension.VDer :=
    Module.Finite.equiv parameterLinearEquiv
  letI : Module.Finite ℝ nativeCartanSpan :=
    Module.Finite.of_injective nativeCartanSpan.subtype Subtype.coe_injective
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨D, hD, rfl⟩
    exact realWeylCycle_maps_nativeCartanSpan hD
  · exact (conjugateNativeDerivationLieEquiv realWeylCycle).toLinearEquiv.finrank_map_eq
      nativeCartanSpan

theorem realWeylReflection_nativeCartanSpan_map_eq :
    nativeCartanSpan.map
        (conjugateNativeDerivationLieEquiv realWeylReflection).toLinearMap =
      nativeCartanSpan := by
  letI : Module.Finite ℝ InfoGeometry.Lie.CanonicalZornDerivationDimension.VDer :=
    Module.Finite.equiv parameterLinearEquiv
  letI : Module.Finite ℝ nativeCartanSpan :=
    Module.Finite.of_injective nativeCartanSpan.subtype Subtype.coe_injective
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨D, hD, rfl⟩
    exact G2NativeWeylReflectionCartanSpan.realWeylReflection_maps_nativeCartanSpan hD
  · exact (conjugateNativeDerivationLieEquiv realWeylReflection).toLinearEquiv.finrank_map_eq
      nativeCartanSpan

noncomputable def realWeylCycle_nativeCartanSpanEquiv :
    nativeCartanSpan ≃ₗ[ℝ] nativeCartanSpan := by
  let f : nativeCartanSpan →ₗ[ℝ] nativeCartanSpan :=
    { toFun := fun D => ⟨conjugateNativeDerivation realWeylCycle D,
        realWeylCycle_maps_nativeCartanSpan D.property⟩
      map_add' := by
        intro D E
        apply Subtype.ext
        change conjugateNativeDerivationLinear realWeylCycle (D + E) =
          conjugateNativeDerivationLinear realWeylCycle D +
            conjugateNativeDerivationLinear realWeylCycle E
        simp only [map_add]
      map_smul' := by
        intro a D
        apply Subtype.ext
        change conjugateNativeDerivationLinear realWeylCycle (a • D) =
          a • conjugateNativeDerivationLinear realWeylCycle D
        simp only [map_smul] }
  apply LinearEquiv.ofBijective f
  constructor
  · intro D E h
    apply Subtype.ext
    apply (conjugateNativeDerivationLieEquiv realWeylCycle).injective
    exact congrArg (fun z : nativeCartanSpan => z.1) h
  · intro E
    have hE : (E : ZornVectorMatrix.Derivation) ∈
        nativeCartanSpan.map
          (conjugateNativeDerivationLieEquiv realWeylCycle).toLinearMap := by
      rw [realWeylCycle_nativeCartanSpan_map_eq]
      exact E.property
    rcases hE with ⟨D, hD, hDE⟩
    refine ⟨⟨D, hD⟩, ?_⟩
    change f ⟨D, hD⟩ = E
    dsimp [f]
    apply Subtype.ext
    change (conjugateNativeDerivationLieEquiv realWeylCycle) D = E.1
    exact hDE

@[simp] theorem realWeylCycle_nativeCartanSpanEquiv_apply (D : nativeCartanSpan) :
    realWeylCycle_nativeCartanSpanEquiv D =
      ⟨conjugateNativeDerivation realWeylCycle D,
        realWeylCycle_maps_nativeCartanSpan D.property⟩ := by
  rfl

noncomputable def realWeylReflection_nativeCartanSpanEquiv :
    nativeCartanSpan ≃ₗ[ℝ] nativeCartanSpan := by
  let f : nativeCartanSpan →ₗ[ℝ] nativeCartanSpan :=
    { toFun := fun D => ⟨conjugateNativeDerivation realWeylReflection D,
        G2NativeWeylReflectionCartanSpan.realWeylReflection_maps_nativeCartanSpan
          D.property⟩
      map_add' := by
        intro D E
        apply Subtype.ext
        change conjugateNativeDerivationLinear realWeylReflection (D + E) =
          conjugateNativeDerivationLinear realWeylReflection D +
            conjugateNativeDerivationLinear realWeylReflection E
        simp only [map_add]
      map_smul' := by
        intro a D
        apply Subtype.ext
        change conjugateNativeDerivationLinear realWeylReflection (a • D) =
          a • conjugateNativeDerivationLinear realWeylReflection D
        simp only [map_smul] }
  apply LinearEquiv.ofBijective f
  constructor
  · intro D E h
    apply Subtype.ext
    apply (conjugateNativeDerivationLieEquiv realWeylReflection).injective
    exact congrArg (fun z : nativeCartanSpan => z.1) h
  · intro E
    have hE : (E : ZornVectorMatrix.Derivation) ∈
        nativeCartanSpan.map
          (conjugateNativeDerivationLieEquiv realWeylReflection).toLinearMap := by
      rw [realWeylReflection_nativeCartanSpan_map_eq]
      exact E.property
    rcases hE with ⟨D, hD, hDE⟩
    refine ⟨⟨D, hD⟩, ?_⟩
    change f ⟨D, hD⟩ = E
    dsimp [f]
    apply Subtype.ext
    change (conjugateNativeDerivationLieEquiv realWeylReflection) D = E.1
    exact hDE

@[simp] theorem realWeylReflection_nativeCartanSpanEquiv_apply (D : nativeCartanSpan) :
    realWeylReflection_nativeCartanSpanEquiv D =
      ⟨conjugateNativeDerivation realWeylReflection D,
        G2NativeWeylReflectionCartanSpan.realWeylReflection_maps_nativeCartanSpan
          D.property⟩ := by
  rfl

noncomputable def nativeCartanSpanCanonicalEquiv :
    nativeCartanSpan ≃ₗ[ℝ] canonicalCartanPlane := by
  let f : nativeCartanSpan →ₗ[ℝ] canonicalCartanPlane :=
    { toFun := fun D => ⟨vectorCanonicalLieEquiv D,
        by
          rw [← vectorCanonicalLieEquiv_map_nativeCartanSpan_eq_canonicalCartanPlane]
          exact ⟨D, D.property, rfl⟩⟩
      map_add' := by intro D E; apply Subtype.ext; exact vectorCanonicalLieEquiv.toLinearEquiv.map_add D E
      map_smul' := by intro a D; apply Subtype.ext; exact vectorCanonicalLieEquiv.toLinearEquiv.map_smul a D }
  apply LinearEquiv.ofBijective f
  constructor
  · intro D E h
    apply Subtype.ext
    apply vectorCanonicalLieEquiv.injective
    exact congrArg (fun z : canonicalCartanPlane => z.1) h
  · intro E
    have hE : (E : canonicalZornDerivations) ∈
        nativeCartanSpan.map vectorCanonicalLieEquiv.toLinearMap := by
      rw [vectorCanonicalLieEquiv_map_nativeCartanSpan_eq_canonicalCartanPlane]
      exact E.property
    rcases hE with ⟨D, hD, hDE⟩
    refine ⟨⟨D, hD⟩, ?_⟩
    apply Subtype.ext
    change vectorCanonicalLieEquiv D = E.1
    exact hDE

noncomputable def realWeylCycle_canonicalCartanPlaneEquiv :
    canonicalCartanPlane ≃ₗ[ℝ] canonicalCartanPlane :=
  nativeCartanSpanCanonicalEquiv.symm.trans
    (realWeylCycle_nativeCartanSpanEquiv.trans nativeCartanSpanCanonicalEquiv)

noncomputable def realWeylReflection_canonicalCartanPlaneEquiv :
    canonicalCartanPlane ≃ₗ[ℝ] canonicalCartanPlane :=
  nativeCartanSpanCanonicalEquiv.symm.trans
    (realWeylReflection_nativeCartanSpanEquiv.trans nativeCartanSpanCanonicalEquiv)

theorem nativeCartanSpanCanonicalEquiv_cycle_covariant (D : nativeCartanSpan) :
    nativeCartanSpanCanonicalEquiv
        (realWeylCycle_nativeCartanSpanEquiv D) =
      ⟨conjugateCanonicalDerivation realWeylCycle
          (nativeCartanSpanCanonicalEquiv D), by
        have hD : vectorCanonicalLieEquiv.symm
            (nativeCartanSpanCanonicalEquiv D) = D := by
          simpa [nativeCartanSpanCanonicalEquiv] using congrArg Subtype.val
            (nativeCartanSpanCanonicalEquiv.symm_apply_apply D)
        rw [conjugateCanonicalDerivation_apply, hD]
        exact (nativeCartanSpanCanonicalEquiv
          (realWeylCycle_nativeCartanSpanEquiv D)).property⟩ := by
  apply Subtype.ext
  simp [nativeCartanSpanCanonicalEquiv, realWeylCycle_nativeCartanSpanEquiv,
    conjugateCanonicalDerivation_apply]

theorem nativeCartanSpanCanonicalEquiv_reflection_covariant (D : nativeCartanSpan) :
    nativeCartanSpanCanonicalEquiv
        (realWeylReflection_nativeCartanSpanEquiv D) =
      ⟨conjugateCanonicalDerivation realWeylReflection
          (nativeCartanSpanCanonicalEquiv D), by
        have hD : vectorCanonicalLieEquiv.symm
            (nativeCartanSpanCanonicalEquiv D) = D := by
          simpa [nativeCartanSpanCanonicalEquiv] using congrArg Subtype.val
            (nativeCartanSpanCanonicalEquiv.symm_apply_apply D)
        rw [conjugateCanonicalDerivation_apply, hD]
        exact (nativeCartanSpanCanonicalEquiv
          (realWeylReflection_nativeCartanSpanEquiv D)).property⟩ := by
  apply Subtype.ext
  simp [nativeCartanSpanCanonicalEquiv, realWeylReflection_nativeCartanSpanEquiv,
    conjugateCanonicalDerivation_apply]

theorem nativeRootWeight_cycle_compat
    (i : InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional.NativeIndex)
    (H : InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional.Cartan) :
    InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional.transportedNativeRootWeight i
        realWeylCycle_axialCartanEquiv H =
      InfoGeometry.Lie.CanonicalZornCartanRootSystem.nativeRootWeight i
        (realWeylCycle_axialCartanEquiv.symm H) := by
  rfl

theorem nativeRootWeight_reflection_compat
    (i : InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional.NativeIndex)
    (H : InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional.Cartan) :
    InfoGeometry.Algebra.Zorn.G2NativeRootWeightFunctional.transportedNativeRootWeight i
        realWeylReflection_axialCartanEquiv H =
      InfoGeometry.Lie.CanonicalZornCartanRootSystem.nativeRootWeight i
        (realWeylReflection_axialCartanEquiv.symm H) := by
  rfl

end InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction
