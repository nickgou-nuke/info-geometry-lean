/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.CanonicalZornAutomorphismConstraintDifferential
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.CanonicalZornDerivationCentralKernel

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev DerivativeConstraintValues := Fin 8 → Fin 8 → CZ

def derivativeConstraintFailure (D : EndCZ) : CZ →ₗ[ℝ] CZ →ₗ[ℝ] CZ :=
  LinearMap.mk₂ ℝ (fun X Y => D (zMul X Y) - zMul (D X) Y - zMul X (D Y))
    (by intro X₁ X₂ Y; simp only [map_add, zMul_add_left]; abel)
    (by intro r X Y; simp only [map_smul, zMul_smul_left, smul_sub])
    (by intro X Y₁ Y₂; simp only [map_add, zMul_add_right]; abel)
    (by intro r X Y; simp only [map_smul, zMul_smul_right, smul_sub])

def derivativeConstraintReadout (D : EndCZ) : DerivativeConstraintValues :=
  fun i j => derivativeConstraintFailure D
    (circularPeirceBasis i) (circularPeirceBasis j)

noncomputable def derivativeConstraintReadoutLinear :
    EndCZ →ₗ[ℝ] DerivativeConstraintValues where
  toFun := derivativeConstraintReadout
  map_add' D E := by
    funext i j
    change (D + E) (zMul (circularPeirceBasis i) (circularPeirceBasis j)) -
      zMul ((D + E) (circularPeirceBasis i)) (circularPeirceBasis j) -
        zMul (circularPeirceBasis i) ((D + E) (circularPeirceBasis j)) = _
    change _ =
      (D (zMul (circularPeirceBasis i) (circularPeirceBasis j)) -
        zMul (D (circularPeirceBasis i)) (circularPeirceBasis j) -
          zMul (circularPeirceBasis i) (D (circularPeirceBasis j))) +
      (E (zMul (circularPeirceBasis i) (circularPeirceBasis j)) -
        zMul (E (circularPeirceBasis i)) (circularPeirceBasis j) -
          zMul (circularPeirceBasis i) (E (circularPeirceBasis j)))
    simp only [ContinuousLinearMap.add_apply, zMul_add_left, zMul_add_right]
    abel
  map_smul' r D := by
    funext i j
    change (r • D) (zMul (circularPeirceBasis i) (circularPeirceBasis j)) -
      zMul ((r • D) (circularPeirceBasis i)) (circularPeirceBasis j) -
        zMul (circularPeirceBasis i) ((r • D) (circularPeirceBasis j)) = _
    change _ = r •
      (D (zMul (circularPeirceBasis i) (circularPeirceBasis j)) -
        zMul (D (circularPeirceBasis i)) (circularPeirceBasis j) -
          zMul (circularPeirceBasis i) (D (circularPeirceBasis j)))
    simp only [ContinuousLinearMap.smul_apply, zMul_smul_left,
      zMul_smul_right]
    simp only [smul_sub]

abbrev TangentConstraintValues := CZ × DerivativeConstraintValues

noncomputable def tangentConstraintReadoutLinear :
    EndCZ →ₗ[ℝ] TangentConstraintValues where
  toFun D := (D (1 : CZ), derivativeConstraintReadoutLinear D)
  map_add' D E := by
    apply Prod.ext
    · simp only [ContinuousLinearMap.add_apply]
      rfl
    · exact derivativeConstraintReadoutLinear.map_add D E
  map_smul' r D := by
    apply Prod.ext
    · simp only [ContinuousLinearMap.smul_apply]
      rfl
    · exact derivativeConstraintReadoutLinear.map_smul r D

noncomputable def tangentConstraintReadoutContinuous :
    EndCZ →L[ℝ] TangentConstraintValues :=
  LinearMap.toContinuousLinearMap tangentConstraintReadoutLinear

theorem hasFDerivAt_tangentConstraintReadoutLinear (D : EndCZ) :
    HasFDerivAt (fun E => tangentConstraintReadoutLinear E)
      tangentConstraintReadoutContinuous D := by
  exact tangentConstraintReadoutContinuous.hasFDerivAt

noncomputable def derivativeConstraintReadoutContinuous :
    EndCZ →L[ℝ] DerivativeConstraintValues :=
  LinearMap.toContinuousLinearMap derivativeConstraintReadoutLinear

theorem hasFDerivAt_derivativeConstraintReadoutLinear (D : EndCZ) :
    HasFDerivAt derivativeConstraintReadout
      derivativeConstraintReadoutContinuous D := by
  exact derivativeConstraintReadoutContinuous.hasFDerivAt

theorem derivativeConstraintReadout_zero_iff_isDerivation (D : EndCZ) :
    derivativeConstraintReadout D = 0 ↔ IsDerivation D.toLinearMap := by
  constructor
  · intro h X Y
    have hz : derivativeConstraintFailure D X Y = 0 := by
      have hzero : derivativeConstraintFailure D = 0 := by
        apply LinearMap.ext_basis circularPeirceBasis circularPeirceBasis
        intro i j
        simpa [derivativeConstraintReadout] using congrFun (congrFun h i) j
      exact congrArg (fun q : CZ →ₗ[ℝ] CZ →ₗ[ℝ] CZ => q X Y) hzero
    have hz' : D (zMul X Y) - zMul (D X) Y - zMul X (D Y) = 0 := hz
    apply sub_eq_zero.mp
    calc
      D (zMul X Y) - (zMul (D X) Y + zMul X (D Y)) =
          D (zMul X Y) - zMul (D X) Y - zMul X (D Y) := by abel
      _ = 0 := hz'
  · intro h
    funext i j
    have hh := h (circularPeirceBasis i) (circularPeirceBasis j)
    change D (zMul (circularPeirceBasis i) (circularPeirceBasis j)) =
      zMul (D (circularPeirceBasis i)) (circularPeirceBasis j) +
        zMul (circularPeirceBasis i) (D (circularPeirceBasis j)) at hh
    apply sub_eq_zero.mpr
    calc
      D (zMul (circularPeirceBasis i) (circularPeirceBasis j)) -
          zMul (D (circularPeirceBasis i)) (circularPeirceBasis j) =
          (zMul (D (circularPeirceBasis i)) (circularPeirceBasis j) +
            zMul (circularPeirceBasis i) (D (circularPeirceBasis j))) -
            zMul (D (circularPeirceBasis i)) (circularPeirceBasis j) := by rw [hh]
      _ = zMul (circularPeirceBasis i) (D (circularPeirceBasis j)) := by abel

abbrev derivativeConstraintKernel : Type :=
  LinearMap.ker derivativeConstraintReadoutLinear

noncomputable def derivativeConstraintKernelDerivationEquiv :
    derivativeConstraintKernel ≃ₗ[ℝ] canonicalZornDerivations where
  toFun D :=
    ⟨D.1.toLinearMap,
      (mem_canonicalZornDerivations _).mpr
        ((derivativeConstraintReadout_zero_iff_isDerivation D.1).mp D.2)⟩
  invFun D :=
    ⟨LinearMap.toContinuousLinearMap D.1,
      (derivativeConstraintReadout_zero_iff_isDerivation
        (LinearMap.toContinuousLinearMap D.1)).mpr
        ((mem_canonicalZornDerivations _).mp D.2)⟩
  left_inv D := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro X
    rfl
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    rfl

  map_add' D E := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    rfl
  map_smul' r D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    rfl

theorem finrank_derivativeConstraintKernel :
    Module.finrank ℝ derivativeConstraintKernel = 14 := by
  rw [derivativeConstraintKernelDerivationEquiv.finrank_eq]
  exact InfoGeometry.Lie.CanonicalZornDerivationDimension.finrank_canonicalZornDerivations

theorem mem_derivativeConstraintKernel_iff_isDerivation (D : EndCZ) :
    D ∈ (LinearMap.ker derivativeConstraintReadoutLinear) ↔
      IsDerivation D.toLinearMap := by
  change derivativeConstraintReadoutLinear D = 0 ↔ IsDerivation D.toLinearMap
  exact derivativeConstraintReadout_zero_iff_isDerivation D

theorem derivativeConstraintReadoutLinear_apply_eq_pointwiseDerivative
    (D : EndCZ) (i j : Fin 8) :
    derivativeConstraintReadoutLinear D i j =
      automorphismConstraintDerivativeAt
        (circularPeirceBasis i) (circularPeirceBasis j)
        (ContinuousLinearMap.id ℝ CZ) D := by
  rw [automorphismConstraintDerivativeAt_apply]
  rfl

theorem derivativeConstraintReadoutContinuous_eq_pointwisePi :
    derivativeConstraintReadoutContinuous =
      ContinuousLinearMap.pi (fun i =>
        ContinuousLinearMap.pi (fun j =>
          automorphismConstraintDerivativeAt
            (circularPeirceBasis i) (circularPeirceBasis j)
            (ContinuousLinearMap.id ℝ CZ))) := by
  apply ContinuousLinearMap.ext
  intro D
  funext i j
  change derivativeConstraintReadoutLinear D i j =
    automorphismConstraintDerivativeAt
      (circularPeirceBasis i) (circularPeirceBasis j)
      (ContinuousLinearMap.id ℝ CZ) D
  exact derivativeConstraintReadoutLinear_apply_eq_pointwiseDerivative D i j

def ambientAutomorphismConstraintReadout (A : EndCZ) : TangentConstraintValues :=
  (A (1 : CZ) - (1 : CZ), fun i j =>
    automorphismConstraintAt (circularPeirceBasis i) (circularPeirceBasis j) A)

theorem hasStrictFDerivAt_ambientAutomorphismConstraintReadout_pointwise :
    HasStrictFDerivAt ambientAutomorphismConstraintReadout
      (((ContinuousLinearMap.apply ℝ CZ (1 : CZ)).prod
        (ContinuousLinearMap.pi (fun i =>
          ContinuousLinearMap.pi (fun j =>
            automorphismConstraintDerivativeAt
              (circularPeirceBasis i) (circularPeirceBasis j)
              (ContinuousLinearMap.id ℝ CZ))))))
      (ContinuousLinearMap.id ℝ CZ) := by
  have hunit : HasStrictFDerivAt
      (fun A : EndCZ => A (1 : CZ) - (1 : CZ))
      (ContinuousLinearMap.apply ℝ CZ (1 : CZ))
      (ContinuousLinearMap.id ℝ CZ) := by
    exact (ContinuousLinearMap.apply ℝ CZ (1 : CZ)).hasStrictFDerivAt.sub_const _
  have hmul : HasStrictFDerivAt
      (fun A : EndCZ => fun i j =>
        automorphismConstraintAt (circularPeirceBasis i) (circularPeirceBasis j) A)
      (ContinuousLinearMap.pi (fun i =>
        ContinuousLinearMap.pi (fun j =>
          automorphismConstraintDerivativeAt
            (circularPeirceBasis i) (circularPeirceBasis j)
            (ContinuousLinearMap.id ℝ CZ))))
      (ContinuousLinearMap.id ℝ CZ) := by
    rw [hasStrictFDerivAt_pi]
    intro i
    rw [hasStrictFDerivAt_pi]
    intro j
    exact hasStrictFDerivAt_automorphismConstraintAt
      (circularPeirceBasis i) (circularPeirceBasis j)
      (ContinuousLinearMap.id ℝ CZ)
  change HasStrictFDerivAt
    (fun A : EndCZ =>
      (A (1 : CZ) - (1 : CZ), fun i j =>
        automorphismConstraintAt (circularPeirceBasis i) (circularPeirceBasis j) A))
    (((ContinuousLinearMap.apply ℝ CZ (1 : CZ)).prod
      (ContinuousLinearMap.pi (fun i =>
        ContinuousLinearMap.pi (fun j =>
          automorphismConstraintDerivativeAt
            (circularPeirceBasis i) (circularPeirceBasis j)
            (ContinuousLinearMap.id ℝ CZ))))))
    (ContinuousLinearMap.id ℝ CZ)
  exact hunit.prodMk hmul

theorem ambientAutomorphismConstraintReadout_derivative_eq_tangentConstraintReadoutContinuous :
    (((ContinuousLinearMap.apply ℝ CZ (1 : CZ)).prod
      (ContinuousLinearMap.pi (fun i =>
        ContinuousLinearMap.pi (fun j =>
          automorphismConstraintDerivativeAt
            (circularPeirceBasis i) (circularPeirceBasis j)
            (ContinuousLinearMap.id ℝ CZ)))))) =
      tangentConstraintReadoutContinuous := by
  apply ContinuousLinearMap.ext
  intro D
  apply Prod.ext
  · rfl
  · change
      (ContinuousLinearMap.pi (fun i =>
        ContinuousLinearMap.pi (fun j =>
          automorphismConstraintDerivativeAt
            (circularPeirceBasis i) (circularPeirceBasis j)
            (ContinuousLinearMap.id ℝ CZ))) D) =
        derivativeConstraintReadoutContinuous D
    rw [derivativeConstraintReadoutContinuous_eq_pointwisePi]

theorem hasStrictFDerivAt_ambientAutomorphismConstraintReadout :
    HasStrictFDerivAt ambientAutomorphismConstraintReadout
      tangentConstraintReadoutContinuous
      (ContinuousLinearMap.id ℝ CZ) := by
  rw [← ambientAutomorphismConstraintReadout_derivative_eq_tangentConstraintReadoutContinuous]
  exact hasStrictFDerivAt_ambientAutomorphismConstraintReadout_pointwise

theorem ambientAutomorphismConstraintReadout_one_zero :
    ambientAutomorphismConstraintReadout (ContinuousLinearMap.id ℝ CZ) = 0 := by
  apply Prod.ext
  · simp [ambientAutomorphismConstraintReadout]
  · funext i j
    simp [ambientAutomorphismConstraintReadout, automorphismConstraintAt]

theorem tangentConstraintReadoutLinear_zero_iff_isDerivation (D : EndCZ) :
    tangentConstraintReadoutLinear D = 0 ↔ IsDerivation D.toLinearMap := by
  constructor
  · intro h
    have hs : derivativeConstraintReadoutLinear D = 0 := by
      simpa [tangentConstraintReadoutLinear] using congrArg Prod.snd h
    exact (derivativeConstraintReadout_zero_iff_isDerivation D).mp hs
  · intro h
    apply Prod.ext
    · change D (1 : CZ) = 0
      exact derivation_apply_one
        ⟨D.toLinearMap, (mem_canonicalZornDerivations _).mpr h⟩
    · exact (derivativeConstraintReadout_zero_iff_isDerivation D).mpr h

abbrev tangentConstraintKernel : Type :=
  LinearMap.ker tangentConstraintReadoutLinear

noncomputable def tangentConstraintKernelDerivationEquiv :
    tangentConstraintKernel ≃ₗ[ℝ] canonicalZornDerivations where
  toFun D :=
    ⟨D.1.toLinearMap,
      (mem_canonicalZornDerivations _).mpr
        ((tangentConstraintReadoutLinear_zero_iff_isDerivation D.1).mp D.2)⟩
  invFun D :=
    ⟨LinearMap.toContinuousLinearMap D.1,
      (tangentConstraintReadoutLinear_zero_iff_isDerivation
        (LinearMap.toContinuousLinearMap D.1)).mpr
        ((mem_canonicalZornDerivations _).mp D.2)⟩
  left_inv D := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro X
    rfl
  right_inv D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    rfl
  map_add' D E := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    rfl
  map_smul' r D := by
    apply Subtype.ext
    apply LinearMap.ext
    intro X
    rfl

theorem finrank_tangentConstraintKernel :
    Module.finrank ℝ tangentConstraintKernel = 14 := by
  rw [tangentConstraintKernelDerivationEquiv.finrank_eq]
  exact InfoGeometry.Lie.CanonicalZornDerivationDimension.finrank_canonicalZornDerivations

theorem exists_tangentConstraintKernel_isCompl :
    ∃ S : Submodule ℝ EndCZ,
      IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S := by
  exact Submodule.exists_isCompl (LinearMap.ker tangentConstraintReadoutLinear)

noncomputable def endCZToModuleEnd :
    EndCZ ≃ₗ[ℝ] Module.End ℝ CZ where
  toFun D := D.toLinearMap
  invFun D := LinearMap.toContinuousLinearMap D
  left_inv D := by
    apply ContinuousLinearMap.ext
    intro X
    rfl
  right_inv D := by
    apply LinearMap.ext
    intro X
    rfl
  map_add' D E := by
    apply LinearMap.ext
    intro X
    rfl
  map_smul' r D := by
    apply LinearMap.ext
    intro X
    rfl

theorem finrank_endCZ : Module.finrank ℝ EndCZ = 64 := by
  rw [endCZToModuleEnd.finrank_eq, Module.finrank_linearMap,
    InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.canonicalZorn_finrank]

theorem finrank_tangentConstraintKernel_complement
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S) :
    Module.finrank ℝ S = 50 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker tangentConstraintReadoutLinear) S
  rw [hS.sup_eq_top, hS.inf_eq_bot] at h
  have h' : 64 + 0 = 14 + Module.finrank ℝ S := by
    simpa only [finrank_top ℝ EndCZ, finrank_bot ℝ EndCZ,
      finrank_endCZ, finrank_tangentConstraintKernel] using h
  omega

theorem finrank_tangentConstraintReadout_range :
    Module.finrank ℝ (LinearMap.range tangentConstraintReadoutLinear) = 50 := by
  have h := LinearMap.finrank_range_add_finrank_ker tangentConstraintReadoutLinear
  rw [finrank_tangentConstraintKernel, finrank_endCZ] at h
  omega

noncomputable def tangentConstraintReadoutToRange :
    EndCZ →ₗ[ℝ] LinearMap.range tangentConstraintReadoutLinear :=
  LinearMap.codRestrict (LinearMap.range tangentConstraintReadoutLinear)
    tangentConstraintReadoutLinear (fun D => by
      change ∃ E, tangentConstraintReadoutLinear E = tangentConstraintReadoutLinear D
      exact ⟨D, rfl⟩)

theorem tangentConstraintReadoutToRange_surjective :
    Function.Surjective tangentConstraintReadoutToRange := by
  intro y
  rcases y.property with ⟨D, hD⟩
  exact ⟨D, Subtype.ext hD⟩

noncomputable def tangentConstraintReadoutContinuousToRange :
    EndCZ →L[ℝ] LinearMap.range tangentConstraintReadoutLinear :=
  tangentConstraintReadoutContinuous.codRestrict
    (LinearMap.range tangentConstraintReadoutLinear) (fun D => by
      change ∃ E, tangentConstraintReadoutLinear E = tangentConstraintReadoutLinear D
      exact ⟨D, rfl⟩)

theorem tangentConstraintReadoutContinuousToRange_surjective :
    Function.Surjective tangentConstraintReadoutContinuousToRange := by
  intro y
  rcases y.property with ⟨D, hD⟩
  exact ⟨D, Subtype.ext hD⟩

noncomputable def tangentConstraintRestriction
    (S : Submodule ℝ EndCZ) :
    S →ₗ[ℝ] LinearMap.range tangentConstraintReadoutLinear :=
  LinearMap.codRestrict (LinearMap.range tangentConstraintReadoutLinear)
    (tangentConstraintReadoutLinear.domRestrict S) (fun D => by
      change ∃ E, tangentConstraintReadoutLinear E = tangentConstraintReadoutLinear D.1
      exact ⟨D.1, rfl⟩)

theorem tangentConstraintRestriction_injective
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S) :
    Function.Injective (tangentConstraintRestriction S) := by
  intro D E h
  apply Subtype.ext
  have hz : tangentConstraintReadoutLinear (D.1 - E.1) = 0 := by
    have hv := congrArg Subtype.val h
    rw [map_sub]
    exact sub_eq_zero.mpr (by
      simpa [tangentConstraintRestriction] using hv)
  have hk : D.1 - E.1 ∈ LinearMap.ker tangentConstraintReadoutLinear :=
    LinearMap.mem_ker.mpr hz
  have hs : D.1 - E.1 ∈ S := S.sub_mem D.2 E.2
  have hzero : D.1 - E.1 = 0 :=
    (Submodule.disjoint_def.mp hS.disjoint) (D.1 - E.1) hk hs
  exact sub_eq_zero.mp hzero

theorem tangentConstraintRestriction_surjective
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S) :
    Function.Surjective (tangentConstraintRestriction S) := by
  intro y
  rcases y.property with ⟨D, hD⟩
  have hmem : D ∈ LinearMap.ker tangentConstraintReadoutLinear ⊔ S := by
    rw [hS.sup_eq_top]
    trivial
  rcases Submodule.mem_sup.mp hmem with ⟨K, hK, Q, hQ, hKQ⟩
  refine ⟨⟨Q, hQ⟩, ?_⟩
  apply Subtype.ext
  have hkernel : tangentConstraintReadoutLinear K = 0 :=
    LinearMap.mem_ker.mp hK
  have hread : tangentConstraintReadoutLinear Q = tangentConstraintReadoutLinear D := by
    rw [← hKQ, map_add, hkernel, zero_add]
  exact hread.trans hD

noncomputable def tangentConstraintRestrictionEquiv
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S) :
    S ≃ₗ[ℝ] LinearMap.range tangentConstraintReadoutLinear :=
  LinearEquiv.ofBijective (tangentConstraintRestriction S)
    ⟨tangentConstraintRestriction_injective hS,
      tangentConstraintRestriction_surjective hS⟩

theorem finrank_tangentConstraintRestriction_domain
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S) :
    Module.finrank ℝ S = 50 := by
  rw [(tangentConstraintRestrictionEquiv hS).finrank_eq]
  exact finrank_tangentConstraintReadout_range

noncomputable def tangentConstraintKernelProjection
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S) :
    EndCZ →ₗ[ℝ] LinearMap.ker tangentConstraintReadoutLinear :=
  (LinearMap.ker tangentConstraintReadoutLinear).linearProjOfIsCompl S hS

theorem tangentConstraintKernelProjection_apply_kernel
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S)
    (D : LinearMap.ker tangentConstraintReadoutLinear) :
    tangentConstraintKernelProjection hS D.1 = D := by
  exact Submodule.linearProjOfIsCompl_apply_left hS D

theorem tangentConstraintKernelProjection_apply_complement
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S)
    (D : S) :
    tangentConstraintKernelProjection hS D.1 = 0 := by
  exact Submodule.linearProjOfIsCompl_apply_right hS D

noncomputable def tangentConstraintComplementProjection
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S) :
    EndCZ →ₗ[ℝ] S :=
  S.linearProjOfIsCompl (LinearMap.ker tangentConstraintReadoutLinear) hS.symm

theorem tangentConstraint_decomposition
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S)
    (D : EndCZ) :
    (D : EndCZ) =
      (tangentConstraintKernelProjection hS D : EndCZ) +
        (tangentConstraintComplementProjection hS D : EndCZ) := by
  have hmem : D ∈ LinearMap.ker tangentConstraintReadoutLinear ⊔ S := by
    rw [hS.sup_eq_top]
    trivial
  rcases Submodule.mem_sup.mp hmem with ⟨K, hK, Q, hQ, hKQ⟩
  have hprojK : tangentConstraintKernelProjection hS D = ⟨K, hK⟩ := by
    have hK' := Submodule.linearProjOfIsCompl_apply_left hS (⟨K, hK⟩ :
      LinearMap.ker tangentConstraintReadoutLinear)
    have hQ' := Submodule.linearProjOfIsCompl_apply_right hS (⟨Q, hQ⟩ : S)
    calc
      tangentConstraintKernelProjection hS D =
          tangentConstraintKernelProjection hS (K + Q) := by rw [hKQ]
      _ = tangentConstraintKernelProjection hS K +
          tangentConstraintKernelProjection hS Q := by rw [map_add]
      _ = ⟨K, hK⟩ := by
        change (LinearMap.ker tangentConstraintReadoutLinear).linearProjOfIsCompl S hS K +
            (LinearMap.ker tangentConstraintReadoutLinear).linearProjOfIsCompl S hS Q =
          ⟨K, hK⟩
        rw [hK', hQ']
        simp
  have hprojQ : tangentConstraintComplementProjection hS D = ⟨Q, hQ⟩ := by
    have hK' := Submodule.linearProjOfIsCompl_apply_right hS.symm (⟨K, hK⟩ :
      LinearMap.ker tangentConstraintReadoutLinear)
    have hQ' := Submodule.linearProjOfIsCompl_apply_left hS.symm (⟨Q, hQ⟩ : S)
    calc
      tangentConstraintComplementProjection hS D =
          tangentConstraintComplementProjection hS (K + Q) := by rw [hKQ]
      _ = tangentConstraintComplementProjection hS K +
          tangentConstraintComplementProjection hS Q := by rw [map_add]
      _ = ⟨Q, hQ⟩ := by
        change S.linearProjOfIsCompl (LinearMap.ker tangentConstraintReadoutLinear) hS.symm K +
            S.linearProjOfIsCompl (LinearMap.ker tangentConstraintReadoutLinear) hS.symm Q =
          ⟨Q, hQ⟩
        rw [hK', hQ']
        simp
  rw [hprojK, hprojQ]
  exact hKQ.symm

noncomputable def endCZKernelComplementEquiv
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S) :
    EndCZ ≃ₗ[ℝ]
      (LinearMap.ker tangentConstraintReadoutLinear × S) :=
  (Submodule.prodEquivOfIsCompl
    (LinearMap.ker tangentConstraintReadoutLinear) S hS).symm

theorem endCZKernelComplementEquiv_apply
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S)
    (D : EndCZ) :
    endCZKernelComplementEquiv hS D =
      (tangentConstraintKernelProjection hS D,
        tangentConstraintComplementProjection hS D) := by
  exact Submodule.prodEquivOfIsCompl_symm_apply hS D

noncomputable def tangentConstraintRestrictionContinuousEquiv
    {S : Submodule ℝ EndCZ}
    (hS : IsCompl (LinearMap.ker tangentConstraintReadoutLinear) S) :
    S ≃L[ℝ] LinearMap.range tangentConstraintReadoutLinear :=
  (tangentConstraintRestrictionEquiv hS).toContinuousLinearEquiv

end
end InfoGeometry.Canonical
