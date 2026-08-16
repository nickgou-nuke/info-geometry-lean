import Mathlib

import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import proofs.RealO55ProjectiveBoundaryAction

/-!
# Native `O(5,5)` action on the PAC projective boundary

The PAC coordinate carrier and the native `V55/Q55` carrier have an explicit
projective-boundary equivalence in
`ProjectiveAffineConformalClosure55`.  This file transports the already
proved noncommutative native `OQ55` and full-real-Pin actions across that
equivalence.

No new quadratic form, scalar action, or reflection representation is
introduced here.  The only construction is conjugation of the existing
boundary representation by the proved carrier equivalence.
-/

noncomputable section

namespace ProjectiveAffineConformalNativeActionWeld

open ProjectiveAffineConformalClosure55
open RealO55ProjectiveBoundaryAction
open InfoGeometry.Projective

abbrev PACBoundary := GenericProjectiveNullBoundary55
abbrev NativeBoundary := RealO55ProjectiveBoundaryAction.Boundary

noncomputable abbrev boundaryEquiv : PACBoundary ≃ NativeBoundary :=
  ProjectiveAffineConformalClosure55.pacNativeProjectiveBoundaryEquiv

/-! ## Transport of the native orthogonal action -/

/-- Conjugate the native `OQ55` action to the PAC boundary quotient. -/
noncomputable def transportedOQBoundaryRepresentation :
    RealPin55QuadraticRepresentation.OQ55 →*
      Function.End PACBoundary where
  toFun := fun f X =>
    boundaryEquiv.symm
      (oqBoundaryRepresentation f (boundaryEquiv X))
  map_one' := by
    funext X
    change boundaryEquiv.symm
        (oqBoundaryRepresentation 1 (boundaryEquiv X)) = X
    rw [map_one]
    exact boundaryEquiv.symm_apply_apply X
  map_mul' := by
    intro f g
    funext X
    change boundaryEquiv.symm
        (oqBoundaryRepresentation (f * g) (boundaryEquiv X)) =
      boundaryEquiv.symm
        (oqBoundaryRepresentation f
          (boundaryEquiv (boundaryEquiv.symm
            (oqBoundaryRepresentation g (boundaryEquiv X)))))
    rw [map_mul]
    rw [boundaryEquiv.apply_symm_apply]
    change boundaryEquiv.symm
        (oqBoundaryRepresentation f
          (oqBoundaryRepresentation g (boundaryEquiv X))) = _
    rfl

@[simp]
theorem transportedOQBoundaryRepresentation_apply
    (f : RealPin55QuadraticRepresentation.OQ55) (X : PACBoundary) :
    transportedOQBoundaryRepresentation f X =
      boundaryEquiv.symm
        (oqBoundaryRepresentation f (boundaryEquiv X)) :=
  rfl

/-- The transported action is conjugate to the native action pointwise. -/
theorem transportedOQBoundaryRepresentation_conjugates
    (f : RealPin55QuadraticRepresentation.OQ55) (X : PACBoundary) :
    boundaryEquiv (transportedOQBoundaryRepresentation f X) =
      oqBoundaryRepresentation f (boundaryEquiv X) := by
  rw [transportedOQBoundaryRepresentation_apply]
  exact boundaryEquiv.apply_symm_apply _

/-! ## Transport of the full real Pin action -/

/-- Transport the full-real Pin boundary action to the PAC quotient. -/
noncomputable def transportedFullPinBoundaryRepresentation :
    RealPin55Core.FullPin55 →* Function.End PACBoundary :=
  transportedOQBoundaryRepresentation.comp
    RealPin55QuadraticRepresentation.fullPinToOQ55

theorem transportedFullPinBoundaryRepresentation_apply
    (g : RealPin55Core.FullPin55) (X : PACBoundary) :
    transportedFullPinBoundaryRepresentation g X =
      boundaryEquiv.symm
        (fullPinBoundaryRepresentation g (boundaryEquiv X)) := by
  change boundaryEquiv.symm
      (oqBoundaryRepresentation
        (RealPin55QuadraticRepresentation.fullPinToOQ55 g)
        (boundaryEquiv X)) = _
  have hfactor :
      fullPinBoundaryRepresentation g =
        (oqBoundaryRepresentation.comp
          RealPin55QuadraticRepresentation.fullPinToOQ55) g :=
    congrArg
      (fun F : RealPin55Core.FullPin55 →*
          Function.End NativeBoundary => F g)
      fullPinBoundaryRepresentation_factorization
  rw [hfactor]
  rfl

/-- Pin-to-orthogonal factorization survives transport to the PAC carrier. -/
theorem transportedFullPinBoundaryRepresentation_factorization :
    transportedFullPinBoundaryRepresentation =
      transportedOQBoundaryRepresentation.comp
        RealPin55QuadraticRepresentation.fullPinToOQ55 :=
  by
    simp [transportedFullPinBoundaryRepresentation]

/-! ## Surjectivity transferred to the PAC boundary carrier -/

theorem transportedFullPinBoundaryRepresentation_range_eq :
    Set.range transportedFullPinBoundaryRepresentation =
      Set.range transportedOQBoundaryRepresentation := by
  apply Set.Subset.antisymm
  · intro F hF
    rcases hF with ⟨g, rfl⟩
    exact ⟨RealPin55QuadraticRepresentation.fullPinToOQ55 g, rfl⟩
  · intro F hF
    rcases hF with ⟨f, rfl⟩
    rcases RealO55CartanDieudonne.fullPinToOQ55_surjective f with
      ⟨g, hg⟩
    refine ⟨g, ?_⟩
    calc
      transportedFullPinBoundaryRepresentation g =
          transportedOQBoundaryRepresentation
            (RealPin55QuadraticRepresentation.fullPinToOQ55 g) := by
              rw [transportedFullPinBoundaryRepresentation_factorization]
              rfl
      _ = transportedOQBoundaryRepresentation f := by rw [hg]

/-! ## Transported action laws as native boundary theorems -/

theorem transportedOQBoundaryRepresentation_one (X : PACBoundary) :
    transportedOQBoundaryRepresentation
      (1 : RealPin55QuadraticRepresentation.OQ55) X = X := by
  change boundaryEquiv.symm
      (oqBoundaryRepresentation 1 (boundaryEquiv X)) = X
  rw [map_one]
  exact boundaryEquiv.symm_apply_apply X

theorem transportedOQBoundaryRepresentation_mul
    (f g : RealPin55QuadraticRepresentation.OQ55) (X : PACBoundary) :
    transportedOQBoundaryRepresentation (f * g) X =
      transportedOQBoundaryRepresentation f
        (transportedOQBoundaryRepresentation g X) := by
  change boundaryEquiv.symm
      (oqBoundaryRepresentation (f * g) (boundaryEquiv X)) =
    boundaryEquiv.symm
      (oqBoundaryRepresentation f
        (boundaryEquiv (boundaryEquiv.symm
          (oqBoundaryRepresentation g (boundaryEquiv X)))))
  rw [map_mul]
  rw [boundaryEquiv.apply_symm_apply]
  change boundaryEquiv.symm
      (oqBoundaryRepresentation f
        (oqBoundaryRepresentation g (boundaryEquiv X))) = _
  rfl

/-! ## PAC coordinate generators as native `OQ55` elements -/

/-- Native flip of the fifth positive Witt coordinate. -/
noncomputable def nativeReflectUEquiv :
    InfoGeometry.Clifford.Clifford55.V55 ≃ₗ[ℝ]
      InfoGeometry.Clifford.Clifford55.V55 where
  toFun v :=
    (![v.1 0, v.1 1, v.1 2, v.1 3, -v.1 4], v.2)
  invFun v :=
    (![v.1 0, v.1 1, v.1 2, v.1 3, -v.1 4], v.2)
  left_inv := by
    intro v
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  right_inv := by
    intro v
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  map_add' := by
    intro v w
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp <;> ring
  map_smul' := by
    intro a v
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp

theorem nativeReflectUEquiv_preserves_Q
    (v : InfoGeometry.Clifford.Clifford55.V55) :
    InfoGeometry.Clifford.Clifford55.Q55 (nativeReflectUEquiv v) =
      InfoGeometry.Clifford.Clifford55.Q55 v := by
  rw [InfoGeometry.Clifford.Clifford55.Q55_apply,
    InfoGeometry.Clifford.Clifford55.Q55_apply]
  simp [nativeReflectUEquiv, Fin.sum_univ_succ]

/-- The PAC `u`-flip as a native `OQ55` element. -/
noncomputable def nativeReflectU :
    RealPin55QuadraticRepresentation.OQ55 :=
  ⟨nativeReflectUEquiv, nativeReflectUEquiv_preserves_Q⟩

theorem nativeReflectU_coordinate_weld (X : PACSplit55) :
    nativeReflectUEquiv (pacSplit55ToNativeV55 X) =
      pacSplit55ToNativeV55 (reflectU X) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- Native flip of the fifth negative Witt coordinate. -/
noncomputable def nativeReflectVEquiv :
    InfoGeometry.Clifford.Clifford55.V55 ≃ₗ[ℝ]
      InfoGeometry.Clifford.Clifford55.V55 where
  toFun v :=
    (v.1, ![v.2 0, v.2 1, v.2 2, v.2 3, -v.2 4])
  invFun v :=
    (v.1, ![v.2 0, v.2 1, v.2 2, v.2 3, -v.2 4])
  left_inv := by
    intro v
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  right_inv := by
    intro v
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  map_add' := by
    intro v w
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp <;> ring
  map_smul' := by
    intro a v
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp

theorem nativeReflectVEquiv_preserves_Q
    (v : InfoGeometry.Clifford.Clifford55.V55) :
    InfoGeometry.Clifford.Clifford55.Q55 (nativeReflectVEquiv v) =
      InfoGeometry.Clifford.Clifford55.Q55 v := by
  rw [InfoGeometry.Clifford.Clifford55.Q55_apply,
    InfoGeometry.Clifford.Clifford55.Q55_apply]
  simp [nativeReflectVEquiv, Fin.sum_univ_succ]

/-- The PAC `v`-flip as a native `OQ55` element. -/
noncomputable def nativeReflectV :
    RealPin55QuadraticRepresentation.OQ55 :=
  ⟨nativeReflectVEquiv, nativeReflectVEquiv_preserves_Q⟩

theorem nativeReflectV_coordinate_weld (X : PACSplit55) :
    nativeReflectVEquiv (pacSplit55ToNativeV55 X) =
      pacSplit55ToNativeV55 (reflectV X) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-! ## Native subgroup closure generated by the PAC coordinate lanes -/

noncomputable def nativePACReflectionGroup :
    Subgroup RealPin55QuadraticRepresentation.OQ55 :=
  Subgroup.closure
    {r | r = nativeReflectU ∨ r = nativeReflectV}

theorem nativeReflectU_mem_nativePACReflectionGroup :
    nativeReflectU ∈ nativePACReflectionGroup := by
  apply Subgroup.subset_closure
  exact Or.inl rfl

theorem nativeReflectV_mem_nativePACReflectionGroup :
    nativeReflectV ∈ nativePACReflectionGroup := by
  apply Subgroup.subset_closure
  exact Or.inr rfl

theorem nativePACReflectionGroup_le_fullReflectionGroup :
    nativePACReflectionGroup ≤
      RealO55CartanDieudonne.reflectionGeneratedOQ55 := by
  rw [nativePACReflectionGroup, Subgroup.closure_le]
  intro r hr
  rcases hr with rfl | rfl
  · rw [RealO55CartanDieudonne.reflectionGeneratedOQ55_eq_top]
    trivial
  · rw [RealO55CartanDieudonne.reflectionGeneratedOQ55_eq_top]
    trivial

noncomputable def nativePACBoundaryRepresentation :
    nativePACReflectionGroup →* Function.End NativeBoundary :=
  oqBoundaryRepresentation.comp (Subgroup.subtype nativePACReflectionGroup)

noncomputable def transportedNativePACBoundaryRepresentation :
    nativePACReflectionGroup →* Function.End PACBoundary :=
  transportedOQBoundaryRepresentation.comp
    (Subgroup.subtype nativePACReflectionGroup)

@[simp] theorem nativePACBoundaryRepresentation_apply
    (g : nativePACReflectionGroup) :
    nativePACBoundaryRepresentation g =
      oqBoundaryRepresentation g.1 :=
  rfl

@[simp] theorem transportedNativePACBoundaryRepresentation_apply
    (g : nativePACReflectionGroup) (X : PACBoundary) :
    transportedNativePACBoundaryRepresentation g X =
      boundaryEquiv.symm
        (oqBoundaryRepresentation g.1 (boundaryEquiv X)) :=
  rfl

/-! ## Descended generator actions -/

@[simp] theorem reflectU_involutive (X : PACSplit55) :
    reflectU (reflectU X) = X := by
  cases X
  simp [reflectU]

@[simp] theorem reflectV_involutive (X : PACSplit55) :
    reflectV (reflectV X) = X := by
  cases X
  simp [reflectV]

@[simp] theorem reflectU_zero :
    reflectU pacSplit55Zero = pacSplit55Zero := by
  simp [reflectU, pacSplit55Zero]

@[simp] theorem reflectV_zero :
    reflectV pacSplit55Zero = pacSplit55Zero := by
  simp [reflectV, pacSplit55Zero]

noncomputable def pacReflectUBoundaryHom :
    ProjectiveNullBoundaryDatum.BoundaryHom
      projectiveNullBoundaryDatum55 projectiveNullBoundaryDatum55 where
  toFun := reflectU
  map_zero := by
    change reflectU pacSplit55Zero = pacSplit55Zero
    exact reflectU_zero
  map_null := by
    intro X hX
    change Q55 X = 0 at hX
    change Q55 (reflectU X) = 0
    exact reflectU_preserves_null X hX
  map_ne_zero := by
    intro X hX hzero
    apply hX
    change reflectU X = pacSplit55Zero at hzero
    calc
      X = reflectU (reflectU X) := (reflectU_involutive X).symm
      _ = reflectU pacSplit55Zero := congrArg reflectU hzero
      _ = pacSplit55Zero := reflectU_zero
  map_scale := by
    intro u X
    exact reflectU_smul (u : ℝ) X

noncomputable def pacReflectVBoundaryHom :
    ProjectiveNullBoundaryDatum.BoundaryHom
      projectiveNullBoundaryDatum55 projectiveNullBoundaryDatum55 where
  toFun := reflectV
  map_zero := by
    change reflectV pacSplit55Zero = pacSplit55Zero
    exact reflectV_zero
  map_null := by
    intro X hX
    change Q55 X = 0 at hX
    change Q55 (reflectV X) = 0
    exact reflectV_preserves_null X hX
  map_ne_zero := by
    intro X hX hzero
    apply hX
    change reflectV X = pacSplit55Zero at hzero
    calc
      X = reflectV (reflectV X) := (reflectV_involutive X).symm
      _ = reflectV pacSplit55Zero := congrArg reflectV hzero
      _ = pacSplit55Zero := reflectV_zero
  map_scale := by
    intro u X
    exact reflectV_smul (u : ℝ) X

noncomputable def pacReflectUBoundaryAction : PACBoundary → PACBoundary :=
  ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
    pacReflectUBoundaryHom

noncomputable def pacReflectVBoundaryAction : PACBoundary → PACBoundary :=
  ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
    pacReflectVBoundaryHom

theorem pacReflectU_native_boundary_conjugacy
    (X : PACBoundary) :
    pacToNativeBoundaryAction (pacReflectUBoundaryAction X) =
      oqBoundaryAction nativeReflectU
        (pacToNativeBoundaryAction X) := by
  refine Quotient.inductionOn X ?_
  intro Z
  change
    ProjectiveNullBoundaryDatum.nullMk
        InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
        (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
          pacToNativeBoundaryHom
          (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacReflectUBoundaryHom Z)) =
      oqBoundaryAction nativeReflectU
        (ProjectiveNullBoundaryDatum.nullMk
          InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
          (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacToNativeBoundaryHom Z))
  change
    ProjectiveNullBoundaryDatum.nullMk
        InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
        (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
          pacToNativeBoundaryHom
          (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacReflectUBoundaryHom Z)) =
      ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
        (oqBoundaryHom nativeReflectU)
        (ProjectiveNullBoundaryDatum.nullMk
          InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
          (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacToNativeBoundaryHom Z))
  rw [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply congrArg
    (ProjectiveNullBoundaryDatum.nullMk
      InfoGeometry.Projective.Cl55NullBoundaryBridge.datum)
  apply ProjectiveNullBoundaryDatum.NullRep.ext_Z
  exact nativeReflectU_coordinate_weld Z.Z

theorem pacReflectV_native_boundary_conjugacy
    (X : PACBoundary) :
    pacToNativeBoundaryAction (pacReflectVBoundaryAction X) =
      oqBoundaryAction nativeReflectV
        (pacToNativeBoundaryAction X) := by
  refine Quotient.inductionOn X ?_
  intro Z
  change
    ProjectiveNullBoundaryDatum.nullMk
        InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
        (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
          pacToNativeBoundaryHom
          (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacReflectVBoundaryHom Z)) =
      oqBoundaryAction nativeReflectV
        (ProjectiveNullBoundaryDatum.nullMk
          InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
          (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacToNativeBoundaryHom Z))
  change
    ProjectiveNullBoundaryDatum.nullMk
        InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
        (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
          pacToNativeBoundaryHom
          (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacReflectVBoundaryHom Z)) =
      ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
        (oqBoundaryHom nativeReflectV)
        (ProjectiveNullBoundaryDatum.nullMk
          InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
          (ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacToNativeBoundaryHom Z))
  rw [ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply congrArg
    (ProjectiveNullBoundaryDatum.nullMk
      InfoGeometry.Projective.Cl55NullBoundaryBridge.datum)
  apply ProjectiveNullBoundaryDatum.NullRep.ext_Z
  exact nativeReflectV_coordinate_weld Z.Z

end ProjectiveAffineConformalNativeActionWeld

end noncomputable section
