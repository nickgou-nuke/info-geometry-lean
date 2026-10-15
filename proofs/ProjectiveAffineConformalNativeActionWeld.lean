import Mathlib

import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import InfoGeometry.Canonical.PACNativeCliffordBridge
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
open InfoGeometry.Projective.ProjectiveNullBoundaryDatum
open InfoGeometry.Canonical.PACNativeCliffordBridge
open InfoGeometry.Projective.Cl55NullBoundaryBridge

def projectiveNullBoundaryDatum55 :
    ProjectiveNullBoundaryDatum ℝ ℝ ProjectiveAffineConformalClosure55.PACSplit55 where
  q := ProjectiveAffineConformalClosure55.Q55
  zero := pacSplit55Zero
  scale := fun u X => ProjectiveAffineConformalClosure55.smul55 (u : ℝ) X
  scale_one := by
    intro X
    cases X
    simp [ProjectiveAffineConformalClosure55.smul55]
  scale_mul := by
    intro u v X
    cases X
    simp [ProjectiveAffineConformalClosure55.smul55, mul_assoc]
  null_scale := by
    intro u X
    rw [ProjectiveAffineConformalClosure55.Q55_smul]
    constructor
    · intro h
      have h' : (u : ℝ) ^ 2 *
          ProjectiveAffineConformalClosure55.Q55 X = 0 := h
      rcases mul_eq_zero.mp h' with hu | hX
      · have hu' : (u : ℝ) = 0 := by
          have hu2 : (u : ℝ) * (u : ℝ) = 0 := by
            simpa [pow_two] using hu
          rcases mul_eq_zero.mp hu2 with h | h
          · exact h
          · exact h
        exact (Units.ne_zero u hu').elim
      · exact hX
    · intro hX
      rw [hX]
      simp
  scale_ne_zero := by
    intro u X hX hs
    apply hX
    apply (pac55ToV55_eq_zero_iff X).1
    have hs' := congrArg pac55ToV55 hs
    rw [pac55ToV55_smul, pac55ToV55_pacSplit55Zero] at hs'
    rcases smul_eq_zero.mp hs' with hu | hvec
    · exact (Units.ne_zero u hu).elim
    · exact hvec

noncomputable def pacToNativeNullRep
    (X : NullRep projectiveNullBoundaryDatum55) : NullRep datum where
  Z := pac55ToV55 X.Z
  null := by
    change InfoGeometry.Clifford.Clifford55.Q55 (pac55ToV55 X.Z) = 0
    rw [pac55ToV55_Q55]
    exact X.null
  nonzero := by
    intro hzero
    exact X.nonzero ((pac55ToV55_eq_zero_iff X.Z).mp hzero)

noncomputable def pacNullRepToNativeBoundary
    (X : NullRep projectiveNullBoundaryDatum55) : Boundary :=
  InfoGeometry.Projective.ProjectiveNullBoundaryDatum.nullMk datum
    (pacToNativeNullRep X)

noncomputable def boundaryEquiv :
    ProjectiveNullBoundary projectiveNullBoundaryDatum55 ≃ Boundary := by
  classical
  let toNative : ProjectiveNullBoundary projectiveNullBoundaryDatum55 → Boundary :=
    Quotient.lift pacNullRepToNativeBoundary (by
      intro X Y hXY
      rcases hXY with ⟨u, hXY⟩
      exact pacNullToNativeBoundary_eq_of_sameProjectiveLine
        X.null X.nonzero Y.null Y.nonzero
        ⟨(u : ℝ), Units.ne_zero u, hXY.symm⟩)
  let toPacRep : NullRep datum → NullRep projectiveNullBoundaryDatum55 := fun X =>
    { Z := v55ToPac55 X.Z
      null := by
        change ProjectiveAffineConformalClosure55.Q55 (v55ToPac55 X.Z) = 0
        rw [← pac55ToV55_Q55, pac55ToV55_v55ToPac55]
        exact X.null
      nonzero := by
        intro h
        apply X.nonzero
        have h' := congrArg pac55ToV55 h
        have hzero : pac55ToV55 (v55ToPac55 X.Z) =
            pac55ToV55 pacSplit55Zero := h'
        have hvec : X.Z = (0 : InfoGeometry.Clifford.Clifford55.V55) := by
          simpa [pac55ToV55_v55ToPac55, pac55ToV55_pacSplit55Zero] using hzero
        exact hvec }
  let toPac : Boundary → ProjectiveNullBoundary projectiveNullBoundaryDatum55 :=
    Quotient.lift (fun X => Quotient.mk _ (toPacRep X)) (by
      intro X Y hXY
      rcases hXY with ⟨u, hXY⟩
      apply Quotient.sound
      refine ⟨u, ?_⟩
      apply pac55Equiv.injective
      change pac55ToV55
          (ProjectiveAffineConformalClosure55.smul55 (u : ℝ)
            (v55ToPac55 X.Z)) = pac55ToV55 (v55ToPac55 Y.Z)
      rw [pac55ToV55_smul]
      rw [pac55ToV55_v55ToPac55, pac55ToV55_v55ToPac55]
      exact hXY)
  refine ⟨toNative, toPac, ?_, ?_⟩
  · intro X
    induction X using Quotient.inductionOn with
    | h X =>
      change Quotient.mk _ (toPacRep
        { Z := pac55ToV55 X.Z
          null := by
            change InfoGeometry.Clifford.Clifford55.Q55
              (pac55ToV55 X.Z) = 0
            rw [pac55ToV55_Q55]
            exact X.null
          nonzero := by
            intro hz
            exact X.nonzero ((pac55ToV55_eq_zero_iff X.Z).mp hz) }) =
        Quotient.mk _ X
      apply Quotient.sound
      refine ⟨1, ?_⟩
      simpa [toPacRep, projectiveNullBoundaryDatum55,
        pac55ToV55_v55ToPac55, ProjectiveAffineConformalClosure55.smul55]
  · intro X
    induction X using Quotient.inductionOn with
    | h X =>
      dsimp [toNative, toPac, pacNullRepToNativeBoundary,
        pacNullToNativeBoundary, toPacRep]
      apply Quotient.sound
      refine ⟨1, ?_⟩
      rw [InfoGeometry.Projective.Cl55NullBoundaryBridge.datum.scale_one]
      change pac55ToV55 (v55ToPac55 X.Z) = X.Z
      exact pac55ToV55_v55ToPac55 X.Z

/-! ## Transport of the native orthogonal action -/

/-- Conjugate the native `OQ55` action to the PAC boundary quotient. -/
noncomputable def transportedOQBoundaryRepresentation :
    RealPin55QuadraticRepresentation.OQ55 →*
      Function.End (ProjectiveNullBoundary projectiveNullBoundaryDatum55) where
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

/-- The transported action is conjugate to the native action pointwise. -/
theorem transportedOQBoundaryRepresentation_conjugates
    (f : RealPin55QuadraticRepresentation.OQ55) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    boundaryEquiv (transportedOQBoundaryRepresentation f X) =
      oqBoundaryRepresentation f (boundaryEquiv X) := by
  change boundaryEquiv
      (boundaryEquiv.symm
        (oqBoundaryRepresentation f (boundaryEquiv X))) =
    oqBoundaryRepresentation f (boundaryEquiv X)
  exact boundaryEquiv.apply_symm_apply _

/-! Native permutation-valued transport.  The older `Function.End` action
above remains as a compatibility surface; this is the bijective owner. -/

noncomputable def transportedOQBoundaryPermutationRepresentation :
    RealPin55QuadraticRepresentation.OQ55 →* Equiv.Perm (ProjectiveNullBoundary projectiveNullBoundaryDatum55) :=
  { toFun := fun f =>
      boundaryEquiv.trans
        ((oqBoundaryPermutationRepresentation f).trans boundaryEquiv.symm)
    map_one' := by
      ext X
      simp
    map_mul' := by
      intro f g
      ext X
      simp [Equiv.Perm.mul_apply] }

@[simp] theorem transportedOQBoundaryPermutationRepresentation_apply
    (f : RealPin55QuadraticRepresentation.OQ55) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    transportedOQBoundaryPermutationRepresentation f X =
      boundaryEquiv.symm
        (oqBoundaryPermutationRepresentation f (boundaryEquiv X)) :=
  rfl

/-! ## Transport of the full real Pin action -/

/-- Transport the full-real Pin boundary action to the PAC quotient. -/
noncomputable def transportedFullPinBoundaryRepresentation :
    RealPin55Core.FullPin55 →* Function.End (ProjectiveNullBoundary projectiveNullBoundaryDatum55) :=
  transportedOQBoundaryRepresentation.comp
    RealPin55QuadraticRepresentation.fullPinToOQ55

theorem transportedFullPinBoundaryRepresentation_apply
    (g : RealPin55Core.FullPin55) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
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
          Function.End InfoGeometry.Projective.Cl55NullBoundaryBridge.Boundary => F g)
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

noncomputable def transportedFullPinBoundaryPermutationRepresentation :
    RealPin55Core.FullPin55 →* Equiv.Perm (ProjectiveNullBoundary projectiveNullBoundaryDatum55) :=
  transportedOQBoundaryPermutationRepresentation.comp
    RealPin55QuadraticRepresentation.fullPinToOQ55

@[simp] theorem transportedFullPinBoundaryPermutationRepresentation_apply
    (g : RealPin55Core.FullPin55) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    transportedFullPinBoundaryPermutationRepresentation g X =
      boundaryEquiv.symm
        (oqBoundaryPermutationRepresentation
          (RealPin55QuadraticRepresentation.fullPinToOQ55 g)
          (boundaryEquiv X)) :=
  rfl

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

theorem transportedOQBoundaryRepresentation_one (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    transportedOQBoundaryRepresentation
      (1 : RealPin55QuadraticRepresentation.OQ55) X = X := by
  change boundaryEquiv.symm
      (oqBoundaryRepresentation 1 (boundaryEquiv X)) = X
  rw [map_one]
  exact boundaryEquiv.symm_apply_apply X

theorem transportedOQBoundaryRepresentation_mul
    (f g : RealPin55QuadraticRepresentation.OQ55) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
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
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp; ring
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
    nativeReflectUEquiv (pac55ToV55 X) =
      pac55ToV55 (reflectU X) := by
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
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp; ring
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
    nativeReflectVEquiv (pac55ToV55 X) =
      pac55ToV55 (reflectV X) := by
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
    nativePACReflectionGroup →* Function.End InfoGeometry.Projective.Cl55NullBoundaryBridge.Boundary :=
  oqBoundaryRepresentation.comp (Subgroup.subtype nativePACReflectionGroup)

noncomputable def transportedNativePACBoundaryRepresentation :
    nativePACReflectionGroup →* Function.End (ProjectiveNullBoundary projectiveNullBoundaryDatum55) :=
  transportedOQBoundaryRepresentation.comp
    (Subgroup.subtype nativePACReflectionGroup)

noncomputable def nativePACBoundaryPermutationRepresentation :
    nativePACReflectionGroup →* Equiv.Perm InfoGeometry.Projective.Cl55NullBoundaryBridge.Boundary :=
  oqBoundaryPermutationRepresentation.comp
    (Subgroup.subtype nativePACReflectionGroup)

noncomputable def transportedNativePACBoundaryPermutationRepresentation :
    nativePACReflectionGroup →* Equiv.Perm (ProjectiveNullBoundary projectiveNullBoundaryDatum55) :=
  transportedOQBoundaryPermutationRepresentation.comp
    (Subgroup.subtype nativePACReflectionGroup)

@[simp] theorem transportedNativePACBoundaryPermutationRepresentation_apply
    (g : nativePACReflectionGroup) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    transportedNativePACBoundaryPermutationRepresentation g X =
      boundaryEquiv.symm
        (oqBoundaryPermutationRepresentation g.1 (boundaryEquiv X)) :=
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
    InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom
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
    InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom
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

noncomputable def pacReflectUBoundaryAction : ProjectiveNullBoundary projectiveNullBoundaryDatum55 → ProjectiveNullBoundary projectiveNullBoundaryDatum55 :=
  InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
    pacReflectUBoundaryHom

noncomputable def pacReflectVBoundaryAction : ProjectiveNullBoundary projectiveNullBoundaryDatum55 → ProjectiveNullBoundary projectiveNullBoundaryDatum55 :=
  InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
    pacReflectVBoundaryHom

noncomputable def pacToNativeBoundaryAction :
    ProjectiveNullBoundary projectiveNullBoundaryDatum55 → Boundary :=
  Quotient.lift pacNullRepToNativeBoundary (by
    intro X Y hXY
    rcases hXY with ⟨u, hXY⟩
    exact pacNullToNativeBoundary_eq_of_sameProjectiveLine
      X.null X.nonzero Y.null Y.nonzero
      ⟨(u : ℝ), Units.ne_zero u, hXY.symm⟩)

theorem pacReflectU_native_boundary_conjugacy
    (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    pacToNativeBoundaryAction (pacReflectUBoundaryAction X) =
      oqBoundaryAction nativeReflectU
        (pacToNativeBoundaryAction X) := by
  refine Quotient.inductionOn X ?_
  intro Z
  change
    InfoGeometry.Projective.ProjectiveNullBoundaryDatum.nullMk
        InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
        (pacToNativeNullRep
          (InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacReflectUBoundaryHom Z)) =
      InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
        (oqBoundaryHom nativeReflectU)
        (InfoGeometry.Projective.ProjectiveNullBoundaryDatum.nullMk
          InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
          (pacToNativeNullRep Z))
  rw [InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply congrArg
    (InfoGeometry.Projective.ProjectiveNullBoundaryDatum.nullMk
      InfoGeometry.Projective.Cl55NullBoundaryBridge.datum)
  apply InfoGeometry.Projective.ProjectiveNullBoundaryDatum.NullRep.ext_Z
  exact nativeReflectU_coordinate_weld Z.Z

theorem pacReflectV_native_boundary_conjugacy
    (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    pacToNativeBoundaryAction (pacReflectVBoundaryAction X) =
      oqBoundaryAction nativeReflectV
        (pacToNativeBoundaryAction X) := by
  refine Quotient.inductionOn X ?_
  intro Z
  change
    InfoGeometry.Projective.ProjectiveNullBoundaryDatum.nullMk
        InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
        (pacToNativeNullRep
          (InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom.mapNullRep
            pacReflectVBoundaryHom Z)) =
      InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary
        (oqBoundaryHom nativeReflectV)
        (InfoGeometry.Projective.ProjectiveNullBoundaryDatum.nullMk
          InfoGeometry.Projective.Cl55NullBoundaryBridge.datum
          (pacToNativeNullRep Z))
  rw [InfoGeometry.Projective.ProjectiveNullBoundaryDatum.BoundaryHom.mapBoundary_nullMk]
  apply congrArg
    (InfoGeometry.Projective.ProjectiveNullBoundaryDatum.nullMk
      InfoGeometry.Projective.Cl55NullBoundaryBridge.datum)
  apply InfoGeometry.Projective.ProjectiveNullBoundaryDatum.NullRep.ext_Z
  exact nativeReflectV_coordinate_weld Z.Z

/-! ## Native Mathlib group actions -/

noncomputable instance transportedOQBoundaryMulAction :
    MulAction RealPin55QuadraticRepresentation.OQ55 (ProjectiveNullBoundary projectiveNullBoundaryDatum55) where
  smul := fun f X => transportedOQBoundaryRepresentation f X
  one_smul := by
    intro X
    exact transportedOQBoundaryRepresentation_one X
  mul_smul := by
    intro f g X
    exact transportedOQBoundaryRepresentation_mul f g X

noncomputable instance transportedFullPinBoundaryMulAction :
    MulAction RealPin55Core.FullPin55 (ProjectiveNullBoundary projectiveNullBoundaryDatum55) where
  smul := fun g X => transportedFullPinBoundaryRepresentation g X
  one_smul := by
    intro X
    change transportedFullPinBoundaryRepresentation
        (1 : RealPin55Core.FullPin55) X = X
    rw [map_one]
    rfl
  mul_smul := by
    intro g h X
    change transportedFullPinBoundaryRepresentation (g * h) X =
      transportedFullPinBoundaryRepresentation g
        (transportedFullPinBoundaryRepresentation h X)
    rw [map_mul]
    rfl

theorem fullPin_smul_factors_through_OQ55
    (g : RealPin55Core.FullPin55) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    g • X = (RealPin55QuadraticRepresentation.fullPinToOQ55 g) • X := by
  change transportedFullPinBoundaryRepresentation g X =
    transportedOQBoundaryRepresentation
      (RealPin55QuadraticRepresentation.fullPinToOQ55 g) X
  rw [transportedFullPinBoundaryRepresentation_factorization]
  rfl

/-! ## Reflection-generated projective-affine action -/

/-- The concrete native reflection subgroup acts on the native boundary. -/
noncomputable instance nativePACReflectionGroupMulAction :
    MulAction nativePACReflectionGroup InfoGeometry.Projective.Cl55NullBoundaryBridge.Boundary where
  smul := fun g X => oqBoundaryAction g.1 X
  one_smul := by
    intro X
    change oqBoundaryRepresentation (1 : RealPin55QuadraticRepresentation.OQ55) X = X
    rw [map_one]
    rfl
  mul_smul := by
    intro g h X
    change oqBoundaryAction (g.1 * h.1) X =
      oqBoundaryAction g.1 (oqBoundaryAction h.1 X)
    change oqBoundaryRepresentation (g.1 * h.1) X =
      oqBoundaryRepresentation g.1
        (oqBoundaryRepresentation h.1 X)
    rw [map_mul]
    rfl

@[simp] theorem nativePACReflectionGroup_smul_eq
    (g : nativePACReflectionGroup) (X : InfoGeometry.Projective.Cl55NullBoundaryBridge.Boundary) :
    g • X = oqBoundaryAction g.1 X :=
  rfl

theorem pacReflectU_native_smul_conjugacy
    (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    pacToNativeBoundaryAction (pacReflectUBoundaryAction X) =
      (⟨nativeReflectU, nativeReflectU_mem_nativePACReflectionGroup⟩ :
        nativePACReflectionGroup) •
        pacToNativeBoundaryAction X := by
  simpa only [nativePACReflectionGroup_smul_eq,
    oqBoundaryRepresentation, transportedOQBoundaryRepresentation] using
    pacReflectU_native_boundary_conjugacy X

theorem pacReflectV_native_smul_conjugacy
    (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    pacToNativeBoundaryAction (pacReflectVBoundaryAction X) =
      (⟨nativeReflectV, nativeReflectV_mem_nativePACReflectionGroup⟩ :
        nativePACReflectionGroup) •
        pacToNativeBoundaryAction X := by
  simpa only [nativePACReflectionGroup_smul_eq,
    oqBoundaryRepresentation, transportedOQBoundaryRepresentation] using
    pacReflectV_native_boundary_conjugacy X

/-- The PAC/native projective boundary equivalence intertwines the native
reflection subgroup actions. -/
theorem boundaryEquiv_nativePACReflectionGroup_smul
    (g : nativePACReflectionGroup) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    boundaryEquiv (g • X) = g • boundaryEquiv X := by
  change boundaryEquiv
      (transportedOQBoundaryRepresentation g.1 X) =
    oqBoundaryAction g.1 (boundaryEquiv X)
  exact transportedOQBoundaryRepresentation_conjugates g.1 X

/-- The PAC/native boundary equivalence intertwines the full native `OQ55`
action. -/
theorem boundaryEquiv_oq_smul
    (f : RealPin55QuadraticRepresentation.OQ55) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    boundaryEquiv (f • X) =
      oqBoundaryAction f (boundaryEquiv X) := by
  change boundaryEquiv
      (transportedOQBoundaryRepresentation f X) =
    oqBoundaryAction f (boundaryEquiv X)
  exact transportedOQBoundaryRepresentation_conjugates f X

/-! ## Constructive reflection action on the PAC boundary -/

noncomputable instance reflectionGeneratedPACBoundaryMulAction :
    MulAction RealO55CartanDieudonne.reflectionGeneratedOQ55 (ProjectiveNullBoundary projectiveNullBoundaryDatum55) where
  smul := fun r X => transportedOQBoundaryRepresentation r.1 X
  one_smul := by
    intro X
    change transportedOQBoundaryRepresentation
        (1 : RealPin55QuadraticRepresentation.OQ55) X = X
    rw [map_one]
    rfl
  mul_smul := by
    intro r h X
    change transportedOQBoundaryRepresentation (r.1 * h.1) X =
      transportedOQBoundaryRepresentation r.1
        (transportedOQBoundaryRepresentation h.1 X)
    rw [map_mul]
    rfl

theorem exists_reflectionGenerated_pacBoundary_smul_eq
    (X Y : ProjectiveNullBoundary projectiveNullBoundaryDatum55)
    (hXY : ∃ f : RealPin55QuadraticRepresentation.OQ55,
      f • boundaryEquiv X = boundaryEquiv Y) :
    ∃ r : RealO55CartanDieudonne.reflectionGeneratedOQ55, r • X = Y := by
  rcases hXY with ⟨f, hf⟩
  rcases
      RealO55ProjectiveBoundaryAction.exists_reflectionGenerated_boundary_smul_eq
        f (boundaryEquiv X) with
    ⟨r, hr⟩
  refine ⟨r, ?_⟩
  apply boundaryEquiv.injective
  calc
    boundaryEquiv (r • X) = r • boundaryEquiv X :=
      boundaryEquiv_oq_smul r.1 X
    _ = f • boundaryEquiv X := hr
    _ = boundaryEquiv Y := hf

/-- The PAC/native boundary equivalence intertwines the full real Pin
action. -/
theorem boundaryEquiv_fullPin_smul
    (g : RealPin55Core.FullPin55) (X : ProjectiveNullBoundary projectiveNullBoundaryDatum55) :
    boundaryEquiv (g • X) =
      fullPinBoundaryAction g (boundaryEquiv X) := by
  change boundaryEquiv
      (transportedFullPinBoundaryRepresentation g X) =
    fullPinBoundaryAction g (boundaryEquiv X)
  rw [transportedFullPinBoundaryRepresentation_apply]
  exact boundaryEquiv.apply_symm_apply _

/-- A native orthogonal transporter lifts to a full-Pin transporter on the
PAC boundary.  Transitivity is deliberately supplied as an explicit orbit
hypothesis rather than asserted by the representation bridge. -/
theorem exists_fullPin_pacBoundary_smul_eq
    (X Y : ProjectiveNullBoundary projectiveNullBoundaryDatum55)
    (hXY : ∃ f : RealPin55QuadraticRepresentation.OQ55,
      f • boundaryEquiv X = boundaryEquiv Y) :
    ∃ g : RealPin55Core.FullPin55, g • X = Y := by
  rcases hXY with ⟨f, hf⟩
  rcases
      RealO55ProjectiveBoundaryAction.exists_fullPin_boundary_smul_eq
        f (boundaryEquiv X) with
    ⟨g, hg⟩
  refine ⟨g, ?_⟩
  apply boundaryEquiv.injective
  calc
    boundaryEquiv (g • X) = fullPinBoundaryAction g (boundaryEquiv X) :=
      boundaryEquiv_fullPin_smul g X
    _ = g • boundaryEquiv X := rfl
    _ = f • boundaryEquiv X := hg
    _ = boundaryEquiv Y := hf

end ProjectiveAffineConformalNativeActionWeld

end noncomputable section
