import InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
import InfoGeometry.Canonical.RealCl55NativeMatrixFaithfulBridge

/-!
# Native continuous action of the transported `Q55` Spin group

This is a finite-dimensional consumer bridge.  It converts the already
constructed matrix-valued `Q55` Spin representation into continuous linear
maps on `EuclideanSpace ℝ (Fin 32)` using the existing matrix reindexing
equivalence.  It does not identify a particular matrix basis with the
Chevalley carrier, and it makes no Kasparov, completion, or physical claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeSpinorGroupActionBridge

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SplitClifford55NeutralFormBridge
open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge

abbrev Spin55 : Type _ := Clifford55.Spin55
abbrev SpinMatrix55 : Type _ := InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5
abbrev NativeSpinorCLM : Type _ :=
  RealCl55FiniteModuleEndBridge.NativeSpinorCLM

noncomputable def spinorMatrixToMat32 : SpinMatrix55 ≃ₐ[ℝ]
    RealCl55FiniteModuleEndBridge.Mat32 :=
  (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).symm

noncomputable def nativeSpinorAction : Spin55 →* NativeSpinorCLM where
  toFun g :=
    nativeContinuous
      (spinorMatrixToMat32
        ((nativeMatrixSpinRepresentation g : SpinMatrixGL55) : SpinMatrix55))
  map_one' := by
    rw [nativeMatrixSpinRepresentation_one]
    have hmap : spinorMatrixToMat32 (1 : SpinMatrix55) =
        (1 : RealCl55FiniteModuleEndBridge.Mat32) :=
      map_one spinorMatrixToMat32
    have hunit : ((1 : SpinMatrixGL55) : SpinMatrix55) =
        (1 : SpinMatrix55) := rfl
    rw [hunit, hmap]
    exact nativeContinuous_one
  map_mul' g h := by
    change nativeContinuous
        (spinorMatrixToMat32
          (((nativeMatrixSpinRepresentation (g * h) : SpinMatrixGL55) :
            SpinMatrix55))) =
      (nativeContinuous
        (spinorMatrixToMat32
          ((nativeMatrixSpinRepresentation g : SpinMatrixGL55) : SpinMatrix55))).comp
      (nativeContinuous
        (spinorMatrixToMat32
          ((nativeMatrixSpinRepresentation h : SpinMatrixGL55) : SpinMatrix55)))
    rw [nativeMatrixSpinRepresentation_mul]
    change nativeContinuous
        (spinorMatrixToMat32
          ((((nativeMatrixSpinRepresentation g : SpinMatrixGL55) : SpinMatrix55) *
            ((nativeMatrixSpinRepresentation h : SpinMatrixGL55) : SpinMatrix55)))) = _
    rw [map_mul, nativeContinuous_mul]

@[simp] theorem nativeSpinorAction_apply (g : Spin55) :
    nativeSpinorAction g =
      nativeContinuous
        (spinorMatrixToMat32
          ((nativeMatrixSpinRepresentation g : SpinMatrixGL55) : SpinMatrix55)) := rfl

theorem nativeSpinorAction_one :
    nativeSpinorAction (1 : Spin55) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  exact map_one nativeSpinorAction

theorem nativeSpinorAction_mul (g h : Spin55) :
    nativeSpinorAction (g * h) =
      (nativeSpinorAction g).comp (nativeSpinorAction h) := by
  exact map_mul nativeSpinorAction g h

theorem nativeSpinorAction_comp_inv (g : Spin55) :
    (nativeSpinorAction g).comp (nativeSpinorAction g⁻¹) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  rw [← nativeSpinorAction_mul]
  simp
  exact nativeContinuous_one

theorem nativeSpinorAction_inv_comp (g : Spin55) :
    (nativeSpinorAction g⁻¹).comp (nativeSpinorAction g) =
      ContinuousLinearMap.id ℝ NativeSpinorCarrier := by
  rw [← nativeSpinorAction_mul]
  simp
  exact nativeContinuous_one

theorem nativeSpinorAction_bijective (g : Spin55) :
    Function.Bijective (nativeSpinorAction g) := by
  constructor
  · intro x y hxy
    have h := congrArg (fun T : NativeSpinorCLM => T y)
      (nativeSpinorAction_inv_comp g)
    have hx := congrArg (fun T : NativeSpinorCLM => T x)
      (nativeSpinorAction_inv_comp g)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h hx
    rw [hxy] at hx
    exact hx.symm.trans h
  · intro y
    refine ⟨nativeSpinorAction g⁻¹ y, ?_⟩
    have h := congrArg (fun T : NativeSpinorCLM => T y)
      (nativeSpinorAction_comp_inv g)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

noncomputable def nativeSpinorContinuousLinearEquiv (g : Spin55) :
    NativeSpinorCarrier ≃L[ℝ] NativeSpinorCarrier where
  toFun := nativeSpinorAction g
  invFun := nativeSpinorAction g⁻¹
  map_add' := (nativeSpinorAction g).map_add
  map_smul' := (nativeSpinorAction g).map_smul
  left_inv := by
    intro x
    have h := congrArg (fun T : NativeSpinorCLM => T x)
      (nativeSpinorAction_inv_comp g)
    simpa [ContinuousLinearMap.comp_apply] using h
  right_inv := by
    intro x
    have h := congrArg (fun T : NativeSpinorCLM => T x)
      (nativeSpinorAction_comp_inv g)
    simpa [ContinuousLinearMap.comp_apply] using h
  continuous_toFun := (nativeSpinorAction g).cont
  continuous_invFun := (nativeSpinorAction g⁻¹).cont

@[simp] theorem nativeSpinorContinuousLinearEquiv_apply
    (g : Spin55) (x : NativeSpinorCarrier) :
    nativeSpinorContinuousLinearEquiv g x = nativeSpinorAction g x := rfl

noncomputable def nativeSpinorContinuousLinearRepresentation :
    Spin55 →* (NativeSpinorCarrier ≃L[ℝ] NativeSpinorCarrier) where
  toFun := nativeSpinorContinuousLinearEquiv
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext x
    change nativeSpinorAction (1 : Spin55) x = x
    rw [nativeSpinorAction_one]
    rfl
  map_mul' g h := by
    apply ContinuousLinearEquiv.ext
    funext x
    change nativeSpinorAction (g * h) x =
      nativeSpinorAction g (nativeSpinorAction h x)
    rw [nativeSpinorAction_mul]
    rfl

@[simp] theorem nativeSpinorContinuousLinearRepresentation_apply
    (g : Spin55) :
    nativeSpinorContinuousLinearRepresentation g =
      nativeSpinorContinuousLinearEquiv g := rfl

noncomputable def nativeSpinorLinearEquiv (g : Spin55) :
    NativeSpinorCarrier ≃ₗ[ℝ] NativeSpinorCarrier :=
  { toFun := nativeSpinorAction g
    invFun := nativeSpinorAction g⁻¹
    left_inv := by
      intro x
      have h := congrArg (fun T : NativeSpinorCLM => T x)
        (nativeSpinorAction_inv_comp g)
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    right_inv := by
      intro x
      have h := congrArg (fun T : NativeSpinorCLM => T x)
        (nativeSpinorAction_comp_inv g)
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    map_add' := by
      intro x y
      exact (nativeSpinorAction g).map_add x y
    map_smul' := by
      intro c x
      exact (nativeSpinorAction g).map_smul c x }

@[simp] theorem nativeSpinorLinearEquiv_apply (g : Spin55)
    (x : NativeSpinorCarrier) :
    nativeSpinorLinearEquiv g x = nativeSpinorAction g x := rfl

noncomputable def nativeSpinorGeneralLinearRepresentation :
    Spin55 →* LinearMap.GeneralLinearGroup ℝ NativeSpinorCarrier where
  toFun g := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (nativeSpinorLinearEquiv g)
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    change nativeSpinorAction (1 : Spin55) x = x
    rw [nativeSpinorAction_one]
    rfl
  map_mul' g h := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    change nativeSpinorAction (g * h) x =
      nativeSpinorAction g (nativeSpinorAction h x)
    rw [nativeSpinorAction_mul]
    rfl

@[simp] theorem nativeSpinorGeneralLinearRepresentation_toLinearMap
    (g : Spin55) :
    ((nativeSpinorGeneralLinearRepresentation g :
      LinearMap.GeneralLinearGroup ℝ NativeSpinorCarrier) :
        NativeSpinorCarrier →ₗ[ℝ] NativeSpinorCarrier) =
      (nativeSpinorAction g).toLinearMap := rfl

theorem nativeSpinorAction_injective :
    Function.Injective nativeSpinorAction := by
  intro g h gh
  have hcont :
      nativeContinuous
          (spinorMatrixToMat32
            ((nativeMatrixSpinRepresentation g : SpinMatrixGL55) : SpinMatrix55)) =
        nativeContinuous
          (spinorMatrixToMat32
            ((nativeMatrixSpinRepresentation h : SpinMatrixGL55) : SpinMatrix55)) := by
    exact gh
  have hmat32 :
      spinorMatrixToMat32
          ((nativeMatrixSpinRepresentation g : SpinMatrixGL55) : SpinMatrix55) =
        spinorMatrixToMat32
          ((nativeMatrixSpinRepresentation h : SpinMatrixGL55) : SpinMatrix55) :=
    RealCl55NativeMatrixFaithfulBridge.nativeContinuous_injective hcont
  have hspinmat :
      ((nativeMatrixSpinRepresentation g : SpinMatrixGL55) : SpinMatrix55) =
        ((nativeMatrixSpinRepresentation h : SpinMatrixGL55) : SpinMatrix55) :=
    spinorMatrixToMat32.injective hmat32
  have hgroupmat : nativeMatrixSpinRepresentation g =
      nativeMatrixSpinRepresentation h := by
    apply Units.ext
    exact hspinmat
  exact nativeMatrixSpinRepresentation_injective hgroupmat

theorem nativeSpinorContinuousLinearRepresentation_injective :
    Function.Injective nativeSpinorContinuousLinearRepresentation := by
  intro g h hgh
  apply nativeSpinorAction_injective
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun T => T x) hgh
  exact hx

end InfoGeometry.Canonical.RealCl55NativeSpinorGroupActionBridge
