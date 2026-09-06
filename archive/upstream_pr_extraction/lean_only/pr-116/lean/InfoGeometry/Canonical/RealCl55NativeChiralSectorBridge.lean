import Mathlib
import InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
import InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge

/-!
# Native chiral sector submodules

The two chiral sectors are packaged as native Mathlib submodules using the
projector fixed-point conditions.  The supplied group action preserves these
submodules.  No dimension or irreducibility claim is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeChiralSectorBridge

open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge
open InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge

variable {G : Type*} [Group G]

def nativePlusSector : Submodule ℝ NativeSpinorCarrier where
  carrier := {x | nativeChiralProjectorPlus x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change nativeChiralProjectorPlus (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro c x hx
    change nativeChiralProjectorPlus (c • x) = c • x
    rw [map_smul, hx]

def nativeMinusSector : Submodule ℝ NativeSpinorCarrier where
  carrier := {x | nativeChiralProjectorMinus x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change nativeChiralProjectorMinus (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' := by
    intro c x hx
    change nativeChiralProjectorMinus (c • x) = c • x
    rw [map_smul, hx]

@[simp] theorem mem_nativePlusSector (x : NativeSpinorCarrier) :
    x ∈ nativePlusSector ↔ nativeChiralProjectorPlus x = x := Iff.rfl

@[simp] theorem mem_nativeMinusSector (x : NativeSpinorCarrier) :
    x ∈ nativeMinusSector ↔ nativeChiralProjectorMinus x = x := Iff.rfl

theorem nativeIntegratedAction_maps_plusSector
    (act : G2IntegratedAction G) (g : G) :
    nativePlusSector.map (nativeIntegratedAction act g).toLinearMap ≤
      nativePlusSector := by
  rintro _ ⟨x, hx, rfl⟩
  change nativeChiralProjectorPlus (nativeIntegratedAction act g x) =
    nativeIntegratedAction act g x
  exact nativeIntegratedAction_preserves_plus_sector act g x hx

theorem nativeIntegratedAction_maps_minusSector
    (act : G2IntegratedAction G) (g : G) :
    nativeMinusSector.map (nativeIntegratedAction act g).toLinearMap ≤
      nativeMinusSector := by
  rintro _ ⟨x, hx, rfl⟩
  change nativeChiralProjectorMinus (nativeIntegratedAction act g x) =
    nativeIntegratedAction act g x
  exact nativeIntegratedAction_preserves_minus_sector act g x hx

theorem nativePlusSector_inf_nativeMinusSector :
    nativePlusSector ⊓ nativeMinusSector = ⊥ := by
  apply le_antisymm
  · intro x hx
    have horth := congrArg
      (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x)
      nativeChiralProjectors_orthogonal.1
    have hzero : x = 0 := by
      change nativeChiralProjectorPlus (nativeChiralProjectorMinus x) = 0 at horth
      rw [hx.2, hx.1] at horth
      exact horth
    rw [hzero]
    exact Submodule.zero_mem _
  · exact bot_le

theorem nativePlusSector_sup_nativeMinusSector :
    nativePlusSector ⊔ nativeMinusSector = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro x hx
    have hplus : nativeChiralProjectorPlus (nativeChiralProjectorPlus x) =
        nativeChiralProjectorPlus x := by
      have h := congrArg
        (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x)
        nativeChiralProjectorPlus_sq
      simpa [ContinuousLinearMap.comp_apply] using h
    have hminus : nativeChiralProjectorMinus (nativeChiralProjectorMinus x) =
        nativeChiralProjectorMinus x := by
      have h := congrArg
        (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x)
        nativeChiralProjectorMinus_sq
      simpa [ContinuousLinearMap.comp_apply] using h
    have hsum := congrArg
      (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x)
      nativeChiralProjectors_sum
    apply Submodule.mem_sup.mpr
    refine ⟨nativeChiralProjectorPlus x, hplus,
      nativeChiralProjectorMinus x, hminus, ?_⟩
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] using hsum

noncomputable def nativeChiralDecomposition :
    NativeSpinorCarrier ≃ₗ[ℝ] nativePlusSector × nativeMinusSector where
  toFun x :=
    (⟨nativeChiralProjectorPlus x, by
        have h := congrArg
          (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x)
          nativeChiralProjectorPlus_sq
        simpa [ContinuousLinearMap.comp_apply] using h⟩,
      ⟨nativeChiralProjectorMinus x, by
        have h := congrArg
          (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x)
          nativeChiralProjectorMinus_sq
        simpa [ContinuousLinearMap.comp_apply] using h⟩)
  invFun p := p.1.1 + p.2.1
  left_inv x := by
    change nativeChiralProjectorPlus x + nativeChiralProjectorMinus x = x
    have hsum := congrArg
      (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x)
      nativeChiralProjectors_sum
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] using hsum
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change nativeChiralProjectorPlus (p.1.1 + p.2.1) = p.1.1
      have hzero := congrArg
        (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T p.2.1)
        nativeChiralProjectors_orthogonal.1
      change nativeChiralProjectorPlus (nativeChiralProjectorMinus p.2.1) = 0 at hzero
      rw [p.2.2] at hzero
      rw [map_add, p.1.2, hzero, add_zero]
    · apply Subtype.ext
      change nativeChiralProjectorMinus (p.1.1 + p.2.1) = p.2.1
      have hzero := congrArg
        (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T p.1.1)
        nativeChiralProjectors_orthogonal.2
      change nativeChiralProjectorMinus (nativeChiralProjectorPlus p.1.1) = 0 at hzero
      rw [p.1.2] at hzero
      rw [map_add, hzero, p.2.2, zero_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [map_add]
  map_smul' c x := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [map_smul]

def nativePlusSectorAction
    (act : G2IntegratedAction G) (g : G) :
    nativePlusSector →ₗ[ℝ] nativePlusSector where
  toFun x :=
    ⟨nativeIntegratedAction act g x.1,
      nativeIntegratedAction_preserves_plus_sector act g x.1 x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul]

def nativeMinusSectorAction
    (act : G2IntegratedAction G) (g : G) :
    nativeMinusSector →ₗ[ℝ] nativeMinusSector where
  toFun x :=
    ⟨nativeIntegratedAction act g x.1,
      nativeIntegratedAction_preserves_minus_sector act g x.1 x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul]

@[simp] theorem nativePlusSectorAction_apply
    (act : G2IntegratedAction G) (g : G) (x : nativePlusSector) :
    nativePlusSectorAction act g x =
      ⟨nativeIntegratedAction act g x.1,
        nativeIntegratedAction_preserves_plus_sector act g x.1 x.2⟩ := rfl

@[simp] theorem nativeMinusSectorAction_apply
    (act : G2IntegratedAction G) (g : G) (x : nativeMinusSector) :
    nativeMinusSectorAction act g x =
      ⟨nativeIntegratedAction act g x.1,
        nativeIntegratedAction_preserves_minus_sector act g x.1 x.2⟩ := rfl

theorem nativePlusSectorAction_bijective
    (act : G2IntegratedAction G) (g : G) :
    Function.Bijective (nativePlusSectorAction act g) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (nativeIntegratedAction_bijective act g).1
    exact congrArg Subtype.val hxy
  · intro y
    refine ⟨⟨nativeIntegratedAction act g⁻¹ y.1,
      nativeIntegratedAction_preserves_plus_sector act g⁻¹ y.1 y.2⟩, ?_⟩
    apply Subtype.ext
    have h := congrArg (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T y.1)
      (nativeIntegratedAction_comp_inverse act g)
    simpa [ContinuousLinearMap.comp_apply] using h

theorem nativeMinusSectorAction_bijective
    (act : G2IntegratedAction G) (g : G) :
    Function.Bijective (nativeMinusSectorAction act g) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (nativeIntegratedAction_bijective act g).1
    exact congrArg Subtype.val hxy
  · intro y
    refine ⟨⟨nativeIntegratedAction act g⁻¹ y.1,
      nativeIntegratedAction_preserves_minus_sector act g⁻¹ y.1 y.2⟩, ?_⟩
    apply Subtype.ext
    have h := congrArg (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T y.1)
      (nativeIntegratedAction_comp_inverse act g)
    simpa [ContinuousLinearMap.comp_apply] using h

/-! The restricted actions are genuine automorphisms of their sectors.  The
`MonoidHom` APIs below remain available for consumers that only need the
linear action; these equivalences expose the invertibility at the native
`LinearEquiv` level. -/

noncomputable def nativePlusSectorActionEquiv
    (act : G2IntegratedAction G) (g : G) :
    nativePlusSector ≃ₗ[ℝ] nativePlusSector :=
  LinearEquiv.ofBijective (nativePlusSectorAction act g)
    (nativePlusSectorAction_bijective act g)

noncomputable def nativeMinusSectorActionEquiv
    (act : G2IntegratedAction G) (g : G) :
    nativeMinusSector ≃ₗ[ℝ] nativeMinusSector :=
  LinearEquiv.ofBijective (nativeMinusSectorAction act g)
    (nativeMinusSectorAction_bijective act g)

@[simp] theorem nativePlusSectorActionEquiv_apply
    (act : G2IntegratedAction G) (g : G) (x : nativePlusSector) :
    nativePlusSectorActionEquiv act g x = nativePlusSectorAction act g x := rfl

@[simp] theorem nativeMinusSectorActionEquiv_apply
    (act : G2IntegratedAction G) (g : G) (x : nativeMinusSector) :
    nativeMinusSectorActionEquiv act g x = nativeMinusSectorAction act g x := rfl

/-- The restricted plus-sector maps form the induced group action. -/
noncomputable def nativePlusSectorActionHom
    (act : G2IntegratedAction G) :
    G →* (nativePlusSector →ₗ[ℝ] nativePlusSector) where
  toFun := nativePlusSectorAction act
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change nativeIntegratedAction act 1 x.1 = x.1
    have h := congrArg
      (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
      (nativeIntegratedAction act).map_one
    simpa [nativeIntegratedAction_apply, ContinuousLinearMap.id_apply] using h
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change nativeIntegratedAction act (g * h) x.1 =
      nativeIntegratedAction act g (nativeIntegratedAction act h x.1)
    have hs := congrArg
      (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
      ((nativeIntegratedAction act).map_mul g h)
    simpa [ContinuousLinearMap.comp_apply] using hs

/-- The restricted minus-sector maps form the induced group action. -/
noncomputable def nativeMinusSectorActionHom
    (act : G2IntegratedAction G) :
    G →* (nativeMinusSector →ₗ[ℝ] nativeMinusSector) where
  toFun := nativeMinusSectorAction act
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change nativeIntegratedAction act 1 x.1 = x.1
    have h := congrArg
      (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
      (nativeIntegratedAction act).map_one
    simpa [nativeIntegratedAction_apply, ContinuousLinearMap.id_apply] using h
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change nativeIntegratedAction act (g * h) x.1 =
      nativeIntegratedAction act g (nativeIntegratedAction act h x.1)
    have hs := congrArg
      (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
      ((nativeIntegratedAction act).map_mul g h)
    simpa [ContinuousLinearMap.comp_apply] using hs

@[simp] theorem nativePlusSectorActionHom_apply
    (act : G2IntegratedAction G) (g : G) :
    nativePlusSectorActionHom act g = nativePlusSectorAction act g := rfl

@[simp] theorem nativeMinusSectorActionHom_apply
    (act : G2IntegratedAction G) (g : G) :
    nativeMinusSectorActionHom act g = nativeMinusSectorAction act g := rfl

theorem nativeChiralProjectorMinus_comp_chiralDiracPlus :
    nativeChiralProjectorMinus.comp nativeChiralDiracPlus =
      nativeChiralDiracPlus := by
  unfold nativeChiralProjectorMinus nativeChiralDiracPlus
  rw [← nativeContinuous_mul]
  rw [masterChiralDiracPlus_eq_projectorMinus_mul_hodge]
  rw [← Matrix.mul_assoc, masterChiralProjectorMinus_sq]

theorem nativeChiralProjectorPlus_comp_chiralDiracMinus :
    nativeChiralProjectorPlus.comp nativeChiralDiracMinus =
      nativeChiralDiracMinus := by
  unfold nativeChiralProjectorPlus nativeChiralDiracMinus
  rw [← nativeContinuous_mul]
  rw [masterChiralDiracMinus_eq_projectorPlus_mul_hodge]
  rw [← Matrix.mul_assoc, masterChiralProjectorPlus_sq]

noncomputable def nativeChiralDiracPlusArrow :
    nativePlusSector →ₗ[ℝ] nativeMinusSector where
  toFun x :=
    ⟨nativeChiralDiracPlus x.1, by
      have h := congrArg
        (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
        nativeChiralProjectorMinus_comp_chiralDiracPlus
      simpa [ContinuousLinearMap.comp_apply] using h⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul]

noncomputable def nativeChiralDiracMinusArrow :
    nativeMinusSector →ₗ[ℝ] nativePlusSector where
  toFun x :=
    ⟨nativeChiralDiracMinus x.1, by
      have h := congrArg
        (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
        nativeChiralProjectorPlus_comp_chiralDiracMinus
      simpa [ContinuousLinearMap.comp_apply] using h⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul]

@[simp] theorem nativeChiralDiracPlusArrow_apply
    (x : nativePlusSector) :
    nativeChiralDiracPlusArrow x =
      ⟨nativeChiralDiracPlus x.1, by
        have h := congrArg
          (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
          nativeChiralProjectorMinus_comp_chiralDiracPlus
        simpa [ContinuousLinearMap.comp_apply] using h⟩ := rfl

@[simp] theorem nativeChiralDiracMinusArrow_apply
    (x : nativeMinusSector) :
    nativeChiralDiracMinusArrow x =
      ⟨nativeChiralDiracMinus x.1, by
        have h := congrArg
          (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
          nativeChiralProjectorPlus_comp_chiralDiracMinus
        simpa [ContinuousLinearMap.comp_apply] using h⟩ := rfl

theorem nativePlusSectorAction_intertwines_chiralDiracPlus
    (act : G2IntegratedAction G) (g : G) :
    (nativeMinusSectorAction act g).comp nativeChiralDiracPlusArrow =
      nativeChiralDiracPlusArrow.comp (nativePlusSectorAction act g) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := congrArg
    (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
    (nativeIntegratedAction_commutes_chiralDiracPlus act g)
  simpa [ContinuousLinearMap.comp_apply] using h

theorem nativeMinusSectorAction_intertwines_chiralDiracMinus
    (act : G2IntegratedAction G) (g : G) :
    (nativePlusSectorAction act g).comp nativeChiralDiracMinusArrow =
      nativeChiralDiracMinusArrow.comp (nativeMinusSectorAction act g) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := congrArg
    (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
    (nativeIntegratedAction_commutes_chiralDiracMinus act g)
  simpa [ContinuousLinearMap.comp_apply] using h

end InfoGeometry.Canonical.RealCl55NativeChiralSectorBridge
