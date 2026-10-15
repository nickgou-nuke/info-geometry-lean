import InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Stabilization of logarithmic tensor-power braid actions

The finite braid-group tower stabilizes by adding a strand on the right.  On the
standard Jordan tensor powers we use the primary vector `e₀` as the spectator.
Since `N e₀ = 0`, right append by `e₀` is a logarithmic intertwiner.

The main results prove generator-level and then full group-level equivariance
with the existing `B_n → B_{n+1}` stabilization.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanTensorPowerStabilization

open CategoryTheory
open scoped TensorProduct
open Braid

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
open InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner

/-- The primary vector expressed in the carrier instance owned by the
standard logarithmic Jordan object. -/
def primaryVector : standardJordanObject.toLogEndModule.V := by
  change InfoGeometry.Canonical.LogJordanTensorFusion.JordanCarrier ℂ
  exact e0

/-- The Jordan endomorphism kills the primary vector in the owned carrier. -/
@[simp]
theorem standardJordanObject_N_primaryVector :
    standardJordanObject.toLogEndModule.N primaryVector = 0 := by
  change standardJordanObject.N
    (e0 : InfoGeometry.Canonical.LogJordanTensorFusion.JordanCarrier ℂ) = 0
  exact standardJordanObject_N_e0

/-- Append one primary spectator to a single standard Jordan factor. -/
def appendPrimaryBase :
    standardJordanObject ⟶ tensorPowerObj standardJordanObject 2 where
  hom :=
    { toFun := fun x => x ⊗ₜ[ℂ] primaryVector
      map_add' := by
        intro x y
        exact TensorProduct.add_tmul x y primaryVector
      map_smul' := by
        intro c x
        exact TensorProduct.smul_tmul' c x primaryVector }
  comm := by
    ext x
    apply (LogNilpotentModule.tensorObj_carrierEquiv
      standardJordanObject standardJordanObject).injective
    change standardJordanObject.toLogEndModule.N x ⊗ₜ[ℂ]
        primaryVector =
      (LogEndModule.tensorObj standardJordanObject.toLogEndModule
        standardJordanObject.toLogEndModule).N
        (x ⊗ₜ[ℂ] primaryVector)
    rw [LogEndModule.tensorObj_N_tmul,
      standardJordanObject_N_primaryVector, TensorProduct.tmul_zero, add_zero]

@[simp]
theorem appendPrimaryBase_apply (x : standardJordanObject) :
    appendPrimaryBase.hom x = x ⊗ₜ[ℂ] primaryVector := rfl

/-- Right-spectator bonding map
`J^{⊗(n+1)} → J^{⊗(n+2)}`.  The recursion follows the right-associated tensor
power and therefore appends `e₀` at the far right. -/
def appendPrimaryBonding :
    (n : ℕ) →
      tensorPowerObj standardJordanObject (n + 1) ⟶
        tensorPowerObj standardJordanObject (n + 2)
  | 0 => appendPrimaryBase
  | n + 1 =>
      LogNilpotentModule.tensorHom (𝟙 standardJordanObject)
        (appendPrimaryBonding n)

@[simp]
theorem appendPrimaryBonding_zero_apply (x : standardJordanObject) :
    (appendPrimaryBonding 0).hom x =
      x ⊗ₜ[ℂ] (e0 : standardJordanObject) := rfl

@[simp]
theorem appendPrimaryBonding_zero_leftTmul (x : standardJordanObject) :
    (appendPrimaryBonding 0).hom x =
      tensorPowerObj_succ_succ_leftTmul standardJordanObject 0 x
        (e0 : tensorPowerObj standardJordanObject 1) := rfl

/-- Recursive pure-tensor action of the spectator bonding map. -/
@[simp]
theorem appendPrimaryBonding_succ_tmul
    (n : ℕ) (x : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 1)) :
    (appendPrimaryBonding (n + 1)).hom (x ⊗ₜ[ℂ] t) =
      x ⊗ₜ[ℂ] (appendPrimaryBonding n).hom t := by
  exact LogNilpotentModule.tensorHom_tmul (𝟙 standardJordanObject)
    (appendPrimaryBonding n) x t

/-- The recursive bonding map respects the categorical carrier insertion.
This form keeps every intermediate vector on the bundled tensor-power object. -/
@[simp]
theorem appendPrimaryBonding_succ_leftTmul
    (n : ℕ) (x : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 1)) :
    (appendPrimaryBonding (n + 1)).hom
        (tensorPowerObj_succ_succ_leftTmul standardJordanObject n x t) =
      tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x
        ((appendPrimaryBonding n).hom t) := by
  rw [tensorPowerObj_succ_succ_leftTmul_tmul,
    tensorPowerObj_succ_succ_leftTmul_tmul]
  exact LogNilpotentModule.tensorHom_tmul (𝟙 standardJordanObject)
    (appendPrimaryBonding n) x t

/-- A successor slice acts on the categorical tensor insertion by its action
on the bundled tail. -/
theorem standardTensorPowerGenerator_succ_leftTmul
    (n : ℕ) (i : Fin (n + 1)) (x : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 2)) :
    standardTensorPowerGenerator (n + 1) i.succ
        (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x t) =
      tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x
        (standardTensorPowerGenerator n i t) := by
  rw [tensorPowerObj_succ_succ_leftTmul_tmul,
    tensorPowerObj_succ_succ_leftTmul_tmul]
  exact standardTensorPowerGenerator_succ_tmul n i x t

/-- Every bonding map is, by construction, an exact logarithmic intertwiner. -/
theorem appendPrimaryBonding_intertwines (n : ℕ) :
    (appendPrimaryBonding n).hom.comp
        (tensorPowerObj standardJordanObject (n + 1)).N =
      (tensorPowerObj standardJordanObject (n + 2)).N.comp
        (appendPrimaryBonding n).hom :=
  (appendPrimaryBonding n).comm

/-- Generator-level stabilization compatibility.

Appending the primary spectator after applying the old checked-R slice equals
first appending the spectator and then applying the identically indexed slice at
the next tensor-power stage. -/
theorem appendPrimaryBonding_generator_compat
    (n : ℕ) (i : Fin (n + 1)) :
    (appendPrimaryBonding (n + 1)).hom.comp
        (standardTensorPowerGenerator n i).toLinearMap =
      (standardTensorPowerGenerator (n + 1) i.castSucc).toLinearMap.comp
        (appendPrimaryBonding (n + 1)).hom := by
  induction n with
  | zero =>
      fin_cases i
      apply LinearMap.ext
      intro t
      refine tensorPowerObj_succ_succ_induction standardJordanObject 0
        (P := fun z =>
          (appendPrimaryBonding 1).hom
              (standardTensorPowerGenerator 0 (0 : Fin 1) z) =
            standardTensorPowerGenerator 1 (Fin.castSucc (0 : Fin 1))
              ((appendPrimaryBonding 1).hom z)) ?_ ?_ t
      · intro x y
        calc
          (appendPrimaryBonding 1).hom
              (standardTensorPowerGenerator 0 (0 : Fin 1)
                (tensorPowerObj_succ_succ_leftTmul standardJordanObject 0 x y)) =
            (appendPrimaryBonding 1).hom
              (tensorPowerObj_succ_succ_leftTmul standardJordanObject 0 y x) := by
                apply congrArg (appendPrimaryBonding 1).hom
                rw [tensorPowerObj_succ_succ_leftTmul_tmul,
                  tensorPowerObj_succ_succ_leftTmul_tmul]
                exact standardTensorPowerGenerator_base_tmul x y
          _ = tensorPowerObj_succ_succ_leftTmul standardJordanObject 1 y
                ((appendPrimaryBonding 0).hom x) :=
              appendPrimaryBonding_succ_leftTmul 0 y x
          _ = standardTensorPowerGenerator 1 (Fin.castSucc (0 : Fin 1))
                (tensorPowerObj_succ_succ_leftTmul standardJordanObject 1 x
                  ((appendPrimaryBonding 0).hom y)) := by
              rw [tensorPowerObj_succ_succ_leftTmul_tmul,
                tensorPowerObj_succ_succ_leftTmul_tmul,
                appendPrimaryBonding_zero_apply,
                appendPrimaryBonding_zero_apply]
              exact (standardTensorPowerGenerator_zero_tmul 0 x y
                (e0 : tensorPowerObj standardJordanObject 1)).symm
          _ = standardTensorPowerGenerator 1 (Fin.castSucc (0 : Fin 1))
                ((appendPrimaryBonding 1).hom
                  (tensorPowerObj_succ_succ_leftTmul standardJordanObject 0 x y)) := by
              exact congrArg (standardTensorPowerGenerator 1
                (Fin.castSucc (0 : Fin 1)))
                (appendPrimaryBonding_succ_leftTmul 0 x y).symm
      · intro a b ha hb
        calc
          (appendPrimaryBonding 1).hom
              (standardTensorPowerGenerator 0 (0 : Fin 1) (a + b)) =
            (appendPrimaryBonding 1).hom
                (standardTensorPowerGenerator 0 (0 : Fin 1) a) +
              (appendPrimaryBonding 1).hom
                (standardTensorPowerGenerator 0 (0 : Fin 1) b) := by
              exact map_add
                ((appendPrimaryBonding 1).hom.comp
                  (standardTensorPowerGenerator 0 (0 : Fin 1)).toLinearMap) a b
          _ = _ := congrArg₂ (· + ·) ha hb
          _ = _ := (map_add
            ((standardTensorPowerGenerator 1 (Fin.castSucc (0 : Fin 1))).toLinearMap.comp
              (appendPrimaryBonding 1).hom) a b).symm
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · apply LinearMap.ext
        intro t
        refine tensorPowerObj_succ_succ_induction standardJordanObject (n + 1)
          (P := fun z =>
            (appendPrimaryBonding (n + 2)).hom
                (standardTensorPowerGenerator (n + 1) (0 : Fin (n + 2)) z) =
              standardTensorPowerGenerator (n + 2)
                  (Fin.castSucc (0 : Fin (n + 2)))
                ((appendPrimaryBonding (n + 2)).hom z)) ?_ ?_ t
        · intro x tail
          refine tensorPowerObj_succ_succ_induction standardJordanObject n
            (P := fun rest =>
              (appendPrimaryBonding (n + 2)).hom
                  (standardTensorPowerGenerator (n + 1) (0 : Fin (n + 2))
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x rest)) =
                standardTensorPowerGenerator (n + 2)
                    (Fin.castSucc (0 : Fin (n + 2)))
                  ((appendPrimaryBonding (n + 2)).hom
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x rest))) ?_ ?_ tail
          · intro y rest
            calc
              (appendPrimaryBonding (n + 2)).hom
                  (standardTensorPowerGenerator (n + 1) (0 : Fin (n + 2))
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x
                      (tensorPowerObj_succ_succ_leftTmul standardJordanObject n y rest))) =
                (appendPrimaryBonding (n + 2)).hom
                  (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject n x rest)) := by
                  exact congrArg (appendPrimaryBonding (n + 2)).hom
                    (standardTensorPowerGenerator_zero_leftTmul n x y rest)
              _ = tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) y
                    ((appendPrimaryBonding (n + 1)).hom
                      (tensorPowerObj_succ_succ_leftTmul standardJordanObject n x rest)) :=
                  appendPrimaryBonding_succ_leftTmul (n + 1) y
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject n x rest)
              _ = tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) y
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x
                      ((appendPrimaryBonding n).hom rest)) := by
                  rw [appendPrimaryBonding_succ_leftTmul]
              _ = standardTensorPowerGenerator (n + 2)
                    (Fin.castSucc (0 : Fin (n + 2)))
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
                      (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) y
                        ((appendPrimaryBonding n).hom rest))) := by
                  exact (standardTensorPowerGenerator_zero_leftTmul (n + 1) x y
                    ((appendPrimaryBonding n).hom rest)).symm
              _ = standardTensorPowerGenerator (n + 2)
                    (Fin.castSucc (0 : Fin (n + 2)))
                    ((appendPrimaryBonding (n + 2)).hom
                      (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x
                        (tensorPowerObj_succ_succ_leftTmul standardJordanObject n y rest))) := by
                  rfl
          · intro a b ha hb
            calc
              (appendPrimaryBonding (n + 2)).hom
                  (standardTensorPowerGenerator (n + 1) 0
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x (a + b))) =
                (appendPrimaryBonding (n + 2)).hom
                    (standardTensorPowerGenerator (n + 1) 0
                      (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x a)) +
                  (appendPrimaryBonding (n + 2)).hom
                    (standardTensorPowerGenerator (n + 1) 0
                      (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x b)) := by
                exact map_add (((appendPrimaryBonding (n + 2)).hom.comp
                  (standardTensorPowerGenerator (n + 1) 0).toLinearMap).comp
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x)) a b
              _ = _ := congrArg₂ (· + ·) ha hb
              _ = _ := (map_add (((standardTensorPowerGenerator (n + 2)
                (Fin.castSucc (0 : Fin (n + 2)))).toLinearMap.comp
                  (appendPrimaryBonding (n + 2)).hom).comp
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x)) a b).symm
        · intro a b ha hb
          calc
            (appendPrimaryBonding (n + 2)).hom
                (standardTensorPowerGenerator (n + 1) 0 (a + b)) =
              (appendPrimaryBonding (n + 2)).hom
                (standardTensorPowerGenerator (n + 1) 0 a) +
                (appendPrimaryBonding (n + 2)).hom
                  (standardTensorPowerGenerator (n + 1) 0 b) := by
                exact map_add
                  ((appendPrimaryBonding (n + 2)).hom.comp
                    (standardTensorPowerGenerator (n + 1) 0).toLinearMap) a b
            _ = _ := congrArg₂ (· + ·) ha hb
            _ = _ := (map_add
              ((standardTensorPowerGenerator (n + 2)
                (Fin.castSucc (0 : Fin (n + 2)))).toLinearMap.comp
                (appendPrimaryBonding (n + 2)).hom) a b).symm
      · apply LinearMap.ext
        intro t
        refine tensorPowerObj_succ_succ_induction standardJordanObject (n + 1)
          (P := fun z =>
            (appendPrimaryBonding (n + 2)).hom
                (standardTensorPowerGenerator (n + 1) j.succ z) =
              standardTensorPowerGenerator (n + 2) j.succ.castSucc
                ((appendPrimaryBonding (n + 2)).hom z)) ?_ ?_ t
        · intro x tail
          have htail := LinearMap.congr_fun (ih j) tail
          have hindex : j.succ.castSucc = j.castSucc.succ := by
            apply Fin.ext
            rfl
          calc
            (appendPrimaryBonding (n + 2)).hom
                (standardTensorPowerGenerator (n + 1) j.succ
                  (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x tail)) =
              (appendPrimaryBonding (n + 2)).hom
                (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x
                  (standardTensorPowerGenerator n j tail)) := by
                exact congrArg (appendPrimaryBonding (n + 2)).hom
                  (standardTensorPowerGenerator_succ_leftTmul n j x tail)
            _ = tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
                  ((appendPrimaryBonding (n + 1)).hom
                    (standardTensorPowerGenerator n j tail)) :=
                appendPrimaryBonding_succ_leftTmul (n + 1) x
                  (standardTensorPowerGenerator n j tail)
            _ = tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x
                  (standardTensorPowerGenerator (n + 1) j.castSucc
                    ((appendPrimaryBonding (n + 1)).hom tail)) := by
                exact congrArg
                  (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 2) x)
                  htail
            _ = standardTensorPowerGenerator (n + 2) j.succ.castSucc
                  ((appendPrimaryBonding (n + 2)).hom
                    (tensorPowerObj_succ_succ_leftTmul standardJordanObject (n + 1) x tail)) := by
                rw [hindex, appendPrimaryBonding_succ_leftTmul (n + 1) x tail]
                exact (standardTensorPowerGenerator_succ_leftTmul
                  (n + 1) j.castSucc x
                  ((appendPrimaryBonding (n + 1)).hom tail)).symm
        · intro a b ha hb
          calc
            (appendPrimaryBonding (n + 2)).hom
                (standardTensorPowerGenerator (n + 1) j.succ (a + b)) =
              (appendPrimaryBonding (n + 2)).hom
                (standardTensorPowerGenerator (n + 1) j.succ a) +
              (appendPrimaryBonding (n + 2)).hom
                (standardTensorPowerGenerator (n + 1) j.succ b) := by
                exact map_add
                  ((appendPrimaryBonding (n + 2)).hom.comp
                    (standardTensorPowerGenerator (n + 1) j.succ).toLinearMap) a b
            _ = _ := congrArg₂ (· + ·) ha hb
            _ = _ := (map_add
              ((standardTensorPowerGenerator (n + 2) j.succ.castSucc).toLinearMap.comp
                (appendPrimaryBonding (n + 2)).hom) a b).symm

/-- Subgroup of stage-`n+2` braids whose representation intertwines the primary
spectator bonding map with the stabilized stage representation. -/
def stabilizationSubgroup (n : ℕ) : Subgroup (braid_group (n + 2)) where
  carrier := {g |
    (appendPrimaryBonding (n + 1)).hom.comp
        (standardHadjiivanovBraidProjectHom n g).toLinearMap =
      (standardHadjiivanovBraidProjectHom (n + 1)
          (finiteSuccGroupHom (n + 1) g)).toLinearMap.comp
        (appendPrimaryBonding (n + 1)).hom}
  one_mem' := by
    apply LinearMap.ext
    intro x
    simp
  mul_mem' := by
    intro g h hg hh
    apply LinearMap.ext
    intro x
    have hgx := LinearMap.congr_fun hg
      (standardHadjiivanovBraidProjectHom n h x)
    have hhx := LinearMap.congr_fun hh x
    calc
      (appendPrimaryBonding (n + 1)).hom
          (standardHadjiivanovBraidProjectHom n (g * h) x) =
        (appendPrimaryBonding (n + 1)).hom
          (standardHadjiivanovBraidProjectHom n g
            (standardHadjiivanovBraidProjectHom n h x)) := by
              simp [map_mul, LinearEquiv.mul_apply]
      _ = standardHadjiivanovBraidProjectHom (n + 1)
            (finiteSuccGroupHom (n + 1) g)
            ((appendPrimaryBonding (n + 1)).hom
              (standardHadjiivanovBraidProjectHom n h x)) := by
              simpa [LinearMap.comp_apply] using hgx
      _ = standardHadjiivanovBraidProjectHom (n + 1)
            (finiteSuccGroupHom (n + 1) g)
            (standardHadjiivanovBraidProjectHom (n + 1)
              (finiteSuccGroupHom (n + 1) h)
              ((appendPrimaryBonding (n + 1)).hom x)) := by
              exact congrArg
                (standardHadjiivanovBraidProjectHom (n + 1)
                  (finiteSuccGroupHom (n + 1) g)) hhx
      _ = standardHadjiivanovBraidProjectHom (n + 1)
            (finiteSuccGroupHom (n + 1) (g * h))
            ((appendPrimaryBonding (n + 1)).hom x) := by
              simp [map_mul, LinearEquiv.mul_apply]
  inv_mem' := by
    intro g hg
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun hg
      ((standardHadjiivanovBraidProjectHom n g).symm x)
    have h' := congrArg
      (fun y =>
        (standardHadjiivanovBraidProjectHom (n + 1)
          (finiteSuccGroupHom (n + 1) g)).symm y) h
    simpa [LinearMap.comp_apply, map_inv] using h'.symm

/-- Every Artin generator belongs to the stabilization subgroup. -/
theorem sigma_mem_stabilizationSubgroup
    (n : ℕ) (i : Fin (n + 1)) :
    σ' (n + 1) i ∈ stabilizationSubgroup n := by
  change
    (appendPrimaryBonding (n + 1)).hom.comp
        (standardHadjiivanovBraidProjectHom n (σ' (n + 1) i)).toLinearMap =
      (standardHadjiivanovBraidProjectHom (n + 1)
          (finiteSuccGroupHom (n + 1) (σ' (n + 1) i))).toLinearMap.comp
        (appendPrimaryBonding (n + 1)).hom
  rw [finiteSuccGroupHom_sigma (n + 1) i,
    standardHadjiivanovBraidProject_sigma n i,
    standardHadjiivanovBraidProject_sigma (n + 1) i.castSucc]
  exact appendPrimaryBonding_generator_compat n i

/-- Full finite-stage stabilization equivariance for every braid element. -/
theorem appendPrimaryBonding_braid_compat
    (n : ℕ) (g : braid_group (n + 2)) :
    (appendPrimaryBonding (n + 1)).hom.comp
        (standardHadjiivanovBraidProjectHom n g).toLinearMap =
      (standardHadjiivanovBraidProjectHom (n + 1)
          (finiteSuccGroupHom (n + 1) g)).toLinearMap.comp
        (appendPrimaryBonding (n + 1)).hom := by
  exact PresentedGroup.generated_by
    (braid_rels (n + 1))
    (stabilizationSubgroup n)
    (sigma_mem_stabilizationSubgroup n) g

end InfoGeometry.Categorical.LogJordanTensorPowerStabilization
