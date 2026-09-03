import InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations

/-!
# Stabilization of logarithmic tensor-power braid actions

The finite braid-group tower stabilizes by adding a strand on the right.  On the
standard Jordan tensor powers we use the primary vector `e₀` as the spectator.
Since `N e₀ = 0`, right append by `e₀` is a logarithmic intertwiner.

The main theorem proves generator-level equivariance with the existing
`B_n → B_{n+1}` stabilization: the old `i`th checked-R slice remains the `i`th
slice after the spectator strand is appended.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanTensorPowerStabilization

open CategoryTheory
open scoped TensorProduct

open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
open InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner

/-- Append one primary spectator to a single standard Jordan factor. -/
def appendPrimaryBase :
    standardJordanObject ⟶ tensorPowerObj standardJordanObject 2 where
  hom :=
    { toFun := fun x => x ⊗ₜ[ℂ] (e0 : standardJordanObject)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  comm := by
    ext x
    simp [LogEndModule.tensorObj_N_tmul, standardJordanObject_N_e0]

@[simp]
theorem appendPrimaryBase_apply (x : standardJordanObject) :
    appendPrimaryBase.hom x = x ⊗ₜ[ℂ] (e0 : standardJordanObject) := rfl

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

/-- Recursive pure-tensor action of the spectator bonding map. -/
@[simp]
theorem appendPrimaryBonding_succ_tmul
    (n : ℕ) (x : standardJordanObject)
    (t : tensorPowerObj standardJordanObject (n + 1)) :
    (appendPrimaryBonding (n + 1)).hom (x ⊗ₜ[ℂ] t) =
      x ⊗ₜ[ℂ] (appendPrimaryBonding n).hom t := by
  simp [appendPrimaryBonding, LogNilpotentModule.tensorHom]

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
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      apply LinearMap.ext
      intro t
      refine TensorProduct.induction_on t ?_ ?_ ?_
      · simp
      · intro x y
        simp [LinearMap.comp_apply, appendPrimaryBonding_succ_tmul,
          standardTensorPowerGenerator_base_tmul,
          standardTensorPowerGenerator_zero_tmul,
          standardJordanObject_N_e0]
      · intro a b ha hb
        simp [map_add, ha, hb]
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · apply LinearMap.ext
        intro t
        refine TensorProduct.induction_on t ?_ ?_ ?_
        · simp
        · intro x tail
          refine TensorProduct.induction_on tail ?_ ?_ ?_
          · simp
          · intro y rest
            simp [LinearMap.comp_apply, appendPrimaryBonding_succ_tmul,
              standardTensorPowerGenerator_zero_tmul]
          · intro a b ha hb
            simp [map_add, ha, hb]
        · intro a b ha hb
          simp [map_add, ha, hb]
      · apply LinearMap.ext
        intro t
        refine TensorProduct.induction_on t ?_ ?_ ?_
        · simp
        · intro x tail
          have htail := ih j
          have hpoint := LinearMap.congr_fun htail tail
          simpa [LinearMap.comp_apply, appendPrimaryBonding_succ_tmul,
            standardTensorPowerGenerator_succ_tmul] using
            congrArg (fun y => x ⊗ₜ[ℂ] y) hpoint
        · intro a b ha hb
          simp [map_add, ha, hb]

end InfoGeometry.Categorical.LogJordanTensorPowerStabilization
