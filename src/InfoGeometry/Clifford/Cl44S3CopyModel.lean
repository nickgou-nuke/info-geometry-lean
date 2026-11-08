/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Clifford.Cl44S3Family
import InfoGeometry.Synthesis.Cl44PrimitiveIdempotentIdeal

/-!
# Three-copy permutation model for the even Cl(4,4) semi-spinor carrier

This candidate constructs an `S₃` permutation representation on three copies
of `SemiSpinorPlus`.  The selected family vectors are one-hot copies of a
fixed nonzero even coordinate state.  Arbitrary endomorphisms are lifted
componentwise.  This is only a finite permutation model; it does not assert
an `SU(3)` or `U(1)` action, an action on one spinor, or an action induced by
another algebra.
-/

set_option autoImplicit false

namespace InfoGeometry.Clifford.Cl44S3CopyModel

open InfoGeometry.Clifford.Cl44S3Family
open InfoGeometry.Cl44IdempotentIdeal

abbrev CopyCarrier := Fin 3 → SemiSpinorPlus

/-- The coordinate vacuum has even occupation parity. -/
theorem stateParity_zero_even : stateParity (0 : Fin 16) = 0 := by
  decide

/-- A fixed nonzero even basis state in the coordinate semi-spinor submodule. -/
def evenBasisState : SemiSpinorPlus :=
  ⟨Pi.single (0 : Fin 16) (1 : ℝ), by
    intro i hi
    simp only [Pi.single_apply]
    split_ifs with h
    · subst i
      rw [stateParity_zero_even] at hi
      omega
    · rfl⟩

@[simp] theorem evenBasisState_zero : (evenBasisState : Fin 16 → ℝ) 0 = 1 := by
  simp [evenBasisState]

theorem evenBasisState_ne_zero : evenBasisState ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : SemiSpinorPlus => x.val (0 : Fin 16)) h
  norm_num [evenBasisState_zero] at h0

/-- A one-hot family vector carrying the same even state in one copy. -/
def oneHotFamily (i : Fin 3) : CopyCarrier :=
  fun j => if j = i then evenBasisState else 0

/-- The inverse-precomposition permutation action on copy coordinates. -/
def s3CopyAction (σ : Equiv.Perm (Fin 3)) : CopyCarrier →ₗ[ℝ] CopyCarrier where
  toFun x j := x (σ.symm j)
  map_add' x y := by
    ext j k
    rfl
  map_smul' c x := by
    ext j k
    rfl

/-- Componentwise lift of an arbitrary semi-spinor endomorphism. -/
def diagonalLift (T : SemiSpinorPlus →ₗ[ℝ] SemiSpinorPlus) :
    CopyCarrier →ₗ[ℝ] CopyCarrier where
  toFun x j := T (x j)
  map_add' x y := by
    ext j k
    exact congrFun (congrArg Subtype.val (T.map_add (x j) (y j))) k
  map_smul' c x := by
    ext j k
    exact congrFun (congrArg Subtype.val (T.map_smul c (x j))) k

@[simp] theorem s3CopyAction_one :
    s3CopyAction (1 : Equiv.Perm (Fin 3)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext j
  apply Subtype.ext
  funext k
  change (x ((Equiv.refl (Fin 3)).symm j)).val k = (x j).val k
  rfl

@[simp] theorem s3CopyAction_mul (σ τ : Equiv.Perm (Fin 3)) :
    s3CopyAction (σ * τ) = (s3CopyAction σ).comp (s3CopyAction τ) := by
  apply LinearMap.ext
  intro x
  funext j
  apply Subtype.ext
  funext k
  have hinv : (σ * τ).symm = τ.symm * σ.symm := by
    change (τ.trans σ).symm = τ.symm * σ.symm
    rw [Equiv.symm_trans]
    rfl
  change (x ((σ * τ).symm j)).val k = (x (τ.symm (σ.symm j))).val k
  rw [hinv]
  rfl

@[simp] theorem s3CopyAction_oneHot (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    s3CopyAction σ (oneHotFamily i) = oneHotFamily (σ i) := by
  ext j k
  have hiff : σ.symm j = i ↔ j = σ i := by
    constructor
    · intro h
      have := congrArg σ h
      simpa using this
    · intro h
      have := congrArg (fun x => σ.symm x) h
      simpa using this
  simp [s3CopyAction, oneHotFamily, hiff]

theorem s3CopyAction_commutes_diagonalLift
    (σ : Equiv.Perm (Fin 3))
    (T : SemiSpinorPlus →ₗ[ℝ] SemiSpinorPlus) :
    (s3CopyAction σ).comp (diagonalLift T) =
      (diagonalLift T).comp (s3CopyAction σ) := by
  ext x j k
  rfl

theorem oneHotFamily_linearIndependent : LinearIndependent ℝ oneHotFamily := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i his
  have hcoord : (∑ j ∈ s, g j * (oneHotFamily j i).val (0 : Fin 16)) = 0 := by
    have hcomponent : (∑ j ∈ s, g j • oneHotFamily j i) = 0 := by
      simpa only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply] using
        congrFun hsum i
    have heval := congrArg (fun z : SemiSpinorPlus => z.val (0 : Fin 16)) hcomponent
    simpa [Pi.smul_apply, smul_eq_mul] using heval
  have hcollapse :
      (∑ j ∈ s, g j * (oneHotFamily j i).val (0 : Fin 16)) = g i := by
    rw [Finset.sum_eq_single i]
    · simp [oneHotFamily, evenBasisState_zero]
    · intro j hj hji
      simp [oneHotFamily, hji.symm]
    · intro hi
      exact (hi his).elim
  rw [hcollapse] at hcoord
  exact hcoord

/-- A concrete datum for three copies, with arbitrary pointwise operators. -/
def threeCopyDatum
    (C Q : SemiSpinorPlus →ₗ[ℝ] SemiSpinorPlus) :
    SplitS3FamilyDatum CopyCarrier where
  s3Action := s3CopyAction
  action_one := s3CopyAction_one
  action_mul := s3CopyAction_mul
  family := oneHotFamily
  colorOperator := diagonalLift C
  chargeOperator := diagonalLift Q
  preserves_semiSpinors := s3CopyAction_oneHot
  color_invariant := fun σ => s3CopyAction_commutes_diagonalLift σ C
  charge_invariant := fun σ => s3CopyAction_commutes_diagonalLift σ Q
  linearly_independent_families := oneHotFamily_linearIndependent

/-- The requested finite three-copy permutation model. -/
theorem exists_cl44_three_copy_s3_family_datum
    (C Q : SemiSpinorPlus →ₗ[ℝ] SemiSpinorPlus) :
    ∃ D : SplitS3FamilyDatum CopyCarrier,
      D.colorOperator = diagonalLift C ∧
      D.chargeOperator = diagonalLift Q := by
  exact ⟨threeCopyDatum C Q, rfl, rfl⟩

end InfoGeometry.Clifford.Cl44S3CopyModel
