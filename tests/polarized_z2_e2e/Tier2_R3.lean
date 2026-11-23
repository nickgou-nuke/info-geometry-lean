/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
import InfoGeometry.OperatorAlgebra.ProjectorCurvatureSplitting
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option autoImplicit false

noncomputable section

namespace PolarizedZ2E2E.Tier2R3

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
open InfoGeometry.OperatorAlgebra.ProjectorCurvatureSplitting

/-! ## Local non-commutativity witnesses and concrete helpers -/

private theorem local_mat2_real_noncomm :
    (!![(0 : ℝ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 0; 1, 0] ≠
      !![0, 0; 1, 0] * !![0, 1; 0, 0] := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

private theorem local_mat3_real_noncomm :
    (!![(0 : ℝ), 0, 1; 0, 0, 0; -1, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ) *
        !![0, 0, 0; 0, 0, 1; 0, -1, 0] ≠
      !![0, 0, 0; 0, 0, 1; 0, -1, 0] * !![0, 0, 1; 0, 0, 0; -1, 0, 0] := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_three] at h01

private def localZmod2E01 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]
private def localZmod2E10 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 0; 1, 0]

private theorem local_mat2_zmod2_noncomm :
    localZmod2E01 * localZmod2E10 ≠ localZmod2E10 * localZmod2E01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 2) => M 0 0) h
  norm_num [localZmod2E01, localZmod2E10, Matrix.mul_apply, Fin.sum_univ_two] at h00

private def mat2Proj : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

private theorem mat2Proj_sq : mat2Proj * mat2Proj = mat2Proj := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [mat2Proj, Matrix.mul_apply, Fin.sum_univ_two]

private def mat2ShearUnit : (Matrix (Fin 2) (Fin 2) ℝ)ˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private def mat2LowerShearUnit : (Matrix (Fin 2) (Fin 2) ℝ)ˣ where
  val := !![1, 0; 1, 1]
  inv := !![1, 0; -1, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private def mat2DiagTwoUnit : (Matrix (Fin 2) (Fin 2) ℝ)ˣ where
  val := !![2, 0; 0, 1]
  inv := !![(2⁻¹ : ℝ), 0; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private def mat2Coupled2Unit : (Matrix (Fin 2) (Fin 2) ℝ)ˣ where
  val := !![1, 1; 1, 2]
  inv := !![2, -1; -1, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def nonflatTheta3 : OneForm (matrixDerivationsLane ℝ (Fin 3)) where
  toFun d :=
    Matrix.of fun i j : Fin 3 =>
      if i = 0 ∧ j = 1 then
        ((matrixDerivationsLane ℝ (Fin 3)).operatorAction d !![0, 1, 0; 0, 0, 0; 0, 0, 0]) 0 1
      else if i = 0 ∧ j = 2 then
        ((matrixDerivationsLane ℝ (Fin 3)).operatorAction d !![0, 0, 0; 0, -1, 0; 0, 0, 0]) 1 2
      else if i = 1 ∧ j = 0 then
        ((matrixDerivationsLane ℝ (Fin 3)).operatorAction d !![0, 0, 0; 1, 0, 0; 0, 0, 0]) 1 0
      else 0
  map_add' d₁ d₂ := by
    have hadd : ∀ M : Matrix (Fin 3) (Fin 3) ℝ,
        (matrixDerivationsLane ℝ (Fin 3)).operatorAction (d₁ + d₂) M =
          (matrixDerivationsLane ℝ (Fin 3)).operatorAction d₁ M +
            (matrixDerivationsLane ℝ (Fin 3)).operatorAction d₂ M := fun M =>
      congrArg (fun f : NonAssocDerivation.derivations ℝ (Matrix (Fin 3) (Fin 3) ℝ) =>
        (f : Module.End ℝ (Matrix (Fin 3) (Fin 3) ℝ)) M) (map_add _ d₁ d₂)
    ext i j
    dsimp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp only [hadd, Matrix.add_apply, add_zero]
  map_smul' c d := by
    have hsmul : ∀ M : Matrix (Fin 3) (Fin 3) ℝ,
        (matrixDerivationsLane ℝ (Fin 3)).operatorAction (c • d) M =
          c • (matrixDerivationsLane ℝ (Fin 3)).operatorAction d M := fun M =>
      congrArg (fun f : NonAssocDerivation.derivations ℝ (Matrix (Fin 3) (Fin 3) ℝ) =>
        (f : Module.End ℝ (Matrix (Fin 3) (Fin 3) ℝ)) M) (map_smul _ c d)
    ext i j
    dsimp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp only [hsmul, Matrix.smul_apply, smul_eq_mul, mul_zero]

/-! ## Feature F9 Boundary & Separation -/

theorem t2_f9_nongrading_derivation_breaks_cartan_split :
    let K := matrixDerivationsLane ℝ (Fin 2)
    let x := matrixInnerLieHom ℝ (Fin 2) !![0, 1; 0, 0]
    let y := matrixInnerLieHom ℝ (Fin 2) !![1, 0; 0, 0]
    let θ := gaugeForm K mat2LowerShearUnit
    let ϖ := peirceEvenOneForm K mat2Proj θ
    let e := peirceOddOneForm K mat2Proj θ
    K.operatorAction x mat2Proj ≠ 0 ∧
    connectionCurvature K θ = 0 ∧
    connectionCurvature K ϖ x y ≠ -(e x * e y - e y * e x) := by
  let K := matrixDerivationsLane ℝ (Fin 2)
  let x := matrixInnerLieHom ℝ (Fin 2) !![0, 1; 0, 0]
  let y := matrixInnerLieHom ℝ (Fin 2) !![1, 0; 0, 0]
  have hKP : K.operatorAction x mat2Proj ≠ 0 := by
    intro hzero
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hzero
    norm_num [K, x, mat2Proj, DerivationLieLane.operatorAction, matrixDerivationsLane,
      Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hflat : connectionCurvature K (gaugeForm K mat2LowerShearUnit) = 0 :=
    gaugeForm_flat K mat2LowerShearUnit
  have hbreak :
      connectionCurvature K (peirceEvenOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit)) x y ≠
        -(peirceOddOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit) x *
            peirceOddOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit) y -
          peirceOddOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit) y *
            peirceOddOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit) x) := by
    have hθx : gaugeForm K mat2LowerShearUnit x = !![1, 0; -1, -1] := by
      change mat2LowerShearUnit.inv * (!![0, 1; 0, 0] * mat2LowerShearUnit.val -
          mat2LowerShearUnit.val * !![0, 1; 0, 0]) = !![1, 0; -1, -1]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [mat2LowerShearUnit, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; norm_num)
    have hθy : gaugeForm K mat2LowerShearUnit y = !![0, 0; -1, 0] := by
      change mat2LowerShearUnit.inv * (!![1, 0; 0, 0] * mat2LowerShearUnit.val -
          mat2LowerShearUnit.val * !![1, 0; 0, 0]) = !![0, 0; -1, 0]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [mat2LowerShearUnit, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]; norm_num)
    have hlie : ⁅x, y⁆ = -x := by
      rw [← matrixInnerLieHom_commutator]
      rw [← map_neg (matrixInnerLieHom ℝ (Fin 2))]
      congr 1
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.mul_apply,
          Fin.sum_univ_two]; norm_num)
    have hθxy : gaugeForm K mat2LowerShearUnit ⁅x, y⁆ = !![-1, 0; 1, 1] := by
      rw [hlie, map_neg, hθx]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [Matrix.neg_apply]; norm_num)
    have hϖx : peirceEvenOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit) x = !![1, 0; 0, -1] := by
      rw [peirceEvenOneForm_apply, hθx]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [evenGrade, mat2Proj, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
          Matrix.one_apply, Fin.sum_univ_two]; norm_num)
    have hϖy : peirceEvenOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit) y = 0 := by
      rw [peirceEvenOneForm_apply, hθy]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [evenGrade, mat2Proj, Matrix.zero_apply, Matrix.add_apply, Matrix.sub_apply,
          Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]; norm_num)
    have hϖxy : peirceEvenOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit) ⁅x, y⁆ = !![-1, 0; 0, 1] := by
      rw [peirceEvenOneForm_apply, hθxy]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [evenGrade, mat2Proj, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
          Matrix.one_apply, Fin.sum_univ_two]; norm_num)
    have hex : peirceOddOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit) x = !![0, 0; -1, 0] := by
      rw [peirceOddOneForm_apply, hθx]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [oddGrade, mat2Proj, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
          Matrix.one_apply, Fin.sum_univ_two]; norm_num)
    have hey : peirceOddOneForm K mat2Proj (gaugeForm K mat2LowerShearUnit) y = !![0, 0; -1, 0] := by
      rw [peirceOddOneForm_apply, hθy]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [oddGrade, mat2Proj, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
          Matrix.one_apply, Fin.sum_univ_two]; norm_num)
    have hKya : K.operatorAction y !![1, 0; 0, -1] = 0 := by
      simp only [K, y, DerivationLieLane.operatorAction, LinearMap.coe_mk, AddHom.coe_mk,
        LieHom.id_apply, matrixInnerLieHom_apply]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [Matrix.sub_apply, Matrix.zero_apply, Matrix.mul_apply, Fin.sum_univ_two]; norm_num)
    intro hEq
    rw [connectionCurvature_apply, hϖx, hϖy, hϖxy, hex, hey, map_zero, hKya] at hEq
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hEq
    simp only [Matrix.neg_apply, Matrix.sub_apply,
      Matrix.mul_apply, Fin.sum_univ_two] at h00
    norm_num at h00
  exact ⟨hKP, hflat, hbreak⟩

theorem t2_f9_nonflat_theta_breaks_cartan_under_grading_preserving_K :
    let K := matrixDerivationsLane ℝ (Fin 3)
    let P : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
    let x := matrixInnerLieHom ℝ (Fin 3) !![0, 0, 0; 0, 1, 0; 0, 0, 0]
    let y := matrixInnerLieHom ℝ (Fin 3) !![0, 0, 0; 0, 0, 1; 0, 0, 0]
    let θ := nonflatTheta3
    let ϖ := peirceEvenOneForm K P θ
    let e := peirceOddOneForm K P θ
    K.operatorAction x P = 0 ∧
    K.operatorAction y P = 0 ∧
    connectionCurvature K θ x y ≠ 0 ∧
    connectionCurvature K ϖ x y ≠ -(e x * e y - e y * e x) := by
  let K := matrixDerivationsLane ℝ (Fin 3)
  let P : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
  let x := matrixInnerLieHom ℝ (Fin 3) !![0, 0, 0; 0, 1, 0; 0, 0, 0]
  let y := matrixInnerLieHom ℝ (Fin 3) !![0, 0, 0; 0, 0, 1; 0, 0, 0]
  let θ := nonflatTheta3
  have hxP : K.operatorAction x P = 0 := by
    change !![0, 0, 0; 0, 1, 0; 0, 0, 0] * P - P * !![0, 0, 0; 0, 1, 0; 0, 0, 0] = 0
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp only [P, Matrix.sub_apply, Matrix.zero_apply, Matrix.mul_apply, Fin.sum_univ_three]; norm_num)
  have hyP : K.operatorAction y P = 0 := by
    change !![0, 0, 0; 0, 0, 1; 0, 0, 0] * P - P * !![0, 0, 0; 0, 0, 1; 0, 0, 0] = 0
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp only [P, Matrix.sub_apply, Matrix.zero_apply, Matrix.mul_apply, Fin.sum_univ_three]; norm_num)
  have hact_x (M : Matrix (Fin 3) (Fin 3) ℝ) :
      K.operatorAction x M =
        !![0, 0, 0; 0, 1, 0; 0, 0, 0] * M - M * !![0, 0, 0; 0, 1, 0; 0, 0, 0] := rfl
  have hact_y (M : Matrix (Fin 3) (Fin 3) ℝ) :
      K.operatorAction y M =
        !![0, 0, 0; 0, 0, 1; 0, 0, 0] * M - M * !![0, 0, 0; 0, 0, 1; 0, 0, 0] := rfl
  have hx1 :
      ((matrixDerivationsLane ℝ (Fin 3)).operatorAction x !![0, 1, 0; 0, 0, 0; 0, 0, 0]) 0 1 =
        -1 := by
    change (K.operatorAction x !![0, 1, 0; 0, 0, 0; 0, 0, 0]) 0 1 = -1
    rw [hact_x]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  have hx2 :
      ((matrixDerivationsLane ℝ (Fin 3)).operatorAction x !![0, 0, 0; 0, -1, 0; 0, 0, 0]) 1 2 =
        0 := by
    change (K.operatorAction x !![0, 0, 0; 0, -1, 0; 0, 0, 0]) 1 2 = 0
    rw [hact_x]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  have hx3 :
      ((matrixDerivationsLane ℝ (Fin 3)).operatorAction x !![0, 0, 0; 1, 0, 0; 0, 0, 0]) 1 0 =
        1 := by
    change (K.operatorAction x !![0, 0, 0; 1, 0, 0; 0, 0, 0]) 1 0 = 1
    rw [hact_x]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  have hθx : θ x = !![0, -1, 0; 1, 0, 0; 0, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [θ, nonflatTheta3, Matrix.of_apply, hx1, hx2, hx3]
  have hy1 :
      ((matrixDerivationsLane ℝ (Fin 3)).operatorAction y !![0, 1, 0; 0, 0, 0; 0, 0, 0]) 0 1 =
        0 := by
    change (K.operatorAction y !![0, 1, 0; 0, 0, 0; 0, 0, 0]) 0 1 = 0
    rw [hact_y]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  have hy2 :
      ((matrixDerivationsLane ℝ (Fin 3)).operatorAction y !![0, 0, 0; 0, -1, 0; 0, 0, 0]) 1 2 =
        1 := by
    change (K.operatorAction y !![0, 0, 0; 0, -1, 0; 0, 0, 0]) 1 2 = 1
    rw [hact_y]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  have hy3 :
      ((matrixDerivationsLane ℝ (Fin 3)).operatorAction y !![0, 0, 0; 1, 0, 0; 0, 0, 0]) 1 0 =
        0 := by
    change (K.operatorAction y !![0, 0, 0; 1, 0, 0; 0, 0, 0]) 1 0 = 0
    rw [hact_y]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  have hθy : θ y = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [θ, nonflatTheta3, Matrix.of_apply, hy1, hy2, hy3]
  have hlie : ⁅x, y⁆ = y := by
    rw [← matrixInnerLieHom_commutator]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]; norm_num)
  have hnonflat : connectionCurvature K θ x y ≠ 0 := by
    intro hzero
    rw [connectionCurvature_apply, hlie, hθx, hθy, hact_x, hact_y] at hzero
    have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) hzero
    simp only [Matrix.zero_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.mul_apply, Fin.sum_univ_three] at h02
    norm_num at h02
  have hbreak :
      connectionCurvature K (peirceEvenOneForm K P θ) x y ≠
        -(peirceOddOneForm K P θ x * peirceOddOneForm K P θ y -
          peirceOddOneForm K P θ y * peirceOddOneForm K P θ x) := by
    have hϖ : peirceEvenOneForm K P θ = 0 := by
      ext d i j
      rw [peirceEvenOneForm_apply]
      fin_cases i <;> fin_cases j <;>
        (simp only [evenGrade, P, θ, nonflatTheta3, Matrix.add_apply,
          Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply,
          Fin.sum_univ_three];
         norm_num)
    have hex : peirceOddOneForm K P θ x = !![0, -1, 0; 1, 0, 0; 0, 0, 0] := by
      rw [peirceOddOneForm_apply, hθx]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [oddGrade, P, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
          Matrix.one_apply, Fin.sum_univ_three]; norm_num)
    have hey : peirceOddOneForm K P θ y = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
      rw [peirceOddOneForm_apply, hθy]
      ext i j; fin_cases i <;> fin_cases j <;>
        (simp only [oddGrade, P, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
          Matrix.one_apply, Fin.sum_univ_three]; norm_num)
    intro hEq
    rw [hϖ, connectionCurvature_apply, hex, hey] at hEq
    have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) hEq
    simp only [LinearMap.zero_apply, map_zero, sub_self, mul_zero, add_zero,
      Matrix.zero_apply, Matrix.neg_apply, Matrix.sub_apply,
      Matrix.mul_apply, Fin.sum_univ_three] at h12
    norm_num at h12
  exact ⟨hxP, hyP, hnonflat, hbreak⟩

theorem t2_f9_trivial_projectors_zero_and_one_collapse_odd_part
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (θ : OneForm K) (hflat : connectionCurvature K θ = 0)
    (x y : K.L) :
    peirceOddOneForm K (0 : A) θ = 0 ∧
    peirceEvenOneForm K (0 : A) θ = θ ∧
    peirceOddOneForm K (1 : A) θ = 0 ∧
    peirceEvenOneForm K (1 : A) θ = θ ∧
    connectionCurvature K (peirceEvenOneForm K (0 : A) θ) x y = 0 ∧
    connectionCurvature K (peirceEvenOneForm K (1 : A) θ) x y = 0 := by
  have h0odd : peirceOddOneForm K (0 : A) θ = 0 := by
    ext z
    simp [peirceOddOneForm_apply, oddGrade]
  have h0even : peirceEvenOneForm K (0 : A) θ = θ := by
    ext z
    simp [peirceEvenOneForm_apply, evenGrade]
  have h1odd : peirceOddOneForm K (1 : A) θ = 0 := by
    ext z
    simp [peirceOddOneForm_apply, oddGrade]
  have h1even : peirceEvenOneForm K (1 : A) θ = θ := by
    ext z
    simp [peirceEvenOneForm_apply, evenGrade]
  refine ⟨h0odd, h0even, h1odd, h1even, ?_, ?_⟩
  · rw [h0even, hflat]; rfl
  · rw [h1even, hflat]; rfl

theorem t2_f9_characteristic_two_division_free_peirce_vs_parity :
    ¬ Nonempty (Invertible (2 : ZMod 2)) ∧
    (∀ (K : DerivationLieLane (ZMod 2) (Matrix (Fin 2) (Fin 2) (ZMod 2)))
       (P : Matrix (Fin 2) (Fin 2) (ZMod 2)),
       P * P = P →
       (∀ x : K.L, K.operatorAction x P = 0) →
       ∀ (θ : OneForm K),
       connectionCurvature K θ = 0 →
       ∀ (x y : K.L),
       let ϖ := peirceEvenOneForm K P θ
       let e := peirceOddOneForm K P θ
       θ = ϖ + e ∧
       connectionCurvature K ϖ x y = -(e x * e y - e y * e x) ∧
       exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
         (ϖ y * e x - e x * ϖ y) = 0) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hinv⟩
    have h01 := hinv.invOf_mul_self
    have h20 : (2 : ZMod 2) = 0 := by decide
    have hmul : @Invertible.invOf (ZMod 2) _ _ _ hinv * (2 : ZMod 2) = 0 := by
      calc @Invertible.invOf (ZMod 2) _ _ _ hinv * (2 : ZMod 2)
          = @Invertible.invOf (ZMod 2) _ _ _ hinv * 0 := congrArg (_ * ·) h20
        _ = 0 := mul_zero _
    exact zero_ne_one (hmul.symm.trans h01)
  · intro K P hP hKP θ hflat x y
    exact graded_split_flat_cartan_equations K hP hKP θ hflat x y

theorem t2_f9_grade_orthogonality_and_odd_square_even
    {A : Type*} [Ring A] {P : A} (hP : P * P = P) (a : A) :
    evenGrade P (oddGrade P a) = 0 ∧
    oddGrade P (evenGrade P a) = 0 ∧
    (let m : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
     oddGrade mat2Proj m = m ∧
     evenGrade mat2Proj (m * m) = m * m ∧
     m * m ≠ 0) := by
  have hlaws := grade_projection_laws hP a
  refine ⟨hlaws.2.1, hlaws.2.2.1, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2Proj, oddGrade, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2Proj, evenGrade, Matrix.mul_apply, Fin.sum_univ_two]
  · intro hzero
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hzero
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-! ## Feature F10 Boundary & Separation -/

theorem t2_f10_odd_bijective_fails_equivariance :
    ∃ e_swapped : OneForm Witnesses.witnessLane,
      (∀ x, oddGrade Witnesses.witnessP (e_swapped x) = e_swapped x) ∧
      Function.Injective e_swapped ∧
      (∀ m : Witnesses.PairMat2, oddGrade Witnesses.witnessP m = m →
        ∃ x : Witnesses.witnessLane.L, e_swapped x = m) ∧
      (∃ (h : Witnesses.witnessH) (x : Witnesses.witnessLane.L),
        e_swapped (Witnesses.witnessSoldering.baseRightAct h x) ≠
          frameTransport (h.1 : Witnesses.PairMat2ˣ) (e_swapped x)) :=
  Witnesses.witness_odd_bijective_not_equivariant

theorem t2_f10_odd_equivariant_fails_bijectivity :
    ∃ e_upper : OneForm Witnesses.witnessLane,
      (∀ x, oddGrade Witnesses.witnessP (e_upper x) = e_upper x) ∧
      (∀ (h : Witnesses.witnessH) (x : Witnesses.witnessLane.L),
        e_upper (Witnesses.witnessSoldering.baseRightAct h x) =
          frameTransport (h.1 : Witnesses.PairMat2ˣ) (e_upper x)) ∧
      ¬ Function.Injective e_upper ∧
      LinearMap.range e_upper ≠ peirceOddSubmodule ℝ Witnesses.PairMat2 Witnesses.witnessP :=
  Witnesses.witness_odd_equivariant_not_bijective

theorem t2_f10_trivial_base_action_excluded_for_soldering :
    ¬ ∃ S : SolderingOneForm Witnesses.witnessLane Witnesses.witnessP Witnesses.witnessH,
      ∀ (h : Witnesses.witnessH) (x : Witnesses.witnessLane.L), S.baseRightAct h x = x :=
  Witnesses.witness_trivial_action_impossible

theorem t2_f10_zero_oneForm_never_soldering_on_nontrivial_odd_subspace
    {R : Type*} [CommRing R] [Algebra R (Matrix (Fin 2) (Fin 2) ℝ)]
    (K : DerivationLieLane R (Matrix (Fin 2) (Fin 2) ℝ))
    (H : Subgroup (Matrix (Fin 2) (Fin 2) ℝ)ˣ) :
    ¬ ∃ S : SolderingOneForm K mat2Proj H, S.toOneForm = 0 := by
  rintro ⟨S, hzero⟩
  have hodd : oddGrade mat2Proj (!![(0 : ℝ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2Proj, oddGrade, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rcases S.surjective_odd !![0, 1; 0, 0] hodd with ⟨x, hx⟩
  rw [hzero, LinearMap.zero_apply] at hx
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hx
  norm_num at h01

theorem t2_f10_non_isotropy_unit_breaks_odd_invariance_and_even_gauge :
    let K := matrixDerivationsLane ℝ (Fin 2)
    let x := matrixInnerLieHom ℝ (Fin 2) !![1, 0; 0, 0]
    let m : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    mat2ShearUnit ∉ peirceIsotropySubgroup (Matrix (Fin 2) (Fin 2) ℝ) mat2Proj ∧
    oddGrade mat2Proj m = m ∧
    evenGrade mat2Proj (frameTransport mat2ShearUnit m) ≠ 0 ∧
    oddGrade mat2Proj (gaugeForm K mat2ShearUnit x) ≠ 0 := by
  let K := matrixDerivationsLane ℝ (Fin 2)
  let x := matrixInnerLieHom ℝ (Fin 2) !![1, 0; 0, 0]
  let m : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmem
    rw [mem_peirceIsotropySubgroup] at hmem
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hmem.eq
    norm_num [mat2ShearUnit, mat2Proj, Matrix.mul_apply, Fin.sum_univ_two] at h01
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp only [mat2Proj, oddGrade, Matrix.add_apply, Matrix.sub_apply,
        Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]; norm_num)
  · intro hzero
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hzero
    simp only [mat2Proj, evenGrade, frameTransport, mat2ShearUnit,
      Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_two] at h00
    norm_num at h00
  · intro hzero
    have hg : gaugeForm K mat2ShearUnit x = !![0, 1; 0, 0] := by
      change mat2ShearUnit.inv * (!![1, 0; 0, 0] * mat2ShearUnit.val -
          mat2ShearUnit.val * !![1, 0; 0, 0]) = !![0, 1; 0, 0]
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [mat2ShearUnit, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hg] at hzero
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hzero
    simp only [mat2Proj, oddGrade, Matrix.add_apply, Matrix.sub_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] at h01
    norm_num at h01

/-! ## Feature F11 Boundary & Separation -/

theorem t2_f11_trivial_projectors_zero_and_one_annihilate_curvature
    {A : Type*} [Ring A] (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    coneMinus (0 : A) (D₁ 0) = 0 ∧
    conePlus (0 : A) (D₁ 0) = 0 ∧
    coneMinus (1 : A) (D₁ 1) = 0 ∧
    conePlus (1 : A) (D₁ 1) = 0 ∧
    (0 : A) * (D₁ 0 * D₂ 0 - D₂ 0 * D₁ 0) * 0 = 0 ∧
    (1 : A) * (D₁ 1 * D₂ 1 - D₂ 1 * D₁ 1) * 1 = 0 := by
  have h1 := projected_two_direction_curvature (P := (1 : A)) (one_mul 1) D₁ D₂ hD₁ hD₂
  have h0cM : coneMinus (0 : A) (D₁ 0) = 0 := by simp [coneMinus]
  have h0cP : conePlus (0 : A) (D₁ 0) = 0 := by simp [conePlus]
  have h1cM : coneMinus (1 : A) (D₁ 1) = 0 := by simp [coneMinus]
  have h1cP : conePlus (1 : A) (D₁ 1) = 0 := by simp [conePlus]
  have h1cM₂ : coneMinus (1 : A) (D₂ 1) = 0 := by simp [coneMinus]
  have h1cP₂ : conePlus (1 : A) (D₂ 1) = 0 := by simp [conePlus]
  refine ⟨h0cM, h0cP, h1cM, h1cP, by simp, ?_⟩
  rw [h1, h1cP, h1cP₂, zero_mul, zero_mul, sub_self]

theorem t2_f11_same_direction_or_commuting_corners_zero_curvature
    {A : Type*} [Ring A] {P : A} (hP : P * P = P)
    (D : A → A) (hD : ∀ a b : A, D (a * b) = D a * b + a * D b) :
    P * (D P * D P - D P * D P) * P = 0 ∧
    (let K := matrixDerivationsLane ℝ (Fin 2)
     let d₁ := matrixInnerLieHom ℝ (Fin 2) !![0, 1; 0, 0]
     let d₂ := matrixInnerLieHom ℝ (Fin 2) !![0, 2; 0, 0]
     d₁ ≠ d₂ ∧
     K.operatorAction d₁ mat2Proj ≠ 0 ∧
     mat2Proj * (K.operatorAction d₁ mat2Proj * K.operatorAction d₂ mat2Proj -
       K.operatorAction d₂ mat2Proj * K.operatorAction d₁ mat2Proj) * mat2Proj = 0) := by
  have hsame := projected_two_direction_curvature hP D D hD hD
  refine ⟨by rw [← sub_self (conePlus P (D P) * coneMinus P (D P)), ← hsame], ?_, ?_, ?_⟩
  · intro hEq
    have hval := congrArg (fun d => (matrixDerivationsLane ℝ (Fin 2)).operatorAction d !![0, 0; 1, 0]) hEq
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hval
    norm_num [DerivationLieLane.operatorAction, matrixDerivationsLane,
      Matrix.mul_apply, Fin.sum_univ_two] at h00
  · intro hzero
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hzero
    norm_num [DerivationLieLane.operatorAction, matrixDerivationsLane, mat2Proj,
      Matrix.mul_apply, Fin.sum_univ_two] at h01
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [DerivationLieLane.operatorAction, matrixDerivationsLane, mat2Proj,
        Matrix.mul_apply]

theorem t2_f11_unilateral_off_diagonal_vanishes_projected_curvature
    {A : Type*} [Ring A] {P : A} (hP : P * P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b)
    (hX₁ : coneMinus P (D₁ P) = 0) (hX₂ : coneMinus P (D₂ P) = 0) :
    P * (D₁ P * D₂ P - D₂ P * D₁ P) * P = 0 ∧
    (1 - P) * (D₁ P * D₂ P - D₂ P * D₁ P) * (1 - P) = 0 := by
  have hp := projected_two_direction_curvature hP D₁ D₂ hD₁ hD₂
  have hc := projected_complement_two_direction_curvature hP D₁ D₂ hD₁ hD₂
  rw [hX₁, hX₂, mul_zero, mul_zero, sub_self] at hp
  rw [hX₁, hX₂, zero_mul, zero_mul, sub_self] at hc
  exact ⟨hp, hc⟩

theorem t2_f11_non_idempotent_fails_diagonal_vanishing :
    let Q : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 2]
    let D := (matrixDerivationsLane ℝ (Fin 2)).operatorAction
      (matrixInnerLieHom ℝ (Fin 2) !![0, 0; 1, 0])
    Q * Q ≠ Q ∧ Q * D Q * Q ≠ 0 := by
  let Q : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 2]
  let D := (matrixDerivationsLane ℝ (Fin 2)).operatorAction
    (matrixInnerLieHom ℝ (Fin 2) !![0, 0; 1, 0])
  refine ⟨?_, ?_⟩
  · intro hEq
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hEq
    norm_num [Q, Matrix.mul_apply, Fin.sum_univ_two] at h11
  · intro hzero
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hzero
    norm_num [Q, D, DerivationLieLane.operatorAction, matrixDerivationsLane,
      Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem t2_f11_antisymmetry_and_traceless_commutator_vs_nonzero_projected_trace
    {A : Type*} [Ring A] {P : A} (hP : P * P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    P * (D₁ P * D₂ P - D₂ P * D₁ P) * P = -(P * (D₂ P * D₁ P - D₁ P * D₂ P) * P) ∧
    (let d₁ := matrixInnerLieHom ℝ (Fin 2) mat2E01
     let d₂ := matrixInnerLieHom ℝ (Fin 2) mat2E10
     let K := matrixDerivationsLane ℝ (Fin 2)
     Matrix.trace (K.operatorAction d₁ mat2P * K.operatorAction d₂ mat2P -
       K.operatorAction d₂ mat2P * K.operatorAction d₁ mat2P) = 0 ∧
     Matrix.trace (mat2P * (K.operatorAction d₁ mat2P * K.operatorAction d₂ mat2P -
       K.operatorAction d₂ mat2P * K.operatorAction d₁ mat2P) * mat2P) = -1) := by
  have h12 := projected_two_direction_curvature hP D₁ D₂ hD₁ hD₂
  have h21 := projected_two_direction_curvature hP D₂ D₁ hD₂ hD₁
  refine ⟨?_, ?_, mat2_projected_curvature_trace_ne_zero⟩
  · rw [h12, h21, neg_sub]
  · exact trace_projector_deriv_commutator_eq_zero
      (Matrix.traceAddMonoidHom (Fin 2) ℝ) Matrix.trace_mul_comm mat2P _ _

/-! ## Feature F12 Boundary & Separation -/

theorem t2_f12_commutative_ring_collapses_product_and_wedge
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (K : DerivationLieLane R A) (Γ : OneForm K) (g h : Aˣ) (x : K.L) :
    connectionWedgeSquare K Γ = 0 ∧
    connectionCurvature K Γ = exteriorDerivativeOne K Γ ∧
    (SatisfiesMaurerCartan K Γ ↔ IsClosedOneForm K Γ) ∧
    gaugeForm K (g * h) x = gaugeForm K g x + gaugeForm K h x := by
  refine ⟨connectionWedgeSquare_eq_zero_of_commRing K Γ,
    connectionCurvature_eq_exteriorDerivativeOne_of_commRing K Γ,
    satisfiesMaurerCartan_iff_isClosed_of_commRing K Γ, ?_⟩
  exact (gaugeForm_product_general_separation K g h x).2.2.2.2.2
    (Commute.all (↑h : A) (gaugeForm K g x))

theorem t2_f12_nonabelian_mat2_order_and_additivity_collapse_impossible :
    let K := matrixDerivationsLane ℝ (Fin 2)
    let x := matrixInnerLieHom ℝ (Fin 2) !![1, 0; 0, 0]
    gaugeForm K (mat2ShearUnit * mat2DiagTwoUnit) x ≠
      gaugeForm K mat2ShearUnit x + gaugeForm K mat2DiagTwoUnit x ∧
    gaugeForm K (mat2ShearUnit * mat2DiagTwoUnit) x ≠
      gaugeForm K (mat2DiagTwoUnit * mat2ShearUnit) x ∧
    connectionCurvature K (gaugeForm K (mat2ShearUnit * mat2DiagTwoUnit)) = 0 ∧
    connectionCurvature K (gaugeForm K (mat2DiagTwoUnit * mat2ShearUnit)) = 0 := by
  let K := matrixDerivationsLane ℝ (Fin 2)
  let x := matrixInnerLieHom ℝ (Fin 2) !![1, 0; 0, 0]
  refine ⟨?_, ?_, gaugeForm_flat K (mat2ShearUnit * mat2DiagTwoUnit),
    gaugeForm_flat K (mat2DiagTwoUnit * mat2ShearUnit)⟩
  · intro hEq
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hEq
    norm_num [K, x, gaugeForm_apply, mat2ShearUnit, mat2DiagTwoUnit,
      DerivationLieLane.operatorAction, matrixDerivationsLane,
      Matrix.mul_apply, Fin.sum_univ_two] at h01
  · intro hEq
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hEq
    norm_num [K, x, gaugeForm_apply, mat2ShearUnit, mat2DiagTwoUnit,
      DerivationLieLane.operatorAction, matrixDerivationsLane,
      Matrix.mul_apply, Fin.sum_univ_two] at h01

theorem t2_f12_stabilizer_direction_and_unit_boundary
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (g h : Aˣ) (x : K.L)
    (hg : K.operatorAction x (g : A) = 0) :
    gaugeForm K (1 : Aˣ) x = 0 ∧
    gaugeForm K g x = 0 ∧
    gaugeForm K (g * h) x = gaugeForm K h x := by
  have hg0 : gaugeForm K g x = 0 := by
    rw [gaugeForm_apply, hg, mul_zero]
  have hprod : gaugeForm K (g * h) x = gaugeForm K h x := by
    rw [gaugeForm_product, hg0, mul_zero, zero_mul, zero_add]
  exact ⟨(gaugeForm_product_general_separation K g h x).2.1, hg0, hprod⟩

theorem t2_f12_inverse_gaugeForm_requires_conjugation_order :
    let K := matrixDerivationsLane ℝ (Fin 2)
    let x := matrixInnerLieHom ℝ (Fin 2) !![1, 0; 0, 0]
    gaugeForm K mat2Coupled2Unit⁻¹ x =
      -((↑mat2Coupled2Unit : Matrix (Fin 2) (Fin 2) ℝ) * gaugeForm K mat2Coupled2Unit x *
        (↑mat2Coupled2Unit⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    gaugeForm K mat2Coupled2Unit⁻¹ x ≠ -gaugeForm K mat2Coupled2Unit x := by
  let K := matrixDerivationsLane ℝ (Fin 2)
  let x := matrixInnerLieHom ℝ (Fin 2) !![1, 0; 0, 0]
  refine ⟨(gaugeForm_product_general_separation K mat2Coupled2Unit mat2Coupled2Unit x).2.2.1, ?_⟩
  have hginv : gaugeForm K mat2Coupled2Unit⁻¹ x = !![1, -1; 2, -1] := by
    change mat2Coupled2Unit.val * (!![1, 0; 0, 0] * mat2Coupled2Unit.inv -
        mat2Coupled2Unit.inv * !![1, 0; 0, 0]) = !![1, -1; 2, -1]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [mat2Coupled2Unit, Matrix.mul_apply, Fin.sum_univ_two]
  have hg : gaugeForm K mat2Coupled2Unit x = !![1, 2; -1, -1] := by
    change mat2Coupled2Unit.inv * (!![1, 0; 0, 0] * mat2Coupled2Unit.val -
        mat2Coupled2Unit.val * !![1, 0; 0, 0]) = !![1, 2; -1, -1]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [mat2Coupled2Unit, Matrix.mul_apply, Fin.sum_univ_two]
  intro hEq
  rw [hginv, hg] at hEq
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hEq
  norm_num at h00

theorem t2_f12_exact_oneForm_closed_but_not_flat_unlike_gaugeForm :
    let K := matrixDerivationsLane ℝ (Fin 2)
    let d₁ := matrixInnerLieHom ℝ (Fin 2) mat2E01
    let d₂ := matrixInnerLieHom ℝ (Fin 2) mat2E10
    exteriorDerivativeOne K (exteriorDerivativeZero K mat2P) = 0 ∧
    connectionCurvature K (exteriorDerivativeZero K mat2P) d₁ d₂ ≠ 0 ∧
    ∀ g : (Matrix (Fin 2) (Fin 2) ℝ)ˣ, connectionCurvature K (gaugeForm K g) = 0 := by
  let K := matrixDerivationsLane ℝ (Fin 2)
  let d₁ := matrixInnerLieHom ℝ (Fin 2) mat2E01
  let d₂ := matrixInnerLieHom ℝ (Fin 2) mat2E10
  refine ⟨exteriorDerivativeOne_exteriorDerivativeZero K mat2P, ?_, fun g => gaugeForm_flat K g⟩
  intro hzero
  have hcurv := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => mat2P * M * mat2P) hzero
  rw [lane_projected_exactCurvature K mat2P_idempotent d₁ d₂] at hcurv
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hcurv
  simp only [K, d₁, d₂, mat2P, mat2E01, mat2E10, conePlus, coneMinus,
    DerivationLieLane.operatorAction, matrixDerivationsLane,
    Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] at h00
  norm_num at h00

end PolarizedZ2E2E.Tier2R3

section E2EAxiomAudit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in env.constants do
    if (env.getModuleIdxFor? name).isSome then continue
    if name.toString.startsWith "_private." then continue
    match info with
    | .thmInfo _ | .defnInfo _ =>
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial E2E declaration: {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in E2E declaration {name}"
      audited := audited + 1
    | .axiomInfo _ =>
      throwError "Disallowed axiom declaration in E2E file: {name}"
    | _ => pure ()
  if audited == 0 then
    throwError "E2EAxiomAudit found 0 declarations in current module"
  logInfo m!"E2E_AXIOM_AUDIT_PASS: {audited} local declarations verified"
end E2EAxiomAudit
