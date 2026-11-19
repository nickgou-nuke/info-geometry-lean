/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport
import InfoGeometry.OperatorAlgebra.DerivationRightLogarithmicForm
import InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
import InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
import InfoGeometry.OperatorAlgebra.MatrixMaurerCartan
import InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge
import InfoGeometry.Optics.DerivationBackedMaurerCartanFrame
import InfoGeometry.Canonical.MaurerCartanFactorization
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceMaurerCartanCurvatureWitness
import InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset
import InfoGeometry.Canonical.TensorStageExactConnection

/-!
# Canonical Maurer--Cartan sign dictionary and multi-stage Maurer--Cartan tower

This module reconciles all Maurer--Cartan (MC) conventions and multi-stage tower
constructions in the repository around the canonical left-logarithmic 1-form

`θ_L(g)(x) = g⁻¹ * D_x(g)`, `d θ_L + θ_L ∧ θ_L = 0`:

1. **Section 1 — Canonical Sign Dictionary & Left/Right Gauge Covariance (F1.2, F1.7)**:
   - Freezes `thetaL` and `thetaR` in `DerivationOperatorForm K 1`, proves
     `thetaL_flat` (`ceCurvature K (thetaL K g) = 0`) and `thetaR_maurerCartan`
     (`d θ_R = θ_R ∧ θ_R`), and establishes the exact algebraic dictionary
     relating `thetaL`, `thetaR`, `gaugeForm`, `rightLogarithmicOneForm`,
     `gaugeOneForm K 0`, `NCG.AlgebraDerivation.pureGaugeForm`,
     `MatrixMaurerCartan.maurerCartan`,
     `NoncommutativeMaurerCartanAdjointBridge.maurerCartanForm`, and
     `DerivationBackedMaurerCartanFrame.fromDirectionalDerivation`.
   - Explicitly disambiguates `Canonical.MaurerCartanFactorization.maurerCartanForm`
     (outer-derivation commutator descent on `Out(A)`, not a unit-valued `g⁻¹ dg` 1-form).
   - Proves exact gauge covariance (degree 0, `fundamentalCovariantDerivative`,
     curvature `ceCurvature`, arbitrary-degree `covariantExteriorDerivativeN`,
     and Bianchi) for both the left action `gaugeTransformOneForm K g Γ`
     and the right action `rightGaugeTransformOneForm K Γ g`.

2. **Section 2 — General `LieActionLane` Curvature/MC Calculus & Unified Tower (F1.2, F1.7)**:
   - Lifts `actionWedge_assoc'`, `actionCurvature`, `actionCovariantExteriorDerivativeN`,
     Ricci (`actionCovariantExteriorDerivativeN_comp`), Bianchi (`actionCurvature_bianchi`),
     `actionThetaL`, `actionThetaR`, `actionThetaL_flat`, and `actionGaugeOneForm`
     covariance to arbitrary `LieActionLane R A` with `IsLeibnizAction K`
     (no faithfulness or `Algebra R A` required, supporting `R = ℤ` on arbitrary rings).
   - Defines `MaurerCartanStage`, `MaurerCartanStageHom`, the intertwining cospan
     (`comapLane`, `pushCoeff`, `pullDir`, `StageFormCompatible`), and `MaurerCartanTower`
     with iterated `bond` and `TowerForm`.

3. **Section 3 — Instantiating All Three Repository MC Formalisms (F1.2, F1.7)**:
   - **Formalism 1**: `derivationLieStage` + unit-frame flat MC & gauge-orbit stages.
   - **Formalism 2**: `peirceFiveGradedStage` & `peirce_five_graded_mc_stage`
     bridging `frontier2_nilpotent_differentials_climb_five_graded_maurer_cartan_tower`
     (and `peirceThreeGradedWitnessStage` bridging `PeirceMaurerCartanCurvatureWitness`),
     reconciling CE 2-form flatness (`actionCurvature = 0`) with the single-derivation
     structural defect `D(θ) + θ² = g⁻¹ D²(g)` and the chiral-twisted `d_out2`/`d_in2`.
   - **Formalism 3**: `tensorStageTower` & `tensor_stage_mc_transport` bridging
     `TensorStageExactConnection`, establishing stagewise `d₀ P` transport,
     `exactCutCurvature`, `ofStage` cocone descent (respecting the `BUCKET 3`
     boundary: no fabricated direct-limit connection), the three explicit
     flat `d₀ P` cases (`n = 0`, central `algebraMap ℝ (Stage n) c`, and inner-flat `P`
     on `stageInnerRangeLane`), and unconditionally flat unit-frame `thetaL` transport.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MaurerCartanTower

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
open InfoGeometry.Geometry.AssociativeGaugeConnection

/-! ## Section 1A: General `LieActionLane` associative wedge, curvature, MC, and gauge calculus -/

section GeneralLieActionCalculus

section BasicForms

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- Degree-0 linear equivalence `A ≃ₗ[R] ActionOperatorForm K 0`. -/
def actionZeroFormEquiv (K : LieActionLane R A) :
    A ≃ₗ[R] ActionOperatorForm K 0 :=
  AlternatingMap.constLinearEquivOfIsEmpty

@[simp] theorem actionZeroFormEquiv_apply (K : LieActionLane R A)
    (a : A) (v : Fin 0 → K.L) :
    actionZeroFormEquiv K a v = a :=
  rfl

@[simp] theorem actionZeroFormEquiv_symm_apply (K : LieActionLane R A)
    (ω : ActionOperatorForm K 0) :
    (actionZeroFormEquiv K).symm ω = ω Fin.elim0 := by
  change ω _ = ω Fin.elim0
  congr 1
  exact Subsingleton.elim _ _

end BasicForms

variable {R A : Type*} [CommRing R] [Ring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Associativity of `actionWedge` over any associative ring `A` with scalar compatibility
(without requiring `[Algebra R A]`, so `R = ℤ` on arbitrary `[Ring B]` avoids diamonds). -/
theorem actionWedge_assoc' (K : LieActionLane R A) :
    ∀ (p q r : ℕ) (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q)
      (θ : ActionOperatorForm K r),
      reindexForm (Nat.add_assoc p q r) (actionWedge K (actionWedge K ω η) θ) =
        actionWedge K ω (actionWedge K η θ)
  | 0, 0, r, ω, η, θ => by
    ext v
    simp only [reindexForm_apply, actionWedge_zero_left,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply', mul_assoc]
    congr 2
  | 0, q' + 1, 0, ω, η, θ => by
    ext v
    simp only [reindexForm_apply, actionWedge_zero_left, actionWedge_zero_right,
      LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, LinearMap.mul_apply', mul_assoc]
    congr 2
  | 0, q' + 1, r' + 1, ω, η, θ => by
    apply alternating_ext_curryLeft
    intro x
    rw [reindexForm_curryLeft, actionWedge_succ_succ_curryLeft]
    have hL : (actionWedge K ω η).curryLeft x =
        reindexForm (by omega : 0 + q' = 0 + (q' + 1) - 1)
          (actionWedge K ω (η.curryLeft x)) := by
      rw [actionWedge_zero_left, reindexForm_curryLeft, actionWedge_zero_left, reindexForm_trans]
      rfl
    have hR : (actionWedge K ω (actionWedge K η θ)).curryLeft x =
        reindexForm (by omega : 0 + (q' + 1 + r') = 0 + (q' + 1 + (r' + 1)) - 1)
          (actionWedge K ω ((actionWedge K η θ).curryLeft x)) := by
      rw [actionWedge_zero_left, reindexForm_curryLeft, actionWedge_zero_left, reindexForm_trans]
      rfl
    rw [hL, actionWedge_reindexForm_left, hR, actionWedge_succ_succ_curryLeft,
      actionWedge_add_right, actionWedge_smul_right, actionWedge_reindexForm_right]
    have ih1 := actionWedge_assoc' K 0 q' (r' + 1) ω (η.curryLeft x) θ
    have ih2 := actionWedge_assoc' K 0 (q' + 1) r' ω η (θ.curryLeft x)
    rw [← ih1, ← ih2]
    simp only [reindexForm_add, reindexForm_smul, reindexForm_trans]
    ext w
    simp only [AlternatingMap.add_apply, AlternatingMap.smul_apply, reindexForm_apply]
    rw [show (-1 : R) ^ (Nat.add 0 q' + 1) = (-1 : R) ^ (q' + 1) by
      change (-1 : R) ^ (0 + q' + 1) = _
      rw [Nat.zero_add]]
  | p' + 1, 0, 0, ω, η, θ => by
    ext v
    simp only [reindexForm_apply, actionWedge_zero_right, LinearMap.compAlternatingMap_apply,
      LinearMap.flip_apply, LinearMap.mul_apply', mul_assoc]
    congr 2
  | p' + 1, 0, r' + 1, ω, η, θ => by
    apply alternating_ext_curryLeft
    intro x
    rw [reindexForm_curryLeft, actionWedge_succ_succ_curryLeft,
      actionWedge_succ_succ_curryLeft]
    have h0 : (actionWedge K ω η).curryLeft x = actionWedge K (ω.curryLeft x) η := by
      rw [actionWedge_zero_right, actionWedge_zero_right]
      rfl
    rw [h0]
    have h1 : (actionWedge K η θ).curryLeft x =
        reindexForm (by omega : 0 + r' = (0 + (r' + 1)) - 1)
          (actionWedge K η (θ.curryLeft x)) := by
      rw [actionWedge_zero_left, reindexForm_curryLeft, actionWedge_zero_left, reindexForm_trans]
      rfl
    rw [h1, actionWedge_reindexForm_right]
    have ih1 := actionWedge_assoc' K p' 0 (r' + 1) (ω.curryLeft x) η θ
    have ih2 := actionWedge_assoc' K (p' + 1) 0 r' ω η (θ.curryLeft x)
    rw [← ih1, ← ih2]
    simp only [reindexForm_add, reindexForm_smul, reindexForm_trans]
  | p' + 1, q' + 1, 0, ω, η, θ => by
    apply alternating_ext_curryLeft
    intro x
    rw [reindexForm_curryLeft]
    have hL : (actionWedge K (actionWedge K ω η) θ).curryLeft x =
        actionWedge K ((actionWedge K ω η).curryLeft x) θ := by
      rw [actionWedge_zero_right, actionWedge_zero_right]
      rfl
    have hR' : (actionWedge K η θ).curryLeft x = actionWedge K (η.curryLeft x) θ := by
      rw [actionWedge_zero_right, actionWedge_zero_right]
      rfl
    rw [hL, actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft, hR',
      actionWedge_add_left, actionWedge_smul_left, actionWedge_reindexForm_left]
    have ih1 := actionWedge_assoc' K p' (q' + 1) 0 (ω.curryLeft x) η θ
    have ih2 := actionWedge_assoc' K (p' + 1) q' 0 ω (η.curryLeft x) θ
    rw [← ih1, ← ih2]
    simp only [reindexForm_add, reindexForm_smul, reindexForm_trans]
  | p' + 1, q' + 1, r' + 1, ω, η, θ => by
    apply alternating_ext_curryLeft
    intro x
    rw [reindexForm_curryLeft]
    rw [actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft,
      actionWedge_succ_succ_curryLeft, actionWedge_succ_succ_curryLeft]
    simp only [reindexForm_add, reindexForm_smul,
      actionWedge_add_left, actionWedge_smul_left,
      actionWedge_add_right, actionWedge_smul_right,
      actionWedge_reindexForm_left, actionWedge_reindexForm_right, reindexForm_trans]
    have ih1 := actionWedge_assoc' K p' (q' + 1) (r' + 1) (ω.curryLeft x) η θ
    have ih2 := actionWedge_assoc' K (p' + 1) q' (r' + 1) ω (η.curryLeft x) θ
    have ih3 := actionWedge_assoc' K (p' + 1) (q' + 1) r' ω η (θ.curryLeft x)
    rw [← ih1, ← ih2, ← ih3]
    simp only [reindexForm_trans, smul_add, smul_smul, pow_add, add_assoc]
    ext w
    simp only [AlternatingMap.add_apply, AlternatingMap.smul_apply, reindexForm_apply]
    rw [show (-1 : R) ^ ((p' + 1).add q') * (-1 : R) ^ 1 =
        (-1 : R) ^ p' * (-1 : R) ^ 1 * ((-1 : R) ^ q' * (-1 : R) ^ 1) by
      change (-1 : R) ^ (p' + 1 + q') * (-1 : R) ^ 1 = _
      rw [pow_add, pow_add, pow_one]
      ring]
termination_by p q r => p + q + r

/-- Arbitrary-degree curvature `F = dΓ + Γ ∧ Γ` on `ActionOperatorForm K 1`. -/
def actionCurvature (K : LieActionLane R A) (Γ : ActionOperatorForm K 1) :
    ActionOperatorForm K 2 :=
  actionExteriorDerivative K 1 Γ + actionWedge K Γ Γ

@[simp] theorem actionCurvature_apply (K : LieActionLane R A)
    (Γ : ActionOperatorForm K 1) (x y : K.L) :
    actionCurvature K Γ ![x, y] =
      K.operatorAction x (Γ ![y]) - K.operatorAction y (Γ ![x]) -
        Γ ![⁅x, y⁆] + (Γ ![x] * Γ ![y] - Γ ![y] * Γ ![x]) := by
  dsimp [actionCurvature]
  rw [actionWedge_one_one_apply]
  have h01 : ![x, y] = Matrix.vecCons x ![y] := by
    ext i; fin_cases i <;> rfl
  have h1 : (actionExteriorDerivative K 1 Γ) ![x, y] =
      K.operatorAction x (Γ ![y]) - K.operatorAction y (Γ ![x]) - Γ ![⁅x, y⁆] := by
    rw [h01, ← AlternatingMap.curryLeft_apply_apply, actionExteriorDerivative_succ_curryLeft]
    simp only [AlternatingMap.sub_apply, lieDeriv_apply, actionExteriorDerivative_zero_apply]
    have hsum : (∑ i : Fin 1, Γ (Function.update ![y] i ⁅x, ![y] i⁆)) = Γ ![⁅x, y⁆] := by
      rw [Fin.sum_univ_one]
      congr 1
      ext j; fin_cases j; rfl
    have hcur : (Γ.curryLeft x) Fin.elim0 = Γ ![x] := by
      rw [AlternatingMap.curryLeft_apply_apply]
      congr 1
    rw [hsum, hcur]
    abel
  rw [h1]
  rfl

/-- Arbitrary-degree covariant exterior derivative on `ActionOperatorForm K n`:
`d_Γ ω = dω + Γ ∧ ω - (-1)^n ω ∧ Γ`. -/
def actionCovariantExteriorDerivativeN (K : LieActionLane R A)
    (Γ : ActionOperatorForm K 1) (n : ℕ) :
    ActionOperatorForm K n →ₗ[R] ActionOperatorForm K (n + 1) where
  toFun ω :=
    actionExteriorDerivative K n ω +
      reindexForm (Nat.add_comm 1 n) (actionWedge K Γ ω) -
        ((-1 : R) ^ n) • actionWedge K ω Γ
  map_add' ω₁ ω₂ := by
    simp only [map_add, actionWedge_add_right, actionWedge_add_left, reindexForm_add, smul_add]
    abel
  map_smul' c ω := by
    simp only [map_smul, actionWedge_smul_right, actionWedge_smul_left, reindexForm_smul,
      RingHom.id_apply]
    rw [smul_sub, smul_add, smul_comm c ((-1 : R) ^ n)]

/-- Arbitrary-degree Ricci identity on any `LieActionLane R A` satisfying `IsLeibnizAction K`:
`d_Γ (d_Γ ω) = F ∧ ω - ω ∧ F`. -/
theorem actionCovariantExteriorDerivativeN_comp (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (Γ : ActionOperatorForm K 1) (n : ℕ)
    (ω : ActionOperatorForm K n) :
    actionCovariantExteriorDerivativeN K Γ (n + 1)
        (actionCovariantExteriorDerivativeN K Γ n ω) =
      reindexForm (Nat.add_comm 2 n) (actionWedge K (actionCurvature K Γ) ω) -
        actionWedge K ω (actionCurvature K Γ) := by
  dsimp [actionCovariantExteriorDerivativeN, actionCurvature]
  simp only [map_add, map_sub, map_smul, actionExteriorDerivative_succ_comp, zero_add,
    actionExteriorDerivative_reindexForm, actionExteriorDerivative_actionWedge K hK,
    actionWedge_add_left, actionWedge_add_right, actionWedge_sub_left, actionWedge_sub_right,
    actionWedge_smul_left, actionWedge_smul_right,
    reindexForm_add, reindexForm_sub, reindexForm_smul, reindexForm_trans,
    pow_one, smul_add, smul_smul]
  have hsq : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
    rw [← mul_pow]
    have hneg1 : (-1 : R) * -1 = 1 := by ring
    simp [hneg1]
  have hsucc : (-1 : R) ^ (n + 1) = -((-1 : R) ^ n) := by
    rw [pow_succ]
    ring
  rw [hsucc, hsq, one_smul]
  have hassoc1 :
      reindexForm (by omega : (1 + 1) + n = n + 2) (actionWedge K (actionWedge K Γ Γ) ω) =
        reindexForm (by omega : 1 + (n + 1) = n + 2)
          (actionWedge K Γ (reindexForm (Nat.add_comm 1 n) (actionWedge K Γ ω))) := by
    rw [actionWedge_reindexForm_right, reindexForm_trans,
      ← actionWedge_assoc' K 1 1 n Γ Γ ω, reindexForm_trans]
  have hassoc2 :
      reindexForm (by omega : 1 + (n + 1) = n + 2)
          (actionWedge K Γ (actionWedge K ω Γ)) =
        actionWedge K (reindexForm (Nat.add_comm 1 n) (actionWedge K Γ ω)) Γ := by
    rw [actionWedge_reindexForm_left, ← actionWedge_assoc' K 1 n 1 Γ ω Γ, reindexForm_trans]
  have hassoc3 :
      actionWedge K (actionWedge K ω Γ) Γ = actionWedge K ω (actionWedge K Γ Γ) := by
    simpa [reindexForm_rfl] using actionWedge_assoc' K n 1 1 ω Γ Γ
  rw [← hassoc1, hassoc2, hassoc3]
  ext v
  simp only [AlternatingMap.add_apply, AlternatingMap.sub_apply,
    AlternatingMap.smul_apply, reindexForm_apply]
  have hid : ∀ {m : ℕ} (h : m = m) (α : ActionOperatorForm K m) (u : Fin m → K.L),
      α (u ∘ finCongr h) = α u := fun _ _ _ => rfl
  simp only [hid]
  simp only [sub_eq_add_neg, smul_add, smul_neg, smul_smul, neg_mul, neg_neg, hsq,
    one_smul, neg_smul]
  abel

theorem actionCovariantExteriorDerivativeN_comp_of_flat (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (Γ : ActionOperatorForm K 1)
    (hΓ : actionCurvature K Γ = 0) (n : ℕ) (ω : ActionOperatorForm K n) :
    actionCovariantExteriorDerivativeN K Γ (n + 1)
        (actionCovariantExteriorDerivativeN K Γ n ω) = 0 := by
  rw [actionCovariantExteriorDerivativeN_comp K hK, hΓ]
  simp [actionWedge]

/-- Arbitrary-degree covariant Bianchi identity on any `LieActionLane R A` with `IsLeibnizAction K`:
`d_Γ F = 0`. -/
theorem actionCurvature_bianchi (K : LieActionLane R A) (hK : IsLeibnizAction K)
    (Γ : ActionOperatorForm K 1) :
    actionCovariantExteriorDerivativeN K Γ 2 (actionCurvature K Γ) = 0 := by
  dsimp [actionCovariantExteriorDerivativeN, actionCurvature]
  rw [map_add, actionExteriorDerivative_succ_comp, zero_add]
  have hdw : actionExteriorDerivative K 2 (actionWedge K Γ Γ) =
      reindexForm (by omega : (1 + 1) + 1 = 2 + 1)
          (actionWedge K (actionExteriorDerivative K 1 Γ) Γ) +
        ((-1 : R) ^ (1 : ℕ)) •
          reindexForm (by omega : 1 + (1 + 1) = 2 + 1)
            (actionWedge K Γ (actionExteriorDerivative K 1 Γ)) :=
    actionExteriorDerivative_actionWedge K hK 1 1 Γ Γ
  rw [hdw]
  have hp1 :
      ((-1 : R) ^ (1 : ℕ)) •
          reindexForm (by omega : 1 + (1 + 1) = 2 + 1)
            (actionWedge K Γ (actionExteriorDerivative K 1 Γ)) =
        -reindexForm (by omega : 1 + (1 + 1) = 2 + 1)
          (actionWedge K Γ (actionExteriorDerivative K 1 Γ)) := by
    rw [pow_one]
    exact neg_one_smul R (reindexForm (by omega : 1 + (1 + 1) = 2 + 1)
      (actionWedge K Γ (actionExteriorDerivative K 1 Γ)))
  have hp2 : (-1 : R) ^ (2 : ℕ) = 1 := by ring
  rw [hp1, hp2, one_smul]
  simp only [actionWedge_add_left, actionWedge_add_right, reindexForm_add]
  have hassoc :
      actionWedge K (actionWedge K Γ Γ) Γ = actionWedge K Γ (actionWedge K Γ Γ) := by
    simpa [reindexForm_rfl] using actionWedge_assoc' K 1 1 1 Γ Γ Γ
  rw [hassoc]
  ext v
  have hv : v ∘ finCongr (Nat.add_comm 1 2) = v := funext fun i => rfl
  simp only [AlternatingMap.add_apply, AlternatingMap.sub_apply, AlternatingMap.neg_apply,
    AlternatingMap.zero_apply, reindexForm_apply, hv]
  abel

/-! ### Leibniz unit differentiation, conjugation, `actionThetaL`/`actionThetaR`, and gauge covariance -/

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem lieAction_operatorAction_one (K : LieActionLane R A) (hK : IsLeibnizAction K)
    (x : K.L) : K.operatorAction x (1 : A) = 0 := by
  have h := hK x (1 : A) 1
  simp only [one_mul, mul_one] at h
  exact add_eq_left.mp h.symm

omit [IsScalarTower R A A] [SMulCommClass R A A] in
theorem lieAction_operatorAction_inv_unit (K : LieActionLane R A) (hK : IsLeibnizAction K)
    (g : Aˣ) (x : K.L) :
    K.operatorAction x (↑g⁻¹ : A) =
      -((↑g⁻¹ : A) * K.operatorAction x (g : A) * (↑g⁻¹ : A)) := by
  have h : K.operatorAction x (g : A) * (↑g⁻¹ : A) +
      (g : A) * K.operatorAction x (↑g⁻¹ : A) = 0 := by
    rw [← hK x (g : A) (↑g⁻¹ : A), Units.mul_inv, lieAction_operatorAction_one K hK x]
  have hh := congrArg (fun a : A => (↑g⁻¹ : A) * a) h
  simp only [mul_add, mul_zero, ← mul_assoc, Units.inv_mul, one_mul] at hh
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hh

/-- Canonical left-logarithmic Maurer--Cartan 1-form `θ_L(g)(x) = g⁻¹ * D_x(g)`
on any `LieActionLane R A`. -/
def actionThetaL (K : LieActionLane R A) (g : Aˣ) : ActionOperatorForm K 1 :=
  AlternatingMap.ofSubsingleton R K.L A (0 : Fin 1)
    { toFun := fun x => (↑g⁻¹ : A) * K.operatorAction x (g : A)
      map_add' := fun x y => by simp [map_add, mul_add]
      map_smul' := fun c x => by simp [map_smul, mul_smul_comm] }

omit [IsScalarTower R A A] in
@[simp] theorem actionThetaL_apply (K : LieActionLane R A) (g : Aˣ) (v : Fin 1 → K.L) :
    actionThetaL K g v = (↑g⁻¹ : A) * K.operatorAction (v 0) (g : A) :=
  rfl

/-- Right-logarithmic Maurer--Cartan 1-form `θ_R(g)(x) = D_x(g) * g⁻¹`
on any `LieActionLane R A`. -/
def actionThetaR (K : LieActionLane R A) (g : Aˣ) : ActionOperatorForm K 1 :=
  AlternatingMap.ofSubsingleton R K.L A (0 : Fin 1)
    { toFun := fun x => K.operatorAction x (g : A) * (↑g⁻¹ : A)
      map_add' := fun x y => by simp [map_add, add_mul]
      map_smul' := fun c x => by simp [map_smul, smul_mul_assoc] }

omit [SMulCommClass R A A] in
@[simp] theorem actionThetaR_apply (K : LieActionLane R A) (g : Aˣ) (v : Fin 1 → K.L) :
    actionThetaR K g v = K.operatorAction (v 0) (g : A) * (↑g⁻¹ : A) :=
  rfl

/-- Unconditional CE 2-form flatness of `actionThetaL` on any `LieActionLane R A`
satisfying `IsLeibnizAction K`: `d θ_L + θ_L ∧ θ_L = 0`. -/
theorem actionThetaL_flat (K : LieActionLane R A) (hK : IsLeibnizAction K) (g : Aˣ) :
    actionCurvature K (actionThetaL K g) = 0 := by
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i; fin_cases i <;> rfl
  rw [hv, actionCurvature_apply]
  simp only [actionThetaL_apply, Matrix.cons_val_zero, K.operatorAction_commutator_apply,
    AlternatingMap.zero_apply]
  rw [hK (v 0) (↑g⁻¹ : A) (K.operatorAction (v 1) (g : A)),
    hK (v 1) (↑g⁻¹ : A) (K.operatorAction (v 0) (g : A)),
    lieAction_operatorAction_inv_unit K hK g (v 0),
    lieAction_operatorAction_inv_unit K hK g (v 1)]
  noncomm_ring

/-- `R`-linear conjugation equivalence `x ↦ g * x * g⁻¹` on an associative ring `A`
with `[Module R A] [IsScalarTower R A A] [SMulCommClass R A A]`. -/
def actionConjugateLinearEquiv (R A : Type*) [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (g : Aˣ) : A ≃ₗ[R] A where
  toFun := conjugate g
  invFun := conjugate g⁻¹
  left_inv x := by simp [conjugate, mul_assoc]
  right_inv x := by simp [conjugate, mul_assoc]
  map_add' x y := by simp [conjugate, mul_add, add_mul]
  map_smul' r x := by simp [conjugate, mul_smul_comm, smul_mul_assoc]

@[simp] theorem actionConjugateLinearEquiv_apply (R A : Type*) [CommRing R] [Ring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (g : Aˣ) (x : A) :
    actionConjugateLinearEquiv R A g x = conjugate g x :=
  rfl

/-- Left conjugation action `(g · ω)(v) = g * ω(v) * g⁻¹` on `ActionOperatorForm K n`. -/
def actionConjugateForm (K : LieActionLane R A) (g : Aˣ) {n : ℕ} :
    ActionOperatorForm K n ≃ₗ[R] ActionOperatorForm K n where
  toFun ω := (actionConjugateLinearEquiv R A g).toLinearMap.compAlternatingMap ω
  invFun ω := (actionConjugateLinearEquiv R A g⁻¹).toLinearMap.compAlternatingMap ω
  left_inv ω := by
    ext v
    simp [conjugate, mul_assoc]
  right_inv ω := by
    ext v
    simp [conjugate, mul_assoc]
  map_add' ω₁ ω₂ := by
    ext v
    simp [conjugate]
  map_smul' r ω := by
    ext v
    simp [conjugate]

@[simp] theorem actionConjugateForm_apply (K : LieActionLane R A) (g : Aˣ) {n : ℕ}
    (ω : ActionOperatorForm K n) (v : Fin n → K.L) :
    actionConjugateForm K g ω v = conjugate g (ω v) :=
  rfl

@[simp] theorem actionConjugateForm_one (K : LieActionLane R A) {n : ℕ}
    (ω : ActionOperatorForm K n) :
    actionConjugateForm K 1 ω = ω := by
  ext v
  simp [conjugate]

theorem actionConjugateForm_mul (K : LieActionLane R A) (g h : Aˣ) {n : ℕ}
    (ω : ActionOperatorForm K n) :
    actionConjugateForm K (g * h) ω =
      actionConjugateForm K g (actionConjugateForm K h ω) := by
  ext v
  simp [conjugate, mul_assoc]

@[simp] theorem actionConjugateForm_inv (K : LieActionLane R A) (g : Aˣ) {n : ℕ}
    (ω : ActionOperatorForm K n) :
    actionConjugateForm K g⁻¹ (actionConjugateForm K g ω) = ω := by
  rw [← actionConjugateForm_mul, inv_mul_cancel, actionConjugateForm_one]

@[simp] theorem actionConjugateForm_curryLeft (K : LieActionLane R A) (g : Aˣ) {n : ℕ}
    (ω : ActionOperatorForm K (n + 1)) (x : K.L) :
    (actionConjugateForm K g ω).curryLeft x =
      actionConjugateForm K g (ω.curryLeft x) := by
  ext w
  rfl

@[simp] theorem actionConjugateForm_reindexForm (K : LieActionLane R A) (g : Aˣ)
    {m n : ℕ} (h : m = n) (ω : ActionOperatorForm K m) :
    actionConjugateForm K g (reindexForm h ω) =
      reindexForm h (actionConjugateForm K g ω) := by
  subst h
  rfl

theorem actionConjugateForm_actionWedge (K : LieActionLane R A) (g : Aˣ) :
    ∀ {p q : ℕ} (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q),
      actionConjugateForm K g (actionWedge K ω η) =
        actionWedge K (actionConjugateForm K g ω) (actionConjugateForm K g η)
  | 0, q, ω, η => by
    ext v
    simp only [actionConjugateForm_apply, actionWedge_zero_left, reindexForm_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply']
    exact (conjugate_mul g (ω Fin.elim0) (η (v ∘ finCongr (Nat.zero_add q).symm))).symm
  | p' + 1, 0, ω, η => by
    ext v
    simp only [actionConjugateForm_apply, actionWedge_zero_right,
      LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, LinearMap.mul_apply']
    exact (conjugate_mul g (ω v) (η Fin.elim0)).symm
  | p' + 1, q' + 1, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    rw [actionConjugateForm_curryLeft, actionWedge_succ_succ_curryLeft, map_add, map_smul,
      actionConjugateForm_reindexForm, actionConjugateForm_actionWedge K g (ω.curryLeft x) η,
      actionConjugateForm_actionWedge K g ω (η.curryLeft x),
      actionWedge_succ_succ_curryLeft, actionConjugateForm_curryLeft, actionConjugateForm_curryLeft]

theorem actionThetaR_eq_conj_actionThetaL (K : LieActionLane R A) (g : Aˣ) :
    actionThetaR K g = actionConjugateForm K g (actionThetaL K g) := by
  ext v
  simp [conjugate]

theorem actionThetaR_eq_neg_actionThetaL_inv (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (g : Aˣ) :
    actionThetaR K g = -actionThetaL K g⁻¹ := by
  ext v
  simp only [actionThetaR_apply, AlternatingMap.neg_apply, actionThetaL_apply, inv_inv]
  rw [lieAction_operatorAction_inv_unit K hK g (v 0)]
  simp only [mul_neg, neg_neg, ← mul_assoc, Units.mul_inv, one_mul]

theorem actionThetaR_maurerCartan (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (g : Aˣ) :
    actionExteriorDerivative K 1 (actionThetaR K g) =
      actionWedge K (actionThetaR K g) (actionThetaR K g) := by
  have hflat := actionThetaL_flat K hK g⁻¹
  rw [← neg_neg (actionThetaL K g⁻¹), ← actionThetaR_eq_neg_actionThetaL_inv K hK g] at hflat
  dsimp [actionCurvature] at hflat
  rw [map_neg] at hflat
  have hww : actionWedge K (-actionThetaR K g) (-actionThetaR K g) =
      actionWedge K (actionThetaR K g) (actionThetaR K g) := by
    simp only [actionWedge, map_neg, LinearMap.neg_apply, neg_neg]
  rw [hww] at hflat
  calc
    actionExteriorDerivative K 1 (actionThetaR K g) =
        actionExteriorDerivative K 1 (actionThetaR K g) +
          (-actionExteriorDerivative K 1 (actionThetaR K g) +
            actionWedge K (actionThetaR K g) (actionThetaR K g)) := by
      rw [hflat, add_zero]
    _ = actionWedge K (actionThetaR K g) (actionThetaR K g) := by abel

private theorem lieDeriv_actionConjugateForm (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (g : Aˣ) (x : K.L) {n : ℕ}
    (ω : ActionOperatorForm K n) :
    lieDeriv K x (actionConjugateForm K g ω) =
      actionConjugateForm K g (lieDeriv K x ω) +
        ((LinearMap.mul R A (actionThetaR K g ![x])).compAlternatingMap
            (actionConjugateForm K g ω) -
          ((LinearMap.mul R A).flip (actionThetaR K g ![x])).compAlternatingMap
            (actionConjugateForm K g ω)) := by
  ext v
  simp only [lieDeriv_apply, actionConjugateForm_apply, AlternatingMap.add_apply,
    AlternatingMap.sub_apply, LinearMap.compAlternatingMap_apply, LinearMap.mul_apply',
    LinearMap.flip_apply, actionThetaR_apply, Matrix.cons_val_zero, conjugate]
  rw [hK x ((g : A) * ω v) (↑g⁻¹ : A), hK x (g : A) (ω v),
    lieAction_operatorAction_inv_unit K hK g x]
  have hsum :
      (∑ i : Fin n, (g : A) * ω (Function.update v i ⁅x, v i⁆) * (↑g⁻¹ : A)) =
        (g : A) * (∑ i : Fin n, ω (Function.update v i ⁅x, v i⁆)) * (↑g⁻¹ : A) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hsum]
  have hterm1 :
      K.operatorAction x (g : A) * ω v * (↑g⁻¹ : A) =
        (K.operatorAction x (g : A) * (↑g⁻¹ : A)) * ((g : A) * ω v * (↑g⁻¹ : A)) := by
    calc
      K.operatorAction x (g : A) * ω v * (↑g⁻¹ : A) =
          K.operatorAction x (g : A) * ((↑g⁻¹ : A) * (g : A)) * ω v * (↑g⁻¹ : A) := by
        rw [Units.inv_mul, mul_one]
      _ = (K.operatorAction x (g : A) * (↑g⁻¹ : A)) * ((g : A) * ω v * (↑g⁻¹ : A)) := by
        noncomm_ring
  have hterm2 :
      (g : A) * ω v * -((↑g⁻¹ : A) * K.operatorAction x (g : A) * (↑g⁻¹ : A)) =
        -((g : A) * ω v * (↑g⁻¹ : A) * (K.operatorAction x (g : A) * (↑g⁻¹ : A))) := by
    noncomm_ring
  rw [add_mul, hterm1, hterm2]
  noncomm_ring

/-- Fundamental differential identity for left conjugation of an arbitrary-degree form:
`d(g ω g⁻¹) = g (dω) g⁻¹ + θ_R(g) ∧ (g ω g⁻¹) - (-1)^n (g ω g⁻¹) ∧ θ_R(g)`. -/
theorem actionExteriorDerivative_actionConjugateForm (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (g : Aˣ) :
    ∀ {n : ℕ} (ω : ActionOperatorForm K n),
      actionExteriorDerivative K n (actionConjugateForm K g ω) =
        actionConjugateForm K g (actionExteriorDerivative K n ω) +
          reindexForm (Nat.add_comm 1 n)
            (actionWedge K (actionThetaR K g) (actionConjugateForm K g ω)) -
          ((-1 : R) ^ n) •
            actionWedge K (actionConjugateForm K g ω) (actionThetaR K g)
  | 0, ω => by
    apply alternating_ext_curryLeft
    intro x
    rw [actionExteriorDerivative_zero_curryLeft, lieDeriv_actionConjugateForm K hK g x ω,
      curryLeft_sub_helper, AlternatingMap.curryLeft_add, LinearMap.add_apply,
      actionConjugateForm_curryLeft, actionExteriorDerivative_zero_curryLeft,
      reindexForm_curryLeft, AlternatingMap.curryLeft_smul, LinearMap.smul_apply]
    ext w
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst hw
    simp only [AlternatingMap.add_apply, AlternatingMap.sub_apply,
      reindexForm_apply, AlternatingMap.curryLeft_apply_apply, pow_zero, one_smul]
    have hL :
        actionWedge K (actionThetaR K g) (actionConjugateForm K g ω)
            (Matrix.vecCons x (Fin.elim0 ∘ finCongr (Nat.succ.inj (Nat.add_comm 1 0)))) =
          actionThetaR K g ![x] * actionConjugateForm K g ω Fin.elim0 := by
      rw [actionWedge_succ_zero]
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, LinearMap.mul_apply']
      congr 2
    have hR :
        actionWedge K (actionConjugateForm K g ω) (actionThetaR K g) (Matrix.vecCons x Fin.elim0) =
          actionConjugateForm K g ω Fin.elim0 * actionThetaR K g ![x] := by
      rw [actionWedge_zero_left]
      simp only [reindexForm_apply, LinearMap.compAlternatingMap_apply, LinearMap.mul_apply']
      congr 2
    rw [hL, hR]
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.mul_apply', LinearMap.flip_apply]
    abel
  | m + 1, ω => by
    apply alternating_ext_curryLeft
    intro x
    rw [actionExteriorDerivative_succ_curryLeft, lieDeriv_actionConjugateForm K hK g x ω,
      actionConjugateForm_curryLeft,
      actionExteriorDerivative_actionConjugateForm K hK g (ω.curryLeft x),
      curryLeft_sub_helper, AlternatingMap.curryLeft_add, LinearMap.add_apply,
      actionConjugateForm_curryLeft, actionExteriorDerivative_succ_curryLeft, map_sub,
      reindexForm_curryLeft, actionWedge_succ_succ_curryLeft,
      AlternatingMap.curryLeft_smul, LinearMap.smul_apply, actionWedge_succ_succ_curryLeft]
    simp only [reindexForm_add, reindexForm_smul, reindexForm_trans, smul_add, smul_smul]
    have hsq : (-1 : R) ^ (m + 1) * (-1 : R) ^ (m + 1) = 1 := by
      rw [← mul_pow]
      have hneg1 : (-1 : R) * -1 = 1 := by ring
      simp [hneg1]
    have hsucc : (-1 : R) ^ (m + 1) = -((-1 : R) ^ m) := by
      rw [pow_succ]
      ring
    ext w
    simp only [AlternatingMap.add_apply, AlternatingMap.sub_apply, AlternatingMap.smul_apply,
      reindexForm_apply, actionWedge_zero_left, actionWedge_zero_right,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply', LinearMap.flip_apply,
      AlternatingMap.curryLeft_apply_apply]
    have hxL : Matrix.vecCons x ((w ∘ finCongr (by omega : 0 + (m + 1) = m + 1)) 0 |> fun _ => Fin.elim0) =
        ![x] := by
      ext i
      fin_cases i
      rfl
    have hvec1 : Matrix.vecCons x (Fin.elim0 : Fin 0 → K.L) = ![x] := rfl
    have hwL : (w ∘ finCongr (by omega : 0 + (m + 1) = m + 1)) ∘
        finCongr (Nat.zero_add (m + 1)).symm = w := by
      funext i
      exact congrArg w (Fin.ext rfl)
    have hw1 :
        actionWedge K (actionThetaR K g) (actionConjugateForm K g (ω.curryLeft x))
            (w ∘ finCongr (Nat.succ.inj (Nat.add_comm 1 (m + 1)))) =
          actionWedge K (actionThetaR K g) (actionConjugateForm K g (ω.curryLeft x))
            (w ∘ finCongr (Nat.add_comm 1 m)) := rfl
    have hw2 :
        actionWedge K (actionConjugateForm K g (ω.curryLeft x)) (actionThetaR K g)
            (w ∘ finCongr (by omega : m + 1 + 0 = m + 1)) =
          actionWedge K (actionConjugateForm K g (ω.curryLeft x)) (actionThetaR K g) w := rfl
    rw [hvec1, actionConjugateForm_curryLeft]
    have hLcongr :
        ((actionConjugateForm K g) ω)
            ((w ∘ finCongr (by omega : 0 + (m + 1) = m + 1)) ∘
              finCongr (Nat.zero_add (m + 1)).symm) =
          ((actionConjugateForm K g) ω) w :=
      congrArg (actionConjugateForm K g ω) hwL
    rw [hLcongr, hw1, hw2]
    have hsm1 :
        ((-1 : R) ^ (m + 1) * (-1 : R) ^ (m + 1)) •
            (((actionConjugateForm K g) ω) w * (actionThetaR K g) ![x]) =
          ((actionConjugateForm K g) ω) w * (actionThetaR K g) ![x] := by
      rw [hsq, one_smul]
    have hsm0 : ((-1 : R) ^ (0 + 1)) = (-1 : R) := by ring
    have hsm2 :
        (-1 : R) ^ (m + 1) •
            actionWedge K (actionConjugateForm K g (ω.curryLeft x)) (actionThetaR K g) w =
          -((-1 : R) ^ m •
            actionWedge K (actionConjugateForm K g (ω.curryLeft x)) (actionThetaR K g) w) := by
      rw [hsucc, neg_smul]
    rw [hsm1, hsm0, neg_one_smul, hsm2]
    abel

/-- Left gauge transformation on `ActionOperatorForm K 1`:
`g · Γ = g Γ g⁻¹ - θ_R(g)`. -/
def actionGaugeOneForm (K : LieActionLane R A)
    (Γ : ActionOperatorForm K 1) (u : Aˣ) : ActionOperatorForm K 1 :=
  actionConjugateForm K u Γ - actionThetaR K u

@[simp] theorem actionGaugeOneForm_apply (K : LieActionLane R A)
    (Γ : ActionOperatorForm K 1) (u : Aˣ) (v : Fin 1 → K.L) :
    actionGaugeOneForm K Γ u v =
      (u : A) * Γ v * (↑u⁻¹ : A) - K.operatorAction (v 0) (u : A) * (↑u⁻¹ : A) :=
  rfl

theorem actionGaugeOneForm_eq_add_actionThetaL_inv (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (Γ : ActionOperatorForm K 1) (u : Aˣ) :
    actionGaugeOneForm K Γ u = actionConjugateForm K u Γ + actionThetaL K u⁻¹ := by
  rw [actionGaugeOneForm, actionThetaR_eq_neg_actionThetaL_inv K hK u, sub_neg_eq_add]

@[simp] theorem actionGaugeOneForm_one (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (Γ : ActionOperatorForm K 1) :
    actionGaugeOneForm K Γ 1 = Γ := by
  ext v
  simp only [actionGaugeOneForm_apply, inv_one, Units.val_one, one_mul, mul_one]
  rw [show K.operatorAction (v 0) (1 : A) = 0 from lieAction_operatorAction_one K hK (v 0)]
  simp

theorem actionGaugeOneForm_mul (K : LieActionLane R A) (hK : IsLeibnizAction K)
    (Γ : ActionOperatorForm K 1) (u v : Aˣ) :
    actionGaugeOneForm K (actionGaugeOneForm K Γ v) u =
      actionGaugeOneForm K Γ (u * v) := by
  ext w
  simp only [actionGaugeOneForm_apply, Units.val_mul, mul_inv_rev,
    hK (w 0) (u : A) (v : A), mul_sub, sub_mul, add_mul, mul_assoc,
    Units.mul_inv_cancel_left]
  abel

@[simp] theorem actionGaugeOneForm_inv (K : LieActionLane R A) (hK : IsLeibnizAction K)
    (Γ : ActionOperatorForm K 1) (u : Aˣ) :
    actionGaugeOneForm K (actionGaugeOneForm K Γ u) u⁻¹ = Γ := by
  rw [actionGaugeOneForm_mul K hK, inv_mul_cancel, actionGaugeOneForm_one K hK]

theorem actionGaugeOneForm_zero (K : LieActionLane R A) (hK : IsLeibnizAction K) (u : Aˣ) :
    actionGaugeOneForm K 0 u = actionThetaL K u⁻¹ := by
  rw [actionGaugeOneForm_eq_add_actionThetaL_inv K hK, map_zero, zero_add]

/-- Arbitrary-degree covariant exterior derivative equivariance on any `LieActionLane R A`
satisfying `IsLeibnizAction K`: `d_{u · Γ}(u ω u⁻¹) = u (d_Γ ω) u⁻¹`. -/
theorem actionCovariantExteriorDerivativeN_actionGaugeOneForm (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (Γ : ActionOperatorForm K 1) (u : Aˣ) (n : ℕ)
    (ω : ActionOperatorForm K n) :
    actionCovariantExteriorDerivativeN K (actionGaugeOneForm K Γ u) n
        (actionConjugateForm K u ω) =
      actionConjugateForm K u (actionCovariantExteriorDerivativeN K Γ n ω) := by
  dsimp [actionCovariantExteriorDerivativeN, actionGaugeOneForm]
  rw [actionExteriorDerivative_actionConjugateForm K hK u ω,
    actionWedge_sub_left, actionWedge_sub_right,
    ← actionConjugateForm_actionWedge, ← actionConjugateForm_actionWedge,
    reindexForm_sub, smul_sub,
    map_sub, map_add, actionConjugateForm_reindexForm, map_smul]
  abel

/-- Curvature equivariance on any `LieActionLane R A` with `IsLeibnizAction K`:
`F(u · Γ) = u F(Γ) u⁻¹`. -/
theorem actionCurvature_actionGaugeOneForm (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (Γ : ActionOperatorForm K 1) (u : Aˣ) :
    actionCurvature K (actionGaugeOneForm K Γ u) =
      actionConjugateForm K u (actionCurvature K Γ) := by
  dsimp [actionCurvature, actionGaugeOneForm]
  rw [map_sub, actionExteriorDerivative_actionConjugateForm K hK u Γ,
    actionThetaR_maurerCartan K hK u,
    actionWedge_sub_left, actionWedge_sub_right, actionWedge_sub_right,
    ← actionConjugateForm_actionWedge, map_add]
  have hr :
      reindexForm (Nat.add_comm 1 1)
          (actionWedge K (actionThetaR K u) (actionConjugateForm K u Γ)) =
        actionWedge K (actionThetaR K u) (actionConjugateForm K u Γ) := by
    ext v; rfl
  have hneg :
      ((-1 : R) ^ (1 : ℕ)) •
          actionWedge K (actionConjugateForm K u Γ) (actionThetaR K u) =
        -actionWedge K (actionConjugateForm K u Γ) (actionThetaR K u) := by
    rw [pow_one]
    exact neg_one_smul R (actionWedge K (actionConjugateForm K u Γ) (actionThetaR K u))
  rw [hr, hneg]
  abel

theorem actionCurvature_actionGaugeOneForm_eq_zero_iff (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (Γ : ActionOperatorForm K 1) (u : Aˣ) :
    actionCurvature K (actionGaugeOneForm K Γ u) = 0 ↔ actionCurvature K Γ = 0 := by
  rw [actionCurvature_actionGaugeOneForm K hK]
  constructor
  · intro h
    have h' := congrArg (actionConjugateForm K u⁻¹) h
    simpa using h'
  · intro h
    rw [h, map_zero]

theorem actionCurvature_bianchi_actionGaugeOneForm (K : LieActionLane R A)
    (hK : IsLeibnizAction K) (Γ : ActionOperatorForm K 1) (u : Aˣ) :
    actionCovariantExteriorDerivativeN K (actionGaugeOneForm K Γ u) 2
        (actionCurvature K (actionGaugeOneForm K Γ u)) = 0 :=
  actionCurvature_bianchi K hK (actionGaugeOneForm K Γ u)

end GeneralLieActionCalculus

/-! ## Section 1B: Canonical Maurer--Cartan Sign Dictionary, Bridges & Left/Right Gauge Covariance -/

section CanonicalSignDictionary

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- Canonical left-logarithmic Maurer--Cartan 1-form `θ_L(g)(x) = g⁻¹ * D_x(g)`
in `DerivationOperatorForm K 1`. -/
def thetaL (g : Aˣ) : DerivationOperatorForm K 1 :=
  oneFormAlternatingLinearEquiv K (gaugeForm K g)

/-- Right-logarithmic Maurer--Cartan 1-form `θ_R(g)(x) = D_x(g) * g⁻¹`
in `DerivationOperatorForm K 1`. -/
def thetaR (g : Aˣ) : DerivationOperatorForm K 1 :=
  oneFormAlternatingLinearEquiv K (rightLogarithmicOneForm K g)

@[simp] theorem thetaL_apply (g : Aˣ) (v : Fin 1 → K.L) :
    thetaL K g v = (↑g⁻¹ : A) * K.operatorAction (v 0) (g : A) :=
  rfl

@[simp] theorem thetaR_apply (g : Aˣ) (v : Fin 1 → K.L) :
    thetaR K g v = K.operatorAction (v 0) (g : A) * (↑g⁻¹ : A) :=
  rfl

@[simp] theorem thetaL_one : thetaL K (1 : Aˣ) = 0 := by
  ext v
  simp [action_one K]

@[simp] theorem thetaR_one : thetaR K (1 : Aˣ) = 0 := by
  ext v
  simp [action_one K]

@[simp] theorem actionThetaL_toLieActionLane (g : Aˣ) :
    actionThetaL K.toLieActionLane g = thetaL K g := by
  ext v
  rfl

@[simp] theorem actionThetaR_toLieActionLane (g : Aˣ) :
    actionThetaR K.toLieActionLane g = thetaR K g := by
  ext v
  rfl

@[simp] theorem thetaL_eq_gaugeForm (g : Aˣ) :
    (oneFormAlternatingLinearEquiv K).symm (thetaL K g) = gaugeForm K g :=
  rfl

@[simp] theorem thetaR_eq_rightLogarithmicOneForm (g : Aˣ) :
    (oneFormAlternatingLinearEquiv K).symm (thetaR K g) = rightLogarithmicOneForm K g :=
  rfl

theorem oneFormAlternatingLinearEquiv_gaugeForm (g : Aˣ) :
    oneFormAlternatingLinearEquiv K (gaugeForm K g) = thetaL K g :=
  rfl

theorem oneFormAlternatingLinearEquiv_rightLogarithmicOneForm (g : Aˣ) :
    oneFormAlternatingLinearEquiv K (rightLogarithmicOneForm K g) = thetaR K g :=
  rfl

/-- Canonical Maurer--Cartan flatness: `ceCurvature K (thetaL K g) = 0`. -/
theorem thetaL_flat (g : Aˣ) : ceCurvature K (thetaL K g) = 0 := by
  rw [thetaL, ceCurvature_eq, gaugeForm_flat, map_zero]

/-- Expanded canonical Maurer--Cartan equation: `d θ_L + θ_L ∧ θ_L = 0`. -/
theorem thetaL_maurerCartan (g : Aˣ) :
    ceExteriorDerivative K 1 (thetaL K g) + ceWedge K (thetaL K g) (thetaL K g) = 0 := by
  simpa [ceCurvature] using thetaL_flat K g

/-- Right-logarithmic Maurer--Cartan equation: `d θ_R = θ_R ∧ θ_R`. -/
theorem thetaR_maurerCartan (g : Aˣ) :
    ceExteriorDerivative K 1 (thetaR K g) = ceWedge K (thetaR K g) (thetaR K g) := by
  rw [thetaR, ceExteriorDerivative_one_eq, rightLogarithmicOneForm_maurerCartan,
    ← ceWedge_one_one_eq_connectionWedgeSquare]

/-- `R`-algebra conjugation equivalence `x ↦ g * x * g⁻¹`. -/
def conjugateAlgEquiv (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (g : Aˣ) : A ≃ₐ[R] A where
  toFun := conjugate g
  invFun := conjugate g⁻¹
  left_inv x := by simp [conjugate, mul_assoc]
  right_inv x := by simp [conjugate, mul_assoc]
  map_mul' x y := (conjugate_mul g x y).symm
  map_add' x y := by simp [conjugate, mul_add, add_mul]
  commutes' r := by simp [conjugate, Algebra.commutes, mul_assoc]

/-- Left conjugation `(g · ω)(v) = g * ω(v) * g⁻¹` on `DerivationOperatorForm K n`. -/
def conjugateForm (g : Aˣ) {n : ℕ} :
    DerivationOperatorForm K n ≃ₗ[R] DerivationOperatorForm K n :=
  actionConjugateForm K.toLieActionLane g

@[simp] theorem conjugateForm_apply (g : Aˣ) {n : ℕ}
    (ω : DerivationOperatorForm K n) (v : Fin n → K.L) :
    conjugateForm K g ω v = conjugate g (ω v) :=
  rfl

@[simp] theorem conjugateForm_one {n : ℕ} (ω : DerivationOperatorForm K n) :
    conjugateForm K 1 ω = ω :=
  actionConjugateForm_one K.toLieActionLane ω

theorem conjugateForm_mul (g h : Aˣ) {n : ℕ} (ω : DerivationOperatorForm K n) :
    conjugateForm K (g * h) ω = conjugateForm K g (conjugateForm K h ω) :=
  actionConjugateForm_mul K.toLieActionLane g h ω

@[simp] theorem conjugateForm_inv (g : Aˣ) {n : ℕ} (ω : DerivationOperatorForm K n) :
    conjugateForm K g⁻¹ (conjugateForm K g ω) = ω :=
  actionConjugateForm_inv K.toLieActionLane g ω

theorem conjugateForm_ceWedge (g : Aˣ) {p q : ℕ}
    (ω : DerivationOperatorForm K p) (η : DerivationOperatorForm K q) :
    conjugateForm K g (ceWedge K ω η) =
      ceWedge K (conjugateForm K g ω) (conjugateForm K g η) :=
  actionConjugateForm_actionWedge K.toLieActionLane g ω η

/-- Sign dictionary (1): `θ_R(g) = g · θ_L(g) · g⁻¹`. -/
theorem thetaR_eq_conj_thetaL (g : Aˣ) :
    thetaR K g = conjugateForm K g (thetaL K g) :=
  actionThetaR_eq_conj_actionThetaL K.toLieActionLane g

/-- Sign dictionary (2): `θ_R(g) = -θ_L(g⁻¹)`. -/
theorem thetaR_eq_neg_thetaL_inv (g : Aˣ) :
    thetaR K g = -thetaL K g⁻¹ := by
  ext v
  exact AlternatingMap.congr_fun
    (actionThetaR_eq_neg_actionThetaL_inv K.toLieActionLane K.isLeibnizAction g) v

theorem thetaL_inv_eq_neg_thetaR (g : Aˣ) :
    thetaL K g⁻¹ = -thetaR K g := by
  rw [thetaR_eq_neg_thetaL_inv, neg_neg]

/-- Sign dictionary (3a): `gaugeOneForm K 0 g = gaugeForm K g⁻¹` on `OneForm K`. -/
theorem gaugeOneForm_zero_eq_thetaL_inv_oneForm (g : Aˣ) :
    gaugeOneForm K (0 : OneForm K) g = gaugeForm K g⁻¹ := by
  rw [gaugeOneForm_zero_eq_neg_rightLogarithmicOneForm]
  ext x
  simp only [LinearMap.neg_apply, rightLogarithmicOneForm_apply, gaugeForm_apply, inv_inv]
  rw [action_inverse K x g]
  simp only [mul_neg, ← mul_assoc, Units.mul_inv, one_mul]

/-- Sign dictionary (3b): `oneFormAlternatingLinearEquiv K (gaugeOneForm K 0 g) = thetaL K g⁻¹`. -/
theorem gaugeOneForm_zero_eq_thetaL_inv (g : Aˣ) :
    oneFormAlternatingLinearEquiv K (gaugeOneForm K (0 : OneForm K) g) = thetaL K g⁻¹ := by
  rw [gaugeOneForm_zero_eq_thetaL_inv_oneForm]
  rfl

/-- Sign dictionary (4a): `NCG.AlgebraDerivation.pureGaugeForm D g = θ_L(g⁻¹)(D)`. -/
theorem pureGaugeForm_eq_thetaL_inv
    (D : InfoGeometry.NCG.AlgebraDerivation R A) (g : Aˣ) :
    InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D g =
      thetaL (fullDerivationLieLane R A) g⁻¹ ![algebraDerivationToDerivations D] :=
  rfl

/-- Bundle any direction `x : K.L` of an arbitrary `DerivationLieLane R A` as an
`NCG.AlgebraDerivation R A`. -/
def algDerivOfLane (x : K.L) : InfoGeometry.NCG.AlgebraDerivation R A where
  toLinearMap := K.operatorAction x
  leibniz' := K.operatorAction_leibniz x

/-- Sign dictionary (4b): `pureGaugeForm` along an arbitrary lane direction `x : K.L`. -/
theorem pureGaugeForm_lane_eq_thetaL_inv (x : K.L) (g : Aˣ) :
    InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm (algDerivOfLane K x) g =
      thetaL K g⁻¹ ![x] :=
  rfl

end CanonicalSignDictionary

section NoncommPureGaugeBridge

/-- Sign dictionary (4c): over any possibly noncommutative scalar ring `[Ring R]`,
`NCG.AlgebraDerivation.pureGaugeForm D g` agrees with `θ_L(g⁻¹)` on `fullDerivationLieLane ℤ A`
via `ncDerivationEquivDerivations (algebraDerivationToNCDerivation D)`. -/
theorem pureGaugeForm_nc_eq_thetaL_inv
    {R A : Type*} [Ring R] [Ring A] [Module R A]
    (D : InfoGeometry.NCG.AlgebraDerivation R A) (g : Aˣ) :
    InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D g =
      thetaL (fullDerivationLieLane ℤ A) g⁻¹
        ![ncDerivationEquivDerivations (algebraDerivationToNCDerivation D)] := by
  rfl

end NoncommPureGaugeBridge

section CompatibilityBridges

/-- Compatibility with `OperatorAlgebra.MatrixMaurerCartan.maurerCartan`:
`maurerCartan G H = θ_L(G)(ad_H)` on `matrixDerivationsLane ℂ n`. -/
theorem matrixMaurerCartan_eq_thetaL {n : Type*} [Fintype n] [DecidableEq n]
    (G : (Matrix n n ℂ)ˣ) (H : Matrix n n ℂ) :
    InfoGeometry.OperatorAlgebra.MatrixMaurerCartan.maurerCartan G H =
      thetaL (DerivationMatrixGeometry.matrixDerivationsLane ℂ n) G
        ![DerivationMatrixGeometry.matrixInnerLieHom ℂ n H] := by
  rw [InfoGeometry.OperatorAlgebra.MatrixMaurerCartan.maurerCartan_apply, thetaL_apply]
  rfl

/-- Compatibility with `NoncommutativeMaurerCartanAdjointBridge.maurerCartanForm`:
`maurerCartanForm G Ginv H = θ_L(⟨G, Ginv, ...⟩)(adCLM H)`. -/
theorem adjointBridge_maurerCartanForm_eq_thetaL {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {G Ginv : A}
    (hG : InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge.IsInvertiblePair
      G Ginv)
    (H : A) :
    InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge.maurerCartanForm
        G Ginv H =
      thetaL (fullDerivationLieLane ℝ A) ⟨G, Ginv, hG.mul_inv, hG.inv_mul⟩
        ![⟨(InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge.adCLM
            H).toLinearMap,
          InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge.adCLM_leibniz
            H⟩] :=
  rfl

/-- Compatibility with `Optics.DerivationBackedMaurerCartanFrame.fromDirectionalDerivation`:
the local frame's `.theta p X` equals `θ_R(u p)(D p X)`. -/
theorem directionalDerivation_theta_eq_thetaR
    {R Point Tangent A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : InfoGeometry.Optics.DerivationBackedMaurerCartanFrame.DirectionalDerivation
      (R := R) (Point := Point) (Tangent := Tangent) (A := A))
    (u : Point → Aˣ) (p : Point) (X : Tangent) :
    (InfoGeometry.Optics.DerivationBackedMaurerCartanFrame.fromDirectionalDerivation D u).theta
        p X =
      thetaR (fullDerivationLieLane R A) (u p) ![algebraDerivationToDerivations (D p X)] :=
  rfl

/-- Compatibility with `Optics.DerivationBackedMaurerCartanFrame.fromDirectionalDerivation`
in the canonical `θ_L` convention: `.theta p X = -θ_L((u p)⁻¹)(D p X)`. -/
theorem directionalDerivation_theta_eq_neg_thetaL_inv
    {R Point Tangent A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : InfoGeometry.Optics.DerivationBackedMaurerCartanFrame.DirectionalDerivation
      (R := R) (Point := Point) (Tangent := Tangent) (A := A))
    (u : Point → Aˣ) (p : Point) (X : Tangent) :
    (InfoGeometry.Optics.DerivationBackedMaurerCartanFrame.fromDirectionalDerivation D u).theta
        p X =
      -thetaL (fullDerivationLieLane R A) (u p)⁻¹
        ![algebraDerivationToDerivations (D p X)] := by
  rw [directionalDerivation_theta_eq_thetaR, thetaR_eq_neg_thetaL_inv]
  rfl

/-- **Semantic disambiguation of `Canonical.MaurerCartanFactorization.maurerCartanForm`**:
Unlike `thetaL K g : DerivationOperatorForm K 1` (a unit-valued logarithmic 1-form
`g⁻¹ * D(g)`), `Canonical.MaurerCartanFactorization.maurerCartanForm D` is an endomorphism
on the outer-derivation quotient `Out(A) = Der(A) / Inn(A)` induced by commutator descent
`π(X) ↦ π([D, X])` in `modularDerivationsLane A` modulo `modularInnerIdeal A`. -/
theorem outer_maurerCartanForm_commutator_disambiguation {A : Type*} [Ring A]
    (D X : InfoGeometry.Modular.ExactSequence.Derivation A) :
    InfoGeometry.Canonical.MaurerCartanFactorization.maurerCartanForm D
        (InfoGeometry.Canonical.MaurerCartanFactorization.modularFlowProjection X) =
      InfoGeometry.Canonical.MaurerCartanFactorization.modularFlowProjection
        (modularDerivationToDerivations.symm
          ⁅modularDerivationToDerivations D, modularDerivationToDerivations X⁆) := by
  rw [← InfoGeometry.Canonical.MaurerCartanFactorization.logarithmicBridgeFactorsThroughMaurerCartan]
  rw [← modularDerivationToDerivations_commutator]
  rw [AddEquiv.symm_apply_apply]

end CompatibilityBridges

section LeftAndRightGaugeCovariance

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- **Left** gauge action on `DerivationOperatorForm K 1`:
`gaugeTransformOneForm K g Γ = g Γ g⁻¹ - θ_R(g)`. -/
def gaugeTransformOneForm (g : Aˣ) (Γ : DerivationOperatorForm K 1) :
    DerivationOperatorForm K 1 :=
  conjugateForm K g Γ - thetaR K g

@[simp] theorem gaugeTransformOneForm_apply (g : Aˣ) (Γ : DerivationOperatorForm K 1)
    (v : Fin 1 → K.L) :
    gaugeTransformOneForm K g Γ v =
      (g : A) * Γ v * (↑g⁻¹ : A) - K.operatorAction (v 0) (g : A) * (↑g⁻¹ : A) :=
  rfl

@[simp] theorem actionGaugeOneForm_toLieActionLane (Γ : DerivationOperatorForm K 1) (g : Aˣ) :
    actionGaugeOneForm K.toLieActionLane Γ g = gaugeTransformOneForm K g Γ :=
  rfl

theorem gaugeTransformOneForm_eq_add_thetaL_inv (g : Aˣ) (Γ : DerivationOperatorForm K 1) :
    gaugeTransformOneForm K g Γ = conjugateForm K g Γ + thetaL K g⁻¹ := by
  rw [gaugeTransformOneForm, thetaR_eq_neg_thetaL_inv, sub_neg_eq_add]

theorem gaugeTransformOneForm_eq_gaugeOneForm (g : Aˣ) (Γ : DerivationOperatorForm K 1) :
    gaugeTransformOneForm K g Γ =
      oneFormAlternatingLinearEquiv K
        (gaugeOneForm K ((oneFormAlternatingLinearEquiv K).symm Γ) g) := by
  ext v
  simp [gaugeTransformOneForm_apply, gaugeOneForm_apply, oneFormAlternatingLinearEquiv_symm_apply]
  congr 2
  ext i
  fin_cases i
  rfl

@[simp] theorem gaugeTransformOneForm_one (Γ : DerivationOperatorForm K 1) :
    gaugeTransformOneForm K 1 Γ = Γ :=
  actionGaugeOneForm_one K.toLieActionLane K.isLeibnizAction Γ

theorem gaugeTransformOneForm_mul (g h : Aˣ) (Γ : DerivationOperatorForm K 1) :
    gaugeTransformOneForm K g (gaugeTransformOneForm K h Γ) =
      gaugeTransformOneForm K (g * h) Γ :=
  actionGaugeOneForm_mul K.toLieActionLane K.isLeibnizAction Γ g h

@[simp] theorem gaugeTransformOneForm_inv (g : Aˣ) (Γ : DerivationOperatorForm K 1) :
    gaugeTransformOneForm K g⁻¹ (gaugeTransformOneForm K g Γ) = Γ :=
  actionGaugeOneForm_inv K.toLieActionLane K.isLeibnizAction Γ g

@[simp] theorem gaugeTransformOneForm_zero (g : Aˣ) :
    gaugeTransformOneForm K g 0 = thetaL K g⁻¹ :=
  actionGaugeOneForm_zero K.toLieActionLane K.isLeibnizAction g

theorem covariantDerivative_gaugeTransformOneForm (g : Aˣ)
    (Γ : DerivationOperatorForm K 1) (x : K.L) (a : A) :
    covariantDerivative K ((oneFormAlternatingLinearEquiv K).symm (gaugeTransformOneForm K g Γ))
        x (conjugate g a) =
      conjugate g (covariantDerivative K ((oneFormAlternatingLinearEquiv K).symm Γ) x a) := by
  rw [gaugeTransformOneForm_eq_gaugeOneForm, LinearEquiv.symm_apply_apply]
  exact covariantDerivative_gaugeOneForm K ((oneFormAlternatingLinearEquiv K).symm Γ) g x a

theorem fundamentalCovariantDerivative_gaugeTransformOneForm (g : Aˣ)
    (Γ : DerivationOperatorForm K 1) (x : K.L) (a : A) :
    fundamentalCovariantDerivative K
        ((oneFormAlternatingLinearEquiv K).symm (gaugeTransformOneForm K g Γ)) x ((g : A) * a) =
      (g : A) * fundamentalCovariantDerivative K
        ((oneFormAlternatingLinearEquiv K).symm Γ) x a := by
  rw [gaugeTransformOneForm_eq_gaugeOneForm, LinearEquiv.symm_apply_apply]
  exact fundamentalCovariantDerivative_gauge_intertwine K
    ((oneFormAlternatingLinearEquiv K).symm Γ) g x a

theorem algDeriv_covariantDerivative_gaugeTransformOneForm (g : Aˣ)
    (Γ : DerivationOperatorForm K 1) (x : K.L) (a : A) :
    InfoGeometry.NCG.AlgebraDerivation.covariantDerivative (algDerivOfLane K x)
        (gaugeTransformOneForm K g Γ ![x]) (conjugate g a) =
      conjugate g (InfoGeometry.NCG.AlgebraDerivation.covariantDerivative (algDerivOfLane K x)
        (Γ ![x]) a) := by
  have harg : (![x] : Fin 1 → K.L) = fun _ => x := funext fun i => by fin_cases i; rfl
  simp only [InfoGeometry.NCG.AlgebraDerivation.covariantDerivative, algDerivOfLane]
  rw [harg]
  simpa only [DerivationDifferentialForms.covariantDerivative,
    oneFormAlternatingLinearEquiv_symm_apply, add_sub_assoc] using
    covariantDerivative_gaugeTransformOneForm K g Γ x a

/-- Curvature covariance under the left gauge action: `F(g · Γ) = g F(Γ) g⁻¹`. -/
theorem ceCurvature_gaugeTransformOneForm (g : Aˣ) (Γ : DerivationOperatorForm K 1) :
    ceCurvature K (gaugeTransformOneForm K g Γ) = conjugateForm K g (ceCurvature K Γ) :=
  actionCurvature_actionGaugeOneForm K.toLieActionLane K.isLeibnizAction Γ g

/-- Arbitrary-degree covariant exterior derivative equivariance under the left gauge action:
`d_{g · Γ}(g ω g⁻¹) = g (d_Γ ω) g⁻¹`. -/
theorem covariantExteriorDerivativeN_gaugeTransformOneForm (g : Aˣ)
    (Γ : DerivationOperatorForm K 1) (n : ℕ) (ω : DerivationOperatorForm K n) :
    covariantExteriorDerivativeN K (gaugeTransformOneForm K g Γ) n (conjugateForm K g ω) =
      conjugateForm K g (covariantExteriorDerivativeN K Γ n ω) :=
  actionCovariantExteriorDerivativeN_actionGaugeOneForm K.toLieActionLane K.isLeibnizAction
    Γ g n ω

/-- Bianchi identity in any gauge-transformed connection. -/
theorem ceCurvature_bianchi_gaugeTransform (g : Aˣ) (Γ : DerivationOperatorForm K 1) :
    covariantExteriorDerivativeN K (gaugeTransformOneForm K g Γ) 2
        (ceCurvature K (gaugeTransformOneForm K g Γ)) = 0 :=
  ceCurvature_bianchi K (gaugeTransformOneForm K g Γ)

theorem ceCurvature_bianchi_gaugeTransform_equivariant (g : Aˣ)
    (Γ : DerivationOperatorForm K 1) :
    covariantExteriorDerivativeN K (gaugeTransformOneForm K g Γ) 2
        (ceCurvature K (gaugeTransformOneForm K g Γ)) =
      conjugateForm K g (covariantExteriorDerivativeN K Γ 2 (ceCurvature K Γ)) := by
  rw [ceCurvature_gaugeTransformOneForm, covariantExteriorDerivativeN_gaugeTransformOneForm]

/-- **Right** gauge action on `DerivationOperatorForm K 1`, matching
`MaurerCartanFrameTransport.frameTransport g a = g⁻¹ * a * g`:
`rightGaugeTransformOneForm K Γ g = g⁻¹ Γ g + θ_L(g)`. -/
def rightGaugeTransformOneForm (Γ : DerivationOperatorForm K 1) (g : Aˣ) :
    DerivationOperatorForm K 1 :=
  gaugeTransformOneForm K g⁻¹ Γ

@[simp] theorem rightGaugeTransformOneForm_apply (Γ : DerivationOperatorForm K 1)
    (g : Aˣ) (x : K.L) :
    rightGaugeTransformOneForm K Γ g ![x] = frameTransport g (Γ ![x]) + thetaL K g ![x] := by
  simp [rightGaugeTransformOneForm, gaugeTransformOneForm_eq_add_thetaL_inv, frameTransport,
    conjugate, add_comm]

@[simp] theorem rightGaugeTransformOneForm_one (Γ : DerivationOperatorForm K 1) :
    rightGaugeTransformOneForm K Γ 1 = Γ := by
  simp [rightGaugeTransformOneForm]

@[simp] theorem rightGaugeTransformOneForm_zero (g : Aˣ) :
    rightGaugeTransformOneForm K 0 g = thetaL K g := by
  simp [rightGaugeTransformOneForm]

/-- Right group action law: `(Γ · g) · h = Γ · (g * h)`. -/
theorem rightGaugeTransformOneForm_mul (Γ : DerivationOperatorForm K 1) (g h : Aˣ) :
    rightGaugeTransformOneForm K (rightGaugeTransformOneForm K Γ g) h =
      rightGaugeTransformOneForm K Γ (g * h) := by
  simp only [rightGaugeTransformOneForm, gaugeTransformOneForm_mul, mul_inv_rev]

/-- Curvature covariance under the right gauge action: `F(Γ · g) = g⁻¹ F(Γ) g`. -/
theorem ceCurvature_rightGaugeTransformOneForm (Γ : DerivationOperatorForm K 1) (g : Aˣ) :
    ceCurvature K (rightGaugeTransformOneForm K Γ g) =
      conjugateForm K g⁻¹ (ceCurvature K Γ) :=
  ceCurvature_gaugeTransformOneForm K g⁻¹ Γ

/-- Arbitrary-degree covariant exterior derivative equivariance under the right gauge action:
`d_{Γ · g}(g⁻¹ ω g) = g⁻¹ (d_Γ ω) g`, specializing at `Γ = 0, n = 0` to
`MaurerCartanFrameTransport.covariant_frameTransport`. -/
theorem covariantExteriorDerivativeN_rightGaugeTransformOneForm
    (Γ : DerivationOperatorForm K 1) (g : Aˣ) (n : ℕ) (ω : DerivationOperatorForm K n) :
    covariantExteriorDerivativeN K (rightGaugeTransformOneForm K Γ g) n
        (conjugateForm K g⁻¹ ω) =
      conjugateForm K g⁻¹ (covariantExteriorDerivativeN K Γ n ω) :=
  covariantExteriorDerivativeN_gaugeTransformOneForm K g⁻¹ Γ n ω

end LeftAndRightGaugeCovariance

/-! ## Section 2: Unified `MaurerCartanStage`, `MaurerCartanStageHom`, and `MaurerCartanTower` -/

section UnifiedMaurerCartanTower

universe uR uA uL

/-- A stage in a multi-stage Maurer--Cartan tower over scalar ring `R`:
an associative ring `A` with compatible `R`-module structure and a Leibniz
Lie-action lane `lane : LieActionLane R A` (not required to be faithful). -/
structure MaurerCartanStage (R : Type uR) [CommRing R] where
  A : Type uA
  [ring : Ring A]
  [module : Module R A]
  [isScalarTower : IsScalarTower R A A]
  [smulCommClass : SMulCommClass R A A]
  lane : LieActionLane.{uR, uA, uL} R A
  isLeibniz : IsLeibnizAction lane

attribute [instance]
  MaurerCartanStage.ring
  MaurerCartanStage.module
  MaurerCartanStage.isScalarTower
  MaurerCartanStage.smulCommClass

namespace MaurerCartanStage

variable {R : Type uR} [CommRing R]

abbrev Form (S : MaurerCartanStage.{uR, uA, uL} R) (n : ℕ) :=
  ActionOperatorForm S.lane n

def d (S : MaurerCartanStage.{uR, uA, uL} R) (n : ℕ) :
    S.Form n →ₗ[R] S.Form (n + 1) :=
  actionExteriorDerivative S.lane n

def wedge (S : MaurerCartanStage.{uR, uA, uL} R) {p q : ℕ}
    (ω : S.Form p) (η : S.Form q) : S.Form (p + q) :=
  actionWedge S.lane ω η

def curvature (S : MaurerCartanStage.{uR, uA, uL} R) (Γ : S.Form 1) : S.Form 2 :=
  actionCurvature S.lane Γ

def covariantDeriv (S : MaurerCartanStage.{uR, uA, uL} R)
    (Γ : S.Form 1) (n : ℕ) : S.Form n →ₗ[R] S.Form (n + 1) :=
  actionCovariantExteriorDerivativeN S.lane Γ n

def thetaL (S : MaurerCartanStage.{uR, uA, uL} R) (g : S.Aˣ) : S.Form 1 :=
  actionThetaL S.lane g

def thetaR (S : MaurerCartanStage.{uR, uA, uL} R) (g : S.Aˣ) : S.Form 1 :=
  actionThetaR S.lane g

def gaugeOneForm (S : MaurerCartanStage.{uR, uA, uL} R)
    (Γ : S.Form 1) (u : S.Aˣ) : S.Form 1 :=
  actionGaugeOneForm S.lane Γ u

def IsFlat (S : MaurerCartanStage.{uR, uA, uL} R) (Γ : S.Form 1) : Prop :=
  S.curvature Γ = 0

def IsExact (S : MaurerCartanStage.{uR, uA, uL} R) (Γ : S.Form 1) : Prop :=
  ∃ P : S.A, Γ = S.d 0 (actionZeroFormEquiv S.lane P)

def IsInnerFlatOn (S : MaurerCartanStage.{uR, uA, uL} R)
    {L₀ : Type*} [LieRing L₀] [LieAlgebra R L₀]
    (dir : L₀ →ₗ⁅R⁆ S.lane.L) (Γ : S.Form 1) : Prop :=
  ∀ x y : L₀, S.curvature Γ ![dir x, dir y] = 0

theorem thetaL_flat (S : MaurerCartanStage.{uR, uA, uL} R) (g : S.Aˣ) :
    S.IsFlat (S.thetaL g) :=
  actionThetaL_flat S.lane S.isLeibniz g

theorem curvature_bianchi (S : MaurerCartanStage.{uR, uA, uL} R) (Γ : S.Form 1) :
    S.covariantDeriv Γ 2 (S.curvature Γ) = 0 :=
  actionCurvature_bianchi S.lane S.isLeibniz Γ

end MaurerCartanStage

/-- A transition morphism between Maurer--Cartan stages consists of an `R`-linear
unital ring homomorphism `algHom : S₁.A →+* S₂.A` and an intertwining Lie-algebra
homomorphism `lieHom : S₁.lane.L →ₗ⁅R⁆ S₂.lane.L`. -/
structure MaurerCartanStageHom {R : Type uR} [CommRing R]
    (S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R) where
  algHom : S₁.A →+* S₂.A
  map_smul' : ∀ (r : R) (a : S₁.A), algHom (r • a) = r • algHom a
  lieHom : S₁.lane.L →ₗ⁅R⁆ S₂.lane.L
  intertwine : ∀ (x : S₁.lane.L) (a : S₁.A),
    S₂.lane.operatorAction (lieHom x) (algHom a) = algHom (S₁.lane.operatorAction x a)

namespace MaurerCartanStageHom

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {R : Type uR} [CommRing R]

/-- Identity stage morphism. -/
def id (S : MaurerCartanStage.{uR, uA, uL} R) : MaurerCartanStageHom S S where
  algHom := RingHom.id S.A
  map_smul' _ _ := rfl
  lieHom := LieHom.id
  intertwine _ _ := rfl

/-- Composition of stage morphisms. -/
def comp {S₁ S₂ S₃ : MaurerCartanStage.{uR, uA, uL} R}
    (m₂ : MaurerCartanStageHom S₂ S₃) (m₁ : MaurerCartanStageHom S₁ S₂) :
    MaurerCartanStageHom S₁ S₃ where
  algHom := m₂.algHom.comp m₁.algHom
  map_smul' r a := by
    simp only [RingHom.comp_apply, m₁.map_smul', m₂.map_smul']
  lieHom := m₂.lieHom.comp m₁.lieHom
  intertwine x a := by
    simp only [LieHom.comp_apply, RingHom.comp_apply]
    rw [m₂.intertwine, m₁.intertwine]

/-- The `R`-linear map underlying `m.algHom`. -/
def algLinearMap {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) : S₁.A →ₗ[R] S₂.A where
  toFun := m.algHom
  map_add' := m.algHom.map_add
  map_smul' := m.map_smul'

@[simp] theorem algLinearMap_apply {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (a : S₁.A) :
    m.algLinearMap a = m.algHom a :=
  rfl

/-- Pulled-back cospan lane `S₁.lane.L` acting on `S₂.A` via `m.lieHom`. -/
abbrev comapLane {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) : LieActionLane R S₂.A where
  L := S₁.lane.L
  lieRing := S₁.lane.lieRing
  lieAlgebra := S₁.lane.lieAlgebra
  act := S₂.lane.act.comp m.lieHom

theorem comapLane_isLeibniz {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) :
    IsLeibnizAction (comapLane m) :=
  fun x => S₂.isLeibniz (m.lieHom x)

@[simp] theorem comapLane_operatorAction {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (x : S₁.lane.L) (b : S₂.A) :
    (comapLane m).operatorAction x b = S₂.lane.operatorAction (m.lieHom x) b :=
  rfl

/-- Covariant pushforward of coefficients into the cospan lane `comapLane m`. -/
def pushCoeff {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (n : ℕ) :
    ActionOperatorForm S₁.lane n →ₗ[R] ActionOperatorForm (comapLane m) n where
  toFun ω := m.algLinearMap.compAlternatingMap ω
  map_add' ω₁ ω₂ := by ext v; exact m.algHom.map_add _ _
  map_smul' r ω := by ext v; exact m.map_smul' _ _

@[simp] theorem pushCoeff_apply {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (n : ℕ)
    (ω : ActionOperatorForm S₁.lane n) (v : Fin n → S₁.lane.L) :
    pushCoeff m n ω v = m.algHom (ω v) :=
  rfl

@[simp] theorem pushCoeff_curryLeft {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) {n : ℕ}
    (ω : ActionOperatorForm S₁.lane (n + 1)) (x : S₁.lane.L) :
    (pushCoeff m (n + 1) ω).curryLeft x = pushCoeff m n (ω.curryLeft x) := by
  ext w
  rfl

@[simp] theorem pushCoeff_reindexForm {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) {a b : ℕ} (h : a = b)
    (ω : ActionOperatorForm S₁.lane a) :
    pushCoeff m b (reindexForm h ω) = reindexForm h (pushCoeff m a ω) := by
  subst h
  rfl

/-- Contravariant pullback of directions into the cospan lane `comapLane m`. -/
def pullDir {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (n : ℕ) :
    ActionOperatorForm S₂.lane n →ₗ[R] ActionOperatorForm (comapLane m) n :=
  pullbackActionForm (K₁ := comapLane m) (K₂ := S₂.lane) (m.lieHom : S₁.lane.L →ₗ[R] S₂.lane.L) n

@[simp] theorem pullDir_apply {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (n : ℕ)
    (ω : ActionOperatorForm S₂.lane n) (v : Fin n → S₁.lane.L) :
    pullDir m n ω v = ω (fun i => m.lieHom (v i)) :=
  rfl

@[simp] theorem pullDir_reindexForm {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) {a b : ℕ} (h : a = b)
    (ω : ActionOperatorForm S₂.lane a) :
    pullDir m b (reindexForm h ω) = reindexForm h (pullDir m a ω) := by
  subst h
  rfl

theorem lieDeriv_pushCoeff {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (x : S₁.lane.L) {n : ℕ}
    (ω : ActionOperatorForm S₁.lane n) :
    lieDeriv (comapLane m) x (pushCoeff m n ω) =
      pushCoeff m n (lieDeriv S₁.lane x ω) := by
  ext v
  simp only [lieDeriv_apply, pushCoeff_apply]
  rw [comapLane_operatorAction, m.intertwine, ← map_sum m.algHom, ← map_sub m.algHom]
  rfl

theorem actionExteriorDerivative_pushCoeff {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) :
    ∀ (n : ℕ) (ω : ActionOperatorForm S₁.lane n),
      actionExteriorDerivative (comapLane m) n (pushCoeff m n ω) =
        pushCoeff m (n + 1) (actionExteriorDerivative S₁.lane n ω)
  | 0, ω => by
    apply alternating_ext_curryLeft
    intro x
    change (actionExteriorDerivative (comapLane m) 0 (pushCoeff m 0 ω)).curryLeft x =
      (pushCoeff m 1 (actionExteriorDerivative S₁.lane 0 ω)).curryLeft x
    rw [actionExteriorDerivative_zero_curryLeft, lieDeriv_pushCoeff,
      pushCoeff_curryLeft, actionExteriorDerivative_zero_curryLeft]
  | k + 1, ω => by
    apply alternating_ext_curryLeft
    intro x
    change (actionExteriorDerivative (comapLane m) (k + 1) (pushCoeff m (k + 1) ω)).curryLeft x =
      (pushCoeff m (k + 2) (actionExteriorDerivative S₁.lane (k + 1) ω)).curryLeft x
    rw [actionExteriorDerivative_succ_curryLeft, lieDeriv_pushCoeff,
      pushCoeff_curryLeft, actionExteriorDerivative_pushCoeff m k (ω.curryLeft x),
      pushCoeff_curryLeft, actionExteriorDerivative_succ_curryLeft, map_sub]

theorem actionWedge_pushCoeff {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) :
    ∀ {p q : ℕ} (ω : ActionOperatorForm S₁.lane p) (η : ActionOperatorForm S₁.lane q),
      actionWedge (comapLane m) (pushCoeff m p ω) (pushCoeff m q η) =
        pushCoeff m (p + q) (actionWedge S₁.lane ω η)
  | 0, q, ω, η => by
    ext v
    simp only [actionWedge_zero_left, reindexForm_apply,
      LinearMap.compAlternatingMap_apply, LinearMap.mul_apply']
    exact (m.algHom.map_mul _ _).symm
  | p' + 1, 0, ω, η => by
    ext v
    simp only [actionWedge_zero_right,
      LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, LinearMap.mul_apply']
    exact (m.algHom.map_mul _ _).symm
  | p' + 1, q' + 1, ω, η => by
    apply alternating_ext_curryLeft
    intro x
    change (actionWedge (comapLane m) (pushCoeff m (p' + 1) ω) (pushCoeff m (q' + 1) η)).curryLeft x =
      pushCoeff m (p' + 1 + q') ((actionWedge S₁.lane ω η).curryLeft x)
    rw [actionWedge_succ_succ_curryLeft, pushCoeff_curryLeft, pushCoeff_curryLeft,
      actionWedge_succ_succ_curryLeft,
      map_add, map_smul, pushCoeff_reindexForm,
      actionWedge_pushCoeff m (ω.curryLeft x) η,
      actionWedge_pushCoeff m ω (η.curryLeft x)]

theorem actionExteriorDerivative_pullDir {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (n : ℕ) (ω : ActionOperatorForm S₂.lane n) :
    actionExteriorDerivative (comapLane m) n (pullDir m n ω) =
      pullDir m (n + 1) (actionExteriorDerivative S₂.lane n ω) :=
  pullbackActionForm_actionExteriorDerivative (K₁ := comapLane m) (K₂ := S₂.lane)
    m.lieHom (fun _ _ => rfl) n ω

theorem actionWedge_pullDir {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) {p q : ℕ}
    (ω : ActionOperatorForm S₂.lane p) (η : ActionOperatorForm S₂.lane q) :
    actionWedge (comapLane m) (pullDir m p ω) (pullDir m q η) =
      pullDir m (p + q) (actionWedge S₂.lane ω η) :=
  (pullbackActionForm_actionWedge (K₁ := comapLane m) (K₂ := S₂.lane)
    (m.lieHom : S₁.lane.L →ₗ[R] S₂.lane.L) ω η).symm

/-- Cospan compatibility of forms `ω₁ : S₁.Form n` and `ω₂ : S₂.Form n` across a
stage morphism `m : MaurerCartanStageHom S₁ S₂`: `pullDir m n ω₂ = pushCoeff m n ω₁`. -/
def StageFormCompatible {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (n : ℕ)
    (ω₁ : S₁.Form n) (ω₂ : S₂.Form n) : Prop :=
  pullDir m n ω₂ = pushCoeff m n ω₁

theorem StageFormCompatible.d {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    {m : MaurerCartanStageHom S₁ S₂} {n : ℕ}
    {ω₁ : S₁.Form n} {ω₂ : S₂.Form n}
    (h : StageFormCompatible m n ω₁ ω₂) :
    StageFormCompatible m (n + 1) (S₁.d n ω₁) (S₂.d n ω₂) := by
  dsimp [StageFormCompatible, MaurerCartanStage.d] at h ⊢
  rw [← actionExteriorDerivative_pullDir, h, actionExteriorDerivative_pushCoeff]

theorem StageFormCompatible.wedge {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    {m : MaurerCartanStageHom S₁ S₂} {p q : ℕ}
    {ω₁ : S₁.Form p} {ω₂ : S₂.Form p}
    {η₁ : S₁.Form q} {η₂ : S₂.Form q}
    (hω : StageFormCompatible m p ω₁ ω₂)
    (hη : StageFormCompatible m q η₁ η₂) :
    StageFormCompatible m (p + q) (S₁.wedge ω₁ η₁) (S₂.wedge ω₂ η₂) := by
  dsimp [StageFormCompatible, MaurerCartanStage.wedge] at hω hη ⊢
  rw [← actionWedge_pullDir, hω, hη, actionWedge_pushCoeff]

theorem StageFormCompatible.curvature {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    {m : MaurerCartanStageHom S₁ S₂}
    {Γ₁ : S₁.Form 1} {Γ₂ : S₂.Form 1}
    (hΓ : StageFormCompatible m 1 Γ₁ Γ₂) :
    StageFormCompatible m 2 (S₁.curvature Γ₁) (S₂.curvature Γ₂) := by
  dsimp [StageFormCompatible, MaurerCartanStage.curvature, actionCurvature] at hΓ ⊢
  rw [map_add, ← actionExteriorDerivative_pullDir,
    ← actionWedge_pullDir m (p := 1) (q := 1) Γ₂ Γ₂, hΓ,
    actionExteriorDerivative_pushCoeff, actionWedge_pushCoeff, map_add]

theorem StageFormCompatible.covariantDeriv {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    {m : MaurerCartanStageHom S₁ S₂} {n : ℕ}
    {Γ₁ : S₁.Form 1} {Γ₂ : S₂.Form 1}
    {ω₁ : S₁.Form n} {ω₂ : S₂.Form n}
    (hΓ : StageFormCompatible m 1 Γ₁ Γ₂)
    (hω : StageFormCompatible m n ω₁ ω₂) :
    StageFormCompatible m (n + 1) (S₁.covariantDeriv Γ₁ n ω₁) (S₂.covariantDeriv Γ₂ n ω₂) := by
  dsimp [StageFormCompatible, MaurerCartanStage.covariantDeriv,
    actionCovariantExteriorDerivativeN] at hΓ hω ⊢
  rw [map_sub, map_add, map_smul, ← actionExteriorDerivative_pullDir,
    pullDir_reindexForm, ← actionWedge_pullDir m (p := 1) (q := n) Γ₂ ω₂,
    ← actionWedge_pullDir m (p := n) (q := 1) ω₂ Γ₂,
    hΓ, hω, actionExteriorDerivative_pushCoeff, actionWedge_pushCoeff, actionWedge_pushCoeff,
    map_sub, map_add, map_smul, pushCoeff_reindexForm]

theorem StageFormCompatible.thetaL {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (g : S₁.Aˣ) :
    StageFormCompatible m 1 (S₁.thetaL g)
      (S₂.thetaL (Units.map m.algHom.toMonoidHom g)) := by
  ext v
  change actionThetaL S₂.lane (Units.map m.algHom.toMonoidHom g) (fun i => m.lieHom (v i)) =
    m.algHom (actionThetaL S₁.lane g v)
  simp only [actionThetaL_apply, Units.coe_map, Units.coe_map_inv]
  erw [m.intertwine]
  exact (m.algHom.map_mul _ _).symm

theorem StageFormCompatible.thetaR {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    (m : MaurerCartanStageHom S₁ S₂) (g : S₁.Aˣ) :
    StageFormCompatible m 1 (S₁.thetaR g)
      (S₂.thetaR (Units.map m.algHom.toMonoidHom g)) := by
  ext v
  change actionThetaR S₂.lane (Units.map m.algHom.toMonoidHom g) (fun i => m.lieHom (v i)) =
    m.algHom (actionThetaR S₁.lane g v)
  simp only [actionThetaR_apply, Units.coe_map, Units.coe_map_inv]
  erw [m.intertwine]
  exact (m.algHom.map_mul _ _).symm

theorem StageFormCompatible.gaugeOneForm {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    {m : MaurerCartanStageHom S₁ S₂} {Γ₁ : S₁.Form 1} {Γ₂ : S₂.Form 1}
    (hΓ : StageFormCompatible m 1 Γ₁ Γ₂) (u : S₁.Aˣ) :
    StageFormCompatible m 1 (S₁.gaugeOneForm Γ₁ u)
      (S₂.gaugeOneForm Γ₂ (Units.map m.algHom.toMonoidHom u)) := by
  ext v
  have hv : Γ₂ (fun i => m.lieHom (v i)) = m.algHom (Γ₁ v) :=
    AlternatingMap.congr_fun hΓ v
  change actionGaugeOneForm S₂.lane Γ₂ (Units.map m.algHom.toMonoidHom u)
      (fun i => m.lieHom (v i)) =
    m.algHom (actionGaugeOneForm S₁.lane Γ₁ u v)
  simp only [actionGaugeOneForm_apply, Units.coe_map, Units.coe_map_inv]
  erw [hv, m.intertwine]
  simp only [map_sub, map_mul]
  rfl

theorem StageFormCompatible.flat_of_algInjective {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    {m : MaurerCartanStageHom S₁ S₂} (hinj : Function.Injective m.algHom)
    {Γ₁ : S₁.Form 1} {Γ₂ : S₂.Form 1}
    (hΓ : StageFormCompatible m 1 Γ₁ Γ₂) (hflat : S₂.IsFlat Γ₂) :
    S₁.IsFlat Γ₁ := by
  have hc := hΓ.curvature
  dsimp [StageFormCompatible, MaurerCartanStage.IsFlat] at hc hflat ⊢
  rw [hflat, map_zero] at hc
  ext v
  exact hinj (by
    have hv := AlternatingMap.congr_fun hc v
    change (0 : S₂.A) = m.algHom (S₁.curvature Γ₁ v) at hv
    simpa [map_zero] using hv.symm)

theorem StageFormCompatible.flat_of_lieSurjective {S₁ S₂ : MaurerCartanStage.{uR, uA, uL} R}
    {m : MaurerCartanStageHom S₁ S₂} (hsurj : Function.Surjective m.lieHom)
    {Γ₁ : S₁.Form 1} {Γ₂ : S₂.Form 1}
    (hΓ : StageFormCompatible m 1 Γ₁ Γ₂) (hflat : S₁.IsFlat Γ₁) :
    S₂.IsFlat Γ₂ := by
  have hc := hΓ.curvature
  dsimp [StageFormCompatible, MaurerCartanStage.IsFlat] at hc hflat ⊢
  rw [hflat, map_zero] at hc
  ext v
  choose u hu using fun i => hsurj (v i)
  have hv := AlternatingMap.congr_fun hc u
  change (S₂.curvature Γ₂) (fun i => m.lieHom (u i)) = 0 at hv
  rw [funext hu] at hv
  exact hv

theorem StageFormCompatible.comp {S₁ S₂ S₃ : MaurerCartanStage.{uR, uA, uL} R}
    {m₁ : MaurerCartanStageHom S₁ S₂} {m₂ : MaurerCartanStageHom S₂ S₃}
    {n : ℕ} {ω₁ : S₁.Form n} {ω₂ : S₂.Form n} {ω₃ : S₃.Form n}
    (h₁₂ : StageFormCompatible m₁ n ω₁ ω₂)
    (h₂₃ : StageFormCompatible m₂ n ω₂ ω₃) :
    StageFormCompatible (m₂.comp m₁) n ω₁ ω₃ := by
  ext v
  have h1 : ω₂ (fun i => m₁.lieHom (v i)) = m₁.algHom (ω₁ v) :=
    AlternatingMap.congr_fun h₁₂ v
  have h2 : ω₃ (fun i => m₂.lieHom (m₁.lieHom (v i))) = m₂.algHom (ω₂ (fun i => m₁.lieHom (v i))) :=
    AlternatingMap.congr_fun h₂₃ (fun i => m₁.lieHom (v i))
  change ω₃ (fun i => m₂.lieHom (m₁.lieHom (v i))) = m₂.algHom (m₁.algHom (ω₁ v))
  rw [h2, h1]

theorem StageFormCompatible.id {S : MaurerCartanStage.{uR, uA, uL} R}
    {n : ℕ} (ω : S.Form n) :
    StageFormCompatible (MaurerCartanStageHom.id S) n ω ω := by
  ext v
  rfl

end MaurerCartanStageHom

section TowerDef

set_option linter.dupNamespace false

/-- A graded/indexed Maurer--Cartan tower over `ℕ` with stage transitions. -/
structure MaurerCartanTower (R : Type uR) [CommRing R] where
  stage : ℕ → MaurerCartanStage.{uR, uA, uL} R
  step : ∀ n : ℕ, MaurerCartanStageHom (stage n) (stage (n + 1))

namespace MaurerCartanTower

variable {R : Type uR} [CommRing R]

/-- Iterated bonding morphism `stage m → stage n` for `m ≤ n`. -/
def bond (T : MaurerCartanTower.{uR, uA, uL} R) {m n : ℕ} (h : m ≤ n) :
    MaurerCartanStageHom (T.stage m) (T.stage n) :=
  Nat.leRecOn h
    (C := fun k => MaurerCartanStageHom (T.stage m) (T.stage k))
    (fun {k} ih => (T.step k).comp ih)
    (MaurerCartanStageHom.id (T.stage m))

@[simp] theorem bond_refl (T : MaurerCartanTower.{uR, uA, uL} R) (m : ℕ) :
    T.bond (le_refl m) = MaurerCartanStageHom.id (T.stage m) := by
  simpa [bond] using
    (Nat.leRecOn_self
      (C := fun k => MaurerCartanStageHom (T.stage m) (T.stage k))
      (next := fun {k} ih => (T.step k).comp ih)
      (x := MaurerCartanStageHom.id (T.stage m)))

@[simp] theorem bond_succ (T : MaurerCartanTower.{uR, uA, uL} R) {m n : ℕ} (h : m ≤ n) :
    T.bond (Nat.le_trans h (Nat.le_succ n)) = (T.step n).comp (T.bond h) := by
  unfold bond
  rw [Nat.leRecOn_trans h (Nat.le_succ n), Nat.leRecOn_succ']

/-- A compatible family of `k`-forms across all stages of a `MaurerCartanTower`. -/
structure TowerForm (T : MaurerCartanTower.{uR, uA, uL} R) (k : ℕ) where
  atStage : ∀ n : ℕ, (T.stage n).Form k
  compat : ∀ n : ℕ, MaurerCartanStageHom.StageFormCompatible (T.step n) k (atStage n) (atStage (n + 1))

namespace TowerForm

variable {T : MaurerCartanTower.{uR, uA, uL} R}

theorem compat_bond {k : ℕ} (ω : TowerForm T k) {m n : ℕ} (h : m ≤ n) :
    MaurerCartanStageHom.StageFormCompatible (T.bond h) k (ω.atStage m) (ω.atStage n) := by
  refine Nat.le_induction
    (m := m)
    (P := fun t ht =>
      MaurerCartanStageHom.StageFormCompatible (T.bond ht) k (ω.atStage m) (ω.atStage t))
    ?base ?succ n h
  · rw [bond_refl]
    exact MaurerCartanStageHom.StageFormCompatible.id (ω.atStage m)
  · intro t hmt ih
    rw [bond_succ T hmt]
    exact MaurerCartanStageHom.StageFormCompatible.comp ih (ω.compat t)

def d {k : ℕ} (ω : TowerForm T k) : TowerForm T (k + 1) where
  atStage n := (T.stage n).d k (ω.atStage n)
  compat n := (ω.compat n).d

def wedge {p q : ℕ} (ω : TowerForm T p) (η : TowerForm T q) : TowerForm T (p + q) where
  atStage n := (T.stage n).wedge (ω.atStage n) (η.atStage n)
  compat n := (ω.compat n).wedge (η.compat n)

def curvature (Γ : TowerForm T 1) : TowerForm T 2 where
  atStage n := (T.stage n).curvature (Γ.atStage n)
  compat n := (Γ.compat n).curvature

def covariantDeriv (Γ : TowerForm T 1) {k : ℕ} (ω : TowerForm T k) : TowerForm T (k + 1) where
  atStage n := (T.stage n).covariantDeriv (Γ.atStage n) k (ω.atStage n)
  compat n := (Γ.compat n).covariantDeriv (ω.compat n)

theorem bianchi (Γ : TowerForm T 1) (n : ℕ) :
    (covariantDeriv Γ (curvature Γ)).atStage n = 0 :=
  (T.stage n).curvature_bianchi (Γ.atStage n)

/-- Canonical unit-frame `thetaL` family generated by a stage-0 unit `g₀`. -/
def unitThetaL (T : MaurerCartanTower.{uR, uA, uL} R) (g₀ : (T.stage 0).Aˣ) :
    TowerForm T 1 where
  atStage n := (T.stage n).thetaL (Units.map (T.bond (Nat.zero_le n)).algHom.toMonoidHom g₀)
  compat n := by
    have hcomp := MaurerCartanStageHom.StageFormCompatible.thetaL (T.step n)
      (Units.map (T.bond (Nat.zero_le n)).algHom.toMonoidHom g₀)
    have hmap :
        Units.map (T.step n).algHom.toMonoidHom
            (Units.map (T.bond (Nat.zero_le n)).algHom.toMonoidHom g₀) =
          Units.map (T.bond (Nat.zero_le (n + 1))).algHom.toMonoidHom g₀ := by
      ext
      simp [MaurerCartanStageHom.comp]
    rwa [hmap] at hcomp

theorem flat_thetaL (T : MaurerCartanTower.{uR, uA, uL} R) (g₀ : (T.stage 0).Aˣ) (n : ℕ) :
    (T.stage n).IsFlat ((unitThetaL T g₀).atStage n) :=
  (T.stage n).thetaL_flat _

end TowerForm

end MaurerCartanTower

end TowerDef

end UnifiedMaurerCartanTower

/-! ## Section 3: Instantiating All Three Repository Maurer--Cartan Formalisms -/

section Formalism1_DerivationLieStage

/-- **Formalism 1**: Any faithful `DerivationLieLane R A` instantiates `MaurerCartanStage R`
with `ActionOperatorForm K.toLieActionLane n ≡ DerivationOperatorForm K n` definitionally. -/
abbrev derivationLieStage {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) : MaurerCartanStage R where
  A := A
  lane := K.toLieActionLane
  isLeibniz := K.isLeibnizAction

@[simp] theorem derivationLieStage_thetaL_eq {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (g : Aˣ) :
    (derivationLieStage K).thetaL g = thetaL K g := by
  ext v
  rfl

theorem derivationLieStage_thetaL_flat {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (g : Aˣ) :
    (derivationLieStage K).IsFlat ((derivationLieStage K).thetaL g) :=
  (derivationLieStage K).thetaL_flat g

theorem derivationLieStage_gauge_covariant {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (g : Aˣ) (Γ : DerivationOperatorForm K 1)
    (n : ℕ) (ω : DerivationOperatorForm K n) :
    (derivationLieStage K).curvature ((derivationLieStage K).gaugeOneForm Γ g) =
        conjugateForm K g ((derivationLieStage K).curvature Γ) ∧
      (derivationLieStage K).covariantDeriv ((derivationLieStage K).gaugeOneForm Γ g) n
          (conjugateForm K g ω) =
        conjugateForm K g ((derivationLieStage K).covariantDeriv Γ n ω) :=
  ⟨ceCurvature_gaugeTransformOneForm K g Γ,
    covariantExteriorDerivativeN_gaugeTransformOneForm K g Γ n ω⟩

end Formalism1_DerivationLieStage

section Formalism2_PeirceMaurerCartan

/-- Inner Lie-action lane `x ↦ [x, -]` over any commutative scalar ring `R` acting on an
associative ring `A` with `[Module R A] [IsScalarTower R A A] [SMulCommClass R A A]`.
This generalizes `innerLieActionLane` (which is `R = ℤ`) without requiring faithfulness. -/
abbrev innerAlgLieActionLane (R A : Type*) [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : LieActionLane R A :=
  letI : LieRing A := LieRing.ofAssociativeRing
  letI : LieAlgebra R A :=
    { lie_smul := fun r x y => by
        change x * (r • y) - (r • y) * x = r • (x * y - y * x)
        simp only [mul_smul_comm, smul_mul_assoc, smul_sub] }
  letI : LieRing (Module.End R A) := LieRing.ofAssociativeRing
  { L := A
    lieRing := ‹_›
    lieAlgebra := ‹_›
    act :=
      { toFun := fun x =>
          { toFun := fun y => x * y - y * x
            map_add' := fun y z => by noncomm_ring
            map_smul' := fun r y => by
              simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc, smul_sub] }
        map_add' := fun x₁ x₂ => by
          ext y
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
          noncomm_ring
        map_smul' := fun r x => by
          ext y
          simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
            smul_mul_assoc, mul_smul_comm, smul_sub]
        map_lie' := fun {x₁ x₂} => by
          ext y
          change (x₁ * x₂ - x₂ * x₁) * y - y * (x₁ * x₂ - x₂ * x₁) =
            (x₁ * (x₂ * y - y * x₂) - (x₂ * y - y * x₂) * x₁) -
            (x₂ * (x₁ * y - y * x₁) - (x₁ * y - y * x₁) * x₂)
          noncomm_ring } }

@[simp] theorem innerAlgLieActionLane_operatorAction (R A : Type*) [CommRing R] [Ring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (x y : A) :
    (innerAlgLieActionLane R A).operatorAction x y = x * y - y * x :=
  rfl

theorem innerAlgLieActionLane_isLeibniz (R A : Type*) [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    IsLeibnizAction (innerAlgLieActionLane R A) := by
  intro x y z
  change x * (y * z) - (y * z) * x =
    (x * y - y * x) * z + y * (x * z - z * x)
  noncomm_ring

theorem innerLieActionLane_isLeibniz (B : Type*) [Ring B] :
    IsLeibnizAction (innerLieActionLane B) := by
  intro x y z
  let x' : B := x
  change x' * (y * z) - (y * z) * x' =
    (x' * y - y * x') * z + y * (x' * z - z * x')
  noncomm_ring

/-- **Formalism 2**: The 5-graded Peirce Maurer--Cartan stage over an arbitrary ring `B`,
built from `innerLieActionLane B` (which is non-faithful whenever `Z(B) ≠ 0`). -/
abbrev peirceFiveGradedStage (B : Type*) [Ring B] : MaurerCartanStage ℤ where
  A := B
  lane := innerLieActionLane B
  isLeibniz := innerLieActionLane_isLeibniz B

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.HistoricalDictionaryAndTomitaFrontiersPoset

/-- **Peirce 5-Graded Maurer--Cartan Reconciliation (`peirce_five_graded_mc_stage`)**:
For commuting idempotents `P² = P`, `Q² = Q`, `Q * P = P * Q` and `X : B` with
unipotent dressing `g = 1 + N_{+1}` and `g⁻¹ = 1 - N_{+1} + N_{+2}` from
`frontier2_nilpotent_differentials_climb_five_graded_maurer_cartan_tower`:
1. `θ := (peirceFiveGradedStage B).thetaL gUnit` evaluates on `H = P - Q` to
   `θ ![H] = N_{+1} - N_{+2}`, matching `θ_H` and `g⁻¹ H g = H + θ_H`.
2. `θ` is unconditionally flat as a Chevalley--Eilenberg 2-form (`d θ + θ ∧ θ = 0`).
3. Reconciles the single-derivation structural defect `D_H(θ_H) + θ_H² = g⁻¹ D_H²(g)`
   (`maurerCartan_structural_eq`, which does not vanish when `D_H²(g) ≠ 0`) with
   the chiral-twisted square-zero super-differentials `d_out2`, `d_in2` (`parConj2`)
   whose sum `d_tot2` generates grade `±1` at order 1 and `-2(N_{+2} - N_{-2})` at order 2. -/
theorem peirce_five_graded_mc_stage {B : Type*} [Ring B]
    (P Q X Z : B) (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : Q * P = P * Q) :
    let hF := frontier2_nilpotent_differentials_climb_five_graded_maurer_cartan_tower
      P Q X Z hP hQ hPQ
    let H := H_bit P Q
    let np1 := N_pos1_2 P Q X
    let nm1 := N_neg1_2 P Q X
    let np2 := N_pos2_2 P Q X
    let nm2 := N_neg2_2 P Q X
    let gUnit : Bˣ := ⟨1 + np1, 1 - np1 + np2, hF.2.2.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.2.1⟩
    let S := peirceFiveGradedStage B
    let H_dir : S.lane.L := H
    let θ := S.thetaL gUnit
    θ ![H_dir] = np1 - np2 ∧
    frameTransport gUnit H = H + θ ![H_dir] ∧
    S.IsFlat θ ∧
    (S.lane.operatorAction H_dir (θ ![H_dir]) + θ ![H_dir] * θ ![H_dir] =
      (↑gUnit⁻¹ : B) * PeirceSpine.comm H (PeirceSpine.comm H (gUnit : B))) ∧
    (d_out2 P Q X (d_out2 P Q X Z) = 0 ∧
      d_in2 P Q X (d_in2 P Q X Z) = 0 ∧
      d_tot2 P Q X H = -(np1 - nm1) ∧
      d_tot2 P Q X (d_tot2 P Q X H) = -(2 • (np2 - nm2))) := by
  intro hF H np1 nm1 np2 nm2 gUnit S H_dir θ
  have hθ : θ ![H_dir] = np1 - np2 := by
    change (↑gUnit⁻¹ : B) * PeirceSpine.comm H (gUnit : B) = np1 - np2
    exact hF.2.2.2.2.2.2.2.2.2.1
  have hframe : frameTransport gUnit H = H + θ ![H_dir] :=
    hF.2.2.2.2.2.2.2.2.2.2
  have hflat : S.IsFlat θ := S.thetaL_flat gUnit
  have hstruct :
      S.lane.operatorAction H_dir (θ ![H_dir]) + θ ![H_dir] * θ ![H_dir] =
        (↑gUnit⁻¹ : B) * PeirceSpine.comm H (PeirceSpine.comm H (gUnit : B)) := by
    change PeirceSpine.comm H ((↑gUnit⁻¹ : B) * PeirceSpine.comm H (gUnit : B)) +
        ((↑gUnit⁻¹ : B) * PeirceSpine.comm H (gUnit : B)) *
          ((↑gUnit⁻¹ : B) * PeirceSpine.comm H (gUnit : B)) =
      (↑gUnit⁻¹ : B) * PeirceSpine.comm H (PeirceSpine.comm H (gUnit : B))
    have hD_inv :
        PeirceSpine.comm H (↑gUnit⁻¹ : B) =
          -((↑gUnit⁻¹ : B) * PeirceSpine.comm H (gUnit : B) * (↑gUnit⁻¹ : B)) :=
      lieAction_operatorAction_inv_unit S.lane S.isLeibniz gUnit H_dir
    have hleib :
        PeirceSpine.comm H ((↑gUnit⁻¹ : B) * PeirceSpine.comm H (gUnit : B)) =
          PeirceSpine.comm H (↑gUnit⁻¹ : B) * PeirceSpine.comm H (gUnit : B) +
            (↑gUnit⁻¹ : B) * PeirceSpine.comm H (PeirceSpine.comm H (gUnit : B)) := by
      dsimp [PeirceSpine.comm]
      noncomm_ring
    rw [hleib, hD_inv]
    noncomm_ring
  exact ⟨hθ, hframe, hflat, hstruct,
    ⟨hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2.2.1⟩⟩

/-- Stage alias of `peirceFiveGradedStage` for the 3-graded Peirce curvature witness carrier. -/
abbrev peirceThreeGradedWitnessStage (B : Type*) [Ring B] : MaurerCartanStage ℤ :=
  peirceFiveGradedStage B

/-- **Peirce 3-Graded Witness Reconciliation**:
Bridges `PeirceMaurerCartanCurvatureWitness` into `peirceThreeGradedWitnessStage B`.
For the unipotent `u = 1 + conePlus P A`, `u⁻¹ = 1 - conePlus P A`:
- `θ := S.thetaL u` evaluates in direction `P` to `peirceMaurerCartanForm (PeirceSpine.comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A`;
- `S.IsFlat θ` holds unconditionally as a CE 2-form (`dθ + θ ∧ θ = 0`);
- while the single-derivation structural curvature `D_P(θ_P) + θ_P²` equals `conePlus P A`
  (nonzero in `Mat2` for `curvatureWitnessP`, `curvatureWitnessA`). -/
theorem peirce_three_graded_mc_stage {B : Type*} [Ring B]
    {P : B} (hP : P * P = P) (A : B) :
    let np := conePlus P A
    have hnp2 : np * np = 0 := conePlus_mul_conePlus hP A A
    let u : Bˣ := ⟨1 + np, 1 - np,
      by calc (1 + np) * (1 - np) = 1 - np * np := by noncomm_ring
        _ = 1 := by rw [hnp2, sub_zero],
      by calc (1 - np) * (1 + np) = 1 - np * np := by noncomm_ring
        _ = 1 := by rw [hnp2, sub_zero]⟩
    let S := peirceFiveGradedStage B
    let P_dir : S.lane.L := P
    let θ := S.thetaL u
    θ ![P_dir] = peirceMaurerCartanForm (PeirceSpine.comm P) (1 + np) (1 - np) ∧
    θ ![P_dir] = np ∧
    S.IsFlat θ ∧
    S.lane.operatorAction P_dir (θ ![P_dir]) + θ ![P_dir] * θ ![P_dir] = np := by
  intro np hnp2 u S P_dir θ
  have hθ_def : θ ![P_dir] = peirceMaurerCartanForm (PeirceSpine.comm P) (1 + np) (1 - np) := rfl
  have hθ_val : θ ![P_dir] = np := by
    change (1 - np) * PeirceSpine.comm P (1 + np) = np
    have hcomm : PeirceSpine.comm P (1 + np) = np := by
      dsimp [PeirceSpine.comm, np, conePlus]
      peirce_nf hP
    rw [hcomm, sub_mul, one_mul, hnp2, sub_zero]
  have hstruct : S.lane.operatorAction P_dir (θ ![P_dir]) + θ ![P_dir] * θ ![P_dir] = np := by
    rw [hθ_def]
    exact peirce_unipotent_maurer_cartan_curvature_eq_conePlus hP A
  exact ⟨hθ_def, hθ_val, S.thetaL_flat u, hstruct⟩

end Formalism2_PeirceMaurerCartan

section Formalism3_TensorStageTower

open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.TensorStageExactConnection

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Stage `n` of the `Cl(1,1)` matrix tensor tower equipped with its inner
Lie-action lane `innerAlgLieActionLane ℝ (Stage n)`. -/
abbrev tensorTowerStage (n : ℕ) : MaurerCartanStage ℝ where
  A := Stage n
  lane := innerAlgLieActionLane ℝ (Stage n)
  isLeibniz := innerAlgLieActionLane_isLeibniz ℝ (Stage n)

/-- **Formalism 3**: The multi-stage `Cl(1,1)` matrix tensor Maurer--Cartan tower
with bonding maps `(stageEmbed n).toRingHom` and `stageEmbedLieHom n`. -/
abbrev tensorStageTower : MaurerCartanTower ℝ where
  stage := tensorTowerStage
  step n :=
    { algHom := (stageEmbed n).toRingHom
      map_smul' := fun r a => map_smul (stageEmbed n) r a
      lieHom := stageEmbedLieHom n
      intertwine := fun x a => by
        change stageEmbed n x * stageEmbed n a - stageEmbed n a * stageEmbed n x =
          stageEmbed n (x * a - a * x)
        simp only [map_sub, map_mul] }

/-- Stage morphism comparing the inner-direction stage `tensorStageTower.stage n`
against the full derivation stage `derivationLieStage (matrixDerivationsLane ℝ (Idx n))`. -/
def matrixInnerToDerivationsHom (n : ℕ) :
    MaurerCartanStageHom (tensorStageTower.stage n)
      (derivationLieStage (matrixDerivationsLane ℝ (Idx n))) where
  algHom := RingHom.id (Stage n)
  map_smul' _ _ := rfl
  lieHom := matrixInnerLieHom ℝ (Idx n)
  intertwine _ _ := rfl

/-- Faithful range derivation lane on inner derivations at stage `n`. -/
def stageInnerRangeLane (n : ℕ) : DerivationLieLane ℝ (Stage n) :=
  rangeDerivationLieLane (matrixInnerLieHom ℝ (Idx n))

theorem tensorStageTower_bond_algHom {m n : ℕ} (h : m ≤ n) :
    (tensorStageTower.bond h).algHom = bondMap stageBond m n h := by
  refine Nat.le_induction
    (m := m)
    (P := fun t ht => (tensorStageTower.bond ht).algHom = bondMap stageBond m t ht)
    ?base ?succ n h
  · rw [tensorStageTower.bond_refl, bondMap_refl]
    rfl
  · intro t hmt ih
    rw [tensorStageTower.bond_succ hmt, bondMap_succ stageBond m t hmt]
    dsimp [MaurerCartanStageHom.comp]
    rw [ih]

theorem tensorStageTower_bond_lieHom_apply {m n : ℕ} (h : m ≤ n) (X : Stage m) :
    (tensorStageTower.bond h).lieHom X = bondMap stageBond m n h X := by
  refine Nat.le_induction
    (m := m)
    (P := fun t ht => (tensorStageTower.bond ht).lieHom X = bondMap stageBond m t ht X)
    ?base ?succ n h
  · rw [tensorStageTower.bond_refl, bondMap_refl]
    rfl
  · intro t hmt ih
    rw [tensorStageTower.bond_succ hmt, bondMap_succ stageBond m t hmt]
    dsimp [MaurerCartanStageHom.comp]
    change stageEmbed t ((tensorStageTower.bond hmt).lieHom X) =
      stageEmbed t (bondMap stageBond m t hmt X)
    rw [ih]

/-- Exact 1-form `d₀ P` at stage `n` on `matrixDerivationsLane ℝ (Idx n)`. -/
def stageExactOneForm (n : ℕ) (P : Stage n) :
    DerivationOperatorForm (matrixDerivationsLane ℝ (Idx n)) 1 :=
  ceExteriorDerivative (matrixDerivationsLane ℝ (Idx n)) 0
    (zeroFormAlternatingEquiv (matrixDerivationsLane ℝ (Idx n)) P)

/-- Inner-restricted exact 1-form `d₀ P` on `tensorStageTower.stage n`. -/
def stageInnerExactOneForm (n : ℕ) (P : Stage n) :
    (tensorStageTower.stage n).Form 1 :=
  MaurerCartanStageHom.pullDir (matrixInnerToDerivationsHom n) 1 (stageExactOneForm n P)

@[simp] theorem stageExactOneForm_apply (n : ℕ) (P : Stage n)
    (D : (matrixDerivationsLane ℝ (Idx n)).L) :
    stageExactOneForm n P ![D] = (D : Module.End ℝ (Stage n)) P :=
  actionExteriorDerivative_zero_apply (matrixDerivationsLane ℝ (Idx n)).toLieActionLane
    (zeroFormAlternatingEquiv (matrixDerivationsLane ℝ (Idx n)) P) ![D]

@[simp] theorem stageInnerExactOneForm_apply (n : ℕ) (P X : Stage n) :
    stageInnerExactOneForm n P ![X] = X * P - P * X := by
  dsimp [stageInnerExactOneForm]
  erw [MaurerCartanStageHom.pullDir_apply]
  have harg : (fun i : Fin 1 => (matrixInnerToDerivationsHom n).lieHom (![X] i)) =
      ![matrixInnerLieHom ℝ (Idx n) X] := by
    ext i; fin_cases i; rfl
  rw [harg]
  erw [stageExactOneForm_apply]
  rfl

theorem stageExactOneForm_closed (n : ℕ) (P : Stage n) :
    ceExteriorDerivative (matrixDerivationsLane ℝ (Idx n)) 1 (stageExactOneForm n P) = 0 :=
  ceExteriorDerivative_succ_comp (matrixDerivationsLane ℝ (Idx n)) 0 _

theorem stageExactOneForm_curvature_inner (n : ℕ) (P X Y : Stage n) :
    ceCurvature (matrixDerivationsLane ℝ (Idx n)) (stageExactOneForm n P)
        ![matrixInnerLieHom ℝ (Idx n) X, matrixInnerLieHom ℝ (Idx n) Y] =
      exactCutCurvature n P X Y := by
  have h0 : stageExactOneForm n P =
      oneFormAlternatingLinearEquiv (matrixDerivationsLane ℝ (Idx n))
        (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P) :=
    ceExteriorDerivative_zero_eq (matrixDerivationsLane ℝ (Idx n)) P
  rw [h0, ceCurvature_eq]
  rfl

theorem stageInnerExactOneForm_curvature (n : ℕ) (P X Y : Stage n) :
    (tensorStageTower.stage n).curvature (stageInnerExactOneForm n P) ![X, Y] =
      exactCutCurvature n P X Y := by
  rw [exactCutCurvature_apply]
  dsimp [MaurerCartanStage.curvature]
  rw [actionCurvature_apply]
  have h1 : stageInnerExactOneForm n P ![X] = X * P - P * X := stageInnerExactOneForm_apply n P X
  have h2 : stageInnerExactOneForm n P ![Y] = Y * P - P * Y := stageInnerExactOneForm_apply n P Y
  have h3 : stageInnerExactOneForm n P ![⁅X, Y⁆] =
      (X * Y - Y * X) * P - P * (X * Y - Y * X) :=
    stageInnerExactOneForm_apply n P (X * Y - Y * X)
  rw [h1, h2, h3]
  change (X * (Y * P - P * Y) - (Y * P - P * Y) * X) -
      (Y * (X * P - P * X) - (X * P - P * X) * Y) -
      ((X * Y - Y * X) * P - P * (X * Y - Y * X)) +
      ((X * P - P * X) * (Y * P - P * Y) - (Y * P - P * Y) * (X * P - P * X)) =
    (X * P - P * X) * (Y * P - P * Y) - (Y * P - P * Y) * (X * P - P * X)
  noncomm_ring

theorem stageInnerExactOneForm_step_compat (n : ℕ) (P : Stage n) :
    MaurerCartanStageHom.StageFormCompatible (tensorStageTower.step n) 1
      (stageInnerExactOneForm n P)
      (stageInnerExactOneForm (n + 1) (stageEmbed n P)) := by
  apply AlternatingMap.ext
  intro v
  change stageInnerExactOneForm (n + 1) (stageEmbed n P)
      (fun i => stageEmbedLieHom n (v i)) =
    stageEmbed n (stageInnerExactOneForm n P v)
  have hv : v = ![v 0] := funext fun i => by rw [Fin.eq_zero i]; rfl
  rw [hv]
  have harg : (fun i : Fin 1 => stageEmbedLieHom n (![v 0] i)) = ![stageEmbed n (v 0)] := by
    ext i; fin_cases i; rfl
  rw [harg]
  erw [stageInnerExactOneForm_apply, stageInnerExactOneForm_apply]
  simp only [map_sub, map_mul]

/-- Iterated `bondMap` transport of `stageInnerExactOneForm` and its curvature across
arbitrary stages `n ≤ m`. -/
theorem stageInnerExactOneForm_bond_compat {n m : ℕ} (hnm : n ≤ m) (P : Stage n) :
    MaurerCartanStageHom.StageFormCompatible (tensorStageTower.bond hnm) 1
      (stageInnerExactOneForm n P)
      (stageInnerExactOneForm m (bondMap stageBond n m hnm P)) := by
  refine Nat.le_induction
    (m := n)
    (P := fun t hnt =>
      MaurerCartanStageHom.StageFormCompatible (tensorStageTower.bond hnt) 1
        (stageInnerExactOneForm n P)
        (stageInnerExactOneForm t (bondMap stageBond n t hnt P)))
    ?base ?succ m hnm
  · rw [tensorStageTower.bond_refl, bondMap_refl]
    exact MaurerCartanStageHom.StageFormCompatible.id _
  · intro t hnt ih
    rw [tensorStageTower.bond_succ hnt, bondMap_succ stageBond n t hnt]
    exact MaurerCartanStageHom.StageFormCompatible.comp ih
      (stageInnerExactOneForm_step_compat t (bondMap stageBond n t hnt P))

/-- Cocone descent of iterated `bondMap` into `Limit` via `ofStage`. -/
theorem ofStage_bondMap {n m : ℕ} (hnm : n ≤ m) (A : Stage n) :
    ofStage m (bondMap stageBond n m hnm A) = ofStage n A :=
  directLimitOf_bondMap stageBond n m hnm A

/-- Cocone descent of `exactCutCurvature` along arbitrary iterated `bondMap` transitions
`n ≤ m` (without fabricating a direct-limit connection; `BUCKET 3` boundary). -/
theorem ofStage_exactCutCurvature_bondMap {n m : ℕ} (hnm : n ≤ m) (P X Y : Stage n) :
    ofStage m (exactCutCurvature m (bondMap stageBond n m hnm P)
        (bondMap stageBond n m hnm X) (bondMap stageBond n m hnm Y)) =
      ofStage n (exactCutCurvature n P X Y) := by
  rw [← bondMap_exactCutCurvature hnm P X Y]
  exact ofStage_bondMap hnm _

/-- Global flat unit-frame `thetaL` `TowerForm` along `tensorStageTower` generated by any
stage-0 unit `g₀ : (Stage 0)ˣ`. -/
theorem tensorStageTower_unitThetaL_flat (g₀ : (Stage 0)ˣ) (n : ℕ) :
    (tensorStageTower.stage n).IsFlat
      ((MaurerCartanTower.TowerForm.unitThetaL tensorStageTower g₀).atStage n) :=
  MaurerCartanTower.TowerForm.flat_thetaL tensorStageTower g₀ n

theorem bondMap_algebraMap {n m : ℕ} (hnm : n ≤ m) (c : ℝ) :
    bondMap stageBond n m hnm (algebraMap ℝ (Stage n) c) = algebraMap ℝ (Stage m) c := by
  refine Nat.le_induction
    (m := n)
    (P := fun t hnt =>
      bondMap stageBond n t hnt (algebraMap ℝ (Stage n) c) = algebraMap ℝ (Stage t) c)
    ?base ?succ m hnm
  · rw [bondMap_refl]
    rfl
  · intro t hnt ih
    rw [bondMap_succ stageBond n t hnt, RingHom.comp_apply, ih]
    exact (stageEmbed t).commutes c

/-- Zero-curvature / flat MC embedding Case (a): at stage `n = 0`, `Stage 0` is commutative
(`Subsingleton (Idx 0)`), so `stageExactOneForm 0 P` is unconditionally flat on ALL derivations. -/
theorem stageExactOneForm_zero_flat (P : Stage 0) :
    (derivationLieStage (matrixDerivationsLane ℝ (Idx 0))).IsFlat (stageExactOneForm 0 P) := by
  dsimp [MaurerCartanStage.IsFlat, MaurerCartanStage.curvature]
  change ceCurvature (matrixDerivationsLane ℝ (Idx 0)) (stageExactOneForm 0 P) = 0
  have h0 : stageExactOneForm 0 P =
      oneFormAlternatingLinearEquiv (matrixDerivationsLane ℝ (Idx 0))
        (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx 0)) P) :=
    ceExteriorDerivative_zero_eq (matrixDerivationsLane ℝ (Idx 0)) P
  rw [h0, ceCurvature_eq, ← map_zero (twoCochainEquivDerivationOperatorForm (matrixDerivationsLane ℝ (Idx 0)))]
  congr 1
  apply Subtype.ext
  apply LinearMap.ext; intro D
  apply LinearMap.ext; intro E
  change connectionCurvature (matrixDerivationsLane ℝ (Idx 0))
    (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx 0)) P) D E = 0
  rw [matrixExactOneForm_curvature]
  have hcomm : ∀ A B : Stage 0, A * B = B * A := by
    intro A B
    ext i j
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Subsingleton.elim k i, Subsingleton.elim j i, mul_comm]
  rw [hcomm, sub_self]

/-- Zero-curvature / flat MC embedding Case (b): scalar/central `P = algebraMap ℝ (Stage n) c`
has `stageExactOneForm n P = 0` and stays globally flat across all `m ≥ n`. -/
theorem stageExactOneForm_central_flat {n m : ℕ} (hnm : n ≤ m) (c : ℝ) :
    let Pm := bondMap stageBond n m hnm (algebraMap ℝ (Stage n) c)
    stageExactOneForm m Pm = 0 ∧
      (derivationLieStage (matrixDerivationsLane ℝ (Idx m))).IsFlat (stageExactOneForm m Pm) := by
  intro Pm
  have hPm : Pm = algebraMap ℝ (Stage m) c := bondMap_algebraMap hnm c
  have hform : stageExactOneForm m Pm = 0 := by
    rw [hPm]
    apply AlternatingMap.ext
    intro v
    have hv : v = ![v 0] := funext fun i => by rw [Fin.eq_zero i]; rfl
    rw [hv, stageExactOneForm_apply, Algebra.algebraMap_eq_smul_one, map_smul,
      show ((v 0 : NonAssocDerivation.derivations ℝ (Stage m)) : Module.End ℝ (Stage m)) 1 = 0 from
        action_one (matrixDerivationsLane ℝ (Idx m)) (v 0),
      smul_zero]
    rfl
  refine ⟨hform, ?_⟩
  dsimp [MaurerCartanStage.IsFlat, MaurerCartanStage.curvature]
  change ceCurvature (matrixDerivationsLane ℝ (Idx m)) (stageExactOneForm m Pm) = 0
  rw [hform, ceCurvature, map_zero, zero_add]
  change actionWedge (matrixDerivationsLane ℝ (Idx m)).toLieActionLane
    (0 : ActionOperatorForm (matrixDerivationsLane ℝ (Idx m)).toLieActionLane 1)
    (0 : ActionOperatorForm (matrixDerivationsLane ℝ (Idx m)).toLieActionLane 1) = 0
  exact actionWedge_zero_val_left _ _

/-- Zero-curvature / flat MC embedding Case (c): if `P : Stage n` is inner-flat
(`∀ X Y, exactCutCurvature n P X Y = 0`), then the restricted exact 1-form on the faithful
inner-derivation lane `stageInnerRangeLane n := rangeDerivationLieLane (matrixInnerLieHom ℝ (Idx n))`
is genuinely flat (`ceCurvature = 0`), and inner-flatness persists along all `bondMap` stages `m ≥ n`. -/
theorem stageExactOneForm_innerRange_flat {n : ℕ} (P : Stage n)
    (hflat : ∀ X Y : Stage n, exactCutCurvature n P X Y = 0) :
    let K := stageInnerRangeLane n
    let Γ : DerivationOperatorForm K 1 :=
      ceExteriorDerivative K 0 (zeroFormAlternatingEquiv K P)
    ceCurvature K Γ = 0 ∧
      ∀ {m : ℕ} (hnm : n ≤ m) (X Y : Stage n),
        exactCutCurvature m (bondMap stageBond n m hnm P)
          (bondMap stageBond n m hnm X) (bondMap stageBond n m hnm Y) = 0 := by
  intro K Γ
  refine ⟨?_, ?_⟩
  · apply AlternatingMap.ext
    intro v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv]
    have hv0 : ∃ X : Stage n, matrixInnerLieHom ℝ (Idx n) X = (v 0).1 := (v 0).2
    have hv1 : ∃ Y : Stage n, matrixInnerLieHom ℝ (Idx n) Y = (v 1).1 := (v 1).2
    rcases hv0 with ⟨X, hX⟩
    rcases hv1 with ⟨Y, hY⟩
    have hX' : ((v 0).1 : Module.End ℝ (Stage n)) P =
        (matrixInnerLieHom ℝ (Idx n) X : Module.End ℝ (Stage n)) P :=
      congrArg (fun D : NonAssocDerivation.derivations ℝ (Stage n) =>
        (D : Module.End ℝ (Stage n)) P) hX.symm
    have hY' : ((v 1).1 : Module.End ℝ (Stage n)) P =
        (matrixInnerLieHom ℝ (Idx n) Y : Module.End ℝ (Stage n)) P :=
      congrArg (fun D : NonAssocDerivation.derivations ℝ (Stage n) =>
        (D : Module.End ℝ (Stage n)) P) hY.symm
    have h0 : Γ = oneFormAlternatingLinearEquiv K (exteriorDerivativeZero K P) :=
      ceExteriorDerivative_zero_eq K P
    rw [h0, ceCurvature_eq]
    change connectionCurvature K (exteriorDerivativeZero K P) (v 0) (v 1) = 0
    rw [connectionCurvature, exteriorDerivativeOne_exteriorDerivativeZero, zero_add,
      connectionWedgeSquare_apply]
    change ((v 0).1 : Module.End ℝ (Stage n)) P * ((v 1).1 : Module.End ℝ (Stage n)) P -
      ((v 1).1 : Module.End ℝ (Stage n)) P * ((v 0).1 : Module.End ℝ (Stage n)) P = 0
    rw [hX', hY']
    have hcut := hflat X Y
    rw [exactCutCurvature_apply] at hcut
    exact hcut
  · intro m hnm X Y
    rw [← bondMap_exactCutCurvature hnm P X Y, hflat X Y, map_zero]

/-- **Tensor-Stage Maurer--Cartan Transport (`tensor_stage_mc_transport`)**:
Unifies `TensorStageExactConnection` with `tensorStageTower` without fabricating an
infinite-stage direct-limit connection (`BUCKET 3` boundary):
1. **Exact `d₀ P` stages**: `d₁(d₀ P) = 0`, curvature on inner directions equals
   `exactCutCurvature`, `bondMap` transports both `d₀ P` and `exactCutCurvature` across
   all `n ≤ m`, and `ofStage` descends `exactCutCurvature` to the direct-limit cocone.
2. **Flat `d₀ P` embedding cases**: `n = 0` is unconditionally flat, central
   `algebraMap ℝ (Stage n) c` is globally flat for all `m ≥ n`, and inner-flat `P`
   is flat on `stageInnerRangeLane n` and persists across `m ≥ n`.
3. **Unit-frame `thetaL` along `tensorStageTower`**: unconditionally flat at every stage `n`,
   transported via `bondMap`, and descending under `ofStage` on inner directions. -/
theorem tensor_stage_mc_transport {n m : ℕ} (hnm : n ≤ m)
    (P X Y : Stage n) (g : (Stage n)ˣ) :
    let g_m : (Stage m)ˣ := Units.map (bondMap stageBond n m hnm).toMonoidHom g
    -- (1) Exact `d₀ P`: closed, inner curvature = exactCutCurvature, bondMap transport & ofStage cocone descent
    (ceExteriorDerivative (matrixDerivationsLane ℝ (Idx n)) 1 (stageExactOneForm n P) = 0) ∧
    (ceCurvature (matrixDerivationsLane ℝ (Idx n)) (stageExactOneForm n P)
        ![matrixInnerLieHom ℝ (Idx n) X, matrixInnerLieHom ℝ (Idx n) Y] =
      exactCutCurvature n P X Y) ∧
    (MaurerCartanStageHom.StageFormCompatible (tensorStageTower.bond hnm) 2
        ((tensorStageTower.stage n).curvature (stageInnerExactOneForm n P))
        ((tensorStageTower.stage m).curvature
          (stageInnerExactOneForm m (bondMap stageBond n m hnm P)))) ∧
    (ofStage m (exactCutCurvature m (bondMap stageBond n m hnm P)
        (bondMap stageBond n m hnm X) (bondMap stageBond n m hnm Y)) =
      ofStage n (exactCutCurvature n P X Y)) ∧
    -- (2) Unit-frame `thetaL` along `tensorStageTower`: unconditionally flat & cocone-invariant
    ((tensorStageTower.stage n).IsFlat ((tensorStageTower.stage n).thetaL g)) ∧
    ((tensorStageTower.stage m).IsFlat ((tensorStageTower.stage m).thetaL g_m)) ∧
    (bondMap stageBond n m hnm ((tensorStageTower.stage n).thetaL g ![X]) =
      (tensorStageTower.stage m).thetaL g_m ![bondMap stageBond n m hnm X]) ∧
    (ofStage m ((tensorStageTower.stage m).thetaL g_m ![bondMap stageBond n m hnm X]) =
      ofStage n ((tensorStageTower.stage n).thetaL g ![X])) := by
  intro g_m
  have hcompat1 := stageInnerExactOneForm_bond_compat hnm P
  have hcompat2 := hcompat1.curvature
  have hdescent_cut :
      ofStage m (exactCutCurvature m (bondMap stageBond n m hnm P)
          (bondMap stageBond n m hnm X) (bondMap stageBond n m hnm Y)) =
        ofStage n (exactCutCurvature n P X Y) := by
    rw [← bondMap_exactCutCurvature hnm P X Y]
    exact ofStage_bondMap hnm _
  have htheta_compat :
      MaurerCartanStageHom.StageFormCompatible (tensorStageTower.bond hnm) 1
        ((tensorStageTower.stage n).thetaL g)
        ((tensorStageTower.stage m).thetaL g_m) := by
    have ht := MaurerCartanStageHom.StageFormCompatible.thetaL (tensorStageTower.bond hnm) g
    have hgunits :
        Units.map (tensorStageTower.bond hnm).algHom.toMonoidHom g = g_m := by
      ext
      simp [g_m, tensorStageTower_bond_algHom hnm]
    rwa [hgunits] at ht
  have htheta_bond :
      bondMap stageBond n m hnm ((tensorStageTower.stage n).thetaL g ![X]) =
        (tensorStageTower.stage m).thetaL g_m ![bondMap stageBond n m hnm X] := by
    have hv := AlternatingMap.congr_fun htheta_compat ![X]
    change (tensorStageTower.stage m).thetaL g_m
        (fun i => (tensorStageTower.bond hnm).lieHom (![X] i)) =
      (tensorStageTower.bond hnm).algHom ((tensorStageTower.stage n).thetaL g ![X]) at hv
    have harg : (fun i : Fin 1 => (tensorStageTower.bond hnm).lieHom (![X] i)) =
        ![bondMap stageBond n m hnm X] := by
      funext i
      fin_cases i
      exact tensorStageTower_bond_lieHom_apply hnm X
    rw [harg, tensorStageTower_bond_algHom hnm] at hv
    exact hv.symm
  have htheta_descent :
      ofStage m ((tensorStageTower.stage m).thetaL g_m ![bondMap stageBond n m hnm X]) =
        ofStage n ((tensorStageTower.stage n).thetaL g ![X]) := by
    rw [← htheta_bond]
    exact ofStage_bondMap hnm _
  exact ⟨stageExactOneForm_closed n P,
    stageExactOneForm_curvature_inner n P X Y,
    hcompat2,
    hdescent_cut,
    (tensorStageTower.stage n).thetaL_flat g,
    (tensorStageTower.stage m).thetaL_flat g_m,
    htheta_bond,
    htheta_descent⟩

end Formalism3_TensorStageTower

end InfoGeometry.OperatorAlgebra.MaurerCartanTower
