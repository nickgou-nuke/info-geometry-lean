import InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge
import InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness

/-!
# Normalized trace on the noncommutative matrix direct limit

The finite normalized matrix traces are compatible with the genuine
noncommutative successor embeddings.  This file descends that compatible
complex-linear family through the existing ring direct limit.  It does not
identify the result with a C*-completion and it does not claim a Gibbs state;
the finite Gibbs owners remain separate.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Prequantum.AlgebraicGNSState

def traceFunctional : Carrier →ₗ[ℂ] ℂ where
  toFun := DirectLimit.lift
    (fun _ _ hij => rawMap hij)
    (fun n A => matrixTraceState n A)
    (by
      intro i j hij A
      exact (concreteMap_trace hij A).symm)
  map_add' := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ i A B =>
        simp only [DirectLimit.add_def, DirectLimit.lift_def]
        simpa [matrixTraceState] using
          (matrixTraceFunctional i).map_add A B
  map_smul' := by
    intro c x
    induction x using DirectLimit.induction with
    | _ i A =>
        simp only [DirectLimit.smul_def, DirectLimit.lift_def]
        change matrixTraceFunctional i (c • A) =
          c • matrixTraceFunctional i A
        exact (matrixTraceFunctional i).map_smul c A

@[simp] theorem traceFunctional_stage (n : ℕ) (A : MatrixStage n) :
    traceFunctional (stageInjection n A) = matrixTraceState n A := by
  rfl

theorem traceFunctional_one :
    traceFunctional (1 : Carrier) = 1 := by
  rw [DirectLimit.one_def 0]
  exact matrixTraceState_one 0

theorem traceFunctional_positive (x : Carrier) :
    0 ≤ (traceFunctional (star x * x)).re := by
  induction x using DirectLimit.induction with
  | _ n A =>
      rw [star_mk]
      rw [DirectLimit.mul_def]
      change 0 ≤ (matrixTraceState n (star A * A)).re
      exact InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness.matrixTraceState_star_mul_self_re_nonneg n A

theorem traceFunctional_cyclic (x y : Carrier) :
    traceFunctional (x * y) = traceFunctional (y * x) := by
  induction x, y using DirectLimit.induction₂ with
  | _ n A B =>
      rw [DirectLimit.mul_def, DirectLimit.mul_def]
      change matrixTraceState n (A * B) = matrixTraceState n (B * A)
      simp only [matrixTraceState, matrixTraceFunctional_apply]
      rw [Matrix.trace_mul_comm]

theorem traceFunctional_star (x : Carrier) :
    traceFunctional (star x) = star (traceFunctional x) := by
  induction x using DirectLimit.induction with
  | _ n A =>
      rw [star_mk]
      change matrixTraceState n (star A) = star (matrixTraceState n A)
      simp only [matrixTraceState, matrixTraceFunctional_apply]
      have htrace : Matrix.trace (star A) = star (Matrix.trace A) := by
        rw [← Matrix.trace_conjTranspose]
        rfl
      rw [htrace]
      simp only [star_mul, Complex.star_def]
      have hcoef : (starRingEnd ℂ) (1 / (2 ^ n : ℂ)) =
          1 / (2 ^ n : ℂ) := by
        have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
          exact Complex.conj_natCast 2
        rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, h2]
        simp
      rw [hcoef]
      rw [mul_comm]

theorem traceFunctional_commutator_zero (x y : Carrier) :
    traceFunctional (x * y - y * x) = 0 := by
  rw [map_sub, traceFunctional_cyclic]
  exact sub_self _

instance carrierStarModuleReal : StarModule ℝ Carrier where
  star_smul := by
    intro r x
    induction x using DirectLimit.induction with
    | _ n A =>
        change (⟦⟨n, star ((r : ℂ) • A)⟩⟧ : Carrier) =
          ⟦⟨n, (r : ℂ) • star A⟩⟧
        have hmat : star ((r : ℂ) • A) = (r : ℂ) • star A := by
          ext i j
          simp [Matrix.star_apply]
        exact congrArg (fun B => (⟦⟨n, B⟩⟧ : Carrier)) hmat

def realTraceFunctional : Carrier →ₗ[ℝ] ℝ :=
  { toFun := fun x => (traceFunctional x).re
    map_add' := by
      intro x y
      simp only [map_add, Complex.add_re]
    map_smul' := by
      intro c x
      change (traceFunctional ((c : ℂ) • x)).re = _
      rw [map_smul]
      simp [Complex.mul_re] }

@[simp] theorem realTraceFunctional_apply (x : Carrier) :
    realTraceFunctional x = (traceFunctional x).re :=
  rfl

theorem realTraceFunctional_one :
    realTraceFunctional (1 : Carrier) = 1 := by
  rw [realTraceFunctional_apply, traceFunctional_one]
  rfl

theorem realTraceFunctional_positive (x : Carrier) :
    0 ≤ realTraceFunctional (star x * x) := by
  rw [realTraceFunctional_apply]
  exact traceFunctional_positive x

def realTraceState : RealAlgebraicState Carrier where
  toLinearMap := realTraceFunctional
  normalized := realTraceFunctional_one
  positive := realTraceFunctional_positive
  symmetric := by
    intro x y
    rw [realTraceFunctional_apply, realTraceFunctional_apply]
    have hstar := traceFunctional_star (star x * y)
    have hreal := congrArg Complex.re hstar
    simpa [star_mul, Complex.star_def] using hreal

@[simp] theorem realTraceState_eval (x : Carrier) :
    realTraceState.eval x = (traceFunctional x).re :=
  rfl

@[simp] theorem realTraceState_stage (n : ℕ) (A : MatrixStage n) :
    realTraceState.eval (stageInjection n A) =
      (matrixTraceState n A).re := by
  rfl

theorem realTraceState_one :
    realTraceState.eval (1 : Carrier) = 1 :=
  realTraceFunctional_one

theorem realTraceState_cyclic (x y : Carrier) :
    realTraceState.eval (x * y) =
      realTraceState.eval (y * x) := by
  rw [realTraceState_eval, realTraceState_eval, traceFunctional_cyclic]

theorem realTraceState_commutator_zero (x y : Carrier) :
    realTraceState.eval (x * y - y * x) = 0 := by
  rw [realTraceState_eval]
  have h := traceFunctional_commutator_zero x y
  exact congrArg Complex.re h

theorem realTraceState_positive (x : Carrier) :
    0 ≤ realTraceState.eval (star x * x) :=
  realTraceFunctional_positive x

end InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
