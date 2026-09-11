import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FibonacciHadjiivanovIntertwiner

/-!
# Topological braid monodromy: the finite norm estimate

This owner records only the analytic consequence that is available from a
bounded square-zero perturbation.  It deliberately does not define a
Tomita--Takesaki flow or a KMS condition: those require additional analytic
and state data.
-/

namespace InfoGeometry.Physics.Algebra

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

structure ContinuousMonodromyOperator (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  lambda : ℝ
  N : H →L[ℝ] H

def ContinuousMonodromyOperatorLaws (M : ContinuousMonodromyOperator H) : Prop :=
  M.N.comp M.N = 0

variable (M : ContinuousMonodromyOperator H)

/-! ### Square-zero unipotent shadow -/

/--
The unipotent monodromy shadow `1 + t • N` associated to the bounded
square-zero perturbation.

This is the structural operator-level transport law used by the finite braid
and Jordan lanes in the repository.
-/
def continuousUnipotentFlow (t : ℝ) : H →L[ℝ] H :=
  (1 : H →L[ℝ] H) + (t : ℝ) • M.N

@[simp] theorem continuousUnipotentFlow_zero :
    continuousUnipotentFlow M 0 = (1 : H →L[ℝ] H) := by
  ext x
  simp [continuousUnipotentFlow]

/--
The unipotent shadow composes by addition of its parameter.
-/
theorem continuousUnipotentFlow_add (hM : ContinuousMonodromyOperatorLaws M)
    (s t : ℝ) :
    continuousUnipotentFlow M s * continuousUnipotentFlow M t =
      continuousUnipotentFlow M (s + t) := by
  ext x
  have hN : M.N (M.N x) = 0 := by
    exact congrArg (fun f : H →L[ℝ] H => f x) hM
  simp [continuousUnipotentFlow, hN, add_comm, add_left_comm, add_assoc,
    add_smul]

/--
The `n`-fold product of the unipotent shadow is the shadow at the scaled
parameter `n`.
-/
theorem continuousUnipotentFlow_pow (hM : ContinuousMonodromyOperatorLaws M)
    (t : ℝ) (n : ℕ) :
    (continuousUnipotentFlow M t) ^ n =
      continuousUnipotentFlow M ((n : ℝ) * t) := by
  induction n with
  | zero =>
      simp [continuousUnipotentFlow]
  | succ n ih =>
      calc
        (continuousUnipotentFlow M t) ^ (n + 1)
            = (continuousUnipotentFlow M t) ^ n *
                continuousUnipotentFlow M t := by
                  simp [pow_succ]
        _ = continuousUnipotentFlow M ((n : ℝ) * t) *
              continuousUnipotentFlow M t := by rw [ih]
        _ = continuousUnipotentFlow M (((n : ℝ) * t) + t) := by
              exact continuousUnipotentFlow_add M hM ((n : ℝ) * t) t
        _ = continuousUnipotentFlow M (((n + 1 : ℕ) : ℝ) * t) := by
              simp [Nat.cast_add, add_mul, add_comm]

/--
The unipotent flow has a right inverse at `-t`.
-/
theorem continuousUnipotentFlow_mul_neg
    (hM : ContinuousMonodromyOperatorLaws M) (t : ℝ) :
    continuousUnipotentFlow M t * continuousUnipotentFlow M (-t) =
      (1 : H →L[ℝ] H) := by
  rw [continuousUnipotentFlow_add M hM]
  simp [continuousUnipotentFlow]

/--
The unipotent flow has a left inverse at `-t`.
-/
theorem continuousUnipotentFlow_neg_mul
    (hM : ContinuousMonodromyOperatorLaws M) (t : ℝ) :
    continuousUnipotentFlow M (-t) * continuousUnipotentFlow M t =
      (1 : H →L[ℝ] H) := by
  rw [continuousUnipotentFlow_add M hM]
  simp [continuousUnipotentFlow]

theorem continuous_continuousUnipotentFlow :
    Continuous (continuousUnipotentFlow M) := by
  unfold continuousUnipotentFlow
  refine Continuous.add continuous_const ?_
  exact Continuous.smul continuous_id continuous_const

/--
The real-parameter similarity flow associated with the scalar/Jordan data.
This is an algebraic bounded-operator flow; it is not by itself a KMS state.
-/
noncomputable def continuousModularMonodromyFlow (t : ℝ) : H →L[ℝ] H :=
  Real.exp (t * Real.log |M.lambda|) •
    ((1 : H →L[ℝ] H) + (t * (1 / M.lambda)) • M.N)

@[simp] theorem continuousModularMonodromyFlow_zero :
    continuousModularMonodromyFlow M 0 = (1 : H →L[ℝ] H) := by
  ext x
  simp [continuousModularMonodromyFlow]

theorem modular_flow_group_homomorphism
    (hM : ContinuousMonodromyOperatorLaws M) (t s : ℝ) :
    continuousModularMonodromyFlow M (t + s) =
      (continuousModularMonodromyFlow M t).comp
        (continuousModularMonodromyFlow M s) := by
  ext x
  simp only [continuousModularMonodromyFlow, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_smul]
  have hN : M.N (M.N x) = 0 := by
    exact congrArg (fun f : H →L[ℝ] H => f x) hM
  rw [add_mul, Real.exp_add]
  simp only [smul_add, smul_smul, hN, smul_zero, add_zero]
  module

theorem continuous_continuousModularMonodromyFlow :
    Continuous (continuousModularMonodromyFlow M) := by
  unfold continuousModularMonodromyFlow
  refine Continuous.smul ?_ ?_
  · exact Real.continuous_exp.comp
      (Continuous.mul continuous_id continuous_const)
  · refine Continuous.add continuous_const ?_
    exact Continuous.smul
      (Continuous.mul continuous_id continuous_const) continuous_const

/--
The modular monodromy flow is a continuous linear equivalence with inverse
given by the negated parameter.
-/
noncomputable def continuousModularMonodromyFlowEquiv
    (hM : ContinuousMonodromyOperatorLaws M) (t : ℝ) :
    H ≃L[ℝ] H := by
  let e : H ≃ₗ[ℝ] H :=
    { toLinearMap := continuousModularMonodromyFlow M t
      invFun := continuousModularMonodromyFlow M (-t)
      left_inv := by
        intro x
        have h :
            (1 : H →L[ℝ] H) =
              (continuousModularMonodromyFlow M (-t)).comp
                (continuousModularMonodromyFlow M t) := by
          simpa [continuousModularMonodromyFlow_zero, add_comm] using
            (modular_flow_group_homomorphism (M := M) hM (-t) t)
        have hx := congrArg (fun f : H →L[ℝ] H => f x) h
        simpa [ContinuousLinearMap.comp_apply] using hx.symm
      right_inv := by
        intro x
        have h :
            (1 : H →L[ℝ] H) =
              (continuousModularMonodromyFlow M t).comp
              (continuousModularMonodromyFlow M (-t)) := by
          simpa [continuousModularMonodromyFlow_zero, add_comm] using
              (modular_flow_group_homomorphism (M := M) hM t (-t))
        have hx := congrArg (fun f : H →L[ℝ] H => f x) h
        simpa [ContinuousLinearMap.comp_apply] using hx.symm }
  exact ContinuousLinearEquiv.mk e
    (continuousModularMonodromyFlow M t).continuous
    (continuousModularMonodromyFlow M (-t)).continuous

@[simp] theorem continuousModularMonodromyFlowEquiv_symm_apply_apply
    (t : ℝ) (x : H) :
    (continuousModularMonodromyFlowEquiv M hM t).symm
        (continuousModularMonodromyFlow M t x) = x := by
  simpa [continuousModularMonodromyFlowEquiv] using
      (ContinuousLinearEquiv.symm_apply_apply
      (continuousModularMonodromyFlowEquiv M hM t) x)

/--
The square-zero unipotent shadow is a one-parameter family of continuous
linear equivalences, with inverse obtained by negating the parameter.
-/
noncomputable def continuousUnipotentFlowEquiv
    (hM : ContinuousMonodromyOperatorLaws M) (t : ℝ) :
    H ≃L[ℝ] H := by
  let e : H ≃ₗ[ℝ] H :=
    { toLinearMap := continuousUnipotentFlow M t
      invFun := continuousUnipotentFlow M (-t)
      left_inv := by
        intro x
        have h :
            continuousUnipotentFlow M (-t) *
                continuousUnipotentFlow M t = (1 : H →L[ℝ] H) := by
          rw [continuousUnipotentFlow_add M hM]
          simp [continuousUnipotentFlow]
        simpa using congrArg (fun f : H →L[ℝ] H => f x) h
      right_inv := by
        intro x
        have h :
            continuousUnipotentFlow M t *
                continuousUnipotentFlow M (-t) = (1 : H →L[ℝ] H) := by
          rw [continuousUnipotentFlow_add M hM]
          simp [continuousUnipotentFlow]
        simpa using congrArg (fun f : H →L[ℝ] H => f x) h }
  exact ContinuousLinearEquiv.mk e
    ((continuousUnipotentFlow M t).continuous)
    ((continuousUnipotentFlow M (-t)).continuous)

@[simp] theorem continuousUnipotentFlowEquiv_zero :
    continuousUnipotentFlowEquiv M hM 0 = ContinuousLinearEquiv.refl ℝ H := by
  ext x
  simp [continuousUnipotentFlowEquiv, continuousUnipotentFlow]

@[simp] theorem continuousUnipotentFlowEquiv_symm_apply_apply (t : ℝ) (x : H) :
    (continuousUnipotentFlowEquiv M hM t).symm
        (continuousUnipotentFlow M t x) = x := by
  simpa [continuousUnipotentFlowEquiv] using
      (ContinuousLinearEquiv.symm_apply_apply
      (continuousUnipotentFlowEquiv M hM t) x)

/--
The norm of the unipotent factor grows at most linearly in the winding
number.  The square-zero property is part of the carrier structure, but
the estimate itself uses only boundedness of `N`.
-/
theorem continuous_monodromy_norm_bound (n : ℕ) :
    ‖(1 : H →L[ℝ] H) + (n : ℝ) • M.N‖ ≤
      1 + (n : ℝ) * ‖M.N‖ := by
  calc
    ‖(1 : H →L[ℝ] H) + (n : ℝ) • M.N‖
        ≤ ‖(1 : H →L[ℝ] H)‖ + ‖(n : ℝ) • M.N‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ 1 + (n : ℝ) * ‖M.N‖ := by
      have hId : ‖(1 : H →L[ℝ] H)‖ ≤ 1 :=
        ContinuousLinearMap.norm_id_le
      have hsmul : ‖(n : ℝ) • M.N‖ ≤ (n : ℝ) * ‖M.N‖ := by
        have hn : ‖(n : ℝ)‖ = (n : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg]
          positivity
        simpa [hn] using
          (ContinuousLinearMap.opNorm_smul_le (n : ℝ) M.N)
      exact add_le_add hId hsmul

/--
The modular flow equivalences compose additively in the flow parameter.
-/
theorem continuousModularMonodromyFlowEquiv_comp
    (hM : ContinuousMonodromyOperatorLaws M) (t s : ℝ) :
    (continuousModularMonodromyFlowEquiv M hM t).trans
        (continuousModularMonodromyFlowEquiv M hM s) =
      continuousModularMonodromyFlowEquiv M hM (t + s) := by
  ext x
  change continuousModularMonodromyFlow M s
      (continuousModularMonodromyFlow M t x) =
    continuousModularMonodromyFlow M (t + s) x
  have h := modular_flow_group_homomorphism (M := M) hM s t
  have hx := congrArg (fun f : H →L[ℝ] H => f x) h.symm
  simpa [add_comm, Homeomorph.trans] using hx

end InfoGeometry.Physics.Algebra
