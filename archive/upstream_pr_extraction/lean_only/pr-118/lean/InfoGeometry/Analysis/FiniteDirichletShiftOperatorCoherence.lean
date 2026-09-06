import Mathlib
import InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge
import InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge
import InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge

/-!
# Coherence of the two finite logarithmic-shift readouts

The analysis and arithmetic owners use different names for the same native
translation operator and the same exponential test family.  This file is the
small interoperability layer between them.  The finite-sum statement also
records the indexing convention: the analysis stage `N` contains the terms
`1, ..., N + 1`, hence agrees with the arithmetic cutoff `N + 1`.
-/

namespace InfoGeometry.Analysis.FiniteDirichletShiftOperatorCoherence

open InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge
open InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge

theorem translationShift_eq_shiftOp (u : ℝ) :
    translationShift u = shiftOp u := rfl

theorem exponentialTest_eq_expTestFun (s : ℂ) :
    exponentialTest s = expTestFun s := rfl

theorem translationShift_exponentialTest_eq_shiftOp_expTestFun
    (u : ℝ) (s : ℂ) :
    translationShift u (exponentialTest s) =
      shiftOp u (expTestFun s) := rfl

private theorem sum_range_shift_succ {α : Type*} [AddCommMonoid α]
    (N : ℕ) (F : ℕ → α) :
    (∑ n ∈ Finset.range N, F (n + 1)) =
      ∑ m ∈ Finset.Icc 1 N, F m := by
  refine Finset.sum_bij (fun x _ => x + 1) ?_ ?_ ?_ ?_
  · intro x hx
    have hxlt : x < N := Finset.mem_range.mp hx
    simp only [Finset.mem_Icc]
    omega
  · intro x hx y hy hxy
    change x + 1 = y + 1 at hxy
    omega
  · intro y hy
    refine ⟨y - 1, ?_, ?_⟩
    · have hy' := Finset.mem_Icc.mp hy
      simp only [Finset.mem_range]
      rw [Nat.sub_lt_iff_lt_add hy'.1]
      omega
    · have hy' := Finset.mem_Icc.mp hy
      exact Nat.sub_add_cancel hy'.1
  · intro x hx
    rfl

theorem finiteDirichletShift_succ_eq_finiteDirichletShiftOp (N : ℕ) :
    finiteDirichletShift N =
      finiteDirichletShiftOp (N + 1) := by
  ext f t
  simp only [finiteDirichletShift, finiteDirichletShiftOp,
    LinearMap.sum_apply, Finset.sum_apply]
  rw [Finset.sum_range_succ]
  simp only [Nat.succ_eq_add_one]
  rw [Finset.sum_Icc_succ_top (by omega)]
  congr 1
  simpa [logShiftOp, translationShift, shiftOp] using
    (sum_range_shift_succ N
      (fun m => shiftOp (Real.log (m : ℝ)) f t))

theorem dirichletOperator_succ_eq_arithmeticDirichletOperator
    (N : ℕ) (a : ℕ → ℂ) :
    InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge.dirichletOperator
        N a =
      InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge.dirichletOperator
        (N + 1) a := by
  ext f t
  simp only [
    InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge.dirichletOperator,
    InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge.dirichletOperator,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_range_succ]
  simp only [Nat.succ_eq_add_one]
  rw [Finset.sum_Icc_succ_top (by omega)]
  congr 1
  simpa [logShiftOp, translationShift, shiftOp] using
    (sum_range_shift_succ N
      (fun m => a m • shiftOp (Real.log (m : ℝ)) f t))

theorem arithmeticDirichletOperator_succ_expTestFun_eigenvector
    (N : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge.dirichletOperator
        (N + 1) a
        (InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge.expTestFun s) =
      InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge.dirichletEigenvalue
        N a s •
        InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge.expTestFun s := by
  rw [← dirichletOperator_succ_eq_arithmeticDirichletOperator N a]
  rw [← exponentialTest_eq_expTestFun]
  exact dirichletOperator_exponentialTest_eigenvector N a s

end InfoGeometry.Analysis.FiniteDirichletShiftOperatorCoherence
