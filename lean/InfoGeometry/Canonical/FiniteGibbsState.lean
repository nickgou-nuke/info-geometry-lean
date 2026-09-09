import InfoGeometry.Canonical.FiniteThermalTraceState

noncomputable section

/-!
# Finite Gibbs-state boundary

The repository currently proves the normalized-trace thermal boundary, not a
general Gibbs exponential construction.  This import owner exposes that
verified boundary under the historical `FiniteGibbsState` target name while
keeping the stronger Gibbs claims explicit and unasserted.
-/

namespace InfoGeometry.Canonical.FiniteGibbsState

open FiniteThermalTraceState
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Meta.MarkovJonesInduction
open InfoGeometry.Prequantum.AlgebraicGNSState

abbrev MatrixState := FiniteThermalTraceState.MatrixState
abbrev finiteState := FiniteThermalTraceState.finiteState
abbrev inverseTemperature := FiniteThermalTraceState.inverseTemperature

theorem finiteState_one (n : ℕ) :
    (finiteState n).eval 1 = 1 :=
  FiniteThermalTraceState.finiteState_one n

theorem finiteState_positive (n : ℕ) (A : MatrixState n) :
    0 ≤ (finiteState n).eval (star A * A) :=
  FiniteThermalTraceState.finiteState_positive n A

theorem finiteState_cyclic (n : ℕ) (A B : MatrixState n) :
    (finiteState n).eval (A * B) = (finiteState n).eval (B * A) :=
  FiniteThermalTraceState.finiteState_cyclic n A B

theorem finiteState_commutator_zero (n : ℕ) (A B : MatrixState n) :
    (finiteState n).eval (A * B - B * A) = 0 :=
  FiniteThermalTraceState.finiteState_commutator_zero n A B

theorem finiteState_stage_compatibility (n : ℕ) (A : MatrixState n) :
    (finiteState (n + 1)).eval (CuntzMatrixTraceTower.concreteStep n A) =
      (finiteState n).eval A :=
  FiniteThermalTraceState.finiteState_stage_compatibility n A

theorem finiteGibbsState_one (n : ℕ) :
    (finiteState n).eval 1 = 1 :=
  by exact (finiteState n).eval_one

theorem finiteGibbsState_positive (n : ℕ) (A : MatrixState n) :
    0 ≤ (finiteState n).eval (star A * A) :=
  by exact (finiteState n).positive A

theorem finiteGibbsState_star (n : ℕ) (A : MatrixState n) :
    (finiteState n).eval (star A) = (finiteState n).eval A :=
  by
    change (matrixTraceFunctional n (star A)).re =
      (matrixTraceFunctional n A).re
    rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply]
    have htrace : Matrix.trace (star A) = star (Matrix.trace A) := by
      rw [← Matrix.trace_conjTranspose]
      rfl
    rw [htrace]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    have hcoef : (1 / (2 ^ n : ℂ)).im = 0 := by
      have hcast : (1 / (2 ^ n : ℂ)) = ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hcast, Complex.ofReal_im]
    rw [hcoef]
    ring

theorem finiteGibbsState_stage_compatibility (n : ℕ) (A : MatrixState n) :
    (finiteState (n + 1)).eval (CuntzMatrixTraceTower.concreteStep n A) =
      (finiteState n).eval A :=
  by
    change (matrixTraceRealAlgebraicState (n + 1)).eval
        (concreteStep n A) =
      (matrixTraceRealAlgebraicState n).eval A
    exact congrArg Complex.re (concreteData.trace_compatible n A)

end InfoGeometry.Canonical.FiniteGibbsState
