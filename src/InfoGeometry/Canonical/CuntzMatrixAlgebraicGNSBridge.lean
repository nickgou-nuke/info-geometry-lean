import InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeBridge
import InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness
import InfoGeometry.Prequantum.GNSBridge

/-!
# Algebraic GNS consumer for the matrix direct-limit trace

This file consumes the already constructed normalized positive trace on the
algebraic matrix direct limit.  It packages that concrete state into the
repository's algebraic GNS quotient and records the cyclic vacuum class.

No norm completion, concrete C*-state extension, faithfulness theorem, or
Tomita--Takesaki operator is asserted here.  Those are downstream analytic
obligations.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixAlgebraicGNSBridge

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeBridge
open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Prequantum.GNSBridge
open InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness

/-! ## Concrete state and quotient -/

/-- The concrete normalized algebraic trace, viewed through the GNS wrapper. -/
def algebraicTraceGNSState : AbstractGNSState Carrier where
  state := realTraceState

/-- The algebraic GNS quotient attached to the concrete direct-limit trace. -/
abbrev algebraicTraceGNSQuotient : Type :=
  RealAlgebraicState.GNSQuotient realTraceState

/-- The cyclic algebraic GNS vacuum, represented by the unit. -/
def algebraicTraceGNSVacuum : algebraicTraceGNSQuotient :=
  Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState) (1 : Carrier)

@[simp] theorem algebraicTraceGNSState_eval (x : Carrier) :
    algebraicTraceGNSState.eval x = realTraceState.eval x :=
  rfl

@[simp] theorem algebraicTraceGNSState_eval_one :
    algebraicTraceGNSState.eval (1 : Carrier) = 1 := by
  exact realTraceState_one

theorem algebraicTraceGNSVacuum_is_unit_class :
    algebraicTraceGNSVacuum =
      (Quotient.mk (RealAlgebraicState.gnsSetoid realTraceState)
        (1 : Carrier) : algebraicTraceGNSQuotient) :=
  rfl

theorem algebraicTraceGNSVacuum_norm_sq :
    realTraceState.eval (star (1 : Carrier) * 1) = 1 := by
  exact realTraceState.gns_vacuum_norm_eq_one

/-! ## Finite-stage readouts -/

/-- The GNS state recovers the normalized trace at every matrix stage. -/
@[simp] theorem algebraicTraceGNSState_stage (n : ℕ) (A : MatrixStage n) :
    algebraicTraceGNSState.eval (stageInjection n A) =
      (matrixTraceState n A).re := by
  rfl

/-- In particular, a diagonal matrix unit has the Bernoulli weight. -/
theorem algebraicTraceGNSState_stage_single_diag
    (n : ℕ) (i : Fin (2 ^ n)) :
    algebraicTraceGNSState.eval
        (stageInjection n (Matrix.single i i 1)) =
      (1 / (2 ^ n : ℂ)).re := by
  rw [algebraicTraceGNSState_stage]
  exact congrArg Complex.re (matrixTraceState_single_diag n i)

/-- Off-diagonal matrix units have zero algebraic GNS readout. -/
theorem algebraicTraceGNSState_stage_single_cross
    (n : ℕ) {i j : Fin (2 ^ n)} (hij : i ≠ j) :
    algebraicTraceGNSState.eval
        (stageInjection n (Matrix.single i j 1)) = 0 := by
  rw [algebraicTraceGNSState_stage]
  exact congrArg Complex.re (matrixTraceState_single_cross (n := n) hij)

/-! ## Faithfulness on the algebraic direct limit -/

theorem realTraceState_gns_quadratic_eq_zero_iff
    (x : Carrier) :
    realTraceState.eval (star x * x) = 0 ↔ x = 0 := by
  induction x using DirectLimit.induction with
  | _ n A =>
      constructor
      · intro hzero
        rw [star_mk, DirectLimit.mul_def] at hzero
        change (matrixTraceState n (star A * A)).re = 0 at hzero
        have h_re_zero :
            (matrixTraceState n (star A * A)).re = 0 := by
          exact hzero
        have h_im_zero :
            (matrixTraceState n (star A * A)).im = 0 := by
          exact matrixTraceState_star_mul_self_im_zero n A
        have h_complex_zero :
            matrixTraceState n (star A * A) = 0 :=
          Complex.ext h_re_zero h_im_zero
        have hA : A = 0 :=
          (matrixTraceState_star_mul_self_eq_zero_iff n A).mp h_complex_zero
        subst A
        change (⟦⟨n, (0 : MatrixStage n)⟩⟧ : Carrier) = 0
        rw [← DirectLimit.zero_def n]
      · intro hx
        rw [hx]
        simp

theorem algebraicTraceGNSQuotient_is_exact_carrier :
    RealAlgebraicState.gnsSetoid realTraceState =
      (⟨fun x y : Carrier => x = y, by
        constructor
        · intro x
          rfl
        · intro x y h
          exact h.symm
        · intro x y z hxy hyz
          exact hxy.trans hyz⟩ : Setoid Carrier) := by
  apply Setoid.ext
  intro x y
  constructor
  · intro hxy
    have hzero : realTraceState.eval (star (x - y) * (x - y)) = 0 := hxy
    have hxy0 : x - y = 0 :=
      (realTraceState_gns_quadratic_eq_zero_iff (x - y)).mp hzero
    exact sub_eq_zero.mp hxy0
  · intro hxy
    subst y
    exact RealAlgebraicState.gnsEquiv_refl realTraceState x

end InfoGeometry.Canonical.CuntzMatrixAlgebraicGNSBridge
