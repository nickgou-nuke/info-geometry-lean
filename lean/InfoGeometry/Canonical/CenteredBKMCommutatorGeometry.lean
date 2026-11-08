/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BKMScalarGaugeQuotient
import InfoGeometry.Canonical.FiniteDimensionalCCRNoGo
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra

/-!
# Centering preserves intersector and commutator geometry

The existing finite BKM centering is a real linear projection that removes
the identity direction. Because that direction is central, it leaves every
commutator and every off-diagonal Peirce corner unchanged. In particular, the
self-wedge of an operator one-form is unchanged by pointwise centering.

The BKM squared norm of this self-wedge detects failure of commutativity.
The centered covariance also detects it: in finite dimension a commutator
cannot be a nonzero scalar multiple of the identity. These are statements
about the noncommutative term of curvature. They do not identify covariance
with a curvature tensor or supply a missing exterior derivative.
-/

noncomputable section

namespace InfoGeometry.Canonical.CenteredBKMCommutatorGeometry

open SouriauOnsagerBKM
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.BKMScalarGaugeQuotient
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra (Op1Form Op2Form wedge wedge_apply)

section CentralShift

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Subtracting central scalar parts preserves the ordered commutator. -/
theorem commutator_sub_smul_one (x y : A) (r s : ℝ) :
    (x - r • (1 : A)) * (y - s • (1 : A)) -
        (y - s • (1 : A)) * (x - r • (1 : A)) =
      x * y - y * x := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    _root_.smul_sub]
  rw [smul_comm r s]
  abel

/-- A central scalar part contributes nothing between orthogonal corners. -/
theorem sandwich_sub_smul_one (p q x : A) (r : ℝ) (hpq : p * q = 0) :
    p * (x - r • (1 : A)) * q = p * x * q := by
  simp [mul_sub, sub_mul, hpq]

end CentralShift

variable {n : ℕ}

/-- The repository's genuine BKM centering preserves operator commutators. -/
theorem centeredStatistic_commutator (D : FaithfulDensityOperator n)
    (x y : Operator n) :
    centeredStatistic D x * centeredStatistic D y -
        centeredStatistic D y * centeredStatistic D x = x * y - y * x := by
  exact commutator_sub_smul_one x y (expectationReal D x) (expectationReal D y)

/-- The commutator of self-adjoint operators is skew-adjoint. -/
theorem star_commutator_of_isSelfAdjoint (x y : Operator n)
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    star (x * y - y * x) = -(x * y - y * x) := by
  rw [star_sub (x * y) (y * x), StarMul.star_mul x y, StarMul.star_mul y x,
    hx.star_eq, hy.star_eq, neg_sub]

/-- A skew-adjoint operator has zero real expectation in a faithful density. -/
theorem expectationReal_eq_zero_of_star_eq_neg (D : FaithfulDensityOperator n)
    (x : Operator n) (hx : star x = -x) : expectationReal D x = 0 := by
  have hstar : star (finiteOperatorTrace (D.rho * x)) =
      -finiteOperatorTrace (D.rho * x) := by
    calc
      star (finiteOperatorTrace (D.rho * x)) =
          finiteOperatorTrace (star (D.rho * x)) :=
        (finiteOperatorTrace_star (D.rho * x)).symm
      _ = finiteOperatorTrace (-(x * D.rho)) := by
        rw [StarMul.star_mul D.rho x, hx, D.strictlyPositive.isSelfAdjoint.star_eq,
          neg_mul x D.rho]
      _ = -finiteOperatorTrace (x * D.rho) :=
        (finiteOperatorTraceLinear n).map_neg (x * D.rho)
      _ = -finiteOperatorTrace (D.rho * x) := by
        rw [finiteOperatorTrace_mul_comm x D.rho]
  have hre := congrArg Complex.re hstar
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hre
  unfold expectationReal
  linarith

/-- Real centering fixes the commutator of self-adjoint directions. -/
theorem centeredStatistic_commutator_of_isSelfAdjoint
    (D : FaithfulDensityOperator n) (x y : Operator n)
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    centeredStatistic D (x * y - y * x) = x * y - y * x := by
  unfold centeredStatistic
  rw [expectationReal_eq_zero_of_star_eq_neg D _
    (star_commutator_of_isSelfAdjoint x y hx hy), zero_smul ℝ (1 : Operator n), sub_zero]

/-- For self-adjoint directions the centered and uncentered BKM commutator
energies agree exactly. -/
theorem centeredBKM_commutator_eq_bkm_of_isSelfAdjoint
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (x y : Operator n) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    centeredBKMRealCovariance D hpow (x * y - y * x) (x * y - y * x) =
      D.bkmRealBilinForm hpow (x * y - y * x) (x * y - y * x) := by
  unfold centeredBKMRealCovariance
  rw [centeredStatistic_commutator_of_isSelfAdjoint D x y hx hy]

/-- Centering preserves, and reflects, commutativity of two operators. -/
theorem centeredStatistic_commute_iff (D : FaithfulDensityOperator n)
    (x y : Operator n) :
    Commute (centeredStatistic D x) (centeredStatistic D y) ↔ Commute x y := by
  change centeredStatistic D x * centeredStatistic D y =
      centeredStatistic D y * centeredStatistic D x ↔ x * y = y * x
  rw [← sub_eq_zero, centeredStatistic_commutator]
  exact sub_eq_zero

/-- The upper Peirce arrow is insensitive to the removed expectation. -/
theorem centeredStatistic_upperCorner (D : FaithfulDensityOperator n)
    (p x : Operator n) (hp : IsIdempotentElem p) :
    p * centeredStatistic D x * (1 - p) = p * x * (1 - p) := by
  apply sandwich_sub_smul_one
  rw [mul_sub, mul_one, hp, sub_self]

/-- The lower Peirce arrow is likewise unchanged by centering. -/
theorem centeredStatistic_lowerCorner (D : FaithfulDensityOperator n)
    (p x : Operator n) (hp : IsIdempotentElem p) :
    (1 - p) * centeredStatistic D x * p = (1 - p) * x * p := by
  apply sandwich_sub_smul_one
  rw [sub_mul, one_mul, hp, sub_self]

section Forms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Pointwise centering of an operator one-form, as a native linear map. -/
def centeredOperator1Form (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (α : Op1Form ℝ V (Operator n)) :
    Op1Form ℝ V (Operator n) :=
  (centeringLinearMap D hpow).comp α

@[simp] theorem centeredOperator1Form_apply (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (α : Op1Form ℝ V (Operator n)) (u : V) :
    centeredOperator1Form D hpow α u = centeredStatistic D (α u) := by
  exact centeringLinearMap_apply D hpow (α u)

/-- The entire alternating self-wedge survives centering unchanged. -/
theorem wedge_centeredOperator1Form (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (α : Op1Form ℝ V (Operator n)) :
    wedge (centeredOperator1Form D hpow α) (centeredOperator1Form D hpow α) =
      wedge α α := by
  apply Op2Form.ext
  intro u v
  simp only [wedge_apply, centeredOperator1Form_apply]
  exact centeredStatistic_commutator D (α u) (α v)

/-- The faithful BKM norm detects the self-wedge without losing central data. -/
theorem bkm_selfWedge_eq_zero_iff (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (α : Op1Form ℝ V (Operator n)) (u v : V) :
    D.bkmRealBilinForm hpow (wedge α α u v) (wedge α α u v) = 0 ↔
      Commute (α u) (α v) := by
  rw [FaithfulDensityOperator.bkmRealBilinForm_apply,
    D.kuboMoriPairing_self_re_eq_zero_iff _ hpow, wedge_apply]
  exact sub_eq_zero

/-- A nonzero operator commutator has strictly positive BKM self-wedge energy. -/
theorem bkm_selfWedge_pos_iff (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (α : Op1Form ℝ V (Operator n)) (u v : V) :
    0 < D.bkmRealBilinForm hpow (wedge α α u v) (wedge α α u v) ↔
      ¬ Commute (α u) (α v) := by
  constructor
  · intro hpos hcomm
    have hz := (bkm_selfWedge_eq_zero_iff D hpow α u v).mpr hcomm
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  · intro hcomm
    rw [FaithfulDensityOperator.bkmRealBilinForm_apply]
    apply D.kuboMoriPairing_self_pos _ hpow
    intro hz
    apply hcomm
    exact sub_eq_zero.mp hz

end Forms

/-- A finite operator commutator in the real scalar gauge is necessarily zero.
This is the repository's native finite-dimensional trace obstruction. -/
theorem commutator_mem_scalarGauge_iff (x y : Operator n) :
    x * y - y * x ∈ scalarGauge n ↔ Commute x y := by
  classical
  constructor
  · intro hscalar
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hscalar
    rcases subsingleton_or_nontrivial (FiniteHilbertSpace n) with hV | hV
    · let := hV
      exact Subsingleton.elim _ _
    · let := hV
      have hlin : x.toLinearMap * y.toLinearMap - y.toLinearMap * x.toLinearMap =
          (r : ℂ) • (1 : Module.End ℂ (FiniteHilbertSpace n)) := by
        exact congrArg ContinuousLinearMap.toLinearMap hr.symm
      have hrzero : (r : ℂ) = 0 :=
        InfoGeometry.Canonical.FiniteDimensionalCCRNoGo.scalar_eq_zero_of_commutator_eq
          x.toLinearMap y.toLinearMap (r : ℂ) hlin
      have hrreal : r = 0 := by simpa using congrArg Complex.re hrzero
      have hzero : x * y - y * x = 0 := by simpa [hrreal] using hr.symm
      exact sub_eq_zero.mp hzero
  · intro hcomm
    rw [sub_eq_zero.mpr hcomm.eq]
    exact (scalarGauge n).zero_mem

/-- Even the centered covariance detects all noncommutativity in finite
dimension: the discarded scalar direction contains no nonzero commutator. -/
theorem centeredBKM_commutator_eq_zero_iff (D : FaithfulDensityOperator n)
    (hpow : Continuous D.rpow) (x y : Operator n) :
    centeredBKMRealCovariance D hpow (x * y - y * x) (x * y - y * x) = 0 ↔
      Commute x y := by
  rw [centeredBKMRealCovariance_eq_zero_iff,
    commutator_mem_scalarGauge_iff]

end InfoGeometry.Canonical.CenteredBKMCommutatorGeometry
