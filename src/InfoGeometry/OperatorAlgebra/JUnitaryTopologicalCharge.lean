/-
InfoGeometry/OperatorAlgebra/JUnitaryTopologicalCharge.lean

J-unitary operators and determinant Z2 charge.

This module formalizes the determinant obstruction for real Krein/Majorana
operator geometry.

The determinant is proof-carrying.  In finite dimensions it can be instantiated
by the ordinary determinant; in infinite dimensions it may be a Fredholm,
Berezinian, core-trace, or regularized determinant.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ChiralPolarization
import InfoGeometry.OperatorAlgebra.DrazinRepresentedSplit
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TopologicalCharge

universe uOp

/-! ## 0. Real bounded operator notation and two-valued charge -/

/-- Real bounded endomorphisms. -/
abbrev RealEnd
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/-- The two determinant-orientation charges. -/
inductive Z2Charge where
  | positive
  | negative
deriving DecidableEq, Repr

/-! ## 1. Abstract adjoint and determinant data -/

/--
A minimal adjoint datum on an operator algebra.
-/
structure AdjointDatum
    (Op : Type*) [Monoid Op] where
  /-- Adjoint/transpose operation. -/
  adj : Op → Op

/--
A proof-carrying determinant backend.

This is deliberately abstract.  It can later be instantiated by finite
determinant, Fredholm determinant, Berezinian, or a regularized determinant.
-/
structure DeterminantDatum
    (Op : Type*) [Monoid Op] where
  /-- Determinant-like scalar readout. -/
  det : Op → ℝ

  /-- Multiplicativity of determinant. -/
  det_mul :
    ∀ A B : Op, det (A * B) = det A * det B

  /-- Determinant of the identity. -/
  det_one :
    det 1 = 1

/--
A determinant compatible with the chosen adjoint.
-/
structure AdjointDeterminantDatum
    (Op : Type*) [Monoid Op]
    (Adj : AdjointDatum Op)
    extends DeterminantDatum Op where
  /-- Determinant is invariant under adjoint/transpose. -/
  det_adj :
    ∀ A : Op, det (Adj.adj A) = det A

namespace AdjointDeterminantDatum

variable {Op : Type*} [Monoid Op]
variable {Adj : AdjointDatum Op}
variable (Det : AdjointDeterminantDatum Op Adj)

@[simp]
theorem det_one_apply :
    Det.det (1 : Op) = 1 :=
  Det.det_one

theorem det_mul_apply
    (A B : Op) :
    Det.det (A * B) = Det.det A * Det.det B :=
  Det.det_mul A B

theorem det_adj_apply
    (A : Op) :
    Det.det (Adj.adj A) = Det.det A :=
  Det.det_adj A

end AdjointDeterminantDatum

/-! ## 2. J-unitary operators -/

/--
`U` is `J`-unitary when it preserves the Krein form encoded by `J`.

Algebraically:

`U^dagger J U = J`.
-/
def IsJUnitary
    {Op : Type uOp} [Monoid Op]
    (Adj : AdjointDatum Op)
    (J U : Op) : Prop :=
  Adj.adj U * (J * U) = J

/--
Bundled J-unitary operator.
-/
structure JUnitary
    {Op : Type uOp} [Monoid Op]
    (Adj : AdjointDatum Op)
    (J : Op) where
  op : Op
  is_junitary :
    IsJUnitary Adj J op

namespace JUnitary

variable
    {Op : Type uOp} [Monoid Op]
    {Adj : AdjointDatum Op}
    {J : Op}

/--
The determinant-square obstruction:

If `U^dagger J U = J` and `det J ≠ 0`, then `det(U)^2 = 1`.

This is the algebraic core of the Z2 determinant charge.
-/
theorem det_sq_eq_one
    (Det : AdjointDeterminantDatum Op Adj)
    (hJ : Det.det J ≠ 0)
    (U : JUnitary Adj J) :
    Det.det U.op ^ 2 = 1 := by
  let d : ℝ := Det.det U.op
  let j : ℝ := Det.det J

  have hj : j ≠ 0 := by
    simpa [j] using hJ

  have hdet :
      Det.det (Adj.adj U.op * (J * U.op)) = Det.det J := by
    rw [U.is_junitary]

  have hexpand :
      Det.det (Adj.adj U.op * (J * U.op)) =
        (Det.det U.op * Det.det J) * Det.det U.op := by
    calc
      Det.det (Adj.adj U.op * (J * U.op))
          = Det.det (Adj.adj U.op) * Det.det (J * U.op) := by
              rw [Det.det_mul_apply]
      _ = Det.det (Adj.adj U.op) * (Det.det J * Det.det U.op) := by
              rw [Det.det_mul_apply]
      _ = Det.det U.op * (Det.det J * Det.det U.op) := by
              rw [Det.det_adj_apply]
      _ = (Det.det U.op * Det.det J) * Det.det U.op := by
              ring

  have hscalar :
      (Det.det U.op * Det.det J) * Det.det U.op = Det.det J :=
    hexpand.symm.trans hdet

  have hdj :
      d ^ 2 * j = j := by
    calc
      d ^ 2 * j
          = (d * j) * d := by ring
      _ = j := by
          simpa [d, j] using hscalar

  have hzero :
      (d ^ 2 - 1) * j = 0 := by
    calc
      (d ^ 2 - 1) * j
          = d ^ 2 * j - j := by ring
      _ = j - j := by rw [hdj]
      _ = 0 := by ring

  have hdminus :
      d ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hj

  change d ^ 2 = 1
  nlinarith

/-- Long API name for the determinant-square obstruction. -/
theorem determinant_sq_eq_one
    (Det : AdjointDeterminantDatum Op Adj)
    (hJ : Det.det J ≠ 0)
    (U : JUnitary Adj J) :
    Det.det U.op ^ 2 = 1 :=
  det_sq_eq_one Det hJ U

/--
The determinant of a J-unitary element is nonzero.
-/
theorem det_ne_zero
    (Det : AdjointDeterminantDatum Op Adj)
    (hJ : Det.det J ≠ 0)
    (U : JUnitary Adj J) :
    Det.det U.op ≠ 0 := by
  intro h
  have hsquare := det_sq_eq_one Det hJ U
  rw [h] at hsquare
  norm_num at hsquare

/--
A simple determinant-sign charge.

The theorem `det_sq_eq_one` supplies the algebraic constraint forcing the
determinant into `{1, -1}` over the real backend. A later topological/path
module should add continuity and path-component hypotheses.
-/
def determinantCharge
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitary Adj J) : ℤ :=
  if 0 < Det.det U.op then 1 else -1

/-- Determinant sign as a two-valued charge. -/
def determinantZ2Charge
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitary Adj J) : Z2Charge :=
  if 0 < Det.det U.op then Z2Charge.positive else Z2Charge.negative

@[simp]
theorem determinantCharge_eq_one_of_det_pos
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitary Adj J)
    (hpos : 0 < Det.det U.op) :
    determinantCharge Det U = 1 := by
  simp [determinantCharge, hpos]

@[simp]
theorem determinantCharge_eq_neg_one_of_det_nonpos
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitary Adj J)
    (hpos : ¬ 0 < Det.det U.op) :
    determinantCharge Det U = -1 := by
  simp [determinantCharge, hpos]

@[simp]
theorem determinantZ2Charge_eq_positive_of_det_pos
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitary Adj J)
    (hpos : 0 < Det.det U.op) :
    determinantZ2Charge Det U = Z2Charge.positive := by
  simp [determinantZ2Charge, hpos]

@[simp]
theorem determinantZ2Charge_eq_negative_of_det_nonpos
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitary Adj J)
    (hpos : ¬ 0 < Det.det U.op) :
    determinantZ2Charge Det U = Z2Charge.negative := by
  simp [determinantZ2Charge, hpos]

end JUnitary

/--
Bundled J-unitary unit.

Use a `Units Op` field for the group-level object. The raw predicate
`IsJUnitary` can still be used for unbundled operators.
-/
structure JUnitaryUnit
    {Op : Type*} [Monoid Op]
    (Adj : AdjointDatum Op)
    (J : Op) where
  unit : Units Op
  is_j_unitary :
    IsJUnitary Adj J unit.val

namespace JUnitaryUnit

variable {Op : Type*} [Monoid Op]
variable {Adj : AdjointDatum Op}
variable {J : Op}

/--
The determinant obstruction:

If `J` is determinant-nondegenerate and `U^dagger J U = J`, then

`det(U)^2 = 1`.
-/
theorem determinant_sq_eq_one
    (Det : AdjointDeterminantDatum Op Adj)
    (hJ : Det.det J ≠ 0)
    (U : JUnitaryUnit Adj J) :
    (Det.det U.unit.val) ^ 2 = 1 := by
  have hdet :
      Det.det (Adj.adj U.unit.val * (J * U.unit.val)) = Det.det J := by
    rw [U.is_j_unitary]

  have hcalc :
      Det.det U.unit.val ^ 2 * Det.det J = Det.det J := by
    calc
      Det.det U.unit.val ^ 2 * Det.det J
          = (Det.det U.unit.val * Det.det U.unit.val) * Det.det J := by
              ring
      _ = Det.det U.unit.val * (Det.det J * Det.det U.unit.val) := by
              ring
      _ = Det.det (Adj.adj U.unit.val) * (Det.det J * Det.det U.unit.val) := by
              rw [Det.det_adj_apply]
      _ = Det.det (Adj.adj U.unit.val) * Det.det (J * U.unit.val) := by
              rw [Det.det_mul_apply J U.unit.val]
      _ = Det.det (Adj.adj U.unit.val * (J * U.unit.val)) := by
              rw [← Det.det_mul_apply]
      _ = Det.det J := hdet

  have hcancel :
      Det.det U.unit.val ^ 2 * Det.det J = 1 * Det.det J := by
    simpa using hcalc

  exact mul_right_cancel₀ hJ hcancel

/-- Short API name for the determinant-square obstruction. -/
theorem det_sq_eq_one
    (Det : AdjointDeterminantDatum Op Adj)
    (hJ : Det.det J ≠ 0)
    (U : JUnitaryUnit Adj J) :
    (Det.det U.unit.val) ^ 2 = 1 :=
  determinant_sq_eq_one Det hJ U

/-- The determinant of a real `J`-unitary operator is either `+1` or `-1`. -/
theorem determinant_eq_one_or_neg_one
    (Det : AdjointDeterminantDatum Op Adj)
    (hJ : Det.det J ≠ 0)
    (U : JUnitaryUnit Adj J) :
    Det.det U.unit.val = 1 ∨ Det.det U.unit.val = -1 := by
  have hsq := determinant_sq_eq_one Det hJ U
  have hfactor :
      (Det.det U.unit.val - 1) * (Det.det U.unit.val + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    nlinarith
  · right
    nlinarith

/--
The determinant sign as an integer-valued topological charge.

This is the `Z2` obstruction written as `plus or minus 1 : Z`.
-/
def topologicalCharge
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitaryUnit Adj J) : ℤ :=
  if 0 < Det.det U.unit.val then 1 else -1

/-- Alias emphasizing that this charge is read from the determinant sign. -/
def determinantCharge
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitaryUnit Adj J) : ℤ :=
  topologicalCharge Det U

/-- Determinant sign as a two-valued charge. -/
def determinantZ2Charge
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitaryUnit Adj J) : Z2Charge :=
  if 0 < Det.det U.unit.val then Z2Charge.positive else Z2Charge.negative

/-- If the determinant is `+1`, the topological charge is `+1`. -/
theorem topologicalCharge_eq_one_of_det_eq_one
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitaryUnit Adj J)
    (hdet : Det.det U.unit.val = 1) :
    topologicalCharge Det U = 1 := by
  simp [topologicalCharge, hdet]

/-- If the determinant is `-1`, the topological charge is `-1`. -/
theorem topologicalCharge_eq_neg_one_of_det_eq_neg_one
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitaryUnit Adj J)
    (hdet : Det.det U.unit.val = -1) :
    topologicalCharge Det U = -1 := by
  simp [topologicalCharge, hdet]

/--
The determinant charge readout is definitionally one of the two signs.
-/
theorem determinantCharge_eq_one_or_neg_one
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitaryUnit Adj J) :
    determinantCharge Det U = 1 ∨ determinantCharge Det U = -1 := by
  dsimp [determinantCharge, topologicalCharge]
  split
  · simp
  · simp

@[simp]
theorem determinantZ2Charge_eq_positive_of_det_pos
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitaryUnit Adj J)
    (hpos : 0 < Det.det U.unit.val) :
    determinantZ2Charge Det U = Z2Charge.positive := by
  simp [determinantZ2Charge, hpos]

@[simp]
theorem determinantZ2Charge_eq_negative_of_det_nonpos
    (Det : AdjointDeterminantDatum Op Adj)
    (U : JUnitaryUnit Adj J)
    (hpos : ¬ 0 < Det.det U.unit.val) :
    determinantZ2Charge Det U = Z2Charge.negative := by
  simp [determinantZ2Charge, hpos]

end JUnitaryUnit

/-! ## 3. Chiral calibration -/

/--
A J-unitary operator preserves the chiral grading if it commutes with `chi`.
-/
def PreservesChirality
    {Op : Type uOp} [Mul Op]
    (chi U : Op) : Prop :=
  U * chi = chi * U

/--
A J-unitary operator reverses chirality if it anticommutes with `chi`.
-/
def ReversesChirality
    {Op : Type uOp} [Mul Op] [Neg Op]
    (chi U : Op) : Prop :=
  U * chi = -(chi * U)

/--
A calibration relating determinant orientation charge to chiral behavior.

This should be supplied by the concrete Majorana/Krein model. It is not true
for arbitrary determinant data without hypotheses on dimensions and the action
on the chiral sectors.
-/
structure ChiralOrientationCalibration
    (Op : Type*) [Monoid Op] [Neg Op]
    {Adj : AdjointDatum Op}
    {J : Op}
    (Det : AdjointDeterminantDatum Op Adj)
    (chi : Op) where
  /-- Positive determinant charge corresponds to chiral preservation. -/
  positive_preserves :
    ∀ U : JUnitary Adj J,
      0 < Det.det U.op →
        PreservesChirality chi U.op

  /-- Negative determinant charge corresponds to chiral reversal. -/
  negative_reverses :
    ∀ U : JUnitary Adj J,
      Det.det U.op < 0 →
        ReversesChirality chi U.op

namespace ChiralOrientationCalibration

variable
    {Op : Type uOp} [Monoid Op] [Neg Op]
    {Adj : AdjointDatum Op}
    {J : Op}
    {Det : AdjointDeterminantDatum Op Adj}
    {chi : Op}

/--
If the determinant is positive, the calibrated J-unitary preserves chirality.
-/
theorem preserves_of_positive_charge
    (C : ChiralOrientationCalibration Op (J := J) Det chi)
    (U : JUnitary Adj J)
    (hU : 0 < Det.det U.op) :
    PreservesChirality chi U.op :=
  C.positive_preserves U hU

/--
If the determinant is negative, the calibrated J-unitary reverses chirality.
-/
theorem reverses_of_negative_charge
    (C : ChiralOrientationCalibration Op (J := J) Det chi)
    (U : JUnitary Adj J)
    (hU : Det.det U.op < 0) :
    ReversesChirality chi U.op :=
  C.negative_reverses U hU

end ChiralOrientationCalibration

/-! ## 4. Chiral grading as a determinant-charged J-unitary -/

/--
Bridge between a chosen chiral grading and determinant parity.

This does not say that `chi` is the determinant charge. It says that the chosen
grading is itself a J-unitary involution and therefore carries a determinant
sign.
-/
structure ChiralDeterminantChargeBridge
    (Op : Type*) [Monoid Op]
    {Adj : AdjointDatum Op}
    (Det : AdjointDeterminantDatum Op Adj) where
  /-- Krein metric/fundamental symmetry. -/
  J : Op

  /-- Chiral grading/involution. -/
  chi : Op

  /-- `chi^2 = 1`. -/
  chi_sq :
    chi * chi = 1

  /-- The grading preserves the Krein form. -/
  chi_j_unitary :
    IsJUnitary Adj J chi

  /-- Nondegenerate metric determinant. -/
  J_nondegenerate :
    Det.det J ≠ 0

namespace ChiralDeterminantChargeBridge

variable
    {Op : Type*} [Monoid Op]
    {Adj : AdjointDatum Op}
    {Det : AdjointDeterminantDatum Op Adj}

variable (B : ChiralDeterminantChargeBridge Op Det)

/-- The grading bundled as a J-unitary operator. -/
def gradingJUnitary : JUnitary Adj B.J where
  op := B.chi
  is_junitary := B.chi_j_unitary

/-- The determinant parity of the chiral grading. -/
def chiralTopologicalCharge : ℤ :=
  JUnitary.determinantCharge Det B.gradingJUnitary

/-- The determinant of the grading is `+1` or `-1`. -/
theorem grading_det_eq_one_or_neg_one :
    Det.det B.chi = 1 ∨ Det.det B.chi = -1 := by
  have hsq :
      Det.det B.chi ^ 2 = 1 :=
    JUnitary.det_sq_eq_one
      Det
      B.J_nondegenerate
      B.gradingJUnitary
  have hfactor :
      (Det.det B.chi - 1) * (Det.det B.chi + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    nlinarith
  · right
    nlinarith

end ChiralDeterminantChargeBridge

/-! ## 5. Carrier-level chiral topological charge bridge -/

/--
A carrier-level bridge relating determinant charge to chiral orientation.

This does not identify the chiral grading with the determinant sign. It records
the model-specific compatibility data needed to interpret determinant
orientation as preservation or reversal of chiral sectors.
-/
structure ChiralTopologicalChargeBridge
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Adjoint backend on real bounded endomorphisms. -/
  adjointDatum : AdjointDatum (RealEnd H)

  /-- Determinant backend on real bounded endomorphisms. -/
  detDatum : AdjointDeterminantDatum (RealEnd H) adjointDatum

  /-- Krein metric/fundamental symmetry. -/
  J : RealEnd H

  /-- Nondegenerate metric determinant. -/
  J_nondegenerate :
    detDatum.det J ≠ 0

  /-- Chiral grading operator. -/
  chi : RealEnd H

  /-- `chi^2 = 1`. -/
  chi_square :
    chi.comp chi = 1

  /-- The grading is `J`-unitary, so it carries the determinant obstruction. -/
  chi_j_unitary :
    IsJUnitary adjointDatum J chi

  /-- Chiral grading flips the `J`-orientation. -/
  J_chi_anticommutes :
    J.comp chi = -(chi.comp J)

namespace ChiralTopologicalChargeBridge

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : ChiralTopologicalChargeBridge H)

/-- The carrier-level grading bundled as a J-unitary operator. -/
def gradingJUnitary : JUnitary B.adjointDatum B.J where
  op := B.chi
  is_junitary := B.chi_j_unitary

/-- The determinant sign of the carrier-level chiral grading. -/
def chiralTopologicalCharge : ℤ :=
  JUnitary.determinantCharge B.detDatum B.gradingJUnitary

/-- A J-unitary real endomorphism has determinant square one. -/
theorem determinant_sq_eq_one
    (U : JUnitary B.adjointDatum B.J) :
    B.detDatum.det U.op ^ 2 = 1 :=
  JUnitary.det_sq_eq_one
    B.detDatum
    B.J_nondegenerate
    U

/-- The determinant of the chiral grading is `+1` or `-1`. -/
theorem grading_det_eq_one_or_neg_one :
    B.detDatum.det B.chi = 1 ∨ B.detDatum.det B.chi = -1 := by
  have hsq :
      B.detDatum.det B.chi ^ 2 = 1 :=
    JUnitary.det_sq_eq_one
      B.detDatum
      B.J_nondegenerate
      B.gradingJUnitary
  have hfactor :
      (B.detDatum.det B.chi - 1) * (B.detDatum.det B.chi + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    nlinarith
  · right
    nlinarith

/-- The stored chiral compatibility is the concrete anti-commutation equation. -/
theorem J_chi_anticommutes_eq :
    B.J.comp B.chi = -(B.chi.comp B.J) :=
  B.J_chi_anticommutes

end ChiralTopologicalChargeBridge

/-! ## 6. Determinant obstruction readout -/

/-- The determinant obstruction follows algebraically from the adjoint determinant datum. -/
theorem jUnitaryTopologicalChargeOwnerTarget :
  ∀ (Op : Type*) [Monoid Op],
  ∀ Adj : AdjointDatum Op,
  ∀ Det : AdjointDeterminantDatum Op Adj,
  ∀ J : Op,
  Det.det J ≠ 0 →
  ∀ U : JUnitary Adj J,
    Det.det U.op ^ 2 = 1 := by
  intro Op _ Adj Det J hJ U
  exact JUnitary.det_sq_eq_one Det hJ U

/-- Packet readout for a concrete `J`-unitary determinant obstruction. -/
theorem jUnitaryTopologicalCharge_packet
    (Op : Type*) [Monoid Op]
    (Adj : AdjointDatum Op)
    (Det : AdjointDeterminantDatum Op Adj)
    (J : Op)
    (hJ : Det.det J ≠ 0)
    (U : JUnitary Adj J) :
    Det.det U.op ^ 2 = 1 :=
  jUnitaryTopologicalChargeOwnerTarget Op Adj Det J hJ U

end InfoGeometry.OperatorAlgebra.TopologicalCharge
