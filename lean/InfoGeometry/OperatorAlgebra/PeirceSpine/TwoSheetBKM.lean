/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetFunctionalCalculus
import InfoGeometry.Analysis.BKMResolventIntegral
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Ordered two-sheet resolvent integration on full matrix algebras

The resolvent is the native matrix inverse. The projection may be any
idempotent, and the two directed inputs are arbitrary complex matrices.
No simultaneous diagonalization or commutation of the inputs is assumed.

The Bochner integral is evaluated only after proving the ordered operator
sandwich identity. Self-adjointness of the odd input is needed for the
positive quadratic readout, not for the operator integral identities.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open MeasureTheory Set InfoGeometry.Analysis
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

/-- A scalar shift acts on both complementary sheets. -/
theorem twoSheet_add_smul_one {B : Type*} [Ring B] [Algebra ℝ B]
    (P : B) (p q s : ℝ) :
    twoSheet P p q + s • (1 : B) = twoSheet P (p + s) (q + s) := by
  simp only [twoSheet, add_smul, smul_sub]
  abel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "Mat" => Matrix ι ι ℂ

/-- Exact native matrix inverse, proved from an explicit right inverse. -/
theorem matrix_twoSheet_inv (P : Mat) (hP : P * P = P)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (twoSheet P a b)⁻¹ = twoSheet P a⁻¹ b⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [twoSheet_mul P hP, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb,
    twoSheet_equal, one_smul]

/-- The resolvent of a two-sheet coefficient, using `Matrix.inv`. -/
def twoSheetResolvent (P : Mat) (p q s : ℝ) : Mat :=
  (twoSheet P p q + s • (1 : Mat))⁻¹

theorem twoSheetResolvent_eq (P : Mat) (hP : P * P = P)
    {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    twoSheetResolvent P p q s = twoSheet P (p + s)⁻¹ (q + s)⁻¹ := by
  unfold twoSheetResolvent
  rw [twoSheet_add_smul_one]
  exact matrix_twoSheet_inv P hP
    (add_pos_of_pos_of_nonneg hp hs).ne'
    (add_pos_of_pos_of_nonneg hq hs).ne'

/-- Both resolvent factors retain their order around the arbitrary odd matrix. -/
theorem twoSheetResolvent_sandwich (P : Mat) (hP : P * P = P)
    (A C : Mat) {p q s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    twoSheetResolvent P p q s * genPhi P A C * twoSheetResolvent P p q s =
      (1 / ((p + s) * (q + s))) • genPhi P A C := by
  rw [twoSheetResolvent_eq P hP hp hq hs, twoSheet_sandwich_phi P hP]
  congr 1
  simp only [one_div, mul_inv_rev, mul_comm]

/-- Left multiplication by any matrix preserves the ordered resolvent identity. -/
theorem twoSheetResolvent_left_product (P : Mat) (hP : P * P = P)
    (A C X : Mat) {p q s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    X * twoSheetResolvent P p q s * genPhi P A C * twoSheetResolvent P p q s =
      (1 / ((p + s) * (q + s))) • (X * genPhi P A C) := by
  calc
    _ = X * (twoSheetResolvent P p q s * genPhi P A C *
        twoSheetResolvent P p q s) := by simp only [mul_assoc]
    _ = X * ((1 / ((p + s) * (q + s))) • genPhi P A C) := by
      rw [twoSheetResolvent_sandwich P hP A C hp hq hs]
    _ = _ := mul_smul_comm _ _ _

/-- The four-factor quadratic integrand retains the full operator-valued square. -/
theorem twoSheetResolvent_quadratic (P : Mat) (hP : P * P = P)
    (A C : Mat) {p q s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    genPhi P A C * twoSheetResolvent P p q s * genPhi P A C *
        twoSheetResolvent P p q s =
      (1 / ((p + s) * (q + s))) • genV P A C := by
  rw [twoSheetResolvent_left_product P hP A C (genPhi P A C) hp hq hs,
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1]

theorem integrableOn_twoSheetResolvent_sandwich (P : Mat) (hP : P * P = P)
    (A C : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ =>
      twoSheetResolvent P p q s * genPhi P A C * twoSheetResolvent P p q s)
      (Ioi 0) := by
  have hbase : IntegrableOn
      (fun s : ℝ => (1 / ((p + s) * (q + s))) • genPhi P A C) (Ioi 0) :=
    (integrableOn_Ioi_logResolventKernel hp hq).smul_const (genPhi P A C)
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro s hs
  exact (twoSheetResolvent_sandwich P hP A C hp hq hs.le).symm

/-- The genuine Bochner resolvent integral on the full finite matrix algebra. -/
theorem integral_twoSheetResolvent_sandwich (P : Mat) (hP : P * P = P)
    (A C : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ),
      twoSheetResolvent P p q s * genPhi P A C * twoSheetResolvent P p q s) =
      logDividedDifference p q • genPhi P A C := by
  calc
    _ = ∫ s in Ioi (0 : ℝ),
        (1 / ((p + s) * (q + s))) • genPhi P A C := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact twoSheetResolvent_sandwich P hP A C hp hq hs.le
    _ = (∫ s in Ioi (0 : ℝ), 1 / ((p + s) * (q + s))) • genPhi P A C :=
      integral_smul_const _ _
    _ = _ := by rw [integral_Ioi_logResolventKernel hp hq]

theorem twoSheetResolvent_trace_left (P : Mat) (hP : P * P = P)
    (A C X : Mat) {p q s : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    (Matrix.trace (X * twoSheetResolvent P p q s * genPhi P A C *
      twoSheetResolvent P p q s)).re =
      (1 / ((p + s) * (q + s))) * (Matrix.trace (X * genPhi P A C)).re := by
  rw [twoSheetResolvent_left_product P hP A C X hp hq hs, Matrix.trace_smul]
  exact Complex.smul_re _ _

theorem integrableOn_twoSheetResolvent_trace_left (P : Mat) (hP : P * P = P)
    (A C X : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ =>
      (Matrix.trace (X * twoSheetResolvent P p q s * genPhi P A C *
        twoSheetResolvent P p q s)).re) (Ioi 0) := by
  have hbase : IntegrableOn (fun s : ℝ =>
      (1 / ((p + s) * (q + s))) * (Matrix.trace (X * genPhi P A C)).re)
      (Ioi 0) :=
    (integrableOn_Ioi_logResolventKernel hp hq).mul_const _
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro s hs
  exact (twoSheetResolvent_trace_left P hP A C X hp hq hs.le).symm

/-- The first trace input remains arbitrary and need not commute with the state. -/
theorem integral_twoSheetResolvent_trace_left (P : Mat) (hP : P * P = P)
    (A C X : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ),
      (Matrix.trace (X * twoSheetResolvent P p q s * genPhi P A C *
        twoSheetResolvent P p q s)).re) =
      logDividedDifference p q * (Matrix.trace (X * genPhi P A C)).re := by
  calc
    _ = ∫ s in Ioi (0 : ℝ),
        (1 / ((p + s) * (q + s))) * (Matrix.trace (X * genPhi P A C)).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact twoSheetResolvent_trace_left P hP A C X hp hq hs.le
    _ = (∫ s in Ioi (0 : ℝ), 1 / ((p + s) * (q + s))) *
        (Matrix.trace (X * genPhi P A C)).re := integral_mul_const _ _
    _ = _ := by rw [integral_Ioi_logResolventKernel hp hq]

/-- The exact quadratic BKM resolvent readout, with no assumption that `p ≠ q`. -/
theorem integral_twoSheetResolvent_quadratic_trace (P : Mat) (hP : P * P = P)
    (A C : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ),
      (Matrix.trace (genPhi P A C * twoSheetResolvent P p q s * genPhi P A C *
        twoSheetResolvent P p q s)).re) =
      logDividedDifference p q * (Matrix.trace (genV P A C)).re := by
  rw [integral_twoSheetResolvent_trace_left P hP A C (genPhi P A C) hp hq,
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1]

/-- A Hermitian perturbation gives a nonnegative quadratic resolvent integral. -/
theorem integral_twoSheetResolvent_quadratic_nonneg (P : Mat) (hP : P * P = P)
    (A C : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hPhi : Matrix.IsHermitian (genPhi P A C)) :
    0 ≤ ∫ s in Ioi (0 : ℝ),
      (Matrix.trace (genPhi P A C * twoSheetResolvent P p q s * genPhi P A C *
        twoSheetResolvent P p q s)).re := by
  rw [integral_twoSheetResolvent_trace_left P hP A C (genPhi P A C) hp hq]
  apply mul_nonneg (logDividedDifference_pos hp hq).le
  have htrace := (Matrix.posSemidef_conjTranspose_mul_self (genPhi P A C)).trace_nonneg
  have hre := (RCLike.nonneg_iff.mp htrace).1
  rwa [hPhi.eq] at hre

/-- Every nonzero Hermitian odd perturbation has strictly positive BKM readout. -/
theorem integral_twoSheetResolvent_quadratic_pos (P : Mat) (hP : P * P = P)
    (A C : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hPhi : Matrix.IsHermitian (genPhi P A C)) (hne : genPhi P A C ≠ 0) :
    0 < ∫ s in Ioi (0 : ℝ),
      (Matrix.trace (genPhi P A C * twoSheetResolvent P p q s * genPhi P A C *
        twoSheetResolvent P p q s)).re := by
  rw [integral_twoSheetResolvent_trace_left P hP A C (genPhi P A C) hp hq]
  apply mul_pos (logDividedDifference_pos hp hq)
  have htrace := (Matrix.posSemidef_conjTranspose_mul_self (genPhi P A C)).trace_nonneg
  have hre := (RCLike.nonneg_iff.mp htrace).1
  have him := (RCLike.nonneg_iff.mp htrace).2
  have htrne : Matrix.trace ((genPhi P A C)ᴴ * genPhi P A C) ≠ 0 := by
    intro hz
    exact hne (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz)
  have hrene : (Matrix.trace ((genPhi P A C)ᴴ * genPhi P A C)).re ≠ 0 := by
    intro hz
    apply htrne
    apply Complex.ext
    · simpa using hz
    · simpa using him
  have hpos : 0 < (Matrix.trace ((genPhi P A C)ᴴ * genPhi P A C)).re :=
    lt_of_le_of_ne hre (Ne.symm hrene)
  rwa [hPhi.eq] at hpos

end InfoGeometry.OperatorAlgebra.PeirceSpine
