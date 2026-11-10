/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetModular
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetBKM
import InfoGeometry.Core.DefectIteration
import InfoGeometry.Core.PeirceSourceOrder
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Modular commutator energy and the exact Peirce defect

The actual negative CFC logarithm acts on an arbitrary odd matrix. Its
resolvent-pairing energy is the squared logarithmic sheet difference times
the original odd energy. The shared quadratic operator is identified with
the existing idempotency defect, without introducing another defect object.

At equal positive sheet weights the modular action vanishes, while the
quadratic resolvent form remains strictly positive on nonzero Hermitian odd
inputs. These are separate statements about the same full matrix algebra.

The imported `Core.PeirceSourceOrder` supplies the existing native prerequisite
partial order and its algebraic synthesis. `Core.DefectIteration` supplies the
recursive defect tower and its antitone chain of generated subalgebras. These
orders do not assert physical causation or strict growth of successive defects.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open MeasureTheory Set InfoGeometry.Analysis
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

section StarRing

variable {B : Type*} [Ring B] [StarRing B] {P : B}

/-- The directed current of a self-adjoint odd input is skew-adjoint.
The two corner representatives remain arbitrary. -/
theorem star_genJ_of_genPhi_selfAdjoint (hP : IsStarProjection P)
    (A C : B) (hPhi : IsSelfAdjoint (genPhi P A C)) :
    star (genJ P A C) = -genJ P A C := by
  have hPid : P * P = P := hP.isIdempotentElem.eq
  have hcurrent : comm P (genPhi P A C) = genJ P A C := by peirce_nf hPid
  rw [← hcurrent]
  simp only [comm, star_sub, star_mul, hP.isSelfAdjoint.star_eq, hPhi.star_eq]
  abel

/-- The current's Gram operator is the exact idempotency defect of `P + Φ`. -/
theorem genJ_gram_eq_idempotencyDefect (hP : IsStarProjection P)
    (A C : B) (hPhi : IsSelfAdjoint (genPhi P A C)) :
    star (genJ P A C) * genJ P A C =
      InfoGeometry.Core.IdempotencyDefect.defect (P + genPhi P A C) := by
  have hdef : InfoGeometry.Core.IdempotencyDefect.defect (P + genPhi P A C) =
      genV P A C := by
    exact InfoGeometry.Core.PeirceDefect.defect_add_coupled hP.isIdempotentElem
      (u := conePlus P A) (v := coneMinus P C) ⟨A, rfl⟩ ⟨C, rfl⟩
  rw [star_genJ_of_genPhi_selfAdjoint hP A C hPhi, neg_mul,
    (archetype_A3_nilpotent_cones_and_tetraktys_table
      hP.isIdempotentElem.eq A C).2.2.2.1, neg_neg]
  exact hdef.symm

end StarRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "Mat" => Matrix ι ι ℂ

/-- The real resolvent pairing, with the star on the first input explicit. -/
def bkmResolventPairing (P : Mat) (p q : ℝ) (X Y : Mat) : ℝ :=
  ∫ s in Ioi (0 : ℝ),
    (Matrix.trace (star X * twoSheetResolvent P p q s * Y *
      twoSheetResolvent P p q s)).re

/-- Real scaling of the two inputs pulls out the product of the scalars. -/
theorem bkmResolventPairing_real_smul (P : Mat) (p q : ℝ)
    (X Y : Mat) (a b : ℝ) :
    bkmResolventPairing P p q (a • X) (b • Y) =
      (a * b) * bkmResolventPairing P p q X Y := by
  unfold bkmResolventPairing
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  simpa only [mul_assoc, mul_left_comm] using
    (integral_const_mul (μ := volume.restrict (Ioi (0 : ℝ))) (a * b)
      (fun s : ℝ => (Matrix.trace
        (star X * twoSheetResolvent P p q s * Y * twoSheetResolvent P p q s)).re))

/-- The modular commutator's energy integrand is integrable, even before
requiring the original odd input to be Hermitian. -/
theorem integrableOn_modular_bkm_energy {P : Mat} (hP : IsStarProjection P)
    (A C : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ =>
      (Matrix.trace
        (star (comm (-CFC.log (twoSheet P p q)) (genPhi P A C)) *
          twoSheetResolvent P p q s *
          comm (-CFC.log (twoSheet P p q)) (genPhi P A C) *
          twoSheetResolvent P p q s)).re) (Ioi 0) := by
  have hJphi : genPhi P A (-C) = genJ P A C := by
    simp only [genPhi, genJ, coneMinus_neg, sub_eq_add_neg]
  have hcurrent : IntegrableOn (fun s : ℝ =>
      (Matrix.trace (star (genJ P A C) * twoSheetResolvent P p q s *
        genJ P A C * twoSheetResolvent P p q s)).re) (Ioi 0) := by
    simpa only [hJphi] using
      integrableOn_twoSheetResolvent_trace_left P hP.isIdempotentElem.eq
        A (-C) (star (genJ P A C)) hp hq
  simpa only [comm_neg_log_twoSheet_phi hP A C p q, star_smul, star_trivial,
    smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul, IntegrableOn] using
    hcurrent.const_mul
      ((-(Real.log p - Real.log q)) * (-(Real.log p - Real.log q)))

/-- The modular BKM energy reads the exact noncommutative idempotency defect. -/
theorem modular_bkm_energy_eq_defect_trace {P : Mat} (hP : IsStarProjection P)
    (A C : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hPhi : Matrix.IsHermitian (genPhi P A C)) :
    bkmResolventPairing P p q
      (comm (-CFC.log (twoSheet P p q)) (genPhi P A C))
      (comm (-CFC.log (twoSheet P p q)) (genPhi P A C)) =
      (Real.log p - Real.log q) ^ 2 * logDividedDifference p q *
        (Matrix.trace
          (InfoGeometry.Core.IdempotencyDefect.defect (P + genPhi P A C))).re := by
  have hJphi : genPhi P A (-C) = genJ P A C := by
    simp only [genPhi, genJ, coneMinus_neg, sub_eq_add_neg]
  have hcurrent : bkmResolventPairing P p q (genJ P A C) (genJ P A C) =
      logDividedDifference p q *
        (Matrix.trace
          (InfoGeometry.Core.IdempotencyDefect.defect (P + genPhi P A C))).re := by
    unfold bkmResolventPairing
    calc
      _ = logDividedDifference p q *
          (Matrix.trace (star (genJ P A C) * genJ P A C)).re := by
        simpa only [hJphi] using
          integral_twoSheetResolvent_trace_left P hP.isIdempotentElem.eq
            A (-C) (star (genJ P A C)) hp hq
      _ = _ := by rw [genJ_gram_eq_idempotencyDefect hP A C hPhi.isSelfAdjoint]
  simp only [comm_neg_log_twoSheet_phi hP A C p q]
  rw [bkmResolventPairing_real_smul, hcurrent]
  ring

/-- The same energy in the existing operator-valued `V` convention. -/
theorem modular_bkm_energy_eq_quadratic_trace {P : Mat} (hP : IsStarProjection P)
    (A C : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hPhi : Matrix.IsHermitian (genPhi P A C)) :
    bkmResolventPairing P p q
      (comm (-CFC.log (twoSheet P p q)) (genPhi P A C))
      (comm (-CFC.log (twoSheet P p q)) (genPhi P A C)) =
      (Real.log p - Real.log q) ^ 2 * logDividedDifference p q *
        (Matrix.trace (genV P A C)).re := by
  rw [modular_bkm_energy_eq_defect_trace hP A C hp hq hPhi]
  have hdef : InfoGeometry.Core.IdempotencyDefect.defect (P + genPhi P A C) =
      genV P A C := by
    exact InfoGeometry.Core.PeirceDefect.defect_add_coupled hP.isIdempotentElem
      (u := conePlus P A) (v := coneMinus P C) ⟨A, rfl⟩ ⟨C, rfl⟩
  rw [hdef]

/-- The modular action scales the original BKM energy by the squared log jump. -/
theorem modular_bkm_energy_eq_log_jump_sq_mul {P : Mat} (hP : IsStarProjection P)
    (A C : Mat) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hPhi : Matrix.IsHermitian (genPhi P A C)) :
    bkmResolventPairing P p q
      (comm (-CFC.log (twoSheet P p q)) (genPhi P A C))
      (comm (-CFC.log (twoSheet P p q)) (genPhi P A C)) =
      (Real.log p - Real.log q) ^ 2 *
        bkmResolventPairing P p q (genPhi P A C) (genPhi P A C) := by
  rw [modular_bkm_energy_eq_quadratic_trace hP A C hp hq hPhi]
  have hquadratic : bkmResolventPairing P p q (genPhi P A C) (genPhi P A C) =
      logDividedDifference p q * (Matrix.trace (genV P A C)).re := by
    unfold bkmResolventPairing
    rw [hPhi.star_eq]
    exact integral_twoSheetResolvent_quadratic_trace
      P hP.isIdempotentElem.eq A C hp hq
  rw [hquadratic]
  exact mul_assoc _ _ _

/-- At equal positive weights, the modular action stops but the metric is
strictly positive on every nonzero Hermitian odd input. -/
theorem isotropic_bkm_positive_modular_zero {P : Mat} (hP : IsStarProjection P)
    (A C : Mat) {p : ℝ} (hp : 0 < p)
    (hPhi : Matrix.IsHermitian (genPhi P A C)) (hne : genPhi P A C ≠ 0) :
    bkmResolventPairing P p p (genPhi P A C) (genPhi P A C) =
        p⁻¹ * (Matrix.trace (genV P A C)).re ∧
      0 < bkmResolventPairing P p p (genPhi P A C) (genPhi P A C) ∧
      comm (-CFC.log (twoSheet P p p)) (genPhi P A C) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold bkmResolventPairing
    rw [hPhi.star_eq, integral_twoSheetResolvent_quadratic_trace
      P hP.isIdempotentElem.eq A C hp hp, logDividedDifference_self]
  · unfold bkmResolventPairing
    rw [hPhi.star_eq]
    exact integral_twoSheetResolvent_quadratic_pos
      P hP.isIdempotentElem.eq A C hp hp hPhi hne
  · exact (comm_neg_log_twoSheet_phi_eq_zero_iff hP A C hp hp).2 (Or.inl rfl)

end InfoGeometry.OperatorAlgebra.PeirceSpine
