/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteGibbsQGTRealization

noncomputable section

namespace InfoGeometry.Canonical.FiniteGibbsQGTRealization

open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie
open InfoGeometry.QuantumGeometry.Projective

variable {State : Type*} [Fintype State] [Nonempty State]

/-- The finite classical Gibbs realization has a real QGT, before taking its real readout. -/
theorem centeredGibbsObservable_qgt_eq_fisher_complex
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i j : Fin 2) :
    QGT (normalizedGibbsState D beta)
      (centeredGibbsObservable D beta i)
      (centeredGibbsObservable D beta j) =
      (fisherSouriauMatrix D beta i j : ℂ) := by
  have hi := centeredGibbsObservable_expectation_zero D beta i
  have hj := centeredGibbsObservable_expectation_zero D beta j
  have hih :
      @inner ℂ (GibbsHilbert State) _
          (centeredGibbsObservable D beta i (gibbsVector D beta))
        (centeredGibbsObservable D beta j (gibbsVector D beta)) =
        (fisherSouriauMatrix D beta i j : ℂ) := by
    classical
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hi' :
        (centeredGibbsObservable D beta i (gibbsVector D beta)).ofLp =
          fun x => (D.momentMap x i - souriauChargeMean D beta i : ℂ) *
            (gibbsVector D beta).ofLp x := by
      funext x
      exact centeredGibbsObservable_ofLp_apply D beta i
        (gibbsVector D beta) x
    have hj' :
        (centeredGibbsObservable D beta j (gibbsVector D beta)).ofLp =
          fun x => (D.momentMap x j - souriauChargeMean D beta j : ℂ) *
            (gibbsVector D beta).ofLp x := by
      funext x
      exact centeredGibbsObservable_ofLp_apply D beta j
        (gibbsVector D beta) x
    rw [hi', hj']
    simp [dotProduct, gibbsVector, Complex.star_def]
    have hnonneg : ∀ x : State, 0 ≤ realGibbsWeight D beta x := by
      intro x
      unfold realGibbsWeight
      exact div_nonneg (Real.exp_pos _).le
        (realGibbsPartition_pos D beta).le
    have hroot (x : State) :
        (↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
            ↑(Real.sqrt (realGibbsWeight D beta x)) =
          (realGibbsWeight D beta x : ℂ) := by
      rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt (hnonneg x)]
    change ∑ x : State,
        (D.momentMap x j - souriauChargeMean D beta j : ℂ) *
            (↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
          ((D.momentMap x i - souriauChargeMean D beta i : ℂ) *
            ↑(Real.sqrt (realGibbsWeight D beta x))) = _
    have hterm (x : State) :
        (D.momentMap x j - souriauChargeMean D beta j : ℂ) *
            (↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
          ((D.momentMap x i - souriauChargeMean D beta i : ℂ) *
            ↑(Real.sqrt (realGibbsWeight D beta x))) =
          (realGibbsWeight D beta x : ℂ) *
            (D.momentMap x i - souriauChargeMean D beta i : ℂ) *
            (D.momentMap x j - souriauChargeMean D beta j : ℂ) := by
      calc
        _ = (D.momentMap x i - souriauChargeMean D beta i : ℂ) *
              (D.momentMap x j - souriauChargeMean D beta j : ℂ) *
              ((↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
                ↑(Real.sqrt (realGibbsWeight D beta x))) := by ring
        _ = _ := by
          rw [hroot]
          ring
    simp_rw [hterm]
    unfold fisherSouriauMatrix
    norm_cast
  have hi0 :
      @inner ℂ (GibbsHilbert State) _
          (centeredGibbsObservable D beta i (gibbsVector D beta))
          (gibbsVector D beta) = 0 := by
    rw [← inner_conj_symm]
    rw [hi]
    simp
  have hj0 :
      @inner ℂ (GibbsHilbert State) _
          (centeredGibbsObservable D beta j (gibbsVector D beta))
          (gibbsVector D beta) = 0 := by
    rw [← inner_conj_symm]
    rw [hj]
    simp
  change
    (@inner ℂ (GibbsHilbert State) _
        (centeredGibbsObservable D beta i (gibbsVector D beta))
        (centeredGibbsObservable D beta j (gibbsVector D beta)) -
      @inner ℂ (GibbsHilbert State) _
        (centeredGibbsObservable D beta i (gibbsVector D beta))
        (gibbsVector D beta) *
      @inner ℂ (GibbsHilbert State) _
        (gibbsVector D beta)
        (centeredGibbsObservable D beta j (gibbsVector D beta))) = _
  rw [hih, hi0, hj]
  norm_num

/-- The Berry channel vanishes for the finite classical Gibbs realization. -/
theorem centeredGibbsObservable_berry_curvature_eq_zero
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i j : Fin 2) :
    berryCurvature (normalizedGibbsState D beta)
      (centeredGibbsObservable D beta i)
      (centeredGibbsObservable D beta j) = 0 := by
  rw [berryCurvature]
  rw [centeredGibbsObservable_qgt_eq_fisher_complex]
  norm_num

end InfoGeometry.Canonical.FiniteGibbsQGTRealization
