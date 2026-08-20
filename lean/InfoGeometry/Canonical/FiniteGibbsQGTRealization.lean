import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.FiniteGibbsQGTRealization

open InfoGeometry.QuantumGeometry.Projective
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie

variable {State : Type*} [Fintype State] [Nonempty State]

abbrev GibbsHilbert (State : Type*) := EuclideanSpace ℂ State

def gibbsVector (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) : GibbsHilbert State :=
  WithLp.toLp 2 (fun x => (Real.sqrt (realGibbsWeight D beta x) : ℂ))

theorem gibbsVector_norm_sq (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) :
    @inner ℂ (GibbsHilbert State) _ (gibbsVector D beta) (gibbsVector D beta) = (1 : ℂ) := by
  classical
  have hnonneg : ∀ x : State, 0 ≤ realGibbsWeight D beta x := by
    intro x
    unfold realGibbsWeight
    exact div_nonneg (Real.exp_pos _).le
      (realGibbsPartition_pos D beta).le
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [gibbsVector, dotProduct]
  simp
  have hterm (x : State) :
      (↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
          ↑(Real.sqrt (realGibbsWeight D beta x)) =
        (realGibbsWeight D beta x : ℂ) := by
    rw [← Complex.ofReal_mul, ← sq]
    rw [Real.sq_sqrt (hnonneg x)]
  change ∑ x : State,
      (↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
        ↑(Real.sqrt (realGibbsWeight D beta x)) = (1 : ℂ)
  simp_rw [hterm]
  simpa using congrArg (fun r : ℝ => (r : ℂ)) (realGibbsWeight_sum_eq_one D beta)

def normalizedGibbsState (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) :
    NormalizedState (GibbsHilbert State) :=
  ⟨gibbsVector D beta, gibbsVector_norm_sq D beta⟩

def gibbsObservable (D : CartanSouriauDatum State) (i : Fin 2) :
    GibbsHilbert State →L[ℂ] GibbsHilbert State :=
  by
    classical
    exact LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (Matrix.diagonal (fun x => (D.momentMap x i : ℂ))))

theorem gibbsObservable_ofLp_apply (D : CartanSouriauDatum State) (i : Fin 2)
    (v : GibbsHilbert State) (x : State) :
    (gibbsObservable D i v).ofLp x =
      (D.momentMap x i : ℂ) * v.ofLp x := by
  classical
  change (Matrix.toEuclideanLin
      (Matrix.diagonal (fun x => (D.momentMap x i : ℂ))) v).ofLp x = _
  rw [Matrix.ofLp_toEuclideanLin_apply]
  rw [Matrix.mulVec_diagonal]


theorem gibbsObservable_inner_self (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ)
    (i j : Fin 2) :
    @inner ℂ (GibbsHilbert State) _
        (gibbsObservable D i (gibbsVector D beta))
        (gibbsObservable D j (gibbsVector D beta)) =
      (∑ x : State,
        realGibbsWeight D beta x * D.momentMap x i * D.momentMap x j : ℝ) := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have hi : (gibbsObservable D i (gibbsVector D beta)).ofLp =
      fun x => (D.momentMap x i : ℂ) * (gibbsVector D beta).ofLp x := by
    funext x
    exact gibbsObservable_ofLp_apply D i (gibbsVector D beta) x
  have hj : (gibbsObservable D j (gibbsVector D beta)).ofLp =
      fun x => (D.momentMap x j : ℂ) * (gibbsVector D beta).ofLp x := by
    funext x
    exact gibbsObservable_ofLp_apply D j (gibbsVector D beta) x
  rw [hi, hj]
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
    rw [← Complex.ofReal_mul, ← sq]
    rw [Real.sq_sqrt (hnonneg x)]
  have hterm (x : State) :
      (D.momentMap x j : ℂ) *
          (↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
          ((D.momentMap x i : ℂ) *
            (↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ)) =
        (realGibbsWeight D beta x : ℂ) *
          (D.momentMap x i : ℂ) * (D.momentMap x j : ℂ) := by
    calc
      _ = (D.momentMap x i : ℂ) * (D.momentMap x j : ℂ) *
          ((↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
            ↑(Real.sqrt (realGibbsWeight D beta x))) := by ring
      _ = (realGibbsWeight D beta x : ℂ) *
          (D.momentMap x i : ℂ) * (D.momentMap x j : ℂ) := by
        rw [hroot]
        ring
  simp_rw [hterm]

def centeredGibbsObservable (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ)
    (i : Fin 2) : GibbsHilbert State →L[ℂ] GibbsHilbert State := by
  classical
  exact LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin
      (Matrix.diagonal (fun x =>
        (D.momentMap x i - souriauChargeMean D beta i : ℂ))))

theorem centeredGibbsObservable_ofLp_apply
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2)
    (v : GibbsHilbert State) (x : State) :
    (centeredGibbsObservable D beta i v).ofLp x =
      (D.momentMap x i - souriauChargeMean D beta i : ℂ) * v.ofLp x := by
  classical
  change (Matrix.toEuclideanLin
      (Matrix.diagonal (fun x =>
        (D.momentMap x i - souriauChargeMean D beta i : ℂ))) v).ofLp x = _
  rw [Matrix.ofLp_toEuclideanLin_apply]
  rw [Matrix.mulVec_diagonal]

theorem centeredGibbsObservable_expectation_zero
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i : Fin 2) :
    @inner ℂ (GibbsHilbert State) _ (gibbsVector D beta)
      (centeredGibbsObservable D beta i (gibbsVector D beta)) = 0 := by
  classical
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [gibbsVector, centeredGibbsObservable, dotProduct,
    Matrix.mulVec_diagonal]
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
      (D.momentMap x i - souriauChargeMean D beta i : ℂ) *
        (↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
          ↑(Real.sqrt (realGibbsWeight D beta x)) = 0
  have hterm (x : State) :
      (D.momentMap x i - souriauChargeMean D beta i : ℂ) *
        (↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
          ↑(Real.sqrt (realGibbsWeight D beta x)) =
        (realGibbsWeight D beta x : ℂ) *
          (D.momentMap x i - souriauChargeMean D beta i : ℂ) := by
    calc
      _ = (D.momentMap x i - souriauChargeMean D beta i : ℂ) *
          ((↑(Real.sqrt (realGibbsWeight D beta x)) : ℂ) *
            ↑(Real.sqrt (realGibbsWeight D beta x))) := by ring
      _ = _ := by rw [hroot]; ring
  simp_rw [hterm]
  have hreal : ∑ x : State,
      realGibbsWeight D beta x *
        (D.momentMap x i - souriauChargeMean D beta i) = 0 := by
    unfold souriauChargeMean
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    rw [realGibbsWeight_sum_eq_one]
    ring
  have hcomplex := congrArg Complex.ofReal hreal
  simp_rw [← Complex.ofReal_sub, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum]
  simpa using hcomplex

theorem centeredGibbsObservable_qgt_real_eq_fisherSouriauMatrix
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (i j : Fin 2) :
    (QGT (normalizedGibbsState D beta)
      (centeredGibbsObservable D beta i)
      (centeredGibbsObservable D beta j)).re =
      fisherSouriauMatrix D beta i j := by
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
          (centeredGibbsObservable D beta j (gibbsVector D beta))).re = _
    rw [hih, hi0, hj]
    norm_num

end InfoGeometry.Canonical.FiniteGibbsQGTRealization
