import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.FiniteGibbsQGTRealization

open InfoGeometry.QuantumGeometry.Projective
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

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

end InfoGeometry.Canonical.FiniteGibbsQGTRealization
