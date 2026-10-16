/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw

/-!
# Finite Markov cylinder observables in a native module colimit

At stage `n`, observables are real functions on successor paths of length
`n`. Pullback along prefix restriction embeds each stage into the next. The
production finite trajectory laws are prefix-consistent, so their finite-stage
expectations form a compatible cocone. The cocone descends through Mathlib's
`ModuleCat` colimit. This constructs a linear functional on the algebraic
colimit of finite cylinder observables; it makes no infinite-path measure or
convergence claim.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.FiniteMarkovObservableColimit

open CategoryTheory CategoryTheory.Limits MeasureTheory ProbabilityTheory
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Real-valued observables on successor paths of a fixed finite horizon. -/
abbrev PathObservable (n : ℕ) (ι : Type) := (Fin n → ι) → ℝ

local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := inferInstance
/-- Restrict a successor path of length `n + 1` to its first `n` entries. -/
def pathPrefix {n : ℕ} (p : Fin (n + 1) → ι) : Fin n → ι :=
  fun k => p k.castSucc

omit [Fintype ι] [DecidableEq ι] in
/-- Every finite path extends by one state, so prefix restriction is
surjective when the state carrier is nonempty. -/
theorem pathPrefix_surjective (n : ℕ) :
    Function.Surjective (pathPrefix (ι := ι) (n := n)) := by
  obtain ⟨a⟩ := ‹Nonempty ι›
  intro p
  refine ⟨Fin.lastCases a p, ?_⟩
  funext k
  simp [pathPrefix]

/-- Pull a finite cylinder observable back along the path-prefix map. -/
def pathPrefixPullback (n : ℕ) :
    PathObservable n ι →ₗ[ℝ] PathObservable (n + 1) ι where
  toFun f p := f (pathPrefix p)
  map_add' f g := by
    funext p
    rfl
  map_smul' c f := by
    funext p
    rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Prefix pullback is injective: a nonempty carrier lets every shorter path
be extended to a successor path. -/
theorem pathPrefixPullback_injective (n : ℕ) :
    Function.Injective (pathPrefixPullback (ι := ι) n) := by
  intro f g h
  funext p
  obtain ⟨q, hq⟩ := pathPrefix_surjective (ι := ι) n p
  have hp := congrFun h q
  change f (pathPrefix q) = g (pathPrefix q) at hp
  rw [hq] at hp
  exact hp

/-- The sequence of finite path-observable modules with prefix-pullback
bonding maps. This is a diagram in `ModuleCat ℝ`. -/
abbrev pathObservableStageFunctor (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ℕ ⥤ ModuleCat ℝ :=
  Functor.ofSequence (fun n => ModuleCat.ofHom (pathPrefixPullback (ι := ι) n))

/-- Expectation of a finite path observable under the production
successor-coordinate law. -/
def finitePathObservableExpectation
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (n : ℕ) (i : ι) : PathObservable n ι →ₗ[ℝ] ℝ where
  toFun f := ∫ p, f p ∂finiteTrajectorySuccessorLaw P hP n i
  map_add' f g := by
    rw [finiteTrajectorySuccessorLaw_eq_successorPathPMF_toMeasure,
      PMF.integral_eq_sum, PMF.integral_eq_sum, PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    rw [finiteTrajectorySuccessorLaw_eq_successorPathPMF_toMeasure,
      PMF.integral_eq_sum, PMF.integral_eq_sum]
    simp only [smul_eq_mul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      (∑ p, (successorPathPMF P hP n i p).toReal * (c * f p)) =
          ∑ p, c * ((successorPathPMF P hP n i p).toReal * f p) := by
        apply Finset.sum_congr rfl
        intro p hp
        calc
          _ = ((successorPathPMF P hP n i p).toReal * c) * f p := by
            rw [mul_assoc]
          _ = (c * (successorPathPMF P hP n i p).toReal) * f p := by
            rw [mul_comm (successorPathPMF P hP n i p).toReal c]
          _ = c * ((successorPathPMF P hP n i p).toReal * f p) := by
            rw [mul_assoc]
      _ = c * ∑ p, (successorPathPMF P hP n i p).toReal * f p := by
        rw [Finset.mul_sum]

omit [Nonempty ι] in
/-- Pullback along prefix restriction preserves expectation, by the
production trajectory law's finite marginal-consistency theorem. -/
theorem finitePathObservableExpectation_prefix
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι)
    (n : ℕ) (i : ι) (f : PathObservable n ι) :
    finitePathObservableExpectation P hP (n + 1) i
        (pathPrefixPullback (ι := ι) n f) =
      finitePathObservableExpectation P hP n i f := by
  change (∫ p, f (pathPrefix p) ∂finiteTrajectorySuccessorLaw P hP (n + 1) i) =
    ∫ p, f p ∂finiteTrajectorySuccessorLaw P hP n i
  rw [← finiteTrajectorySuccessorLaw_prefix P hP n i]
  exact (MeasureTheory.integral_map_of_stronglyMeasurable
    (Measurable.of_discrete : Measurable (pathPrefix (ι := ι) (n := n)))
    StronglyMeasurable.of_discrete).symm

/-- The native filtered colimit of finite path-observable modules. -/
abbrev PathObservableColimit (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] :=
  colimit (pathObservableStageFunctor ι)

/-- Constant target diagram for the compatible scalar expectations. -/
abbrev scalarExpectationTargetFunctor : ℕ ⥤ ModuleCat ℝ :=
  (Functor.const ℕ).obj (ModuleCat.of ℝ ℝ)

/-- The finite-stage expectations form a natural transformation into the
constant scalar module diagram. -/
def pathObservableExpectationNatTrans
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) :
    pathObservableStageFunctor ι ⟶ scalarExpectationTargetFunctor :=
  NatTrans.ofSequence
    (fun n => ModuleCat.ofHom (finitePathObservableExpectation P hP n i))
    (by
      intro n
      rw [Functor.ofSequence_map_homOfLE_succ]
      change ModuleCat.ofHom (pathPrefixPullback (ι := ι) n) ≫
          ModuleCat.ofHom (finitePathObservableExpectation P hP (n + 1) i) =
        ModuleCat.ofHom (finitePathObservableExpectation P hP n i) ≫ 𝟙 _
      rw [Category.comp_id, ← ModuleCat.ofHom_comp]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact finitePathObservableExpectation_prefix P hP n i f)

/-- The compatible expectation cocone over the actual `ModuleCat` sequence
diagram. -/
def pathObservableExpectationCocone
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) :
    Cocone (pathObservableStageFunctor ι) where
  pt := ModuleCat.of ℝ ℝ
  ι := pathObservableExpectationNatTrans P hP i

/-- Descend the finite-stage production expectations to the native
categorical colimit of path observables. -/
def pathObservableColimitExpectation
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι) :
    PathObservableColimit ι ⟶ ModuleCat.of ℝ ℝ :=
  colimit.desc (pathObservableStageFunctor ι)
    (pathObservableExpectationCocone P hP i)

/-- Readback of the descended functional on each finite stage is exactly the
production finite-horizon expectation. -/
theorem pathObservableColimitExpectation_stage
    (P : Matrix ι ι ℝ) (hP : P ∈ Matrix.rowStochastic ℝ ι) (i : ι)
    (n : ℕ) (f : PathObservable n ι) :
    (pathObservableColimitExpectation P hP i).hom
        ((colimit.ι (pathObservableStageFunctor ι) n).hom f) =
      finitePathObservableExpectation P hP n i f := by
  have h := congrArg (fun g => g.hom f)
    (colimit.ι_desc (pathObservableExpectationCocone P hP i) n)
  exact h

end InfoGeometry.QuantumContext.FiniteMarkovObservableColimit
