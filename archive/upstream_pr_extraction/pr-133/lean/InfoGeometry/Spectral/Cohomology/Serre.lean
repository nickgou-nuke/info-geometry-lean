import InfoGeometry.Spectral.Algebra.ExactCouple
import InfoGeometry.Spectral.Algebra.ConcreteIteratedExactCouple
import InfoGeometry.Spectral.Algebra.ExactCoupleFiltration
import InfoGeometry.Spectral.Algebra.SpectralSequence
import InfoGeometry.Spectral.Cohomology.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Algebraic Serre and Gysin owners

This module contains only the algebraic consequences that can be proved from
explicit exact-couple or exact-sequence data.  A fibration alone is not used to
manufacture a spectral sequence: constructing the Serre exact couple from a
topological fibration remains a separate theorem.
-/

namespace InfoGeometry.Spectral.Cohomology.Serre

open InfoGeometry.Spectral.Algebra
open InfoGeometry.Spectral.Cohomology.Basic

universe u

variable {R : Type u} [Ring R]
variable {D E : Z2 → Type u}
variable [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
variable [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]

/-- The first square-zero page supplied by an explicit Serre exact couple. -/
abbrev SerrePage
    (R : Type u) [Ring R]
    (E : Z2 → Type u)
    [∀ pq, AddCommGroup (E pq)] [∀ pq, Module R (E pq)] :=
  SpectralSequencePage R E shiftK

/--
An explicit exact couple determines its square-zero Serre page.  No convergence
claim is included: convergence requires a filtration and an abutment theorem.
-/
def serrePageOfExactCouple (C : ExactCouple R D E) : SerrePage R E :=
  C.toPage

@[simp]
theorem serrePageOfExactCouple_d
    (C : ExactCouple R D E) (pq : Z2) :
    (serrePageOfExactCouple C).d pq = C.differential pq :=
  rfl

/-- Exactness of the couple forces the induced Serre-page differential to square to zero. -/
theorem serrePageOfExactCouple_differential_sq_zero
    (C : ExactCouple R D E) (pq : Z2) :
    ((serrePageOfExactCouple C).d (shiftK pq)).comp
        ((serrePageOfExactCouple C).d pq) = 0 :=
  C.toPage_differential_sq_zero pq

/-- The `n`th genuine derived Serre page supplied by an explicit exact couple. -/
noncomputable abbrev IteratedSerrePage
    (C : ExactCouple R D E) (n : ℕ) (pq : Z2) :=
  C.IteratedPage n pq

/-- The degree equivalence of the differential on the `n`th Serre page. -/
noncomputable abbrev iteratedSerreDifferentialDegree
    (C : ExactCouple R D E) (n : ℕ) : Z2 ≃ Z2 :=
  C.iteratedDifferentialDegree n

/-- The differential on the `n`th genuine derived Serre page. -/
noncomputable def iteratedSerreDifferential
    (C : ExactCouple R D E) (n : ℕ) (pq : Z2) :
    (IteratedSerrePage C n pq : Type u) →ₗ[R]
      (IteratedSerrePage C n
        (iteratedSerreDifferentialDegree C n pq) : Type u) :=
  C.iteratedDifferential n pq

@[simp]
theorem IteratedSerrePage_zero
    (C : ExactCouple R D E) (pq : Z2) :
    IteratedSerrePage C 0 pq = ModuleCat.of R (E pq) :=
  C.IteratedPage_zero pq

@[simp]
theorem iteratedSerreDifferential_zero
    (C : ExactCouple R D E) (pq : Z2) :
    iteratedSerreDifferential C 0 pq = C.differential pq :=
  C.iteratedDifferential_zero pq

/-- Every genuine derived Serre-page differential squares to zero. -/
theorem iteratedSerreDifferential_comp
    (C : ExactCouple R D E) (n : ℕ) (pq : Z2) :
    (iteratedSerreDifferential C n
        (iteratedSerreDifferentialDegree C n pq)).comp
      (iteratedSerreDifferential C n pq) = 0 :=
  C.iteratedDifferential_comp_iteratedDifferential n pq

/-- Each successor Serre page is native homology of the preceding page. -/
theorem IteratedSerrePage_succ
    (C : ExactCouple R D E) (n : ℕ) (pq : Z2) :
    (C.iteratedGradedStage (n + 1)).E pq =
      ModuleCat.of R
        ((C.iteratedGradedStage n).couple.DirectDerivedE pq) :=
  C.IteratedPage_succ n pq

/-- On an iterated Serre stage where the following `k` map vanishes,
exactness identifies the corresponding page term with the associated graded
quotient of the stage's `D` image filtration. -/
noncomputable def iteratedSerreAssociatedGradedEquivOfKZero
    (C : ExactCouple R D E) (n : ℕ) (p : Z2)
    (hk :
      (C.iteratedGradedStage n).couple.k
        ((C.iteratedGradedStage n).jDeg
          ((C.iteratedGradedStage n).iDeg p)) = 0) :
    (C.iteratedGradedStage n).couple.associatedGraded 0
        ((C.iteratedGradedStage n).iDeg p) ≃ₗ[R]
      (IteratedSerrePage C n
        ((C.iteratedGradedStage n).jDeg
          ((C.iteratedGradedStage n).iDeg p)) : Type u) :=
  (C.iteratedGradedStage n).couple
    |>.associatedGradedZeroEquivEOfKZero p hk

/--
A three-term Gysin fragment is an actual exact sequence of additive groups.
Its maps and exactness property are mathematical data, rather than a `True`
placeholder.
-/
abbrev GysinSequence
    (A B C : Type*)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] :=
  ExactSequence A B C

/-- The canonical exact fragment `A --id--> A --0--> A`. -/
def identityZeroGysinSequence (A : Type*) [AddCommGroup A] :
    GysinSequence A A A :=
  ExactSequence.zero

@[simp]
theorem identityZeroGysinSequence_first
    (A : Type*) [AddCommGroup A] :
    (identityZeroGysinSequence A).f = AddMonoidHom.id A :=
  rfl

@[simp]
theorem identityZeroGysinSequence_second
    (A : Type*) [AddCommGroup A] :
    (identityZeroGysinSequence A).g = 0 :=
  rfl

/--
The finite graded additive model underlying the standard mod-two computation
of `ℝPⁿ`: one `ZMod 2` coefficient in every degree `0, ..., n`.

This definition deliberately does not claim the topological computation; that
requires a cellular cochain complex and a proof identifying its cohomology.
-/
abbrev ProjectiveSpaceModTwoAdditiveModel (n : ℕ) :=
  Fin (n + 1) → ZMod 2

/-- The model has one distinguished unit class in each admissible degree. -/
def projectiveSpaceModTwoBasisClass (n : ℕ) (k : Fin (n + 1)) :
    ProjectiveSpaceModTwoAdditiveModel n :=
  Pi.single k 1

@[simp]
theorem projectiveSpaceModTwoBasisClass_apply_same
    (n : ℕ) (k : Fin (n + 1)) :
    projectiveSpaceModTwoBasisClass n k k = 1 := by
  simp [projectiveSpaceModTwoBasisClass]

end InfoGeometry.Spectral.Cohomology.Serre
