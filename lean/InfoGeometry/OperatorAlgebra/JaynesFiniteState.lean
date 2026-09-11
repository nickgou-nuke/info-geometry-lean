import InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Jaynes Finite Empirical States

This file isolates the finite empirical-state owner surface from
`ErlangenJaynesGromov`.

The constructions here are deliberately finite and algebraic:

* a finite sample is a `Fintype`-indexed family of normalized algebraic states;
* an empirical state is a normalized weighted average of that sample;
* invariance and transport are proved exactly at the finite level.

No convergence theorem, positivity theorem, or thermodynamic-limit uniqueness
claim is asserted here.
-/

noncomputable section

open scoped BigOperators
open InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov
open OperatorErlangenSystem

namespace InfoGeometry.OperatorAlgebra.JaynesFiniteState

universe uR uA uS uι

abbrev AlgebraicStateRA (R : Type uR) (A : Type uA)
    [CommSemiring R] [Semiring A] [Algebra R A] :=
  OperatorErlangenSystem.AlgebraicState
    (R := R) (A := A)

abbrev FiniteObservableSample (R : Type uR) (A : Type uA) (ι : Type uι)
    [CommSemiring R] [Semiring A] [Algebra R A] :=
  ι → AlgebraicStateRA R A

section

variable {R : Type uR} {A : Type uA} {S : Type uS} {ι : Type uι}
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [Monoid S] [Fintype ι]

/--
Finite empirical weighted average of a family of algebraic-state readouts.

This is the owner-side finite Jaynes averaging functional; no limiting theorem is
asserted.
-/
def finiteEmpiricalFunctional
    (weight : R)
    (sample : FiniteObservableSample R A ι) :
    A →ₗ[R] R :=
  OperatorErlangenSystem.empiricalWeightedFunctional
    (R := R) (A := A) (ι := ι) weight (fun i => (sample i).toLinearMap)

@[simp]
theorem finiteEmpiricalFunctional_apply
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (a : A) :
    finiteEmpiricalFunctional weight sample a = weight * ∑ i, sample i a := by
  simp [finiteEmpiricalFunctional,
    OperatorErlangenSystem.empiricalWeightedFunctional]

@[simp]
theorem finiteEmpiricalFunctional_map_add
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (a b : A) :
    finiteEmpiricalFunctional weight sample (a + b) =
      finiteEmpiricalFunctional weight sample a + finiteEmpiricalFunctional weight sample b := by
  simpa using (finiteEmpiricalFunctional weight sample).map_add a b

@[simp]
theorem finiteEmpiricalFunctional_map_smul
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (r : R) (a : A) :
    finiteEmpiricalFunctional weight sample (r • a) =
      r • finiteEmpiricalFunctional weight sample a := by
  simpa using (finiteEmpiricalFunctional weight sample).map_smul r a

/--
Normalized finite empirical average of a finite sample of algebraic states.

The hypothesis `hweight` is the exact finite normalization law.
-/
def finiteEmpiricalState
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (hweight : weight * (Fintype.card ι : R) = 1) :
    AlgebraicStateRA R A :=
  OperatorErlangenSystem.empiricalWeightedState
    (R := R) (A := A) (ι := ι) weight sample hweight

@[simp]
theorem finiteEmpiricalState_apply
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (hweight : weight * (Fintype.card ι : R) = 1)
    (a : A) :
    finiteEmpiricalState weight sample hweight a = weight * ∑ i, sample i a := by
  simpa [finiteEmpiricalState] using
    OperatorErlangenSystem.empiricalWeightedState_apply
      (R := R) (A := A) (ι := ι) weight sample hweight a

@[simp]
theorem finiteEmpiricalState_map_one
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (hweight : weight * (Fintype.card ι : R) = 1) :
    finiteEmpiricalState weight sample hweight (1 : A) = 1 := by
  simpa using (finiteEmpiricalState weight sample hweight).map_one

/-- Readout formula for the finite empirical state. -/
theorem finiteEmpiricalState_average_eval
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (hweight : weight * (Fintype.card ι : R) = 1)
    (a : A) :
    finiteEmpiricalState weight sample hweight a = weight * ∑ i, sample i a :=
  finiteEmpiricalState_apply weight sample hweight a

/--
Algebraic convex-combination form of the finite empirical state.

This is only the exact finite weighted-average identity; no positivity or order
structure is asserted.
-/
theorem finiteEmpiricalState_convex
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (hweight : weight * (Fintype.card ι : R) = 1)
    (a : A) :
    finiteEmpiricalState weight sample hweight a = weight * ∑ i, sample i a :=
  finiteEmpiricalState_average_eval weight sample hweight a

section Invariance

variable (E : OperatorErlangenSystem R A S)

/--
If every sampled state is invariant under the symmetry semigroup, then the
finite empirical average is invariant.
-/
theorem finiteEmpiricalState_invariant_of_pointwiseInvariant
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (hweight : weight * (Fintype.card ι : R) = 1)
    (hsample : ∀ i, E.IsStateInvariant (sample i)) :
    E.IsStateInvariant (finiteEmpiricalState weight sample hweight) := by
  rw [E.stateInvariant_iff_eval]
  intro s a
  have hi : ∀ i, sample i (E.act s a) = sample i a := by
    intro i
    exact (E.stateInvariant_iff_eval (ω := sample i)).mp (hsample i) s a
  simp [finiteEmpiricalState_apply, hi]

/--
Pullback along the symmetry action commutes with finite empirical averaging.
-/
theorem finiteEmpiricalState_transport_eq_average_transport
    (weight : R)
    (sample : FiniteObservableSample R A ι)
    (hweight : weight * (Fintype.card ι : R) = 1)
    (s : S) :
    E.pullbackState s (finiteEmpiricalState weight sample hweight) =
      finiteEmpiricalState weight (fun i => E.pullbackState s (sample i)) hweight := by
  ext a
  simp [finiteEmpiricalState_apply, E.pullbackState_apply]

end Invariance

/--
A bundled finite family of algebraic states together with its normalization law.

This is finite compatibility data for Jaynes averaging only; it is not yet the
Nat-indexed directed-system compatibility used in later transport files.
-/
structure FiniteStateCompatibleFamily where
  weight : R
  sample : FiniteObservableSample R A ι
  hweight : weight * (Fintype.card ι : R) = 1

namespace FiniteStateCompatibleFamily

/-- The normalized empirical average associated to the bundled finite family. -/
def averageState
    (F : FiniteStateCompatibleFamily (R := R) (A := A) (ι := ι)) :
    AlgebraicStateRA R A :=
  finiteEmpiricalState F.weight F.sample F.hweight

@[simp]
theorem averageState_apply
    (F : FiniteStateCompatibleFamily (R := R) (A := A) (ι := ι))
    (a : A) :
    F.averageState a = F.weight * ∑ i, F.sample i a := by
  simp [averageState, finiteEmpiricalState_apply]

@[simp]
theorem averageState_map_one
    (F : FiniteStateCompatibleFamily (R := R) (A := A) (ι := ι)) :
    F.averageState (1 : A) = 1 := by
  simpa using F.averageState.map_one

end FiniteStateCompatibleFamily

end

end InfoGeometry.OperatorAlgebra.JaynesFiniteState
