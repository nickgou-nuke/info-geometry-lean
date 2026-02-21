import InfoGeometry.MaxEnt.JaynesInfoStatMech
import Mathlib.Tactic

open JaynesInfoStatMech

-- Test: maxEntDist is a valid probability distribution
example {Ω : Type} [Fintype Ω] [Nonempty Ω] {ι : Type} [Fintype ι]
  (C : ConstraintFamily ι Ω) (lam : ι → ℝ) :
  (∀ ω, 0 ≤ (maxEntDist C lam).p ω) ∧ (∑ ω, (maxEntDist C lam).p ω = 1) :=
by
  constructor
  · intro ω; exact (maxEntDist C lam).nonneg ω
  · exact (maxEntDist C lam).sum_one

-- Test: partitionFunction is positive
example {Ω : Type} [Fintype Ω] [Nonempty Ω] {ι : Type} [Fintype ι]
  (C : ConstraintFamily ι Ω) (lam : ι → ℝ) :
  0 < partitionFunction C lam :=
  partitionFunction_pos C lam

-- Test: boltzmannDist is a valid probability distribution
example {Ω : Type} [Fintype Ω] [Nonempty Ω] (E : Observable Ω) (b : ℝ) :
  (∀ ω, 0 ≤ (boltzmannDist E b).p ω) ∧ (∑ ω, (boltzmannDist E b).p ω = 1) :=
by
  constructor
  · intro ω; exact (boltzmannDist E b).nonneg ω
  · exact (boltzmannDist E b).sum_one
