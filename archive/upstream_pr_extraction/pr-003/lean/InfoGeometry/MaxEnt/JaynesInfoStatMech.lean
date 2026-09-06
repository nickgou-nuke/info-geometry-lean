import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import InfoGeometry.Basic
import InfoGeometry.TransformationGroups

open scoped BigOperators


universe u v

namespace JaynesInfoStatMech
open scoped BigOperators
variable {Ω : Type u} [Fintype Ω]

/-!
## 1. Finite probability distributions and Shannon entropy
(Jaynes 1957; Shannon entropy as the unique measure of “uncertainty”.)
-/

/-- A probability distribution on a finite sample space `Ω`, valued in `ℝ`. -/
structure ProbDist (Ω : Type u) [Fintype Ω] where
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_one : (∑ ω, p ω) = 1

/-- An (ℝ-valued) observable on `Ω`. -/
abbrev Observable (Ω : Type u) := Ω → ℝ

/-- Expectation `E_P[f] = ∑ ω p(ω) f(ω)` on a finite space. -/
noncomputable def expectedValue (P : ProbDist Ω) (f : Observable Ω) : ℝ :=
  ∑ ω, P.p ω * f ω

/--
Shannon entropy (Jaynes uses `K` as a constant; information-theory often takes `K = 1`):
`H_K(P) = -K * ∑ ω p(ω) log(p(ω))`.
-/
noncomputable def shannonEntropy (P : ProbDist Ω) (K : ℝ := 1) : ℝ :=
  -K * ∑ ω, P.p ω * Real.log (P.p ω)
/-!
## 2. MaxEnt constraints (index by a finite type, not a `List`)
This is the canonical Mathlib style: use an index type `ι` with `[Fintype ι]`.
-/

/-- A family of expectation constraints: observables `f r` with target values `d r`. -/
structure ConstraintFamily (ι : Type v) (Ω : Type u) where
  f : ι → Observable Ω
  d : ι → ℝ

variable {ι : Type v} [Fintype ι]

/-- `P` is feasible if it satisfies all constraints `E_P[f r] = d r`. -/
def IsFeasible (P : ProbDist Ω) (C : ConstraintFamily ι Ω) : Prop :=
  ∀ r, expectedValue P (C.f r) = C.d r

/-!
## 3. The exponential family (partition function, MaxEnt distribution)
Jaynes’ general solution: `p(ω) ∝ exp(-∑ r λ_r f_r(ω))`.
-/





section MaxEnt
variable [Nonempty Ω]

/-- Unnormalized weight `w(ω;lam) = exp(-∑ r lam_r f_r(ω))`. -/
noncomputable def weight (C : ConstraintFamily ι Ω) (lam : ι → ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(∑ r, (lam r) * (C.f r ω)))

/-- Partition function `Z(lam) = ∑ ω exp(-∑ r lam_r f_r(ω))`. -/
noncomputable def partitionFunction (C : ConstraintFamily ι Ω) (lam : ι → ℝ) : ℝ :=
  ∑ ω, weight C lam ω

/-- `Z(lam) > 0` on a nonempty finite space since it is a sum of positive exponentials. -/
theorem partitionFunction_pos (C : ConstraintFamily ι Ω) (lam : ι → ℝ) :
    0 < partitionFunction C lam := by
  classical
  simpa [partitionFunction, weight] using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Ω))
      (f := fun ω => Real.exp (-(∑ r, lam r * C.f r ω)))
      (by intro ω _; exact Real.exp_pos _) Finset.univ_nonempty)

/-- log-partition `log Z(lam)` --/
noncomputable def logZ (C : ConstraintFamily ι Ω) (lam : ι → ℝ) : ℝ :=
  Real.log (partitionFunction C lam)

/-- MaxEnt / Gibbs distribution: p(ω) = w(ω)/Z. -/
noncomputable def maxEntDist (C : ConstraintFamily ι Ω) (lam : ι → ℝ) : ProbDist Ω := by
  classical
  have Z_pos : 0 < partitionFunction C lam := partitionFunction_pos (C := C) (lam := lam)
  have Z_ne : partitionFunction C lam ≠ 0 := ne_of_gt Z_pos
  exact {
    p := fun ω => weight C lam ω / partitionFunction C lam,
    nonneg := fun ω => div_nonneg (le_of_lt (Real.exp_pos (-(∑ r, lam r * C.f r ω)))) (le_of_lt Z_pos),
    sum_one := by
      calc
        (∑ ω, weight C lam ω / partitionFunction C lam)
          = (∑ ω, weight C lam ω) / partitionFunction C lam := (Finset.sum_div (s := (Finset.univ : Finset Ω)) (f := fun ω => weight C lam ω) (a := partitionFunction C lam)).symm
        _ = partitionFunction C lam / partitionFunction C lam := rfl
        _ = 1 := div_self Z_ne
  }

end MaxEnt
section StatMech
variable [Nonempty Ω]

/-- One-observable constraint family indexed by `Unit`. -/
def energyFamily (E : Observable Ω) (U : ℝ := 0) : ConstraintFamily Unit Ω :=
  { f := fun _ => E, d := fun _ => U }

/-- In statistical mechanics, `β = 1/(kT)` (parameters `k,T`). -/
noncomputable def beta (k T : ℝ) : ℝ :=
  1 / (k * T)

/-- Boltzmann distribution: MaxEnt with a single observable (energy) and multiplier `β`. -/
noncomputable def boltzmannDist (E : Observable Ω) (b : ℝ) : ProbDist Ω :=
  maxEntDist (energyFamily E) (fun _ => b)

/-- Helmholtz free energy `F = -k T * log Z(β)`. -/
noncomputable def helmholtzFreeEnergy (E : Observable Ω) (k T : ℝ) : ℝ :=
  -k * T * Real.log (partitionFunction (energyFamily E) (fun _ => beta k T))

end StatMech

end JaynesInfoStatMech
