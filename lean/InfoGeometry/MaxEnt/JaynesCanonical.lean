import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import InfoGeometry.Basic
import InfoGeometry.KL.Finite

open scoped BigOperators

universe u

namespace JaynesMaxEnt

variable {Ω : Type} [Fintype Ω]

/-!
### 1. Entropy and Probability Distributions
A (finite) probability distribution on `Ω` as a function `Ω → ℝ`
with nonnegativity and total mass `1`.
-/

structure ProbDist (Ω : Type) [Fintype Ω] where
  f : Ω → ℝ
  nonneg : ∀ i, 0 ≤ f i
  sum_one : (∑ i, f i) = 1

namespace ProbDist

variable {Ω : Type} [Fintype Ω]

/-- Convert local Jaynes probability distributions to the core `InfoGeometry` type. -/
def toInfoProbabilityDist (P : ProbDist Ω) : InfoGeometry.ProbabilityDist (α := Ω) :=
  { prob := P.f
    sum_one := P.sum_one
    nonneg := P.nonneg }

@[simp] lemma toInfoProbabilityDist_prob (P : ProbDist Ω) (i : Ω) :
    (P.toInfoProbabilityDist).prob i = P.f i := rfl

end ProbDist

/-- Discrete Shannon entropy: `H(P) = - ∑ᵢ pᵢ log pᵢ`. -/
noncomputable def shannonEntropy (P : ProbDist Ω) : ℝ :=
  - ∑ i, P.f i * Real.log (P.f i)

/-!
### 2. Combinatorial Foundations (Multiplicity)
Multiplicity is encoded as a multinomial count derived from the count profile.
-/

/-- Total count encoded by a count profile. -/
noncomputable def totalCount (counts : Ω → ℕ) : ℕ :=
  ∑ i, counts i

/-- Multiplicity (multinomial count) for a finite count profile. -/
noncomputable def multiplicity (counts : Ω → ℕ) : ℕ :=
  Nat.multinomial Finset.univ counts

lemma multiplicity_pos (counts : Ω → ℕ) :
    0 < multiplicity counts := by
  simpa [multiplicity] using
    (Nat.multinomial_pos (s := (Finset.univ : Finset Ω)) (f := counts))

lemma multiplicity_spec (counts : Ω → ℕ) :
    (∏ i, Nat.factorial (counts i)) * multiplicity counts
      = Nat.factorial (totalCount counts) := by
  simpa [multiplicity, totalCount] using
    (Nat.multinomial_spec (s := (Finset.univ : Finset Ω)) (f := counts))

lemma multiplicity_one_le (counts : Ω → ℕ) :
    1 ≤ multiplicity counts :=
  Nat.succ_le_of_lt (multiplicity_pos counts)

/-- Log multiplicity. -/
noncomputable def logMultiplicity (counts : Ω → ℕ) : ℝ :=
  Real.log (multiplicity counts)

lemma logMultiplicity_nonneg (counts : Ω → ℕ) :
    0 ≤ logMultiplicity counts := by
  unfold logMultiplicity
  have h1 : (1 : ℝ) ≤ (multiplicity counts : ℝ) := by
    exact_mod_cast multiplicity_one_le counts
  exact Real.log_nonneg h1

/--
Asymptotic Equipartition Property (AEP), stated conceptually.

A fully formal proof typically uses Stirling's approximation and a `Filter.Tendsto`
argument on normalized frequencies; we register it here as an explicit proposition
interface while retaining the intended statement.
-/
def asymptotic_equipartition
    (counts : ℕ → Ω → ℕ) (P : ProbDist Ω) :
    Prop :=
  let _ := counts
  let _ := P
  True -- placeholder for actual asymptotic statement

/--
Asymptotic Equipartition Property as a theorem-ready proposition alias.
-/
def AsymptoticEquipartition
    (_counts : ℕ → Ω → ℕ) (_P : ProbDist Ω) :
    Prop :=
  asymptotic_equipartition _counts _P

/-!
### 3. Linear Constraints and the Feasible Set
-/

structure LinearConstraint (Ω : Type u) [Fintype Ω] where
  A : Ω → ℝ  -- observable
  d : ℝ      -- target expectation

/-- `P` satisfies constraint `C` if `∑ᵢ A(i) p(i) = d`. -/
def satisfiesConstraint (P : ProbDist Ω) (C : LinearConstraint Ω) : Prop :=
  (∑ i, C.A i * P.f i) = C.d

/-- Feasible set: distributions satisfying all constraints in a list. -/
def FeasibleSet (constraints : List (LinearConstraint Ω)) : Set (ProbDist Ω) :=
  { P | ∀ C ∈ constraints, satisfiesConstraint P C }

/-!
### 4. Entropy Concentration Theorem (Conceptual)
-/

/--
Conceptual statement placeholder: in the usual asymptotics, `2N * ΔH` behaves like `χ²(k)`.
We keep it abstract here.
-/
def entropy_concentration_bound : Prop :=
  True -- removed unused N, k, ΔH, F arguments

/-!
### 5. Maximum Entropy (Gibbs) Solution
-/

/-- Unnormalized partition function `Z(lam) = ∑ⱼ exp(-lam Aⱼ)`. -/
noncomputable def partitionFunction (C : LinearConstraint Ω) (lam : ℝ) : ℝ :=
  ∑ j, Real.exp (-lam * C.A j)

section Gibbs

variable [Nonempty Ω]

/-- `Z(lam) > 0` since it is a finite sum of strictly positive exponentials. -/
theorem partitionFunction_pos (C : LinearConstraint Ω) (lam : ℝ) :
    0 < partitionFunction C lam := by
  classical
  simpa [partitionFunction] using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Ω))
      (f := fun j => Real.exp (-lam * C.A j))
      (by
        intro j hj
        exact Real.exp_pos _)
      Finset.univ_nonempty)

/-- The canonical Gibbs distribution `p(i) = exp(-lam A(i)) / Z(lam)`. -/
noncomputable def gibbsDist (C : LinearConstraint Ω) (lam : ℝ) : ProbDist Ω := by
  classical
  have Z_pos : 0 < partitionFunction C lam := partitionFunction_pos (C := C) (lam := lam)
  refine
    { f := fun i => Real.exp (-lam * C.A i) / partitionFunction C lam
      nonneg := ?_
      sum_one := ?_ }
  · intro i
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt Z_pos)
  · have Z_ne : partitionFunction C lam ≠ 0 := ne_of_gt Z_pos
    calc
      (∑ i, Real.exp (-lam * C.A i) / partitionFunction C lam)
          = (∑ i, Real.exp (-lam * C.A i)) * (partitionFunction C lam)⁻¹ := by
              simp [div_eq_mul_inv, Finset.sum_mul]
      _ = partitionFunction C lam * (partitionFunction C lam)⁻¹ := by
            simp [partitionFunction]
      _ = 1 := by
            field_simp [Z_ne]

/-- Pointwise formula for the Gibbs distribution. -/
@[simp] lemma gibbsDist_f (C : LinearConstraint Ω) (lam : ℝ) (i : Ω) :
    (gibbsDist C lam).f i = Real.exp (-lam * C.A i) / partitionFunction C lam := rfl

/-- Pointwise positivity of the Gibbs distribution. -/
lemma gibbsDist_pos (C : LinearConstraint Ω) (lam : ℝ) (i : Ω) :
    0 < (gibbsDist C lam).f i := by
  rw [gibbsDist_f]
  exact div_pos (Real.exp_pos _) (partitionFunction_pos C lam)

/-- Log of the Gibbs point mass in affine form. -/
lemma log_gibbsDist_f (C : LinearConstraint Ω) (lam : ℝ) (i : Ω) :
    Real.log ((gibbsDist C lam).f i)
      = -lam * C.A i - Real.log (partitionFunction C lam) := by
  rw [gibbsDist_f]
  have hnum : Real.exp (-lam * C.A i) ≠ 0 := (Real.exp_pos _).ne'
  have hden : partitionFunction C lam ≠ 0 := (partitionFunction_pos C lam).ne'
  rw [Real.log_div hnum hden]
  simp

/-- Cross-entropy against the Gibbs law under the linear constraint. -/
lemma crossEntropyToGibbs_eq
    (C : LinearConstraint Ω) (lam : ℝ)
    (P : ProbDist Ω) (hP : satisfiesConstraint P C) :
    -∑ i, P.f i * Real.log ((gibbsDist C lam).f i)
      = lam * C.d + Real.log (partitionFunction C lam) := by
  have hP' : ∑ i, P.f i * C.A i = C.d := by
    calc
      ∑ i, P.f i * C.A i = ∑ i, C.A i * P.f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = C.d := hP
  have hsum :
      ∑ i, P.f i * (-lam * C.A i - Real.log (partitionFunction C lam))
        = ((-lam) * (∑ i, P.f i * C.A i))
          + ((-Real.log (partitionFunction C lam)) * (∑ i, P.f i)) := by
    calc
      ∑ i, P.f i * (-lam * C.A i - Real.log (partitionFunction C lam))
          = ∑ i, (P.f i * (-lam * C.A i) + P.f i * (-Real.log (partitionFunction C lam))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (∑ i, P.f i * (-lam * C.A i))
            + (∑ i, P.f i * (-Real.log (partitionFunction C lam))) := by
            rw [Finset.sum_add_distrib]
      _ = ((-lam) * (∑ i, P.f i * C.A i))
            + ((-Real.log (partitionFunction C lam)) * (∑ i, P.f i)) := by
            congr
            · calc
                ∑ i, P.f i * (-lam * C.A i)
                    = ∑ i, (-lam) * (P.f i * C.A i) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        ring
                _ = (-lam) * (∑ i, P.f i * C.A i) := by
                      simpa using
                        (Finset.mul_sum (s := Finset.univ) (a := -lam)
                          (f := fun i => P.f i * C.A i)).symm
            · calc
                ∑ i, P.f i * (-Real.log (partitionFunction C lam))
                    = ∑ i, (-Real.log (partitionFunction C lam)) * P.f i := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        ring
                _ = (-Real.log (partitionFunction C lam)) * (∑ i, P.f i) := by
                      simpa using
                        (Finset.mul_sum (s := Finset.univ)
                          (a := -Real.log (partitionFunction C lam))
                          (f := fun i => P.f i)).symm
  calc
    -∑ i, P.f i * Real.log ((gibbsDist C lam).f i)
        = -∑ i, P.f i * (-lam * C.A i - Real.log (partitionFunction C lam)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [log_gibbsDist_f]
    _ = -(((-lam) * (∑ i, P.f i * C.A i))
            + ((-Real.log (partitionFunction C lam)) * (∑ i, P.f i))) := by
          rw [hsum]
    _ = lam * C.d + Real.log (partitionFunction C lam) := by
          rw [hP', P.sum_one]
          ring

/-- Entropy value of the Gibbs law when it satisfies the target moment. -/
lemma entropy_gibbs_eq
    (C : LinearConstraint Ω) (lam : ℝ)
    (hGibbs : satisfiesConstraint (gibbsDist C lam) C) :
    shannonEntropy (gibbsDist C lam) = lam * C.d + Real.log (partitionFunction C lam) := by
  simpa [shannonEntropy] using
    crossEntropyToGibbs_eq (C := C) (lam := lam) (P := gibbsDist C lam) hGibbs

/--
Fundamental MaxEnt theorem (conceptual): if the Gibbs distribution satisfies the constraints,
it maximizes entropy over all feasible distributions.

A fully formal proof typically proceeds via nonnegativity of KL divergence.
-/
theorem gibbs_is_maximum_entropy
    (C : LinearConstraint Ω) (lam : ℝ)
    (P : ProbDist Ω) (hP : satisfiesConstraint P C)
    (hGibbs : satisfiesConstraint (gibbsDist (Ω := Ω) C lam) C) :
    shannonEntropy P ≤ shannonEntropy (gibbsDist (Ω := Ω) C lam) := by
  have hKLnonneg :
      0 ≤ InfoGeometry.klDiv
        P.toInfoProbabilityDist
        (gibbsDist (Ω := Ω) C lam).toInfoProbabilityDist := by
    apply InfoGeometry.KL.klDiv_nonneg_of_fullSupport
    intro i
    simpa using gibbsDist_pos (C := C) (lam := lam) i
  have hKLexpand :
      InfoGeometry.klDiv
        P.toInfoProbabilityDist
        (gibbsDist (Ω := Ω) C lam).toInfoProbabilityDist
        = ∑ i, P.f i * (Real.log (P.f i) - Real.log ((gibbsDist C lam).f i)) := by
    unfold InfoGeometry.klDiv InfoGeometry.expectation InfoGeometry.logDensity
    simp [ProbDist.toInfoProbabilityDist]
  have hkl :
      0 ≤ (∑ i, P.f i * Real.log (P.f i))
            - (∑ i, P.f i * Real.log ((gibbsDist C lam).f i)) := by
    have htmp := hKLnonneg
    rw [hKLexpand] at htmp
    have hsum :
        ∑ i, P.f i * (Real.log (P.f i) - Real.log ((gibbsDist C lam).f i))
          = (∑ i, P.f i * Real.log (P.f i))
            - (∑ i, P.f i * Real.log ((gibbsDist C lam).f i)) := by
      calc
        ∑ i, P.f i * (Real.log (P.f i) - Real.log ((gibbsDist C lam).f i))
            = ∑ i, (P.f i * Real.log (P.f i) - P.f i * Real.log ((gibbsDist C lam).f i)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (∑ i, P.f i * Real.log (P.f i))
              - (∑ i, P.f i * Real.log ((gibbsDist C lam).f i)) := by
              rw [Finset.sum_sub_distrib]
    exact hsum ▸ htmp
  have hP_le_cross :
      shannonEntropy P ≤ -∑ i, P.f i * Real.log ((gibbsDist C lam).f i) := by
    have hP_form : shannonEntropy P = -∑ i, P.f i * Real.log (P.f i) := by
      simp [shannonEntropy]
    linarith [hkl, hP_form]
  have hcross_P :
      -∑ i, P.f i * Real.log ((gibbsDist C lam).f i)
        = lam * C.d + Real.log (partitionFunction C lam) :=
    crossEntropyToGibbs_eq (C := C) (lam := lam) (P := P) hP
  have hEntropy_g :
      shannonEntropy (gibbsDist C lam) = lam * C.d + Real.log (partitionFunction C lam) :=
    entropy_gibbs_eq (C := C) (lam := lam) hGibbs
  calc
    shannonEntropy P ≤ -∑ i, P.f i * Real.log ((gibbsDist C lam).f i) := hP_le_cross
    _ = lam * C.d + Real.log (partitionFunction C lam) := hcross_P
    _ = shannonEntropy (gibbsDist C lam) := hEntropy_g.symm

end Gibbs

/-!
### 6. Time Series and Autocovariance
-/

/-- Empirical autocovariance of a real-valued time series for lag `k`. -/
noncomputable def empiricalAutocovariance (Y : ℕ → ℝ) (T : ℕ) (k : ℕ) : ℝ :=
  let N_terms := T - k + 1
  (1 / (T + 1 : ℝ)) * ∑ j ∈ Finset.range N_terms, Y j * Y (j + k)

/--
Conceptual predicate placeholder: “`P` corresponds to an autoregressive (AR) model”.
Replace `True` with your preferred formalization (e.g. existence of AR coefficients).
-/
def isAutoregressiveModel (P : ProbDist Ω) : Prop :=
  let _ := P
  True

end JaynesMaxEnt
