import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.EntropicInference

open scoped BigOperators ENNReal

/-!
# Finite Bipartite Surprisal

This file separates the finite probability identities from their
noncommutative operator realization.  Local surprisal operators are embedded
linearly into a common bipartite operator carrier; no diagonal matrix or
Kronecker-coordinate presentation is assumed.
-/

namespace InfoGeometry.Canonical.FiniteBipartiteSurprisal

open InfoGeometry

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Independent product law, built through the canonical finite PMF assembly. -/
noncomputable def productFinProb (p : FinProb A) (q : FinProb B) :
    FinProb (A × B) :=
  EntropicInference.assemble p (fun _ => q)

@[simp] theorem productFinProb_apply
    (p : FinProb A) (q : FinProb B) (a : A) (b : B) :
    productFinProb p q (a, b) = p a * q b := by
  exact EntropicInference.assemble_apply p (fun _ => q) a b

private theorem pmf_toReal_ne_zero
    (p : FinProb A) (a : A) (ha : p a ≠ 0) :
    (p a).toReal ≠ 0 := by
  rw [ENNReal.toReal_ne_zero]
  exact ⟨ha, ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one p a) ENNReal.one_lt_top)⟩

/-- Pointwise surprisal is additive on a faithful independent product law. -/
theorem surprisal_productFinProb
    (p : FinProb A) (q : FinProb B)
    (hp : ∀ a, p a ≠ 0) (hq : ∀ b, q b ≠ 0)
    (a : A) (b : B) :
    surprisal (productFinProb p q) (a, b) =
      surprisal p a + surprisal q b := by
  unfold surprisal log_density
  rw [productFinProb_apply, ENNReal.toReal_mul,
    Real.log_mul (pmf_toReal_ne_zero p a (hp a))
      (pmf_toReal_ne_zero q b (hq b))]
  ring

/-! ## Correlation readout for a general finite joint law -/

/-- First marginal of a finite joint law. -/
noncomputable def marginalA (r : FinProb (A × B)) : FinProb A :=
  EntropicInference.marginal_x r

/-- Second marginal of a finite joint law. -/
noncomputable def marginalB (r : FinProb (A × B)) : FinProb B :=
  EntropicInference.marginal_theta r

@[simp] theorem marginalA_apply (r : FinProb (A × B)) (a : A) :
    marginalA r a = ∑ b : B, r (a, b) := by
  exact EntropicInference.marginal_x_apply_sum r a

@[simp] theorem marginalB_apply (r : FinProb (A × B)) (b : B) :
    marginalB r b = ∑ a : A, r (a, b) := by
  letI : DecidableEq B := Classical.decEq B
  rw [marginalB, EntropicInference.marginal_theta, PMF.map_apply, tsum_fintype,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a _
  calc
    (∑ x : B, if b = (a, x).2 then r (a, x) else 0) =
        (if b = (a, b).2 then r (a, b) else 0) := by
      apply Finset.sum_eq_single b
      · intro x _ hxb
        simp [Ne.symm hxb]
      · simp
    _ = r (a, b) := by simp

/-- Mutual information in entropy-difference form. -/
noncomputable def entropyMutualInformation (r : FinProb (A × B)) : ℝ :=
  entropy (marginalA r) + entropy (marginalB r) - entropy r

/-! ## Noncommutative operator realization -/

variable {OpA OpB OpAB : Type*}
variable [AddCommGroup OpA] [Module ℝ OpA]
variable [AddCommGroup OpB] [Module ℝ OpB]
variable [AddCommGroup OpAB] [Module ℝ OpAB]

/-- Sum of the two locally embedded surprisal operators. -/
def productSurprisalOperator
    (embedA : OpA →ₗ[ℝ] OpAB) (embedB : OpB →ₗ[ℝ] OpAB)
    (KA : OpA) (KB : OpB) : OpAB :=
  embedA KA + embedB KB

/-- Positive-orientation total-correlation operator `K_A + K_B - K_AB`. -/
def correlationSurprisalOperator
    (embedA : OpA →ₗ[ℝ] OpAB) (embedB : OpB →ₗ[ℝ] OpAB)
    (KA : OpA) (KB : OpB) (KAB : OpAB) : OpAB :=
  productSurprisalOperator embedA embedB KA KB - KAB

/-- Product-state logarithmic additivity is exactly vanishing correlation defect. -/
theorem correlationSurprisalOperator_eq_zero_iff
    (embedA : OpA →ₗ[ℝ] OpAB) (embedB : OpB →ₗ[ℝ] OpAB)
    (KA : OpA) (KB : OpB) (KAB : OpAB) :
    correlationSurprisalOperator embedA embedB KA KB KAB = 0 ↔
      KAB = productSurprisalOperator embedA embedB KA KB := by
  unfold correlationSurprisalOperator
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    exact sub_eq_zero.mpr h.symm

/-- Any linear state evaluates the correlation operator as a difference. -/
theorem stateReadout_correlationSurprisalOperator
    (ω : OpAB →ₗ[ℝ] ℝ)
    (embedA : OpA →ₗ[ℝ] OpAB) (embedB : OpB →ₗ[ℝ] OpAB)
    (KA : OpA) (KB : OpB) (KAB : OpAB) :
    ω (correlationSurprisalOperator embedA embedB KA KB KAB) =
      ω (embedA KA) + ω (embedB KB) - ω KAB := by
  simp [correlationSurprisalOperator, productSurprisalOperator]

/--
If the state readouts of the three surprisal operators are the two marginal
entropies and the joint entropy, then the noncommutative correlation operator
reads out as mutual information.
-/
theorem stateReadout_correlationSurprisalOperator_eq_mutualInformation
    (r : FinProb (A × B))
    (ω : OpAB →ₗ[ℝ] ℝ)
    (embedA : OpA →ₗ[ℝ] OpAB) (embedB : OpB →ₗ[ℝ] OpAB)
    (KA : OpA) (KB : OpB) (KAB : OpAB)
    (hA : ω (embedA KA) = entropy (marginalA r))
    (hB : ω (embedB KB) = entropy (marginalB r))
    (hAB : ω KAB = entropy r) :
    ω (correlationSurprisalOperator embedA embedB KA KB KAB) =
      entropyMutualInformation r := by
  rw [stateReadout_correlationSurprisalOperator, hA, hB, hAB]
  rfl

end InfoGeometry.Canonical.FiniteBipartiteSurprisal
