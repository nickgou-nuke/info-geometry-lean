import Mathlib.Tactic
import Mathlib.Analysis.MellinTransform
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Analysis.MellinZetaScaling

Finite Mellin scaling bridge for the zeta factor.

This module proves the finite algebraic identity behind the multiplicative
Mellin character:

  M (∑_{k ∈ A} sample k f) = (∑_{k ∈ A} weight k) * M f.

The infinite identity

  M (∑_{k ≥ 1} f (k x)) (s) = ζ(s) * M(f) (s)

requires analytic convergence, Tonelli/Fubini interchange, and decay
hypotheses.  This module deliberately does not expose that infinite statement
as a property interface; only the finite orbit-sum identity below is owned here.

The intended interpretation is:

* Mellin dilation character `k ↦ k^{-s}` is the scalar shadow of projective
  scaling;
* finite orbit sums produce finite Dirichlet characters;
* the infinite orbit sum is later analytic work, not a theorem surface here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Analysis.MellinZetaScaling

/--
Abstract finite Mellin-scaling datum.

`sample n f` represents the multiplicative orbit action `x ↦ f(n * x)`.
`weight n` is the Mellin dilation character, usually `n^{-s}`.
`Mellin` is the transform/readout.
-/
@[rep_depth projective]
structure FiniteMellinScalingDatum
    (Func R : Type*) [AddCommMonoid Func] [CommSemiring R] where
  sample : ℕ → Func → Func
  weight : ℕ → R
  Mellin : Func → R

  /-- Finite additivity of the transform. -/
  map_sum :
    ∀ (A : Finset ℕ) (g : ℕ → Func),
      Mellin (Finset.sum A g) = Finset.sum A (fun n => Mellin (g n))

  /-- Mellin readout of a scaled sample is multiplication by its weight. -/
  Mellin_sample_eq_weight_mul :
    ∀ n f, Mellin (sample n f) = weight n * Mellin f

namespace FiniteMellinScalingDatum

variable {Func R : Type*} [AddCommMonoid Func] [CommSemiring R]
variable (D : FiniteMellinScalingDatum Func R)

/--
Finite Mellin orbit-sum factorization.

This is the finite, kernel-checkable part of the Cook identity.
-/
@[rep_depth projective]
theorem finite_sample_sum_factor
    (A : Finset ℕ)
    (f : Func) :
    D.Mellin (Finset.sum A (fun n => D.sample n f))
      =
    (Finset.sum A D.weight) * D.Mellin f := by
  rw [D.map_sum A (fun n => D.sample n f)]
  calc
    Finset.sum A (fun n => D.Mellin (D.sample n f))
        = Finset.sum A (fun n => D.weight n * D.Mellin f) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [D.Mellin_sample_eq_weight_mul n f]
    _ = Finset.sum A (fun n => D.Mellin f * D.weight n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [mul_comm]
    _ = D.Mellin f * Finset.sum A D.weight := by
          simpa using
            (Finset.mul_sum (s := A) (a := D.Mellin f) (f := D.weight)).symm
    _ = (Finset.sum A D.weight) * D.Mellin f := by
          rw [mul_comm]

/--
Finite multiplicative Mellin orbit-character factorization.

The additive finite orbit sum gives a Dirichlet-weight sum; the product over
orbit labels gives the multiplicative character carried by the same scaling
weights.
-/
@[rep_depth projective]
theorem finite_sample_product_factor
    (A : Finset ℕ)
    (f : Func) :
    (∏ n ∈ A, D.Mellin (D.sample n f))
      =
    (∏ n ∈ A, D.weight n) * D.Mellin f ^ A.card := by
  calc
    (∏ n ∈ A, D.Mellin (D.sample n f))
        = ∏ n ∈ A, D.weight n * D.Mellin f := by
            refine Finset.prod_congr rfl ?_
            intro n hn
            rw [D.Mellin_sample_eq_weight_mul n f]
    _ = (∏ n ∈ A, D.weight n) * (∏ _n ∈ A, D.Mellin f) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ n ∈ A, D.weight n) * D.Mellin f ^ A.card := by
          simp

end FiniteMellinScalingDatum

/--
Finite Dirichlet-polynomial character associated to a Mellin weight.
-/
@[rep_depth projective]
def finiteDirichletWeightSum
    {R : Type*} [AddCommMonoid R]
    (A : Finset ℕ)
    (weight : ℕ → R) : R :=
  Finset.sum A weight

/--
Finite multiplicative character associated to a Mellin weight.
-/
@[rep_depth projective]
def finiteMultiplicativeWeightProduct
    {R : Type*} [CommMonoid R]
    (A : Finset ℕ)
    (weight : ℕ → R) : R :=
  Finset.prod A weight

/--
The finite orbit-sum factor is exactly the finite Dirichlet weight sum.
-/
@[rep_depth projective]
theorem finite_sample_sum_factor_as_dirichlet_weight
    {Func R : Type*} [AddCommMonoid Func] [CommSemiring R]
    (D : FiniteMellinScalingDatum Func R)
    (A : Finset ℕ)
    (f : Func) :
    D.Mellin (Finset.sum A (fun n => D.sample n f))
      =
    finiteDirichletWeightSum A D.weight * D.Mellin f := by
  exact D.finite_sample_sum_factor A f

/--
The finite multiplicative orbit product is exactly the finite product of
Mellin scaling weights.
-/
@[rep_depth projective]
theorem finite_sample_product_factor_as_multiplicative_weight
    {Func R : Type*} [AddCommMonoid Func] [CommSemiring R]
    (D : FiniteMellinScalingDatum Func R)
    (A : Finset ℕ)
    (f : Func) :
    (∏ n ∈ A, D.Mellin (D.sample n f))
      =
    finiteMultiplicativeWeightProduct A D.weight * D.Mellin f ^ A.card := by
  simpa [finiteMultiplicativeWeightProduct] using D.finite_sample_product_factor A f

/-! The finite orbit-sum and orbit-product factorizations. -/
theorem finite_mellin_scaling_factorization :
  ∀ {Func R : Type*} [AddCommMonoid Func] [CommSemiring R]
    (D : FiniteMellinScalingDatum Func R)
    (A : Finset ℕ) (f : Func),
      D.Mellin (Finset.sum A (fun n => D.sample n f))
        =
      finiteDirichletWeightSum A D.weight * D.Mellin f
      ∧
      (∏ n ∈ A, D.Mellin (D.sample n f))
        =
      finiteMultiplicativeWeightProduct A D.weight * D.Mellin f ^ A.card := by
  intro Func R inst1 inst2 D A f
  exact ⟨D.finite_sample_sum_factor A f,
    finite_sample_product_factor_as_multiplicative_weight D A f⟩

end InfoGeometry.Analysis.MellinZetaScaling
