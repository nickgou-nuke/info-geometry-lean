import Mathlib

/-!
# InfoGeometry.Analysis.FiniteSpectralMellinTaylor

Finite spectral/Mellin/Taylor calculus.

This file records a safe algebraic core behind the slogan that finite spectral
functional calculus can be read both as Taylor moments and as a Mellin-type
power transform of spectral values.

For a finite spectral datum with spectral values `λ i` and weights `w i`:

* the integer Mellin moment is `∑ i, w i * λ i ^ k`;
* a finite Taylor prefix is `∑ k < N, c k * λ i ^ k`;
* integrating/summing the Taylor prefix over the finite spectrum equals the
  coefficient-weighted sum of Mellin moments.

No spectral theorem.
No projection-valued measure.
No unbounded operator calculus.
No analytic Taylor-series convergence or Mellin inversion.
-/

namespace FiniteSpectralMellinTaylor

open Finset

/-- Finite spectral data: spectral values and algebraic weights. -/
structure FiniteSpectralData (ι R : Type*) where
  /-- Spectral value attached to a finite index. -/
  spectralValue : ι → R
  /-- Algebraic spectral weight attached to a finite index. -/
  weight : ι → R

namespace FiniteSpectralData

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Integer Mellin/power moment of finite spectral data. -/
def mellinMoment (D : FiniteSpectralData ι R) (k : ℕ) : R :=
  ∑ i : ι, D.weight i * D.spectralValue i ^ k

/-- Finite Taylor prefix evaluated at one spectral value. -/
def pointwiseTaylorPrefix (D : FiniteSpectralData ι R) (c : ℕ → R) (N : ℕ) (i : ι) : R :=
  ∑ k ∈ Finset.range N, c k * D.spectralValue i ^ k

/-- Coefficient-weighted finite Mellin-moment sum. -/
def taylorMomentPrefix (D : FiniteSpectralData ι R) (c : ℕ → R) (N : ℕ) : R :=
  ∑ k ∈ Finset.range N, c k * D.mellinMoment k

@[simp]
theorem mellinMoment_zero (D : FiniteSpectralData ι R) :
    D.mellinMoment 0 = ∑ i : ι, D.weight i := by
  simp [mellinMoment]

omit [Fintype ι] in
@[simp]
theorem pointwiseTaylorPrefix_zero (D : FiniteSpectralData ι R) (c : ℕ → R) (i : ι) :
    D.pointwiseTaylorPrefix c 0 i = 0 := by
  simp [pointwiseTaylorPrefix]

@[simp]
theorem taylorMomentPrefix_zero (D : FiniteSpectralData ι R) (c : ℕ → R) :
    D.taylorMomentPrefix c 0 = 0 := by
  simp [taylorMomentPrefix]

omit [Fintype ι] in
/-- Successor recursion for pointwise finite Taylor prefixes. -/
theorem pointwiseTaylorPrefix_succ (D : FiniteSpectralData ι R)
    (c : ℕ → R) (N : ℕ) (i : ι) :
    D.pointwiseTaylorPrefix c (N + 1) i =
      D.pointwiseTaylorPrefix c N i + c N * D.spectralValue i ^ N := by
  simp [pointwiseTaylorPrefix, Finset.sum_range_succ]

/-- Successor recursion for coefficient-weighted Mellin-moment prefixes. -/
theorem taylorMomentPrefix_succ (D : FiniteSpectralData ι R)
    (c : ℕ → R) (N : ℕ) :
    D.taylorMomentPrefix c (N + 1) =
      D.taylorMomentPrefix c N + c N * D.mellinMoment N := by
  simp [taylorMomentPrefix, Finset.sum_range_succ]

/--
Finite spectral Taylor/Mellin interchange: summing a finite Taylor prefix over
spectral weights equals the coefficient-weighted sum of finite Mellin moments.
-/
theorem weighted_pointwiseTaylorPrefix_eq_taylorMomentPrefix
    (D : FiniteSpectralData ι R) (c : ℕ → R) (N : ℕ) :
    (∑ i : ι, D.weight i * D.pointwiseTaylorPrefix c N i) =
      D.taylorMomentPrefix c N := by
  simp [pointwiseTaylorPrefix, taylorMomentPrefix, mellinMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k hk
  refine Finset.sum_congr rfl ?_
  intro i hi
  ring

/-- The one-term Taylor prefix recovers the zeroth Mellin moment with coefficient `c 0`. -/
theorem taylorMomentPrefix_one (D : FiniteSpectralData ι R) (c : ℕ → R) :
    D.taylorMomentPrefix c 1 = c 0 * D.mellinMoment 0 := by
  simp [taylorMomentPrefix]

end FiniteSpectralData

end FiniteSpectralMellinTaylor
