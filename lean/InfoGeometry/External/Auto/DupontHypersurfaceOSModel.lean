import Mathlib


/-!
# Dupont hypersurface Orlik--Solomon model spine

Clément Dupont's hypersurface-arrangement model has summands

`M_q^n(X,L) = ⊕_S H^{2n-q}(S)(n-q) ⊗ A_S(L)`.

This file formalizes the integer index arithmetic appearing in that model:
cohomological degree, Tate twist, stratum codimension, product signs, products,
and differential shifts.
-/

noncomputable section

namespace DupontHypersurfaceOSModel

/-- The cohomological degree appearing in `H^{2n-q}(S)`. -/
def cohomDegree (n q : ℤ) : ℤ := 2 * n - q

/-- The Tate twist index `(n-q)`. -/
def tateTwist (n q : ℤ) : ℤ := n - q

/-- Stratum codimension index `q-n`. -/
def stratumCodim (n q : ℤ) : ℤ := q - n

/-- Product sign exponent from Dupont's model: `(q-n)q'`. -/
def productSignExponent (n q q' : ℤ) : ℤ := (q - n) * q'

theorem product_cohomDegree (n q n' q' : ℤ) :
    cohomDegree n q + cohomDegree n' q' =
      cohomDegree (n + n') (q + q') := by
  simp only [cohomDegree]
  ring_nf

theorem product_tateTwist (n q n' q' : ℤ) :
    tateTwist n q + tateTwist n' q' =
      tateTwist (n + n') (q + q') := by
  simp only [tateTwist]
  ring_nf

theorem product_stratumCodim (n q n' q' : ℤ) :
    stratumCodim n q + stratumCodim n' q' =
      stratumCodim (n + n') (q + q') := by
  simp only [stratumCodim]
  ring_nf

theorem differential_cohomDegree_shift (n q : ℤ) :
    cohomDegree (n + 1) q = cohomDegree n q + 2 := by
  simp only [cohomDegree]
  ring_nf

theorem differential_tateTwist_shift (n q : ℤ) :
    tateTwist (n + 1) q = tateTwist n q + 1 := by
  simp only [tateTwist]
  ring_nf

theorem differential_codim_shift (n q : ℤ) :
    stratumCodim (n + 1) q = stratumCodim n q - 1 := by
  simp only [stratumCodim]
  ring_nf

theorem productSignExponent_eq_codim_mul (n q q' : ℤ) :
    productSignExponent n q q' = stratumCodim n q * q' := by
  rfl

/-- Consolidated product and differential-shift identities for the integer indices. -/
theorem dupont_index_arithmetic_synthesis (n q n' q' : ℤ) :
    cohomDegree n q + cohomDegree n' q' =
      cohomDegree (n + n') (q + q') ∧
    tateTwist n q + tateTwist n' q' =
      tateTwist (n + n') (q + q') ∧
    cohomDegree (n + 1) q = cohomDegree n q + 2 ∧
    tateTwist (n + 1) q = tateTwist n q + 1 ∧
    stratumCodim (n + 1) q = stratumCodim n q - 1 := by
  exact ⟨product_cohomDegree n q n' q',
    product_tateTwist n q n' q',
    differential_cohomDegree_shift n q,
    differential_tateTwist_shift n q,
    differential_codim_shift n q⟩

end DupontHypersurfaceOSModel

end noncomputable section
