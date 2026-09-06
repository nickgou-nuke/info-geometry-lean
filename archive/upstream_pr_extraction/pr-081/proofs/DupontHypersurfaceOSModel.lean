import proofs.NonIsoConf3QuadricD4PointCount

/-!
# Dupont hypersurface Orlik--Solomon model spine

Clément Dupont's hypersurface-arrangement model has summands

`M_q^n(X,L) = ⊕_S H^{2n-q}(S)(n-q) ⊗ A_S(L)`.

This file formalizes the index arithmetic and structural data needed to use that
model as the proper replacement for the ordinary hyperplane
Orlik--Solomon algebra in the D=4 quadric problem.
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

/-- Abstract hypersurface arrangement data.  Smoothness/projectivity and
arrangement hypotheses are kept explicit because they are the hypotheses of
Dupont's theorem. -/
structure HypersurfaceArrangementInput where
  X : Type
  hypersurface : Type
  stratum : Type
  smoothProjectiveX : Prop
  hypersurfacesSmooth : Prop
  locallyHyperplaneLike : Prop

/-- A term in Dupont's model, abstracting the summand
`H^{2n-q}(S)(n-q) ⊗ A_S(L)`. -/
structure ModelTerm (I : HypersurfaceArrangementInput) where
  n : ℤ
  q : ℤ
  S : I.stratum
  cohomologicalDegree : ℤ := cohomDegree n q
  twist : ℤ := tateTwist n q
  codimension : ℤ := stratumCodim n q

/-- Literature comparison data: Dupont identifies the cohomology of the model
with the weight-graded cohomology of the complement. -/
structure DupontComparisonData (I : HypersurfaceArrangementInput) where
  logarithmicComplexComputesComplement : Prop
  weightSpectralSequenceDegeneratesAtE2 : Prop
  modelIsDGA : Prop
  grWeightCohomologyIso : Prop
  functoriality : Prop

theorem dupont_index_arithmetic_synthesis (n q n' q' : ℤ) :
    cohomDegree n q + cohomDegree n' q' =
      cohomDegree (n + n') (q + q') ∧
    tateTwist n q + tateTwist n' q' =
      tateTwist (n + n') (q + q') ∧
    cohomDegree (n + 1) q = cohomDegree n q + 2 ∧
    tateTwist (n + 1) q = tateTwist n q + 1 ∧
    stratumCodim (n + 1) q = stratumCodim n q - 1 := by
  constructor
  · exact product_cohomDegree n q n' q'
  constructor
  · exact product_tateTwist n q n' q'
  constructor
  · exact differential_cohomDegree_shift n q
  constructor
  · exact differential_tateTwist_shift n q
  · exact differential_codim_shift n q

end DupontHypersurfaceOSModel

end noncomputable section
