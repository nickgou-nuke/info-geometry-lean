/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.ExteriorKleinNullTwistor

/-!
# Quadratic complexes and their native polar systems

A quadratic complex is the null set of a genuine `QuadraticForm` restricted
to the existing projective Klein locus. Adding a multiple of the Klein
quadratic leaves this set unchanged.

The chosen polar is the associated (half-polar) form of `Q`
plus `λ` times the full polar of the Klein form. Its diagonal is therefore
`Q X + 2 * λ * K X`. The real scalar field supplies the required inverse of two.
This matches the supplied draft and amounts to the associated form of `Q + 2λK`.
No singular-surface classification or parameter-dimension count is asserted.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Projective.PluckerQuadraticComplex

open ExteriorKleinProjective ExteriorKleinNullTwistor
open InfoGeometry.Twistor

/-- A quadratic line complex on the established projective Klein locus. -/
def quadraticComplex (Q : QuadraticForm ℝ ExteriorSquare) : Set KleinLocus :=
  {p | IsNull Q p.1}

/-- The coefficient ambiguity is an actual equality of projective line sets. -/
theorem quadraticComplex_add_klein (Q : QuadraticForm ℝ ExteriorSquare) (a : ℝ) :
    quadraticComplex (Q + a • exteriorKleinQuadraticForm) = quadraticComplex Q := by
  ext p
  rcases p with ⟨p, hp⟩
  change IsNull (Q + a • exteriorKleinQuadraticForm) p ↔ IsNull Q p
  revert hp
  refine Projectivization.ind (p := p) ?_
  intro X hX hK
  have hzero : exteriorKleinQuadraticForm X = 0 := by
    rw [exteriorKleinQuadraticForm_apply]
    exact (isKlein_mk_iff X hX).mp hK
  rw [isNull_mk_iff, isNull_mk_iff]
  simp [hzero]

/-- The supplied draft's polar normalization, expressed in Mathlib bilinear forms. -/
def polarComplexForm (Q : QuadraticForm ℝ ExteriorSquare) (a : ℝ) :
    LinearMap.BilinForm ℝ ExteriorSquare :=
  QuadraticMap.associated Q + a • exteriorKleinQuadraticForm.polarBilin

/-- Reciprocity holds for every pair of exterior vectors. -/
theorem polarComplexForm_symm (Q : QuadraticForm ℝ ExteriorSquare) (a : ℝ)
    (X Y : ExteriorSquare) :
    polarComplexForm Q a X Y = polarComplexForm Q a Y X := by
  change QuadraticMap.associated Q X Y + a *
      QuadraticMap.polar exteriorKleinQuadraticForm X Y =
    QuadraticMap.associated Q Y X + a *
      QuadraticMap.polar exteriorKleinQuadraticForm Y X
  rw [QuadraticMap.associated_isSymm ℝ Q X Y,
    QuadraticMap.polar_comm exteriorKleinQuadraticForm X Y]

/-- Exact diagonal identity for the chosen half-polar/full-polar normalization. -/
theorem polarComplexForm_self (Q : QuadraticForm ℝ ExteriorSquare) (a : ℝ)
    (X : ExteriorSquare) :
    polarComplexForm Q a X X = Q X + 2 * a * exteriorKleinQuadraticForm X := by
  change QuadraticMap.associated Q X X + a *
      QuadraticMap.polar exteriorKleinQuadraticForm X X = _
  rw [QuadraticMap.associated_eq_self_apply, QuadraticMap.polar_self]
  simp only [nsmul_eq_mul]
  ring

/-- On the Klein cone, polar self-incidence is precisely the quadratic
complex equation, independently of the multiplier. -/
theorem polarComplexForm_self_eq_zero_iff (Q : QuadraticForm ℝ ExteriorSquare)
    (a : ℝ) (X : ExteriorSquare) (hX : exteriorKleinQuadraticForm X = 0) :
    polarComplexForm Q a X X = 0 ↔ Q X = 0 := by
  rw [polarComplexForm_self, hX, mul_zero, add_zero]

/-- Reciprocity of the zero relation defining a polar complex. -/
theorem polarComplexForm_zero_iff_swap (Q : QuadraticForm ℝ ExteriorSquare)
    (a : ℝ) (X Y : ExteriorSquare) :
    polarComplexForm Q a X Y = 0 ↔ polarComplexForm Q a Y X = 0 := by
  rw [polarComplexForm_symm Q a X Y]

end InfoGeometry.Projective.PluckerQuadraticComplex
