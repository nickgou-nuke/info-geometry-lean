/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.SupercolorMultiplication
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentParity

/-!
# Two-color operator tetraktys and tripotent parity

The existing supercolor operators are `Eᵢⱼ = colorBoson d b i j = d i * b j`.
For distinct colors, their diagonal operators `eᵢ = Eᵢᵢ` and `eⱼ = Eⱼⱼ`
are orthogonal idempotents. The owned construction therefore gives the
tripotent `T = colorTripotent eᵢ eⱼ = eᵢ - eⱼ`.

The existing common-source hypothesis `b i * d i = q` supplies the ordered
products `Eᵢⱼ * Eⱼᵢ = eᵢ` and `Eⱼᵢ * Eᵢⱼ = eⱼ`. The two off-diagonal
operators are actual Peirce corners at `eᵢ`, so the native tetraktys has
`genV = eᵢ + eⱼ` and `genSig = T`. Consequently `T*T = genV` and its zero-mode
reflection is `1 - 2 • genV`, with the full operator mass retained.

The final declarations feed the constructed tripotent into the existing
five-grade parity and Grassmannian tangent theorems. The common-source
hypothesis is used only for the matrix-unit products and their mass/spin
consequences. The tripotent, zero cut, and parity laws need only the base
supercolor system and distinctness of the two colors.

The two cuts have different odd sectors: `Eᵢⱼ` and `Eⱼᵢ` are odd corners at
`eᵢ`, but join the two nonzero eigenspaces of `T`. Their adjoint weights are
`±2`, so they are even for the zero-versus-nonzero cut `P₀`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.SuperGrassmannianSusy
open InfoGeometry.Physics.Algebra

variable {A : Type*} [Ring A] [StarRing A]
variable {ι : Type*} {d b : ι → A}

local notation "E" => colorBoson d b

/-- The two selected color operators are the actual directed corners at `eᵢ`. -/
theorem supercolor_tetraktys_corners (hS : IsSupercolorSystem d b)
    {i j : ι} (hij : i ≠ j) :
    conePlus (E i i) (E i j) = E i j ∧
      coneMinus (E i i) (E j i) = E j i := by
  have hu := colorBoson_mul_left_absorb hS i j
  have hl := colorBoson_mul_right_absorb hS j i
  have huz : E i j * E i i = 0 :=
    colorBoson_mul_eq_zero_of_middle_ne hS (Ne.symm hij)
  have hlz : E i i * E j i = 0 :=
    colorBoson_mul_eq_zero_of_middle_ne hS hij
  constructor
  · simp only [conePlus, hu, mul_sub, mul_one, huz, sub_zero]
  · simp only [coneMinus, sub_mul, one_mul, hlz, sub_zero, hl]

/-- Distinct diagonal colors construct a tripotent using the owned
orthogonal-idempotent construction. A common source is unnecessary here. -/
theorem supercolor_colorTripotent_tripotent (hS : IsSupercolorSystem d b)
    {i j : ι} (hij : i ≠ j) :
    colorTripotent (E i i) (E j j) * colorTripotent (E i i) (E j j) *
        colorTripotent (E i i) (E j j) =
      colorTripotent (E i i) (E j j) := by
  have h := orthogonal_idempotents_color_tripotent
    (colorBoson_mul_left_absorb hS i i)
    (colorBoson_mul_left_absorb hS j j)
    (colorBoson_mul_eq_zero_of_middle_ne hS hij)
    (colorBoson_mul_eq_zero_of_middle_ne hS (Ne.symm hij))
  simpa only [tripotentDefect, sub_eq_zero] using h.1

section CommonSource

variable [DecidableEq ι]

/-- The common source gives both ordered reverse-color products. -/
theorem supercolor_reverse_products (hS : IsSupercolorSystem d b)
    {q : A} (hq : ∀ k, b k * d k = q) (i j : ι) :
    E i j * E j i = E i i ∧ E j i * E i j = E j j := by
  constructor
  · simpa using colorBoson_mul_of_common_source hS hq i j j i
  · simpa using colorBoson_mul_of_common_source hS hq j i i j

/-- The native Jordan mass is the sum of the two color projections. -/
theorem supercolor_tetraktys_mass (hS : IsSupercolorSystem d b)
    {q : A} (hq : ∀ k, b k * d k = q) {i j : ι} (hij : i ≠ j) :
    genV (E i i) (E i j) (E j i) = E i i + E j j := by
  rw [genV, anticomm,
    (supercolor_tetraktys_corners hS hij).1,
    (supercolor_tetraktys_corners hS hij).2,
    (supercolor_reverse_products hS hq i j).1,
    (supercolor_reverse_products hS hq i j).2]

/-- The native spin commutator is the constructed color tripotent. -/
theorem supercolor_tetraktys_spin (hS : IsSupercolorSystem d b)
    {q : A} (hq : ∀ k, b k * d k = q) {i j : ι} (hij : i ≠ j) :
    genSig (E i i) (E i j) (E j i) = colorTripotent (E i i) (E j j) := by
  rw [genSig, comm,
    (supercolor_tetraktys_corners hS hij).1,
    (supercolor_tetraktys_corners hS hij).2,
    (supercolor_reverse_products hS hq i j).1,
    (supercolor_reverse_products hS hq i j).2, colorTripotent]

/-- The square of the color spin is the full native operator mass. -/
theorem supercolor_colorTripotent_sq_eq_mass (hS : IsSupercolorSystem d b)
    {q : A} (hq : ∀ k, b k * d k = q) {i j : ι} (hij : i ≠ j) :
    colorTripotent (E i i) (E j j) * colorTripotent (E i i) (E j j) =
      genV (E i i) (E i j) (E j i) := by
  rw [supercolor_tetraktys_mass hS hq hij]
  simp [colorTripotent, sub_mul, mul_sub,
    colorBoson_mul_of_common_source hS hq, hij, Ne.symm hij]

end CommonSource

section RealProjectors

variable [Algebra ℝ A]

/-- The zero projector is the actual complementary color operator. -/
theorem supercolor_projZero_colorTripotent (hS : IsSupercolorSystem d b)
    {i j : ι} (hij : i ≠ j) :
    projZero (colorTripotent (E i i) (E j j)) = 1 - E i i - E j j := by
  have h := orthogonal_idempotents_color_tripotent
    (colorBoson_mul_left_absorb hS i i)
    (colorBoson_mul_left_absorb hS j j)
    (colorBoson_mul_eq_zero_of_middle_ne hS hij)
    (colorBoson_mul_eq_zero_of_middle_ne hS (Ne.symm hij))
  simpa only [projZero, triProj0, colorBlue] using h.2.2.2.2

/-- The zero-sector reflection is `1 - 2V`, retaining the full operator `V`. -/
theorem supercolor_zero_reflection_eq_mass [DecidableEq ι]
    (hS : IsSupercolorSystem d b) {q : A} (hq : ∀ k, b k * d k = q)
    {i j : ι} (hij : i ≠ j) :
    invS (projZero (colorTripotent (E i i) (E j j))) =
      1 - (2 : ℤ) • genV (E i i) (E i j) (E j i) := by
  rw [invS_projZero_eq, supercolor_colorTripotent_sq_eq_mass hS hq hij]

/-- The odd five-grade component is tangent at the constructed color cut. -/
theorem supercolor_oddGrades_isGrassmannianTangent
    (hS : IsSupercolorSystem d b) {i j : ι} (hij : i ≠ j) (X : A) :
    IsGrassmannianTangent (1 - E i i - E j j)
      (gradeNegOneProjector (colorTripotent (E i i) (E j j)) X +
        gradePosOneProjector (colorTripotent (E i i) (E j j)) X) := by
  rw [← supercolor_projZero_colorTripotent hS hij]
  exact oddGrades_isGrassmannianTangent
    (supercolor_colorTripotent_tripotent hS hij) X

/-- The complete native five-grade family has the correct color-cut parity. -/
theorem supercolor_fiveGrade_parity (hS : IsSupercolorSystem d b)
    {i j : ι} (hij : i ≠ j) (k : FiveGrade) (X : A) :
    parityConj (1 - E i i - E j j)
        (fiveGradeProjector (colorTripotent (E i i) (E j j)) k X) =
      if k = .negOne ∨ k = .posOne then
        -(fiveGradeProjector (colorTripotent (E i i) (E j j)) k X)
      else fiveGradeProjector (colorTripotent (E i i) (E j j)) k X := by
  rw [← supercolor_projZero_colorTripotent hS hij]
  exact parityConj_projZero_fiveGradeProjector
    (supercolor_colorTripotent_tripotent hS hij) k X

end RealProjectors

end InfoGeometry.OperatorAlgebra.PeirceSpine
