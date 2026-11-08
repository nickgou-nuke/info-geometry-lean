/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.ExteriorKleinNullTwistor
import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion

/-!
# Clifford inversion on the native exterior Klein carrier

The canonical map used here is
`CliffordAlgebra.ι exteriorKleinQuadraticForm : ExteriorSquare →ₗ[ℝ] _`.
Its domain is the repository's literal exterior square of real four-space.
An exterior two-vector becomes a generating vector of the Clifford algebra
of this six-dimensional Klein quadratic form.

Mathlib owns the general Clifford inversion theorem.  This file connects it
to the established decomposable and projective Klein loci.  A null exterior
representative gives a square-zero, nonunit Clifford generator.  Off the
null cone, the inverse is the generator divided by its Klein form.

These statements concern the Clifford algebra of the native Klein form;
they do not identify it with `Cl(2,2)`.  Square-zero for one generator does
not assert that the product of two different null generators vanishes.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Projective.ExteriorKleinCliffordInversion

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinNullTwistor

local notation "KleinClifford" => CliffordAlgebra exteriorKleinQuadraticForm
local notation "ιK" => CliffordAlgebra.ι exteriorKleinQuadraticForm

/-- The native Klein-null equation is exactly noninvertibility of its
canonical Clifford generator. -/
theorem exteriorKleinForm_eq_zero_iff_not_isUnit (X : ExteriorSquare) :
    exteriorKleinForm X = 0 ↔ ¬ IsUnit (ιK X) := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  simp only [CliffordAlgebra.isUnit_ι_iff,
    exteriorKleinQuadraticForm_apply, isUnit_iff_ne_zero, not_not]

/-- Clifford square-zero follows from the existing exterior Klein equation. -/
theorem generator_square_zero_of_klein
    (X : ExteriorSquare) (hX : exteriorKleinForm X = 0) :
    ιK X * ιK X = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, exteriorKleinQuadraticForm_apply,
    hX, map_zero]

/-- Every literal Plücker wedge gives a square-zero Clifford generator. -/
theorem plucker_generator_square_zero (u v : Vec4) :
    ιK (exteriorPower.ιMulti ℝ 2 ![u, v]) *
        ιK (exteriorPower.ιMulti ℝ 2 ![u, v]) = 0 :=
  generator_square_zero_of_klein _ (exteriorKleinForm_ιMulti u v)

/-- The existing projective Klein predicate can be read on any nonzero
representative as noninvertibility of its Clifford generator. -/
theorem isKlein_mk_iff_not_isUnit (X : ExteriorSquare) (hX : X ≠ 0) :
    IsKlein (Projectivization.mk ℝ X hX) ↔ ¬ IsUnit (ιK X) := by
  rw [isKlein_mk_iff, exteriorKleinForm_eq_zero_iff_not_isUnit]

/-- Mathlib's Clifford inverse specializes to the native Klein form. -/
theorem generator_ring_inverse
    (X : ExteriorSquare) (hX : exteriorKleinForm X ≠ 0) :
    Ring.inverse (ιK X) = ιK ((exteriorKleinForm X)⁻¹ • X) := by
  letI : Invertible (exteriorKleinQuadraticForm X) :=
    invertibleOfNonzero (by simpa only [exteriorKleinQuadraticForm_apply] using hX)
  letI : Invertible (ιK X) :=
    CliffordAlgebra.invertibleιOfInvertible exteriorKleinQuadraticForm X
  rw [Ring.inverse_invertible, CliffordAlgebra.invOf_ι, invOf_eq_inv,
    exteriorKleinQuadraticForm_apply]

/-- The explicit reciprocal-Klein expression is a left inverse off the null cone. -/
theorem generator_inverse_mul
    (X : ExteriorSquare) (hX : exteriorKleinForm X ≠ 0) :
    ιK ((exteriorKleinForm X)⁻¹ • X) * ιK X = 1 := by
  letI : Invertible (exteriorKleinQuadraticForm X) :=
    invertibleOfNonzero (by simpa only [exteriorKleinQuadraticForm_apply] using hX)
  letI : Invertible (ιK X) :=
    CliffordAlgebra.invertibleιOfInvertible exteriorKleinQuadraticForm X
  simpa only [CliffordAlgebra.invOf_ι, invOf_eq_inv,
    exteriorKleinQuadraticForm_apply] using (invOf_mul_self (ιK X))

/-- The same expression is also a right inverse in the Clifford algebra. -/
theorem generator_mul_inverse
    (X : ExteriorSquare) (hX : exteriorKleinForm X ≠ 0) :
    ιK X * ιK ((exteriorKleinForm X)⁻¹ • X) = 1 := by
  letI : Invertible (exteriorKleinQuadraticForm X) :=
    invertibleOfNonzero (by simpa only [exteriorKleinQuadraticForm_apply] using hX)
  letI : Invertible (ιK X) :=
    CliffordAlgebra.invertibleιOfInvertible exteriorKleinQuadraticForm X
  simpa only [CliffordAlgebra.invOf_ι, invOf_eq_inv,
    exteriorKleinQuadraticForm_apply] using (mul_invOf_self (ιK X))

/-- The canonical generator retains nonzero exterior representatives.
The exterior algebra in this proof is the exterior algebra of `ExteriorSquare`. -/
theorem generator_ne_zero {X : ExteriorSquare} (hX : X ≠ 0) : ιK X ≠ 0 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  intro h
  have he := congrArg (CliffordAlgebra.equivExterior exteriorKleinQuadraticForm) h
  have hz : ExteriorAlgebra.ι ℝ X = 0 := by
    simpa [CliffordAlgebra.equivExterior, CliffordAlgebra.changeForm_ι] using he
  exact hX ((ExteriorAlgebra.ι_eq_zero_iff X).mp hz)

/-- A concrete null representative in the literal exterior square. -/
def coordinateNullRepresentative : ExteriorSquare :=
  exteriorPower.ιMulti ℝ 2 ![i4Basis I4.t, i4Basis I4.x]

theorem coordinateNullRepresentative_ne_zero : coordinateNullRepresentative ≠ 0 := by
  intro h
  have hc := congrArg (fun X : ExteriorSquare => pluckerExteriorMap X 0) h
  norm_num [coordinateNullRepresentative, pluckerExteriorMap_ιMulti,
    pluckerCoords, i4Basis] at hc

/-- The null example produces a nonzero square-zero Clifford element,
and the established unit criterion excludes an inverse. -/
theorem coordinateNullRepresentative_generator_properties :
    ιK coordinateNullRepresentative ≠ 0 ∧
      ιK coordinateNullRepresentative * ιK coordinateNullRepresentative = 0 ∧
      ¬ IsUnit (ιK coordinateNullRepresentative) := by
  have hnull : exteriorKleinForm coordinateNullRepresentative = 0 :=
    exteriorKleinForm_ιMulti _ _
  exact ⟨generator_ne_zero coordinateNullRepresentative_ne_zero,
    generator_square_zero_of_klein _ hnull,
    (exteriorKleinForm_eq_zero_iff_not_isUnit _).mp hnull⟩

/-- Reuse the existing nondecomposable exterior representative: its Klein
form is one, so it lies outside the null locus. -/
theorem nonDecomposableExteriorTwoVector_kleinForm :
    exteriorKleinForm nonDecomposableExteriorTwoVector = 1 := by
  simp [nonDecomposableExteriorTwoVector, exteriorKleinForm, kleinForm]

/-- The existing nonnull exterior representative has an actual Clifford
inverse equal to itself, with both multiplication orders certified. -/
theorem nonDecomposableExteriorTwoVector_generator_inverse :
    Ring.inverse (ιK nonDecomposableExteriorTwoVector) =
        ιK nonDecomposableExteriorTwoVector ∧
      ιK nonDecomposableExteriorTwoVector *
        ιK nonDecomposableExteriorTwoVector = 1 := by
  have hnonzero : exteriorKleinForm nonDecomposableExteriorTwoVector ≠ 0 := by
    rw [nonDecomposableExteriorTwoVector_kleinForm]
    norm_num
  constructor
  · simpa only [nonDecomposableExteriorTwoVector_kleinForm, inv_one, one_smul] using
      generator_ring_inverse nonDecomposableExteriorTwoVector hnonzero
  · simpa only [nonDecomposableExteriorTwoVector_kleinForm, inv_one, one_smul] using
      generator_inverse_mul nonDecomposableExteriorTwoVector hnonzero

end InfoGeometry.Projective.ExteriorKleinCliffordInversion
