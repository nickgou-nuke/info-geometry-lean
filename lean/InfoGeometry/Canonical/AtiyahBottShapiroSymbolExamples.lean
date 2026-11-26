/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AtiyahBottShapiroSymbol
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# The ABS symbol on the real negative line

The native Clifford algebra of `Q x = -(x * x)` acts on itself by the regular
representation, with its native grade involution. Its generator `e = ι Q 1`
is odd and satisfies `e * e = -1`; the unit is even. The ABS symbol at `1`
therefore sends `e` to `1`, and its inverse sends `1` to `e`.

At `-1`, these images acquire a minus sign. The calculations take place in
the actual real Clifford algebra and its grading eigenspaces.
-/

noncomputable section

namespace InfoGeometry.Canonical.AtiyahBottShapiroSymbolExamples

open CliffordAlgebra
open PinOperatorFamilyBridge
open AtiyahBottShapiroSymbol

local instance : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

/-- The negative quadratic form on the real line. -/
abbrev negativeLineForm : QuadraticForm ℝ ℝ := -QuadraticMap.sq

theorem negativeLineForm_apply (x : ℝ) : negativeLineForm x = -(x * x) := rfl

theorem negativeLineForm_one : negativeLineForm 1 = -1 := by
  simp only [negativeLineForm_apply, mul_one]

theorem negativeLineForm_neg_one : negativeLineForm (-1) = -1 := by
  simp only [negativeLineForm_apply, neg_mul_neg, one_mul]

theorem negativeLineForm_one_ne_zero : negativeLineForm 1 ≠ 0 := by
  rw [negativeLineForm_one]
  exact neg_ne_zero.mpr one_ne_zero

theorem negativeLineForm_neg_one_ne_zero : negativeLineForm (-1) ≠ 0 := by
  rw [negativeLineForm_neg_one]
  exact neg_ne_zero.mpr one_ne_zero

/-- The actual regular graded representation on the real Clifford algebra. -/
abbrev negativeLineRepresentation :=
  GradedCliffordOperatorRepresentation.negativeLine

/-- The Clifford generator corresponding to the real vector `1`. -/
def lineGenerator : CliffordAlgebra negativeLineForm := ι negativeLineForm 1

/-- The native Clifford relation gives the sign needed for the ABS symbol. -/
theorem lineGenerator_sq : lineGenerator * lineGenerator = -1 := by
  simpa only [lineGenerator, negativeLineForm_one, map_neg, map_one] using
    CliffordAlgebra.ι_sq_scalar negativeLineForm (1 : ℝ)

theorem lineGenerator_mem_oddSpace :
    lineGenerator ∈ oddSpace negativeLineRepresentation := by
  rw [mem_oddSpace_iff]
  change CliffordAlgebra.involute (ι negativeLineForm (1 : ℝ)) =
    -(ι negativeLineForm (1 : ℝ))
  exact CliffordAlgebra.involute_ι _

theorem one_mem_evenSpace :
    (1 : CliffordAlgebra negativeLineForm) ∈ evenSpace negativeLineRepresentation := by
  rw [mem_evenSpace_iff]
  change CliffordAlgebra.involute (1 : CliffordAlgebra negativeLineForm) = 1
  exact map_one _

/-- The generator as an element of the actual odd eigenspace. -/
def oddGenerator : oddSpace negativeLineRepresentation :=
  ⟨lineGenerator, lineGenerator_mem_oddSpace⟩

/-- The unit as an element of the actual even eigenspace. -/
def evenUnit : evenSpace negativeLineRepresentation := ⟨1, one_mem_evenSpace⟩

/-- Native Clifford nontriviality supplies a nonzero even unit. -/
theorem negativeLine_one_ne_zero : (1 : CliffordAlgebra negativeLineForm) ≠ 0 :=
  one_ne_zero

theorem lineGenerator_ne_zero : lineGenerator ≠ 0 := by
  intro h
  have hsq := lineGenerator_sq
  rw [h, zero_mul] at hsq
  exact (neg_ne_zero.mpr negativeLine_one_ne_zero) hsq.symm

theorem oddGenerator_ne_zero : oddGenerator ≠ 0 := by
  intro h
  exact lineGenerator_ne_zero (congrArg Subtype.val h)

theorem evenUnit_ne_zero : evenUnit ≠ 0 := by
  intro h
  exact negativeLine_one_ne_zero (congrArg Subtype.val h)

/-- At the real vector `1`, the ABS minus sign cancels the negative square. -/
theorem symbol_one_oddGenerator :
    symbol negativeLineRepresentation (1 : ℝ) oddGenerator = evenUnit := by
  apply Subtype.ext
  rw [symbol_apply]
  change -(lineGenerator * lineGenerator) = (1 : CliffordAlgebra negativeLineForm)
  rw [lineGenerator_sq, neg_neg]

/-- On this negative unit vector, the inverse is multiplication by the generator. -/
theorem symbolEquiv_one_symm_evenUnit :
    (symbolEquiv negativeLineRepresentation (1 : ℝ)
      negativeLineForm_one_ne_zero).symm evenUnit = oddGenerator := by
  apply Subtype.ext
  rw [symbolEquiv_symm_apply_of_neg_one negativeLineRepresentation (1 : ℝ)
    negativeLineForm_one_ne_zero negativeLineForm_one evenUnit]
  change lineGenerator * (1 : CliffordAlgebra negativeLineForm) = lineGenerator
  exact mul_one _

/-- Reversing the unit vector reverses the sign of the symbol on the generator. -/
theorem symbol_neg_one_oddGenerator :
    symbol negativeLineRepresentation (-1 : ℝ) oddGenerator = -evenUnit := by
  apply Subtype.ext
  rw [symbol_apply]
  change -(ι negativeLineForm (-1 : ℝ) * lineGenerator) =
    -(1 : CliffordAlgebra negativeLineForm)
  rw [map_neg]
  change -(-lineGenerator * lineGenerator) = -(1 : CliffordAlgebra negativeLineForm)
  rw [neg_mul, neg_neg, lineGenerator_sq]

/-- The inverse at the opposite unit vector also has the opposite image. -/
theorem symbolEquiv_neg_one_symm_evenUnit :
    (symbolEquiv negativeLineRepresentation (-1 : ℝ)
      negativeLineForm_neg_one_ne_zero).symm evenUnit = -oddGenerator := by
  apply Subtype.ext
  rw [symbolEquiv_symm_apply_of_neg_one negativeLineRepresentation (-1 : ℝ)
    negativeLineForm_neg_one_ne_zero negativeLineForm_neg_one evenUnit]
  change ι negativeLineForm (-1 : ℝ) * (1 : CliffordAlgebra negativeLineForm) =
    -(ι negativeLineForm (1 : ℝ))
  simp only [map_neg, mul_one]

end InfoGeometry.Canonical.AtiyahBottShapiroSymbolExamples
