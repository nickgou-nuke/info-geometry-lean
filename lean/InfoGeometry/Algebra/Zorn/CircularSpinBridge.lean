/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LocalZornCl11Slice
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Clifford.Cl11KleinTwist

/-!
# A fixed real matrix channel in the native Zorn carrier

The construction uses the existing fixed-direction multiplication theorem:

* The codomain is the existing `InfoGeometry.Canonical.ZornMatrix ℝ`.
* `fixedChannel` transports the existing fixed-direction `localZornSlice` by
  `canonicalVectorEquiv.symm`.  Its multiplicativity uses the actual ambient
  product theorem `localZornSlice_mul`, with both direction hypotheses proved
  by the existing coordinate-basis lemmas.
* The existing `upperLadder`, `lowerLadder`, `upperCorner`, and `lowerCorner`
  provide the common matrix source for the native channel images.
* The native upper/lower basis sums and differences have squares `1` and `-1`.
  Their anticommutator is zero.  These identities are transported from the
  existing real split-atom matrices, not installed as assumptions.
* Different channels retain the native nonassociative Zorn product.  No
  multiplicative representation of the full Zorn algebra by matrices is
  asserted, and no new Zorn carrier or associative instance is introduced.

The common two-by-two source also has the signed circular representation in
`Clifford.RealCircularSpin`. The lower matrix unit corresponds there to the
negative circular ladder; the native Zorn convention itself is unchanged.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.CircularSpinBridge

open Matrix
open scoped Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Clifford.SplitAtomDoubling
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix

/-- An ordinary real `2 × 2` matrix in one fixed native Zorn colour channel. -/
def fixedChannel (i : Fin 3) : Mat2R →ₗ[ℝ] InfoGeometry.Canonical.ZornMatrix ℝ where
  toFun A := canonicalVectorEquiv.symm
    (localZornSlice (InfoGeometry.Algebra.ZornVec3.basis i)
      (A 0 0) (A 1 1) (A 0 1) (A 1 0))
  map_add' A B := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · rfl
    · rfl
    · funext j
      change (A 0 1 + B 0 1) * (if j = i then 1 else 0) =
        A 0 1 * (if j = i then 1 else 0) +
          B 0 1 * (if j = i then 1 else 0)
      ring
    · funext j
      change (A 1 0 + B 1 0) * (if j = i then 1 else 0) =
        A 1 0 * (if j = i then 1 else 0) +
          B 1 0 * (if j = i then 1 else 0)
      ring
  map_smul' r A := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · rfl
    · rfl
    · funext j
      change (r * A 0 1) * (if j = i then 1 else 0) =
        r * (A 0 1 * (if j = i then 1 else 0))
      ring
    · funext j
      change (r * A 1 0) * (if j = i then 1 else 0) =
        r * (A 1 0 * (if j = i then 1 else 0))
      ring

@[simp] theorem vectorEquiv_fixedChannel (i : Fin 3) (A : Mat2R) :
    canonicalVectorEquiv (fixedChannel i A) =
      localZornSlice (InfoGeometry.Algebra.ZornVec3.basis i)
        (A 0 0) (A 1 1) (A 0 1) (A 1 0) := by
  exact canonicalVectorEquiv.apply_symm_apply _

@[simp] theorem fixedChannel_one (i : Fin 3) :
    fixedChannel i (1 : Mat2R) = 1 := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    simp [fixedChannel, canonicalVectorEquiv, localZornSlice]

/-- Every source matrix entry is recovered by a native Zorn coordinate. -/
theorem fixedChannel_injective (i : Fin 3) :
    Function.Injective (fixedChannel i) := by
  intro A B h
  ext p q
  fin_cases p <;> fin_cases q
  · exact congrArg (fun Z : InfoGeometry.Canonical.ZornMatrix ℝ => Z.a) h
  · have hv := congrArg (fun Z : InfoGeometry.Canonical.ZornMatrix ℝ => Z.x i) h
    simpa [fixedChannel, canonicalVectorEquiv, localZornSlice,
      InfoGeometry.Algebra.ZornVec3.basis] using hv
  · have hw := congrArg (fun Z : InfoGeometry.Canonical.ZornMatrix ℝ => Z.y i) h
    simpa [fixedChannel, canonicalVectorEquiv, localZornSlice,
      InfoGeometry.Algebra.ZornVec3.basis] using hw
  · exact congrArg (fun Z : InfoGeometry.Canonical.ZornMatrix ℝ => Z.b) h

/-- Multiplicativity holds for the chosen channel, with the ambient native
Zorn product on the right. -/
theorem fixedChannel_mul (i : Fin 3) (A B : Mat2R) :
    fixedChannel i (A * B) = fixedChannel i A * fixedChannel i B := by
  apply canonicalVectorEquiv.injective
  rw [vectorEquiv_fixedChannel, canonicalVectorEquiv_mul,
    vectorEquiv_fixedChannel, vectorEquiv_fixedChannel]
  rw [localZornSlice_mul _ (localZorn_basis_direction_norm i)
    (localZorn_basis_direction_cross_self i)]
  congr 1 <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[simp] theorem fixedChannel_upperLadder (i : Fin 3) :
    fixedChannel i (upperLadder : Mat2R) = chiralUpperBasis i := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext j
    simp [fixedChannel, canonicalVectorEquiv, localZornSlice, upperLadder,
      chiralUpperBasis, InfoGeometry.Algebra.ZornVec3.basis,
      Pi.single_apply, eq_comm]
  · funext j
    simp [fixedChannel, canonicalVectorEquiv, localZornSlice, upperLadder,
      chiralUpperBasis]

@[simp] theorem fixedChannel_lowerLadder (i : Fin 3) :
    fixedChannel i (lowerLadder : Mat2R) = chiralLowerBasis i := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · rfl
  · rfl
  · funext j
    simp [fixedChannel, canonicalVectorEquiv, localZornSlice, lowerLadder,
      chiralLowerBasis]
  · funext j
    simp [fixedChannel, canonicalVectorEquiv, localZornSlice, lowerLadder,
      chiralLowerBasis, InfoGeometry.Algebra.ZornVec3.basis,
      Pi.single_apply, eq_comm]

@[simp] theorem fixedChannel_upperCorner (i : Fin 3) :
    fixedChannel i (upperCorner : Mat2R) = zornPlus := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    simp [fixedChannel, canonicalVectorEquiv, localZornSlice,
      upperCorner, zornPlus]

@[simp] theorem fixedChannel_lowerCorner (i : Fin 3) :
    fixedChannel i (lowerCorner : Mat2R) = zornMinus := by
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    simp [fixedChannel, canonicalVectorEquiv, localZornSlice,
      lowerCorner, zornMinus]

@[simp] theorem fixedChannel_positive (i : Fin 3) :
    fixedChannel i (positive : Mat2R) =
      chiralUpperBasis i + chiralLowerBasis i := by
  rw [← ladder_sum, map_add, fixedChannel_upperLadder, fixedChannel_lowerLadder]

@[simp] theorem fixedChannel_negative (i : Fin 3) :
    fixedChannel i (negative : Mat2R) =
      chiralUpperBasis i - chiralLowerBasis i := by
  have h : (negative : Mat2R) = upperLadder - lowerLadder := by
    simpa [omega] using congrArg (fun M : Mat2R => -M)
      (ladder_difference (A := ℝ)).symm
  rw [h, map_sub, fixedChannel_upperLadder, fixedChannel_lowerLadder]

@[simp] theorem fixedChannel_twisted_one (i : Fin 3) :
    fixedChannel i (twisted (1 : ℝ)) = zornPlus - zornMinus := by
  change fixedChannel i (chirality : Mat2R) = _
  rw [← corner_difference, map_sub, fixedChannel_upperCorner,
    fixedChannel_lowerCorner]

/-- A paired native channel has positive square. -/
theorem paired_positive_square (i : Fin 3) :
    (chiralUpperBasis (R := ℝ) i + chiralLowerBasis i) *
        (chiralUpperBasis i + chiralLowerBasis i) = 1 := by
  rw [← fixedChannel_positive i, ← fixedChannel_mul,
    positive_square, fixedChannel_one]

/-- The difference in the same native channel has negative square. -/
theorem paired_negative_square (i : Fin 3) :
    (chiralUpperBasis (R := ℝ) i - chiralLowerBasis i) *
        (chiralUpperBasis i - chiralLowerBasis i) = -1 := by
  rw [← fixedChannel_negative i, ← fixedChannel_mul, negative_square]
  simp only [map_neg, fixedChannel_one]

/-- The two paired generators anticommute inside their common channel. -/
theorem paired_anticommutator (i : Fin 3) :
    (chiralUpperBasis (R := ℝ) i + chiralLowerBasis i) *
        (chiralUpperBasis i - chiralLowerBasis i) +
      (chiralUpperBasis i - chiralLowerBasis i) *
        (chiralUpperBasis i + chiralLowerBasis i) = 0 := by
  calc
    _ = fixedChannel i
        ((positive : Mat2R) * negative + negative * positive) := by
      rw [map_add, fixedChannel_mul, fixedChannel_mul,
        fixedChannel_positive, fixedChannel_negative]
    _ = 0 := by rw [head_anticommutator, map_zero]

theorem pole_cut_square :
    (zornPlus (R := ℝ) - zornMinus) * (zornPlus - zornMinus) = 1 := by
  have h : twisted (1 : ℝ) * twisted 1 = (1 : Mat2R) := by
    exact chirality_square
  rw [← fixedChannel_twisted_one (0 : Fin 3), ← fixedChannel_mul,
    h, fixedChannel_one]

/-- A native cross-channel product, inherited from the Zorn vector owner. -/
theorem upper_zero_mul_upper_one :
    chiralUpperBasis (R := ℝ) 0 * chiralUpperBasis 1 = chiralLowerBasis 2 := by
  apply canonicalVectorEquiv.injective
  rw [canonicalVectorEquiv_mul, canonicalUpperBasis_map,
    canonicalUpperBasis_map, canonicalLowerBasis_map]
  exact InfoGeometry.Algebra.ZornVectorMatrix.U_zero_mul_U_one

private theorem vectorEquiv_neg (X : InfoGeometry.Canonical.ZornMatrix ℝ) :
    canonicalVectorEquiv (-X) =
      InfoGeometry.Algebra.ZornVectorMatrix.neg (canonicalVectorEquiv X) := by
  rfl

/-- The opposite channel has the signed cross product from the native owner. -/
theorem lower_zero_mul_lower_one :
    chiralLowerBasis (R := ℝ) 0 * chiralLowerBasis 1 = -chiralUpperBasis 2 := by
  apply canonicalVectorEquiv.injective
  rw [canonicalVectorEquiv_mul, canonicalLowerBasis_map,
    canonicalLowerBasis_map, vectorEquiv_neg, canonicalUpperBasis_map]
  exact InfoGeometry.Algebra.ZornVectorMatrix.V_zero_mul_V_one

end InfoGeometry.Algebra.Zorn.CircularSpinBridge

end
