/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# KKS pairing with supplied isotropy data

The declarations in this compatibility owner evaluate the pairing on the
original Lie algebra. They prove invariance under a supplied null submodule;
they do not construct a quotient or a smooth symplectic reduction. The actual
radical quotient and its nondegenerate form are constructed separately in
`SouriauKKSRadicalQuotient`.
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace SouriauReduction

variable {R L : Type*} [Ring R] [LieRing L] [Module R L]

/-! The KKS pairing is formed from a native Lie-ring bracket and a linear
functional on the Lie algebra. -/
def kksForm (mu : L →ₗ[R] R) (X Y : L) : R :=
  mu ⁅X, Y⁆

structure CoadjointIsotropyData where
  mu : L →ₗ[R] R
  isotropySubmodule : Submodule R L

/-- Nullity in the second argument follows from nullity in the first. -/
theorem isotropy_coad_null_skew (data : CoadjointIsotropyData (R := R) (L := L))
    (X Y : L) (hX : X ∈ data.isotropySubmodule)
    (h_coad_null : ∀ Z : L, Z ∈ data.isotropySubmodule →
      ∀ W : L, kksForm data.mu Z W = 0) :
    kksForm data.mu Y X = 0 := by
  have h := h_coad_null X hX Y
  have hskew : ⁅Y, X⁆ = -⁅X, Y⁆ := by
    have h' := congrArg Neg.neg (lie_skew X Y)
    simpa using h'
  calc
    kksForm data.mu Y X = -kksForm data.mu X Y := by
      unfold kksForm
      rw [hskew, map_neg]
    _ = 0 := by rw [h, neg_zero]

/-- Compatibility name for the KKS pairing on representatives in `L`. -/
def reducedKKSForm (data : CoadjointIsotropyData (R := R) (L := L)) (X Y : L) : R :=
  kksForm data.mu X Y

/-- Invariance under addition of an element of a supplied null submodule. -/
theorem reducedKKSForm_well_defined
    (data : CoadjointIsotropyData (R := R) (L := L)) (X Y Z : L)
    (hZ : Z ∈ data.isotropySubmodule)
    (h_coad_null : ∀ W : L, W ∈ data.isotropySubmodule →
      ∀ V : L, kksForm data.mu W V = 0) :
    reducedKKSForm data (X + Z) Y = reducedKKSForm data X Y := by
  change data.mu ⁅X + Z, Y⁆ = data.mu ⁅X, Y⁆
  rw [LieRing.add_lie, map_add]
  have h := h_coad_null Z hZ Y
  have h' : data.mu ⁅Z, Y⁆ = 0 := by
    simpa [kksForm] using h
  rw [h', add_zero]

/-- Skewness of the pairing on representatives. -/
theorem reducedKKSForm_skew
    (data : CoadjointIsotropyData (R := R) (L := L)) (X Y : L) :
    reducedKKSForm data X Y = - reducedKKSForm data Y X := by
  have hskew : ⁅Y, X⁆ = -⁅X, Y⁆ := by
    have h' := congrArg Neg.neg (lie_skew X Y)
    simpa using h'
  unfold reducedKKSForm kksForm
  rw [hskew, map_neg]
  simp

/-- Compatibility identity on representatives. This does not assert a smooth
Marsden--Weinstein reduction. -/
theorem marsden_weinstein_pullback_identity
    (data : CoadjointIsotropyData (R := R) (L := L)) (X Y : L) :
    reducedKKSForm data X Y = kksForm data.mu X Y := rfl

end SouriauReduction
