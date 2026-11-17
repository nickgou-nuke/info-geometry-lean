/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.RegularActionAssociator
import InfoGeometry.Algebra.ZornCARAdjoint
import InfoGeometry.Algebra.Zorn.Associator
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Canonical.CattoGurseySplitBasis
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The real Zorn associator Gram form

The carrier is the existing full eight-dimensional real `ZornVectorMatrix`.
The form sums the existing positive coefficient pairing over all 64 ordered
pairs of the signed split basis. Each summand uses the actual Zorn
associator, equivalently the existing regular-action commutator. There is no
averaging factor, omitted channel, or assumed positivity field.

The kernel consists exactly of scalar multiples of the Zorn unit. Being in
an associative quaternion subalgebra does not put an element in this kernel:
the other two associator arguments range over the whole Zorn algebra.
The proof transports the established scalar-nucleus result through the
existing multiplication-compatible equivalence of the two Zorn carriers.

This is a finite real bilinear construction. No evolution, dissipation,
Landauer bound, or spacetime integration is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornAssociatorGram

open ZornPinorReconstruction ZornCARAdjoint
open InfoGeometry.Canonical.GunaydinGursey
open Zorn.CanonicalVectorMatrixBridge
open scoped BigOperators

/-- The exact eight indices of the existing signed split basis. -/
abbrev BasisIndex := Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 3

theorem basisIndex_card : Fintype.card BasisIndex = 8 := by decide

/-- Alternativity identifies the existing regular-action commutator with
the actual associator having the state in its first slot. -/
theorem leftRightCommutator_apply_first (y z X : Z) :
    leftRightCommutator (R := ℝ) y z X = _root_.associator X y z := by
  rw [ZornVectorMatrix.zorn_leftRightCommutator_apply]
  exact alternative_associator_cycle
    InfoGeometry.Algebra.zorn_left_alternative
    InfoGeometry.Algebra.zorn_right_alternative X y z

/-- The full, unnormalized 8-by-8 associator Gram form. Bilinearity is
inherited from the existing linear regular actions and coefficient pairing. -/
def associatorGram : LinearMap.BilinForm ℝ Z :=
  ∑ i : BasisIndex, ∑ j : BasisIndex,
    coefficientPairing.compl₁₂
      (leftRightCommutator (R := ℝ)
        (signedBasis (R := ℝ) i) (signedBasis (R := ℝ) j))
      (leftRightCommutator (R := ℝ)
        (signedBasis (R := ℝ) i) (signedBasis (R := ℝ) j))

/-- The form retains the full nonassociative products in every summand. -/
theorem associatorGram_apply (X Y : Z) :
    associatorGram X Y =
      ∑ i : BasisIndex, ∑ j : BasisIndex,
        coefficientPairing
          (_root_.associator X (signedBasis (R := ℝ) i) (signedBasis (R := ℝ) j))
          (_root_.associator Y (signedBasis (R := ℝ) i) (signedBasis (R := ℝ) j)) := by
  simp only [associatorGram, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.compl₁₂_apply, leftRightCommutator_apply_first]

theorem associatorGram_symm (X Y : Z) :
    associatorGram X Y = associatorGram Y X := by
  rw [associatorGram_apply, associatorGram_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact coefficientPairing_symm _ _

theorem associatorGram_isSymm : associatorGram.IsSymm :=
  ⟨associatorGram_symm⟩

/-- Positive semidefiniteness follows from the constructed positive pairing,
not from the indefinite multiplicative Zorn norm. -/
theorem associatorGram_nonneg (X : Z) : 0 ≤ associatorGram X X := by
  rw [associatorGram_apply]
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => coefficientPairing_nonneg _

/-- A zero Gram value annihilates every one of the 64 basis-pair defects. -/
theorem associatorGram_zero_iff_basis (X : Z) :
    associatorGram X X = 0 ↔
      ∀ i j : BasisIndex,
        _root_.associator X (signedBasis (R := ℝ) i) (signedBasis (R := ℝ) j) = 0 := by
  rw [associatorGram_apply]
  constructor
  · intro h i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Finset.sum_nonneg
        (fun _ _ => coefficientPairing_nonneg _))).mp h i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => coefficientPairing_nonneg _)).mp hi j (Finset.mem_univ j)
    exact (coefficientPairing_zero_iff _).mp hij
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [h i j]
    simp only [map_zero]

/-- The two parameter slots of the actual associator form a native bilinear
map. This is only an arity adapter used for basis extensionality. -/
private def associatorParameters (X : Z) : Z →ₗ[ℝ] Z →ₗ[ℝ] Z :=
  LinearMap.mk₂ ℝ (fun y z => _root_.associator X y z)
    (by
      intro y₁ y₂ z
      simp only [_root_.associator_apply, _root_.mul_add, _root_.add_mul]
      abel)
    (by
      intro r y z
      simp only [_root_.associator_apply, _root_.mul_smul_comm,
        _root_.smul_mul_assoc, _root_.smul_sub])
    (by
      intro y z₁ z₂
      simp only [_root_.associator_apply, _root_.mul_add]
      abel)
    (by
      intro r y z
      simp only [_root_.associator_apply, _root_.mul_smul_comm, _root_.smul_sub])

/-- Testing both parameter slots on the full basis is equivalent to testing
them on the entire Zorn algebra. -/
theorem associator_basis_zero_iff (X : Z) :
    (∀ i j : BasisIndex,
      _root_.associator X (signedBasis (R := ℝ) i) (signedBasis (R := ℝ) j) = 0) ↔
      ∀ y z : Z, _root_.associator X y z = 0 := by
  constructor
  · intro h
    have hmap : associatorParameters X = 0 := by
      apply (signedBasis (R := ℝ)).ext
      intro i
      apply (signedBasis (R := ℝ)).ext
      intro j
      exact h i j
    intro y z
    change associatorParameters X y z = 0
    simp only [hmap, LinearMap.zero_apply]
  · intro h i j
    exact h _ _

/-- The established carrier equivalence transports the actual associator;
it does not substitute associative matrix multiplication. -/
theorem canonical_associator_transport (X Y W : CZ) :
    canonicalVectorEquiv (Zorn.associatorDefect X Y W) =
      _root_.associator (canonicalVectorEquiv X)
        (canonicalVectorEquiv Y) (canonicalVectorEquiv W) := by
  simp only [Zorn.associatorDefect, canonicalVectorEquiv_sub,
    canonicalVectorEquiv_mul, _root_.associator_apply, zvm_mul_def,
    _root_.sub_eq_add_neg, zvm_add_def, zvm_neg_def, ZornVectorMatrix.sub]

/-- Exact scalar-nucleus characterization on the vector carrier, transported
from the existing nonzero-associator theorem on the canonical carrier. -/
theorem associator_zero_iff_scalar (X : Z) :
    (∀ y z : Z, _root_.associator X y z = 0) ↔
      ∃ r : ℝ, X = r • (ZornVectorMatrix.one : Z) := by
  constructor
  · intro hX
    have hscalar : ∃ r : ℝ,
        canonicalVectorEquiv.symm X = r • (1 : CZ) := by
      by_contra hnscalar
      obtain ⟨Y, W, hYW⟩ := Zorn.exists_nonzero_associator_of_not_scalar hnscalar
      apply hYW
      apply canonicalVectorEquiv.injective
      rw [canonical_associator_transport, canonicalVectorEquiv_zero,
        Equiv.apply_symm_apply]
      exact hX _ _
    obtain ⟨r, hr⟩ := hscalar
    refine ⟨r, ?_⟩
    have h := congrArg canonicalVectorEquiv hr
    simpa only [Equiv.apply_symm_apply, canonicalVectorEquiv_smul,
      canonicalVectorEquiv_one, zvm_smul_def] using h
  · rintro ⟨r, rfl⟩ y z
    have hs : r • (ZornVectorMatrix.one : Z) = ZornVectorMatrix.scalar r := by
      ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.one,
        ZornVectorMatrix.scalar]
    rw [hs]
    exact ZornVectorMatrix.associator_scalar_left r y z

/-- The full associator Gram form vanishes exactly on scalar states. -/
theorem associatorGram_zero_iff_scalar (X : Z) :
    associatorGram X X = 0 ↔
      ∃ r : ℝ, X = r • (ZornVectorMatrix.one : Z) :=
  (associatorGram_zero_iff_basis X).trans
    ((associator_basis_zero_iff X).trans (associator_zero_iff_scalar X))

/-- The bilinear left kernel, as well as its quadratic zero set, is exactly
the scalar line. -/
theorem associatorGram_left_kernel_iff_scalar (X : Z) :
    (∀ Y : Z, associatorGram X Y = 0) ↔
      ∃ r : ℝ, X = r • (ZornVectorMatrix.one : Z) := by
  constructor
  · intro h
    exact (associatorGram_zero_iff_scalar X).mp (h X)
  · intro h Y
    have hX := (associator_zero_iff_scalar X).mpr h
    rw [associatorGram_apply]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [hX]
    simp only [map_zero, LinearMap.zero_apply]

theorem associatorGram_pos_of_not_scalar {X : Z}
    (hX : ¬ ∃ r : ℝ, X = r • (ZornVectorMatrix.one : Z)) :
    0 < associatorGram X X := by
  apply lt_of_le_of_ne (associatorGram_nonneg X)
  intro h
  exact hX ((associatorGram_zero_iff_scalar X).mp h.symm)

/-- The nonscalar Peirce idempotent is a concrete positive witness. In
particular, restriction to an associative subalgebra is not the kernel test
for this form, whose two probe slots range over the full algebra. -/
theorem associatorGram_E11_pos :
    0 < associatorGram (ZornVectorMatrix.E11 : Z) ZornVectorMatrix.E11 := by
  apply associatorGram_pos_of_not_scalar
  rintro ⟨r, hr⟩
  have ha := congrArg ZornVectorMatrix.a hr
  have hb := congrArg ZornVectorMatrix.b hr
  norm_num [ZornVectorMatrix.E11, ZornVectorMatrix.one, ZornVectorMatrix.smul] at ha hb
  linarith

/-- The ordinary quaternion unit `i` also has positive ambient associator
Gram value. The reused quaternion embedding preserves multiplication and
its image is associative, but the two Gram probe slots range over all eight
Zorn coordinates, including elements outside that quaternion image. -/
theorem associatorGram_quaternion_i_pos :
    0 < associatorGram
      (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))
      (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ)) := by
  apply associatorGram_pos_of_not_scalar
  rintro ⟨r, hr⟩
  have hw := congrArg (fun X : Z => X.w (0 : Fin 3)) hr
  norm_num [quaternionEmbedding, ZornVectorMatrix.one, ZornVectorMatrix.smul] at hw

end InfoGeometry.Algebra.ZornAssociatorGram

end
