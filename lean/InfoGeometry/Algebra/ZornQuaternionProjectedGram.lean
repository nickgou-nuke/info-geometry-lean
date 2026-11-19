/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornAssociatorGram

/-!
# The quaternion-projected real Zorn associator Gram form

Both probe slots, rather than the state slot, are projected onto the existing
multiplicative quaternion embedding. The full 64 ordered signed-basis pairs
are retained. Its quadratic zero set and bilinear kernel are exactly that
four-dimensional quaternion range. This differs from the scalar kernel of
the ambient Gram form.

The projection, kernel, and associator sign are constructed on the existing
nonassociative Zorn carrier. No associative instance is imposed on that carrier.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornQuaternionProjectedGram

open ZornPinorReconstruction ZornCARAdjoint ZornAssociatorGram
open InfoGeometry.Canonical.GunaydinGursey
open scoped BigOperators

/-- Extract the quaternion coordinates of the orthogonal projection for the
positive coefficient pairing. -/
def quaternionRetraction : Z →ₗ[ℝ] Quaternion ℝ where
  toFun X := ⟨(X.a + X.b) / 2, (X.w 0 - X.v 0) / 2,
    (X.w 1 - X.v 1) / 2, (X.w 2 - X.v 2) / 2⟩
  map_add' X Y := by
    apply QuaternionAlgebra.ext <;>
      simp [ZornVectorMatrix.add] <;> ring
  map_smul' r X := by
    apply QuaternionAlgebra.ext <;>
      simp [ZornVectorMatrix.smul] <;> ring

@[simp] theorem quaternionRetraction_embedding (q : Quaternion ℝ) :
    quaternionRetraction (quaternionEmbedding q) = q := by
  apply QuaternionAlgebra.ext <;>
    simp [quaternionRetraction, quaternionEmbedding] <;> ring

/-- The actual idempotent endomorphism onto the existing quaternion range. -/
def quaternionProjection : Z →ₗ[ℝ] Z :=
  quaternionEmbedding.comp quaternionRetraction

theorem quaternionProjection_apply (X : Z) :
    quaternionProjection X =
      ⟨(X.a + X.b) / 2, fun i => (X.v i - X.w i) / 2,
        fun i => (X.w i - X.v i) / 2, (X.a + X.b) / 2⟩ := by
  ext i <;> (try fin_cases i) <;>
    simp [quaternionProjection, quaternionRetraction, quaternionEmbedding] <;> ring

@[simp] theorem quaternionProjection_embedding (q : Quaternion ℝ) :
    quaternionProjection (quaternionEmbedding q) = quaternionEmbedding q := by
  simp [quaternionProjection]

@[simp] theorem quaternionProjection_idempotent (X : Z) :
    quaternionProjection (quaternionProjection X) = quaternionProjection X := by
  simp [quaternionProjection]

theorem quaternionProjection_eq_self_iff (X : Z) :
    quaternionProjection X = X ↔ X ∈ LinearMap.range quaternionEmbedding := by
  constructor
  · intro h
    exact ⟨quaternionRetraction X, h⟩
  · rintro ⟨q, rfl⟩
    exact quaternionProjection_embedding q

theorem quaternionProjection_range :
    LinearMap.range quaternionProjection = LinearMap.range quaternionEmbedding := by
  ext X
  constructor
  · rintro ⟨Y, rfl⟩
    exact ⟨quaternionRetraction Y, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨quaternionEmbedding q, quaternionProjection_embedding q⟩

theorem quaternionRange_finrank :
    Module.finrank ℝ (LinearMap.range quaternionEmbedding) = 4 := by
  rw [LinearMap.finrank_range_of_inj quaternionEmbedding_injective]
  exact Quaternion.finrank_eq_four

theorem quaternionProjection_selfAdjoint (X Y : Z) :
    coefficientPairing (quaternionProjection X) Y =
      coefficientPairing X (quaternionProjection Y) := by
  rw [quaternionProjection_apply, quaternionProjection_apply]
  simp [coefficientPairing, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- One ordered quaternion pair detects all four complementary coordinates.
The two multiplication orders in the associator are kept explicitly. -/
theorem associator_quaternion_i_j (X : Z) :
    _root_.associator X
      (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))
      (quaternionEmbedding (⟨0, 0, 1, 0⟩ : Quaternion ℝ)) =
      ⟨-(X.v 2 + X.w 2), ![X.v 1 + X.w 1, -(X.v 0 + X.w 0), X.a - X.b],
        ![X.v 1 + X.w 1, -(X.v 0 + X.w 0), X.a - X.b], X.v 2 + X.w 2⟩ := by
  ext i <;> (try fin_cases i) <;>
    simp [_root_.associator_apply, quaternionEmbedding, ZornVectorMatrix.mul,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem associator_quaternion_i_j_zero_iff (X : Z) :
    _root_.associator X
      (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))
      (quaternionEmbedding (⟨0, 0, 1, 0⟩ : Quaternion ℝ)) = 0 ↔
      X ∈ LinearMap.range quaternionEmbedding := by
  constructor
  · intro h
    rw [associator_quaternion_i_j] at h
    have ha := congrArg ZornVectorMatrix.a h
    have hv0 := congrArg (fun Y : Z => Y.v 0) h
    have hv1 := congrArg (fun Y : Z => Y.v 1) h
    have hv2 := congrArg (fun Y : Z => Y.v 2) h
    simp [ZornVectorMatrix.zero] at ha hv0 hv1 hv2
    have hab : X.a = X.b := by linarith
    have hv : ∀ i : Fin 3, X.v i = -X.w i := by
      intro i
      fin_cases i <;> linarith
    refine ⟨⟨X.a, X.w 0, X.w 1, X.w 2⟩, ?_⟩
    ext i <;> (try fin_cases i) <;> simp [quaternionEmbedding, hab, hv]
  · rintro ⟨q, rfl⟩
    exact sub_eq_zero.mpr (quaternion_sector_associative q
      (⟨0, 1, 0, 0⟩ : Quaternion ℝ) (⟨0, 0, 1, 0⟩ : Quaternion ℝ))

/-- With `ell = diag(1,-1)` and right notation `q ell`, the exact Cayley-Dickson
sign is positive and the quaternion multiplication is `q * k`. -/
theorem associator_quaternion_mul_ell_i_j (q : Quaternion ℝ) :
    _root_.associator
      (ZornVectorMatrix.mul (quaternionEmbedding q) (ZornVectorMatrix.diagonal 1 (-1)))
      (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))
      (quaternionEmbedding (⟨0, 0, 1, 0⟩ : Quaternion ℝ)) =
      (2 : ℝ) • ZornVectorMatrix.mul
        (quaternionEmbedding (q * (⟨0, 0, 0, 1⟩ : Quaternion ℝ)))
        (ZornVectorMatrix.diagonal 1 (-1)) := by
  rw [associator_quaternion_i_j]
  ext i <;> (try fin_cases i) <;>
    simp [quaternionEmbedding, ZornVectorMatrix.mul, ZornVectorMatrix.diagonal,
      ZornVectorMatrix.smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- Projection of both probes, with all 64 ordered basis pairs retained. -/
def projectedAssociatorGram : LinearMap.BilinForm ℝ Z :=
  ∑ i : BasisIndex, ∑ j : BasisIndex,
    coefficientPairing.compl₁₂
      (leftRightCommutator (R := ℝ)
        (quaternionProjection (signedBasis (R := ℝ) i))
        (quaternionProjection (signedBasis (R := ℝ) j)))
      (leftRightCommutator (R := ℝ)
        (quaternionProjection (signedBasis (R := ℝ) i))
        (quaternionProjection (signedBasis (R := ℝ) j)))

theorem projectedAssociatorGram_apply (X Y : Z) :
    projectedAssociatorGram X Y =
      ∑ i : BasisIndex, ∑ j : BasisIndex,
        coefficientPairing
          (_root_.associator X
            (quaternionProjection (signedBasis (R := ℝ) i))
            (quaternionProjection (signedBasis (R := ℝ) j)))
          (_root_.associator Y
            (quaternionProjection (signedBasis (R := ℝ) i))
            (quaternionProjection (signedBasis (R := ℝ) j))) := by
  simp only [projectedAssociatorGram, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.compl₁₂_apply, leftRightCommutator_apply_first]

theorem projectedAssociatorGram_symm (X Y : Z) :
    projectedAssociatorGram X Y = projectedAssociatorGram Y X := by
  rw [projectedAssociatorGram_apply, projectedAssociatorGram_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact coefficientPairing_symm _ _

theorem projectedAssociatorGram_isSymm : projectedAssociatorGram.IsSymm :=
  ⟨projectedAssociatorGram_symm⟩

theorem projectedAssociatorGram_nonneg (X : Z) :
    0 ≤ projectedAssociatorGram X X := by
  rw [projectedAssociatorGram_apply]
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => coefficientPairing_nonneg _

theorem projectedAssociatorGram_zero_iff_basis (X : Z) :
    projectedAssociatorGram X X = 0 ↔
      ∀ i j : BasisIndex,
        _root_.associator X
          (quaternionProjection (signedBasis (R := ℝ) i))
          (quaternionProjection (signedBasis (R := ℝ) j)) = 0 := by
  rw [projectedAssociatorGram_apply]
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
    simp

/-- The projected probe parameters form a native bilinear map, so full-basis
testing extends to arbitrary probes. -/
private def projectedAssociatorParameters (X : Z) : Z →ₗ[ℝ] Z →ₗ[ℝ] Z :=
  LinearMap.mk₂ ℝ
    (fun y z => _root_.associator X (quaternionProjection y) (quaternionProjection z))
    (by
      intro y₁ y₂ z
      simp only [map_add, _root_.associator_apply, _root_.mul_add, _root_.add_mul]
      abel)
    (by
      intro r y z
      simp only [map_smul, _root_.associator_apply, _root_.mul_smul_comm,
        _root_.smul_mul_assoc, _root_.smul_sub])
    (by
      intro y z₁ z₂
      simp only [map_add, _root_.associator_apply, _root_.mul_add]
      abel)
    (by
      intro r y z
      simp only [map_smul, _root_.associator_apply, _root_.mul_smul_comm,
        _root_.smul_sub])

theorem projected_basis_zero_iff (X : Z) :
    (∀ i j : BasisIndex,
      _root_.associator X
        (quaternionProjection (signedBasis (R := ℝ) i))
        (quaternionProjection (signedBasis (R := ℝ) j)) = 0) ↔
      ∀ y z : Z, _root_.associator X (quaternionProjection y) (quaternionProjection z) = 0 := by
  constructor
  · intro h
    have hmap : projectedAssociatorParameters X = 0 := by
      apply (signedBasis (R := ℝ)).ext
      intro i
      apply (signedBasis (R := ℝ)).ext
      intro j
      exact h i j
    intro y z
    change projectedAssociatorParameters X y z = 0
    rw [hmap]
  · intro h i j
    exact h _ _

theorem projected_associator_zero_iff (X : Z) :
    (∀ y z : Z, _root_.associator X (quaternionProjection y) (quaternionProjection z) = 0) ↔
      X ∈ LinearMap.range quaternionEmbedding := by
  constructor
  · intro h
    apply (associator_quaternion_i_j_zero_iff X).mp
    simpa only [quaternionProjection_embedding] using
      h (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))
        (quaternionEmbedding (⟨0, 0, 1, 0⟩ : Quaternion ℝ))
  · rintro ⟨q, rfl⟩ y z
    exact sub_eq_zero.mpr (quaternion_sector_associative q
      (quaternionRetraction y) (quaternionRetraction z))

/-- The projected Gram vanishes exactly on the quaternion register. -/
theorem projectedAssociatorGram_zero_iff (X : Z) :
    projectedAssociatorGram X X = 0 ↔ X ∈ LinearMap.range quaternionEmbedding :=
  (projectedAssociatorGram_zero_iff_basis X).trans
    ((projected_basis_zero_iff X).trans (projected_associator_zero_iff X))

theorem projectedAssociatorGram_left_kernel_iff (X : Z) :
    (∀ Y : Z, projectedAssociatorGram X Y = 0) ↔
      X ∈ LinearMap.range quaternionEmbedding := by
  constructor
  · intro h
    exact (projectedAssociatorGram_zero_iff X).mp (h X)
  · intro h Y
    have hX := (projected_associator_zero_iff X).mpr h
    rw [projectedAssociatorGram_apply]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [hX]
    simp

theorem projectedAssociatorGram_pos_of_not_quaternion {X : Z}
    (hX : X ∉ LinearMap.range quaternionEmbedding) :
    0 < projectedAssociatorGram X X := by
  apply lt_of_le_of_ne (projectedAssociatorGram_nonneg X)
  intro h
  exact hX ((projectedAssociatorGram_zero_iff X).mp h.symm)

theorem projectedAssociatorGram_quaternion (q : Quaternion ℝ) :
    projectedAssociatorGram (quaternionEmbedding q) (quaternionEmbedding q) = 0 :=
  (projectedAssociatorGram_zero_iff _).mpr ⟨q, rfl⟩

/-- A positive witness outside the quaternion register. -/
theorem projectedAssociatorGram_E11_pos :
    0 < projectedAssociatorGram (ZornVectorMatrix.E11 : Z) ZornVectorMatrix.E11 := by
  apply projectedAssociatorGram_pos_of_not_quaternion
  rintro ⟨q, hq⟩
  have ha := congrArg ZornVectorMatrix.a hq
  have hb := congrArg ZornVectorMatrix.b hq
  norm_num [quaternionEmbedding, ZornVectorMatrix.E11] at ha hb
  linarith

/-- The same quaternion state is killed by the projected Gram and detected
strictly positively by the ambient Gram. -/
theorem quaternion_i_ambient_projected_contrast :
    projectedAssociatorGram
      (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))
      (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ)) = 0 ∧
    0 < associatorGram
      (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ))
      (quaternionEmbedding (⟨0, 1, 0, 0⟩ : Quaternion ℝ)) :=
  ⟨projectedAssociatorGram_quaternion _, associatorGram_quaternion_i_pos⟩

end InfoGeometry.Algebra.ZornQuaternionProjectedGram

end
