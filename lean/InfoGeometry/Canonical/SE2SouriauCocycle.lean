import InfoGeometry.Canonical.Barbaresco2020Souriau
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The finite `SE(2)` translation cocycle

The homogeneous matrix multiplication owner already proves the full `3 × 3`
product formula.  This file extracts its translation component as the
standard affine cocycle over the rotation block.
-/

namespace InfoGeometry.Canonical.SE2SouriauCocycle

open InfoGeometry.Canonical.Barbaresco2020Souriau

abbrev Point2 := ℝ × ℝ
abbrev SE2Parameters := ℝ × ℝ × ℝ × ℝ

def rotationAction (c s : ℝ) (v : Point2) : Point2 :=
  (c * v.1 - s * v.2, s * v.1 + c * v.2)

def translationPart (_c _s tx ty : ℝ) : Point2 := (tx, ty)

def se2ParameterProduct
    (c₁ s₁ tx₁ ty₁ c₂ s₂ tx₂ ty₂ : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (c₁ * c₂ - s₁ * s₂,
    s₁ * c₂ + c₁ * s₂,
    c₁ * tx₂ - s₁ * ty₂ + tx₁,
    s₁ * tx₂ + c₁ * ty₂ + ty₁)

def se2ParameterIdentity : SE2Parameters := (1, 0, 0, 0)

def se2ParameterInverse (g : SE2Parameters) : SE2Parameters :=
  (g.1, -g.2.1,
    -(g.1 * g.2.2.1 + g.2.1 * g.2.2.2),
    g.2.1 * g.2.2.1 - g.1 * g.2.2.2)

def rotationConstraint (g : SE2Parameters) : ℝ :=
  g.1 ^ 2 + g.2.1 ^ 2

def se2RotationParameters : Set SE2Parameters :=
  {g | rotationConstraint g = 1}

theorem continuous_rotationConstraint : Continuous rotationConstraint := by
  unfold rotationConstraint
  fun_prop

theorem isClosed_se2RotationParameters :
    IsClosed se2RotationParameters := by
  unfold se2RotationParameters
  exact isClosed_singleton.preimage continuous_rotationConstraint

theorem se2ParameterIdentity_mem_rotation :
    se2ParameterIdentity ∈ se2RotationParameters := by
  unfold se2RotationParameters rotationConstraint se2ParameterIdentity
  norm_num

theorem rotationConstraint_inverse
    (g : SE2Parameters) (hg : g ∈ se2RotationParameters) :
    se2ParameterInverse g ∈ se2RotationParameters := by
  have hrot : g.1 ^ 2 + g.2.1 ^ 2 = 1 := by
    simpa [se2RotationParameters, rotationConstraint] using hg
  change rotationConstraint (se2ParameterInverse g) = 1
  unfold rotationConstraint
  dsimp [se2ParameterInverse]
  nlinarith [hrot]

theorem se2ParameterProduct_inverse_left
    (g : SE2Parameters)
    (hrot : g.1 ^ 2 + g.2.1 ^ 2 = 1) :
    se2ParameterProduct
        (se2ParameterInverse g).1 (se2ParameterInverse g).2.1
          (se2ParameterInverse g).2.2.1 (se2ParameterInverse g).2.2.2
        g.1 g.2.1 g.2.2.1 g.2.2.2 = se2ParameterIdentity := by
  ext <;> dsimp [se2ParameterProduct, se2ParameterInverse,
    se2ParameterIdentity]
  · nlinarith [hrot]
  · ring
  · ring_nf
  · ring_nf

theorem se2ParameterProduct_inverse_right
    (g : SE2Parameters)
    (hrot : g.1 ^ 2 + g.2.1 ^ 2 = 1) :
    se2ParameterProduct
        g.1 g.2.1 g.2.2.1 g.2.2.2
        (se2ParameterInverse g).1 (se2ParameterInverse g).2.1
          (se2ParameterInverse g).2.2.1 (se2ParameterInverse g).2.2.2 = se2ParameterIdentity := by
  ext <;> dsimp [se2ParameterProduct, se2ParameterInverse,
    se2ParameterIdentity]
  · nlinarith [hrot]
  · ring
  · ring_nf
    linear_combination -g.2.2.1 * hrot
  · ring_nf
    linear_combination -g.2.2.2 * hrot

def left_se2ParameterTranslation
    (g h : SE2Parameters) : SE2Parameters :=
  se2ParameterProduct g.1 g.2.1 g.2.2.1 g.2.2.2
    h.1 h.2.1 h.2.2.1 h.2.2.2

def right_se2ParameterTranslation
    (g h : SE2Parameters) : SE2Parameters :=
  se2ParameterProduct h.1 h.2.1 h.2.2.1 h.2.2.2
    g.1 g.2.1 g.2.2.1 g.2.2.2

theorem se2_translation_cocycle
    (c₁ s₁ tx₁ ty₁ c₂ s₂ tx₂ ty₂ : ℝ) :
    translationPart (se2ParameterProduct c₁ s₁ tx₁ ty₁ c₂ s₂ tx₂ ty₂).1
        (se2ParameterProduct c₁ s₁ tx₁ ty₁ c₂ s₂ tx₂ ty₂).2.1
        (se2ParameterProduct c₁ s₁ tx₁ ty₁ c₂ s₂ tx₂ ty₂).2.2.1
        (se2ParameterProduct c₁ s₁ tx₁ ty₁ c₂ s₂ tx₂ ty₂).2.2.2 =
      (tx₁, ty₁) + (rotationAction c₁ s₁ (tx₂, ty₂)) := by
  apply Prod.ext <;> dsimp [translationPart, se2ParameterProduct, rotationAction]
  · ring
  · ring

theorem se2_matrix_translation_cocycle
    (c₁ s₁ tx₁ ty₁ c₂ s₂ tx₂ ty₂ : ℝ) :
    (se2GroupMatrix c₁ s₁ tx₁ ty₁ *
        se2GroupMatrix c₂ s₂ tx₂ ty₂) 0 2 =
      tx₁ + (rotationAction c₁ s₁ (tx₂, ty₂)).1 := by
  rw [se2GroupMatrix_mul]
  simp [se2GroupMatrix, rotationAction]
  ring

theorem continuous_rotationAction :
    Continuous (fun q : ℝ × ℝ × Point2 =>
      rotationAction q.1 q.2.1 q.2.2) := by
  unfold rotationAction
  fun_prop

theorem continuous_translation_cocycle :
    Continuous (fun q : (ℝ × ℝ) × Point2 × Point2 =>
      (q.2.1 + rotationAction q.1.1 q.1.2 q.2.2)) := by
  unfold rotationAction
  fun_prop

/- The coordinate multiplication law is polynomial, hence continuous on its
  finite-dimensional parameter space.  This is the topological edge of the
  algebraic cocycle identity above. -/
theorem continuous_se2ParameterProduct :
    Continuous (fun q : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ =>
      se2ParameterProduct q.1 q.2.1 q.2.2.1 q.2.2.2.1
        q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2) := by
  unfold se2ParameterProduct
  fun_prop

theorem continuous_left_se2ParameterTranslation (g : SE2Parameters) :
    Continuous (left_se2ParameterTranslation g) := by
  unfold left_se2ParameterTranslation se2ParameterProduct
  fun_prop

theorem continuous_right_se2ParameterTranslation (g : SE2Parameters) :
    Continuous (right_se2ParameterTranslation g) := by
  unfold right_se2ParameterTranslation se2ParameterProduct
  fun_prop

theorem rotationConstraint_left_product
    (g h : SE2Parameters)
    (hg : g ∈ se2RotationParameters)
    (hh : h ∈ se2RotationParameters) :
    left_se2ParameterTranslation g h ∈ se2RotationParameters := by
  unfold se2RotationParameters rotationConstraint at hg hh ⊢
  dsimp [left_se2ParameterTranslation, se2ParameterProduct]
  calc
    (g.1 * h.1 - g.2.1 * h.2.1) ^ 2
        + (g.2.1 * h.1 + g.1 * h.2.1) ^ 2 =
      (g.1 ^ 2 + g.2.1 ^ 2) * (h.1 ^ 2 + h.2.1 ^ 2) := by ring
    _ = 1 := by rw [hg, hh]; norm_num

theorem rotationConstraint_right_product
    (g h : SE2Parameters)
    (hg : g ∈ se2RotationParameters)
    (hh : h ∈ se2RotationParameters) :
    right_se2ParameterTranslation g h ∈ se2RotationParameters := by
  unfold se2RotationParameters rotationConstraint at hg hh ⊢
  dsimp [right_se2ParameterTranslation, se2ParameterProduct]
  calc
    (h.1 * g.1 - h.2.1 * g.2.1) ^ 2
        + (h.2.1 * g.1 + h.1 * g.2.1) ^ 2 =
      (h.1 ^ 2 + h.2.1 ^ 2) * (g.1 ^ 2 + g.2.1 ^ 2) := by ring
    _ = 1 := by rw [hh, hg]; norm_num

abbrev SE2RotationCarrier := {g : SE2Parameters // g ∈ se2RotationParameters}

def rotationCarrierIdentity : SE2RotationCarrier :=
  ⟨se2ParameterIdentity, se2ParameterIdentity_mem_rotation⟩

def rotationCarrierProduct
    (g h : SE2RotationCarrier) : SE2RotationCarrier :=
  ⟨left_se2ParameterTranslation g.1 h.1,
    rotationConstraint_left_product g.1 h.1 g.2 h.2⟩

def rotationCarrierInverse (g : SE2RotationCarrier) : SE2RotationCarrier :=
  ⟨se2ParameterInverse g.1, rotationConstraint_inverse g.1 g.2⟩

theorem rotationCarrierProduct_assoc
    (g h k : SE2RotationCarrier) :
    rotationCarrierProduct (rotationCarrierProduct g h) k =
      rotationCarrierProduct g (rotationCarrierProduct h k) := by
  apply Subtype.ext
  ext <;> dsimp [rotationCarrierProduct, left_se2ParameterTranslation,
    se2ParameterProduct]
  <;> ring

theorem rotationCarrierProduct_identity_left
    (g : SE2RotationCarrier) :
    rotationCarrierProduct rotationCarrierIdentity g = g := by
  apply Subtype.ext
  ext <;> dsimp [rotationCarrierProduct, left_se2ParameterTranslation,
    se2ParameterProduct, rotationCarrierIdentity, se2ParameterIdentity]
  <;> ring

theorem rotationCarrierProduct_identity_right
    (g : SE2RotationCarrier) :
    rotationCarrierProduct g rotationCarrierIdentity = g := by
  apply Subtype.ext
  ext <;> dsimp [rotationCarrierProduct, left_se2ParameterTranslation,
    se2ParameterProduct, rotationCarrierIdentity, se2ParameterIdentity]
  <;> ring

theorem rotationCarrierProduct_inverse_left
    (g : SE2RotationCarrier) :
    rotationCarrierProduct (rotationCarrierInverse g) g =
      rotationCarrierIdentity := by
  apply Subtype.ext
  change se2ParameterProduct
      (se2ParameterInverse g.1).1 (se2ParameterInverse g.1).2.1
        (se2ParameterInverse g.1).2.2.1 (se2ParameterInverse g.1).2.2.2
      (g.1).1 (g.1).2.1 (g.1).2.2.1 (g.1).2.2.2 = se2ParameterIdentity
  apply se2ParameterProduct_inverse_left g.1
  exact g.2

theorem rotationCarrierProduct_inverse_right
    (g : SE2RotationCarrier) :
    rotationCarrierProduct g (rotationCarrierInverse g) =
      rotationCarrierIdentity := by
  apply Subtype.ext
  change se2ParameterProduct
      (g.1).1 (g.1).2.1 (g.1).2.2.1 (g.1).2.2.2
      (se2ParameterInverse g.1).1 (se2ParameterInverse g.1).2.1
        (se2ParameterInverse g.1).2.2.1 (se2ParameterInverse g.1).2.2.2 = se2ParameterIdentity
  apply se2ParameterProduct_inverse_right g.1
  exact g.2

instance : Group SE2RotationCarrier where
  mul := rotationCarrierProduct
  one := rotationCarrierIdentity
  inv := rotationCarrierInverse
  mul_assoc := rotationCarrierProduct_assoc
  one_mul := rotationCarrierProduct_identity_left
  mul_one := rotationCarrierProduct_identity_right
  inv_mul_cancel := rotationCarrierProduct_inverse_left

theorem continuous_se2ParameterInverse :
    Continuous se2ParameterInverse := by
  unfold se2ParameterInverse
  fun_prop

theorem continuousOn_se2ParameterInverse :
    ContinuousOn se2ParameterInverse se2RotationParameters :=
  continuous_se2ParameterInverse.continuousOn

theorem se2ParameterProduct_inverse_left_of_mem
    (g : SE2Parameters) (hg : g ∈ se2RotationParameters) :
    se2ParameterProduct
        (se2ParameterInverse g).1 (se2ParameterInverse g).2.1
          (se2ParameterInverse g).2.2.1 (se2ParameterInverse g).2.2.2
        g.1 g.2.1 g.2.2.1 g.2.2.2 = se2ParameterIdentity := by
  apply se2ParameterProduct_inverse_left g
  exact hg

theorem se2ParameterProduct_inverse_right_of_mem
    (g : SE2Parameters) (hg : g ∈ se2RotationParameters) :
    se2ParameterProduct
        g.1 g.2.1 g.2.2.1 g.2.2.2
        (se2ParameterInverse g).1 (se2ParameterInverse g).2.1
          (se2ParameterInverse g).2.2.1 (se2ParameterInverse g).2.2.2 = se2ParameterIdentity := by
  apply se2ParameterProduct_inverse_right g
  exact hg

theorem continuous_rotationCarrierProduct_left
    (g : SE2RotationCarrier) :
    Continuous (rotationCarrierProduct g) := by
  apply Continuous.subtype_mk
  exact (continuous_left_se2ParameterTranslation g.1).comp
    continuous_subtype_val

theorem continuous_rotationCarrierProduct_right
    (g : SE2RotationCarrier) :
    Continuous (fun h => rotationCarrierProduct h g) := by
  apply Continuous.subtype_mk
  exact (continuous_right_se2ParameterTranslation g.1).comp
    continuous_subtype_val

theorem continuous_rotationCarrierProduct :
    Continuous (fun p : SE2RotationCarrier × SE2RotationCarrier =>
      rotationCarrierProduct p.1 p.2) := by
  apply Continuous.subtype_mk
  unfold left_se2ParameterTranslation se2ParameterProduct
  fun_prop

theorem continuous_rotationCarrierInverse :
    Continuous rotationCarrierInverse := by
  apply Continuous.subtype_mk
  exact continuous_se2ParameterInverse.comp continuous_subtype_val

instance : ContinuousMul SE2RotationCarrier where
  continuous_mul := continuous_rotationCarrierProduct

instance : ContinuousInv SE2RotationCarrier where
  continuous_inv := continuous_rotationCarrierInverse

instance : IsTopologicalGroup SE2RotationCarrier := IsTopologicalGroup.mk

/- Matrix-valued continuity is proved entrywise because the notation `!![...]`
  is a finite function constructor rather than a registered polynomial map. -/
theorem continuous_se2GroupMatrix :
    Continuous (fun q : ℝ × ℝ × ℝ × ℝ =>
      se2GroupMatrix q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold se2GroupMatrix
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_se2GroupMatrix_product :
    Continuous (fun q : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ =>
      se2GroupMatrix q.1 q.2.1 q.2.2.1 q.2.2.2.1 *
        se2GroupMatrix q.2.2.2.2.1 q.2.2.2.2.2.1
          q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2) := by
  unfold se2GroupMatrix
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> fun_prop

/-! ## Topological matrix representation

The rotation-constrained carrier is not merely an abstract topological group:
its homogeneous `3 × 3` realization is a continuous monoid homomorphism.
The determinant calculation below records the affine `SE(2)` image inside the
invertible matrix locus without introducing an unproved analytic claim. -/

def se2MatrixRepresentation : SE2RotationCarrier →* Mat3 where
  toFun := fun g =>
    se2GroupMatrix g.1.1 g.1.2.1 g.1.2.2.1 g.1.2.2.2
  map_one' := by
    change se2GroupMatrix 1 0 0 0 = 1
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [se2GroupMatrix]
  map_mul' := by
    intro g h
    symm
    exact se2GroupMatrix_mul _ _ _ _ _ _ _ _

theorem continuous_se2MatrixRepresentation :
    Continuous (se2MatrixRepresentation : SE2RotationCarrier → Mat3) := by
  unfold se2MatrixRepresentation
  exact continuous_se2GroupMatrix.comp continuous_subtype_val

theorem se2MatrixRepresentation_det (g : SE2RotationCarrier) :
    Matrix.det (se2MatrixRepresentation g) = 1 := by
  have hrot : g.1.1 ^ 2 + g.1.2.1 ^ 2 = 1 := by
    exact g.2
  simp [se2MatrixRepresentation, se2GroupMatrix, Matrix.det_fin_three]
  simpa [pow_two] using hrot

theorem se2MatrixRepresentation_det_ne_zero (g : SE2RotationCarrier) :
    Matrix.det (se2MatrixRepresentation g) ≠ 0 := by
  rw [se2MatrixRepresentation_det]
  norm_num

abbrev HomogeneousPoint := InfoGeometry.Algebra.FiniteSpin.Vec3R

def se2MatrixAction (g : SE2RotationCarrier) (v : HomogeneousPoint) :
    HomogeneousPoint :=
  Matrix.mulVec (se2MatrixRepresentation g) v

theorem se2MatrixAction_mul
    (g h : SE2RotationCarrier) (v : HomogeneousPoint) :
    se2MatrixAction (g * h) v = se2MatrixAction g (se2MatrixAction h v) := by
  dsimp [se2MatrixAction]
  rw [map_mul]
  exact (Matrix.mulVec_mulVec v (se2MatrixRepresentation g)
    (se2MatrixRepresentation h)).symm

theorem se2MatrixAction_one (v : HomogeneousPoint) :
    se2MatrixAction (1 : SE2RotationCarrier) v = v := by
  dsimp [se2MatrixAction]
  rw [map_one, Matrix.one_mulVec]

theorem continuous_se2MatrixAction :
    Continuous (fun p : SE2RotationCarrier × HomogeneousPoint =>
      se2MatrixAction p.1 p.2) := by
  unfold se2MatrixAction
  apply Continuous.matrix_mulVec
  · exact continuous_se2MatrixRepresentation.comp continuous_fst
  · exact continuous_snd

theorem continuous_se2MatrixAction_fixed (g : SE2RotationCarrier) :
    Continuous (se2MatrixAction g) := by
  unfold se2MatrixAction
  exact Continuous.matrix_mulVec continuous_const continuous_id

def se2MatrixActionHomeomorph (g : SE2RotationCarrier) :
    HomogeneousPoint ≃ₜ HomogeneousPoint where
  toFun := se2MatrixAction g
  invFun := se2MatrixAction g⁻¹
  left_inv := by
    intro v
    rw [← se2MatrixAction_mul, inv_mul_cancel, se2MatrixAction_one]
  right_inv := by
    intro v
    rw [← se2MatrixAction_mul, mul_inv_cancel, se2MatrixAction_one]
  continuous_toFun := continuous_se2MatrixAction_fixed g
  continuous_invFun := continuous_se2MatrixAction_fixed g⁻¹

theorem se2MatrixActionHomeomorph_apply_mul
    (g h : SE2RotationCarrier) (v : HomogeneousPoint) :
    se2MatrixActionHomeomorph (g * h) v =
      se2MatrixActionHomeomorph g (se2MatrixActionHomeomorph h v) := by
  exact se2MatrixAction_mul g h v

theorem se2MatrixActionHomeomorph_one :
    se2MatrixActionHomeomorph (1 : SE2RotationCarrier) =
      Homeomorph.refl HomogeneousPoint := by
  apply Homeomorph.ext
  intro v
  exact se2MatrixAction_one v

/-! The determinant-one image is now exposed in Mathlib's native matrix
`SpecialLinearGroup`, rather than left as an informal invertibility claim. -/

def se2SpecialLinearRepresentation :
    SE2RotationCarrier →* Matrix.SpecialLinearGroup (Fin 3) ℝ where
  toFun := fun g =>
    ⟨se2MatrixRepresentation g, se2MatrixRepresentation_det g⟩
  map_one' := by
    apply Subtype.ext
    change se2GroupMatrix 1 0 0 0 = 1
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [se2GroupMatrix]
  map_mul' := by
    intro g h
    apply Subtype.ext
    change se2MatrixRepresentation (g * h) =
      se2MatrixRepresentation g * se2MatrixRepresentation h
    exact map_mul se2MatrixRepresentation g h

theorem continuous_se2SpecialLinearRepresentation :
    Continuous (se2SpecialLinearRepresentation :
      SE2RotationCarrier → Matrix.SpecialLinearGroup (Fin 3) ℝ) := by
  apply Continuous.subtype_mk
  exact continuous_se2MatrixRepresentation

end InfoGeometry.Canonical.SE2SouriauCocycle
