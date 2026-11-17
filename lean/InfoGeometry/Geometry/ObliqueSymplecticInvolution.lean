/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ParaHyperkahlerPresymplecticBridge
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Positive compatibility does not force anticommutation

Reuse the existing real symplectic form and split-quaternion matrix frame.
For the convention `G(x,y) = omega(x,I y)`, the positive complex operator is
the native linear map of `-I_mat`. The oblique family
`K_a = K_mat + (a/2) • (J_mat + I_mat)` is an anti-symplectic involution with
one-dimensional isotropic positive and negative eigenspaces.

Its anticommutator with the complex operator is exactly `a • id` and its
commutator is nonzero for every parameter. Thus `a = 1` gives a positive
compatible metric and an anti-symplectic involution which neither commute
nor anticommute. Preserving the positive metric is the extra condition:
in this family it holds exactly when `a = 0`.

All carriers, bilinear forms, endomorphisms, eigenspaces, spans and dimensions
are native Mathlib objects. The final counterexample collects proved facts
about these explicit objects. No geometric laws are stored as assumptions,
and no curved connection, statistical metric or Clifford faithfulness
claim is made.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Geometry.ObliqueSymplecticInvolution

open scoped Matrix
open InfoGeometry.Canonical.ParaHyperkahlerPresymplecticBridge

/-- An oblique involution assembled from the existing matrix frame. -/
def obliqueMatrix (a : ℝ) : Mat2 :=
  K_mat + (a / 2) • (J_mat + I_mat)

theorem obliqueMatrix_eq (a : ℝ) : obliqueMatrix a = !![1, a; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [obliqueMatrix, K_mat, J_mat, I_mat]; ring)

/-- The existing symplectic form, bundled by the native matrix-to-form equivalence. -/
def omega : LinearMap.BilinForm ℝ R2 := Matrix.toBilin' I_mat

@[simp] theorem omega_apply (x y : R2) : omega x y = omega2 x y := by
  rw [omega, Matrix.toBilin'_apply]
  simp [I_mat, Fin.sum_univ_two, omega2, sub_eq_add_neg]

/-- Negating the existing elliptic seed gives positivity in the right-slot convention. -/
def complexOp : Module.End ℝ R2 := Matrix.toLin' (-I_mat)

/-- The actual matrix action of the oblique involution. -/
def obliqueOp (a : ℝ) : Module.End ℝ R2 := Matrix.toLin' (obliqueMatrix a)

@[simp] theorem complexOp_apply (x : R2) : complexOp x = ![-x 1, x 0] := by
  change (-I_mat).mulVec x = ![-x 1, x 0]
  ext i
  fin_cases i <;> simp [I_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem obliqueOp_apply (a : ℝ) (x : R2) :
    obliqueOp a x = ![x 0 + a * x 1, -x 1] := by
  change (obliqueMatrix a).mulVec x = ![x 0 + a * x 1, -x 1]
  rw [obliqueMatrix_eq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The compatible metric is the native right composition with the complex operator. -/
def compatibleMetric : LinearMap.BilinForm ℝ R2 := omega.compRight complexOp

theorem compatibleMetric_apply (x y : R2) :
    compatibleMetric x y = x 0 * y 0 + x 1 * y 1 := by
  change omega x (complexOp y) = _
  rw [omega_apply, complexOp_apply]
  simp [omega2]

theorem omega_alternating : omega.IsAlt := by
  intro x
  rw [omega_apply]
  exact omega2_self_zero x

theorem omega_nondegenerate : omega.Nondegenerate := by
  change I_mat.toBilin'.Nondegenerate
  apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' I_mat
  norm_num [I_mat, Matrix.det_fin_two]

theorem compatibleMetric_symmetric (x y : R2) :
    compatibleMetric x y = compatibleMetric y x := by
  rw [compatibleMetric_apply, compatibleMetric_apply,
    mul_comm (x 0) (y 0), mul_comm (x 1) (y 1)]

/-- Strict positivity holds on every nonzero vector, with no parameter restriction. -/
theorem compatibleMetric_positive (x : R2) (hx : x ≠ 0) :
    0 < compatibleMetric x x := by
  rw [compatibleMetric_apply]
  by_cases hx0 : x 0 = 0
  · have hx1 : x 1 ≠ 0 := by
      intro hx1
      apply hx
      ext i
      fin_cases i <;> simp [hx0, hx1]
    simpa [hx0, pow_two] using sq_pos_of_ne_zero hx1
  · have h0 := sq_pos_of_ne_zero hx0
    have h1 := sq_nonneg (x 1)
    nlinarith

theorem complexOp_sq : complexOp * complexOp = -1 := by
  change (-I_mat).toLin'.comp (-I_mat).toLin' = -LinearMap.id
  rw [← Matrix.toLin'_mul, neg_mul_neg, I_sq, map_neg, Matrix.toLin'_one]

theorem obliqueMatrix_sq (a : ℝ) : obliqueMatrix a * obliqueMatrix a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [obliqueMatrix_eq, Matrix.mul_apply, Fin.sum_univ_two]

theorem obliqueOp_sq (a : ℝ) : obliqueOp a * obliqueOp a = 1 := by
  change (obliqueMatrix a).toLin'.comp (obliqueMatrix a).toLin' = LinearMap.id
  rw [← Matrix.toLin'_mul, obliqueMatrix_sq, Matrix.toLin'_one]

theorem obliqueOp_ne_one (a : ℝ) : obliqueOp a ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : Module.End ℝ R2 => f ![0, 1] 1) h
  norm_num [obliqueOp_apply] at h1

theorem obliqueOp_ne_neg_one (a : ℝ) : obliqueOp a ≠ -1 := by
  intro h
  have h0 := congrArg (fun f : Module.End ℝ R2 => f ![1, 0] 0) h
  norm_num [obliqueOp_apply] at h0

/-- The complex operator preserves the existing symplectic form. -/
theorem complexOp_symplectic (x y : R2) :
    omega (complexOp x) (complexOp y) = omega x y := by
  rw [omega_apply, omega_apply, complexOp_apply, complexOp_apply]
  change (-x 1) * y 0 - x 0 * (-y 1) = x 0 * y 1 - x 1 * y 0
  rw [neg_mul, mul_neg, neg_sub_neg]

/-- The full ordered matrix pullback reverses the existing symplectic matrix. -/
theorem obliqueMatrix_antisymplectic (a : ℝ) :
    (obliqueMatrix a)ᵀ * I_mat * obliqueMatrix a = -I_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [obliqueMatrix_eq, I_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every oblique involution reverses the existing symplectic form. -/
theorem obliqueOp_antisymplectic (a : ℝ) (x y : R2) :
    omega (obliqueOp a x) (obliqueOp a y) = -omega x y := by
  change (I_mat.toBilin'.comp (obliqueMatrix a).toLin'
    (obliqueMatrix a).toLin') x y = (-I_mat.toBilin') x y
  rw [Matrix.toBilin'_comp, obliqueMatrix_antisymplectic, map_neg]

/-- The actual ordered matrix anticommutator is a scalar multiple of the identity. -/
theorem matrix_anticommutator (a : ℝ) :
    (-I_mat) * obliqueMatrix a + obliqueMatrix a * (-I_mat) = a • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I_mat, obliqueMatrix_eq]

/-- Transport the ordered matrix identity to native endomorphisms. -/
theorem operator_anticommutator (a : ℝ) :
    complexOp * obliqueOp a + obliqueOp a * complexOp = a • (1 : Module.End ℝ R2) := by
  change (-I_mat).toLin'.comp (obliqueMatrix a).toLin' +
    (obliqueMatrix a).toLin'.comp (-I_mat).toLin' = a • LinearMap.id
  have h := congrArg (fun M : Mat2 => Matrix.toLin' M) (matrix_anticommutator a)
  simpa only [map_add, map_smul, Matrix.toLin'_mul, Matrix.toLin'_one] using h

/-- The two operators never commute, including at the anticommuting parameter zero. -/
theorem operator_noncommutation (a : ℝ) :
    complexOp * obliqueOp a ≠ obliqueOp a * complexOp := by
  intro h
  have h0 := congrArg (fun f : Module.End ℝ R2 => f ![0, 1] 0) h
  norm_num [Module.End.mul_apply, complexOp_apply, obliqueOp_apply] at h0

theorem operator_anticommutation_iff (a : ℝ) :
    complexOp * obliqueOp a = -(obliqueOp a * complexOp) ↔ a = 0 := by
  rw [eq_neg_iff_add_eq_zero, operator_anticommutator]
  constructor
  · intro h
    have h0 := congrArg (fun f : Module.End ℝ R2 => f ![1, 0] 0) h
    simpa using h0
  · rintro rfl
    exact zero_smul ℝ (1 : Module.End ℝ R2)

/-- Metric isometry is an additional condition, satisfied only by the orthogonal member. -/
theorem compatibleMetric_isometry_iff (a : ℝ) :
    (∀ x y : R2, compatibleMetric (obliqueOp a x) (obliqueOp a y) =
      compatibleMetric x y) ↔ a = 0 := by
  constructor
  · intro h
    have h01 := h ![1, 0] ![0, 1]
    simpa [compatibleMetric_apply, obliqueOp_apply] using h01
  · rintro rfl
    intro x y
    simp [compatibleMetric_apply, obliqueOp_apply]

theorem mem_positive_eigenspace_iff (a : ℝ) (x : R2) :
    x ∈ Module.End.eigenspace (obliqueOp a) 1 ↔ x 1 = 0 := by
  rw [Module.End.mem_eigenspace_iff, one_smul, obliqueOp_apply]
  constructor
  · intro h
    have h1 := congrFun h (1 : Fin 2)
    change -x 1 = x 1 at h1
    exact CharZero.neg_eq_self_iff.mp h1
  · intro h
    ext i
    fin_cases i <;> simp [h]

theorem mem_negative_eigenspace_iff (a : ℝ) (x : R2) :
    x ∈ Module.End.eigenspace (obliqueOp a) (-1) ↔ 2 * x 0 + a * x 1 = 0 := by
  rw [Module.End.mem_eigenspace_iff, neg_one_smul, obliqueOp_apply]
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 2)
    change x 0 + a * x 1 = -x 0 at h0
    rw [two_mul, add_assoc, h0, add_neg_cancel]
  · intro h
    ext i
    fin_cases i
    · change x 0 + a * x 1 = -x 0
      apply eq_neg_iff_add_eq_zero.mpr
      calc
        (x 0 + a * x 1) + x 0 = (x 0 + x 0) + a * x 1 :=
          add_right_comm _ _ _
        _ = 0 := by simpa only [two_mul] using h
    · rfl

/-- The positive eigenspace is the actual span of the first coordinate vector. -/
theorem positive_eigenspace_eq_span (a : ℝ) :
    Module.End.eigenspace (obliqueOp a) 1 = ℝ ∙ (![1, 0] : R2) := by
  ext x
  rw [mem_positive_eigenspace_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i <;> simp [h]
  · rintro ⟨c, rfl⟩
    simp

/-- The negative eigenspace is the actual oblique line, with its parameter-dependent slope. -/
theorem negative_eigenspace_eq_span (a : ℝ) :
    Module.End.eigenspace (obliqueOp a) (-1) = ℝ ∙ (![-a / 2, 1] : R2) := by
  ext x
  rw [mem_negative_eigenspace_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨x 1, ?_⟩
    ext i
    fin_cases i
    · change x 1 * (-a / 2) = x 0
      nlinarith
    · simp
  · rintro ⟨c, rfl⟩
    simp
    ring

theorem positive_eigenspace_finrank (a : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (obliqueOp a) 1) = 1 := by
  rw [positive_eigenspace_eq_span]
  apply finrank_span_singleton
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num at h0

theorem negative_eigenspace_finrank (a : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (obliqueOp a) (-1)) = 1 := by
  rw [negative_eigenspace_eq_span]
  apply finrank_span_singleton
  intro h
  have h1 := congrFun h (1 : Fin 2)
  norm_num at h1

theorem positive_eigenspace_isotropic (a : ℝ) {x y : R2}
    (hx : x ∈ Module.End.eigenspace (obliqueOp a) 1)
    (hy : y ∈ Module.End.eigenspace (obliqueOp a) 1) : omega x y = 0 := by
  have hx1 := (mem_positive_eigenspace_iff a x).mp hx
  have hy1 := (mem_positive_eigenspace_iff a y).mp hy
  simp [omega_apply, omega2, hx1, hy1]

theorem negative_eigenspace_isotropic (a : ℝ) {x y : R2}
    (hx : x ∈ Module.End.eigenspace (obliqueOp a) (-1))
    (hy : y ∈ Module.End.eigenspace (obliqueOp a) (-1)) : omega x y = 0 := by
  rw [negative_eigenspace_eq_span] at hx hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hzero := omega_alternating (![-a / 2, 1] : R2)
  simp only [map_smul, LinearMap.smul_apply, hzero, smul_zero]

/-- The two eigenlines are paired nontrivially by the same symplectic form. -/
theorem eigenvectors_cross_pairing (a : ℝ) :
    omega (![1, 0] : R2) (![-a / 2, 1] : R2) = 1 := by
  norm_num [omega_apply, omega2]

/-- Without anticommutation, the proposed ordered `I*K` metric intertwiner fails. -/
theorem ordered_intertwiner_failure :
    (omega.compLeft (obliqueOp 1))
      ((complexOp * obliqueOp 1) (![1, 0] : R2)) (![0, 1] : R2) ≠
        compatibleMetric (![1, 0] : R2) (![0, 1] : R2) := by
  norm_num [LinearMap.BilinForm.compLeft_apply, Module.End.mul_apply,
    complexOp_apply, obliqueOp_apply, omega_apply, omega2, compatibleMetric_apply]

/-- A closed counterexample satisfies all finite symplectic and positivity hypotheses,
including the equal one-dimensional isotropic eigenleaves, but has neither operator relation. -/
theorem positive_compatible_counterexample :
    omega.IsAlt ∧ omega.Nondegenerate ∧
    (∀ x y : R2, compatibleMetric x y = omega x (complexOp y)) ∧
    (∀ x y : R2, compatibleMetric x y = compatibleMetric y x) ∧
    (∀ x : R2, x ≠ 0 → 0 < compatibleMetric x x) ∧
    complexOp * complexOp = -1 ∧
    obliqueOp 1 * obliqueOp 1 = 1 ∧ obliqueOp 1 ≠ 1 ∧ obliqueOp 1 ≠ -1 ∧
    (∀ x y : R2, omega (complexOp x) (complexOp y) = omega x y) ∧
    (∀ x y : R2, omega (obliqueOp 1 x) (obliqueOp 1 y) = -omega x y) ∧
    Module.finrank ℝ (Module.End.eigenspace (obliqueOp 1) 1) = 1 ∧
    Module.finrank ℝ (Module.End.eigenspace (obliqueOp 1) (-1)) = 1 ∧
    (∀ x y : R2, x ∈ Module.End.eigenspace (obliqueOp 1) 1 →
      y ∈ Module.End.eigenspace (obliqueOp 1) 1 → omega x y = 0) ∧
    (∀ x y : R2, x ∈ Module.End.eigenspace (obliqueOp 1) (-1) →
      y ∈ Module.End.eigenspace (obliqueOp 1) (-1) → omega x y = 0) ∧
    complexOp * obliqueOp 1 ≠ obliqueOp 1 * complexOp ∧
    complexOp * obliqueOp 1 ≠ -(obliqueOp 1 * complexOp) := by
  refine ⟨omega_alternating, omega_nondegenerate, (fun _ _ => rfl),
    compatibleMetric_symmetric, compatibleMetric_positive, complexOp_sq,
    obliqueOp_sq 1, obliqueOp_ne_one 1, obliqueOp_ne_neg_one 1,
    complexOp_symplectic, obliqueOp_antisymplectic 1,
    positive_eigenspace_finrank 1, negative_eigenspace_finrank 1,
    (fun _ _ hx hy => positive_eigenspace_isotropic 1 hx hy),
    (fun _ _ hx hy => negative_eigenspace_isotropic 1 hx hy),
    operator_noncommutation 1, ?_⟩
  intro h
  exact one_ne_zero ((operator_anticommutation_iff 1).mp h)

end InfoGeometry.Geometry.ObliqueSymplecticInvolution
