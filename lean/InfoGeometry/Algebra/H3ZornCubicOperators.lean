import InfoGeometry.Algebra.H3ZornCubicNormStructure

/-!
# Structural operators for the split Albert cubic norm

This module proves bilinearity and symmetry properties of the trace pairing,
adjoint polarization, and outer slots of the cubic `T` operator. The proofs
use bundled Zorn composition laws and do not enumerate split-octonion
coordinates.
-/

namespace InfoGeometry.Algebra.H3Zorn

variable {R : Type*} [CommRing R]

theorem traceBilin_symm (X Y : H3Zorn R) :
    traceBilin X Y = traceBilin Y X := by
  simp only [traceBilin]
  rw [ZornVectorMatrix.trace_mul_conj_comm X.a Y.a,
    ZornVectorMatrix.trace_mul_conj_comm X.b Y.b,
    ZornVectorMatrix.trace_mul_conj_comm X.c Y.c]
  ring

theorem traceBilin_add_left (X₁ X₂ Y : H3Zorn R) :
    traceBilin (X₁ + X₂) Y = traceBilin X₁ Y + traceBilin X₂ Y := by
  simp only [traceBilin, add_readback, ZornVectorMatrix.add_mul,
    ZornVectorMatrix.trace_add]
  ring

theorem traceBilin_add_right (X Y₁ Y₂ : H3Zorn R) :
    traceBilin X (Y₁ + Y₂) = traceBilin X Y₁ + traceBilin X Y₂ := by
  rw [traceBilin_symm, traceBilin_add_left]
  rw [traceBilin_symm X Y₁, traceBilin_symm X Y₂]

theorem traceBilin_smul_left (r : R) (X Y : H3Zorn R) :
    traceBilin (r • X) Y = r * traceBilin X Y := by
  simp only [traceBilin, smul_readback, ZornVectorMatrix.smul_mul,
    ZornVectorMatrix.trace_smul]
  ring

theorem traceBilin_smul_right (r : R) (X Y : H3Zorn R) :
    traceBilin X (r • Y) = r * traceBilin X Y := by
  rw [traceBilin_symm, traceBilin_smul_left, traceBilin_symm X Y]

theorem traceBilin_sub_left (X₁ X₂ Y : H3Zorn R) :
    traceBilin (X₁ - X₂) Y = traceBilin X₁ Y - traceBilin X₂ Y := by
  rw [sub_eq_add_neg, traceBilin_add_left]
  rw [show -X₂ = (-1 : R) • X₂ by module, traceBilin_smul_left]
  ring

theorem traceBilin_sub_right (X Y₁ Y₂ : H3Zorn R) :
    traceBilin X (Y₁ - Y₂) = traceBilin X Y₁ - traceBilin X Y₂ := by
  rw [sub_eq_add_neg, traceBilin_add_right]
  rw [show -Y₂ = (-1 : R) • Y₂ by module, traceBilin_smul_right]
  ring

theorem crossProduct_symm (X Y : H3Zorn R) :
    crossProduct X Y = crossProduct Y X := by
  simp only [crossProduct, add_comm X Y]
  abel

/-- Polarization reconstructs the adjoint of a sum. -/
theorem adjointQuad_add (X Y : H3Zorn R) :
    adjointQuad (X + Y) =
      adjointQuad X + crossProduct X Y + adjointQuad Y := by
  simp only [crossProduct]
  abel

/-- The full polarization of the cubic norm is symmetric: the trace pairing
may be moved cyclically across the adjoint cross product.  This is derived
from the cubic norm polarization law, without expanding Zorn coordinates. -/
theorem traceBilin_crossProduct_assoc (X Y Z : H3Zorn R) :
    traceBilin (crossProduct X Y) Z =
      traceBilin X (crossProduct Y Z) := by
  have h₁ := normCubic_add (X + Y) Z
  have h₂ := normCubic_add X (Y + Z)
  rw [add_assoc] at h₁
  rw [adjointQuad_add] at h₁ h₂
  simp only [traceBilin_add_left, traceBilin_add_right] at h₁ h₂
  rw [h₂] at h₁
  rw [normCubic_add X Y, normCubic_add Y Z] at h₁
  rw [traceBilin_symm X (crossProduct Y Z)]
  linear_combination -h₁

theorem crossProduct_add_left (X₁ X₂ Y : H3Zorn R) :
    crossProduct (X₁ + X₂) Y = crossProduct X₁ Y + crossProduct X₂ Y := by
  apply ext_h3
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback]
    simp only [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      ZornVectorMatrix.add_mul, ZornVectorMatrix.trace_add]
    ring
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback]
    simp only [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      ZornVectorMatrix.add_mul, ZornVectorMatrix.trace_add]
    ring
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback]
    simp only [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      ZornVectorMatrix.add_mul, ZornVectorMatrix.trace_add]
    ring
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul,
      ZornVectorMatrix.mul_add, ZornVectorMatrix.smul_add,
      ZornVectorMatrix.add_smul]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def]
    module
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul,
      ZornVectorMatrix.mul_add, ZornVectorMatrix.smul_add,
      ZornVectorMatrix.add_smul]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def]
    module
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul,
      ZornVectorMatrix.mul_add, ZornVectorMatrix.smul_add,
      ZornVectorMatrix.add_smul]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def]
    module

theorem crossProduct_add_right (X Y₁ Y₂ : H3Zorn R) :
    crossProduct X (Y₁ + Y₂) = crossProduct X Y₁ + crossProduct X Y₂ := by
  rw [crossProduct_symm, crossProduct_add_left]
  rw [crossProduct_symm X Y₁, crossProduct_symm X Y₂]

theorem crossProduct_smul_left (r : R) (X Y : H3Zorn R) :
    crossProduct (r • X) Y = r • crossProduct X Y := by
  -- Additivity above is not enough over an arbitrary ring, so expand structurally.
  apply ext_h3
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback,
      smul_readback, ZornVectorMatrix.norm_smul]
    simp only [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      ZornVectorMatrix.norm_smul, ZornVectorMatrix.smul_mul,
      ZornVectorMatrix.trace_smul]
    ring
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback,
      smul_readback, ZornVectorMatrix.norm_smul]
    simp only [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      ZornVectorMatrix.norm_smul, ZornVectorMatrix.smul_mul,
      ZornVectorMatrix.trace_smul]
    ring
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback,
      smul_readback, ZornVectorMatrix.norm_smul]
    simp only [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      ZornVectorMatrix.norm_smul, ZornVectorMatrix.smul_mul,
      ZornVectorMatrix.trace_smul]
    ring
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback,
      smul_readback, ZornVectorMatrix.conj_add, ZornVectorMatrix.conj_smul,
      ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add,
      ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul,
      ZornVectorMatrix.smul_add, ZornVectorMatrix.add_smul]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def]
    module
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback,
      smul_readback, ZornVectorMatrix.conj_add, ZornVectorMatrix.conj_smul,
      ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add,
      ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul,
      ZornVectorMatrix.smul_add, ZornVectorMatrix.add_smul]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def]
    module
  · simp only [crossProduct, adjointQuad, add_readback, sub_readback,
      smul_readback, ZornVectorMatrix.conj_add, ZornVectorMatrix.conj_smul,
      ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add,
      ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul,
      ZornVectorMatrix.smul_add, ZornVectorMatrix.add_smul]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def]
    module

theorem crossProduct_smul_right (r : R) (X Y : H3Zorn R) :
    crossProduct X (r • Y) = r • crossProduct X Y := by
  rw [crossProduct_symm, crossProduct_smul_left, crossProduct_symm X Y]

/-- The linear trace of the adjoint cross product is the polarization of the
quadratic trace coefficient. -/
@[simp] theorem linearTrace_crossProduct (X Y : H3Zorn R) :
    linearTrace (crossProduct X Y) =
      linearTrace X * linearTrace Y - traceBilin X Y := by
  have h := traceBilin_crossProduct_assoc X Y (1 : H3Zorn R)
  rw [traceBilin_one, crossProduct_one] at h
  rw [show linearTrace Y • (1 : H3Zorn R) - Y =
      linearTrace Y • 1 + (-1 : R) • Y by module] at h
  rw [traceBilin_add_right, traceBilin_smul_right,
    traceBilin_smul_right, traceBilin_one] at h
  linear_combination h

/-- The trace of polarization against the cubic basepoint is twice the linear
trace. -/
@[simp] theorem linearTrace_crossProduct_one (X : H3Zorn R) :
    linearTrace (crossProduct X 1) = (2 : R) * linearTrace X := by
  rw [crossProduct_one, sub_readback, smul_readback, one_readback]
  simp [linearTrace]
  ring

theorem T_outer_formula (X Y Z : H3Zorn R) :
    T X Y Z = traceBilin X Y • Z + traceBilin Z Y • X -
      crossProduct (crossProduct X Z) Y := by
  have hadj : adjointQuad (X + Z) =
      crossProduct X Z + adjointQuad X + adjointQuad Z := by
    simp only [crossProduct]
    abel
  simp only [T, U, traceBilin_add_left, hadj,
    crossProduct_add_left]
  module

/-- Swapping the cubic basepoint between the first two slots leaves the
triple product unchanged. -/
theorem T_one_swap (X Z : H3Zorn R) : T 1 X Z = T X 1 Z := by
  rw [T_outer_formula, T_outer_formula]
  rw [traceBilin_symm (1 : H3Zorn R) X, traceBilin_one,
    traceBilin_symm Z X, traceBilin_one,
    crossProduct_symm (1 : H3Zorn R) Z, crossProduct_one]
  rw [show linearTrace Z • (1 : H3Zorn R) - Z =
      linearTrace Z • 1 + (-1 : R) • Z by module]
  rw [crossProduct_add_left, crossProduct_smul_left,
    crossProduct_smul_left, crossProduct_symm (1 : H3Zorn R) X,
    crossProduct_one, crossProduct_one, linearTrace_crossProduct]
  rw [crossProduct_symm Z X]
  module

/-- Evaluating the outer slots at the cubic basepoint recovers twice the
original element. -/
@[simp] theorem T_one_one (X : H3Zorn R) :
    T X 1 1 = (2 : R) • X := by
  have h11 : traceBilin (1 : H3Zorn R) 1 = (3 : R) := by
    rw [traceBilin_one, one_readback]
    simp [linearTrace]
    ring
  rw [T_outer_formula, traceBilin_one, crossProduct_one,
    linearTrace_crossProduct_one, crossProduct_one, h11]
  module

theorem T_symm_outer (X Y Z : H3Zorn R) : T X Y Z = T Z Y X := by
  rw [T_outer_formula, T_outer_formula, crossProduct_symm X Z]
  abel

theorem T_add_left (X₁ X₂ Y Z : H3Zorn R) :
    T (X₁ + X₂) Y Z = T X₁ Y Z + T X₂ Y Z := by
  simp only [T_outer_formula, traceBilin_add_left, add_smul,
    smul_add, crossProduct_add_left]
  abel

theorem T_add_right (X Y Z₁ Z₂ : H3Zorn R) :
    T X Y (Z₁ + Z₂) = T X Y Z₁ + T X Y Z₂ := by
  rw [T_symm_outer, T_add_left]
  rw [T_symm_outer Z₁ Y X, T_symm_outer Z₂ Y X]

theorem T_smul_left (r : R) (X Y Z : H3Zorn R) :
    T (r • X) Y Z = r • T X Y Z := by
  simp only [T_outer_formula, traceBilin_smul_left,
    crossProduct_smul_left]
  module

theorem T_smul_right (r : R) (X Y Z : H3Zorn R) :
    T X Y (r • Z) = r • T X Y Z := by
  rw [T_symm_outer, T_smul_left]
  rw [T_symm_outer Z Y X]

/-- Scalar-line expansion of the cubic norm.  Its coefficient linear in `r`
is the directional derivative `traceBilin (X#) Y`. -/
theorem normCubic_line (r : R) (X Y : H3Zorn R) :
    normCubic (X + r • Y) = normCubic X +
      r * traceBilin (adjointQuad X) Y +
      r ^ 2 * traceBilin (adjointQuad Y) X +
      r ^ 3 * normCubic Y := by
  rw [normCubic_add, normCubic_smul,
    traceBilin_smul_right, adjointQuad_smul, traceBilin_smul_left]
  ring

end InfoGeometry.Algebra.H3Zorn
