import InfoGeometry.Algebra.ZornMatrixTransportedAdditive
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.ZornMatrixRealModule

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Algebra.ZornMatrixTransportedAdditive
open InfoGeometry.Canonical.SplitOctonionGogberashviliVectorMultiplicationBridge

def neg (X : ZornMatrix ℝ) : ZornMatrix ℝ where
  a := -X.a
  v := Vec3.smul (-1) X.v
  w := Vec3.smul (-1) X.w
  b := -X.b

noncomputable instance : Neg (ZornMatrix ℝ) := ⟨neg⟩

theorem add_assoc (X Y Z : ZornMatrix ℝ) : X + Y + Z = X + (Y + Z) := by
  apply oldToVectorEquiv.injective
  exact add_assoc_readout X Y Z

theorem zero_add (X : ZornMatrix ℝ) : 0 + X = X := by
  apply oldToVectorEquiv.injective
  exact zero_add_readout X

theorem add_zero (X : ZornMatrix ℝ) : X + 0 = X := by
  apply oldToVectorEquiv.injective
  exact add_zero_readout X

theorem add_comm (X Y : ZornMatrix ℝ) : X + Y = Y + X := by
  apply oldToVectorEquiv.injective
  exact add_comm_readout X Y

theorem neg_add_cancel (X : ZornMatrix ℝ) : -X + X = 0 := by
  change neg X + X = 0
  apply ZornMatrix.ext <;>
    simp [neg, ZornMatrix.zero, ZornMatrix.add, Vec3.add, Vec3.smul]

noncomputable instance : AddGroup (ZornMatrix ℝ) :=
  AddGroup.ofLeftAxioms add_assoc zero_add neg_add_cancel

noncomputable instance : AddCommGroup (ZornMatrix ℝ) :=
  AddCommGroup.mk add_comm

theorem smul_zero (r : ℝ) : r • (0 : ZornMatrix ℝ) = 0 := by
  apply ZornMatrix.ext <;>
    simp [ZornMatrix.smul, ZornMatrix.zero, Vec3.smul]

theorem zero_smul (X : ZornMatrix ℝ) : (0 : ℝ) • X = 0 := by
  apply ZornMatrix.ext <;>
    simp [ZornMatrix.smul, ZornMatrix.zero, Vec3.smul]

theorem one_smul (X : ZornMatrix ℝ) : (1 : ℝ) • X = X := by
  change ZornMatrix.smul 1 X = X
  apply ZornMatrix.ext
  · simp [ZornMatrix.smul]
  · funext i
    fin_cases i <;> simp [ZornMatrix.smul, Vec3.smul]
  · funext i
    fin_cases i <;> simp [ZornMatrix.smul, Vec3.smul]
  · simp [ZornMatrix.smul]

theorem smul_add (r : ℝ) (X Y : ZornMatrix ℝ) :
    r • (X + Y) = r • X + r • Y := by
  apply oldToVectorEquiv.injective
  exact smul_add_readout r X Y

theorem add_smul (r s : ℝ) (X : ZornMatrix ℝ) :
    (r + s) • X = r • X + s • X := by
  apply oldToVectorEquiv.injective
  exact add_smul_readout r s X

noncomputable instance : SMul ℝ (ZornMatrix ℝ) := ⟨ZornMatrix.smul⟩

noncomputable instance : Module ℝ (ZornMatrix ℝ) where
  smul := ZornMatrix.smul
  one_smul := one_smul
  mul_smul := by
    intro r s X
    apply ZornMatrix.ext <;>
      simp [ZornMatrix.smul, Vec3.smul, mul_assoc]
  smul_zero := smul_zero
  smul_add := smul_add
  add_smul := add_smul
  zero_smul := zero_smul

end InfoGeometry.Algebra.ZornMatrixRealModule
