/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GeneralSupercarrierDeformation
import InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule

namespace InfoGeometry.SuperGrassmannian.GeneralScalarClosure

open Matrix
open InfoGeometry.SuperGrassmannian.GeneralSupercarrierDeformation
open InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule

variable {R : Type*} [CommRing R]

/-- Representation of the scalar `1|1` carrier by one-point block matrices. -/
def scalarRepresentation (M : SuperMatrix R) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R :=
  Matrix.fromBlocks
    (fun _ _ => M.A) (fun _ _ => M.B)
    (fun _ _ => M.C) (fun _ _ => M.D)

/-- The scalar carrier representation preserves its multiplication. -/
theorem scalarRepresentation_mul (M N : SuperMatrix R) :
    scalarRepresentation (M * N) =
      scalarRepresentation M * scalarRepresentation N := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [scalarRepresentation, Matrix.fromBlocks, SuperMatrix.mul_A,
      SuperMatrix.mul_B, SuperMatrix.mul_C, SuperMatrix.mul_D,
      Matrix.mul_apply]

/-- The general block supertrace specializes to the scalar supertrace. -/
theorem general_superTrace_scalarRepresentation (M : SuperMatrix R) :
    GeneralSupercarrierDeformation.superTrace (scalarRepresentation M) =
      SuperMatrix.supertrace M := by
  let A : Matrix (Fin 1) (Fin 1) R := fun _ _ => M.A
  let D : Matrix (Fin 1) (Fin 1) R := fun _ _ => M.D
  change Matrix.trace A - Matrix.trace D = M.A - M.D
  rw [Matrix.trace_fin_one, Matrix.trace_fin_one]

/-- The scalar odd-square identity is inherited from the general chiral-square
supertrace theorem through the multiplication-preserving representation. -/
theorem scalar_odd_square_from_general
    (B C : R) :
    SuperMatrix.supertrace
      ((⟨0, B, C, 0⟩ : SuperMatrix R) * ⟨0, B, C, 0⟩) = 0 := by
  rw [← general_superTrace_scalarRepresentation]
  rw [scalarRepresentation_mul]
  apply GeneralSupercarrierDeformation.superTrace_chiral_square

end InfoGeometry.SuperGrassmannian.GeneralScalarClosure

#print axioms InfoGeometry.SuperGrassmannian.GeneralScalarClosure.scalarRepresentation_mul
#print axioms InfoGeometry.SuperGrassmannian.GeneralScalarClosure.general_superTrace_scalarRepresentation
#print axioms InfoGeometry.SuperGrassmannian.GeneralScalarClosure.scalar_odd_square_from_general
