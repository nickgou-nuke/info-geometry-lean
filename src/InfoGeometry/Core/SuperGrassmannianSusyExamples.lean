/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.SuperGrassmannianSusy

/-!
# Concrete finite-color smoke examples

These examples instantiate the finite-color contracts at `Fin 2` and `Fin 4`.
They use the zero square-zero/Moore--Penrose system, which is the smallest
fully explicit model and keeps the examples independent of a matrix carrier.
The conditional `sl(k|1)` interpretation remains intentionally absent.
-/

namespace InfoGeometry.Core.SuperGrassmannianSusy

open InfoGeometry.Singular.MoorePenrose

variable {R : Type*} [Ring R] [StarRing R]

theorem zeroOrthogonalExtendedSusy {ι : Type*} [Fintype ι] :
    IsOrthogonalExtendedSusy (fun _ : ι => (0 : R)) (fun _ : ι => (0 : R)) where
  mp := fun _ => ⟨by simp, by simp, by simp, by simp⟩
  d_mul_d := by simp
  b_mul_b := by simp
  b_mul_d_ne := by simp
  d_mul_b_ne := by simp

theorem fin2ZeroSupercolor :
    IsOrthogonalExtendedSusy (fun _ : Fin 2 => (0 : R)) (fun _ : Fin 2 => (0 : R)) :=
  zeroOrthogonalExtendedSusy

theorem fin4ZeroSupercolor :
    IsOrthogonalExtendedSusy (fun _ : Fin 4 => (0 : R)) (fun _ : Fin 4 => (0 : R)) :=
  zeroOrthogonalExtendedSusy

omit [StarRing R] in
theorem fin2_zero_total_charges :
    totalMajoranaPlus (fun _ : Fin 2 => (0 : R)) (fun _ : Fin 2 => (0 : R)) = 0 ∧
    totalMajoranaMinus (fun _ : Fin 2 => (0 : R)) (fun _ : Fin 2 => (0 : R)) = 0 ∧
    totalCentralCharge (fun _ : Fin 2 => (0 : R)) (fun _ : Fin 2 => (0 : R)) = 0 := by
  simp [totalMajoranaPlus, totalMajoranaMinus, totalCentralCharge,
    majoranaPlus, majoranaMinus, sectorCentralCharge, jordanProd]

omit [StarRing R] in
theorem fin4_zero_total_charges :
    totalMajoranaPlus (fun _ : Fin 4 => (0 : R)) (fun _ : Fin 4 => (0 : R)) = 0 ∧
    totalMajoranaMinus (fun _ : Fin 4 => (0 : R)) (fun _ : Fin 4 => (0 : R)) = 0 ∧
    totalCentralCharge (fun _ : Fin 4 => (0 : R)) (fun _ : Fin 4 => (0 : R)) = 0 := by
  simp [totalMajoranaPlus, totalMajoranaMinus, totalCentralCharge,
    majoranaPlus, majoranaMinus, sectorCentralCharge, jordanProd]

theorem fin2_zero_extended_susy_certificate :
    totalMajoranaPlus (fun _ : Fin 2 => (0 : R)) (fun _ : Fin 2 => (0 : R)) *
        totalMajoranaPlus (fun _ : Fin 2 => (0 : R)) (fun _ : Fin 2 => (0 : R)) =
      totalCentralCharge (fun _ : Fin 2 => (0 : R)) (fun _ : Fin 2 => (0 : R)) :=
  n4_extended_susy fin2ZeroSupercolor

theorem fin4_zero_extended_susy_certificate :
    totalMajoranaPlus (fun _ : Fin 4 => (0 : R)) (fun _ : Fin 4 => (0 : R)) *
        totalMajoranaPlus (fun _ : Fin 4 => (0 : R)) (fun _ : Fin 4 => (0 : R)) =
      totalCentralCharge (fun _ : Fin 4 => (0 : R)) (fun _ : Fin 4 => (0 : R)) :=
  n8_extended_susy fin4ZeroSupercolor

end InfoGeometry.Core.SuperGrassmannianSusy
