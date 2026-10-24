/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ConcreteKitaevBdGMatrix
import InfoGeometry.CliffordWeyl.DiracSolderOperatorAction

/-! Complete sweet-spot boundary kernel and its actual Dirac ket–bra
projector. The parameter is nonzero only for the kernel classification.
-/
noncomputable section
namespace InfoGeometry.Canonical.ConcreteKitaevBdGMatrix
open Matrix InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

theorem sweetSpot_kernel_coordinates (t : ℝ) (ht : t ≠ 0) (v : Vec4C) :
    kitaevSweetSpot4 t *ᵥ v = 0 ↔ v 2 = -v 0 ∧ v 3 = v 1 := by
  constructor
  · intro h
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have hsum : (t : ℂ) * (v 0 + v 2) = 0 := by
      calc
        _ = -((kitaevSweetSpot4 t *ᵥ v) 1) := by
          simp [kitaevSweetSpot4, mulVec, dotProduct, Fin.sum_univ_four]
          ring
        _ = 0 := by rw [h1]; simp
    have hdiff : (t : ℂ) * (v 3 - v 1) = 0 := by
      calc
        _ = (kitaevSweetSpot4 t *ᵥ v) 0 := by
          simp [kitaevSweetSpot4, mulVec, dotProduct, Fin.sum_univ_four]
          ring
        _ = 0 := h0
    have hs := (mul_eq_zero.mp hsum).resolve_left htC
    have hd := (mul_eq_zero.mp hdiff).resolve_left htC
    exact ⟨eq_neg_of_add_eq_zero_right hs, sub_eq_zero.mp hd⟩
  · rintro ⟨h2, h3⟩
    ext i
    fin_cases i <;>
      simp [kitaevSweetSpot4, mulVec, dotProduct, Fin.sum_univ_four, h2, h3]

theorem boundary_expansion_iff (v : Vec4C) :
    v = v 0 • majoranaZeroModeLeft + v 1 • majoranaZeroModeRight ↔
      v 2 = -v 0 ∧ v 3 = v 1 := by
  constructor
  · intro h
    constructor
    · simpa [majoranaZeroModeLeft, majoranaZeroModeRight] using congrFun h 2
    · simpa [majoranaZeroModeLeft, majoranaZeroModeRight] using congrFun h 3
  · rintro ⟨h2, h3⟩
    ext i
    fin_cases i <;> simp [majoranaZeroModeLeft, majoranaZeroModeRight, h2, h3]

theorem sweetSpot_kernel_iff_boundary_expansion (t : ℝ) (ht : t ≠ 0) (v : Vec4C) :
    kitaevSweetSpot4 t *ᵥ v = 0 ↔
      v = v 0 • majoranaZeroModeLeft + v 1 • majoranaZeroModeRight := by
  rw [sweetSpot_kernel_coordinates t ht, boundary_expansion_iff]

def boundaryDiracProjector : Mat4C :=
  (-1 / 2 : ℂ) • solder particleHole4 majoranaZeroModeLeft majoranaZeroModeLeft +
    (1 / 2 : ℂ) • solder particleHole4 majoranaZeroModeRight majoranaZeroModeRight

theorem boundaryDiracProjector_explicit :
    boundaryDiracProjector =
      !![1/2, 0, -1/2, 0; 0, 1/2, 0, 1/2;
         -1/2, 0, 1/2, 0; 0, 1/2, 0, 1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundaryDiracProjector, solder, diracRow, particleHole4,
      majoranaZeroModeLeft, majoranaZeroModeRight, vecMul, dotProduct, Fin.sum_univ_four,
      Pi.star_def, vecHead, vecTail]

theorem boundaryDiracProjector_idempotent :
    boundaryDiracProjector * boundaryDiracProjector = boundaryDiracProjector := by
  rw [boundaryDiracProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mul_apply, Fin.sum_univ_four]

theorem boundaryDiracProjector_metric_adjoint :
    particleHole4 * boundaryDiracProjector.conjTranspose * particleHole4 =
      boundaryDiracProjector := by
  rw [boundaryDiracProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [particleHole4, mul_apply, conjTranspose_apply, Fin.sum_univ_four,
      vecMul, dotProduct, map_ofNat]

theorem boundaryDiracProjector_fixed_iff (v : Vec4C) :
    boundaryDiracProjector *ᵥ v = v ↔ v 2 = -v 0 ∧ v 3 = v 1 := by
  rw [boundaryDiracProjector_explicit]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [mulVec, dotProduct, Fin.sum_univ_four] at h0 h1
    constructor
    · linear_combination -2 * h0
    · linear_combination 2 * h1
  · rintro ⟨h2, h3⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four, h2, h3] <;> ring

theorem boundaryDiracProjector_fixed_iff_kernel (t : ℝ) (ht : t ≠ 0) (v : Vec4C) :
    boundaryDiracProjector *ᵥ v = v ↔ kitaevSweetSpot4 t *ᵥ v = 0 := by
  rw [boundaryDiracProjector_fixed_iff, sweetSpot_kernel_coordinates t ht]

end InfoGeometry.Canonical.ConcreteKitaevBdGMatrix
