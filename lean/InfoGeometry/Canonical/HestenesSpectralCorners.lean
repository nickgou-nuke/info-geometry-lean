/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.HestenesHermitianAdjoint
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Intrinsic spectral projectors and adjoint transport in real spacetime algebra

The carrier is the full native Mathlib even Clifford algebra `ClPlus14` for
signature `(+---)`. The projectors below are the spectral projectors of
`sigmaEven 0 = gamma 1 * gamma 0`; they are different from the existing circular
projectors, whose defining axis is `sigmaEven 2`.

Clifford reversion exchanges these two projectors. The fixed-observer
Hestenes Hermitian adjoint fixes them. Since both operations reverse products,
reversion preserves each off-diagonal Peirce corner, while the Hermitian
adjoint exchanges the two corners. A nonzero native Clifford witness prevents
the preserved corner from being silently identified with the opposite corner.

Only finite algebraic statements are made here. The Hestenes Hermitian adjoint
is the existing operation `gamma 0 * reverse x * gamma 0`; this file does not
identify it with bare reversion or with either beta-twisted operation. The
existing real algebra equivalence is used only to separate a projector from
zero, with real-entry matrices in that proof.
-/

noncomputable section

namespace HestenesSpectralCorners

open HestenesCl14
open HestenesKreinMatrixBridge
open HestenesHermitianAdjoint

/-- The positive spectral projector of the native bivector `gamma 1 * gamma 0`. -/
def projectorPlus : ClPlus14 :=
  (1 / 2 : ℝ) • ((1 : ClPlus14) + sigmaEven 0)

/-- The negative spectral projector of the same native bivector. -/
def projectorMinus : ClPlus14 :=
  (1 / 2 : ℝ) • ((1 : ClPlus14) - sigmaEven 0)

@[simp] theorem projectorPlus_sq :
    projectorPlus * projectorPlus = projectorPlus := by
  have h : ((1 : ClPlus14) + sigmaEven 0) * (1 + sigmaEven 0) =
      (1 + sigmaEven 0) + (1 + sigmaEven 0) := by
    calc
      (1 + sigmaEven 0) * (1 + sigmaEven 0) =
          1 + sigmaEven 0 + sigmaEven 0 + sigmaEven 0 * sigmaEven 0 := by
            noncomm_ring
      _ = (1 + sigmaEven 0) + (1 + sigmaEven 0) := by
        rw [sigmaEven_zero_sq]
        noncomm_ring
  simp only [projectorPlus, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h, smul_add, ← add_smul]
  norm_num

@[simp] theorem projectorMinus_sq :
    projectorMinus * projectorMinus = projectorMinus := by
  have h : ((1 : ClPlus14) - sigmaEven 0) * (1 - sigmaEven 0) =
      (1 - sigmaEven 0) + (1 - sigmaEven 0) := by
    calc
      (1 - sigmaEven 0) * (1 - sigmaEven 0) =
          1 - sigmaEven 0 - sigmaEven 0 + sigmaEven 0 * sigmaEven 0 := by
            noncomm_ring
      _ = (1 - sigmaEven 0) + (1 - sigmaEven 0) := by
        rw [sigmaEven_zero_sq]
        noncomm_ring
  simp only [projectorMinus, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h, smul_add, ← add_smul]
  norm_num

@[simp] theorem projectorPlus_mul_projectorMinus :
    projectorPlus * projectorMinus = 0 := by
  have h : ((1 : ClPlus14) + sigmaEven 0) * (1 - sigmaEven 0) = 0 := by
    calc
      (1 + sigmaEven 0) * (1 - sigmaEven 0) =
          1 - sigmaEven 0 * sigmaEven 0 := by noncomm_ring
      _ = 0 := by rw [sigmaEven_zero_sq, sub_self]
  simp only [projectorPlus, projectorMinus, smul_mul_assoc, mul_smul_comm,
    smul_smul, h, smul_zero]

@[simp] theorem projectorMinus_mul_projectorPlus :
    projectorMinus * projectorPlus = 0 := by
  have h : ((1 : ClPlus14) - sigmaEven 0) * (1 + sigmaEven 0) = 0 := by
    calc
      (1 - sigmaEven 0) * (1 + sigmaEven 0) =
          1 - sigmaEven 0 * sigmaEven 0 := by noncomm_ring
      _ = 0 := by rw [sigmaEven_zero_sq, sub_self]
  simp only [projectorPlus, projectorMinus, smul_mul_assoc, mul_smul_comm,
    smul_smul, h, smul_zero]

@[simp] theorem projectorPlus_add_projectorMinus :
    projectorPlus + projectorMinus = 1 := by
  rw [projectorPlus, projectorMinus, ← smul_add]
  have h : ((1 : ClPlus14) + sigmaEven 0) + (1 - sigmaEven 0) = 1 + 1 := by
    noncomm_ring
  rw [h, smul_add, ← add_smul]
  norm_num

private theorem reverseEven_one : reverseEven (1 : ClPlus14) = 1 := by
  apply Subtype.ext
  simp [reverseEven]

private theorem reverseEven_sub (x y : ClPlus14) :
    reverseEven (x - y) = reverseEven x - reverseEven y := by
  apply Subtype.ext
  simp [reverseEven, map_sub]

@[simp] theorem reverseEven_sigma_zero :
    reverseEven (sigmaEven 0) = -sigmaEven 0 := by
  apply Subtype.ext
  exact HestenesCliffordKrein.reverse_beta

@[simp] theorem reverseEven_projectorPlus :
    reverseEven projectorPlus = projectorMinus := by
  rw [projectorPlus, reverseEven_smul, reverseEven_add,
    reverseEven_one, reverseEven_sigma_zero]
  simp only [projectorMinus, sub_eq_add_neg]

@[simp] theorem reverseEven_projectorMinus :
    reverseEven projectorMinus = projectorPlus := by
  rw [projectorMinus, reverseEven_smul, reverseEven_sub,
    reverseEven_one, reverseEven_sigma_zero]
  simp only [projectorPlus, sub_neg_eq_add]

private theorem hestenesAdjoint_one : hestenesAdjoint (1 : ClPlus14) = 1 := by
  apply Subtype.ext
  simp [hestenesAdjoint, reverseEven]

private theorem hestenesAdjoint_sub (x y : ClPlus14) :
    hestenesAdjoint (x - y) = hestenesAdjoint x - hestenesAdjoint y := by
  apply Subtype.ext
  simp [hestenesAdjoint, reverseEven, map_sub, mul_sub, sub_mul]

@[simp] theorem hestenesAdjoint_sigma_zero :
    hestenesAdjoint (sigmaEven 0) = sigmaEven 0 := by
  apply Subtype.ext
  change gamma 0 * CliffordAlgebra.reverse (gamma 1 * gamma 0) * gamma 0 =
    gamma 1 * gamma 0
  have hr0 : CliffordAlgebra.reverse (gamma 0) = gamma 0 := by simp [gamma]
  have hr1 : CliffordAlgebra.reverse (gamma 1) = gamma 1 := by simp [gamma]
  rw [CliffordAlgebra.reverse.map_mul, hr0, hr1]
  simp only [← mul_assoc, gamma_zero_sq, one_mul]

@[simp] theorem hestenesAdjoint_projectorPlus :
    hestenesAdjoint projectorPlus = projectorPlus := by
  rw [projectorPlus, hestenesAdjoint_smul, hestenesAdjoint_add,
    hestenesAdjoint_one, hestenesAdjoint_sigma_zero]

@[simp] theorem hestenesAdjoint_projectorMinus :
    hestenesAdjoint projectorMinus = projectorMinus := by
  rw [projectorMinus, hestenesAdjoint_smul, hestenesAdjoint_sub,
    hestenesAdjoint_one, hestenesAdjoint_sigma_zero]

/-- Reversing the order and exchanging the endpoints preserves the `(+,-)` corner. -/
theorem reverseEven_plus_minus_corner (x : ClPlus14) :
    reverseEven (projectorPlus * x * projectorMinus) =
      projectorPlus * reverseEven x * projectorMinus := by
  simp only [reverseEven_mul, reverseEven_projectorPlus,
    reverseEven_projectorMinus, mul_assoc]

/-- The other off-diagonal corner is likewise preserved by reversion. -/
theorem reverseEven_minus_plus_corner (x : ClPlus14) :
    reverseEven (projectorMinus * x * projectorPlus) =
      projectorMinus * reverseEven x * projectorPlus := by
  simp only [reverseEven_mul, reverseEven_projectorPlus,
    reverseEven_projectorMinus, mul_assoc]

/-- The observer adjoint fixes the endpoints, so reversing the order exchanges corners. -/
theorem hestenesAdjoint_plus_minus_corner (x : ClPlus14) :
    hestenesAdjoint (projectorPlus * x * projectorMinus) =
      projectorMinus * hestenesAdjoint x * projectorPlus := by
  simp only [hestenesAdjoint_mul, hestenesAdjoint_projectorPlus,
    hestenesAdjoint_projectorMinus, mul_assoc]

theorem hestenesAdjoint_minus_plus_corner (x : ClPlus14) :
    hestenesAdjoint (projectorMinus * x * projectorPlus) =
      projectorPlus * hestenesAdjoint x * projectorMinus := by
  simp only [hestenesAdjoint_mul, hestenesAdjoint_projectorPlus,
    hestenesAdjoint_projectorMinus, mul_assoc]

/-- The spectral projector is nonzero in the genuine eight-dimensional real algebra. -/
theorem projectorPlus_ne_zero : projectorPlus ≠ 0 := by
  intro h
  have hm := congrArg HestenesPauliSheetBridge.clPlusToPauli h
  have h00 := congrArg
    (fun A : HestenesPauliSheetBridge.Sheet => A 0 0) hm
  norm_num [projectorPlus, map_smul, map_add, map_one, map_zero,
    HestenesEvenPauliEquiv.clPlusToPauli_sigma0,
    HestenesEvenPauliEquiv.pauli1] at h00

private theorem transverse_sq : sigmaEven 2 * sigmaEven 2 = 1 := by
  apply Subtype.ext
  change (gamma 3 * gamma 0) * (gamma 3 * gamma 0) = (1 : Cl14)
  have h03 : gamma 0 * gamma 3 = -(gamma 3 * gamma 0) :=
    eq_neg_of_add_eq_zero_left (gamma_anticomm (by decide))
  calc
    (gamma 3 * gamma 0) * (gamma 3 * gamma 0) =
        gamma 3 * (gamma 0 * gamma 3) * gamma 0 := by simp only [mul_assoc]
    _ = 1 := by
      rw [h03]
      simp only [mul_neg, neg_mul, ← mul_assoc, gamma_three_sq,
        neg_one_mul, neg_neg, gamma_zero_sq]

private theorem transverse_mul_beta :
    sigmaEven 2 * sigmaEven 0 = -(sigmaEven 0 * sigmaEven 2) := by
  apply Subtype.ext
  change (gamma 3 * gamma 0) * (gamma 1 * gamma 0) =
    -((gamma 1 * gamma 0) * (gamma 3 * gamma 0))
  have h01 : gamma 0 * gamma 1 = -(gamma 1 * gamma 0) :=
    eq_neg_of_add_eq_zero_left (gamma_anticomm (by decide))
  have h03 : gamma 0 * gamma 3 = -(gamma 3 * gamma 0) :=
    eq_neg_of_add_eq_zero_left (gamma_anticomm (by decide))
  have h31 : gamma 3 * gamma 1 = -(gamma 1 * gamma 3) :=
    eq_neg_of_add_eq_zero_left (gamma_anticomm (by decide))
  have hleft : (gamma 3 * gamma 0) * (gamma 1 * gamma 0) =
      -(gamma 3 * gamma 1) := by
    calc
      (gamma 3 * gamma 0) * (gamma 1 * gamma 0) =
          gamma 3 * (gamma 0 * gamma 1) * gamma 0 := by simp only [mul_assoc]
      _ = -(gamma 3 * gamma 1) := by
        rw [h01]
        simp only [mul_neg, neg_mul, mul_assoc, gamma_zero_sq, mul_one]
  have hright : (gamma 1 * gamma 0) * (gamma 3 * gamma 0) =
      -(gamma 1 * gamma 3) := by
    calc
      (gamma 1 * gamma 0) * (gamma 3 * gamma 0) =
          gamma 1 * (gamma 0 * gamma 3) * gamma 0 := by simp only [mul_assoc]
      _ = -(gamma 1 * gamma 3) := by
        rw [h03]
        simp only [mul_neg, neg_mul, mul_assoc, gamma_zero_sq, mul_one]
  rw [hleft, hright, h31]

private theorem transverse_mul_projectorMinus :
    sigmaEven 2 * projectorMinus = projectorPlus * sigmaEven 2 := by
  simp only [projectorMinus, projectorPlus, mul_smul_comm, smul_mul_assoc,
    mul_sub, add_mul, mul_one, one_mul, transverse_mul_beta, sub_neg_eq_add]

/-- An off-diagonal operator formed from a transverse native Clifford bivector. -/
def offDiagonalWitness : ClPlus14 :=
  projectorPlus * sigmaEven 2 * projectorMinus

theorem offDiagonalWitness_eq_projectorPlus_mul :
    offDiagonalWitness = projectorPlus * sigmaEven 2 := by
  rw [offDiagonalWitness, mul_assoc, transverse_mul_projectorMinus,
    ← mul_assoc, projectorPlus_sq]

theorem offDiagonalWitness_mul_transverse :
    offDiagonalWitness * sigmaEven 2 = projectorPlus := by
  rw [offDiagonalWitness_eq_projectorPlus_mul, mul_assoc, transverse_sq, mul_one]

theorem offDiagonalWitness_ne_zero : offDiagonalWitness ≠ 0 := by
  intro h
  apply projectorPlus_ne_zero
  have hh := congrArg (fun x : ClPlus14 => x * sigmaEven 2) h
  simpa only [offDiagonalWitness_mul_transverse, zero_mul] using hh

theorem offDiagonalWitness_sq_zero : offDiagonalWitness * offDiagonalWitness = 0 := by
  calc
    offDiagonalWitness * offDiagonalWitness =
        projectorPlus * sigmaEven 2 * (projectorMinus * projectorPlus) *
          sigmaEven 2 * projectorMinus := by
            simp only [offDiagonalWitness, mul_assoc]
    _ = 0 := by rw [projectorMinus_mul_projectorPlus]; simp

theorem offDiagonalWitness_opposite_corner_zero :
    projectorMinus * offDiagonalWitness * projectorPlus = 0 := by
  calc
    projectorMinus * offDiagonalWitness * projectorPlus =
        (projectorMinus * projectorPlus) * sigmaEven 2 *
          (projectorMinus * projectorPlus) := by
            simp only [offDiagonalWitness, mul_assoc]
    _ = 0 := by rw [projectorMinus_mul_projectorPlus]; simp

private theorem reverseEven_transverse :
    reverseEven (sigmaEven 2) = -sigmaEven 2 := by
  apply Subtype.ext
  change CliffordAlgebra.reverse (gamma 3 * gamma 0) = -(gamma 3 * gamma 0)
  have hr0 : CliffordAlgebra.reverse (gamma 0) = gamma 0 := by simp [gamma]
  have hr3 : CliffordAlgebra.reverse (gamma 3) = gamma 3 := by simp [gamma]
  rw [CliffordAlgebra.reverse.map_mul, hr0, hr3]
  exact eq_neg_of_add_eq_zero_left (gamma_anticomm (by decide))

@[simp] theorem reverseEven_offDiagonalWitness :
    reverseEven offDiagonalWitness = -offDiagonalWitness := by
  rw [offDiagonalWitness, reverseEven_plus_minus_corner, reverseEven_transverse]
  simp only [mul_neg, neg_mul]

/-- A concrete obstruction to the incorrect claim that reversion exchanges these corners. -/
theorem reverseEven_offDiagonalWitness_not_in_opposite_corner :
    projectorMinus * reverseEven offDiagonalWitness * projectorPlus ≠
      reverseEven offDiagonalWitness := by
  rw [reverseEven_offDiagonalWitness]
  simp only [mul_neg, neg_mul, offDiagonalWitness_opposite_corner_zero, neg_zero]
  intro h
  exact offDiagonalWitness_ne_zero (neg_eq_zero.mp h.symm)

end HestenesSpectralCorners

end
