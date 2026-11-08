/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevChainKernel
import InfoGeometry.Physics.MajoranaKreinPfaffianCarrier

/-! The literal interior compression of the native chain coefficient matrix
is the existing doubled skew pairing. Endpoint coordinates are excluded. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevInteriorPairing

open Matrix KitaevChainCoefficients KitaevChainKernel
open InfoGeometry.Physics.MajoranaKreinPfaffianCarrier

variable {N : ℕ}

def interiorIndex : Sum (Fin (N - 1)) (Fin (N - 1)) → Fin (2 * N)
  | Sum.inl j => bondLeft j
  | Sum.inr j => bondRight j

theorem interiorIndex_injective : Function.Injective (interiorIndex (N := N)) := by
  intro p q h
  rcases p with j | j <;> rcases q with k | k
  · exact congrArg Sum.inl ((bondLeft_eq_iff j k).mp h)
  · exact False.elim (bondLeft_ne_bondRight_any j k h)
  · exact False.elim (bondLeft_ne_bondRight_any k j h.symm)
  · exact congrArg Sum.inr ((bondRight_eq_iff j k).mp h)

theorem chain_entry_bondLeft (t : ℝ) (j : Fin (N - 1)) (k : Fin (2 * N)) :
    chainCoefficientMatrix N t (bondLeft j) k =
      if bondRight j = k then 2 * t else 0 := by
  have h := chain_action_bondLeft t (Pi.single k 1) j
  simpa [Matrix.mulVec_single, Pi.single_apply, eq_comm] using h

theorem chain_entry_bondRight (t : ℝ) (j : Fin (N - 1)) (k : Fin (2 * N)) :
    chainCoefficientMatrix N t (bondRight j) k =
      -(if bondLeft j = k then 2 * t else 0) := by
  have h := chain_action_bondRight t (Pi.single k 1) j
  simpa [Matrix.mulVec_single, Pi.single_apply, eq_comm] using h

theorem chain_interior_eq_offDiagonalPairing (t : ℝ) :
    (chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex =
      offDiagonalPairing ((2 * t) • (1 : Matrix (Fin (N - 1)) (Fin (N - 1)) ℝ)) := by
  have hcross : ∀ j k : Fin (N - 1), bondRight j ≠ bondLeft k :=
    fun j k => (bondLeft_ne_bondRight_any k j).symm
  ext p q
  rcases p with j | j <;> rcases q with k | k <;>
    simp [Matrix.submatrix, interiorIndex, chain_entry_bondLeft, chain_entry_bondRight,
      offDiagonalPairing, Matrix.one_apply, bondLeft_ne_bondRight_any, hcross, mul_ite]

theorem chain_interior_det_ne_zero (t : ℝ) (ht : t ≠ 0) :
    ((chainCoefficientMatrix N t).submatrix interiorIndex interiorIndex).det ≠ 0 := by
  rw [chain_interior_eq_offDiagonalPairing]
  apply (offDiagonalPairing_det_ne_zero_iff _).mpr
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (mul_ne_zero (by norm_num) ht)

end InfoGeometry.Canonical.KitaevInteriorPairing
