import InfoGeometry.Canonical.DrazinSpectralFittingBridge
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

namespace InfoGeometry.Canonical.DrazinPairingAdjunction

open Drazin DrazinSpectralFittingBridge

variable {Scalar Space : Type*} [CommRing Scalar] [AddCommGroup Space] [Module Scalar Space]
variable (pairing : LinearMap.BilinForm Scalar Space)
variable {operator inverse : Module.End Scalar Space} {index : ℕ}

theorem power_adjoint
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator operator) (power : ℕ) :
    LinearMap.IsAdjointPair pairing pairing (operator ^ power : Module.End Scalar Space)
      (operator ^ power : Module.End Scalar Space) := by
  induction power with
  | zero => simpa only [pow_zero] using (LinearMap.isAdjointPair_one (B := pairing))
  | succ power previous =>
    have relation := previous.mul adjunction
    simpa only [← pow_succ, ← pow_succ'] using relation

theorem inverse_pairing_nilpotent_eq_zero
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator operator)
    (drazin : IsDrazinInverse operator inverse index)
    (left right : Space) (nilpotent : (operator ^ index) right = 0) :
    pairing (inverse left) right = 0 := by
  have reduction := LinearMap.congr_fun (drazin_pow_reduction_rev drazin index) left
  rw [reduction]
  change pairing ((operator ^ index) ((inverse ^ (index + 1)) left)) right = 0
  rw [power_adjoint pairing adjunction index, nilpotent, map_zero]

theorem nilpotent_pairing_inverse_eq_zero
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator operator)
    (drazin : IsDrazinInverse operator inverse index)
    (left right : Space) (nilpotent : (operator ^ index) left = 0) :
    pairing left (inverse right) = 0 := by
  have reduction := LinearMap.congr_fun (drazin_pow_reduction_rev drazin index) right
  rw [reduction]
  change pairing left ((operator ^ index) ((inverse ^ (index + 1)) right)) = 0
  rw [← power_adjoint pairing adjunction index, nilpotent, pairing.map_zero₂]

theorem inverse_adjoint
    (adjunction : LinearMap.IsAdjointPair pairing pairing operator operator)
    (drazin : IsDrazinInverse operator inverse index) :
    LinearMap.IsAdjointPair pairing pairing inverse inverse := by
  let residue := IsDrazinInverse.complementaryProjection operator inverse
  have power_residue (state : Space) : (operator ^ index) (residue state) = 0 :=
    LinearMap.congr_fun (IsDrazinInverse.power_mul_complementaryProjection_eq_zero drazin) state
  intro left right
  have right_zero := inverse_pairing_nilpotent_eq_zero pairing adjunction drazin
    left (residue right) (power_residue right)
  have left_zero := nilpotent_pairing_inverse_eq_zero pairing adjunction drazin
    (residue left) right (power_residue left)
  change pairing (inverse left) (right - operator (inverse right)) = 0 at right_zero
  change pairing (left - operator (inverse left)) (inverse right) = 0 at left_zero
  rw [map_sub, sub_eq_zero] at right_zero
  rw [pairing.map_sub₂, sub_eq_zero] at left_zero
  exact right_zero.trans ((adjunction (inverse left) (inverse right)).symm.trans left_zero.symm)

end InfoGeometry.Canonical.DrazinPairingAdjunction
