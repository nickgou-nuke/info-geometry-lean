import InfoGeometry.Canonical.DrazinSpectralFittingBridge

namespace InfoGeometry.Canonical.DrazinCommutant

open Drazin DrazinSpectralFittingBridge

variable {Algebra : Type*} [Ring Algebra]
variable {operator inverse : Algebra} {index : ℕ}

theorem inverse_commutes_of_commutes (drazin : IsDrazinInverse operator inverse index)
    (commuting : Algebra) (commutes : operator * commuting = commuting * operator) :
    inverse * commuting = commuting * inverse := by
  let residue := IsDrazinInverse.complementaryProjection operator inverse
  have power_commutes : operator ^ index * commuting = commuting * operator ^ index :=
    (show Commute operator commuting from commutes).pow_left index
  have power_residue : operator ^ index * residue = 0 :=
    IsDrazinInverse.power_mul_complementaryProjection_eq_zero drazin
  have residue_power : residue * operator ^ index = 0 :=
    IsDrazinInverse.complementaryProjection_mul_power_eq_zero drazin
  have inverse_reduction : inverse = operator ^ index * inverse ^ (index + 1) := by
    calc
      inverse = inverse ^ (index + 1) * operator ^ index := drazin_pow_reduction drazin index
      _ = operator ^ index * inverse ^ (index + 1) :=
        ((show Commute operator inverse from drazin.comm).pow_pow index (index + 1)).eq.symm
  have left_zero : inverse * (commuting * residue) = 0 := by
    apply drazin_annihilates_nilpotent drazin (commuting * residue)
    change operator ^ index * (commuting * residue) = 0
    rw [← mul_assoc, power_commutes, mul_assoc, power_residue, mul_zero]
  have right_zero : residue * (commuting * inverse) = 0 := by
    calc
      residue * (commuting * inverse) =
          residue * (commuting * (operator ^ index * inverse ^ (index + 1))) := by
        conv_lhs => arg 2; arg 2; rw [inverse_reduction]
      _ = (residue * (commuting * operator ^ index)) * inverse ^ (index + 1) := by
        noncomm_ring
      _ = (residue * (operator ^ index * commuting)) * inverse ^ (index + 1) := by
        rw [power_commutes]
      _ = (residue * operator ^ index) * commuting * inverse ^ (index + 1) := by
        noncomm_ring
      _ = 0 := by rw [residue_power]; simp
  have left_regular : inverse * commuting = inverse * commuting * (operator * inverse) := by
    change inverse * (commuting * (1 - operator * inverse)) = 0 at left_zero
    rw [mul_sub, mul_one, mul_sub, sub_eq_zero] at left_zero
    simpa only [mul_assoc] using left_zero
  have right_regular : commuting * inverse = (operator * inverse) * (commuting * inverse) := by
    change (1 - operator * inverse) * (commuting * inverse) = 0 at right_zero
    rw [sub_mul, one_mul, sub_eq_zero] at right_zero
    exact right_zero
  calc
    inverse * commuting = inverse * commuting * (operator * inverse) := left_regular
    _ = inverse * (commuting * operator) * inverse := by noncomm_ring
    _ = inverse * (operator * commuting) * inverse := by rw [commutes]
    _ = (inverse * operator) * (commuting * inverse) := by noncomm_ring
    _ = (operator * inverse) * (commuting * inverse) := by rw [drazin.comm]
    _ = commuting * inverse := right_regular.symm

end InfoGeometry.Canonical.DrazinCommutant
