import InfoGeometry.Holography.BekensteinHawkingDyadicEntropy

open InfoGeometry.Holography.BekensteinHawkingDyadicEntropy
open InfoGeometry.Thermodynamics.FiniteGibbsRelative
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

noncomputable section

#check bekensteinHawkingEntropy
#check dyadicEntropyQuantum
#check twoBranch_massieu_eq_dyadicEntropyQuantum
#check dyadicEntropyBits
#check dyadicEntropyBits_eq_nat_mul_twoBranch_massieu
#check bekensteinHawkingEntropy_eq_dyadicEntropyQuantum
#check bekensteinHawkingEntropy_eq_twoBranch_massieu
#check bekensteinHawkingEntropy_eq_dyadicEntropyBits
#check bekensteinHawkingEntropy_eq_nat_mul_twoBranch_massieu
#check dyadicEntropyQuantum_pos
#check dyadicEntropyBits_nonneg
#check finiteWittenCancel_and_bekensteinHawkingDyadic
#check primeBitState_mobiusParity_wittenCancel_bhDyadic

example : dyadicEntropyQuantum = Real.log 2 := rfl

example : dyadicEntropyBits 3 = 3 * Real.log 2 := rfl

example :
    dyadicEntropyBits 2 = 2 * massieuPotential (ι := Fin 2) (fun _ => (0 : ℝ)) :=
  dyadicEntropyBits_eq_nat_mul_twoBranch_massieu 2

example : 0 < dyadicEntropyQuantum :=
  dyadicEntropyQuantum_pos

example : 0 ≤ dyadicEntropyBits 5 :=
  dyadicEntropyBits_nonneg 5
