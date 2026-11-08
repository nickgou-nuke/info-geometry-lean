import InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimonWittenIndexZetaBridge

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeBitMobiusDirichletBridge

open scoped ArithmeticFunction.Moebius
open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge
open InfoGeometry.Arithmetic.PrimonWittenIndexZetaBridge

theorem primeBit_parity_dirichlet_weight_eq_mobius
    {L : PrimeBitLattice} (ε : PrimeBitState L) (β : ℝ) :
    ((-1 : ℤ) ^ ε.1.card : ℝ) *
        Real.rpow (primeBitInteger L ε : ℝ) (-β) =
      (ArithmeticFunction.moebius (primeBitInteger L ε) : ℝ) *
        Real.rpow (primeBitInteger L ε : ℝ) (-β) := by
  rw [mobius_primeBitInteger_eq_parity ε]
  norm_num

theorem primeBit_parity_boltzmann_weight_eq_mobius
    {L : PrimeBitLattice} (ε : PrimeBitState L) (β : ℝ) :
    ((-1 : ℤ) ^ ε.1.card : ℝ) *
        Real.exp (-β * primeBitEnergy L ε.1) =
      (ArithmeticFunction.moebius (primeBitInteger L ε) : ℝ) *
        Real.rpow (primeBitInteger L ε : ℝ) (-β) := by
  rw [mobius_primeBitInteger_eq_parity ε]
  rw [primeBitEnergy_eq_log_primeBitInteger]
  have hweight := boltzmannWeight_eq_exp β (primeBitInteger L ε)
    (Nat.pos_of_ne_zero (primeBitInteger_ne_zero ε))
  simpa [boltzmannWeight, primonEnergy] using congrArg
    (fun x : ℝ => ((-1 : ℤ) ^ ε.1.card : ℝ) * x) hweight

end InfoGeometry.Arithmetic.PrimeBitMobiusDirichletBridge
