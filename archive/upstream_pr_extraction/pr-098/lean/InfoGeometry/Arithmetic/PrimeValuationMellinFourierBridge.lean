import InfoGeometry.Arithmetic.PrimeBitMobiusDirichletBridge

/-!
# Finite prime-energy and Mellin characters

The finite prime-bit lattice is the squarefree sector of the valuation
picture.  Its additive logarithmic energy produces the multiplicative
Mellin/Dirichlet weight.  This owner records that exact bridge only; no
identification with an exceptional root lattice is asserted.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeValuationMellinFourierBridge

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.PrimeBitLattice
open InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge
open InfoGeometry.Arithmetic.PrimonWittenIndexZetaBridge

def primeBitMellinCharacter {L : PrimeBitLattice}
    (β : ℝ) (ε : PrimeBitState L) : ℝ :=
  Real.exp (-β * primeBitEnergy L ε.1)

theorem primeBitMellinCharacter_eq_integer_rpow
    {L : PrimeBitLattice} (β : ℝ) (ε : PrimeBitState L) :
    primeBitMellinCharacter β ε =
      Real.rpow (primeBitInteger L ε : ℝ) (-β) := by
  unfold primeBitMellinCharacter
  rw [primeBitEnergy_eq_log_primeBitInteger]
  have h := boltzmannWeight_eq_exp β (primeBitInteger L ε)
    (Nat.pos_of_ne_zero (primeBitInteger_ne_zero ε))
  simpa [boltzmannWeight, primonEnergy] using h

theorem primeBitMobiusMellinTerm_eq_parityCharacter
    {L : PrimeBitLattice} (β : ℝ) (ε : PrimeBitState L) :
    (ArithmeticFunction.moebius (primeBitInteger L ε) : ℝ) *
        primeBitMellinCharacter β ε =
      ((-1 : ℤ) ^ ε.1.card : ℝ) *
        primeBitMellinCharacter β ε := by
  have h := mobius_primeBitInteger_eq_parity ε
  have h' := congrArg
    (fun z : ℤ => (z : ℝ) * primeBitMellinCharacter β ε) h
  simpa using h'

end InfoGeometry.Arithmetic.PrimeValuationMellinFourierBridge
