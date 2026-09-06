import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeBitMobiusDirichletBridge

/-!
# Prime-bit Mellin/Laplace character bridge

For a finite prime-bit state, the integer encoded by the occupied primes is
positive.  This file identifies its complex Mellin character with the
Laplace character of its logarithmic energy.  Only finite pointwise algebra is
formalized; no transform integral, convergence statement, or Euler-product
limit is asserted.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeBitMellinLaplaceBridge

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.PrimeBitLattice
open InfoGeometry.Arithmetic.PrimeBitMobiusParityBridge

/-- The complex Mellin character of a finite prime-bit state. -/
def primeBitMellinCharacter {L : PrimeBitLattice}
    (s : ℂ) (ε : PrimeBitState L) : ℂ :=
  (primeBitInteger L ε : ℂ) ^ (-s)

/-- The Laplace character of the logarithmic prime-bit energy. -/
def primeBitLaplaceLogCharacter {L : PrimeBitLattice}
    (s : ℂ) (ε : PrimeBitState L) : ℂ :=
  Complex.exp (-s * (Real.log (primeBitInteger L ε : ℝ) : ℂ))

theorem primeBitInteger_pos {L : PrimeBitLattice} (ε : PrimeBitState L) :
    0 < primeBitInteger L ε := by
  exact Nat.pos_of_ne_zero (primeBitInteger_ne_zero ε)

theorem primeBitMellinCharacter_eq_laplaceLogCharacter
    {L : PrimeBitLattice} (s : ℂ) (ε : PrimeBitState L) :
    primeBitMellinCharacter s ε = primeBitLaplaceLogCharacter s ε := by
  have hn : 0 < primeBitInteger L ε := primeBitInteger_pos ε
  have hn0 : (primeBitInteger L ε : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  have hlog :
      Complex.log (primeBitInteger L ε : ℂ) =
        (Real.log (primeBitInteger L ε : ℝ) : ℂ) := by
    have hnreal : (0 : ℝ) ≤ (primeBitInteger L ε : ℝ) := by
      exact_mod_cast (Nat.zero_le (primeBitInteger L ε))
    exact (Complex.ofReal_log hnreal).symm
  rw [primeBitMellinCharacter, primeBitLaplaceLogCharacter]
  rw [Complex.cpow_def_of_ne_zero hn0]
  rw [hlog]
  congr 1
  ring

/-- The Mellin character is the Laplace character of the named finite energy. -/
theorem primeBitMellinCharacter_eq_primeBitEnergy_character
    {L : PrimeBitLattice} (s : ℂ) (ε : PrimeBitState L) :
    primeBitMellinCharacter s ε =
      Complex.exp (-s * (primeBitEnergy L ε.1 : ℂ)) := by
  rw [primeBitMellinCharacter_eq_laplaceLogCharacter]
  rw [primeBitEnergy_eq_log_primeBitInteger]
  rfl

end InfoGeometry.Arithmetic.PrimeBitMellinLaplaceBridge
