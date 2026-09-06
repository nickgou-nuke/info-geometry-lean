import InfoGeometry.Arithmetic.PrimeEnergyNative
import InfoGeometry.Arithmetic.PrimonPhaseLift
import InfoGeometry.Physics.LogCFT
import InfoGeometry.Physics.LogCFTFiniteJordanBridge

/-!
# Finite Primon-to-Log-CFT Jordan injection

This is the finite algebraic part of the proposed arithmetic/Log-CFT bridge.
Prime energy is used as the scalar Jordan weight in the existing `L0` carrier.
No OPE, contour integral, central-charge, or scaling-limit statement is made.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonLogCFTInjection

open InfoGeometry.Arithmetic.PrimeEnergyNative
open InfoGeometry.Arithmetic.PrimonPhaseLift
open InfoGeometry.Physics
open Matrix

/-- The complexified logarithmic energy of a prime mode. -/
def primeLogWeight (p : Nat.Primes) : ℂ :=
  (Real.log (p : ℝ) : ℂ)

@[simp] theorem primeLogWeight_apply (p : Nat.Primes) :
    primeLogWeight p = (Real.log (p : ℝ) : ℂ) :=
  rfl

/-- The existing finite `L0` operator at the prime logarithmic weight. -/
def primeLogL0 (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  L0 (primeLogWeight p)

theorem primeLogL0_is_jordan_block (p : Nat.Primes) :
    primeLogL0 p = !![primeLogWeight p, 1; 0, primeLogWeight p] := by
  exact L0_is_jordan_block (primeLogWeight p)

/-- The centered prime Log-CFT operator is the canonical nilpotent shear. -/
theorem primeLogL0_centered_eq_N_log (p : Nat.Primes) :
    primeLogL0 p - primeLogWeight p •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) = N_log := by
  exact L0_sub_scalar_eq_N_log (primeLogWeight p)

theorem primeLogL0_centered_sq_zero (p : Nat.Primes) :
    (primeLogL0 p - primeLogWeight p •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) ^ 2 = 0 := by
  rw [primeLogL0_centered_eq_N_log p]
  simpa [pow_two] using (N_log_sq_zero (R := ℂ))

/-- The Jordan action on the packet's ordered pair `(logPartner, primary)`. -/
theorem primeLogL0_action (p : Nat.Primes) (logPartner primary : ℂ) :
    (primeLogL0 p).mulVec ![logPartner, primary] =
      ![primeLogWeight p * logPartner + primary,
        primeLogWeight p * primary] := by
  rw [primeLogL0_is_jordan_block p]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec]

/-! The arithmetic input remains separate from the Jordan carrier. -/

theorem primeLogWeight_real_pos (p : Nat.Primes) :
    0 < Real.log (p : ℝ) := by
  exact Real.log_pos (by exact_mod_cast p.property.one_lt)

/-! The scalar phase channel is the centered logarithmic Jordan weight. -/
theorem primonLogGenerator_scalar_eq_neg_realPart_primeLogWeight
    (σ t : ℝ) (p : Nat.Primes) (n : ℤ) :
    (primonLogGenerator σ t p n).scalar =
      -σ * (primeLogWeight p).re := by
  rw [primonLogGenerator_scalar, primeLogWeight_apply]
  change -σ * Real.log (p : ℝ) = -σ * Real.log (p : ℝ)
  rfl

end InfoGeometry.Arithmetic.PrimonLogCFTInjection
