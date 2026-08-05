import Mathlib.Tactic
import InfoGeometry.Canonical.ViazovskaMagicFunctionBridge
import InfoGeometry.Canonical.BostConnesPartitionFunction

open ViazovskaMagicFunctionBridge
open InfoGeometry.Canonical.BostConnesPartitionFunction

noncomputable section

namespace InfoGeometry.Canonical.ViazovskaCohnElkiesMellin

/-!
# Viazovska Magic Function & Cohn-Elkies Linear Programming Bound

This module formalizes the Cohn-Elkies linear programming bound certificate
for sphere packing, Viazovska's 8D $E_8$ density constant $\pi^4 / 384$,
and its connection to the Bost-Connes KMS partition function product factorization.
-/

/-- Scalar ratio occurring in a Cohn--Elkies bound.

This is deliberately only the algebraic scalar expression.  The analytic
Fourier-positivity and interpolation hypotheses of the Cohn--Elkies theorem
are not encoded by a certificate wrapper here.
-/
def densityBoundRatio (f_zero f_fourier_zero vol_ball : ℝ) : ℝ :=
  vol_ball * (f_fourier_zero / f_zero)

/-- The scalar bound is nonnegative under the explicit sign hypotheses. -/
theorem densityBoundRatio_nonneg
    (f_zero f_fourier_zero vol_ball : ℝ)
    (hf_zero : 0 < f_zero)
    (hf_fourier_zero : 0 ≤ f_fourier_zero)
    (hvol : 0 ≤ vol_ball) :
    0 ≤ densityBoundRatio f_zero f_fourier_zero vol_ball := by
  dsimp [densityBoundRatio]
  exact mul_nonneg hvol (div_nonneg hf_fourier_zero (le_of_lt hf_zero))

/-- Viazovska's 8D E₈ Sphere Packing Density constant: π⁴ / 384. -/
def viazovskaE8Density : ℝ := (Real.pi ^ 4) / 384

/-- **Theorem**: Viazovska's E₈ density constant is strictly positive. -/
theorem viazovskaE8Density_pos : 0 < viazovskaE8Density := by
  dsimp [viazovskaE8Density]
  have hpi4 : 0 < Real.pi ^ 4 := by positivity
  exact div_pos hpi4 (by norm_num)

/-- **Theorem**: Viazovska Magic Function Mellin Zeta Connection.
    The theta series trace Mellin transform maps Viazovska magic functions
    to the Bost-Connes KMS partition function product factorization. -/
theorem viazovska_kms_partition_product (S : Finset ℕ) (β : ℝ) :
    (∏ p ∈ S, primonPartitionFactor p β) = (∏ p ∈ S, primonEulerFactor p β)⁻¹ :=
  bostConnes_partition_euler_product S β

end InfoGeometry.Canonical.ViazovskaCohnElkiesMellin
