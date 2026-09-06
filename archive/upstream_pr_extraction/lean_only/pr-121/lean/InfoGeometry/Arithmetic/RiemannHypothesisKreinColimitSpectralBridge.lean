import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Tactic

/-!
# Native arithmetic and coordinate readouts for the zeta/Krein lane

This module contains only theorem-backed finite statements:

* the centered complex coordinate `s(E) = 1/2 + I E` and its inverse;
* the exact real-energy/critical-line coordinate equivalence;
* the native Mathlib Möbius--zeta convolution inverse.

It deliberately does not call scalar identities spectral, Hamiltonian,
Krein, PT-symmetric, or colimit theorems.  Operator anticommutation belongs
to the repository's CAR/Clifford owners, and Euler/L-series readouts belong
to the Bost--Connes owners.
-/

namespace InfoGeometry.Arithmetic.RiemannHypothesisKreinColimitSpectral

open ArithmeticFunction Complex

/-! ## Centered energy coordinates -/

/-- The complex coordinate associated to an energy parameter. -/
noncomputable def zeroFromEnergy (E : ℂ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * E

/-- The inverse coordinate map. -/
noncomputable def energyFromZero (s : ℂ) : ℂ :=
  -Complex.I * (s - 1 / 2)

theorem energy_zero_inverse (E : ℂ) :
    energyFromZero (zeroFromEnergy E) = E := by
  dsimp [energyFromZero, zeroFromEnergy]
  calc
    -Complex.I * (1 / 2 + Complex.I * E - 1 / 2) =
        -Complex.I * (Complex.I * E) := by ring
    _ = - (Complex.I * Complex.I) * E := by ring
    _ = - (-1) * E := by rw [Complex.I_mul_I]
    _ = E := by ring

theorem real_energy_iff_critical_line (E : ℂ) :
    E.im = 0 ↔ (zeroFromEnergy E).re = 1 / 2 := by
  have h_re : (zeroFromEnergy E).re = 1 / 2 - E.im := by
    dsimp [zeroFromEnergy]
    simp
    ring
  rw [h_re]
  constructor <;> intro h <;> linarith

theorem zeroFromEnergy_re (E : ℂ) :
    (zeroFromEnergy E).re = 1 / 2 - E.im := by
  dsimp [zeroFromEnergy]
  simp
  ring

/-! ## Native arithmetic inversion -/

/-- Mathlib's exact Dirichlet-convolution inverse for the zeta function. -/
theorem zeta_mul_moebius_eq_one :
    (ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction ℤ) = 1 := by
  exact ArithmeticFunction.coe_zeta_mul_coe_moebius

/-- The reversed convolution form, using commutativity of arithmetic functions.
-/
theorem moebius_mul_zeta_eq_one :
    (ArithmeticFunction.moebius * ArithmeticFunction.zeta :
      ArithmeticFunction ℤ) = 1 := by
  simpa [mul_comm] using zeta_mul_moebius_eq_one

theorem zeta_moebius_apply_one :
    ((ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction ℤ) 1) = 1 := by
  rw [zeta_mul_moebius_eq_one]
  simp

theorem zeta_moebius_apply_ne_one {n : ℕ} (hn : n ≠ 1) :
    ((ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction ℤ) n) = 0 := by
  rw [zeta_mul_moebius_eq_one]
  simp [hn]

end InfoGeometry.Arithmetic.RiemannHypothesisKreinColimitSpectral
