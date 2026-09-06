/-
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `phi_pow3` — φ³ = 2φ + 1 from φ² = φ + 1
- `phi_pow4_sub_one` — φ⁴ - 1 = 3φ + 1
- `one_add_phi_sq_mul_phi` — (1+φ²)·φ = 3φ + 1 (anyonic quantum dimension)
- `phi_mul_sub_one_eq_one` — φ·(φ-1) = 1 (golden ratio invertibility)
- `phi_ne_zero` — φ ≠ 0 (golden ratio is non-zero)
- `phi_inv_eq` — φ⁻¹ = φ - 1 (inverse identity)
- `phi_pow3_sub_inv` — φ³ - φ⁻¹ = φ + 2
- `verlinde_golden_identity_mul` — φ³ - φ⁻¹ = 1 + φ² (Verlinde fusion)
- `verlinde_golden_identity` — (φ³ - φ⁻¹)/(1+φ²) = 1 (anyonic loop closure)

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[None in this module.]

#### BUCKET 3: OPEN CLOSURE DEBT
[None in this module.]
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

namespace InfoGeometry.Canonical.GoldenRatioInvariants

variable {F : Type*} [Field F]

-- The defining equation of the golden ratio: φ² = φ + 1.
variable (phi : F) (hphi : phi ^ 2 = phi + 1)

include hphi

/-- The third power of the golden ratio equals 2φ + 1. -/
theorem phi_pow3 : phi^3 = 2 * phi + 1 := by
  calc
    phi^3 = phi * phi^2 := by ring
    _ = phi * (phi + 1) := by rw [hphi]
    _ = phi^2 + phi := by ring
    _ = (phi + 1) + phi := by rw [hphi]
    _ = 2 * phi + 1 := by ring

/-- φ⁴ - 1 = 3φ + 1. -/
theorem phi_pow4_sub_one : phi^4 - 1 = 3 * phi + 1 := by
  have h3 : phi ^ 3 = 2 * phi + 1 := phi_pow3 (phi := phi) (hphi := hphi)
  calc
    phi^4 - 1 = phi * phi^3 - 1 := by ring
    _ = phi * (2 * phi + 1) - 1 := by rw [h3]
    _ = 2 * phi^2 + phi - 1 := by ring
    _ = 2 * (phi + 1) + phi - 1 := by rw [hphi]
    _ = 3 * phi + 1 := by ring

/-- The anyonic quantum dimension scaling relation (1+φ²)·φ = 3φ+1. -/
theorem one_add_phi_sq_mul_phi : (1 + phi^2) * phi = 3 * phi + 1 := by
  have h3 : phi ^ 3 = 2 * phi + 1 := phi_pow3 (phi := phi) (hphi := hphi)
  calc
    (1 + phi^2) * phi = phi + phi^3 := by ring
    _ = phi + (2 * phi + 1) := by rw [h3]
    _ = 3 * phi + 1 := by ring

/-- The golden ratio satisfies φ·(φ-1) = 1. -/
theorem phi_mul_sub_one_eq_one : phi * (phi - 1) = 1 := by
  calc
    phi * (phi - 1) = phi^2 - phi := by ring
    _ = (phi + 1) - phi := by rw [hphi]
    _ = 1 := by ring

/-- The golden ratio is non-zero. -/
theorem phi_ne_zero : phi ≠ 0 := by
  intro hzero
  have h := phi_mul_sub_one_eq_one (phi := phi) (hphi := hphi)
  rw [hzero, zero_mul] at h
  exact zero_ne_one h

/-- φ⁻¹ = φ - 1. -/
theorem phi_inv_eq : phi⁻¹ = phi - 1 := by
  have h_ne : phi ≠ 0 := phi_ne_zero (phi := phi) (hphi := hphi)
  have hmul : phi * (phi - 1) = 1 := phi_mul_sub_one_eq_one (phi := phi) (hphi := hphi)
  calc
    phi⁻¹ = phi⁻¹ * 1 := by ring
    _ = phi⁻¹ * (phi * (phi - 1)) := by rw [hmul]
    _ = phi⁻¹ * phi * (phi - 1) := by ring
    _ = 1 * (phi - 1) := by rw [inv_mul_cancel₀ h_ne]
    _ = phi - 1 := by ring

/-- φ³ - φ⁻¹ = φ + 2. -/
theorem phi_pow3_sub_inv : phi^3 - phi⁻¹ = phi + 2 := by
  rw [phi_inv_eq (phi := phi) (hphi := hphi), phi_pow3 (phi := phi) (hphi := hphi)]
  ring

/-- Verlinde fusion: φ³ - φ⁻¹ = 1 + φ². -/
theorem verlinde_golden_identity_mul : phi^3 - phi⁻¹ = 1 + phi^2 := by
  rw [phi_pow3_sub_inv (phi := phi) (hphi := hphi)]
  calc
    phi + 2 = 1 + (phi + 1) := by ring
    _ = 1 + phi^2 := by rw [← hphi]

/-- Verlinde anyonic loop closure: (φ³ - φ⁻¹)/(1+φ²) = 1. -/
theorem verlinde_golden_identity (h_div : 1 + phi^2 ≠ 0) :
    (phi^3 - phi⁻¹) / (1 + phi^2) = 1 := by
  rw [verlinde_golden_identity_mul (phi := phi) (hphi := hphi)]
  exact div_self h_div

end InfoGeometry.Canonical.GoldenRatioInvariants
