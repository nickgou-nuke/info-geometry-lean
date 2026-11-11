/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.CliffordWeyl.ChiralIdeals

/-!
# An involution constructed from an energy-square relation

All identities retain the full associative real algebra. Normalization derives
the involution law from `H * H = E² • 1` and `E ≠ 0`. The existing Peirce owner
then supplies the two corner selection laws. These are algebraic projectors;
their interpretation as positive and negative energy spectral projectors needs
a self-adjoint represented Hamiltonian and `E > 0`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.EnergySign

open InfoGeometry.CliffordWeyl

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Derive an involution by normalizing a nonzero energy-square relation. -/
def energySignInvolution (H : A) (E : ℝ) (hE : E ≠ 0)
    (hH : H * H = E ^ 2 • (1 : A)) : ChiralInvolution A where
  chi := E⁻¹ • H
  chi_sq := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hH, smul_smul]
    have hcoeff : (E⁻¹ * E⁻¹) * E ^ 2 = (1 : ℝ) := by
      field_simp [hE] <;> ring
    rw [hcoeff, one_smul]

/-- The energy-square relation gives an explicit two-sided inverse of `H`. -/
theorem scaledHamiltonian_inverse (H : A) (E : ℝ) (hE : E ≠ 0)
    (hH : H * H = E ^ 2 • (1 : A)) :
    ((E ^ 2)⁻¹ • H) * H = 1 ∧ H * ((E ^ 2)⁻¹ • H) = 1 := by
  constructor
  · rw [smul_mul_assoc, hH, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hE), one_smul]
  · rw [mul_smul_comm, hH, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hE), one_smul]

/-- The polynomial-over-energy form of the odd residual. When `H² = E² • 1`,
the removed term equals `k H⁻¹` for the explicitly obtained inverse `H/E²`. -/
def energyResidual (H v : A) (E k : ℝ) : A :=
  v - (k / E ^ 2) • H

/-- The explicit residual agrees with the residual of the derived involution. -/
theorem energyResidual_eq_normalizedResidual (H v : A) (E k : ℝ)
    (hE : E ≠ 0) (hH : H * H = E ^ 2 • (1 : A)) :
    energyResidual H v E k =
      normalizedResidual (energySignInvolution H E hE hH) v (k / E) := by
  change v - (k / E ^ 2) • H = v - (k / E) • (E⁻¹ • H)
  rw [smul_smul]
  have hcoeff : k / E ^ 2 = (k / E) * E⁻¹ := by
    field_simp [hE] <;> ring
  rw [hcoeff]

/-- The Hamiltonian anticommutator scales by the same nonzero energy. -/
theorem energySignInvolution_anticommutator (H v : A) (E k : ℝ)
    (hE : E ≠ 0) (hH : H * H = E ^ 2 • (1 : A))
    (h : v * H + H * v = (2 * k) • (1 : A)) :
    v * (energySignInvolution H E hE hH).chi +
        (energySignInvolution H E hE hH).chi * v =
      (2 * (k / E)) • (1 : A) := by
  change v * (E⁻¹ • H) + (E⁻¹ • H) * v = (2 * (k / E)) • (1 : A)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, h, smul_smul]
  congr 1
  ring

/-- The explicit residual is odd under the constructed energy involution. -/
theorem energyResidual_anticommutes_energySign (H v : A) (E k : ℝ)
    (hE : E ≠ 0) (hH : H * H = E ^ 2 • (1 : A))
    (h : v * H + H * v = (2 * k) • (1 : A)) :
    let C := energySignInvolution H E hE hH
    energyResidual H v E k * C.chi = -(C.chi * energyResidual H v E k) := by
  simp only [energyResidual_eq_normalizedResidual H v E k hE hH]
  exact normalizedResidual_anticommutes _ v (k / E)
    (energySignInvolution_anticommutator H v E k hE hH h)

/-- Oddness also holds with respect to the unnormalized Hamiltonian. -/
theorem energyResidual_anticommutes (H v : A) (E k : ℝ)
    (hE : E ≠ 0) (hH : H * H = E ^ 2 • (1 : A))
    (h : v * H + H * v = (2 * k) • (1 : A)) :
    energyResidual H v E k * H = -(H * energyResidual H v E k) := by
  let C := energySignInvolution H E hE hH
  have hodd : energyResidual H v E k * C.chi =
      -(C.chi * energyResidual H v E k) :=
    energyResidual_anticommutes_energySign H v E k hE hH h
  have hrestore : E • C.chi = H := by
    change E • (E⁻¹ • H) = H
    rw [smul_smul, mul_inv_cancel₀ hE, one_smul]
  calc
    energyResidual H v E k * H = energyResidual H v E k * (E • C.chi) := by
      rw [hrestore]
    _ = E • (energyResidual H v E k * C.chi) := by rw [mul_smul_comm]
    _ = E • (-(C.chi * energyResidual H v E k)) := by rw [hodd]
    _ = -(H * energyResidual H v E k) := by
      rw [smul_neg, ← smul_mul_assoc, hrestore]

/-- The exact residual square for a square-one observable. -/
theorem energyResidual_sq (H v : A) (E k : ℝ)
    (hE : E ≠ 0) (hH : H * H = E ^ 2 • (1 : A)) (hv : v * v = 1)
    (h : v * H + H * v = (2 * k) • (1 : A)) :
    energyResidual H v E k * energyResidual H v E k =
      (1 - (k / E) ^ 2) • (1 : A) := by
  simp only [energyResidual_eq_normalizedResidual H v E k hE hH]
  exact normalizedResidual_sq _ v (k / E) hv
    (energySignInvolution_anticommutator H v E k hE hH h)

/-- Reuse the existing diagonal-corner theorem for the constructed energy split. -/
theorem energyResidual_diagonal_corners_zero (H v : A) (E k : ℝ)
    (hE : E ≠ 0) (hH : H * H = E ^ 2 • (1 : A))
    (h : v * H + H * v = (2 * k) • (1 : A)) :
    let C := energySignInvolution H E hE hH
    C.Pleft * energyResidual H v E k * C.Pleft = 0 ∧
      C.Pright * energyResidual H v E k * C.Pright = 0 := by
  exact diagonal_corners_zero (energySignInvolution H E hE hH) _
    (energyResidual_anticommutes_energySign H v E k hE hH h)

/-- Recover the full residual from its two inter-sector corners. -/
theorem energyResidual_off_diagonal_decomposition (H v : A) (E k : ℝ)
    (hE : E ≠ 0) (hH : H * H = E ^ 2 • (1 : A))
    (h : v * H + H * v = (2 * k) • (1 : A)) :
    let C := energySignInvolution H E hE hH
    energyResidual H v E k =
      C.Pleft * energyResidual H v E k * C.Pright +
        C.Pright * energyResidual H v E k * C.Pleft := by
  exact off_diagonal_decomposition (energySignInvolution H E hE hH) _
    (energyResidual_anticommutes_energySign H v E k hE hH h)

end InfoGeometry.OperatorAlgebra.EnergySign
