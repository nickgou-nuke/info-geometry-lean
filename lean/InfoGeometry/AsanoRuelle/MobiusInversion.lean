import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.AsanoRuelle.MobiusInversion

Mathematical Proof:
Step-1 Möbius inversion algebra for the Asano--Ruelle reduction.

No placeholders. No `sorry`.
-/

namespace InfoGeometry.AsanoRuelle

variable {K : Type*} [Field K]

/-- The forward Möbius map `ψ(z) = (A + B z) / (C + D z)`. -/
def ruelle_psi (A B C D z : K) : K :=
  (A + B * z) / (C + D * z)

/-- The dual Möbius map `χ(w) = (A + C w) / (B + D w)`. -/
def ruelle_chi (A B C D w : K) : K :=
  (A + C * w) / (B + D * w)

/--
Solve for `z₂`: off the pole, roots of the affine polynomial are exactly
`z₂ = -ψ(z₁)`.
-/
theorem asano_root_iff_psi
    (A B C D z1 z2 : K) (hpole : C + D * z1 ≠ 0) :
    A + B * z1 + C * z2 + D * z1 * z2 = 0 ↔ z2 = - ruelle_psi A B C D z1 := by
  constructor
  · intro h
    unfold ruelle_psi
    have h1 : z2 * (C + D * z1) = - (A + B * z1) := by
      calc
        z2 * (C + D * z1) = C * z2 + D * z1 * z2 := by ring
        _ = (A + B * z1 + C * z2 + D * z1 * z2) - (A + B * z1) := by ring
        _ = 0 - (A + B * z1) := by rw [h]
        _ = - (A + B * z1) := by ring
    calc
      z2 = z2 * (C + D * z1) / (C + D * z1) := (mul_div_cancel_right₀ z2 hpole).symm
      _ = -(A + B * z1) / (C + D * z1) := by rw [h1]
      _ = - ((A + B * z1) / (C + D * z1)) := by ring
  · intro h
    unfold ruelle_psi at h
    have h2 : z2 = -(A + B * z1) / (C + D * z1) := by
      calc
        z2 = - ((A + B * z1) / (C + D * z1)) := h
        _ = -(A + B * z1) / (C + D * z1) := by ring
    calc
      A + B * z1 + C * z2 + D * z1 * z2
          = A + B * z1 + z2 * (C + D * z1) := by ring
      _ = A + B * z1 + (-(A + B * z1) / (C + D * z1)) * (C + D * z1) := by rw [h2]
      _ = A + B * z1 + -(A + B * z1) := by rw [div_mul_cancel₀ _ hpole]
      _ = 0 := by ring

/--
Solve for `z₁`: off the pole, roots of the affine polynomial are exactly
`z₁ = -χ(z₂)`.
-/
theorem asano_root_iff_chi
    (A B C D z1 z2 : K) (hpole : B + D * z2 ≠ 0) :
    A + B * z1 + C * z2 + D * z1 * z2 = 0 ↔ z1 = - ruelle_chi A B C D z2 := by
  constructor
  · intro h
    unfold ruelle_chi
    have h1 : z1 * (B + D * z2) = - (A + C * z2) := by
      calc
        z1 * (B + D * z2) = B * z1 + D * z1 * z2 := by ring
        _ = (A + B * z1 + C * z2 + D * z1 * z2) - (A + C * z2) := by ring
        _ = 0 - (A + C * z2) := by rw [h]
        _ = - (A + C * z2) := by ring
    calc
      z1 = z1 * (B + D * z2) / (B + D * z2) := (mul_div_cancel_right₀ z1 hpole).symm
      _ = -(A + C * z2) / (B + D * z2) := by rw [h1]
      _ = - ((A + C * z2) / (B + D * z2)) := by ring
  · intro h
    unfold ruelle_chi at h
    have h2 : z1 = -(A + C * z2) / (B + D * z2) := by
      calc
        z1 = - ((A + C * z2) / (B + D * z2)) := h
        _ = -(A + C * z2) / (B + D * z2) := by ring
    calc
      A + B * z1 + C * z2 + D * z1 * z2
          = A + C * z2 + z1 * (B + D * z2) := by ring
      _ = A + C * z2 + (-(A + C * z2) / (B + D * z2)) * (B + D * z2) := by rw [h2]
      _ = A + C * z2 + -(A + C * z2) := by rw [div_mul_cancel₀ _ hpole]
      _ = 0 := by ring

/--
Nondegenerate pole-avoidance for the χ-denominator after substituting
`z₂ = -ψ(z)`.
-/
theorem chi_pole_avoidance
    (A B C D z : K)
    (hnondeg : A * D - B * C ≠ 0)
    (hpole : C + D * z ≠ 0) :
    B + D * (- ruelle_psi A B C D z) ≠ 0 := by
  unfold ruelle_psi
  intro h
  have h1 : (B + D * (- ((A + B * z) / (C + D * z)))) * (C + D * z) = 0 := by
    rw [h, zero_mul]
  have h2 : (B + D * (- ((A + B * z) / (C + D * z)))) * (C + D * z) = B * C - A * D := by
    have hcancel : (-(A + B * z) / (C + D * z)) * (C + D * z) = -(A + B * z) := by
      rw [div_mul_cancel₀ _ hpole]
    calc
      (B + D * (- ((A + B * z) / (C + D * z)))) * (C + D * z)
          = B * (C + D * z) + D * (- ((A + B * z) / (C + D * z))) * (C + D * z) := by ring
      _ = B * (C + D * z) + D * (-(A + B * z) / (C + D * z)) * (C + D * z) := by ring
      _ = B * (C + D * z) + D * ((-(A + B * z) / (C + D * z)) * (C + D * z)) := by ring
      _ = B * (C + D * z) + D * -(A + B * z) := by rw [hcancel]
      _ = B * C - A * D := by ring
  rw [h2] at h1
  have h3 : A * D - B * C = 0 := by
    calc
      A * D - B * C = -(B * C - A * D) := by ring
      _ = -0 := by rw [h1]
      _ = 0 := by ring
  exact hnondeg h3

/--
Inverse law: mapping `z ↦ -ψ(z) ↦ -χ(·)` returns `z`.
-/
theorem chi_psi_inverse
    (A B C D z : K)
    (hnondeg : A * D - B * C ≠ 0)
    (hpole : C + D * z ≠ 0) :
    - ruelle_chi A B C D (- ruelle_psi A B C D z) = z := by
  let z2 := - ruelle_psi A B C D z
  have h_root : A + B * z + C * z2 + D * z * z2 = 0 := by
    exact (asano_root_iff_psi A B C D z z2 hpole).mpr rfl
  have h_z2_pole : B + D * z2 ≠ 0 := chi_pole_avoidance A B C D z hnondeg hpole
  exact ((asano_root_iff_chi A B C D z z2 h_z2_pole).mp h_root).symm

end InfoGeometry.AsanoRuelle
