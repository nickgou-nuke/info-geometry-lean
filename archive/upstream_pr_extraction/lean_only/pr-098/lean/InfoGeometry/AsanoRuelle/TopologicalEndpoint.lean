import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic.Ring

/-!
# InfoGeometry.AsanoRuelle.TopologicalEndpoint

Exact open target and first algebraic sublemmas for the nondegenerate
Asano-Ruelle topological endpoint step.

No wrappers. No fake closures.
-/

namespace InfoGeometry.AsanoRuelle

/--
Exact open mathematical target for the nondegenerate topological endpoint.
-/
def asanoRuelleTopologicalEndpointClaim
    (K1 K2 : Set ℂ)
    (B C D : ℂ) : Prop :=
  (C ≠ 0 ∧ (-C / D) ∈ K1) ∨ (B ≠ 0 ∧ (-B / D) ∈ K2)

/--
Algebraic isolation of `z₂` from `Φ = 0`, off the left pole.
-/
theorem asano_isolate_z2
    {K : Type*} [Field K]
    {A B C D z1 z2 : K}
    (hPhi : A + B * z1 + C * z2 + D * z1 * z2 = 0)
    (hPole : C + D * z1 ≠ 0) :
    z2 = - (A + B * z1) / (C + D * z1) := by
  have h1 : (C + D * z1) * z2 = - (A + B * z1) := by
    calc
      (C + D * z1) * z2 = C * z2 + D * z1 * z2 := by ring
      _ = (A + B * z1 + C * z2 + D * z1 * z2) - (A + B * z1) := by ring
      _ = 0 - (A + B * z1) := by rw [hPhi]
      _ = - (A + B * z1) := by ring
  rw [← h1]
  exact (mul_div_cancel_left₀ z2 hPole).symm

/--
Pole-image exclusion: in the nondegenerate branch, the numerator does not
vanish at the left pole.
-/
theorem asano_numerator_ne_zero_at_pole
    {K : Type*} [Field K]
    {A B C D z1 : K}
    (hNondeg : A * D - B * C ≠ 0)
    (hPole : C + D * z1 = 0) :
    A + B * z1 ≠ 0 := by
  intro hNum
  have h_det : A * D - B * C = D * (A + B * z1) - B * (C + D * z1) := by ring
  rw [hNum, hPole, mul_zero, mul_zero, sub_zero] at h_det
  exact hNondeg h_det

/--
Nondegenerate pole exclusion on the zero locus.

If `AD - BC ≠ 0`, a root of
`A + B z₁ + C z₂ + D z₁ z₂ = 0`
cannot occur at the left Möbius pole `C + D z₁ = 0`.
-/
theorem asano_no_root_at_left_pole_of_nondegenerate
    {K : Type*} [Field K]
    {A B C D z1 z2 : K}
    (hNondeg : A * D - B * C ≠ 0)
    (hPole : C + D * z1 = 0)
    (hRoot : A + B * z1 + C * z2 + D * z1 * z2 = 0) :
    False := by
  have hNumNe : A + B * z1 ≠ 0 :=
    asano_numerator_ne_zero_at_pole (A := A) (B := B) (C := C) (D := D) hNondeg hPole
  have hNumEq : A + B * z1 = 0 := by
    have hLin :
        (C + D * z1) * z2 = - (A + B * z1) := by
      calc
        (C + D * z1) * z2 = C * z2 + D * z1 * z2 := by ring
        _ = (A + B * z1 + C * z2 + D * z1 * z2) - (A + B * z1) := by ring
        _ = 0 - (A + B * z1) := by rw [hRoot]
        _ = - (A + B * z1) := by ring
    rw [hPole, zero_mul] at hLin
    have hNeg : -(A + B * z1) = 0 := by simpa using hLin.symm
    exact neg_eq_zero.mp hNeg
  exact hNumNe hNumEq

/--
Möbius value identity near pole:
-(A + B(p + ε)) / (C + D(p + ε)) = -Δ / (D^2 ε) - B / D, where p = -C/D
-/
theorem mobius_pole_identity (A B C D ε : ℂ) (hD : D ≠ 0) (hε : ε ≠ 0) :
    -(A + B * (-C / D + ε)) / (C + D * (-C / D + ε)) =
    -(A * D - B * C) / (D^2 * ε) - B / D := by
  have hden : C + D * (-C / D + ε) = D * ε := by
    calc C + D * (-C / D + ε) = C + D * (-C / D) + D * ε := by ring
    _ = C - C + D * ε := by
      have : D * (-C / D) = -C := by
        calc D * (-C / D) = (D * -C) / D := by ring
        _ = -C := by rw [mul_div_cancel_left₀ (-C) hD]
      rw [this]
      ring
    _ = D * ε := by ring
  rw [hden]
  have hD2 : D^2 ≠ 0 := pow_ne_zero 2 hD
  have hD2ε : D^2 * ε ≠ 0 := mul_ne_zero hD2 hε
  have hDε : D * ε ≠ 0 := mul_ne_zero hD hε
  calc -(A + B * (-C / D + ε)) / (D * ε)
    _ = (-(A + B * (-C / D + ε)) * D) / (D^2 * ε) := by
      have : -(A + B * (-C / D + ε)) / (D * ε) = (-(A + B * (-C / D + ε)) * D) / (D * ε * D) := by
        rw [mul_div_mul_right _ _ hD]
      rw [this]
      have : D * ε * D = D^2 * ε := by ring
      rw [this]
    _ = (-(A * D - B * C) - B * D * ε) / (D^2 * ε) := by
      congr 1
      have : D * (-C / D) = -C := by
        calc D * (-C / D) = (D * -C) / D := by ring
        _ = -C := by rw [mul_div_cancel_left₀ (-C) hD]
      calc -(A + B * (-C / D + ε)) * D = -(A * D + B * (D * (-C / D + ε))) := by ring
      _ = -(A * D + B * (D * (-C / D) + D * ε)) := by ring
      _ = -(A * D + B * (-C + D * ε)) := by rw [this]
      _ = -(A * D - B * C) - B * D * ε := by ring
    _ = -(A * D - B * C) / (D^2 * ε) - (B * D * ε) / (D^2 * ε) := by
      rw [sub_div]
    _ = -(A * D - B * C) / (D^2 * ε) - B / D := by
      congr 1
      calc (B * D * ε) / (D^2 * ε) = (B * (D * ε)) / (D * (D * ε)) := by ring
      _ = B / D := by rw [mul_div_mul_right B D hDε]

/--
Vanishing of the two-variable Asano affine polynomial at the perturbed Möbius point:
$(z₁, z₂) = \left(-\frac{C}{D} + ε, -\frac{AD - BC}{D^2 ε} - \frac{B}{D}\right)$.
-/
theorem asanoPoly_zero_at_perturbed_pole (A B C D ε : ℂ) (hD : D ≠ 0) (hε : ε ≠ 0) :
    let z1 := -C / D + ε
    let z2 := -(A * D - B * C) / (D^2 * ε) - B / D
    A + B * z1 + C * z2 + D * z1 * z2 = 0 := by
  intro z1 z2
  dsimp [z1, z2]
  have hden : C + D * (-C / D + ε) = D * ε := by
    calc C + D * (-C / D + ε) = C + D * (-C / D) + D * ε := by ring
    _ = C - C + D * ε := by
      have : D * (-C / D) = -C := by
        calc D * (-C / D) = (D * -C) / D := by ring
        _ = -C := by rw [mul_div_cancel_left₀ (-C) hD]
      rw [this]
      ring
    _ = D * ε := by ring
  have hDε : D * ε ≠ 0 := mul_ne_zero hD hε
  have h_prod1 : (D * ε) * (-(A * D - B * C) / (D^2 * ε)) = -(A * D - B * C) / D := by
    have : (D * ε) * (-(A * D - B * C) / (D^2 * ε)) = (-(A * D - B * C) * (D * ε)) / (D * (D * ε)) := by ring
    rw [this, mul_div_mul_right _ _ hDε]
  have h_prod2 : (D * ε) * (B / D) = B * ε := by
    calc (D * ε) * (B / D) = (D * (B / D)) * ε := by ring
    _ = B * ε := by rw [mul_div_cancel₀ B hD]
  calc A + B * (-C / D + ε) + C * (-(A * D - B * C) / (D^2 * ε) - B / D) + D * (-C / D + ε) * (-(A * D - B * C) / (D^2 * ε) - B / D)
    _ = (A + B * (-C / D + ε)) + (C + D * (-C / D + ε)) * (-(A * D - B * C) / (D^2 * ε) - B / D) := by ring
    _ = (A + B * (-C / D + ε)) + (D * ε) * (-(A * D - B * C) / (D^2 * ε) - B / D) := by rw [hden]
    _ = (A + B * (-C / D + ε)) + ((D * ε) * (-(A * D - B * C) / (D^2 * ε)) - (D * ε) * (B / D)) := by rw [mul_sub]
    _ = (A + B * (-C / D + ε)) + (-(A * D - B * C) / D - B * ε) := by rw [h_prod1, h_prod2]
    _ = A + B * (-C / D) + B * ε - (A * D - B * C) / D - B * ε := by ring
    _ = A - (B * C) / D - (A * D - B * C) / D := by
      have : B * (-C / D) = - ((B * C) / D) := by ring
      rw [this]
      ring
    _ = (A * D - B * C) / D - (A * D - B * C) / D := by
      have : A - (B * C) / D = (A * D - B * C) / D := by
        calc A - (B * C) / D = (A * D) / D - (B * C) / D := by rw [mul_div_cancel_right₀ A hD]
        _ = (A * D - B * C) / D := by rw [sub_div]
      rw [this]
    _ = 0 := by ring

end InfoGeometry.AsanoRuelle
