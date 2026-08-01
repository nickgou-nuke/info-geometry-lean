import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge

/-!
# InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge

Artin braid group B₃ generators β₁, β₂ inside 3-ary Toeplitz-Cuntz ℰ₃ over a non-commutative Ring A,
the Coxeter element β₂ β₁ = Q + P₀, and compression Q = H (β₂ β₁) H.

This formalizes the Coxeter/permutation shadow of anyonic braiding inside ℰ₃.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
open ToeplitzCuntzThreeGenerators

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

/-- Adjacent sector swap β₁ = E₁₂ + E₂₁ + P₃ + P₀. -/
def braidGenerator1 : A :=
  g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3 + g.P0

/-- Adjacent sector swap β₂ = E₂₃ + E₃₂ + P₁ + P₀. -/
def braidGenerator2 : A :=
  g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1 + g.P0

/-- Coxeter element c = β₂ β₁ = E₁₂ + E₂₃ + E₃₁ + P₀ = Q + P₀. -/
def coxeterElement : A :=
  braidGenerator2 g * braidGenerator1 g

/-- **Theorem**: β₁ is self-adjoint. -/
theorem braidGenerator1_star : star (braidGenerator1 g) = braidGenerator1 g := by
  dsimp [braidGenerator1, P3, P0, P1, P2]
  simp only [star_add, star_mul, star_star, star_sub, star_one]
  noncomm_ring

/-- **Theorem**: β₂ is self-adjoint. -/
theorem braidGenerator2_star : star (braidGenerator2 g) = braidGenerator2 g := by
  dsimp [braidGenerator2, P1, P0, P2, P3]
  simp only [star_add, star_mul, star_star, star_sub, star_one]
  noncomm_ring

/-- **Theorem**: β₁² = 1. -/
theorem braidGenerator1_sq : braidGenerator1 g * braidGenerator1 g = 1 := by
  have hp1 := p1_idempotent g
  have hp2 := p2_idempotent g
  have hp3 := p3_idempotent g
  have hp0 := defectProjection_sq g
  have h12 := p1_p2_ortho g
  have h21 := p2_p1_ortho g
  have h23 := p2_p3_ortho g
  have h32 := p3_p2_ortho g
  have h13 := p1_p3_ortho g
  have h31 := p3_p1_ortho g
  have h_res := toeplitzCuntz3_resolution g
  have h12_21 : g.V1 * star g.V2 * (g.V2 * star g.V1) = g.P1 := by
    dsimp [P1]
    have h : g.V1 * star g.V2 * (g.V2 * star g.V1) = g.V1 * (star g.V2 * g.V2) * star g.V1 := by noncomm_ring
    rw [h, g.V2_isometry, mul_one]
  have h21_12 : g.V2 * star g.V1 * (g.V1 * star g.V2) = g.P2 := by
    dsimp [P2]
    have h : g.V2 * star g.V1 * (g.V1 * star g.V2) = g.V2 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V1_isometry, mul_one]
  have h12_12 : g.V1 * star g.V2 * (g.V1 * star g.V2) = 0 := by
    have h : g.V1 * star g.V2 * (g.V1 * star g.V2) = g.V1 * (star g.V2 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V2_V1_ortho, mul_zero, zero_mul]
  have h21_21 : g.V2 * star g.V1 * (g.V2 * star g.V1) = 0 := by
    have h : g.V2 * star g.V1 * (g.V2 * star g.V1) = g.V2 * (star g.V1 * g.V2) * star g.V1 := by noncomm_ring
    rw [h, g.V1_V2_ortho, mul_zero, zero_mul]
  have h12_3 : g.V1 * star g.V2 * g.P3 = 0 := by
    dsimp [P3]
    have h : g.V1 * star g.V2 * (g.V3 * star g.V3) = g.V1 * (star g.V2 * g.V3) * star g.V3 := by noncomm_ring
    rw [h, g.V2_V3_ortho, mul_zero, zero_mul]
  have h21_3 : g.V2 * star g.V1 * g.P3 = 0 := by
    dsimp [P3]
    have h : g.V2 * star g.V1 * (g.V3 * star g.V3) = g.V2 * (star g.V1 * g.V3) * star g.V3 := by noncomm_ring
    rw [h, g.V1_V3_ortho, mul_zero, zero_mul]
  have h3_12 : g.P3 * (g.V1 * star g.V2) = 0 := by
    dsimp [P3]
    have h : g.V3 * star g.V3 * (g.V1 * star g.V2) = g.V3 * (star g.V3 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V3_V1_ortho, mul_zero, zero_mul]
  have h3_21 : g.P3 * (g.V2 * star g.V1) = 0 := by
    dsimp [P3]
    have h : g.V3 * star g.V3 * (g.V2 * star g.V1) = g.V3 * (star g.V3 * g.V2) * star g.V1 := by noncomm_ring
    rw [h, g.V3_V2_ortho, mul_zero, zero_mul]
  have hd_left : (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3) * g.P0 = 0 := by
    have h12_p0 : g.V1 * star g.V2 * g.P0 = 0 := by
      have h1 : g.V1 * star g.V2 = g.V1 * star g.V2 * g.P2 := by
        dsimp [P2]
        have h : g.V1 * star g.V2 * (g.V2 * star g.V2) = g.V1 * (star g.V2 * g.V2) * star g.V2 := by noncomm_ring
        rw [h, g.V2_isometry, mul_one]
      rw [h1, mul_assoc, p2_p0_ortho g, mul_zero]
    have h21_p0 : g.V2 * star g.V1 * g.P0 = 0 := by
      have h1 : g.V2 * star g.V1 = g.V2 * star g.V1 * g.P1 := by
        dsimp [P1]
        have h : g.V2 * star g.V1 * (g.V1 * star g.V1) = g.V2 * (star g.V1 * g.V1) * star g.V1 := by noncomm_ring
        rw [h, g.V1_isometry, mul_one]
      rw [h1, mul_assoc, p1_p0_ortho g, mul_zero]
    have h3_p0 : g.P3 * g.P0 = 0 := p3_p0_ortho g
    calc (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3) * g.P0
        = g.V1 * star g.V2 * g.P0 + g.V2 * star g.V1 * g.P0 + g.P3 * g.P0 := by noncomm_ring
      _ = 0 := by rw [h12_p0, h21_p0, h3_p0]; abel
  have hd_right : g.P0 * (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3) = 0 := by
    have hp0_12 : g.P0 * (g.V1 * star g.V2) = 0 := by
      have h1 : g.V1 * star g.V2 = g.P1 * (g.V1 * star g.V2) := by
        dsimp [P1]
        have h : g.V1 * star g.V1 * (g.V1 * star g.V2) = g.V1 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
        rw [h, g.V1_isometry, mul_one]
      rw [h1, ← mul_assoc, p0_p1_ortho g, zero_mul]
    have hp0_21 : g.P0 * (g.V2 * star g.V1) = 0 := by
      have h1 : g.V2 * star g.V1 = g.P2 * (g.V2 * star g.V1) := by
        dsimp [P2]
        have h : g.V2 * star g.V2 * (g.V2 * star g.V1) = g.V2 * (star g.V2 * g.V2) * star g.V1 := by noncomm_ring
        rw [h, g.V2_isometry, mul_one]
      rw [h1, ← mul_assoc, p0_p2_ortho g, zero_mul]
    have hp0_3 : g.P0 * g.P3 = 0 := p0_p3_ortho g
    calc g.P0 * (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3)
        = g.P0 * (g.V1 * star g.V2) + g.P0 * (g.V2 * star g.V1) + g.P0 * g.P3 := by noncomm_ring
      _ = 0 := by rw [hp0_12, hp0_21, hp0_3]; abel
  dsimp [braidGenerator1]
  calc (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3 + g.P0) * (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3 + g.P0)
      = g.V1 * star g.V2 * (g.V1 * star g.V2) + g.V1 * star g.V2 * (g.V2 * star g.V1) + g.V1 * star g.V2 * g.P3
        + g.V2 * star g.V1 * (g.V1 * star g.V2) + g.V2 * star g.V1 * (g.V2 * star g.V1) + g.V2 * star g.V1 * g.P3
        + g.P3 * (g.V1 * star g.V2) + g.P3 * (g.V2 * star g.V1) + g.P3 * g.P3
        + (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3) * g.P0
        + g.P0 * (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3)
        + g.P0 * g.P0 := by noncomm_ring
    _ = 0 + g.P1 + 0 + g.P2 + 0 + 0 + 0 + 0 + g.P3 + 0 + 0 + g.P0 := by rw [h12_12, h12_21, h12_3, h21_12, h21_21, h21_3, h3_12, h3_21, hp3, hd_left, hd_right, hp0]
    _ = g.P1 + g.P2 + g.P3 + g.P0 := by abel
    _ = 1 := h_res

/-- **Theorem**: β₂² = 1. -/
theorem braidGenerator2_sq : braidGenerator2 g * braidGenerator2 g = 1 := by
  have hp1 := p1_idempotent g
  have hp2 := p2_idempotent g
  have hp3 := p3_idempotent g
  have hp0 := defectProjection_sq g
  have h12 := p1_p2_ortho g
  have h21 := p2_p1_ortho g
  have h23 := p2_p3_ortho g
  have h32 := p3_p2_ortho g
  have h13 := p1_p3_ortho g
  have h31 := p3_p1_ortho g
  have h_res := toeplitzCuntz3_resolution g
  have h23_32 : g.V2 * star g.V3 * (g.V3 * star g.V2) = g.P2 := by
    dsimp [P2]
    have h : g.V2 * star g.V3 * (g.V3 * star g.V2) = g.V2 * (star g.V3 * g.V3) * star g.V2 := by noncomm_ring
    rw [h, g.V3_isometry, mul_one]
  have h32_23 : g.V3 * star g.V2 * (g.V2 * star g.V3) = g.P3 := by
    dsimp [P3]
    have h : g.V3 * star g.V2 * (g.V2 * star g.V3) = g.V3 * (star g.V2 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V2_isometry, mul_one]
  have h23_23 : g.V2 * star g.V3 * (g.V2 * star g.V3) = 0 := by
    have h : g.V2 * star g.V3 * (g.V2 * star g.V3) = g.V2 * (star g.V3 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V3_V2_ortho, mul_zero, zero_mul]
  have h32_32 : g.V3 * star g.V2 * (g.V3 * star g.V2) = 0 := by
    have h : g.V3 * star g.V2 * (g.V3 * star g.V2) = g.V3 * (star g.V2 * g.V3) * star g.V2 := by noncomm_ring
    rw [h, g.V2_V3_ortho, mul_zero, zero_mul]
  have h23_1 : g.V2 * star g.V3 * g.P1 = 0 := by
    dsimp [P1]
    have h : g.V2 * star g.V3 * (g.V1 * star g.V1) = g.V2 * (star g.V3 * g.V1) * star g.V1 := by noncomm_ring
    rw [h, g.V3_V1_ortho, mul_zero, zero_mul]
  have h32_1 : g.V3 * star g.V2 * g.P1 = 0 := by
    dsimp [P1]
    have h : g.V3 * star g.V2 * (g.V1 * star g.V1) = g.V3 * (star g.V2 * g.V1) * star g.V1 := by noncomm_ring
    rw [h, g.V2_V1_ortho, mul_zero, zero_mul]
  have h1_23 : g.P1 * (g.V2 * star g.V3) = 0 := by
    dsimp [P1]
    have h : g.V1 * star g.V1 * (g.V2 * star g.V3) = g.V1 * (star g.V1 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V1_V2_ortho, mul_zero, zero_mul]
  have h1_32 : g.P1 * (g.V3 * star g.V2) = 0 := by
    dsimp [P1]
    have h : g.V1 * star g.V1 * (g.V3 * star g.V2) = g.V1 * (star g.V1 * g.V3) * star g.V2 := by noncomm_ring
    rw [h, g.V1_V3_ortho, mul_zero, zero_mul]
  have hd_left : (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1) * g.P0 = 0 := by
    have h23_p0 : g.V2 * star g.V3 * g.P0 = 0 := by
      have h1 : g.V2 * star g.V3 = g.V2 * star g.V3 * g.P3 := by
        dsimp [P3]
        have h : g.V2 * star g.V3 * (g.V3 * star g.V3) = g.V2 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
        rw [h, g.V3_isometry, mul_one]
      rw [h1, mul_assoc, p3_p0_ortho g, mul_zero]
    have h32_p0 : g.V3 * star g.V2 * g.P0 = 0 := by
      have h1 : g.V3 * star g.V2 = g.V3 * star g.V2 * g.P2 := by
        dsimp [P2]
        have h : g.V3 * star g.V2 * (g.V2 * star g.V2) = g.V3 * (star g.V2 * g.V2) * star g.V2 := by noncomm_ring
        rw [h, g.V2_isometry, mul_one]
      rw [h1, mul_assoc, p2_p0_ortho g, mul_zero]
    have h1_p0 : g.P1 * g.P0 = 0 := p1_p0_ortho g
    calc (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1) * g.P0
        = g.V2 * star g.V3 * g.P0 + g.V3 * star g.V2 * g.P0 + g.P1 * g.P0 := by noncomm_ring
      _ = 0 := by rw [h23_p0, h32_p0, h1_p0]; abel
  have hd_right : g.P0 * (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1) = 0 := by
    have hp0_23 : g.P0 * (g.V2 * star g.V3) = 0 := by
      have h1 : g.V2 * star g.V3 = g.P2 * (g.V2 * star g.V3) := by
        dsimp [P2]
        have h : g.V2 * star g.V2 * (g.V2 * star g.V3) = g.V2 * (star g.V2 * g.V2) * star g.V3 := by noncomm_ring
        rw [h, g.V2_isometry, mul_one]
      rw [h1, ← mul_assoc, p0_p2_ortho g, zero_mul]
    have hp0_32 : g.P0 * (g.V3 * star g.V2) = 0 := by
      have h1 : g.V3 * star g.V2 = g.P3 * (g.V3 * star g.V2) := by
        dsimp [P3]
        have h : g.V3 * star g.V3 * (g.V3 * star g.V2) = g.V3 * (star g.V3 * g.V3) * star g.V2 := by noncomm_ring
        rw [h, g.V3_isometry, mul_one]
      rw [h1, ← mul_assoc, p0_p3_ortho g, zero_mul]
    have hp0_1 : g.P0 * g.P1 = 0 := p0_p1_ortho g
    calc g.P0 * (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1)
        = g.P0 * (g.V2 * star g.V3) + g.P0 * (g.V3 * star g.V2) + g.P0 * g.P1 := by noncomm_ring
      _ = 0 := by rw [hp0_23, hp0_32, hp0_1]; abel
  dsimp [braidGenerator2]
  calc (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1 + g.P0) * (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1 + g.P0)
      = g.V2 * star g.V3 * (g.V2 * star g.V3) + g.V2 * star g.V3 * (g.V3 * star g.V2) + g.V2 * star g.V3 * g.P1
        + g.V3 * star g.V2 * (g.V2 * star g.V3) + g.V3 * star g.V2 * (g.V3 * star g.V2) + g.V3 * star g.V2 * g.P1
        + g.P1 * (g.V2 * star g.V3) + g.P1 * (g.V3 * star g.V2) + g.P1 * g.P1
        + (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1) * g.P0
        + g.P0 * (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1)
        + g.P0 * g.P0 := by noncomm_ring
    _ = 0 + g.P2 + 0 + g.P3 + 0 + 0 + 0 + 0 + g.P1 + 0 + 0 + g.P0 := by rw [h23_23, h23_32, h23_1, h32_23, h32_32, h32_1, h1_23, h1_32, hp1, hd_left, hd_right, hp0]
    _ = g.P1 + g.P2 + g.P3 + g.P0 := by abel
    _ = 1 := h_res

/-- **Theorem**: Coxeter Element is Cyclic Supercharge plus Defect: β₂ β₁ = Q + P₀. -/
theorem coxeterElement_eq_cyclicSupercharge_add_defect :
    coxeterElement g = cyclicSupercharge g + g.P0 := by
  dsimp [coxeterElement, braidGenerator1, braidGenerator2, cyclicSupercharge, P0, P1, P2, P3]
  have h23_3 : g.V2 * star g.V3 * g.P3 = g.V2 * star g.V3 := by
    dsimp [P3]
    have h : g.V2 * star g.V3 * (g.V3 * star g.V3) = g.V2 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
    rw [h, g.V3_isometry, mul_one]
  have h32_21 : g.V3 * star g.V2 * (g.V2 * star g.V1) = g.V3 * star g.V1 := by
    have h : g.V3 * star g.V2 * (g.V2 * star g.V1) = g.V3 * (star g.V2 * g.V2) * star g.V1 := by noncomm_ring
    rw [h, g.V2_isometry, mul_one]
  have h1_12 : g.P1 * (g.V1 * star g.V2) = g.V1 * star g.V2 := by
    dsimp [P1]
    have h : g.V1 * star g.V1 * (g.V1 * star g.V2) = g.V1 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V1_isometry, mul_one]
  have hp0 := defectProjection_sq g
  have hd_left : (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1) * g.P0 = 0 := by
    have h23_p0 : g.V2 * star g.V3 * g.P0 = 0 := by
      have h1 : g.V2 * star g.V3 = g.V2 * star g.V3 * g.P3 := by
        dsimp [P3]
        have h : g.V2 * star g.V3 * (g.V3 * star g.V3) = g.V2 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
        rw [h, g.V3_isometry, mul_one]
      rw [h1, mul_assoc, p3_p0_ortho g, mul_zero]
    have h32_p0 : g.V3 * star g.V2 * g.P0 = 0 := by
      have h1 : g.V3 * star g.V2 = g.V3 * star g.V2 * g.P2 := by
        dsimp [P2]
        have h : g.V3 * star g.V2 * (g.V2 * star g.V2) = g.V3 * (star g.V2 * g.V2) * star g.V2 := by noncomm_ring
        rw [h, g.V2_isometry, mul_one]
      rw [h1, mul_assoc, p2_p0_ortho g, mul_zero]
    have h1_p0 : g.P1 * g.P0 = 0 := p1_p0_ortho g
    calc (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1) * g.P0
        = g.V2 * star g.V3 * g.P0 + g.V3 * star g.V2 * g.P0 + g.P1 * g.P0 := by noncomm_ring
      _ = 0 := by rw [h23_p0, h32_p0, h1_p0]; abel
  have hd_right : g.P0 * (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3) = 0 := by
    have hp0_12 : g.P0 * (g.V1 * star g.V2) = 0 := by
      have h1 : g.V1 * star g.V2 = g.P1 * (g.V1 * star g.V2) := by
        dsimp [P1]
        have h : g.V1 * star g.V1 * (g.V1 * star g.V2) = g.V1 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
        rw [h, g.V1_isometry, mul_one]
      rw [h1, ← mul_assoc, p0_p1_ortho g, zero_mul]
    have hp0_21 : g.P0 * (g.V2 * star g.V1) = 0 := by
      have h1 : g.V2 * star g.V1 = g.P2 * (g.V2 * star g.V1) := by
        dsimp [P2]
        have h : g.V2 * star g.V2 * (g.V2 * star g.V1) = g.V2 * (star g.V2 * g.V2) * star g.V1 := by noncomm_ring
        rw [h, g.V2_isometry, mul_one]
      rw [h1, ← mul_assoc, p0_p2_ortho g, zero_mul]
    have hp0_3 : g.P0 * g.P3 = 0 := p0_p3_ortho g
    calc g.P0 * (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3)
        = g.P0 * (g.V1 * star g.V2) + g.P0 * (g.V2 * star g.V1) + g.P0 * g.P3 := by noncomm_ring
      _ = 0 := by rw [hp0_12, hp0_21, hp0_3]; abel
  have h23_12 : g.V2 * star g.V3 * (g.V1 * star g.V2) = 0 := by
    have h : g.V2 * star g.V3 * (g.V1 * star g.V2) = g.V2 * (star g.V3 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V3_V1_ortho, mul_zero, zero_mul]
  have h23_21 : g.V2 * star g.V3 * (g.V2 * star g.V1) = 0 := by
    have h : g.V2 * star g.V3 * (g.V2 * star g.V1) = g.V2 * (star g.V3 * g.V2) * star g.V1 := by noncomm_ring
    rw [h, g.V3_V2_ortho, mul_zero, zero_mul]
  have h32_12 : g.V3 * star g.V2 * (g.V1 * star g.V2) = 0 := by
    have h : g.V3 * star g.V2 * (g.V1 * star g.V2) = g.V3 * (star g.V2 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V2_V1_ortho, mul_zero, zero_mul]
  have h32_3 : g.V3 * star g.V2 * g.P3 = 0 := by
    dsimp [P3]
    have h : g.V3 * star g.V2 * (g.V3 * star g.V3) = g.V3 * (star g.V2 * g.V3) * star g.V3 := by noncomm_ring
    rw [h, g.V2_V3_ortho, mul_zero, zero_mul]
  have h1_21 : g.P1 * (g.V2 * star g.V1) = 0 := by
    dsimp [P1]
    have h : g.V1 * star g.V1 * (g.V2 * star g.V1) = g.V1 * (star g.V1 * g.V2) * star g.V1 := by noncomm_ring
    rw [h, g.V1_V2_ortho, mul_zero, zero_mul]
  have h1_3 : g.P1 * g.P3 = 0 := p1_p3_ortho g
  calc (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1 + g.P0) *
       (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3 + g.P0)
      = g.V2 * star g.V3 * (g.V1 * star g.V2) + g.V2 * star g.V3 * (g.V2 * star g.V1) + g.V2 * star g.V3 * g.P3
        + g.V3 * star g.V2 * (g.V1 * star g.V2) + g.V3 * star g.V2 * (g.V2 * star g.V1) + g.V3 * star g.V2 * g.P3
        + g.P1 * (g.V1 * star g.V2) + g.P1 * (g.V2 * star g.V1) + g.P1 * g.P3
        + (g.V2 * star g.V3 + g.V3 * star g.V2 + g.P1) * g.P0
        + g.P0 * (g.V1 * star g.V2 + g.V2 * star g.V1 + g.P3)
        + g.P0 * g.P0 := by noncomm_ring
    _ = 0 + 0 + g.V2 * star g.V3
        + 0 + g.V3 * star g.V1 + 0
        + g.V1 * star g.V2 + 0 + 0
        + 0 + 0 + g.P0 := by rw [h23_12, h23_21, h23_3, h32_12, h32_21, h32_3, h1_12, h1_21, h1_3, hd_left, hd_right, hp0]
    _ = g.V1 * star g.V2 + g.V2 * star g.V3 + g.V3 * star g.V1 + g.P0 := by abel

/-- **Theorem**: Q is the compressed Coxeter element: Q = H (β₂ β₁) H. -/
theorem cyclicSupercharge_eq_compressed_coxeter :
    cyclicSupercharge g = g.susyHamiltonian * coxeterElement g * g.susyHamiltonian := by
  have h_cox := coxeterElement_eq_cyclicSupercharge_add_defect g
  have hQ0 := cyclicSupercharge_defect_annihilation_right g
  have h0Q := cyclicSupercharge_defect_annihilation_left g
  have h_h : g.susyHamiltonian = 1 - g.P0 := by dsimp [susyHamiltonian, P0]; noncomm_ring
  rw [h_cox, h_h]
  symm
  calc (1 - g.P0) * (cyclicSupercharge g + g.P0) * (1 - g.P0)
      = (1 - g.P0) * (cyclicSupercharge g * (1 - g.P0) + g.P0 * (1 - g.P0)) := by noncomm_ring
    _ = (1 - g.P0) * (cyclicSupercharge g - cyclicSupercharge g * g.P0 + g.P0 - g.P0 * g.P0) := by noncomm_ring
    _ = (1 - g.P0) * cyclicSupercharge g := by rw [hQ0, defectProjection_sq g]; noncomm_ring
    _ = cyclicSupercharge g - g.P0 * cyclicSupercharge g := by noncomm_ring
    _ = cyclicSupercharge g := by rw [h0Q, sub_zero]

/-- **Theorem**: Coxeter Element Cube Identity (β₂ β₁)^3 = 1. -/
theorem coxeterElement_cube :
    coxeterElement g * coxeterElement g * coxeterElement g = 1 := by
  have h_cox := coxeterElement_eq_cyclicSupercharge_add_defect g
  have hQ3 := cyclicSupercharge_cube_eq_hamiltonian g
  have hQ0 := cyclicSupercharge_defect_annihilation_right g
  have h0Q := cyclicSupercharge_defect_annihilation_left g
  have hp0 := defectProjection_sq g
  rw [h_cox]
  calc (cyclicSupercharge g + g.P0) * (cyclicSupercharge g + g.P0) * (cyclicSupercharge g + g.P0)
      = (cyclicSupercharge g * cyclicSupercharge g + cyclicSupercharge g * g.P0 + g.P0 * cyclicSupercharge g + g.P0 * g.P0) * (cyclicSupercharge g + g.P0) := by noncomm_ring
    _ = (cyclicSupercharge g * cyclicSupercharge g + g.P0) * (cyclicSupercharge g + g.P0) := by rw [hQ0, h0Q, hp0]; noncomm_ring
    _ = cyclicSupercharge g * cyclicSupercharge g * cyclicSupercharge g + cyclicSupercharge g * cyclicSupercharge g * g.P0 + g.P0 * cyclicSupercharge g + g.P0 * g.P0 := by noncomm_ring
    _ = cyclicSupercharge g * cyclicSupercharge g * cyclicSupercharge g + g.P0 := by
        have hQ2_0 : cyclicSupercharge g * cyclicSupercharge g * g.P0 = 0 := by
          rw [mul_assoc, hQ0, mul_zero]
        rw [hQ2_0, h0Q, hp0]
        noncomm_ring
    _ = g.susyHamiltonian + g.P0 := by rw [hQ3]
    _ = 1 := by
        dsimp [susyHamiltonian, P0]
        exact toeplitzCuntz3_resolution g

/-- **Theorem**: Artin Braid Relation β₁ β₂ β₁ = β₂ β₁ β₂. -/
theorem artin_braid_relation :
    braidGenerator1 g * braidGenerator2 g * braidGenerator1 g =
    braidGenerator2 g * braidGenerator1 g * braidGenerator2 g := by
  have h1 := braidGenerator1_sq g
  have h2 := braidGenerator2_sq g
  have h_cube : (braidGenerator2 g * braidGenerator1 g) * (braidGenerator2 g * braidGenerator1 g) * (braidGenerator2 g * braidGenerator1 g) = 1 := by
    change coxeterElement g * coxeterElement g * coxeterElement g = 1
    exact coxeterElement_cube g
  have h_sub : (braidGenerator2 g * braidGenerator1 g * braidGenerator2 g * braidGenerator1 g * braidGenerator2 g) * braidGenerator1 g = 1 := by
    calc (braidGenerator2 g * braidGenerator1 g * braidGenerator2 g * braidGenerator1 g * braidGenerator2 g) * braidGenerator1 g
        = (braidGenerator2 g * braidGenerator1 g) * (braidGenerator2 g * braidGenerator1 g) * (braidGenerator2 g * braidGenerator1 g) := by noncomm_ring
      _ = 1 := h_cube
  have h_b2 : braidGenerator2 g * braidGenerator1 g * braidGenerator2 g * braidGenerator1 g * braidGenerator2 g = braidGenerator1 g := by
    calc braidGenerator2 g * braidGenerator1 g * braidGenerator2 g * braidGenerator1 g * braidGenerator2 g
        = (braidGenerator2 g * braidGenerator1 g * braidGenerator2 g * braidGenerator1 g * braidGenerator2 g) * (braidGenerator1 g * braidGenerator1 g) := by rw [h1, mul_one]
      _ = ((braidGenerator2 g * braidGenerator1 g * braidGenerator2 g * braidGenerator1 g * braidGenerator2 g) * braidGenerator1 g) * braidGenerator1 g := by noncomm_ring
      _ = 1 * braidGenerator1 g := by rw [h_sub]
      _ = braidGenerator1 g := by noncomm_ring
  calc braidGenerator1 g * braidGenerator2 g * braidGenerator1 g
      = 1 * (braidGenerator1 g * braidGenerator2 g * braidGenerator1 g) := by noncomm_ring
    _ = (braidGenerator2 g * braidGenerator2 g) * (braidGenerator1 g * braidGenerator2 g * braidGenerator1 g) := by rw [h2]
    _ = braidGenerator2 g * (braidGenerator2 g * braidGenerator1 g * braidGenerator2 g * braidGenerator1 g) := by noncomm_ring
    _ = braidGenerator2 g * (braidGenerator2 g * braidGenerator1 g * braidGenerator2 g * braidGenerator1 g * (braidGenerator2 g * braidGenerator2 g)) := by rw [h2, mul_one]
    _ = braidGenerator2 g * (braidGenerator2 g * braidGenerator1 g * braidGenerator2 g * braidGenerator1 g * braidGenerator2 g) * braidGenerator2 g := by noncomm_ring
    _ = braidGenerator2 g * braidGenerator1 g * braidGenerator2 g := by rw [h_b2]


end InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
