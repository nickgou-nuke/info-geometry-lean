import InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge

/-!
# InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge

Order-three fractional supersymmetry (Z₃-graded cubic SUSY QM) on Toeplitz-Cuntz ℰ₃.

Cyclic Supercharge: Q = V₁ V₂* + V₂ V₃* + V₃ V₁*.
Fundamental Z₃ Relation: Q* = Q².
Cubic Fractional SUSY Law: Q³ = H = 1 - P₀.
Normal Partial Isometry: Q* Q = Q Q* = H.
Bilateral Vacuum Annihilation: Q P₀ = 0, P₀ Q = 0, H P₀ = 0, P₀ H = 0.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open ToeplitzCuntzThreeGenerators

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

/-- Cyclic Supercharge Q = V₁ V₂* + V₂ V₃* + V₃ V₁*. -/
def cyclicSupercharge (g : ToeplitzCuntzThreeGenerators A) : A :=
  g.V1 * star g.V2 + g.V2 * star g.V3 + g.V3 * star g.V1

/-- Square of the Cyclic Supercharge Q² = V₁ V₃* + V₂ V₁* + V₃ V₂*. -/
theorem cyclicSupercharge_sq :
    cyclicSupercharge g * cyclicSupercharge g =
    g.V1 * star g.V3 + g.V2 * star g.V1 + g.V3 * star g.V2 := by
  dsimp [cyclicSupercharge]
  have h12_23 : g.V1 * star g.V2 * (g.V2 * star g.V3) = g.V1 * star g.V3 := by
    have h : g.V1 * star g.V2 * (g.V2 * star g.V3) = g.V1 * (star g.V2 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V2_isometry, mul_one]
  have h23_31 : g.V2 * star g.V3 * (g.V3 * star g.V1) = g.V2 * star g.V1 := by
    have h : g.V2 * star g.V3 * (g.V3 * star g.V1) = g.V2 * (star g.V3 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, g.V3_isometry, mul_one]
  have h31_12 : g.V3 * star g.V1 * (g.V1 * star g.V2) = g.V3 * star g.V2 := by
    have h : g.V3 * star g.V1 * (g.V1 * star g.V2) = g.V3 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V1_isometry, mul_one]
  have h_ortho1 : g.V1 * star g.V2 * (g.V1 * star g.V2) = 0 := by
    have h : g.V1 * star g.V2 * (g.V1 * star g.V2) = g.V1 * (star g.V2 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V2_V1_ortho, mul_zero, zero_mul]
  have h_ortho2 : g.V1 * star g.V2 * (g.V3 * star g.V1) = 0 := by
    have h : g.V1 * star g.V2 * (g.V3 * star g.V1) = g.V1 * (star g.V2 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, g.V2_V3_ortho, mul_zero, zero_mul]
  have h_ortho3 : g.V2 * star g.V3 * (g.V1 * star g.V2) = 0 := by
    have h : g.V2 * star g.V3 * (g.V1 * star g.V2) = g.V2 * (star g.V3 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V3_V1_ortho, mul_zero, zero_mul]
  have h_ortho4 : g.V2 * star g.V3 * (g.V2 * star g.V3) = 0 := by
    have h : g.V2 * star g.V3 * (g.V2 * star g.V3) = g.V2 * (star g.V3 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V3_V2_ortho, mul_zero, zero_mul]
  have h_ortho5 : g.V3 * star g.V1 * (g.V2 * star g.V3) = 0 := by
    have h : g.V3 * star g.V1 * (g.V2 * star g.V3) = g.V3 * (star g.V1 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V1_V2_ortho, mul_zero, zero_mul]
  have h_ortho6 : g.V3 * star g.V1 * (g.V3 * star g.V1) = 0 := by
    have h : g.V3 * star g.V1 * (g.V3 * star g.V1) = g.V3 * (star g.V1 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, g.V1_V3_ortho, mul_zero, zero_mul]
  calc (g.V1 * star g.V2 + g.V2 * star g.V3 + g.V3 * star g.V1) * (g.V1 * star g.V2 + g.V2 * star g.V3 + g.V3 * star g.V1)
      = g.V1 * star g.V2 * (g.V1 * star g.V2) + g.V1 * star g.V2 * (g.V2 * star g.V3) + g.V1 * star g.V2 * (g.V3 * star g.V1)
        + g.V2 * star g.V3 * (g.V1 * star g.V2) + g.V2 * star g.V3 * (g.V2 * star g.V3) + g.V2 * star g.V3 * (g.V3 * star g.V1)
        + g.V3 * star g.V1 * (g.V1 * star g.V2) + g.V3 * star g.V1 * (g.V2 * star g.V3) + g.V3 * star g.V1 * (g.V3 * star g.V1) := by noncomm_ring
    _ = 0 + g.V1 * star g.V3 + 0
        + 0 + 0 + g.V2 * star g.V1
        + g.V3 * star g.V2 + 0 + 0 := by rw [h_ortho1, h12_23, h_ortho2, h_ortho3, h_ortho4, h23_31, h31_12, h_ortho5, h_ortho6]
    _ = g.V1 * star g.V3 + g.V2 * star g.V1 + g.V3 * star g.V2 := by abel

/-- Fundamental Z₃ Adjoint Relation: Q* = Q². -/
theorem cyclicSupercharge_star_eq_sq :
    star (cyclicSupercharge g) = cyclicSupercharge g * cyclicSupercharge g := by
  rw [cyclicSupercharge_sq g]
  dsimp [cyclicSupercharge]
  simp
  abel

/-- **Theorem**: Cubic Fractional SUSY Law Q³ = H = 1 - P₀. -/
theorem cyclicSupercharge_cube_eq_hamiltonian :
    cyclicSupercharge g * cyclicSupercharge g * cyclicSupercharge g = g.susyHamiltonian := by
  rw [cyclicSupercharge_sq g]
  dsimp [cyclicSupercharge, susyHamiltonian, P1, P2, P3]
  have h13_31 : g.V1 * star g.V3 * (g.V3 * star g.V1) = g.V1 * star g.V1 := by
    have h : g.V1 * star g.V3 * (g.V3 * star g.V1) = g.V1 * (star g.V3 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, g.V3_isometry, mul_one]
  have h21_12 : g.V2 * star g.V1 * (g.V1 * star g.V2) = g.V2 * star g.V2 := by
    have h : g.V2 * star g.V1 * (g.V1 * star g.V2) = g.V2 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V1_isometry, mul_one]
  have h32_23 : g.V3 * star g.V2 * (g.V2 * star g.V3) = g.V3 * star g.V3 := by
    have h : g.V3 * star g.V2 * (g.V2 * star g.V3) = g.V3 * (star g.V2 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V2_isometry, mul_one]
  have h_o1 : g.V1 * star g.V3 * (g.V1 * star g.V2) = 0 := by
    have h : g.V1 * star g.V3 * (g.V1 * star g.V2) = g.V1 * (star g.V3 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V3_V1_ortho, mul_zero, zero_mul]
  have h_o2 : g.V1 * star g.V3 * (g.V2 * star g.V3) = 0 := by
    have h : g.V1 * star g.V3 * (g.V2 * star g.V3) = g.V1 * (star g.V3 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V3_V2_ortho, mul_zero, zero_mul]
  have h_o3 : g.V2 * star g.V1 * (g.V2 * star g.V3) = 0 := by
    have h : g.V2 * star g.V1 * (g.V2 * star g.V3) = g.V2 * (star g.V1 * g.V2) * star g.V3 := by noncomm_ring
    rw [h, g.V1_V2_ortho, mul_zero, zero_mul]
  have h_o4 : g.V2 * star g.V1 * (g.V3 * star g.V1) = 0 := by
    have h : g.V2 * star g.V1 * (g.V3 * star g.V1) = g.V2 * (star g.V1 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, g.V1_V3_ortho, mul_zero, zero_mul]
  have h_o5 : g.V3 * star g.V2 * (g.V1 * star g.V2) = 0 := by
    have h : g.V3 * star g.V2 * (g.V1 * star g.V2) = g.V3 * (star g.V2 * g.V1) * star g.V2 := by noncomm_ring
    rw [h, g.V2_V1_ortho, mul_zero, zero_mul]
  have h_o6 : g.V3 * star g.V2 * (g.V3 * star g.V1) = 0 := by
    have h : g.V3 * star g.V2 * (g.V3 * star g.V1) = g.V3 * (star g.V2 * g.V3) * star g.V1 := by noncomm_ring
    rw [h, g.V2_V3_ortho, mul_zero, zero_mul]
  calc (g.V1 * star g.V3 + g.V2 * star g.V1 + g.V3 * star g.V2) * (g.V1 * star g.V2 + g.V2 * star g.V3 + g.V3 * star g.V1)
      = g.V1 * star g.V3 * (g.V1 * star g.V2) + g.V1 * star g.V3 * (g.V2 * star g.V3) + g.V1 * star g.V3 * (g.V3 * star g.V1)
        + g.V2 * star g.V1 * (g.V1 * star g.V2) + g.V2 * star g.V1 * (g.V2 * star g.V3) + g.V2 * star g.V1 * (g.V3 * star g.V1)
        + g.V3 * star g.V2 * (g.V1 * star g.V2) + g.V3 * star g.V2 * (g.V2 * star g.V3) + g.V3 * star g.V2 * (g.V3 * star g.V1) := by noncomm_ring
    _ = 0 + 0 + g.V1 * star g.V1
        + g.V2 * star g.V2 + 0 + 0
        + 0 + g.V3 * star g.V3 + 0 := by rw [h_o1, h_o2, h13_31, h21_12, h_o3, h_o4, h_o5, h32_23, h_o6]
    _ = g.V1 * star g.V1 + g.V2 * star g.V2 + g.V3 * star g.V3 := by abel

/-- Normal partial isometry Q* Q = H. -/
theorem cyclicSupercharge_star_mul_self :
    star (cyclicSupercharge g) * cyclicSupercharge g = g.susyHamiltonian := by
  rw [cyclicSupercharge_star_eq_sq g]
  exact cyclicSupercharge_cube_eq_hamiltonian g

/-- Normal partial isometry Q Q* = H. -/
theorem cyclicSupercharge_mul_star :
    cyclicSupercharge g * star (cyclicSupercharge g) = g.susyHamiltonian := by
  rw [cyclicSupercharge_star_eq_sq g]
  have h : cyclicSupercharge g * (cyclicSupercharge g * cyclicSupercharge g) =
           cyclicSupercharge g * cyclicSupercharge g * cyclicSupercharge g := by noncomm_ring
  rw [h]
  exact cyclicSupercharge_cube_eq_hamiltonian g

/-- Right vacuum annihilation Q P₀ = 0. -/
theorem cyclicSupercharge_defect_annihilation_right : cyclicSupercharge g * g.P0 = 0 := by
  have h1 : g.V1 * star g.V2 * (1 - g.P1 - g.P2 - g.P3) = 0 := by
    dsimp [P1, P2, P3]
    have h_split : g.V1 * star g.V2 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) =
                   g.V1 * star g.V2 - g.V1 * star g.V2 * (g.V1 * star g.V1) - g.V1 * star g.V2 * (g.V2 * star g.V2) - g.V1 * star g.V2 * (g.V3 * star g.V3) := by noncomm_ring
    have h_sub1 : g.V1 * star g.V2 * (g.V1 * star g.V1) = 0 := by
      have h : g.V1 * star g.V2 * (g.V1 * star g.V1) = g.V1 * (star g.V2 * g.V1) * star g.V1 := by noncomm_ring
      rw [h, g.V2_V1_ortho, mul_zero, zero_mul]
    have h_sub2 : g.V1 * star g.V2 * (g.V2 * star g.V2) = g.V1 * star g.V2 := by
      have h : g.V1 * star g.V2 * (g.V2 * star g.V2) = g.V1 * (star g.V2 * g.V2) * star g.V2 := by noncomm_ring
      rw [h, g.V2_isometry, mul_one]
    have h_sub3 : g.V1 * star g.V2 * (g.V3 * star g.V3) = 0 := by
      have h : g.V1 * star g.V2 * (g.V3 * star g.V3) = g.V1 * (star g.V2 * g.V3) * star g.V3 := by noncomm_ring
      rw [h, g.V2_V3_ortho, mul_zero, zero_mul]
    rw [h_split, h_sub1, h_sub2, h_sub3]
    noncomm_ring
  have h2 : g.V2 * star g.V3 * (1 - g.P1 - g.P2 - g.P3) = 0 := by
    dsimp [P1, P2, P3]
    have h_split : g.V2 * star g.V3 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) =
                   g.V2 * star g.V3 - g.V2 * star g.V3 * (g.V1 * star g.V1) - g.V2 * star g.V3 * (g.V2 * star g.V2) - g.V2 * star g.V3 * (g.V3 * star g.V3) := by noncomm_ring
    have h_sub1 : g.V2 * star g.V3 * (g.V1 * star g.V1) = 0 := by
      have h : g.V2 * star g.V3 * (g.V1 * star g.V1) = g.V2 * (star g.V3 * g.V1) * star g.V1 := by noncomm_ring
      rw [h, g.V3_V1_ortho, mul_zero, zero_mul]
    have h_sub2 : g.V2 * star g.V3 * (g.V2 * star g.V2) = 0 := by
      have h : g.V2 * star g.V3 * (g.V2 * star g.V2) = g.V2 * (star g.V3 * g.V2) * star g.V2 := by noncomm_ring
      rw [h, g.V3_V2_ortho, mul_zero, zero_mul]
    have h_sub3 : g.V2 * star g.V3 * (g.V3 * star g.V3) = g.V2 * star g.V3 := by
      have h : g.V2 * star g.V3 * (g.V3 * star g.V3) = g.V2 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
      rw [h, g.V3_isometry, mul_one]
    rw [h_split, h_sub1, h_sub2, h_sub3]
    noncomm_ring
  have h3 : g.V3 * star g.V1 * (1 - g.P1 - g.P2 - g.P3) = 0 := by
    dsimp [P1, P2, P3]
    have h_split : g.V3 * star g.V1 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) =
                   g.V3 * star g.V1 - g.V3 * star g.V1 * (g.V1 * star g.V1) - g.V3 * star g.V1 * (g.V2 * star g.V2) - g.V3 * star g.V1 * (g.V3 * star g.V3) := by noncomm_ring
    have h_sub1 : g.V3 * star g.V1 * (g.V1 * star g.V1) = g.V3 * star g.V1 := by
      have h : g.V3 * star g.V1 * (g.V1 * star g.V1) = g.V3 * (star g.V1 * g.V1) * star g.V1 := by noncomm_ring
      rw [h, g.V1_isometry, mul_one]
    have h_sub2 : g.V3 * star g.V1 * (g.V2 * star g.V2) = 0 := by
      have h : g.V3 * star g.V1 * (g.V2 * star g.V2) = g.V3 * (star g.V1 * g.V2) * star g.V2 := by noncomm_ring
      rw [h, g.V1_V2_ortho, mul_zero, zero_mul]
    have h_sub3 : g.V3 * star g.V1 * (g.V3 * star g.V3) = 0 := by
      have h : g.V3 * star g.V1 * (g.V3 * star g.V3) = g.V3 * (star g.V1 * g.V3) * star g.V3 := by noncomm_ring
      rw [h, g.V1_V3_ortho, mul_zero, zero_mul]
    rw [h_split, h_sub1, h_sub2, h_sub3]
    noncomm_ring
  dsimp [cyclicSupercharge, P0]
  calc (g.V1 * star g.V2 + g.V2 * star g.V3 + g.V3 * star g.V1) * (1 - g.P1 - g.P2 - g.P3)
      = g.V1 * star g.V2 * (1 - g.P1 - g.P2 - g.P3) + g.V2 * star g.V3 * (1 - g.P1 - g.P2 - g.P3) + g.V3 * star g.V1 * (1 - g.P1 - g.P2 - g.P3) := by noncomm_ring
    _ = 0 + 0 + 0 := by rw [h1, h2, h3]
    _ = 0 := by abel

/-- Left vacuum annihilation P₀ Q = 0. -/
theorem cyclicSupercharge_defect_annihilation_left : g.P0 * cyclicSupercharge g = 0 := by
  have h1 : (1 - g.P1 - g.P2 - g.P3) * (g.V1 * star g.V2) = 0 := by
    dsimp [P1, P2, P3]
    have h_split : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V1 * star g.V2) =
                   g.V1 * star g.V2 - g.V1 * star g.V1 * (g.V1 * star g.V2) - g.V2 * star g.V2 * (g.V1 * star g.V2) - g.V3 * star g.V3 * (g.V1 * star g.V2) := by noncomm_ring
    have h_sub1 : g.V1 * star g.V1 * (g.V1 * star g.V2) = g.V1 * star g.V2 := by
      have h : g.V1 * star g.V1 * (g.V1 * star g.V2) = g.V1 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
      rw [h, g.V1_isometry, mul_one]
    have h_sub2 : g.V2 * star g.V2 * (g.V1 * star g.V2) = 0 := by
      have h : g.V2 * star g.V2 * (g.V1 * star g.V2) = g.V2 * (star g.V2 * g.V1) * star g.V2 := by noncomm_ring
      rw [h, g.V2_V1_ortho, mul_zero, zero_mul]
    have h_sub3 : g.V3 * star g.V3 * (g.V1 * star g.V2) = 0 := by
      have h : g.V3 * star g.V3 * (g.V1 * star g.V2) = g.V3 * (star g.V3 * g.V1) * star g.V2 := by noncomm_ring
      rw [h, g.V3_V1_ortho, mul_zero, zero_mul]
    rw [h_split, h_sub1, h_sub2, h_sub3]
    noncomm_ring
  have h2 : (1 - g.P1 - g.P2 - g.P3) * (g.V2 * star g.V3) = 0 := by
    dsimp [P1, P2, P3]
    have h_split : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V2 * star g.V3) =
                   g.V2 * star g.V3 - g.V1 * star g.V1 * (g.V2 * star g.V3) - g.V2 * star g.V2 * (g.V2 * star g.V3) - g.V3 * star g.V3 * (g.V2 * star g.V3) := by noncomm_ring
    have h_sub1 : g.V1 * star g.V1 * (g.V2 * star g.V3) = 0 := by
      have h : g.V1 * star g.V1 * (g.V2 * star g.V3) = g.V1 * (star g.V1 * g.V2) * star g.V3 := by noncomm_ring
      rw [h, g.V1_V2_ortho, mul_zero, zero_mul]
    have h_sub2 : g.V2 * star g.V2 * (g.V2 * star g.V3) = g.V2 * star g.V3 := by
      have h : g.V2 * star g.V2 * (g.V2 * star g.V3) = g.V2 * (star g.V2 * g.V2) * star g.V3 := by noncomm_ring
      rw [h, g.V2_isometry, mul_one]
    have h_sub3 : g.V3 * star g.V3 * (g.V2 * star g.V3) = 0 := by
      have h : g.V3 * star g.V3 * (g.V2 * star g.V3) = g.V3 * (star g.V3 * g.V2) * star g.V3 := by noncomm_ring
      rw [h, g.V3_V2_ortho, mul_zero, zero_mul]
    rw [h_split, h_sub1, h_sub2, h_sub3]
    noncomm_ring
  have h3 : (1 - g.P1 - g.P2 - g.P3) * (g.V3 * star g.V1) = 0 := by
    dsimp [P1, P2, P3]
    have h_split : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V3 * star g.V1) =
                   g.V3 * star g.V1 - g.V1 * star g.V1 * (g.V3 * star g.V1) - g.V2 * star g.V2 * (g.V3 * star g.V1) - g.V3 * star g.V3 * (g.V3 * star g.V1) := by noncomm_ring
    have h_sub1 : g.V1 * star g.V1 * (g.V3 * star g.V1) = 0 := by
      have h : g.V1 * star g.V1 * (g.V3 * star g.V1) = g.V1 * (star g.V1 * g.V3) * star g.V1 := by noncomm_ring
      rw [h, g.V1_V3_ortho, mul_zero, zero_mul]
    have h_sub2 : g.V2 * star g.V2 * (g.V3 * star g.V1) = 0 := by
      have h : g.V2 * star g.V2 * (g.V3 * star g.V1) = g.V2 * (star g.V2 * g.V3) * star g.V1 := by noncomm_ring
      rw [h, g.V2_V3_ortho, mul_zero, zero_mul]
    have h_sub3 : g.V3 * star g.V3 * (g.V3 * star g.V1) = g.V3 * star g.V1 := by
      have h : g.V3 * star g.V3 * (g.V3 * star g.V1) = g.V3 * (star g.V3 * g.V3) * star g.V1 := by noncomm_ring
      rw [h, g.V3_isometry, mul_one]
    rw [h_split, h_sub1, h_sub2, h_sub3]
    noncomm_ring
  dsimp [cyclicSupercharge, P0]
  calc (1 - g.P1 - g.P2 - g.P3) * (g.V1 * star g.V2 + g.V2 * star g.V3 + g.V3 * star g.V1)
      = (1 - g.P1 - g.P2 - g.P3) * (g.V1 * star g.V2) + (1 - g.P1 - g.P2 - g.P3) * (g.V2 * star g.V3) + (1 - g.P1 - g.P2 - g.P3) * (g.V3 * star g.V1) := by noncomm_ring
    _ = 0 + 0 + 0 := by rw [h1, h2, h3]
    _ = 0 := by abel

/-- **Theorem**: Nontrivial 3-ary Algebraic Vacuum Witness. -/
theorem nontrivial_3ary_algebraic_vacuum_witness
    (hP0 : g.P0 ≠ 0) :
    ∃ p : A,
      p ≠ 0 ∧
      g.susyHamiltonian * p = 0 ∧
      cyclicSupercharge g * p = 0 := by
  use g.P0
  exact ⟨hP0,
         susyHamiltonian_defect_annihilation_right g,
         cyclicSupercharge_defect_annihilation_right g⟩


end ToeplitzCuntzThreeCyclicSuperchargeBridge
