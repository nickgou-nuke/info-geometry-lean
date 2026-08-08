import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge

3-ary Toeplitz-Cuntz algebra ℰ₃ over a non-commutative algebra A:
  V₁* V₁ = 1, V₂* V₂ = 1, V₃* V₃ = 1,
  V_i* V_j = 0 (i ≠ j).

Defect projection P₀ = 1 - P₁ - P₂ - P₃ where P_i = V_i V_i*.
Proves P₀² = P₀, P₀* = P₀, P₁ + P₂ + P₃ + P₀ = 1, vacuum annihilators, and conditional non-triviality.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge

/-- Structure defining generators and core relations of 3-ary Toeplitz-Cuntz algebra ℰ₃. -/
structure ToeplitzCuntzThreeGenerators (A : Type*) [Ring A] [StarRing A] where
  V1 : A
  V2 : A
  V3 : A
  V1_isometry : star V1 * V1 = 1
  V2_isometry : star V2 * V2 = 1
  V3_isometry : star V3 * V3 = 1
  V1_V2_ortho : star V1 * V2 = 0
  V2_V1_ortho : star V2 * V1 = 0
  V2_V3_ortho : star V2 * V3 = 0
  V3_V2_ortho : star V3 * V2 = 0
  V1_V3_ortho : star V1 * V3 = 0
  V3_V1_ortho : star V3 * V1 = 0

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

/-- Range projector P₁ = V₁ V₁*. -/
def ToeplitzCuntzThreeGenerators.P1 : A := g.V1 * star g.V1

/-- Range projector P₂ = V₂ V₂*. -/
def ToeplitzCuntzThreeGenerators.P2 : A := g.V2 * star g.V2

/-- Range projector P₃ = V₃ V₃*. -/
def ToeplitzCuntzThreeGenerators.P3 : A := g.V3 * star g.V3

/-- Defect projection P₀ = 1 - P₁ - P₂ - P₃. -/
def ToeplitzCuntzThreeGenerators.P0 : A := 1 - g.P1 - g.P2 - g.P3

/-- SUSY Hamiltonian H = P₁ + P₂ + P₃ = 1 - P₀. -/
def ToeplitzCuntzThreeGenerators.susyHamiltonian : A :=
  g.P1 + g.P2 + g.P3

theorem p1_idempotent : g.P1 * g.P1 = g.P1 := by
  dsimp [ToeplitzCuntzThreeGenerators.P1]
  have h1 : g.V1 * star g.V1 * (g.V1 * star g.V1) = g.V1 * (star g.V1 * g.V1) * star g.V1 := by noncomm_ring
  rw [h1, g.V1_isometry, mul_one]

theorem p2_idempotent : g.P2 * g.P2 = g.P2 := by
  dsimp [ToeplitzCuntzThreeGenerators.P2]
  have h1 : g.V2 * star g.V2 * (g.V2 * star g.V2) = g.V2 * (star g.V2 * g.V2) * star g.V2 := by noncomm_ring
  rw [h1, g.V2_isometry, mul_one]

theorem p3_idempotent : g.P3 * g.P3 = g.P3 := by
  dsimp [ToeplitzCuntzThreeGenerators.P3]
  have h1 : g.V3 * star g.V3 * (g.V3 * star g.V3) = g.V3 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
  rw [h1, g.V3_isometry, mul_one]

theorem p1_star : star g.P1 = g.P1 := by
  dsimp [ToeplitzCuntzThreeGenerators.P1]
  simp [star_mul, star_star]

theorem p2_star : star g.P2 = g.P2 := by
  dsimp [ToeplitzCuntzThreeGenerators.P2]
  simp [star_mul, star_star]

theorem p3_star : star g.P3 = g.P3 := by
  dsimp [ToeplitzCuntzThreeGenerators.P3]
  simp [star_mul, star_star]

theorem p1_p2_ortho : g.P1 * g.P2 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P2]
  have h1 : g.V1 * star g.V1 * (g.V2 * star g.V2) = g.V1 * (star g.V1 * g.V2) * star g.V2 := by noncomm_ring
  rw [h1, g.V1_V2_ortho, mul_zero, zero_mul]

theorem p2_p1_ortho : g.P2 * g.P1 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P2]
  have h1 : g.V2 * star g.V2 * (g.V1 * star g.V1) = g.V2 * (star g.V2 * g.V1) * star g.V1 := by noncomm_ring
  rw [h1, g.V2_V1_ortho, mul_zero, zero_mul]

theorem p2_p3_ortho : g.P2 * g.P3 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P2, ToeplitzCuntzThreeGenerators.P3]
  have h1 : g.V2 * star g.V2 * (g.V3 * star g.V3) = g.V2 * (star g.V2 * g.V3) * star g.V3 := by noncomm_ring
  rw [h1, g.V2_V3_ortho, mul_zero, zero_mul]

theorem p3_p2_ortho : g.P3 * g.P2 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P2, ToeplitzCuntzThreeGenerators.P3]
  have h1 : g.V3 * star g.V3 * (g.V2 * star g.V2) = g.V3 * (star g.V3 * g.V2) * star g.V2 := by noncomm_ring
  rw [h1, g.V3_V2_ortho, mul_zero, zero_mul]

theorem p1_p3_ortho : g.P1 * g.P3 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P3]
  have h1 : g.V1 * star g.V1 * (g.V3 * star g.V3) = g.V1 * (star g.V1 * g.V3) * star g.V3 := by noncomm_ring
  rw [h1, g.V1_V3_ortho, mul_zero, zero_mul]

theorem p3_p1_ortho : g.P3 * g.P1 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P3]
  have h1 : g.V3 * star g.V3 * (g.V1 * star g.V1) = g.V3 * (star g.V3 * g.V1) * star g.V1 := by noncomm_ring
  rw [h1, g.V3_V1_ortho, mul_zero, zero_mul]

/-- Defect projector P₀ is idempotent: P₀² = P₀. -/
theorem defectProjection_sq : g.P0 * g.P0 = g.P0 := by
  have hp1 := p1_idempotent g
  have hp2 := p2_idempotent g
  have hp3 := p3_idempotent g
  have h12 := p1_p2_ortho g
  have h21 := p2_p1_ortho g
  have h23 := p2_p3_ortho g
  have h32 := p3_p2_ortho g
  have h13 := p1_p3_ortho g
  have h31 := p3_p1_ortho g
  dsimp [ToeplitzCuntzThreeGenerators.P0]
  calc (1 - g.P1 - g.P2 - g.P3) * (1 - g.P1 - g.P2 - g.P3)
      = 1 - g.P1 - g.P2 - g.P3 - g.P1 + g.P1 * g.P1 + g.P1 * g.P2 + g.P1 * g.P3
        - g.P2 + g.P2 * g.P1 + g.P2 * g.P2 + g.P2 * g.P3
        - g.P3 + g.P3 * g.P1 + g.P3 * g.P2 + g.P3 * g.P3 := by noncomm_ring
    _ = 1 - g.P1 - g.P2 - g.P3 - g.P1 + g.P1 + 0 + 0
        - g.P2 + 0 + g.P2 + 0
        - g.P3 + 0 + 0 + g.P3 := by rw [hp1, hp2, hp3, h12, h21, h23, h32, h13, h31]
    _ = 1 - g.P1 - g.P2 - g.P3 := by noncomm_ring

/-- Defect projector P₀ is self-adjoint: P₀* = P₀. -/
theorem defectProjection_star : star g.P0 = g.P0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P0]
  simp [p1_star g, p2_star g, p3_star g]

/-- Resolution of identity: P₁ + P₂ + P₃ + P₀ = 1. -/
theorem toeplitzCuntz3_resolution : g.P1 + g.P2 + g.P3 + g.P0 = 1 := by
  dsimp [ToeplitzCuntzThreeGenerators.P0]
  noncomm_ring

/-- Orthogonality lemma P₁ P₀ = 0. -/
theorem p1_p0_ortho : g.P1 * g.P0 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P0, ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P2, ToeplitzCuntzThreeGenerators.P3]
  have h11 := g.V1_isometry
  have h12 := g.V1_V2_ortho
  have h13 := g.V1_V3_ortho
  have h : g.V1 * star g.V1 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) =
           g.V1 * star g.V1 - g.V1 * (star g.V1 * g.V1) * star g.V1 - g.V1 * (star g.V1 * g.V2) * star g.V2 - g.V1 * (star g.V1 * g.V3) * star g.V3 := by noncomm_ring
  rw [h, h11, h12, h13]
  noncomm_ring

/-- Orthogonality lemma P₂ P₀ = 0. -/
theorem p2_p0_ortho : g.P2 * g.P0 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P0, ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P2, ToeplitzCuntzThreeGenerators.P3]
  have h21 := g.V2_V1_ortho
  have h22 := g.V2_isometry
  have h23 := g.V2_V3_ortho
  have h : g.V2 * star g.V2 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) =
           g.V2 * star g.V2 - g.V2 * (star g.V2 * g.V1) * star g.V1 - g.V2 * (star g.V2 * g.V2) * star g.V2 - g.V2 * (star g.V2 * g.V3) * star g.V3 := by noncomm_ring
  rw [h, h21, h22, h23]
  noncomm_ring

/-- Orthogonality lemma P₃ P₀ = 0. -/
theorem p3_p0_ortho : g.P3 * g.P0 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P0, ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P2, ToeplitzCuntzThreeGenerators.P3]
  have h31 := g.V3_V1_ortho
  have h32 := g.V3_V2_ortho
  have h33 := g.V3_isometry
  have h : g.V3 * star g.V3 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) =
           g.V3 * star g.V3 - g.V3 * (star g.V3 * g.V1) * star g.V1 - g.V3 * (star g.V3 * g.V2) * star g.V2 - g.V3 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
  rw [h, h31, h32, h33]
  noncomm_ring

/-- Orthogonality lemma P₀ P₁ = 0. -/
theorem p0_p1_ortho : g.P0 * g.P1 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P0, ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P2, ToeplitzCuntzThreeGenerators.P3]
  have h11 := g.V1_isometry
  have h21 := g.V2_V1_ortho
  have h31 := g.V3_V1_ortho
  have h : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V1 * star g.V1) =
           g.V1 * star g.V1 - g.V1 * (star g.V1 * g.V1) * star g.V1 - g.V2 * (star g.V2 * g.V1) * star g.V1 - g.V3 * (star g.V3 * g.V1) * star g.V1 := by noncomm_ring
  rw [h, h11, h21, h31]
  noncomm_ring

/-- Orthogonality lemma P₀ P₂ = 0. -/
theorem p0_p2_ortho : g.P0 * g.P2 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P0, ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P2, ToeplitzCuntzThreeGenerators.P3]
  have h12 := g.V1_V2_ortho
  have h22 := g.V2_isometry
  have h32 := g.V3_V2_ortho
  have h : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V2 * star g.V2) =
           g.V2 * star g.V2 - g.V1 * (star g.V1 * g.V2) * star g.V2 - g.V2 * (star g.V2 * g.V2) * star g.V2 - g.V3 * (star g.V3 * g.V2) * star g.V2 := by noncomm_ring
  rw [h, h12, h22, h32]
  noncomm_ring

/-- Orthogonality lemma P₀ P₃ = 0. -/
theorem p0_p3_ortho : g.P0 * g.P3 = 0 := by
  dsimp [ToeplitzCuntzThreeGenerators.P0, ToeplitzCuntzThreeGenerators.P1, ToeplitzCuntzThreeGenerators.P2, ToeplitzCuntzThreeGenerators.P3]
  have h13 := g.V1_V3_ortho
  have h23 := g.V2_V3_ortho
  have h33 := g.V3_isometry
  have h : (1 - g.V1 * star g.V1 - g.V2 * star g.V2 - g.V3 * star g.V3) * (g.V3 * star g.V3) =
           g.V3 * star g.V3 - g.V1 * (star g.V1 * g.V3) * star g.V3 - g.V2 * (star g.V2 * g.V3) * star g.V3 - g.V3 * (star g.V3 * g.V3) * star g.V3 := by noncomm_ring
  rw [h, h13, h23, h33]
  noncomm_ring

theorem susyHamiltonian_eq_one_sub_defect : g.susyHamiltonian = 1 - g.P0 := by
  dsimp [ToeplitzCuntzThreeGenerators.susyHamiltonian, ToeplitzCuntzThreeGenerators.P0]
  noncomm_ring

theorem susyHamiltonian_defect_annihilation_right : g.susyHamiltonian * g.P0 = 0 := by
  calc
    g.susyHamiltonian * g.P0 = g.P1 * g.P0 + g.P2 * g.P0 + g.P3 * g.P0 := by
      dsimp [ToeplitzCuntzThreeGenerators.susyHamiltonian]
      noncomm_ring
    _ = 0 + 0 + 0 := by
      rw [p1_p0_ortho g, p2_p0_ortho g, p3_p0_ortho g]
    _ = 0 := by abel

theorem susyHamiltonian_defect_annihilation_left : g.P0 * g.susyHamiltonian = 0 := by
  calc
    g.P0 * g.susyHamiltonian = g.P0 * g.P1 + g.P0 * g.P2 + g.P0 * g.P3 := by
      dsimp [ToeplitzCuntzThreeGenerators.susyHamiltonian]
      noncomm_ring
    _ = 0 + 0 + 0 := by
      rw [p0_p1_ortho g, p0_p2_ortho g, p0_p3_ortho g]
    _ = 0 := by abel

/-- A nonzero defect prevents the excitation Hamiltonian from being the unit. -/
theorem nontrivial_vacuum_property (hP0 : g.P0 ≠ 0) : g.susyHamiltonian ≠ 1 := by
  intro hH
  apply hP0
  rw [susyHamiltonian_eq_one_sub_defect g] at hH
  calc
    g.P0 = 1 - (1 - g.P0) := by symm; exact sub_sub_cancel 1 g.P0
    _ = 1 - 1 := by rw [hH]
    _ = 0 := sub_self 1

end InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
