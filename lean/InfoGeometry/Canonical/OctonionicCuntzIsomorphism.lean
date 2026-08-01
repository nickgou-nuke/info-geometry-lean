import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.ChiralConeOctonionicBridge
import InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

/-!
# OctonionicCuntzIsomorphism

This module records the projector-level correspondence between:
1. the Toeplitz-Cuntz projector relations for `V₁`, `V₂`;
2. the scalar Weyl/lightcone projectors `½ (1 ± u)` for an involutive unit `u`.

No algebra isomorphism is asserted here.  The file only packages the shared
idempotence, orthogonality, and resolution identities.
-/

namespace InfoGeometry.Canonical

variable {R : Type*} [Ring R] [StarRing R]

/-- OctonionicCuntz structure: Cuntz generators V₁, V₂ realized as Weyl projectors on the split octonion lightcone.
    Given a hyperbolic unit u with u² = 1, we define:
      P₁ := lightconePlus(u) = ½(1 + u)
      P₂ := lightconeMinus(u) = ½(1 - u)
    These satisfy the Cuntz projector axioms: P₁² = P₁, P₂² = P₂, P₁P₂ = 0, P₁ + P₂ = 1. -/
structure OctonionicCuntzGenerators (R : Type*) [Ring R] [StarRing R] where
  u : R
  hu : u * u = 1
  u_star : star u = u  -- u is self-adjoint (hyperbolic unit in split octonions)

namespace OctonionicCuntzGenerators

/-- P₁ := lightconePlus(u) = ½(1 + u) -/
def P1 (g : OctonionicCuntzGenerators R) : R :=
  (1 / 2 : R) * (1 + g.u)

/-- P₂ := lightconeMinus(u) = ½(1 - u) -/
def P2 (g : OctonionicCuntzGenerators R) : R :=
  (1 / 2 : R) * (1 - g.u)

/-- Vacuum defect projector P₀ = 1 - P₁ - P₂ (automatically 0 for pure Cuntz) -/
def P0 (g : OctonionicCuntzGenerators R) : R :=
  1 - P1 g - P2 g

/-- Q₊ = √P₁ (chiral supercharge) -/
def QPlus (g : OctonionicCuntzGenerators R) : R := P1 g

/-- Q₋ = √P₂ (chiral supercharge) -/
def QMinus (g : OctonionicCuntzGenerators R) : R := P2 g

end OctonionicCuntzGenerators

/-- **Theorem 1**: P₁ is idempotent (P₁² = P₁) using Weyl projector idempotency. -/
theorem octonionic_cuntz_p1_idempotent {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) : P1 g * P1 g = P1 g := by
  dsimp [OctonionicCuntzGenerators.P1]
  have h₁ : g.u * g.u = 1 := g.hu
  have h₂ : (1 / 2 : R) * (1 + g.u) * ((1 / 2 : R) * (1 + g.u)) = (1 / 2 : R) * (1 + g.u) := by
    calc
      (1 / 2 : R) * (1 + g.u) * ((1 / 2 : R) * (1 + g.u))
          = (1 / 4 : R) * (1 + g.u) * (1 + g.u) := by ring
      _ = (1 / 4 : R) * (1 + 2 * g.u + g.u * g.u) := by ring
      _ = (1 / 4 : R) * (1 + 2 * g.u + 1) := by rw [g.hu]
      _ = (1 / 2 : R) * (1 + g.u) := by ring
  exact h₂

/-- **Theorem 2**: P₂ is idempotent (P₂² = P₂). -/
theorem octonionic_cuntz_p2_idempotent {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) : P2 g * P2 g = P2 g := by
  dsimp [OctonionicCuntzGenerators.P2]
  have h₁ : g.u * g.u = 1 := g.hu
  have h₂ : (1 / 2 : R) * (1 - g.u) * ((1 / 2 : R) * (1 - g.u)) = (1 / 2 : R) * (1 - g.u) := by
    calc
      (1 / 2 : R) * (1 - g.u) * ((1 / 2 : R) * (1 - g.u))
          = (1 / 4 : R) * (1 - g.u) * (1 - g.u) := by ring
      _ = (1 / 4 : R) * (1 - 2 * g.u + g.u * g.u) := by ring
      _ = (1 / 4 : R) * (1 - 2 * g.u + 1) := by rw [g.hu]
      _ = (1 / 2 : R) * (1 - g.u) := by ring
  exact h₂

/-- **Theorem 3**: P₁ and P₂ are orthogonal (P₁P₂ = 0). -/
theorem octonionic_cuntz_p1_p2_orthogonal {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) : P1 g * P2 g = 0 := by
  dsimp [OctonionicCuntzGenerators.P1, OctonionicCuntzGenerators.P2]
  have h₁ : g.u * g.u = 1 := g.hu
  calc
    ((1 / 2 : R) * (1 + g.u)) * ((1 / 2 : R) * (1 - g.u))
        = (1 / 4 : R) * (1 - g.u * g.u) := by ring
    _ = (1 / 4 : R) * (1 - 1) := by rw [g.hu]
    _ = 0 := by ring

/-- **Theorem 4**: P₂ and P₁ are orthogonal (P₂P₁ = 0). -/
theorem octonionic_cuntz_p2_p1_orthogonal {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) : P2 g * P1 g = 0 := by
  dsimp [OctonionicCuntzGenerators.P1, OctonionicCuntzGenerators.P2]
  have h₁ : g.u * g.u = 1 := g.hu
  calc
    ((1 / 2 : R) * (1 - g.u)) * ((1 / 2 : R) * (1 + g.u))
        = (1 / 4 : R) * (1 - g.u * g.u) := by ring
    _ = (1 / 4 : R) * (1 - 1) := by rw [g.hu]
    _ = 0 := by ring

/-- **Theorem 5**: Resolution of identity P₁ + P₂ = 1. -/
theorem octonionic_cuntz_resolution {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) : P1 g + P2 g = 1 := by
  dsimp [OctonionicCuntzGenerators.P1, OctonionicCuntzGenerators.P2]
  ring

/-- **Theorem 6**: P₀ = 1 - P₁ - P₂ = 0 (pure Cuntz, no defect). -/
theorem octonionic_cuntz_p0_zero {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) : P0 g = 0 := by
  dsimp [OctonionicCuntzGenerators.P0, OctonionicCuntzGenerators.P1, OctonionicCuntzGenerators.P2]
  <;>
  (try ring_nf) <;>
  (try simp_all) <;>
  (try ring) <;>
  (try linarith)

/-- **Theorem 7**: Cuntz resolution of identity P₁ + P₂ + P₀ = 1. -/
theorem octonionic_cuntz_resolution_full {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) : P1 g + P2 g + P0 g = 1 := by
  dsimp [OctonionicCuntzGenerators.P0, OctonionicCuntzGenerators.P1, OctonionicCuntzGenerators.P2]
  <;> ring

/-- **Theorem 8**: P₁ is self-adjoint (P₁* = P₁). -/
theorem octonionic_cuntz_p1_star {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) : star (P1 g) = P1 g := by
  dsimp [OctonionicCuntzGenerators.P1]
  simp [g.u_star, star_add, star_one, star_mul, star_sub]
  <;> ring_nf
  <;> simp_all [g.u_star]
  <;> aesop

/-- **Theorem 9**: P₂ is self-adjoint (P₂* = P₂). -/
theorem octonionic_cuntz_p2_star {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) : star (P2 g) = P2 g := by
  dsimp [OctonionicCuntzGenerators.P2]
  simp [g.u_star, star_add, star_one, star_mul, star_sub]
  <;> ring_nf
  <;> simp_all [g.u_star]
  <;> aesop

/-- **Master Synthesis Theorem**: All Cuntz axioms from split octonion lightcone projectors. -/
theorem octonionic_cuntz_master_synthesis {R : Type*} [Ring R] [StarRing R]
    (g : OctonionicCuntzGenerators R) :
    (P1 g * P1 g = P1 g) ∧
    (P2 g * P2 g = P2 g) ∧
    (P1 g * P2 g = 0) ∧
    (P2 g * P1 g = 0) ∧
    (P1 g + P2 g = 1) ∧
    (P0 g = 0) ∧
    (star (P1 g) = P1 g) ∧
    (star (P2 g) = P2 g) := by
  refine' ⟨
    octonionic_cuntz_p1_idempotent g,
    octonionic_cuntz_p2_idempotent g,
    octonionic_cuntz_p1_p2_orthogonal g,
    octonionic_cuntz_p2_p1_orthogonal g,
    octonionic_cuntz_resolution g,
    octonionic_cuntz_p0_zero g,
    octonionic_cuntz_p1_star g,
    octonionic_cuntz_p2_star g
  ⟩

end InfoGeometry.Canonical
