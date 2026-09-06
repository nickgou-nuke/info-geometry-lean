import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# Paperwall Holography Superalgebra

This file formalizes the algebraic synthesis of the Cuntz algebra `O₂`
(representing the Cantor-like fractal boundary of LogCFT holography)
and the chiral glide reflections of the 2D boundary "paperwall" symmetry.

By binding the natural fermionic operator contained within the Cuntz algebra
to the unitary glide reflection, we generate a canonical topological
N=2 Supersymmetry (SUSY) superalgebra with a flat-band Hamiltonian (`H = 1`).
-/

/--
An abstract `StarRing` equipped with the generators of the Paperwall Holography.
It contains the Cuntz `O₂` generators (`S₁`, `S₂`) and the Glide reflection (`G`).
-/
class PaperwallAlgebra (R : Type) [Ring R] [StarRing R] where
  S₁ : R
  S₂ : R
  G : R
  -- Cuntz isometry relations
  isom_S₁ : star S₁ * S₁ = 1
  isom_S₂ : star S₂ * S₂ = 1
  -- Cuntz orthogonality
  ortho_S₁S₂ : star S₁ * S₂ = 0
  ortho_S₂S₁ : star S₂ * S₁ = 0
  -- Cuntz completeness
  complete_S : S₁ * star S₁ + S₂ * star S₂ = 1
  
  -- Glide unitary relations
  glide_uni₁ : G * star G = 1
  glide_uni₂ : star G * G = 1
  
  -- Glide commutativity with Cuntz isometries
  -- The geometric glide commutes with the internal/holographic indices
  comm_G_S₁ : G * S₁ = S₁ * G
  comm_G_S₁_star : G * star S₁ = star S₁ * G
  comm_G_S₂ : G * S₂ = S₂ * G
  comm_G_S₂_star : G * star S₂ = star S₂ * G
  
  comm_G_star_S₁ : star G * S₁ = S₁ * star G
  comm_G_star_S₁_star : star G * star S₁ = star S₁ * star G
  comm_G_star_S₂ : star G * S₂ = S₂ * star G
  comm_G_star_S₂_star : star G * star S₂ = star S₂ * star G

namespace PaperwallAlgebra

variable {R : Type} [Ring R] [StarRing R] [PaperwallAlgebra R]

-- ══════════════════════════════════════════════════════════════════════════════
-- §1. Cuntz Algebra Canonical Fermion
-- ══════════════════════════════════════════════════════════════════════════════

/-- The canonical fermion lowering operator constructed from Cuntz isometries. -/
def c : R := S₂ * star S₁

/-- The fermion creation operator. -/
lemma star_c : star (c (R := R)) = S₁ * star S₂ := by
  dsimp [c]
  rw [star_mul, star_star]

/-- Pauli exclusion: The fermion is strictly nilpotent. -/
theorem c_sq_zero : (c (R := R)) * c = 0 := by
  dsimp [c]
  -- c * c = S₂ * S₁* * S₂ * S₁* = S₂ * (S₁* * S₂) * S₁*
  calc
    (S₂ * star S₁) * (S₂ * star S₁)
      = S₂ * (star S₁ * S₂) * star S₁ := by
        -- Reassociate
        rw [mul_assoc S₂ (star S₁) (S₂ * star S₁), ← mul_assoc (star S₁) S₂ (star S₁)]
    _ = S₂ * 0 * star S₁ := by rw [ortho_S₁S₂]
    _ = 0 := by rw [mul_zero, zero_mul]

/-- The canonical fermion anti-commutator {c, c†} = 1. -/
theorem c_anticomm : (c (R := R)) * star c + star c * c = 1 := by
  rw [star_c]
  dsimp [c]
  calc
    (S₂ * star S₁) * (S₁ * star S₂) + (S₁ * star S₂) * (S₂ * star S₁)
      = S₂ * (star S₁ * S₁) * star S₂ + S₁ * (star S₂ * S₂) * star S₁ := by
        rw [mul_assoc S₂ (star S₁) (S₁ * star S₂), ← mul_assoc (star S₁) S₁ (star S₂)]
        rw [mul_assoc S₁ (star S₂) (S₂ * star S₁), ← mul_assoc (star S₂) S₂ (star S₁)]
    _ = S₂ * 1 * star S₂ + S₁ * 1 * star S₁ := by rw [isom_S₁, isom_S₂]
    _ = S₂ * star S₂ + S₁ * star S₁ := by rw [mul_one, mul_one]
    _ = S₁ * star S₁ + S₂ * star S₂ := by rw [add_comm]
    _ = 1 := complete_S

-- ══════════════════════════════════════════════════════════════════════════════
-- §2. Paperwall SUSY Construction via Chiral Glide Reflections
-- ══════════════════════════════════════════════════════════════════════════════

/-- The SUSY supercharge binds the Cuntz fermion to the chiral glide reflection. -/
def Q : R := c * G

/-- The adjoint of the supercharge. -/
lemma star_Q : star (Q (R := R)) = star G * star c := by
  dsimp [Q]
  rw [star_mul]

/-- The supercharge commutes with G/G* in specific ways, we need to pass G through c*. -/
lemma star_c_comm_G_star : star (c (R := R)) * star G = star G * star c := by
  rw [star_c]
  calc
    (S₁ * star S₂) * star G
      = S₁ * (star S₂ * star G) := by rw [mul_assoc]
    _ = S₁ * (star G * star S₂) := by rw [comm_G_star_S₂_star]
    _ = (S₁ * star G) * star S₂ := by rw [← mul_assoc]
    _ = (star G * S₁) * star S₂ := by rw [comm_G_star_S₁]
    _ = star G * (S₁ * star S₂) := by rw [mul_assoc]

/-- Supercharge nilpotency (Q² = 0). -/
theorem Q_sq_zero : (Q (R := R)) * Q = 0 := by
  dsimp [Q]
  calc
    (c * G) * (c * G)
      = c * (G * c) * G := by rw [mul_assoc c G (c * G), ← mul_assoc G c G]
    _ = c * (c * G) * G := by
        -- G * c = G * (S₂ * S₁*) = S₂ * G * S₁* = S₂ * S₁* * G = c * G
        have hGc : G * c = c * G := by
          dsimp [c]
          calc
            G * (S₂ * star S₁) = (G * S₂) * star S₁ := by rw [← mul_assoc]
            _ = (S₂ * G) * star S₁ := by rw [comm_G_S₂]
            _ = S₂ * (G * star S₁) := by rw [mul_assoc]
            _ = S₂ * (star S₁ * G) := by rw [comm_G_S₁_star]
            _ = (S₂ * star S₁) * G := by rw [← mul_assoc]
        rw [hGc]
    _ = (c * c) * (G * G) := by
        rw [← mul_assoc c (c * G) G]
        have h : c * (c * G) = (c * c) * G := mul_assoc c c G
        rw [h, mul_assoc]
    _ = 0 * (G * G) := by rw [c_sq_zero]
    _ = 0 := by rw [zero_mul]

/-- The exact flat-band topological SUSY Hamiltonian: {Q, Q†} = 1. -/
theorem H_susy_eq_one : (Q (R := R)) * star Q + star Q * Q = 1 := by
  rw [star_Q]
  dsimp [Q]
  calc
    (c * G) * (star G * star c) + (star G * star c) * (c * G)
      = c * (G * star G) * star c + star G * (star c * c) * G := by
        rw [mul_assoc c G (star G * star c), ← mul_assoc G (star G) (star c)]
        rw [mul_assoc (star G) (star c) (c * G), ← mul_assoc (star c) c G]
    _ = c * 1 * star c + star G * (star c * c) * G := by rw [glide_uni₁]
    _ = c * star c + star G * (star c * c) * G := by rw [mul_one]
    _ = c * star c + (star c * c) * (star G * G) := by
        -- We must pass star G past (star c * c)
        -- Since star G commutes with S₁ and S₂, it commutes with c and star c.
        have hGsc : star G * star c = star c * star G := by
          rw [star_c_comm_G_star]
        have hGc : star G * c = c * star G := by
          dsimp [c]
          calc
            star G * (S₂ * star S₁) = (star G * S₂) * star S₁ := by rw [← mul_assoc]
            _ = (S₂ * star G) * star S₁ := by rw [comm_G_star_S₂]
            _ = S₂ * (star G * star S₁) := by rw [mul_assoc]
            _ = S₂ * (star S₁ * star G) := by rw [comm_G_star_S₁_star]
            _ = (S₂ * star S₁) * star G := by rw [← mul_assoc]
        calc
          star G * (star c * c) * G
            = (star G * star c) * c * G := by rw [← mul_assoc]
          _ = (star c * star G) * c * G := by rw [hGsc]
          _ = star c * (star G * c) * G := by rw [mul_assoc]
          _ = star c * (c * star G) * G := by rw [hGc]
          _ = (star c * c) * star G * G := by rw [← mul_assoc]
          _ = (star c * c) * (star G * G) := by rw [mul_assoc]
    _ = c * star c + (star c * c) * 1 := by rw [glide_uni₂]
    _ = c * star c + star c * c := by rw [mul_one]
    _ = 1 := c_anticomm

end PaperwallAlgebra
