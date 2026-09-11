import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
import InfoGeometry.Categorical.FibonacciBraiding

/-!
# Toeplitz-Cuntz braid realization bridge

This file separates the genuine braid data from the involutive `S₃` shadow.
The carrier is a non-commutative star ring.  A braid realization supplies
invertible star-compatible generators and a single excitation-sector
commutation law; the cubic charge and full twist are then proved natively.

The Fibonacci matrix transport theorem is deliberately independent of the
Toeplitz realization.  A concrete map from the Fibonacci matrix algebra into a
Toeplitz carrier remains an explicit input rather than an unproved
identification.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeBraidRealizationBridge

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open ToeplitzCuntzThreeGenerators

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

/-- Two-sided star-unitarity in a non-commutative star ring. -/
def StarUnitary (u : A) : Prop :=
  star u * u = 1 ∧ u * star u = 1

/-- A genuine algebraic `B₃` realization on the excitation sector. -/
structure ToeplitzBraidData where
  braid1 : A
  braid2 : A
  artin_relation :
    braid1 * braid2 * braid1 = braid2 * braid1 * braid2
  braid1_star_unitary : StarUnitary braid1
  braid2_star_unitary : StarUnitary braid2
  coxeter_commutes_hamiltonian :
    g.susyHamiltonian * (braid2 * braid1) =
      (braid2 * braid1) * g.susyHamiltonian

/-- The Coxeter word underlying the braided cubic charge. -/
def coxeterWord (D : ToeplitzBraidData g) : A :=
  D.braid2 * D.braid1

/-- The Artin full twist image `(b₂ b₁)³`. -/
def fullTwist (D : ToeplitzBraidData g) : A :=
  coxeterWord g D * coxeterWord g D * coxeterWord g D

/-- The excitation-sector compressed Coxeter word. -/
def braidedCubicSupercharge (D : ToeplitzBraidData g) : A :=
  g.susyHamiltonian * coxeterWord g D * g.susyHamiltonian

theorem susyHamiltonian_sq :
    g.susyHamiltonian * g.susyHamiltonian = g.susyHamiltonian := by
  have hp1 := p1_idempotent g
  have hp2 := p2_idempotent g
  have hp3 := p3_idempotent g
  have h12 := p1_p2_ortho g
  have h21 := p2_p1_ortho g
  have h23 := p2_p3_ortho g
  have h32 := p3_p2_ortho g
  have h13 := p1_p3_ortho g
  have h31 := p3_p1_ortho g
  dsimp [susyHamiltonian]
  calc
    (g.P1 + g.P2 + g.P3) * (g.P1 + g.P2 + g.P3) =
        g.P1 * g.P1 + g.P1 * g.P2 + g.P1 * g.P3
          + g.P2 * g.P1 + g.P2 * g.P2 + g.P2 * g.P3
          + g.P3 * g.P1 + g.P3 * g.P2 + g.P3 * g.P3 := by
            noncomm_ring
    _ = g.P1 + 0 + 0 + 0 + g.P2 + 0 + 0 + 0 + g.P3 := by
      rw [hp1, hp2, hp3, h12, h21, h23, h32, h13, h31]
    _ = g.P1 + g.P2 + g.P3 := by abel

theorem coxeterWord_commutes_hamiltonian (D : ToeplitzBraidData g) :
    g.susyHamiltonian * coxeterWord g D =
      coxeterWord g D * g.susyHamiltonian :=
  D.coxeter_commutes_hamiltonian

theorem fullTwist_commutes_hamiltonian (D : ToeplitzBraidData g) :
    fullTwist g D * g.susyHamiltonian =
      g.susyHamiltonian * fullTwist g D := by
  have h := coxeterWord_commutes_hamiltonian g D
  have h2 : g.susyHamiltonian * coxeterWord g D * coxeterWord g D =
      coxeterWord g D * coxeterWord g D * g.susyHamiltonian := by
    calc
      g.susyHamiltonian * coxeterWord g D * coxeterWord g D =
          (g.susyHamiltonian * coxeterWord g D) * coxeterWord g D := by rfl
      _ = (coxeterWord g D * g.susyHamiltonian) * coxeterWord g D := by rw [h]
      _ = coxeterWord g D * (g.susyHamiltonian * coxeterWord g D) := by
        noncomm_ring
      _ = coxeterWord g D * (coxeterWord g D * g.susyHamiltonian) := by rw [h]
      _ = coxeterWord g D * coxeterWord g D * g.susyHamiltonian := by
        noncomm_ring
  have h3 : g.susyHamiltonian * coxeterWord g D * coxeterWord g D *
      coxeterWord g D =
      coxeterWord g D * coxeterWord g D * coxeterWord g D *
        g.susyHamiltonian := by
    calc
      g.susyHamiltonian * coxeterWord g D * coxeterWord g D * coxeterWord g D =
          (g.susyHamiltonian * coxeterWord g D * coxeterWord g D) *
            coxeterWord g D := by rfl
      _ = (coxeterWord g D * coxeterWord g D * g.susyHamiltonian) *
            coxeterWord g D := by rw [h2]
      _ = coxeterWord g D * coxeterWord g D *
            (g.susyHamiltonian * coxeterWord g D) := by noncomm_ring
      _ = coxeterWord g D * coxeterWord g D *
            (coxeterWord g D * g.susyHamiltonian) := by rw [h]
      _ = coxeterWord g D * coxeterWord g D * coxeterWord g D *
            g.susyHamiltonian := by noncomm_ring
  dsimp [fullTwist]
  calc
    (coxeterWord g D * coxeterWord g D * coxeterWord g D) * g.susyHamiltonian =
        g.susyHamiltonian * (coxeterWord g D * coxeterWord g D * coxeterWord g D) := by
      have h2 : g.susyHamiltonian *
          (coxeterWord g D * coxeterWord g D) =
          (coxeterWord g D * coxeterWord g D) * g.susyHamiltonian := by
        calc
          g.susyHamiltonian * (coxeterWord g D * coxeterWord g D) =
              (g.susyHamiltonian * coxeterWord g D) * coxeterWord g D := by noncomm_ring
          _ = (coxeterWord g D * g.susyHamiltonian) * coxeterWord g D := by rw [h]
          _ = coxeterWord g D * (g.susyHamiltonian * coxeterWord g D) := by noncomm_ring
          _ = coxeterWord g D * (coxeterWord g D * g.susyHamiltonian) := by rw [h]
          _ = (coxeterWord g D * coxeterWord g D) * g.susyHamiltonian := by noncomm_ring
      calc
        (coxeterWord g D * coxeterWord g D * coxeterWord g D) * g.susyHamiltonian =
            (coxeterWord g D * coxeterWord g D) *
              (coxeterWord g D * g.susyHamiltonian) := by noncomm_ring
        _ = (coxeterWord g D * coxeterWord g D) *
              (g.susyHamiltonian * coxeterWord g D) := by rw [h]
        _ = ((coxeterWord g D * coxeterWord g D) * g.susyHamiltonian) *
              coxeterWord g D := by noncomm_ring
        _ = (g.susyHamiltonian *
              (coxeterWord g D * coxeterWord g D)) * coxeterWord g D := by rw [h2]
        _ = g.susyHamiltonian *
              (coxeterWord g D * coxeterWord g D * coxeterWord g D) := by noncomm_ring

theorem braidedCubicSupercharge_eq_hamiltonian_mul (D : ToeplitzBraidData g) :
    braidedCubicSupercharge g D =
      g.susyHamiltonian * coxeterWord g D := by
  have hH := susyHamiltonian_sq g
  have h := coxeterWord_commutes_hamiltonian g D
  dsimp [braidedCubicSupercharge]
  calc
    g.susyHamiltonian * coxeterWord g D * g.susyHamiltonian =
        g.susyHamiltonian * (coxeterWord g D * g.susyHamiltonian) := by
          noncomm_ring
    _ = g.susyHamiltonian * (g.susyHamiltonian * coxeterWord g D) := by
          rw [h]
    _ = (g.susyHamiltonian * g.susyHamiltonian) * coxeterWord g D := by
          noncomm_ring
    _ = g.susyHamiltonian * coxeterWord g D := by rw [hH]

theorem braidedCubicSupercharge_vacuum_annihilation_right
    (D : ToeplitzBraidData g) :
    braidedCubicSupercharge g D * g.P0 = 0 := by
  have hH := susyHamiltonian_defect_annihilation_right g
  dsimp [braidedCubicSupercharge]
  calc
    g.susyHamiltonian * coxeterWord g D * g.susyHamiltonian * g.P0 =
        g.susyHamiltonian * coxeterWord g D *
          (g.susyHamiltonian * g.P0) := by noncomm_ring
    _ = 0 := by rw [hH, mul_zero]

theorem braidedCubicSupercharge_vacuum_annihilation_left
    (D : ToeplitzBraidData g) :
    g.P0 * braidedCubicSupercharge g D = 0 := by
  have hH := susyHamiltonian_defect_annihilation_left g
  dsimp [braidedCubicSupercharge]
  calc
    g.P0 * (g.susyHamiltonian * coxeterWord g D * g.susyHamiltonian) =
        (g.P0 * g.susyHamiltonian) *
          (coxeterWord g D * g.susyHamiltonian) := by noncomm_ring
    _ = 0 := by rw [hH, zero_mul]

theorem braidedCubicSupercharge_cube (D : ToeplitzBraidData g) :
    braidedCubicSupercharge g D * braidedCubicSupercharge g D *
        braidedCubicSupercharge g D =
      fullTwist g D * g.susyHamiltonian := by
  have hH := susyHamiltonian_sq g
  have hC := coxeterWord_commutes_hamiltonian g D
  have hQ := braidedCubicSupercharge_eq_hamiltonian_mul g D
  rw [hQ]
  have h2 : g.susyHamiltonian *
      (coxeterWord g D * coxeterWord g D) =
      (coxeterWord g D * coxeterWord g D) * g.susyHamiltonian := by
    calc
      g.susyHamiltonian * (coxeterWord g D * coxeterWord g D) =
          (g.susyHamiltonian * coxeterWord g D) * coxeterWord g D := by noncomm_ring
      _ = (coxeterWord g D * g.susyHamiltonian) * coxeterWord g D := by rw [hC]
      _ = coxeterWord g D * (g.susyHamiltonian * coxeterWord g D) := by noncomm_ring
      _ = coxeterWord g D * (coxeterWord g D * g.susyHamiltonian) := by rw [hC]
      _ = (coxeterWord g D * coxeterWord g D) * g.susyHamiltonian := by noncomm_ring
  have hpair :
      (g.susyHamiltonian * coxeterWord g D) *
        (g.susyHamiltonian * coxeterWord g D) =
      g.susyHamiltonian * (coxeterWord g D * coxeterWord g D) := by
    calc
      (g.susyHamiltonian * coxeterWord g D) *
          (g.susyHamiltonian * coxeterWord g D) =
          g.susyHamiltonian *
            (coxeterWord g D * g.susyHamiltonian) * coxeterWord g D := by noncomm_ring
      _ = g.susyHamiltonian *
            (g.susyHamiltonian * coxeterWord g D) * coxeterWord g D := by rw [hC.symm]
      _ = g.susyHamiltonian * (g.susyHamiltonian * coxeterWord g D) *
            coxeterWord g D := by rfl
      _ = (g.susyHamiltonian * g.susyHamiltonian) *
            (coxeterWord g D * coxeterWord g D) := by noncomm_ring
      _ = g.susyHamiltonian * (coxeterWord g D * coxeterWord g D) := by
        rw [hH]
  have h3 : g.susyHamiltonian *
      (coxeterWord g D * coxeterWord g D * coxeterWord g D) =
      (coxeterWord g D * coxeterWord g D * coxeterWord g D) *
        g.susyHamiltonian := by
    calc
      g.susyHamiltonian *
          (coxeterWord g D * coxeterWord g D * coxeterWord g D) =
          (g.susyHamiltonian * (coxeterWord g D * coxeterWord g D)) *
            coxeterWord g D := by noncomm_ring
      _ = ((coxeterWord g D * coxeterWord g D) * g.susyHamiltonian) *
            coxeterWord g D := by rw [h2]
      _ = (coxeterWord g D * coxeterWord g D) *
            (g.susyHamiltonian * coxeterWord g D) := by noncomm_ring
      _ = (coxeterWord g D * coxeterWord g D) *
            (coxeterWord g D * g.susyHamiltonian) := by rw [hC]
      _ = (coxeterWord g D * coxeterWord g D * coxeterWord g D) *
            g.susyHamiltonian := by noncomm_ring
  calc
    (g.susyHamiltonian * coxeterWord g D) *
        (g.susyHamiltonian * coxeterWord g D) *
        (g.susyHamiltonian * coxeterWord g D) =
      (g.susyHamiltonian * (coxeterWord g D * coxeterWord g D)) *
        (g.susyHamiltonian * coxeterWord g D) := by rw [hpair]
    _ = g.susyHamiltonian *
        (coxeterWord g D * coxeterWord g D * coxeterWord g D) := by
          calc
            g.susyHamiltonian *
                (coxeterWord g D * coxeterWord g D) *
                (g.susyHamiltonian * coxeterWord g D) =
                g.susyHamiltonian *
                  ((coxeterWord g D * coxeterWord g D) *
                    g.susyHamiltonian) * coxeterWord g D := by noncomm_ring
            _ = g.susyHamiltonian *
                  (g.susyHamiltonian *
                    (coxeterWord g D * coxeterWord g D)) * coxeterWord g D := by
                  rw [h2.symm]
            _ = g.susyHamiltonian *
                  (coxeterWord g D * coxeterWord g D) * coxeterWord g D := by
                  calc
                    g.susyHamiltonian *
                        (g.susyHamiltonian *
                          (coxeterWord g D * coxeterWord g D)) * coxeterWord g D =
                        (g.susyHamiltonian * g.susyHamiltonian) *
                          (coxeterWord g D * coxeterWord g D) * coxeterWord g D := by
                            noncomm_ring
                    _ = g.susyHamiltonian *
                          (coxeterWord g D * coxeterWord g D) * coxeterWord g D := by
                            rw [hH]
            _ = g.susyHamiltonian *
                  (coxeterWord g D * coxeterWord g D * coxeterWord g D) := by
                  noncomm_ring
    _ = fullTwist g D * g.susyHamiltonian := by
          rw [h3]
          rfl

/-- The existing Toeplitz generators give the involutive `S₃` specialization. -/
def toeplitzS3BraidData : ToeplitzBraidData g where
  braid1 := braidGenerator1 g
  braid2 := braidGenerator2 g
  artin_relation := artin_braid_relation g
  braid1_star_unitary := by
    constructor
    · rw [braidGenerator1_star g, braidGenerator1_sq g]
    · rw [braidGenerator1_star g, braidGenerator1_sq g]
  braid2_star_unitary := by
    constructor
    · rw [braidGenerator2_star g, braidGenerator2_sq g]
    · rw [braidGenerator2_star g, braidGenerator2_sq g]
  coxeter_commutes_hamiltonian := by
    have hH := susyHamiltonian_eq_one_sub_defect g
    have hQ0 := cyclicSupercharge_defect_annihilation_right g
    have h0Q := cyclicSupercharge_defect_annihilation_left g
    have hC := coxeterElement_eq_cyclicSupercharge_add_defect g
    have hHQ : g.susyHamiltonian * cyclicSupercharge g = cyclicSupercharge g := by
      calc
        g.susyHamiltonian * cyclicSupercharge g =
            (1 - g.P0) * cyclicSupercharge g := by rw [hH]
        _ = cyclicSupercharge g - g.P0 * cyclicSupercharge g := by
          simp only [sub_mul, one_mul]
        _ = cyclicSupercharge g := by rw [h0Q, sub_zero]
    have hQH : cyclicSupercharge g * g.susyHamiltonian = cyclicSupercharge g := by
      calc
        cyclicSupercharge g * g.susyHamiltonian =
            cyclicSupercharge g * (1 - g.P0) := by rw [hH]
        _ = cyclicSupercharge g - cyclicSupercharge g * g.P0 := by
          simp only [mul_sub, mul_one]
        _ = cyclicSupercharge g := by rw [hQ0, sub_zero]
    rw [show braidGenerator2 g * braidGenerator1 g = coxeterElement g from rfl, hC]
    calc
      g.susyHamiltonian * (cyclicSupercharge g + g.P0) =
          g.susyHamiltonian * cyclicSupercharge g +
            g.susyHamiltonian * g.P0 := by rw [mul_add]
      _ = cyclicSupercharge g + 0 := by
        rw [hHQ, susyHamiltonian_defect_annihilation_right g]
      _ = cyclicSupercharge g * g.susyHamiltonian + 0 := by rw [hQH]
      _ = cyclicSupercharge g * g.susyHamiltonian + g.P0 * g.susyHamiltonian := by
        rw [susyHamiltonian_defect_annihilation_left g]
      _ = (cyclicSupercharge g + g.P0) * g.susyHamiltonian := by rw [add_mul]

theorem toeplitzS3BraidData_braid_squares :
    (toeplitzS3BraidData g).braid1 * (toeplitzS3BraidData g).braid1 = 1 ∧
      (toeplitzS3BraidData g).braid2 * (toeplitzS3BraidData g).braid2 = 1 := by
  exact ⟨braidGenerator1_sq g, braidGenerator2_sq g⟩

theorem toeplitzS3BraidData_cubic_closure :
    braidedCubicSupercharge g (toeplitzS3BraidData g) *
        braidedCubicSupercharge g (toeplitzS3BraidData g) *
        braidedCubicSupercharge g (toeplitzS3BraidData g) =
      fullTwist g (toeplitzS3BraidData g) * g.susyHamiltonian := by
  exact braidedCubicSupercharge_cube g (toeplitzS3BraidData g)

variable [Algebra ℂ A]

theorem map_fibonacci_artin_relation
    (φ : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] A)
    (R B : Matrix (Fin 2) (Fin 2) ℂ)
    (hArtin : R * B * R = B * R * B) :
    φ R * φ B * φ R = φ B * φ R * φ B := by
  simpa only [map_mul] using congrArg φ hArtin

end InfoGeometry.Canonical.ToeplitzCuntzThreeBraidRealizationBridge
