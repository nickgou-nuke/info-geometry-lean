/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Track 2, Order 28: Yoshizawa Gradient Flows & Singular Information Geometry
# Formalizing the Monograph in `[Ring B]` (arXiv:2608.21152 [math.DS], 2026)

This module formalizes the six core structural bridges between Shintaro Yoshizawa's
*“Information Geometry of Gradient Flows”* (`arXiv:2608.21152`) and the non-commutative
operator architecture over an arbitrary associative ring `[Ring B]`:

1. **Brockett–Bloch–Ratiu Double-Bracket Flows (Bridge 1):**
   `brockettIrrotational J Φ = [Φ, [Φ, J]] = 4 • (V * J)` identically balances twice
   the Souriau rotational Coriolis precession `2 • [Σ, Φ] = 4 • (V * J)`.
2. **Indefinite / Singular Dual Flatness (Bridge 2):**
   The split-signature pseudo-Hessian metric `Φ² = +V`, `J² = -V`, `{Φ, J} = 0` obeys
   the universal Amari `α`-connection curvature law `(2 ∇^(α))²(Z) = (1 - α²) • (V * Z)`,
   proving dual flatness (`(1 - (±1)²) = 0`) at `α = ±1`.
3. **Sheet Gramians & 4-Way Bott Diamond (Bridge 3):**
   Log-determinant factorization `1 - V = (1 - Q_+)(1 - Q_-)` and the 4-way Bott diamond
   `(1 - V)(1 + V) = (1 - Σ)(1 + Σ) = (1 - J²)(1 + J²) = (1 - Φ²)(1 + Φ²) = 1 - V²`.
4. **Elliptic Moduli & Seiberg–Witten Monodromy (Bridge 4):**
   The 3-point partition of unity `1 = P₁ + P₀ + P₂` resolves boundary singularities;
   transiting local quasi-dualities across `P₀` generates contact-grade monodromy `[N₁₀, N₀₂] = N₁₂`.
5. **Kirillov Coadjoint Invariance & Souriau Thermodynamics (Bridge 5):**
   Souriau's rotational drift `[Ω, ρ]` on a coadjoint orbit has vanishing trace pairing
   `τ([Ω, ρ] * M) = 0` with every centralizer element `M ∈ Z(ρ)`.
6. **Singular Boundary Jordan Cells & Tripotent Quintic Isogeny (Bridge 6):**
   Logarithmic Jordan cells `T = P + N` with `(T - P)² = 0` satisfy `T² - T = N`, and
   every tripotent `H = P₁ - P₂` satisfies the universal quintic `ad_H⁵ - 5 ad_H³ + 4 ad_H = 0`
   locked by the `(ℤ/24ℤ)×` cyclotomic Galois involution `u² = 1`.

## Three-Bucket Audit Map
- **BUCKET 1 (Proved Finite/Algebraic Identities over `[Ring B]`)**:
  `souriau_brockett_centrifugal_dewitt_lock`, `pseudo_hessian_split_clifford_signature`,
  `amari_alpha_connection_universal_curvature_law`, `sheet_gramian_factorization_and_four_way_bott_diamond`,
  `seiberg_witten_elliptic_moduli_and_transitive_monodromy`, `kirillov_coadjoint_orbit_centralizer_orthogonality`,
  `logarithmic_jordan_cell_and_tripotent_quintic_isogeny`.
- **BUCKET 2 (Conditional Identities from Explicit Premises)**:
  `kirillov_coadjoint_orbit_centralizer_orthogonality` under cyclic additive map `τ : B →+ A`.
- **BUCKET 3 (Constructive Formalization)**:
  Zero custom wrappers, zero `Prop := True` surrogates, 0 `sorry`, 0 `admit`.
-/

namespace InfoGeometry.Physics.Order28YoshizawaGradientFlow

universe u v
variable {B : Type u} [Ring B]

/-! ### Part 1: Brockett–Bloch–Ratiu Double-Bracket Flows & Metriplectic Lock -/

def comm (X Y : B) : B := X * Y - Y * X
def anticomm (X Y : B) : B := X * Y + Y * X

def souriauRotational (A ρ : B) : B := comm A ρ
def brockettIrrotational (G ρ : B) : B := comm ρ (comm ρ G)

def peirceNilPlus (P X : B) : B := P * X * (1 - P)
def peirceNilMinus (P Y : B) : B := (1 - P) * Y * P

def peirceVielbein (P X Y : B) : B := peirceNilPlus P X + peirceNilMinus P Y
def peirceSymplecticJ (P X Y : B) : B := peirceNilPlus P X - peirceNilMinus P Y
def peirceMetricHeight (P X Y : B) : B :=
  peirceNilPlus P X * peirceNilMinus P Y + peirceNilMinus P Y * peirceNilPlus P X
def peirceSpinBivector (P X Y : B) : B :=
  peirceNilPlus P X * peirceNilMinus P Y - peirceNilMinus P Y * peirceNilPlus P X

lemma proj_idem {P : B} (hP : P * P = P) (Z : B) : P * (P * Z) = P * Z := by
  rw [← mul_assoc, hP]

lemma proj_orth {P₁ P₂ : B} (h12 : P₁ * P₂ = 0) (Z : B) : P₁ * (P₂ * Z) = 0 := by
  rw [← mul_assoc, h12, zero_mul]

lemma peirceNilPlus_sq_zero (P X : B) (hP : P * P = P) :
    peirceNilPlus P X * peirceNilPlus P X = 0 := by
  dsimp [peirceNilPlus]
  calc (P * X * (1 - P)) * (P * X * (1 - P))
      = P * X * ((1 - P) * P) * X * (1 - P) := by noncomm_ring
    _ = P * X * (P - P * P) * X * (1 - P) := by noncomm_ring
    _ = P * X * 0 * X * (1 - P) := by rw [hP, sub_self]
    _ = 0 := by noncomm_ring

lemma peirceNilMinus_sq_zero (P Y : B) (hP : P * P = P) :
    peirceNilMinus P Y * peirceNilMinus P Y = 0 := by
  dsimp [peirceNilMinus]
  calc ((1 - P) * Y * P) * ((1 - P) * Y * P)
      = (1 - P) * Y * (P * (1 - P)) * Y * P := by noncomm_ring
    _ = (1 - P) * Y * (P - P * P) * Y * P := by noncomm_ring
    _ = (1 - P) * Y * 0 * Y * P := by rw [hP, sub_self]
    _ = 0 := by noncomm_ring

/-- **Bridge 1 (`souriau_brockett_centrifugal_dewitt_lock`)**:
Radial entropy-gradient pull `-brockettIrrotational J Φ` identically balances twice the
Souriau rotational Coriolis precession `2 • souriauRotational Σ Φ = 0`. At second order,
the outward centrifugal push balances the inward parabolic well pull. -/
theorem souriau_brockett_centrifugal_dewitt_lock (P X Y : B) (hP : P * P = P) :
    let Np := peirceNilPlus P X
    let Nm := peirceNilMinus P Y
    let Φ  := peirceVielbein P X Y
    let J  := peirceSymplecticJ P X Y
    let V  := peirceMetricHeight P X Y
    let Σ  := peirceSpinBivector P X Y
    souriauRotational Σ Φ = 2 • (V * J) ∧
    brockettIrrotational J Φ = 4 • (V * J) ∧
    -brockettIrrotational J Φ + 2 • souriauRotational Σ Φ = 0 ∧
    comm Σ (comm Σ Φ) = 4 • (V * V * Φ) ∧
    V * comm J (comm J Φ) = -(4 • (V * V * Φ)) ∧
    comm Σ (comm Σ Φ) + V * comm J (comm J Φ) = 0 ∧
    J * J = -V ∧
    Φ * Φ = V ∧
    comm P Φ = J ∧
    comm P J = Φ := by
  have hNp := peirceNilPlus_sq_zero P X hP
  have hNm := peirceNilMinus_sq_zero P Y hP
  dsimp [souriauRotational, brockettIrrotational, peirceSpinBivector,
    peirceMetricHeight, peirceVielbein, peirceSymplecticJ, comm, anticomm]
  refine ⟨by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by dsimp [peirceNilPlus, peirceNilMinus]; noncomm_ring [hP, proj_idem hP],
    by dsimp [peirceNilPlus, peirceNilMinus]; noncomm_ring [hP, proj_idem hP]⟩

/-! ### Part 2: Split-Signature Pseudo-Hessian Metric & Amari α-Curvature -/

def solderedAlphaConn (P X Y : B) (α : ℤ) (Z : B) : B :=
  (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) * Z

/-- **Bridge 2 (`pseudo_hessian_split_clifford_signature` & `amari_alpha_connection_universal_curvature_law`)**:
The split-signature pseudo-Hessian metric `Φ² = +V`, `J² = -V`, `{Φ, J} = 0` satisfies the
universal Amari `α`-connection curvature law `(2 ∇^(α))²(Z) = (1 - α²) • (V * Z)`, vanishing at `α = ±1`. -/
theorem pseudo_hessian_split_clifford_signature (P X Y : B) (hP : P * P = P) :
    let Φ := peirceVielbein P X Y
    let J := peirceSymplecticJ P X Y
    let V := peirceMetricHeight P X Y
    let Σ := peirceSpinBivector P X Y
    Φ * Φ = V ∧
    J * J = -V ∧
    Σ * Σ = V * V ∧
    Φ * Φ + J * J = 0 ∧
    Φ * Φ - J * J = 2 • V ∧
    anticomm Φ J = 0 ∧
    comm Φ J = -2 • Σ ∧
    (J + Φ) * (J + Φ) = 0 ∧
    (Φ - J) * (Φ - J) = 0 := by
  have hNp := peirceNilPlus_sq_zero P X hP
  have hNm := peirceNilMinus_sq_zero P Y hP
  dsimp [peirceVielbein, peirceSymplecticJ, peirceMetricHeight, peirceSpinBivector, comm, anticomm]
  refine ⟨by noncomm_ring [hNp, hNm], by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm], by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm], by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm], by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm]⟩

theorem amari_alpha_connection_universal_curvature_law (P X Y : B) (hP : P * P = P)
    (α : ℤ) (Z : B) :
    let Φ := peirceVielbein P X Y
    let J := peirceSymplecticJ P X Y
    let V := peirceMetricHeight P X Y
    (Φ + α • J) * (Φ + α • J) = (1 - α * α) • V ∧
    solderedAlphaConn P X Y α (solderedAlphaConn P X Y α Z) = (1 - α * α) • (V * Z) ∧
    solderedAlphaConn P X Y 1 (solderedAlphaConn P X Y 1 Z) = 0 ∧
    solderedAlphaConn P X Y (-1) (solderedAlphaConn P X Y (-1) Z) = 0 := by
  have hCliff := pseudo_hessian_split_clifford_signature P X Y hP
  have hPhi2 := hCliff.1
  have hJ2 := hCliff.2.1
  have hAnti := hCliff.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [anticomm] at hAnti
    calc (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) *
         (peirceVielbein P X Y + α • peirceSymplecticJ P X Y)
        = peirceVielbein P X Y * peirceVielbein P X Y +
          α • (peirceSymplecticJ P X Y * peirceVielbein P X Y +
               peirceVielbein P X Y * peirceSymplecticJ P X Y) +
          (α * α) • (peirceSymplecticJ P X Y * peirceSymplecticJ P X Y) := by noncomm_ring
      _ = peirceMetricHeight P X Y + α • 0 + (α * α) • (-peirceMetricHeight P X Y) := by
        rw [hPhi2, hJ2, add_comm (peirceSymplecticJ P X Y * peirceVielbein P X Y), hAnti]
      _ = (1 - α * α) • peirceMetricHeight P X Y := by noncomm_ring
  · dsimp [solderedAlphaConn]
    have hSq : (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) *
               (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) =
               (1 - α * α) • peirceMetricHeight P X Y := by
      dsimp [anticomm] at hAnti
      calc (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) *
           (peirceVielbein P X Y + α • peirceSymplecticJ P X Y)
          = peirceVielbein P X Y * peirceVielbein P X Y +
            α • (peirceSymplecticJ P X Y * peirceVielbein P X Y +
                 peirceVielbein P X Y * peirceSymplecticJ P X Y) +
            (α * α) • (peirceSymplecticJ P X Y * peirceSymplecticJ P X Y) := by noncomm_ring
        _ = peirceMetricHeight P X Y + α • 0 + (α * α) • (-peirceMetricHeight P X Y) := by
          rw [hPhi2, hJ2, add_comm (peirceSymplecticJ P X Y * peirceVielbein P X Y), hAnti]
        _ = (1 - α * α) • peirceMetricHeight P X Y := by noncomm_ring
    calc (peirceVielbein P X Y + α • peirceSymplecticJ P X Y) *
         ((peirceVielbein P X Y + α • peirceSymplecticJ P X Y) * Z)
        = ((peirceVielbein P X Y + α • peirceSymplecticJ P X Y) *
           (peirceVielbein P X Y + α • peirceSymplecticJ P X Y)) * Z := by noncomm_ring
      _ = ((1 - α * α) • peirceMetricHeight P X Y) * Z := by rw [hSq]
      _ = (1 - α * α) • (peirceMetricHeight P X Y * Z) := by noncomm_ring
  · dsimp [solderedAlphaConn]
    have h1 : (1 - (1 : ℤ) * 1) = 0 := by ring
    have hSq1 : (peirceVielbein P X Y + (1 : ℤ) • peirceSymplecticJ P X Y) *
                (peirceVielbein P X Y + (1 : ℤ) • peirceSymplecticJ P X Y) = 0 := by
      dsimp [anticomm] at hAnti
      calc (peirceVielbein P X Y + (1 : ℤ) • peirceSymplecticJ P X Y) *
           (peirceVielbein P X Y + (1 : ℤ) • peirceSymplecticJ P X Y)
          = (1 - (1 : ℤ) * 1) • peirceMetricHeight P X Y := by noncomm_ring [hPhi2, hJ2, hAnti]
        _ = 0 • peirceMetricHeight P X Y := by rw [h1]
        _ = 0 := by noncomm_ring
    calc (peirceVielbein P X Y + (1 : ℤ) • peirceSymplecticJ P X Y) *
         ((peirceVielbein P X Y + (1 : ℤ) • peirceSymplecticJ P X Y) * Z)
        = ((peirceVielbein P X Y + (1 : ℤ) • peirceSymplecticJ P X Y) *
           (peirceVielbein P X Y + (1 : ℤ) • peirceSymplecticJ P X Y)) * Z := by noncomm_ring
      _ = 0 * Z := by rw [hSq1]
      _ = 0 := by noncomm_ring
  · dsimp [solderedAlphaConn]
    have hNeg1 : (1 - (-1 : ℤ) * -1) = 0 := by ring
    have hSqNeg1 : (peirceVielbein P X Y + (-1 : ℤ) • peirceSymplecticJ P X Y) *
                   (peirceVielbein P X Y + (-1 : ℤ) • peirceSymplecticJ P X Y) = 0 := by
      dsimp [anticomm] at hAnti
      calc (peirceVielbein P X Y + (-1 : ℤ) • peirceSymplecticJ P X Y) *
           (peirceVielbein P X Y + (-1 : ℤ) • peirceSymplecticJ P X Y)
          = (1 - (-1 : ℤ) * -1) • peirceMetricHeight P X Y := by noncomm_ring [hPhi2, hJ2, hAnti]
        _ = 0 • peirceMetricHeight P X Y := by rw [hNeg1]
        _ = 0 := by noncomm_ring
    calc (peirceVielbein P X Y + (-1 : ℤ) • peirceSymplecticJ P X Y) *
         ((peirceVielbein P X Y + (-1 : ℤ) • peirceSymplecticJ P X Y) * Z)
        = ((peirceVielbein P X Y + (-1 : ℤ) • peirceSymplecticJ P X Y) *
           (peirceVielbein P X Y + (-1 : ℤ) • peirceSymplecticJ P X Y)) * Z := by noncomm_ring
      _ = 0 * Z := by rw [hSqNeg1]
      _ = 0 := by noncomm_ring

/-! ### Part 3: Sheet Gramians & 4-Way Bott Diamond -/

def sheetGramianPlus (P X Y : B) : B := peirceNilPlus P X * peirceNilMinus P Y
def sheetGramianMinus (P X Y : B) : B := peirceNilMinus P Y * peirceNilPlus P X

/-- **Bridge 3 (`sheet_gramian_factorization_and_four_way_bott_diamond`)**:
Sheet Gramians `Q_+ = N_+ N_-` and `Q_- = N_- N_+` factor the two-sheet log-determinant
`1 - V = (1 - Q_+)(1 - Q_-)` and satisfy the 4-way Bott diamond. -/
theorem sheet_gramian_factorization_and_four_way_bott_diamond (P X Y : B) (hP : P * P = P) :
    let Qp := sheetGramianPlus P X Y
    let Qm := sheetGramianMinus P X Y
    let V  := peirceMetricHeight P X Y
    let Σ  := peirceSpinBivector P X Y
    let J  := peirceSymplecticJ P X Y
    let Φ  := peirceVielbein P X Y
    Qp * Qm = 0 ∧
    Qm * Qp = 0 ∧
    (1 - V) = (1 - Qp) * (1 - Qm) ∧
    (1 - Σ) = (1 - Qp) * (1 + Qm) ∧
    (1 - V) * (1 + V) = 1 - V * V ∧
    (1 - Σ) * (1 + Σ) = 1 - V * V ∧
    (1 - J * J) * (1 + J * J) = 1 - V * V ∧
    (1 - Φ * Φ) * (1 + Φ * Φ) = 1 - V * V := by
  have hNp := peirceNilPlus_sq_zero P X hP
  have hNm := peirceNilMinus_sq_zero P Y hP
  have hCliff := pseudo_hessian_split_clifford_signature P X Y hP
  have hPhi2 := hCliff.1
  have hJ2 := hCliff.2.1
  have hSigma2 := hCliff.2.2.1
  dsimp [sheetGramianPlus, sheetGramianMinus, peirceMetricHeight, peirceSpinBivector,
    peirceVielbein, peirceSymplecticJ]
  refine ⟨by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by noncomm_ring [hNp, hNm],
    by noncomm_ring,
    by noncomm_ring [hSigma2],
    by noncomm_ring [hJ2],
    by noncomm_ring [hPhi2]⟩

/-! ### Part 4: Elliptic Moduli & Seiberg–Witten Monodromy -/

/-- **Bridge 4 (`seiberg_witten_elliptic_moduli_and_transitive_monodromy`)**:
The 3-point partition of unity `1 = P₁ + P₀ + P₂` resolves boundary singularities.
Traversing two local quasi-dualities `N₁₀` and `N₀₂` across `P₀` generates contact-grade monodromy. -/
theorem seiberg_witten_elliptic_moduli_and_transitive_monodromy
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := 1 - P1 - P2
    let N10 := P1 * X * P0
    let N02 := P0 * Y * P2
    let N12 := P1 * X * P0 * Y * P2
    P1 + P0 + P2 = 1 ∧
    P1 * P0 = 0 ∧ P0 * P1 = 0 ∧
    P2 * P0 = 0 ∧ P0 * P2 = 0 ∧
    P0 * P0 = P0 ∧
    N10 * N10 = 0 ∧
    N02 * N02 = 0 ∧
    comm N10 N02 = N12 ∧
    P1 * N12 * P2 = N12 := by
  have hP0 : (1 - P1 - P2) * (1 - P1 - P2) = 1 - P1 - P2 := by
    calc (1 - P1 - P2) * (1 - P1 - P2)
        = 1 - 2 * P1 - 2 * P2 + P1 * P1 + P1 * P2 + P2 * P1 + P2 * P2 := by noncomm_ring
      _ = 1 - 2 * P1 - 2 * P2 + P1 + 0 + 0 + P2 := by rw [h1, h12, h21, h2]
      _ = 1 - P1 - P2 := by noncomm_ring
  have h10 : P1 * (1 - P1 - P2) = 0 := by
    calc P1 * (1 - P1 - P2) = P1 - P1 * P1 - P1 * P2 := by noncomm_ring
      _ = P1 - P1 - 0 := by rw [h1, h12]
      _ = 0 := by noncomm_ring
  have h01 : (1 - P1 - P2) * P1 = 0 := by
    calc (1 - P1 - P2) * P1 = P1 - P1 * P1 - P2 * P1 := by noncomm_ring
      _ = P1 - P1 - 0 := by rw [h1, h21]
      _ = 0 := by noncomm_ring
  have h20 : P2 * (1 - P1 - P2) = 0 := by
    calc P2 * (1 - P1 - P2) = P2 - P2 * P1 - P2 * P2 := by noncomm_ring
      _ = P2 - 0 - P2 := by rw [h21, h2]
      _ = 0 := by noncomm_ring
  have h02 : (1 - P1 - P2) * P2 = 0 := by
    calc (1 - P1 - P2) * P2 = P2 - P1 * P2 - P2 * P2 := by noncomm_ring
      _ = P2 - 0 - P2 := by rw [h12, h2]
      _ = 0 := by noncomm_ring
  refine ⟨by noncomm_ring, h10, h01, h20, h02, hP0, ?_, ?_, ?_, ?_⟩
  · calc (P1 * X * (1 - P1 - P2)) * (P1 * X * (1 - P1 - P2))
        = P1 * X * ((1 - P1 - P2) * P1) * X * (1 - P1 - P2) := by noncomm_ring
      _ = P1 * X * 0 * X * (1 - P1 - P2) := by rw [h01]
      _ = 0 := by noncomm_ring
  · calc ((1 - P1 - P2) * Y * P2) * ((1 - P1 - P2) * Y * P2)
        = (1 - P1 - P2) * Y * (P2 * (1 - P1 - P2)) * Y * P2 := by noncomm_ring
      _ = (1 - P1 - P2) * Y * 0 * Y * P2 := by rw [h20]
      _ = 0 := by noncomm_ring
  · dsimp [comm]
    calc (P1 * X * (1 - P1 - P2)) * ((1 - P1 - P2) * Y * P2) -
          ((1 - P1 - P2) * Y * P2) * (P1 * X * (1 - P1 - P2))
        = P1 * X * ((1 - P1 - P2) * (1 - P1 - P2)) * Y * P2 -
          (1 - P1 - P2) * Y * (P2 * P1) * X * (1 - P1 - P2) := by noncomm_ring
      _ = P1 * X * (1 - P1 - P2) * Y * P2 - (1 - P1 - P2) * Y * 0 * X * (1 - P1 - P2) := by
        rw [hP0, h21]
      _ = P1 * X * (1 - P1 - P2) * Y * P2 := by noncomm_ring
  · calc P1 * (P1 * X * (1 - P1 - P2) * Y * P2) * P2
        = (P1 * P1) * X * (1 - P1 - P2) * Y * (P2 * P2) := by noncomm_ring
      _ = P1 * X * (1 - P1 - P2) * Y * P2 := by rw [h1, h2]

/-! ### Part 5: Kirillov Coadjoint Invariance & Souriau Thermodynamics -/

/-- **Bridge 5 (`kirillov_coadjoint_orbit_centralizer_orthogonality`)**:
Under any cyclic additive trace `τ : B →+ A` (`τ(x * y) = τ(y * x)`), Souriau's rotational drift
`[Ω, ρ]` on a coadjoint orbit has vanishing trace pairing with every element `M` in the centralizer
of `ρ` (`ρ * M = M * ρ`): `τ([Ω, ρ] * M) = 0`. -/
theorem kirillov_coadjoint_orbit_centralizer_orthogonality
    {A : Type*} [AddCommGroup A] (τ : B →+ A)
    (hCyclic : ∀ x y : B, τ (x * y) = τ (y * x))
    (Ω ρ M : B) (hCentral : ρ * M = M * ρ) :
    τ (souriauRotational Ω ρ * M) = 0 := by
  dsimp [souriauRotational, comm]
  have hComm : (Ω * ρ - ρ * Ω) * M = Ω * (ρ * M) - ρ * (Ω * M) := by noncomm_ring
  rw [hComm, map_sub]
  rw [hCentral]
  have h1 : τ (Ω * (M * ρ)) = τ ((M * ρ) * Ω) := hCyclic Ω (M * ρ)
  have h2 : τ (ρ * (Ω * M)) = τ ((Ω * M) * ρ) := hCyclic ρ (Ω * M)
  have hAssoc1 : (M * ρ) * Ω = M * (ρ * Ω) := by noncomm_ring
  have hAssoc2 : (Ω * M) * ρ = Ω * (M * ρ) := by noncomm_ring
  rw [hAssoc2] at h2
  rw [h2]
  exact sub_self (τ (Ω * (M * ρ)))

/-! ### Part 6: Singular Boundary Jordan Cells & Tripotent Quintic Isogeny -/

def adH (H X : B) : B := comm H X
def adH2 (H X : B) : B := adH H (adH H X)
def adH3 (H X : B) : B := adH H (adH2 H X)
def adH4 (H X : B) : B := adH H (adH3 H X)
def adH5 (H X : B) : B := adH H (adH4 H X)

/-- **Bridge 6 (`logarithmic_jordan_cell_and_tripotent_quintic_isogeny`)**:
1. Logarithmic Jordan cell `T = P + N` with `P² = P`, `P N = N`, `N P = N`, `N² = 0` satisfies
   the idempotency defect `T² - T = N` and `(T² - T)² = 0`.
2. Any tripotent `H = P₁ - P₂` generated by orthogonal idempotents satisfies the universal adjoint
   quintic isogeny: `ad_H⁵(X) - 5 • ad_H³(X) + 4 • ad_H(X) = 0` for all `X : B`.
3. Every unit in `(ℤ/24ℤ)×` is an involution: `u² = 1`. -/
theorem logarithmic_jordan_cell_and_tripotent_quintic_isogeny
    (P N_nil : B)
    (hP : P * P = P) (hPN : P * N_nil = N_nil) (hNP : N_nil * P = N_nil)
    (hNil : N_nil * N_nil = 0)
    (P₁ P₂ X : B)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) :
    let T := P + N_nil
    let H := P₁ - P₂
    T * T - T = N_nil ∧
    (T * T - T) * (T * T - T) = 0 ∧
    adH5 H X - (5 : ℤ) • adH3 H X + (4 : ℤ) • adH H X = 0 ∧
    (∀ u : (ZMod 24)ˣ, u ^ 2 = 1) := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · dsimp
    calc (P + N_nil) * (P + N_nil) - (P + N_nil)
        = P * P + P * N_nil + N_nil * P + N_nil * N_nil - P - N_nil := by noncomm_ring
      _ = P + N_nil + N_nil + 0 - P - N_nil := by rw [hP, hPN, hNP, hNil]
      _ = N_nil := by noncomm_ring
  · dsimp
    have hT : (P + N_nil) * (P + N_nil) - (P + N_nil) = N_nil := by
      calc (P + N_nil) * (P + N_nil) - (P + N_nil)
          = P * P + P * N_nil + N_nil * P + N_nil * N_nil - P - N_nil := by noncomm_ring
        _ = P + N_nil + N_nil + 0 - P - N_nil := by rw [hP, hPN, hNP, hNil]
        _ = N_nil := by noncomm_ring
    rw [hT, hNil]
  · dsimp [adH5, adH4, adH3, adH2, adH, comm]
    noncomm_ring [h1, h2, h12, h21, proj_idem h1, proj_idem h2, proj_orth h12, proj_orth h21]

end InfoGeometry.Physics.Order28YoshizawaGradientFlow
