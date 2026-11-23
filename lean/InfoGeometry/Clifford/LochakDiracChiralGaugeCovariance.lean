/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Clifford.DaviauRealDirac8x8
import InfoGeometry.Clifford.LochakRodichevFierzKrein
import InfoGeometry.Clifford.DaviauLochakDifferentialGauge

/-!
# Lochak Chiral Gauge Covariance of the Real 8D Dirac & LHWR Equations

Formalizes the dynamical Dirac-operator level of Lochak (2007) and Daviau (2001) on top of
`DaviauLochakDifferentialGauge`:

1. **Differential-Ring Real Dirac Lift**:
   Lifts `gammaZ`, `gammaLowZ`, `gamma0123Z`, `quatPZ`, `gamma5` into `Matrix (Fin 8) (Fin 8) R`
   and equips `Vec8Ring R := Fin 8 → R` with the entrywise derivation `vec8Deriv d`.
2. **Gauge Covariance of the Chiral- vs. Electric-Coupled Dirac Kinetic Operators**:
   For any trigonometric gauge unit `U = c • I₈ + s • Γ⁰¹²³` (`c² + s² = 1`, `d_μ c = -(d_μ θ) s`,
   `d_μ s = (d_μ θ) c`), shifting the chiral gauge potential `B_μ ↦ B_μ - ∂_μ θ` yields exact
   left-inverse intertwining
   `chiralDiracOp R deriv (B - dθ) (U *ᵥ Φ) = U⁻¹ *ᵥ chiralDiracOp R deriv B Φ`,
   contrasting directly with Daviau's electric `U(1)` gauge `E = c • I₈ + s • P₃`, where `[Γ_μ, P₃] = 0`
   gives `electricDiracOp R deriv (A - dθ) (E *ᵥ Φ) = E *ᵥ electricDiracOp R deriv A Φ`.
3. **Constant-Mass Obstruction vs. Nonlinear LHWR Chiral Mass Covariance**:
   Proves why a constant mass `m P₃` cannot be preserved under a nontrivial chiral rotation
   (`sin(2α) ≠ 0`), whereas the Lochak–Heisenberg–Weyl–Rodichev (LHWR) bilinear operator
   `lhwrMassMat Φ = Ω₁(Φ) I₈ + Ω₂(Φ) Γ⁰¹²³` transforms by `(U(α)⁻¹)²` so that
   `lhwrChiralMassVec κ (U(α) Φ) = U(α)⁻¹ *ᵥ lhwrChiralMassVec κ Φ`, yielding an exact
   gauge-covariant nonlinear real Dirac equation whose mass term vanishes on the Weyl lightcone
   (`weylCrossInner Φ = 0`).
4. **Smooth `C^∞(ℝ, ℝ)` Instantiation & Rodichev Torsion Bridge**:
   Realizes local gauge covariance over `SmoothRealFun = C^∞(ℝ, ℝ)` via `smoothChiralGaugeUnit θ`
   and `smoothElectricGaugeUnit θ`, and matches the covector chiral connection `B_ν = -½ σ_ν` onto
   Rodichev's skew-torsion triple-gamma term.
-/

noncomputable section

open Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Algebra.GradedNullconeAlgebra
open InfoGeometry.Canonical.KreinMajoranaBlockInvariance hiding Mat8R Vec8R
open InfoGeometry.Clifford.DaviauRealDirac8x8
open InfoGeometry.Clifford.LochakRodichevFierzKrein
open InfoGeometry.Clifford.DaviauLochakDifferentialGauge

namespace InfoGeometry.Clifford.LochakDiracChiralGaugeCovariance

/-! ### Trap T16 Noncommutativity Guard -/

/-- Explicit Trap T16 noncommutativity witness for real `M₈(ℝ)` Dirac matrices. -/
theorem mat8R_noncomm_guard : ∃ A B : Mat8R, A * B ≠ B * A :=
  ⟨gammaR 0, gammaR 1, daviau_mat8_noncomm.1⟩

/-! ### Section 1: Commutative-Ring Dirac Algebra Lift & Vector Derivation -/

abbrev Mat8Ring (R : Type*) := Matrix (Fin 8) (Fin 8) R
abbrev Vec8Ring (R : Type*) := Fin 8 → R

/-- Contravariant Dirac matrices `Γ^μ` lifted into `M₈(R)`. -/
def gammaRing (R : Type*) [CommRing R] (μ : Fin 4) : Mat8Ring R :=
  castZ8Ring R (gammaZ μ)

/-- Lowered Dirac matrices `Γ_μ = g_{μμ} Γ^μ` lifted into `M₈(R)`. -/
def gammaLowRing (R : Type*) [CommRing R] (μ : Fin 4) : Mat8Ring R :=
  castZ8Ring R (gammaLowZ μ)

/-- Pseudoscalar volume matrix `Γ⁰¹²³` lifted into `M₈(R)`. -/
def gamma0123Ring (R : Type*) [CommRing R] : Mat8Ring R :=
  castZ8Ring R gamma0123Z

/-- Quaternionic commutant generators `P_j` (`j = 0,1,2`) lifted into `M₈(R)`. -/
def quatPRing (R : Type*) [CommRing R] (j : Fin 3) : Mat8Ring R :=
  castZ8Ring R (quatPZ j)

/-- Real `γ₅` operator `Γ⁰¹²³ P_j` in `M₈(R)`. -/
def gamma5Ring (R : Type*) [CommRing R] (j : Fin 3) : Mat8Ring R :=
  gamma0123Ring R * quatPRing R j

@[simp] theorem gammaRing_real (μ : Fin 4) : gammaRing ℝ μ = gammaR μ := rfl
@[simp] theorem gammaLowRing_real (μ : Fin 4) : gammaLowRing ℝ μ = gammaLowR μ := rfl
@[simp] theorem gamma0123Ring_real : gamma0123Ring ℝ = gamma0123R := rfl
@[simp] theorem quatPRing_real (j : Fin 3) : quatPRing ℝ j = quatPR j := rfl
@[simp] theorem gamma5Ring_real (j : Fin 3) : gamma5Ring ℝ j = gamma5Real j := rfl

lemma castZ8Ring_zsmul (R : Type*) [CommRing R] (z : ℤ) (M : Mat8Z) :
    castZ8Ring R (z • M) = z • castZ8Ring R M := by
  ext i j
  change ((z * M i j : ℤ) : R) = (z • castZ8Ring R M) i j
  rw [Matrix.smul_apply, zsmul_eq_mul, Int.cast_mul]
  rfl

theorem gamma0123Ring_sq (R : Type*) [CommRing R] :
    gamma0123Ring R * gamma0123Ring R = -(1 : Mat8Ring R) := by
  dsimp [gamma0123Ring]
  rw [← castZ8Ring_mul, gamma0123Z_sq, castZ8Ring_neg, castZ8Ring_one]

theorem quatPRing_sq (R : Type*) [CommRing R] (j : Fin 3) :
    quatPRing R j * quatPRing R j = -(1 : Mat8Ring R) := by
  dsimp [quatPRing]
  rw [← castZ8Ring_mul, quatPZ_sq j, castZ8Ring_neg, castZ8Ring_one]

theorem gammaLowRing_eq (R : Type*) [CommRing R] (μ : Fin 4) :
    gammaLowRing R μ = minkowskiMetricZ μ • gammaRing R μ := by
  dsimp [gammaLowRing, gammaLowZ, gammaRing]
  exact castZ8Ring_zsmul R (minkowskiMetricZ μ) (gammaZ μ)

theorem gamma0123Ring_anticomm_gammaRing (R : Type*) [CommRing R] (μ : Fin 4) :
    gamma0123Ring R * gammaRing R μ = -(gammaRing R μ * gamma0123Ring R) := by
  have hZ : gamma0123Z * gammaZ μ = -(gammaZ μ * gamma0123Z) :=
    eq_neg_of_add_eq_zero_left (gamma0123Z_anticomm_gammaZ μ)
  dsimp [gamma0123Ring, gammaRing]
  rw [← castZ8Ring_mul, ← castZ8Ring_mul, hZ, castZ8Ring_neg]

theorem gammaLowRing_mul_gamma0123Ring (R : Type*) [CommRing R] (μ : Fin 4) :
    gammaLowRing R μ * gamma0123Ring R = -(gamma0123Ring R * gammaLowRing R μ) := by
  rw [gammaLowRing_eq, smul_mul_assoc, mul_smul_comm, gamma0123Ring_anticomm_gammaRing,
    smul_neg, neg_neg]

theorem gammaLowRing_comm_quatPRing (R : Type*) [CommRing R] (μ : Fin 4) (j : Fin 3) :
    gammaLowRing R μ * quatPRing R j = quatPRing R j * gammaLowRing R μ := by
  rw [gammaLowRing_eq, smul_mul_assoc, mul_smul_comm]
  dsimp [gammaRing, quatPRing]
  rw [← castZ8Ring_mul, ← castZ8Ring_mul, gammaZ_comm_quatPZ μ j]

/-- Entrywise application of a ring derivation `d : RingDeriv R` to `Vec8Ring R`. -/
def vec8Deriv {R : Type*} [CommRing R] (d : RingDeriv R) (Φ : Vec8Ring R) : Vec8Ring R :=
  fun i => d (Φ i)

@[simp]
theorem vec8Deriv_add {R : Type*} [CommRing R] (d : RingDeriv R) (Φ Ψ : Vec8Ring R) :
    vec8Deriv d (Φ + Ψ) = vec8Deriv d Φ + vec8Deriv d Ψ := by
  ext i
  exact d.map_add (Φ i) (Ψ i)

theorem vec8Deriv_mulVec {R : Type*} [CommRing R] (d : RingDeriv R)
    (A : Mat8Ring R) (Φ : Vec8Ring R) :
    vec8Deriv d (A *ᵥ Φ) = mat8RingDeriv d A *ᵥ Φ + A *ᵥ vec8Deriv d Φ := by
  ext i
  simp only [vec8Deriv, Matrix.mulVec, dotProduct, Pi.add_apply, mat8RingDeriv]
  rw [ringDeriv_sum d Finset.univ (fun k => A i k * Φ k)]
  calc
    ∑ k : Fin 8, d (A i k * Φ k)
        = ∑ k : Fin 8, (A i k * d (Φ k) + d (A i k) * Φ k) := by
          refine Finset.sum_congr rfl fun k _ => d.map_mul (A i k) (Φ k)
    _ = ∑ k : Fin 8, A i k * d (Φ k) + ∑ k : Fin 8, d (A i k) * Φ k := Finset.sum_add_distrib
    _ = ∑ k : Fin 8, d (A i k) * Φ k + ∑ k : Fin 8, A i k * d (Φ k) := add_comm _ _

theorem vec8Deriv_castZ8Ring_mulVec {R : Type*} [CommRing R] (d : RingDeriv R)
    (M : Mat8Z) (Φ : Vec8Ring R) :
    vec8Deriv d (castZ8Ring R M *ᵥ Φ) = castZ8Ring R M *ᵥ vec8Deriv d Φ := by
  rw [vec8Deriv_mulVec, mat8RingDeriv_castZ8Ring, Matrix.zero_mulVec, zero_add]

/-! ### Section 2: Differential Chiral- & Electric-Coupled Dirac Operators -/

/-- Chiral-gauged real 8D Dirac kinetic operator
`D_B Φ = ∑_μ Γ_μ (∂_μ Φ + B_μ Γ⁰¹²³ Φ)`. -/
def chiralDiracOp (R : Type*) [CommRing R] (deriv : Fin 4 → RingDeriv R)
    (B : Fin 4 → R) (Φ : Vec8Ring R) : Vec8Ring R :=
  ∑ μ : Fin 4, gammaLowRing R μ *ᵥ (vec8Deriv (deriv μ) Φ + (B μ • gamma0123Ring R) *ᵥ Φ)

/-- Electric-gauged real 8D Dirac kinetic operator
`D_A^e Φ = ∑_μ Γ_μ (∂_μ Φ + A_μ P₃ Φ)`. -/
def electricDiracOp (R : Type*) [CommRing R] (deriv : Fin 4 → RingDeriv R)
    (A : Fin 4 → R) (Φ : Vec8Ring R) : Vec8Ring R :=
  ∑ μ : Fin 4, gammaLowRing R μ *ᵥ (vec8Deriv (deriv μ) Φ + (A μ • quatPRing R 2) *ᵥ Φ)

/-- General local trigonometric gauge unit `g(c, s; J) = c • I₈ + s • J` for `J² = -I₈`. -/
def trigGaugeMatRing {R : Type*} [CommRing R] (J : Mat8Ring R) (c s : R) : Mat8Ring R :=
  c • (1 : Mat8Ring R) + s • J

theorem trigGaugeUnit_val {R : Type*} [CommRing R] (J : Mat8Ring R) (hJ2 : J * J = -1)
    (c s : R) (hcs : c ^ 2 + s ^ 2 = 1) :
    (trigGaugeUnit J hJ2 c s hcs).val = trigGaugeMatRing J c s := rfl

theorem trigGaugeUnit_inv {R : Type*} [CommRing R] (J : Mat8Ring R) (hJ2 : J * J = -1)
    (c s : R) (hcs : c ^ 2 + s ^ 2 = 1) :
    ((trigGaugeUnit J hJ2 c s hcs)⁻¹ : (Mat8Ring R)ˣ).val = trigGaugeMatRing J c (-s) := by
  change c • (1 : Mat8Ring R) - s • J = c • (1 : Mat8Ring R) + (-s) • J
  rw [sub_eq_add_neg, neg_smul]

private lemma trigGaugeMatRing_comm_gen {R : Type*} [CommRing R] (J : Mat8Ring R) (c s : R) :
    trigGaugeMatRing J c s * J = J * trigGaugeMatRing J c s := by
  dsimp [trigGaugeMatRing]
  rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]

private lemma trigGaugeMatRing_anticomm_left {R : Type*} [CommRing R] {G J : Mat8Ring R}
    (hanti : G * J = -(J * G)) (c s : R) :
    G * trigGaugeMatRing J c s = trigGaugeMatRing J c (-s) * G := by
  dsimp [trigGaugeMatRing]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, hanti, smul_neg, neg_smul]

private lemma trigGaugeMatRing_comm_left {R : Type*} [CommRing R] {G J : Mat8Ring R}
    (hcomm : G * J = J * G) (c s : R) :
    G * trigGaugeMatRing J c s = trigGaugeMatRing J c s * G := by
  dsimp [trigGaugeMatRing]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul, hcomm]

private lemma trig_sq_mat_prod {R : Type*} [CommRing R] (J : Mat8Ring R) (hJ2 : J * J = -1)
    (a b c d : R) :
    trigGaugeMatRing J a b * trigGaugeMatRing J c d =
      trigGaugeMatRing J (a * c - b * d) (a * d + b * c) := by
  dsimp [trigGaugeMatRing]
  have h11 : (a • (1 : Mat8Ring R)) * (c • (1 : Mat8Ring R)) = (a * c) • (1 : Mat8Ring R) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, one_mul]
  have h1J : (a • (1 : Mat8Ring R)) * (d • J) = (a * d) • J := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, one_mul]
  have hJ1 : (b • J) * (c • (1 : Mat8Ring R)) = (b * c) • J := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_one]
  have hJJ : (b • J) * (d • J) = -((b * d) • (1 : Mat8Ring R)) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hJ2, smul_neg]
  rw [add_mul, mul_add, mul_add, h11, h1J, hJ1, hJJ, sub_smul, add_smul]
  abel

private lemma mat8RingDeriv_trigGaugeMat {R : Type*} [CommRing R] (d : RingDeriv R)
    (J : Mat8Ring R) (hJ2 : J * J = -1) (hJd : mat8RingDeriv d J = 0)
    (c s dθ : R) (hdc : d c = -(dθ * s)) (hds : d s = dθ * c) :
    mat8RingDeriv d (trigGaugeMatRing J c s) = trigGaugeMatRing J c s * (dθ • J) := by
  dsimp [trigGaugeMatRing]
  rw [(mat8RingDeriv d).map_add, mat8RingDeriv_smul, mat8RingDeriv_smul, (mat8RingDeriv d).map_one,
    hJd, smul_zero, smul_zero, zero_add, zero_add, hdc, hds]
  rw [add_mul, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    one_mul, hJ2, smul_neg, ← neg_smul, smul_smul, smul_smul, mul_comm c dθ,
    mul_neg, mul_comm s dθ, add_comm]

private lemma covDeriv_trigGauge {R : Type*} [CommRing R] (d : RingDeriv R)
    (J : Mat8Ring R) (hJ2 : J * J = -1) (hJd : mat8RingDeriv d J = 0)
    (c s dθ B : R) (hdc : d c = -(dθ * s)) (hds : d s = dθ * c) (Φ : Vec8Ring R) :
    vec8Deriv d (trigGaugeMatRing J c s *ᵥ Φ) +
        ((B - dθ) • J) *ᵥ (trigGaugeMatRing J c s *ᵥ Φ) =
      trigGaugeMatRing J c s *ᵥ (vec8Deriv d Φ + (B • J) *ᵥ Φ) := by
  rw [vec8Deriv_mulVec, mat8RingDeriv_trigGaugeMat d J hJ2 hJd c s dθ hdc hds]
  have h1 : (trigGaugeMatRing J c s * (dθ • J)) *ᵥ Φ =
      trigGaugeMatRing J c s *ᵥ ((dθ • J) *ᵥ Φ) := by
    rw [Matrix.mulVec_mulVec]
  have h2 : ((B - dθ) • J) *ᵥ (trigGaugeMatRing J c s *ᵥ Φ) =
      trigGaugeMatRing J c s *ᵥ (((B - dθ) • J) *ᵥ Φ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, smul_mul_assoc, mul_smul_comm,
      trigGaugeMatRing_comm_gen]
  have h3 : (dθ • J) *ᵥ Φ + ((B - dθ) • J) *ᵥ Φ = (B • J) *ᵥ Φ := by
    rw [← Matrix.add_mulVec, ← add_smul]
    congr 1
    ring
  rw [h1, h2, Matrix.mulVec_add]
  calc
    (trigGaugeMatRing J c s *ᵥ ((dθ • J) *ᵥ Φ) + trigGaugeMatRing J c s *ᵥ vec8Deriv d Φ) +
        trigGaugeMatRing J c s *ᵥ (((B - dθ) • J) *ᵥ Φ)
        = trigGaugeMatRing J c s *ᵥ vec8Deriv d Φ +
            (trigGaugeMatRing J c s *ᵥ ((dθ • J) *ᵥ Φ) +
              trigGaugeMatRing J c s *ᵥ (((B - dθ) • J) *ᵥ Φ)) := by abel
    _ = trigGaugeMatRing J c s *ᵥ vec8Deriv d Φ +
          trigGaugeMatRing J c s *ᵥ ((dθ • J) *ᵥ Φ + ((B - dθ) • J) *ᵥ Φ) := by
            rw [Matrix.mulVec_add]
    _ = trigGaugeMatRing J c s *ᵥ vec8Deriv d Φ +
          trigGaugeMatRing J c s *ᵥ ((B • J) *ᵥ Φ) := by rw [h3]

/-- **Local Chiral Gauge Covariance Theorem (Lochak Eq. 25 / Daviau Eq. 25)** over any
differential commutative ring `(R, ∂_μ)`:
Under local chiral rotation `Φ ↦ U(c, s) Φ` with `U = c I₈ + s Γ⁰¹²³`, `c² + s² = 1`,
`∂_μ c = -(∂_μ θ) s`, `∂_μ s = (∂_μ θ) c`, and potential shift `B_μ ↦ B_μ - ∂_μ θ`,
the real Dirac kinetic operator intertwines by `U⁻¹`:
`D_{B - ∂θ}(U Φ) = U⁻¹ (D_B Φ)`. -/
theorem chiralDiracOp_local_gauge_covariance {R : Type*} [CommRing R]
    (deriv : Fin 4 → RingDeriv R) (B dθ : Fin 4 → R) (c s : R) (hcs : c ^ 2 + s ^ 2 = 1)
    (hdc : ∀ μ : Fin 4, deriv μ c = -(dθ μ * s))
    (hds : ∀ μ : Fin 4, deriv μ s = dθ μ * c)
    (Φ : Vec8Ring R) :
    let U := trigGaugeUnit (gamma0123Ring R) (gamma0123Ring_sq R) c s hcs
    chiralDiracOp R deriv (fun μ => B μ - dθ μ) (U.val *ᵥ Φ) =
      (U⁻¹ : (Mat8Ring R)ˣ).val *ᵥ chiralDiracOp R deriv B Φ := by
  intro U
  dsimp [chiralDiracOp]
  rw [trigGaugeUnit_val, trigGaugeUnit_inv, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hJd : mat8RingDeriv (deriv μ) (gamma0123Ring R) = 0 :=
    mat8RingDeriv_castZ8Ring (deriv μ) gamma0123Z
  rw [covDeriv_trigGauge (deriv μ) (gamma0123Ring R) (gamma0123Ring_sq R) hJd
    c s (dθ μ) (B μ) (hdc μ) (hds μ) Φ]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [trigGaugeMatRing_anticomm_left (gammaLowRing_mul_gamma0123Ring R μ) c s]

/-- **Local Electric `U(1)` Gauge Covariance Theorem** over any differential ring `(R, ∂_μ)`:
Because `[Γ_μ, P₃] = 0`, under local electric rotation `Φ ↦ E(c, s) Φ` with `E = c I₈ + s P₃`
and `A_μ ↦ A_μ - ∂_μ θ`, the Dirac kinetic operator commutes with `E`:
`D_{A - ∂θ}^e(E Φ) = E (D_A^e Φ)`. -/
theorem electricDiracOp_local_gauge_covariance {R : Type*} [CommRing R]
    (deriv : Fin 4 → RingDeriv R) (A dθ : Fin 4 → R) (c s : R) (hcs : c ^ 2 + s ^ 2 = 1)
    (hdc : ∀ μ : Fin 4, deriv μ c = -(dθ μ * s))
    (hds : ∀ μ : Fin 4, deriv μ s = dθ μ * c)
    (Φ : Vec8Ring R) :
    let E := trigGaugeUnit (quatPRing R 2) (quatPRing_sq R 2) c s hcs
    electricDiracOp R deriv (fun μ => A μ - dθ μ) (E.val *ᵥ Φ) =
      E.val *ᵥ electricDiracOp R deriv A Φ := by
  intro E
  dsimp [electricDiracOp]
  rw [trigGaugeUnit_val, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hJd : mat8RingDeriv (deriv μ) (quatPRing R 2) = 0 :=
    mat8RingDeriv_castZ8Ring (deriv μ) (quatPZ 2)
  rw [covDeriv_trigGauge (deriv μ) (quatPRing R 2) (quatPRing_sq R 2) hJd
    c s (dθ μ) (A μ) (hdc μ) (hds μ) Φ]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [trigGaugeMatRing_comm_left (gammaLowRing_comm_quatPRing R μ 2) c s]

/-! ### Section 3: Constant-Mass Chiral Obstruction vs. Electric Covariance -/

/-- Under the electric `U(1)` gauge `E`, a linear mass term `m P₃` commutes with `E`, so the
massive Dirac equation `D_A^e Φ = m P₃ Φ` is strictly gauge covariant. -/
theorem electricDirac_linear_mass_covariant {R : Type*} [CommRing R]
    (deriv : Fin 4 → RingDeriv R) (A dθ : Fin 4 → R) (m c s : R) (hcs : c ^ 2 + s ^ 2 = 1)
    (hdc : ∀ μ : Fin 4, deriv μ c = -(dθ μ * s))
    (hds : ∀ μ : Fin 4, deriv μ s = dθ μ * c)
    (Φ : Vec8Ring R)
    (hsol : electricDiracOp R deriv A Φ = (m • quatPRing R 2) *ᵥ Φ) :
    let E := trigGaugeUnit (quatPRing R 2) (quatPRing_sq R 2) c s hcs
    electricDiracOp R deriv (fun μ => A μ - dθ μ) (E.val *ᵥ Φ) =
      (m • quatPRing R 2) *ᵥ (E.val *ᵥ Φ) := by
  intro E
  rw [electricDiracOp_local_gauge_covariance deriv A dθ c s hcs hdc hds Φ, hsol]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_smul_comm, smul_mul_assoc,
    trigGaugeUnit_val, trigGaugeMatRing_comm_gen (quatPRing R 2) c s]

private lemma chiralGaugeMat_eq_trigRing (α : ℝ) :
    chiralGaugeMat α = trigGaugeMatRing (gamma0123Ring ℝ) (Real.cos α) (Real.sin α) := rfl

/-- Constant-mass chiral obstruction: whenever `m ≠ 0`, `sin(2α) ≠ 0`, and `Φ ≠ 0`, the chiral
transformation `U(α)⁻¹` of a constant mass term `(m • P₃) *ᵥ Φ` never equals `(m • P₃) *ᵥ (U(α) Φ)`.
Hence a fixed mass `m` breaks chiral gauge covariance whenever `sin(2α) ≠ 0`. -/
theorem chiralGauge_constant_mass_obstruction (α m : ℝ) (hm : m ≠ 0) (hsin : Real.sin (2 * α) ≠ 0)
    (Φ : Vec8R) (hΦ : Φ ≠ 0) :
    chiralGaugeMat (-α) *ᵥ ((m • quatPR 2) *ᵥ Φ) ≠
      (m • quatPR 2) *ᵥ (chiralGaugeMat α *ᵥ Φ) := by
  intro heq
  have hcomm : chiralGaugeMat α * (m • quatPR 2) = (m • quatPR 2) * chiralGaugeMat α := by
    rw [chiralGaugeMat_eq_trigRing, mul_smul_comm, smul_mul_assoc]
    congr 1
    exact trigGaugeMatRing_comm_gen (gamma0123Ring ℝ) (Real.cos α) (Real.sin α)
      |> fun h => by
        dsimp [trigGaugeMatRing]
        rw [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one,
          gamma0123R_comm_quatPR 2]
  have hrhs_comm :
      (m • quatPR 2) *ᵥ (chiralGaugeMat α *ᵥ Φ) =
        chiralGaugeMat α *ᵥ ((m • quatPR 2) *ᵥ Φ) := by
    rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec]
  rw [hrhs_comm] at heq
  have hsq : chiralGaugeMat α * chiralGaugeMat α = chiralGaugeMat (2 * α) := by
    rw [chiralGaugeMat_mul, ← two_mul]
  have heq2 : ((m • quatPR 2) *ᵥ Φ) = (chiralGaugeMat (2 * α)) *ᵥ ((m • quatPR 2) *ᵥ Φ) := by
    calc
      ((m • quatPR 2) *ᵥ Φ)
          = (1 : Mat8R) *ᵥ ((m • quatPR 2) *ᵥ Φ) := (Matrix.one_mulVec _).symm
      _ = (chiralGaugeMat α * chiralGaugeMat (-α)) *ᵥ ((m • quatPR 2) *ᵥ Φ) := by
            rw [chiralGaugeMat_mul, add_neg_cancel, chiralGaugeMat_zero]
      _ = chiralGaugeMat α *ᵥ (chiralGaugeMat (-α) *ᵥ ((m • quatPR 2) *ᵥ Φ)) :=
            (Matrix.mulVec_mulVec _ _ _).symm
      _ = chiralGaugeMat α *ᵥ (chiralGaugeMat α *ᵥ ((m • quatPR 2) *ᵥ Φ)) := by
            rw [heq]
      _ = (chiralGaugeMat α * chiralGaugeMat α) *ᵥ ((m • quatPR 2) *ᵥ Φ) :=
            Matrix.mulVec_mulVec _ _ _
      _ = (chiralGaugeMat (2 * α)) *ᵥ ((m • quatPR 2) *ᵥ Φ) := by
            rw [hsq]
  have hzero : (chiralGaugeMat (2 * α) - 1) *ᵥ ((m • quatPR 2) *ᵥ Φ) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← heq2, sub_self]
  have hdiff : chiralGaugeMat (2 * α) - 1 =
      trigGaugeMatRing (gamma0123Ring ℝ) (Real.cos (2 * α) - 1) (Real.sin (2 * α)) := by
    dsimp [chiralGaugeMat, trigGaugeMatRing]
    rw [sub_smul, one_smul]
    abel
  have hconj :
      trigGaugeMatRing (gamma0123Ring ℝ) (Real.cos (2 * α) - 1) (-Real.sin (2 * α)) *
        (chiralGaugeMat (2 * α) - 1) =
      (2 * (1 - Real.cos (2 * α))) • (1 : Mat8R) := by
    rw [hdiff, trig_sq_mat_prod (gamma0123Ring ℝ) (gamma0123Ring_sq ℝ)]
    have hcs := Real.cos_sq_add_sin_sq (2 * α)
    have h1 : (Real.cos (2 * α) - 1) * (Real.cos (2 * α) - 1) -
        (-Real.sin (2 * α)) * Real.sin (2 * α) = 2 * (1 - Real.cos (2 * α)) := by
      linarith
    have h0 : (Real.cos (2 * α) - 1) * Real.sin (2 * α) +
        (-Real.sin (2 * α)) * (Real.cos (2 * α) - 1) = 0 := by ring
    dsimp [trigGaugeMatRing]
    rw [h1, h0, zero_smul, add_zero]
  have hscaled : (2 * (1 - Real.cos (2 * α))) • ((m • quatPR 2) *ᵥ Φ) = 0 := by
    have hmul := congrArg (fun v =>
      trigGaugeMatRing (gamma0123Ring ℝ) (Real.cos (2 * α) - 1) (-Real.sin (2 * α)) *ᵥ v) hzero
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, hconj, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hmul
    exact hmul
  have hne : 2 * (1 - Real.cos (2 * α)) ≠ 0 := by
    intro hc
    have hc1 : Real.cos (2 * α) = 1 := by linarith
    have hcs := Real.cos_sq_add_sin_sq (2 * α)
    rw [hc1, one_pow] at hcs
    have hs2 : Real.sin (2 * α) ^ 2 = 0 := by linarith
    exact hsin (sq_eq_zero_iff.mp hs2)
  have hmvec : (m • quatPR 2) *ᵥ Φ = 0 := (smul_eq_zero.mp hscaled).resolve_left hne
  have hm2 : -(m * m) • Φ = 0 := by
    have hp := congrArg (fun v => (m • quatPR 2) *ᵥ v) hmvec
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, smul_mul_assoc, mul_smul_comm, smul_smul,
      quatPR_sq 2, smul_neg, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← neg_smul] at hp
    exact hp
  have hm2ne : -(m * m) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hm hm)
  exact hΦ ((smul_eq_zero.mp hm2).resolve_left hm2ne)

/-! ### Section 4: Nonlinear LHWR Chiral-Covariant Mass & Null Lightcone Vanishing -/

/-- Matrix factor `Ω₁(Φ) I₈ + Ω₂(Φ) Γ⁰¹²³` in the nonlinear Lochak–Heisenberg–Weyl–Rodichev
(LHWR) chiral-covariant mass term. -/
def lhwrMassMat (Φ : Vec8R) : Mat8R :=
  omega1 Φ • (1 : Mat8R) + omega2 Φ • gamma0123R

/-- Full nonlinear LHWR mass vector `κ (Ω₁(Φ) I₈ + Ω₂(Φ) Γ⁰¹²³) P₃ Φ` in `ℝ⁸`. -/
def lhwrChiralMassVec (κ : ℝ) (Φ : Vec8R) : Vec8R :=
  (κ • (lhwrMassMat Φ * quatPR 2)) *ᵥ Φ

theorem lhwrMassMat_normSq_identity (Φ : Vec8R) :
    lhwrMassMat Φ * (omega1 Φ • (1 : Mat8R) - omega2 Φ • gamma0123R) =
      (omega1 Φ ^ 2 + omega2 Φ ^ 2) • (1 : Mat8R) := by
  have h : omega1 Φ • (1 : Mat8R) - omega2 Φ • gamma0123R =
      trigGaugeMatRing (gamma0123Ring ℝ) (omega1 Φ) (-omega2 Φ) := by
    dsimp [trigGaugeMatRing]
    rw [sub_eq_add_neg, neg_smul]
  change trigGaugeMatRing (gamma0123Ring ℝ) (omega1 Φ) (omega2 Φ) *
      (omega1 Φ • (1 : Mat8R) - omega2 Φ • gamma0123R) = _
  rw [h, trig_sq_mat_prod (gamma0123Ring ℝ) (gamma0123Ring_sq ℝ)]
  dsimp [trigGaugeMatRing]
  have h1 : omega1 Φ * omega1 Φ - omega2 Φ * -omega2 Φ = omega1 Φ ^ 2 + omega2 Φ ^ 2 := by ring
  have h0 : omega1 Φ * -omega2 Φ + omega2 Φ * omega1 Φ = 0 := by ring
  rw [h1, h0, zero_smul, add_zero]

/-- Key nonlinear chiral covariance law for the LHWR matrix factor:
`lhwrMassMat (U(α) Φ) = U(-2α) * lhwrMassMat Φ`. -/
theorem lhwrMassMat_chiralGauge (α : ℝ) (Φ : Vec8R) :
    lhwrMassMat (chiralGaugeMat α *ᵥ Φ) = chiralGaugeMat (-2 * α) * lhwrMassMat Φ := by
  rcases lochak_chiral_gauge_action α Φ with ⟨h1, h2, _, _, _⟩
  dsimp [lhwrMassMat]
  rw [h1, h2]
  have hcm : chiralGaugeMat (-2 * α) =
      trigGaugeMatRing (gamma0123Ring ℝ) (Real.cos (2 * α)) (-Real.sin (2 * α)) := by
    dsimp [chiralGaugeMat, trigGaugeMatRing]
    rw [show -2 * α = -(2 * α) by ring, Real.cos_neg, Real.sin_neg]
  change trigGaugeMatRing (gamma0123Ring ℝ) _ _ =
    chiralGaugeMat (-2 * α) * trigGaugeMatRing (gamma0123Ring ℝ) (omega1 Φ) (omega2 Φ)
  rw [hcm, trig_sq_mat_prod (gamma0123Ring ℝ) (gamma0123Ring_sq ℝ)]
  congr 1 <;> ring

/-- **LHWR Chiral Mass Gauge Covariance Theorem (Lochak Eq. 40)**:
Under chiral rotation `Φ ↦ U(α) Φ`, the nonlinear mass vector transforms by `U(α)⁻¹`:
`lhwrChiralMassVec κ (U(α) Φ) = U(α)⁻¹ *ᵥ lhwrChiralMassVec κ Φ`,
matching the kinetic transformation `D_{B - ∂α}(U Φ) = U⁻¹ (D_B Φ)`! -/
theorem lhwrChiralMassVec_chiralGauge_covariant (κ α : ℝ) (Φ : Vec8R) :
    lhwrChiralMassVec κ (chiralGaugeMat α *ᵥ Φ) =
      chiralGaugeMat (-α) *ᵥ lhwrChiralMassVec κ Φ := by
  dsimp [lhwrChiralMassVec]
  rw [lhwrMassMat_chiralGauge α Φ]
  have hcommP : chiralGaugeMat α * quatPR 2 = quatPR 2 * chiralGaugeMat α := by
    dsimp [chiralGaugeMat]
    rw [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one, gamma0123R_comm_quatPR 2]
  have hcommM : chiralGaugeMat α * lhwrMassMat Φ = lhwrMassMat Φ * chiralGaugeMat α := by
    dsimp [lhwrMassMat]
    rw [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one, one_mul]
    have hcG : chiralGaugeMat α * gamma0123R = gamma0123R * chiralGaugeMat α := by
      dsimp [chiralGaugeMat]
      rw [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one]
    rw [hcG]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  calc
    κ • (chiralGaugeMat (-2 * α) * lhwrMassMat Φ * quatPR 2) * chiralGaugeMat α
        = κ • (chiralGaugeMat (-2 * α) * lhwrMassMat Φ * (quatPR 2 * chiralGaugeMat α)) := by
            rw [smul_mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = κ • (chiralGaugeMat (-2 * α) * ((lhwrMassMat Φ * chiralGaugeMat α) * quatPR 2)) := by
            rw [← hcommP]
            simp only [Matrix.mul_assoc]
    _ = κ • ((chiralGaugeMat (-2 * α) * chiralGaugeMat α) * (lhwrMassMat Φ * quatPR 2)) := by
            rw [← hcommM]
            simp only [Matrix.mul_assoc]
    _ = chiralGaugeMat (-α) * (κ • (lhwrMassMat Φ * quatPR 2)) := by
            rw [chiralGaugeMat_mul, show -2 * α + α = -α by ring, Algebra.mul_smul_comm]

/-- Under Daviau's electric `U(1)` gauge `E(α)`, the LHWR nonlinear mass transforms by `E(α)`:
`lhwrChiralMassVec κ (E(α) Φ) = E(α) *ᵥ lhwrChiralMassVec κ Φ`. -/
theorem lhwrChiralMassVec_electricGauge_covariant (κ α : ℝ) (Φ : Vec8R) :
    lhwrChiralMassVec κ (electricGaugeMat α *ᵥ Φ) =
      electricGaugeMat α *ᵥ lhwrChiralMassVec κ Φ := by
  rcases daviau_electric_gauge_invariance α Φ with ⟨h1, h2, _, _⟩
  have hM : lhwrMassMat (electricGaugeMat α *ᵥ Φ) = lhwrMassMat Φ := by
    dsimp [lhwrMassMat]
    rw [h1, h2]
  have hcommP : electricGaugeMat α * quatPR 2 = quatPR 2 * electricGaugeMat α := by
    dsimp [electricGaugeMat]
    rw [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one]
  have hcommM : electricGaugeMat α * lhwrMassMat Φ = lhwrMassMat Φ * electricGaugeMat α := by
    dsimp [lhwrMassMat]
    rw [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one, one_mul]
    have hcG : electricGaugeMat α * gamma0123R = gamma0123R * electricGaugeMat α := by
      dsimp [electricGaugeMat]
      rw [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one, gamma0123R_comm_quatPR 2]
    rw [hcG]
  dsimp [lhwrChiralMassVec]
  rw [hM, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  congr 1
  calc
    (lhwrMassMat Φ * quatPR 2) * electricGaugeMat α
        = lhwrMassMat Φ * (quatPR 2 * electricGaugeMat α) := Matrix.mul_assoc _ _ _
    _ = lhwrMassMat Φ * (electricGaugeMat α * quatPR 2) := by rw [← hcommP]
    _ = (lhwrMassMat Φ * electricGaugeMat α) * quatPR 2 := (Matrix.mul_assoc _ _ _).symm
    _ = electricGaugeMat α * (lhwrMassMat Φ * quatPR 2) := by rw [← hcommM, Matrix.mul_assoc]

/-- On the null lightcone / Weyl sector (`weylCrossInner Φ = 0`, equivalently `Ω₁² + Ω₂² = 0`),
the LHWR mass term vanishes identically. -/
theorem lhwrChiralMassVec_eq_zero_of_lightcone (κ : ℝ) (Φ : Vec8R)
    (h : weylCrossInner Φ = 0) :
    lhwrChiralMassVec κ Φ = 0 := by
  have hsq : omega1 Φ ^ 2 + omega2 Φ ^ 2 = 0 :=
    (lochak_eq47_lightcone_orthogonality Φ).mpr h
  have h1 : omega1 Φ = 0 := by
    nlinarith [sq_nonneg (omega1 Φ), sq_nonneg (omega2 Φ)]
  have h2 : omega2 Φ = 0 := by
    nlinarith [sq_nonneg (omega1 Φ), sq_nonneg (omega2 Φ)]
  dsimp [lhwrChiralMassVec, lhwrMassMat]
  rw [h1, h2, zero_smul, zero_smul, add_zero, Matrix.zero_mul, smul_zero, Matrix.zero_mulVec]

/-- On a massive spinor (`Φ₀ = e₀`) with coupling `κ ≠ 0`, `lhwrChiralMassVec κ Φ₀ ≠ 0`. -/
theorem lhwrChiralMassVec_massive_witness (κ : ℝ) (hκ : κ ≠ 0) :
    let Φ₀ : Vec8R := ![1, 0, 0, 0, 0, 0, 0, 0]
    lhwrChiralMassVec κ Φ₀ ≠ 0 := by
  intro Φ₀ heq
  have h1 : omega1 Φ₀ = 1 := by
    rw [omega1_expand]
    simp [Φ₀]
  have h2 : omega2 Φ₀ = 0 := by
    rw [omega2_expand]
    simp [Φ₀]
  have h3 := congrFun heq 3
  simp [lhwrChiralMassVec, lhwrMassMat, h1, h2, Φ₀, quatPR, quatPZ, p3Z, castZ8,
    Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at h3
  exact hκ h3

/-! ### Section 5: Smooth `C^∞(ℝ, ℝ)` Instantiation & Rodichev Torsion Match -/

/-- Zero ring derivation on any ring `R`. -/
def zeroRingDeriv (R : Type*) [Ring R] : RingDeriv R where
  toFun _ := 0
  map_add' _ _ := (add_zero 0).symm
  map_mul' _ _ := by simp

/-- Canonical 1D smooth temporal Dirac derivation tuple `(d/dt, 0, 0, 0)` over `SmoothRealFun`. -/
def smoothTemporalDerivs : Fin 4 → RingDeriv SmoothRealFun
  | ⟨0, _⟩ => smoothDeriv
  | ⟨1, _⟩ => zeroRingDeriv SmoothRealFun
  | ⟨2, _⟩ => zeroRingDeriv SmoothRealFun
  | ⟨3, _⟩ => zeroRingDeriv SmoothRealFun

/-- Evaluation of a smooth `8`-spinor field at parameter `t : ℝ`. -/
def evalVec8 (Φ : Vec8Ring SmoothRealFun) (t : ℝ) : Vec8R :=
  fun i => (Φ i).val t

private lemma smoothRealFun_sum_val {ι : Type*} (s : Finset ι) (f : ι → SmoothRealFun) (t : ℝ) :
    (∑ j ∈ s, f j).val t = ∑ j ∈ s, (f j).val t := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    change (f a).val t + (∑ j ∈ s, f j).val t = (f a).val t + ∑ j ∈ s, (f j).val t
    rw [ih]

@[simp]
lemma evalVec8_smoothChiralGauge (θ : SmoothRealFun) (Φ : Vec8Ring SmoothRealFun) (t : ℝ) :
    evalVec8 ((smoothChiralGaugeUnit θ).val *ᵥ Φ) t =
      chiralGaugeMat (θ.val t) *ᵥ evalVec8 Φ t := by
  ext i
  dsimp [evalVec8, Matrix.mulVec, dotProduct]
  rw [smoothRealFun_sum_val]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ((smoothChiralGaugeUnit θ).val i j).val t * (Φ j).val t =
    (chiralGaugeMat (θ.val t) i j) * (Φ j).val t
  congr 1
  by_cases hij : i = j <;>
    · simp [hij, smoothChiralGaugeUnit, trigGaugeUnit, chiralGaugeMat, smoothCos, smoothSin,
        gamma0123R, castZ8Ring, castZ8]
      rfl

@[simp]
lemma evalVec8_smoothChiralGauge_inv (θ : SmoothRealFun) (Φ : Vec8Ring SmoothRealFun) (t : ℝ) :
    evalVec8 (((smoothChiralGaugeUnit θ)⁻¹ : (Mat8Ring SmoothRealFun)ˣ).val *ᵥ Φ) t =
      chiralGaugeMat (-(θ.val t)) *ᵥ evalVec8 Φ t := by
  ext i
  dsimp [evalVec8, Matrix.mulVec, dotProduct]
  rw [smoothRealFun_sum_val]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (((smoothChiralGaugeUnit θ)⁻¹ : (Mat8Ring SmoothRealFun)ˣ).val i j).val t * (Φ j).val t =
    (chiralGaugeMat (-(θ.val t)) i j) * (Φ j).val t
  congr 1
  by_cases hij : i = j <;>
    simp [hij, smoothChiralGaugeUnit, trigGaugeUnit, chiralGaugeMat, smoothCos, smoothSin,
      Real.cos_neg, Real.sin_neg, gamma0123R, castZ8Ring, castZ8]
  · exact sub_eq_add_neg _ _
  · rfl

/-- **Smooth `C^∞(ℝ, ℝ)` Temporal Chiral Gauge Covariance**:
Over `SmoothRealFun = C^∞(ℝ, ℝ)`, transforming `Φ ↦ U(θ) Φ` (`smoothChiralGaugeUnit θ`)
and shifting `B_μ ↦ B_μ - (∂_μ θ)` transforms `chiralDiracOp SmoothRealFun smoothTemporalDerivs`
precisely by `U(θ)⁻¹`. -/
theorem smooth_temporal_chiral_dirac_covariance (B : Fin 4 → SmoothRealFun)
    (θ : SmoothRealFun) (Φ : Vec8Ring SmoothRealFun) :
    let U := smoothChiralGaugeUnit θ
    let dθ := fun μ : Fin 4 => smoothTemporalDerivs μ θ
    chiralDiracOp SmoothRealFun smoothTemporalDerivs (fun μ => B μ - dθ μ) (U.val *ᵥ Φ) =
      (U⁻¹ : (Mat8Ring SmoothRealFun)ˣ).val *ᵥ
        chiralDiracOp SmoothRealFun smoothTemporalDerivs B Φ := by
  intro U dθ
  refine chiralDiracOp_local_gauge_covariance smoothTemporalDerivs B dθ
    (smoothCos θ) (smoothSin θ) (smoothCos_sq_add_sin_sq θ) ?_ ?_ Φ
  · intro μ
    fin_cases μ
    · exact smoothDeriv_cos θ
    · change 0 = -(0 * _); simp
    · change 0 = -(0 * _); simp
    · change 0 = -(0 * _); simp
  · intro μ
    fin_cases μ
    · exact smoothDeriv_sin θ
    · change 0 = 0 * _; simp
    · change 0 = 0 * _; simp
    · change 0 = 0 * _; simp

/-- **Smooth `C^∞(ℝ, ℝ)` Temporal Electric Gauge Covariance**:
Over `SmoothRealFun = C^∞(ℝ, ℝ)`, transforming `Φ ↦ E(θ) Φ` (`smoothElectricGaugeUnit θ`)
and shifting `A_μ ↦ A_μ - ∂_μ θ` commutes with `electricDiracOp`. -/
theorem smooth_temporal_electric_dirac_covariance (A : Fin 4 → SmoothRealFun)
    (θ : SmoothRealFun) (Φ : Vec8Ring SmoothRealFun) :
    let E := smoothElectricGaugeUnit θ
    let dθ := fun μ : Fin 4 => smoothTemporalDerivs μ θ
    electricDiracOp SmoothRealFun smoothTemporalDerivs (fun μ => A μ - dθ μ) (E.val *ᵥ Φ) =
      E.val *ᵥ electricDiracOp SmoothRealFun smoothTemporalDerivs A Φ := by
  intro E dθ
  refine electricDiracOp_local_gauge_covariance smoothTemporalDerivs A dθ
    (smoothCos θ) (smoothSin θ) (smoothCos_sq_add_sin_sq θ) ?_ ?_ Φ
  · intro μ
    fin_cases μ
    · exact smoothDeriv_cos θ
    · change 0 = -(0 * _); simp
    · change 0 = -(0 * _); simp
    · change 0 = -(0 * _); simp
  · intro μ
    fin_cases μ
    · exact smoothDeriv_sin θ
    · change 0 = 0 * _; simp
    · change 0 = 0 * _; simp
    · change 0 = 0 * _; simp

/-- **Full Smooth LHWR Chiral-Covariant Dirac Equation Preservation**:
If `(B, Φ)` solves the nonlinear LHWR real Dirac equation `D_B Φ = lhwrChiralMassVec κ Φ`
evaluated at `t : ℝ`, then for any smooth chiral gauge rotation `θ : SmoothRealFun`,
`(B - ∂θ, U(θ) Φ)` automatically solves the transformed LHWR equation at `t`. -/
theorem smooth_lhwr_dirac_solution_chiral_covariant (B : Fin 4 → SmoothRealFun)
    (θ : SmoothRealFun) (κ : ℝ) (Φ : Vec8Ring SmoothRealFun) (t : ℝ)
    (hsol : evalVec8 (chiralDiracOp SmoothRealFun smoothTemporalDerivs B Φ) t =
      lhwrChiralMassVec κ (evalVec8 Φ t)) :
    let U := smoothChiralGaugeUnit θ
    let dθ := fun μ : Fin 4 => smoothTemporalDerivs μ θ
    evalVec8 (chiralDiracOp SmoothRealFun smoothTemporalDerivs (fun μ => B μ - dθ μ) (U.val *ᵥ Φ)) t =
      lhwrChiralMassVec κ (evalVec8 (U.val *ᵥ Φ) t) := by
  intro U dθ
  rw [smooth_temporal_chiral_dirac_covariance B θ Φ]
  rw [evalVec8_smoothChiralGauge_inv, evalVec8_smoothChiralGauge, hsol]
  exact (lhwrChiralMassVec_chiralGauge_covariant κ (θ.val t) (evalVec8 Φ t)).symm

/-- **Dynamical Rodichev Torsion Bridge**:
Restricting `chiralDiracOp` with zero derivative (`zeroRingDeriv ℝ`) and covector chiral potential
`B_ν = -½ σ_ν` acting on `P_{j+1} Φ` equals Rodichev's totally skew-torsion triple-gamma term
`-(1 / 12) (∑_{a,μ,b} Φ_{[aμb]} Γ^μ Γ^a Γ^b) P_{j+1} Φ`. -/
theorem chiralDiracOp_potential_matches_rodichev_torsion (σ : Fin 4 → ℝ) (j : Fin 3)
    (Φ : Vec8R) :
    chiralDiracOp ℝ (fun _ => zeroRingDeriv ℝ) (fun ν => -(1 / 2 : ℝ) * σ ν)
        (quatPR j *ᵥ Φ) =
      ((∑ a : Fin 4, ∑ μ : Fin 4, ∑ b : Fin 4,
        rodichevTorsion σ a μ b • (gammaR μ * gammaR a * gammaR b)) *
          (-(1 / 12 : ℝ) • quatPR j)) *ᵥ Φ := by
  have hderiv : vec8Deriv (zeroRingDeriv ℝ) (quatPR j *ᵥ Φ) = 0 := by
    ext i
    rfl
  dsimp [chiralDiracOp]
  simp_rw [hderiv, zero_add]
  have hsum :
      (∑ ν : Fin 4, gammaLowR ν *ᵥ (((-(1 / 2 : ℝ) * σ ν) • gamma0123R) *ᵥ (quatPR j *ᵥ Φ))) =
        (∑ ν : Fin 4, gammaLowR ν * ((-(1 / 2 : ℝ) * σ ν) • gamma0123R) * quatPR j) *ᵥ Φ := by
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  change (∑ ν : Fin 4, gammaLowR ν *ᵥ
      (((-(1 / 2 : ℝ) * σ ν) • gamma0123R) *ᵥ (quatPR j *ᵥ Φ))) = _
  rw [hsum, chiral_soldering_matches_rodichev_torsion σ j]

end InfoGeometry.Clifford.LochakDiracChiralGaugeCovariance
