/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Noncommutative Analyticity, Chiral Hodge–Helmholtz, and Bimodule Jaynesian Synthesis

Formalizes over arbitrary noncommutative rings `[Ring B]` and `[Ring A] [StarRing A]`
the five causally ordered strata `H₁`–`H₅` without scalar or commuting reductions:
1. `H₁`: Coupled isotropic Witt sheets `(I₊, I₋)`, chiral Peirce sheets `(P₊, P₋)`,
   and complex-structure sheet reversal `-Ω P_± Ω = P_∓` in `M₂(A)`.
2. `H₂`: Bivector-rotor holomorphicity, division-free Hestenes Cauchy–Riemann
   projections `(∂_hol, ∂̄_anti)`, and the Kähler metric–symplectic pairing `ω_B`.
3. `H₃`: Square-zero chiral Hodge idempotents `(e_exact, e_coexact, e_harm)`,
   Dirac–Hodge kernel equivalence, and noncommutative Hilbert–Schmidt Helmholtz Pythagoras.
4. `H₄`: Noncommutative Leibniz derivations, left-trivialized Maurer–Cartan winding
   cocycle `ω_D(uv) = v⁻¹ ω_D(u) v + ω_D(v)`, and noncommutative bimodule Jaynesian
   Gibbs covariance over `Fin n → B`.
5. `H₅`: Noncommutative Cantor Markov harmonicity on `M₂(A)` and `2N`-horizon RG
   block-decimation invariance for arbitrary operator trajectories `ℕ → A`.
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeAnalyticitySynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

/-- Explicit `2 × 2` matrix constructor avoiding `vecCons`/`vecMul` simp expansion. -/
def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  fun i j => match i, j with
  | 0, 0 => a
  | 0, 1 => b
  | 1, 0 => c
  | 1, 1 => d

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

/-- Anticommutator `{X, Y} = X * Y + Y * X`. -/
def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

omit [Ring A] in @[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
omit [Ring A] in @[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
omit [Ring A] in @[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
omit [Ring A] in @[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

omit [Ring A] in @[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 0 = star (M 0 0) := rfl
omit [Ring A] in @[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 1 = star (M 1 0) := rfl
omit [Ring A] in @[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 0 = star (M 0 1) := rfl
omit [Ring A] in @[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op            : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp             : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp             : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def chiralSheetPlus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def chiralSheetMinus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 0 1
def isotropicSheetPlus  : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def fiberEmbed (a : A)  : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

end Matrix2Simp

/-!
## Stratum H₁: Coupled Isotropic Witt Sheets & Complex-Structure Sheet Reversal
-/

section StratumH1_CoupledIsotropicSheets

variable {A : Type*} [Ring A]

theorem isotropicSheetPlus_sq :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetPlus = 0 := by
  apply ext_fin2 <;> simp [isotropicSheetPlus]

theorem isotropicSheetMinus_sq :
    (isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetMinus = 0 := by
  apply ext_fin2 <;> simp [isotropicSheetMinus]

theorem isotropicSheetPlus_mul_minus :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetMinus = chiralSheetPlus := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, chiralSheetPlus]

theorem isotropicSheetMinus_mul_plus :
    (isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetPlus = chiralSheetMinus := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, chiralSheetMinus]

theorem isotropicSheets_anticommute :
    anticomm (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) isotropicSheetMinus = 1 ∧
    ⁅(isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A), isotropicSheetMinus⁆ =
      (gamma1Op : Matrix (Fin 2) (Fin 2) A) := by
  constructor
  · apply ext_fin2 <;> simp [anticomm, isotropicSheetPlus, isotropicSheetMinus]
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, gamma1Op]

theorem isotropicSheets_sum_eq_r0 :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) + isotropicSheetMinus = sigmaOp := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, sigmaOp]

theorem isotropicSheets_sub_eq_r5 :
    (isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A) - isotropicSheetPlus = omegaOp := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, omegaOp]

theorem complexStructure_reverses_chiral_sheets :
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * chiralSheetPlus * omegaOp) = chiralSheetMinus ∧
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * chiralSheetMinus * omegaOp) = chiralSheetPlus ∧
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * gamma1Op * omegaOp) = -gamma1Op ∧
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * isotropicSheetPlus * omegaOp) = -isotropicSheetMinus ∧
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * isotropicSheetMinus * omegaOp) = -isotropicSheetPlus := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [omegaOp, chiralSheetPlus, chiralSheetMinus, gamma1Op,
            isotropicSheetPlus, isotropicSheetMinus])

end StratumH1_CoupledIsotropicSheets

/-!
## Stratum H₂: Bivector-Rotor Holomorphicity & Kähler Metric–Symplectic Pairing
-/

section StratumH2_BivectorRotorAndKahler

def doubledSymplecticForm {R : Type*} [Ring R] [StarRing R] (B X Y : R) : R :=
  star X * B * Y

theorem doubledSymplecticForm_kahler_identities {R : Type*} [Ring R] [StarRing R]
    {B : R} (hB_sq : B * B = -1) (hB_sa : star B = -B) (X Y : R) :
    star (doubledSymplecticForm B X Y) = -doubledSymplecticForm B Y X ∧
    doubledSymplecticForm B X (B * Y) = -(star X * Y) ∧
    doubledSymplecticForm B (B * X) (B * Y) = doubledSymplecticForm B X Y := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [doubledSymplecticForm]
    simp only [star_mul, star_star, hB_sa]
    noncomm_ring
  · dsimp [doubledSymplecticForm]
    calc star X * B * (B * Y) = star X * (B * B) * Y := by noncomm_ring
      _ = star X * (-1) * Y := by rw [hB_sq]
      _ = -(star X * Y) := by noncomm_ring
  · dsimp [doubledSymplecticForm]
    simp only [star_mul, hB_sa]
    calc star X * -B * B * (B * Y) = -(star X * (B * B) * B * Y) := by noncomm_ring
      _ = -(star X * (-1) * B * Y) := by rw [hB_sq]
      _ = star X * B * Y := by noncomm_ring

variable {A : Type*} [Ring A]

def holomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M - omegaOp * M * omegaOp

def antiholomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M + omegaOp * M * omegaOp

theorem hestenes_cauchy_riemann_rotor_equivariance (M : Matrix (Fin 2) (Fin 2) A) :
    holomorphicProj M + antiholomorphicProj M = 2 • M ∧
    ⁅holomorphicProj M, (omegaOp : Matrix (Fin 2) (Fin 2) A)⁆ = 0 ∧
    anticomm (antiholomorphicProj M) (omegaOp : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    (⁅M, (omegaOp : Matrix (Fin 2) (Fin 2) A)⁆ = 0 ↔ antiholomorphicProj M = 0) := by
  have hO2 : (omegaOp : Matrix (Fin 2) (Fin 2) A) * omegaOp = -1 := by
    apply ext_fin2 <;> simp [omegaOp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [holomorphicProj, antiholomorphicProj]
    rw [two_smul]; noncomm_ring
  · rw [Ring.lie_def]; dsimp [holomorphicProj]
    calc (M - omegaOp * M * omegaOp) * omegaOp - omegaOp * (M - omegaOp * M * omegaOp)
      _ = M * omegaOp - omegaOp * M * (omegaOp * omegaOp) -
          omegaOp * M + (omegaOp * omegaOp) * M * omegaOp := by noncomm_ring
      _ = M * omegaOp - omegaOp * M * (-1) - omegaOp * M + (-1) * M * omegaOp := by rw [hO2]
      _ = 0 := by noncomm_ring
  · dsimp [anticomm, antiholomorphicProj]
    calc (M + omegaOp * M * omegaOp) * omegaOp + omegaOp * (M + omegaOp * M * omegaOp)
      _ = M * omegaOp + omegaOp * M * (omegaOp * omegaOp) +
          omegaOp * M + (omegaOp * omegaOp) * M * omegaOp := by noncomm_ring
      _ = M * omegaOp + omegaOp * M * (-1) + omegaOp * M + (-1) * M * omegaOp := by rw [hO2]
      _ = 0 := by noncomm_ring
  · rw [Ring.lie_def]; dsimp [antiholomorphicProj]
    constructor
    · intro h
      have hM : M * omegaOp = omegaOp * M := sub_eq_zero.mp h
      calc M + omegaOp * M * omegaOp
        _ = M + M * (omegaOp * omegaOp) := by rw [← hM, mul_assoc]
        _ = M + M * (-1) := by rw [hO2]
        _ = 0 := by noncomm_ring
    · intro h
      calc M * omegaOp - omegaOp * M
        _ = (M + omegaOp * M * omegaOp) * omegaOp -
            omegaOp * M * (omegaOp * omegaOp) - omegaOp * M := by noncomm_ring
        _ = 0 * omegaOp - omegaOp * M * (-1) - omegaOp * M := by rw [h, hO2]
        _ = 0 := by noncomm_ring

end StratumH2_BivectorRotorAndKahler

/-!
## Stratum H₃: Square-Zero Chiral Hodge Decomposition & Hilbert–Schmidt Helmholtz Pythagoras
-/

section StratumH3_SquareZeroChiralHodgeAndHelmholtz

variable {B : Type*} [Ring B]

def normalizedDirac (d δ : B) : B := d + δ

theorem square_zero_chiral_hodge_idempotents {d δ : B}
    (hd2 : d * d = 0) (hδ2 : δ * δ = 0)
    (hdδd : d * δ * d = d) (hδdδ : δ * d * δ = δ) (x : B) :
    let e_exact   := d * δ
    let e_coexact := δ * d
    let e_harm    := 1 - (d * δ + δ * d)
    e_exact * x + e_coexact * x + e_harm * x = x ∧
    e_exact * e_exact = e_exact ∧
    e_coexact * e_coexact = e_coexact ∧
    e_harm * e_harm = e_harm ∧
    e_exact * e_coexact = 0 ∧
    e_coexact * e_exact = 0 ∧
    e_exact * e_harm = 0 ∧
    e_coexact * e_harm = 0 := by
  refine ⟨by noncomm_ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (d * δ) * (d * δ) = (d * δ * d) * δ := by noncomm_ring
      _ = d * δ := by rw [hdδd]
  · calc (δ * d) * (δ * d) = (δ * d * δ) * d := by noncomm_ring
      _ = δ * d := by rw [hδdδ]
  · calc (1 - (d * δ + δ * d)) * (1 - (d * δ + δ * d))
      _ = 1 - 2 * (d * δ) - 2 * (δ * d) + (d * δ * d) * δ + (δ * d * δ) * d +
          d * (δ * δ) * d + δ * (d * d) * δ := by noncomm_ring
      _ = 1 - 2 * (d * δ) - 2 * (δ * d) + d * δ + δ * d +
          d * 0 * d + δ * 0 * δ := by rw [hdδd, hδdδ, hδ2, hd2]
      _ = 1 - (d * δ + δ * d) := by noncomm_ring
  · calc (d * δ) * (δ * d) = d * (δ * δ) * d := by noncomm_ring
      _ = d * 0 * d := by rw [hδ2]
      _ = 0 := by noncomm_ring
  · calc (δ * d) * (d * δ) = δ * (d * d) * δ := by noncomm_ring
      _ = δ * 0 * δ := by rw [hd2]
      _ = 0 := by noncomm_ring
  · calc (d * δ) * (1 - (d * δ + δ * d))
      _ = d * δ - (d * δ * d) * δ - d * (δ * δ) * d := by noncomm_ring
      _ = d * δ - d * δ - d * 0 * d := by rw [hdδd, hδ2]
      _ = 0 := by noncomm_ring
  · calc (δ * d) * (1 - (d * δ + δ * d))
      _ = δ * d - δ * (d * d) * δ - (δ * d * δ) * d := by noncomm_ring
      _ = δ * d - δ * 0 * δ - δ * d := by rw [hd2, hδdδ]
      _ = 0 := by noncomm_ring

theorem normalizedDirac_mul_eq_zero_iff_harmonic {d δ : B}
    (hd2 : d * d = 0) (hδ2 : δ * δ = 0)
    (hdδd : d * δ * d = d) (hδdδ : δ * d * δ = δ) (x : B) :
    (normalizedDirac d δ * x = 0 ↔ (d * x = 0 ∧ δ * x = 0)) ∧
    (normalizedDirac d δ * x = 0 ↔ (1 - (d * δ + δ * d)) * x = x) := by
  dsimp [normalizedDirac]
  have h_ker : (d + δ) * x = 0 ↔ (d * x = 0 ∧ δ * x = 0) := by
    constructor
    · intro h
      have hd : d * x = 0 := by
        calc d * x = (d * δ * d) * x + d * (δ * δ) * x := by rw [hdδd, hδ2]; noncomm_ring
          _ = d * δ * ((d + δ) * x) := by noncomm_ring
          _ = d * δ * 0 := by rw [h]
          _ = 0 := mul_zero _
      have hδ : δ * x = 0 := by
        calc δ * x = δ * (d * d) * x + (δ * d * δ) * x := by rw [hd2, hδdδ]; noncomm_ring
          _ = δ * d * ((d + δ) * x) := by noncomm_ring
          _ = δ * d * 0 := by rw [h]
          _ = 0 := mul_zero _
      exact ⟨hd, hδ⟩
    · rintro ⟨hd, hδ⟩
      calc (d + δ) * x = d * x + δ * x := add_mul d δ x
        _ = 0 + 0 := by rw [hd, hδ]
        _ = 0 := add_zero 0
  refine ⟨h_ker, ?_⟩
  rw [h_ker]
  constructor
  · rintro ⟨hd, hδ⟩
    calc (1 - (d * δ + δ * d)) * x
      _ = x - d * (δ * x) - δ * (d * x) := by noncomm_ring
      _ = x - d * 0 - δ * 0 := by rw [hd, hδ]
      _ = x := by noncomm_ring
  · intro hP
    have hd : d * x = 0 := by
      calc d * x = d * ((1 - (d * δ + δ * d)) * x) := by rw [hP]
        _ = (d - d * δ * d - (d * d) * δ) * x := by noncomm_ring
        _ = (d - d - 0 * δ) * x := by rw [hdδd, hd2]
        _ = 0 := by noncomm_ring
    have hδ : δ * x = 0 := by
      calc δ * x = δ * ((1 - (d * δ + δ * d)) * x) := by rw [hP]
        _ = (δ - (δ * δ) * d - δ * d * δ) * x := by noncomm_ring
        _ = (δ - 0 * d - δ) * x := by rw [hδ2, hδdδ]
        _ = 0 := by noncomm_ring
    exact ⟨hd, hδ⟩

/-- **Noncommutative Hilbert–Schmidt Helmholtz Orthogonality & Pythagoras**:
For scalar mode `S = diag(s, s)` and chiral mode `K = diag(k, -k)` in `M₂(A)`:
1. `Tr(Sᴴ K) = 0` and `Tr(Kᴴ S) = 0` (even when `s * k ≠ k * s`),
2. `K * S = S * K ↔ k * s = s * k`,
3. `Tr((S + K)ᴴ (S + K)) = Tr(Sᴴ S) + Tr(Kᴴ K)`. -/
theorem operator_helmholtz_duality_and_hilbert_schmidt_pythagoras
    {A : Type*} [Ring A] [StarRing A] (s k : A) :
    let S : Matrix (Fin 2) (Fin 2) A := mat2 s 0 0 s
    let K : Matrix (Fin 2) (Fin 2) A := mat2 k 0 0 (-k)
    Matrix.trace (Sᴴ * K) = 0 ∧
    Matrix.trace (Kᴴ * S) = 0 ∧
    (K * S = S * K ↔ k * s = s * k) ∧
    Matrix.trace ((S + K)ᴴ * (S + K)) =
      Matrix.trace (Sᴴ * S) + Matrix.trace (Kᴴ * K) := by
  refine ⟨by simp, by simp, ?_, by simp; noncomm_ring⟩
  constructor
  · intro h
    have h00 : (mat2 k 0 0 (-k) * mat2 s 0 0 s) 0 0 =
               (mat2 s 0 0 s * mat2 k 0 0 (-k)) 0 0 := by rw [h]
    simpa using h00
  · intro hks
    apply ext_fin2 <;> simp [hks]

end StratumH3_SquareZeroChiralHodgeAndHelmholtz

/-!
## Stratum H₄: Noncommutative Leibniz Derivations, Winding Cocycle & Jaynesian Gibbs Covariance
-/

section StratumH4_WindingCocycleAndJaynesGibbsCovariance

variable {B : Type*} [Ring B]

def IsRingDeriv (D : B →+ B) : Prop :=
  ∀ a b : B, D (a * b) = D a * b + a * D b

/-- Left-trivialized Maurer–Cartan winding 1-form `ω_D(u) = u⁻¹ D(u) ∈ B`. -/
def windingForm (D : B →+ B) (u : Bˣ) : B :=
  (↑u⁻¹ : B) * D (u : B)

/-- **Noncommutative Winding Cocycle Law**:
`ω_D(u v) = v⁻¹ ω_D(u) v + ω_D(v)` for any derivation `D` and units `u, v ∈ Bˣ`. -/
theorem windingForm_mul {D : B →+ B} (hD : IsRingDeriv D) (u v : Bˣ) :
    windingForm D (u * v) =
      (↑v⁻¹ : B) * windingForm D u * (v : B) + windingForm D v := by
  dsimp [windingForm]
  have h_inv : ((↑(u * v)⁻¹ : Bˣ) : B) = (↑v⁻¹ : B) * (↑u⁻¹ : B) := by
    rw [_root_.mul_inv_rev]; rfl
  have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  rw [h_inv, hD (u : B) (v : B)]
  calc (↑v⁻¹ : B) * (↑u⁻¹ : B) * (D (u : B) * (v : B) + (u : B) * D (v : B))
    _ = (↑v⁻¹ : B) * ((↑u⁻¹ : B) * D (u : B)) * (v : B) +
        (↑v⁻¹ : B) * ((↑u⁻¹ : B) * (u : B)) * D (v : B) := by noncomm_ring
    _ = (↑v⁻¹ : B) * ((↑u⁻¹ : B) * D (u : B)) * (v : B) +
        (↑v⁻¹ : B) * D (v : B) := by rw [hu]; noncomm_ring

/-- Right-weighted and left-weighted noncommutative Gibbs expectations and bimodule covariance. -/
def gibbsExpectationR {n : ℕ} (w f : Fin n → B) : B :=
  ∑ i : Fin n, f i * w i

def gibbsExpectationL {n : ℕ} (w g : Fin n → B) : B :=
  ∑ i : Fin n, w i * g i

def gibbsCrossMoment {n : ℕ} (w f g : Fin n → B) : B :=
  ∑ i : Fin n, f i * w i * g i

def gibbsCovariance {n : ℕ} (w f g : Fin n → B) : B :=
  ∑ i : Fin n, (f i - gibbsExpectationR w f) * w i * (g i - gibbsExpectationL w g)

/-- **Noncommutative Bimodule Jaynesian Gibbs Covariance Identity**:
For any operator weights `w : Fin n → B` satisfying `∑ i, w i = 1` and arbitrary
noncommuting observables `f, g : Fin n → B`,
`Cov_w(f, g) = ∑ i, f i * w i * g i - E_R(w, f) * E_L(w, g)`. -/
theorem winding_cocycle_and_jaynes_gibbs_covariance
    {D : B →+ B} (hD : IsRingDeriv D) (u v : Bˣ)
    {n : ℕ} (w f g : Fin n → B) (hw : ∑ i : Fin n, w i = 1) :
    windingForm D (u * v) =
      (↑v⁻¹ : B) * windingForm D u * (v : B) + windingForm D v ∧
    gibbsCovariance w f g =
      gibbsCrossMoment w f g - gibbsExpectationR w f * gibbsExpectationL w g := by
  refine ⟨windingForm_mul hD u v, ?_⟩
  dsimp [gibbsCovariance, gibbsCrossMoment]
  have h_expand : ∀ i : Fin n,
      (f i - gibbsExpectationR w f) * w i * (g i - gibbsExpectationL w g) =
      (f i * w i * g i - gibbsExpectationR w f * (w i * g i)) +
      (-(f i * w i) * gibbsExpectationL w g +
       gibbsExpectationR w f * w i * gibbsExpectationL w g) := fun i => by noncomm_ring
  simp_rw [h_expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  have h_neg : (∑ x : Fin n, -(f x * w x)) = -gibbsExpectationR w f := by
    dsimp [gibbsExpectationR]; rw [Finset.sum_neg_distrib]
  have h_L : (∑ x : Fin n, w x * g x) = gibbsExpectationL w g := rfl
  rw [h_neg, h_L, hw]
  noncomm_ring

end StratumH4_WindingCocycleAndJaynesGibbsCovariance

/-!
## Stratum H₅: Cantor Markov Harmonicity & Multi-Step RG Block-Decimation Invariance
-/

section StratumH5_CantorMarkovAndRGDecimation

variable {A : Type*} [Ring A]

def cantorMarkovStep (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  X + sigmaOp * X * sigmaOp

def cantorLaplacian (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  sigmaOp * X * sigmaOp - X

def IsCantorHarmonic (X : Matrix (Fin 2) (Fin 2) A) : Prop :=
  cantorMarkovStep X = 2 • X

/-- 2-to-1 Renormalization-Group (RG) block decimation on discrete-time operator trajectories. -/
def rgBlockStep {B : Type*} [Ring B] (X : ℕ → B) (k : ℕ) : B :=
  X (2 * k) + X (2 * k + 1)

/-- Cumulative trajectory sum over horizon `N`. -/
def trajectoryMean {B : Type*} [Ring B] (N : ℕ) (X : ℕ → B) : B :=
  ∑ k ∈ Finset.range N, X k

/-- **Cantor Markov Harmonicity & `2N`-Horizon RG Block-Decimation Theorem**:
1. `X ∈ M₂(A)` is Cantor-harmonic iff `Δ_Cantor(X) = 0`,
2. `Δ_Cantor(M_step(X)) = 0`,
3. For any operator trajectory `X : ℕ → A` and horizon `N ∈ ℕ`,
   `trajectoryMean N (rgBlockStep traj) = trajectoryMean (2 * N) traj`. -/
theorem cantor_markov_harmonicity_and_rg_invariance
    (X : Matrix (Fin 2) (Fin 2) A) (N : ℕ) (traj : ℕ → A) :
    (IsCantorHarmonic X ↔ cantorLaplacian X = 0) ∧
    cantorLaplacian (cantorMarkovStep X) = 0 ∧
    trajectoryMean N (rgBlockStep traj) = trajectoryMean (2 * N) traj := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [IsCantorHarmonic, cantorMarkovStep, cantorLaplacian]
    rw [two_smul]
    constructor
    · intro h
      calc sigmaOp * X * sigmaOp - X = (X + sigmaOp * X * sigmaOp) - (X + X) := by abel
        _ = 0 := by rw [h, sub_self]
    · intro h
      calc X + sigmaOp * X * sigmaOp = (X + X) + (sigmaOp * X * sigmaOp - X) := by abel
        _ = X + X := by rw [h, add_zero]
  · apply ext_fin2 <;> simp [cantorLaplacian, cantorMarkovStep, sigmaOp] <;> abel
  · dsimp [trajectoryMean, rgBlockStep]
    induction' N with N ih
    · simp
    · have h2N : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
      rw [Finset.sum_range_succ, ih, h2N, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]

end StratumH5_CantorMarkovAndRGDecimation


private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Algebra.NoncommutativeAnalyticitySynthesis
