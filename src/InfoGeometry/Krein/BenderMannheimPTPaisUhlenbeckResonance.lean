/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.TwoSheetDiracMassEntropy
import InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
# Archetypes `MA₃`, `MA₄`, & `MA₅`: PT Symmetry, Krein Pseudo-Hermiticity, Bender–Mannheim Pais–Uhlenbeck Diagonalization, Jordan Resonance, & Negative Wigner Time Advance

Formalizes the quantum-mechanical, Krein-space, fourth-order Pais–Uhlenbeck, and
scattering-time-advance core of Philip Mannheim's lecture:

1. **Archetype `MA₃` — Wigner Antilinear Symmetry, Pseudo-Hermiticity, & 3-Phase PT Trichotomy**:
   - Wigner antilinear eigenvalue conjugation vs. unbroken real spectrum;
   - Mostafazadeh `IsPseudoHermitian η H` (`Hᴴ * η = η * H`) bridged directly to
     `InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis.kreinAdjoint`;
   - Biorthogonal orthogonality `(star E₁ - E₂) * ⟨ψ₁, η ψ₂⟩ = 0`;
   - Exact three-phase trichotomy of `benderPTMatrix r s θ`:
     unbroken distinct real eigenvalues + conserved positive `ptMetricV` form (`|r sin θ| < s`),
     exceptional Jordan cell similarity to `LogCftMonodromy.virasoroL0Cell` and non-diagonalizability
     (`s = r sin θ ≠ 0`), and broken complex-conjugate eigenvalues with null `pauliX2` norm
     (`0 ≤ s < |r sin θ|`).

2. **Archetype `MA₄` — Pais–Uhlenbeck Ghost Cancellation, `4 × 4` Symplectic Bender–Mannheim Similarity, & Equal-Frequency Jordan Resonance**:
   - Partial-fraction opposite-residue propagator identity vs. positive `d/d(m²)` equal-mass limit;
   - Exact `4 × 4` SymPy-verified symplectic transformation `puSympHalf` satisfying
     `Sᵀ J₄ S = J₄` and `Sᵀ M_PT S = diag(ω₁², 1, ω₁² ω₂², ω₁⁻²)` (positive entries for `0 < ω₂ < ω₁`),
     and `puSympFullᵀ M_PT puSympFull = M_PTᴴ`;
   - Equal-frequency companion matrix `paisUhlenbeckEqualDrift ω`: `(A² + ω² I) ≠ 0`,
     `(A² + ω² I)² = 0`, non-diagonalizability for `Q * R = 1`, and secular solution
     `(a + b * t) * cos (ω * t)` satisfying `(∂ₜ² + ω²)² = 0` but not `∂ₜ² + ω² = 0`.

3. **Archetype `MA₅` — PT Conjugate Poles, HWHM Scaling, & Negative Wigner Time Advance**:
   - Real Breit–Wigner Lorentzian from conjugate-pole difference and HWHM `Γ₂ √(√2 - 1)`;
   - Opposite-sign `HasDerivAt` phase derivatives: positive Breit–Wigner Wigner delay vs.
     strictly negative PT anti-pole time advance `-Γ₂ / ((E - E₀)² + Γ₂²)` and unitary
     Cayley-phase modulus `1`.
-/

noncomputable section

namespace InfoGeometry.Krein.BenderMannheimPTPaisUhlenbeckResonance

open Matrix Complex
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
open InfoGeometry.MetaCompiler

lemma right_inv_of_mul_eq_one {n : ℕ} {Q R : Matrix (Fin n) (Fin n) ℂ} (hQR : Q * R = 1) :
    R * Q = 1 := by
  have hQ_ne : Q.det ≠ 0 := by
    intro h0
    have hdet := congrArg Matrix.det hQR
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hdet
    exact zero_ne_one hdet
  have hdet : IsUnit Q.det := IsUnit.mk0 Q.det hQ_ne
  have hR : R = Q⁻¹ := by
    calc
      R = (Q⁻¹ * Q) * R := by rw [Matrix.nonsing_inv_mul Q hdet, Matrix.one_mul]
      _ = Q⁻¹ * (Q * R) := Matrix.mul_assoc _ _ _
      _ = Q⁻¹ := by rw [hQR, Matrix.mul_one]
  rw [hR]
  exact Matrix.nonsing_inv_mul Q hdet

/-! ## OpenGauss `T16`: Non-commutativity witness on `M₂(ℂ)` -/

/-- Closed `M₂(ℂ)` matrix non-commutativity witness for PT/Krein operators. -/
theorem pt_matrix2_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨!![(0 : ℂ), 1; 0, 0], !![(0 : ℂ), 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, mul_zero, add_zero, zero_add] at h00
  exact one_ne_zero h00

/-- Closed `M₄(ℂ)` matrix non-commutativity witness for Pais–Uhlenbeck operators. -/
theorem pt_matrix4_noncommutative :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A := by
  refine ⟨!![(0 : ℂ), 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0],
          !![(0 : ℂ), 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h00
  norm_num at h00

/-! ## Archetype `MA₃`: Wigner Antilinearity, Pseudo-Hermiticity & 3-Phase PT Matrix -/

section MA3_PTKrein

/-- `H` is `η`-pseudo-Hermitian (Mostafazadeh convention) when `Hᴴ * η = η * H`. -/
def IsPseudoHermitian {n : ℕ} (η H : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Hᴴ * η = η * H

/-- Complex `η`-sesquilinear pairing `⟨φ, η ψ⟩ = ∑ i, conj(φ i) * (η *ᵥ ψ) i`. -/
def pseudoInner {n : ℕ} (η : Matrix (Fin n) (Fin n) ℂ) (φ ψ : Fin n → ℂ) : ℂ :=
  dotProduct (star φ) (η *ᵥ ψ)

/-- First Pauli involution `σ₁` used as parity `P` on `ℂ²`. -/
def pauliX2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Bender's `2 × 2` PT-symmetric matrix `[r e^{iθ}, s; s, r e^{-iθ}]`. -/
def benderPTMatrix (r s θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(r : ℂ) * Complex.exp (Complex.I * θ), (s : ℂ);
     (s : ℂ), (r : ℂ) * Complex.exp (-Complex.I * θ)]

/-- Anti-Hermitian imaginary-diagonal core `[i a, s; s, -i a]`. -/
def ptTracelessCore (a s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I * (a : ℂ), (s : ℂ); (s : ℂ), -Complex.I * (a : ℂ)]

/-- Positive PT metric `V = ω⁻¹ [s, -i a; i a, s]` in the unbroken PT phase `|a| < s`. -/
def ptMetricV (a s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (s ^ 2 - a ^ 2) : ℂ))⁻¹ •
    !![(s : ℂ), -Complex.I * (a : ℂ); Complex.I * (a : ℂ), (s : ℂ)]

lemma pauliX2_sq : pauliX2 * pauliX2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX2, Matrix.mul_apply]

lemma pauliX2_hermitian : pauliX2ᴴ = pauliX2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX2, Matrix.conjTranspose_apply]

/-- **Wigner Antilinear Time-Reversal Theorem**:
If `T` is antilinear (`T (c • v) = conj c • T v`) and commutes with `H`:
1. Any eigenvector `H ψ = E • ψ` maps to a conjugate-eigenvalue vector `H (T ψ) = conj E • (T ψ)`;
2. When PT symmetry is unbroken on `ψ` (`ψ ≠ 0`, `T ψ = μ • ψ` with `μ ≠ 0`), `E` must be real
   (`star E = E`, i.e. `E.im = 0`). -/
theorem wigner_antilinear_time_reversal {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (T : (Fin n → ℂ) → (Fin n → ℂ))
    (hT_antilin : ∀ (c : ℂ) (v : Fin n → ℂ), T (c • v) = star c • T v)
    (hHT : ∀ v : Fin n → ℂ, H *ᵥ T v = T (H *ᵥ v))
    (ψ : Fin n → ℂ) (E : ℂ) (hEig : H *ᵥ ψ = E • ψ) :
    (H *ᵥ T ψ = star E • T ψ) ∧
    (∀ μ : ℂ, μ ≠ 0 → ψ ≠ 0 → T ψ = μ • ψ → star E = E ∧ E.im = 0) := by
  have hconj : H *ᵥ T ψ = star E • T ψ := by
    rw [hHT, hEig, hT_antilin]
  refine ⟨hconj, ?_⟩
  intro μ hμ hψ hfix
  have h1 : H *ᵥ T ψ = (μ * E) • ψ := by
    calc
      H *ᵥ T ψ = H *ᵥ (μ • ψ) := by rw [hfix]
      _ = μ • (H *ᵥ ψ) := Matrix.mulVec_smul H μ ψ
      _ = μ • (E • ψ) := by rw [hEig]
      _ = (μ * E) • ψ := smul_smul μ E ψ
  have h2 : H *ᵥ T ψ = (μ * star E) • ψ := by
    rw [hconj, hfix, smul_smul, mul_comm]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hψ
  have hcoord : (μ * E) * ψ i = (μ * star E) * ψ i := by
    have := congrFun (h1.symm.trans h2) i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have hE : E = star E :=
    mul_left_cancel₀ hμ (mul_right_cancel₀ hi hcoord)
  have him : E.im = -E.im := by
    have h0 := congrArg Complex.im hE
    simpa only [star_def, Complex.conj_im] using h0
  have him0 : E.im = 0 := by
    linarith
  exact ⟨hE.symm, him0⟩

lemma dotProduct_star_mulVec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (φ w : Fin n → ℂ) :
    dotProduct (star (H *ᵥ φ)) w = dotProduct (star φ) (Hᴴ *ᵥ w) := by
  have hvec : star (H *ᵥ φ) = Matrix.vecMul (star φ) Hᴴ := by
    ext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, mul_comm]
  rw [hvec, Matrix.dotProduct_mulVec]

/-- **Mostafazadeh–Krein Equivalence & `ClTower` Bridge**:
1. On `InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis.ClTower B n` with
   `γ₀² = 1`, `kreinAdjoint γ₀ n H = H` holds **if and only if** `star H * Γₙ = Γₙ * H`;
2. On `Mₙ(ℂ)`, `IsPseudoHermitian η H` (`Hᴴ η = η H`) implies biorthogonal orthogonality
   `(star E₁ - E₂) * ⟨ψ₁, η ψ₂⟩ = 0`, forcing zero `η`-norm when `E.im ≠ 0`. -/
theorem mostafazadeh_krein_and_biorthogonal_pairing :
    (∀ {B : Type} [Ring B] [StarRing B] {γ₀ : B}, γ₀ * γ₀ = 1 →
      ∀ (n : ℕ) (H : ClTower B n),
      kreinAdjoint γ₀ n H = H ↔ star H * kroneckerGamma γ₀ n = kroneckerGamma γ₀ n * H) ∧
    (∀ {n : ℕ} (η H : Matrix (Fin n) (Fin n) ℂ),
      IsPseudoHermitian η H → ∀ ψ₁ ψ₂ : Fin n → ℂ, ∀ E₁ E₂ : ℂ,
      H *ᵥ ψ₁ = E₁ • ψ₁ → H *ᵥ ψ₂ = E₂ • ψ₂ →
      (star E₁ - E₂) * pseudoInner η ψ₁ ψ₂ = 0) := by
  refine ⟨?_, ?_⟩
  · intro B _ _ γ₀ hsq n H
    have hΓ := kroneckerGamma_sq hsq n
    constructor
    · intro hK
      calc
        star H * kroneckerGamma γ₀ n
            = 1 * (star H * kroneckerGamma γ₀ n) := (one_mul _).symm
        _ = (kroneckerGamma γ₀ n * kroneckerGamma γ₀ n) * (star H * kroneckerGamma γ₀ n) := by
              rw [hΓ]
        _ = kroneckerGamma γ₀ n * (kroneckerGamma γ₀ n * star H * kroneckerGamma γ₀ n) := by
              simp only [mul_assoc]
        _ = kroneckerGamma γ₀ n * H := by
              simpa [kreinAdjoint] using congrArg (kroneckerGamma γ₀ n * ·) hK
    · intro hintertw
      dsimp [kreinAdjoint]
      calc
        kroneckerGamma γ₀ n * star H * kroneckerGamma γ₀ n
            = kroneckerGamma γ₀ n * (star H * kroneckerGamma γ₀ n) := mul_assoc _ _ _
        _ = kroneckerGamma γ₀ n * (kroneckerGamma γ₀ n * H) := by rw [hintertw]
        _ = (kroneckerGamma γ₀ n * kroneckerGamma γ₀ n) * H := (mul_assoc _ _ _).symm
        _ = H := by rw [hΓ, one_mul]
  · intro n η H hPH ψ₁ ψ₂ E₁ E₂ h1 h2
    have hLHS : star E₁ * pseudoInner η ψ₁ ψ₂ = dotProduct (star (H *ᵥ ψ₁)) (η *ᵥ ψ₂) := by
      rw [h1]
      unfold pseudoInner
      have hst : star (E₁ • ψ₁) = star E₁ • star ψ₁ := by
        ext i; simp
      rw [hst]
      simp [dotProduct, Finset.mul_sum, mul_assoc]
    have hMid : dotProduct (star (H *ᵥ ψ₁)) (η *ᵥ ψ₂) =
        dotProduct (star ψ₁) ((Hᴴ * η) *ᵥ ψ₂) := by
      rw [dotProduct_star_mulVec, Matrix.mulVec_mulVec]
    have hRHS : dotProduct (star ψ₁) ((Hᴴ * η) *ᵥ ψ₂) = E₂ * pseudoInner η ψ₁ ψ₂ := by
      rw [hPH, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul]
      unfold pseudoInner
      simp [dotProduct, Finset.mul_sum, mul_left_comm]
    calc
      (star E₁ - E₂) * pseudoInner η ψ₁ ψ₂
          = star E₁ * pseudoInner η ψ₁ ψ₂ - E₂ * pseudoInner η ψ₁ ψ₂ := sub_mul _ _ _
      _ = 0 := by rw [hLHS, hMid, hRHS, sub_self]

lemma benderPTMatrix_eq_shift (r s θ : ℝ) :
    benderPTMatrix r s θ =
      ((r * Real.cos θ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ptTracelessCore (r * Real.sin θ) s := by
  set c := Real.cos θ
  set sn := Real.sin θ
  have hexpPos : Complex.exp (Complex.I * (θ : ℂ)) = (c : ℂ) + Complex.I * (sn : ℂ) := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    dsimp [c, sn]
    ring
  have hexpNeg : Complex.exp (-(Complex.I * (θ : ℂ))) = (c : ℂ) - Complex.I * (sn : ℂ) := by
    have harg : -(Complex.I * (θ : ℂ)) = (((-θ : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    dsimp [c, sn]
    push_cast
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [benderPTMatrix, ptTracelessCore, hexpPos, hexpNeg] <;> ring

lemma benderPTMatrix_pauliX2_pseudoHermitian (r s θ : ℝ) :
    IsPseudoHermitian pauliX2 (benderPTMatrix r s θ) := by
  rw [IsPseudoHermitian, benderPTMatrix_eq_shift]
  set E₀ := r * Real.cos θ
  set a := r * Real.sin θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptTracelessCore, pauliX2, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Matrix.smul_apply, Complex.conj_ofReal]

lemma ptMetricV_hermitian (a s : ℝ) : (ptMetricV a s)ᴴ = ptMetricV a s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptMetricV, Matrix.conjTranspose_apply, Complex.conj_ofReal]

lemma ptMetricV_pseudoInner_formula {a s : ℝ} (ha : |a| < s) (ψ : Fin 2 → ℂ) :
    let ω := Real.sqrt (s ^ 2 - a ^ 2)
    let q := s * Complex.normSq (ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1) +
      ((s ^ 2 - a ^ 2) / s) * Complex.normSq (ψ 1)
    pseudoInner (ptMetricV a s) ψ ψ = ((q / ω : ℝ) : ℂ) := by
  have hs0 : s ≠ 0 := ne_of_gt (lt_of_le_of_lt (abs_nonneg a) ha)
  have hω_im_zero : ((Real.sqrt (s ^ 2 - a ^ 2) : ℂ))⁻¹ =
      (((Real.sqrt (s ^ 2 - a ^ 2))⁻¹ : ℝ) : ℂ) := by
    simp
  have hnorm (z : ℂ) : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
  have hconj_I : star (Complex.I : ℂ) = -Complex.I := by
    rw [Complex.star_def]; simp
  have hconj_real (x : ℝ) : star (x : ℂ) = (x : ℂ) := by
    rw [Complex.star_def]; simp
  have hquadC :
      (s : ℂ) * (star (ψ 0) * ψ 0 + star (ψ 1) * ψ 1) -
        Complex.I * (a : ℂ) * (star (ψ 0) * ψ 1 - star (ψ 1) * ψ 0) =
      ((s : ℂ) * (star (ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1) *
          (ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1)) +
        (((s ^ 2 - a ^ 2) / s : ℝ) : ℂ) * (star (ψ 1) * ψ 1)) := by
    have hconj0 : star (ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1) =
        star (ψ 0) + Complex.I * ((a / s : ℝ) : ℂ) * star (ψ 1) := by
      rw [star_sub, star_mul, star_mul, hconj_I, hconj_real]
      ring
    rw [hconj0]
    push_cast
    field_simp [hs0]
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold pseudoInner
  dsimp
  have hmulVec :
      dotProduct (star ψ) ((ptMetricV a s) *ᵥ ψ) =
        ((Real.sqrt (s ^ 2 - a ^ 2) : ℂ))⁻¹ *
          ((s : ℂ) * (star (ψ 0) * ψ 0 + star (ψ 1) * ψ 1) -
            Complex.I * (a : ℂ) * (star (ψ 0) * ψ 1 - star (ψ 1) * ψ 0)) := by
    simp [ptMetricV, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.smul_apply]
    ring
  rw [hmulVec, hquadC, hnorm, hnorm, hω_im_zero]
  push_cast
  ring

/-- **Bender Three-Phase PT Dichotomy & Exceptional Jordan Collapse**:
Let `H = benderPTMatrix r s θ`, `a = r sin θ`, and `E₀ = r cos θ`:
1. **Unbroken PT phase (`|a| < s`)**: `H` has distinct real eigenvalues `E₀ ± ω` (`ω = √(s² - a²)`),
   `ptMetricV a s` is Hermitian and intertwines `H` (`IsPseudoHermitian (ptMetricV a s) H`), and
   `pseudoInner (ptMetricV a s) ψ ψ` is real, non-negative, and vanishes iff `ψ = 0`;
2. **Exceptional point (`s = a ≠ 0`)**: `H` is similar via invertible `S` to
   `LogCftMonodromy.virasoroL0Cell (E₀ : ℂ)` (`det S = s ≠ 0`), `(H - E₀ • 1)² = 0` with
   `H - E₀ • 1 ≠ 0`, and `H` cannot be diagonalized by any `P, R` with `P * R = 1`;
3. **Broken PT phase (`0 ≤ s < |a|`)**: `H` has non-real complex-conjugate eigenvalues
   `E₀ ± i γ` (`γ = √(a² - s²) > 0`), and every eigenvector with `E.im ≠ 0` has null `pauliX2` norm
   `pseudoInner pauliX2 ψ ψ = 0`. -/
theorem benderPT_three_phase_trichotomy (r s θ : ℝ) :
    let a := r * Real.sin θ
    let E₀ := r * Real.cos θ
    let H := benderPTMatrix r s θ
    ((|a| < s →
      let ω := Real.sqrt (s ^ 2 - a ^ 2)
      0 < ω ∧
      (∃ vPos vNeg : Fin 2 → ℂ, vPos ≠ 0 ∧ vNeg ≠ 0 ∧
        H *ᵥ vPos = ((E₀ + ω : ℝ) : ℂ) • vPos ∧
        H *ᵥ vNeg = ((E₀ - ω : ℝ) : ℂ) • vNeg) ∧
      (ptMetricV a s)ᴴ = ptMetricV a s ∧
      IsPseudoHermitian (ptMetricV a s) H ∧
      ∀ ψ : Fin 2 → ℂ,
        (pseudoInner (ptMetricV a s) ψ ψ).im = 0 ∧
        0 ≤ (pseudoInner (ptMetricV a s) ψ ψ).re ∧
        (pseudoInner (ptMetricV a s) ψ ψ = 0 ↔ ψ = 0)) ∧
     (s = a → s ≠ 0 →
      let S : Matrix (Fin 2) (Fin 2) ℂ := !![(s : ℂ), 0; -Complex.I * (s : ℂ), 1]
      let Sinv : Matrix (Fin 2) (Fin 2) ℂ := !![((s : ℂ))⁻¹, 0; Complex.I, 1]
      S * Sinv = 1 ∧ Sinv * S = 1 ∧
      Sinv * H * S = virasoroL0Cell (E₀ : ℂ) ∧
      (H - (E₀ : ℂ) • 1) ^ 2 = 0 ∧ (H - (E₀ : ℂ) • 1) ≠ 0 ∧
      ¬ ∃ (P R : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℂ),
          P * R = 1 ∧ P * H * R = Matrix.diagonal d) ∧
     (0 ≤ s → s < |a| →
      let γ := Real.sqrt (a ^ 2 - s ^ 2)
      0 < γ ∧
      (∃ wPos wNeg : Fin 2 → ℂ, wPos ≠ 0 ∧ wNeg ≠ 0 ∧
        H *ᵥ wPos = ((E₀ : ℂ) + Complex.I * (γ : ℂ)) • wPos ∧
        H *ᵥ wNeg = ((E₀ : ℂ) - Complex.I * (γ : ℂ)) • wNeg) ∧
      ∀ ψ : Fin 2 → ℂ, ∀ E : ℂ,
        H *ᵥ ψ = E • ψ → E.im ≠ 0 → pseudoInner pauliX2 ψ ψ = 0)) := by
  intro a E₀ H
  have hH_shift : H = ((E₀ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + ptTracelessCore a s :=
    benderPTMatrix_eq_shift r s θ
  refine ⟨?_, ?_, ?_⟩
  · intro ha ω
    have hdiff_pos : 0 < s ^ 2 - a ^ 2 := by
      have hs0 : 0 < s := lt_of_le_of_lt (abs_nonneg a) ha
      nlinarith [abs_lt.mp ha]
    have hω_pos : 0 < ω := Real.sqrt_pos.mpr hdiff_pos
    have hω_sqC : (ω : ℂ) ^ 2 = (s : ℂ) ^ 2 - (a : ℂ) ^ 2 := by
      exact_mod_cast Real.sq_sqrt hdiff_pos.le
    have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt (abs_nonneg a) ha))
    refine ⟨hω_pos, ?_, ptMetricV_hermitian a s, ?_, ?_⟩
    · refine ⟨![(s : ℂ), (ω : ℂ) - Complex.I * (a : ℂ)],
        ![(s : ℂ), -(ω : ℂ) - Complex.I * (a : ℂ)], ?_, ?_, ?_, ?_⟩
      · intro h0
        have := congrFun h0 0
        exact hsC (by simpa using this)
      · intro h0
        have := congrFun h0 0
        exact hsC (by simpa using this)
      · rw [hH_shift]
        ext i
        fin_cases i
        · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
        · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          ring_nf
          rw [Complex.I_sq]
          linear_combination -hω_sqC
      · rw [hH_shift]
        ext i
        fin_cases i
        · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
        · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          ring_nf
          rw [Complex.I_sq]
          linear_combination -hω_sqC
    · rw [IsPseudoHermitian, hH_shift]
      set e0 := E₀
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ptMetricV, ptTracelessCore, Matrix.conjTranspose_apply, Matrix.mul_apply,
          Fin.sum_univ_two, Matrix.smul_apply, Complex.conj_ofReal] <;> ring
    · intro ψ
      have hform := ptMetricV_pseudoInner_formula ha ψ
      have hspos : 0 < s := lt_of_le_of_lt (abs_nonneg a) ha
      have hc0 : 0 ≤ s * Complex.normSq (ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1) :=
        mul_nonneg hspos.le (Complex.normSq_nonneg _)
      have hc1 : 0 ≤ ((s ^ 2 - a ^ 2) / s) * Complex.normSq (ψ 1) :=
        mul_nonneg (div_nonneg hdiff_pos.le hspos.le) (Complex.normSq_nonneg _)
      have hre : (pseudoInner (ptMetricV a s) ψ ψ).re =
          (s * Complex.normSq (ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1) +
            ((s ^ 2 - a ^ 2) / s) * Complex.normSq (ψ 1)) / ω := by
        rw [hform]; rfl
      have him : (pseudoInner (ptMetricV a s) ψ ψ).im = 0 := by
        rw [hform]; rfl
      refine ⟨him, ?_, ?_⟩
      · rw [hre]
        exact div_nonneg (add_nonneg hc0 hc1) hω_pos.le
      · constructor
        · intro hz
          have hz_re : (pseudoInner (ptMetricV a s) ψ ψ).re = 0 := by rw [hz]; rfl
          rw [hre, div_eq_zero_iff] at hz_re
          have hnum : s * Complex.normSq (ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1) +
              ((s ^ 2 - a ^ 2) / s) * Complex.normSq (ψ 1) = 0 :=
            hz_re.resolve_right (ne_of_gt hω_pos)
          have hterm1 : ((s ^ 2 - a ^ 2) / s) * Complex.normSq (ψ 1) = 0 := by linarith
          have hposcoef : 0 < (s ^ 2 - a ^ 2) / s := div_pos hdiff_pos hspos
          have hns1 : Complex.normSq (ψ 1) = 0 :=
            (mul_eq_zero.mp hterm1).resolve_left (ne_of_gt hposcoef)
          have hψ1 : ψ 1 = 0 := Complex.normSq_eq_zero.mp hns1
          have hterm0 : s * Complex.normSq (ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1) = 0 := by
            linarith
          have hns0 : Complex.normSq (ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1) = 0 :=
            (mul_eq_zero.mp hterm0).resolve_left (ne_of_gt hspos)
          have hψ0_sub : ψ 0 - Complex.I * ((a / s : ℝ) : ℂ) * ψ 1 = 0 :=
            Complex.normSq_eq_zero.mp hns0
          rw [hψ1, mul_zero, sub_zero] at hψ0_sub
          ext i
          fin_cases i
          · exact hψ0_sub
          · exact hψ1
        · intro hψ
          subst hψ
          unfold pseudoInner
          simp
  · intro hsa hs0 S Sinv
    have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0
    have hSS : S * Sinv = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [S, Sinv, Matrix.mul_apply, Fin.sum_univ_two, hsC]
    have hSS' : Sinv * S = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [S, Sinv, Matrix.mul_apply, Fin.sum_univ_two, hsC]
    have hsim : Sinv * H * S = virasoroL0Cell (E₀ : ℂ) := by
      rw [hH_shift, ← hsa]
      set e0 : ℝ := E₀
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [S, Sinv, ptTracelessCore, virasoroL0Cell, upperJordan, Matrix.mul_apply,
          Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.smul_apply]
         try field_simp [hsC]
         try ring_nf
         try rw [Complex.I_sq]
         try ring)
    have hMsq : (H - (E₀ : ℂ) • 1) ^ 2 = 0 := by
      rw [hH_shift, show ((E₀ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ptTracelessCore a s - (E₀ : ℂ) • 1 = ptTracelessCore a s by abel]
      rw [← hsa, pow_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ptTracelessCore, Matrix.mul_apply, Fin.sum_univ_two] <;>
        (ring_nf; try rw [Complex.I_sq]; try ring)
    have hMne : (H - (E₀ : ℂ) • 1) ≠ 0 := by
      intro hz
      have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hz
      have hshift : (H - (E₀ : ℂ) • 1) 0 1 = (s : ℂ) := by
        rw [hH_shift]
        simp [ptTracelessCore]
      rw [hshift] at h01
      exact hsC h01
    refine ⟨hSS, hSS', hsim, hMsq, hMne, ?_⟩
    rintro ⟨P, R, d, hPR, hdiag⟩
    have hRP : R * P = 1 := right_inv_of_mul_eq_one hPR
    let M : Matrix (Fin 2) (Fin 2) ℂ := H - (E₀ : ℂ) • 1
    have hPMR : P * M * R = Matrix.diagonal (fun i => d i - (E₀ : ℂ)) := by
      calc
        P * M * R = P * H * R - (E₀ : ℂ) • (P * R) := by
          simp [M, Matrix.mul_sub, Matrix.sub_mul]
        _ = Matrix.diagonal d - Matrix.diagonal (fun _ => (E₀ : ℂ)) := by
          rw [hdiag, hPR]
          ext i j; by_cases hij : i = j <;> simp [hij]
        _ = Matrix.diagonal (fun i => d i - (E₀ : ℂ)) := by
          ext i j; by_cases hij : i = j <;> simp [hij]
    have hPMR_sq : (P * M * R) ^ 2 = 0 := by
      calc
        (P * M * R) ^ 2 = (P * M * R) * (P * M * R) := pow_two _
        _ = P * (M * (R * P) * M) * R := by simp only [Matrix.mul_assoc]
        _ = P * (M * M) * R := by rw [hRP, Matrix.mul_one]
        _ = P * M ^ 2 * R := by rw [← pow_two]
        _ = 0 := by rw [hMsq, Matrix.mul_zero, Matrix.zero_mul]
    have hdiag_zero : P * M * R = 0 := by
      rw [pow_two, hPMR, Matrix.diagonal_mul_diagonal] at hPMR_sq
      ext i j
      by_cases hij : i = j
      · subst hij
        have hii := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X i i) hPMR_sq
        simp at hii
        rw [hPMR]
        simp [hii]
      · rw [hPMR]
        simp [hij]
    have hM_eq_zero : M = 0 := by
      calc
        M = (R * P) * M * (R * P) := by rw [hRP, Matrix.one_mul, Matrix.mul_one]
        _ = R * (P * M * R) * P := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hdiag_zero, Matrix.mul_zero, Matrix.zero_mul]
    exact hMne hM_eq_zero
  · intro hs0 hsa γ
    have ha2 : s ^ 2 < a ^ 2 := by
      rw [← sq_abs a]
      exact sq_lt_sq' (by linarith) hsa
    have hdiff_pos : 0 < a ^ 2 - s ^ 2 := by linarith
    have hγ_pos : 0 < γ := Real.sqrt_pos.mpr hdiff_pos
    have hγ_sqC : (γ : ℂ) ^ 2 = (a : ℂ) ^ 2 - (s : ℂ) ^ 2 := by
      exact_mod_cast Real.sq_sqrt hdiff_pos.le
    refine ⟨hγ_pos, ?_, ?_⟩
    · by_cases ha_nonneg : 0 ≤ a
      · have hsum_pos : 0 < a + γ := by linarith
        have hsum_ne : ((a + γ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hsum_pos)
        refine ⟨![((a + γ : ℝ) : ℂ), -Complex.I * (s : ℂ)],
          ![Complex.I * (s : ℂ), ((a + γ : ℝ) : ℂ)], ?_, ?_, ?_, ?_⟩
        · intro h0
          exact hsum_ne (by simpa using congrFun h0 0)
        · intro h0
          exact hsum_ne (by simpa using congrFun h0 1)
        · rw [hH_shift]
          ext i
          fin_cases i
          · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            linear_combination -Complex.I * hγ_sqC
          · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring_nf; rw [Complex.I_sq]; ring
        · rw [hH_shift]
          ext i
          fin_cases i
          · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring_nf; try rw [Complex.I_sq]; try ring
          · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring_nf; try rw [Complex.I_sq]
            linear_combination Complex.I * hγ_sqC
      · have ha_neg : a < 0 := lt_of_not_ge ha_nonneg
        have hsub_pos : 0 < γ - a := by linarith
        have hsub_ne : ((γ - a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hsub_pos)
        refine ⟨![-Complex.I * (s : ℂ), ((γ - a : ℝ) : ℂ)],
          ![((γ - a : ℝ) : ℂ), Complex.I * (s : ℂ)], ?_, ?_, ?_, ?_⟩
        · intro h0
          exact hsub_ne (by simpa using congrFun h0 1)
        · intro h0
          exact hsub_ne (by simpa using congrFun h0 0)
        · rw [hH_shift]
          ext i
          fin_cases i
          · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring_nf; rw [Complex.I_sq]; ring
          · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            linear_combination -Complex.I * hγ_sqC
        · rw [hH_shift]
          ext i
          fin_cases i
          · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring_nf; try rw [Complex.I_sq]
            linear_combination Complex.I * hγ_sqC
          · simp [ptTracelessCore, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
            ring_nf; try rw [Complex.I_sq]; try ring
    · intro ψ E hEig hIm
      have hbi := (mostafazadeh_krein_and_biorthogonal_pairing.2 pauliX2 H
        (benderPTMatrix_pauliX2_pseudoHermitian r s θ) ψ ψ E E hEig hEig)
      have hne : star E - E ≠ 0 := by
        intro hz
        have him := congrArg Complex.im hz
        simp at him
        exact hIm (by linarith)
      exact (mul_eq_zero.mp hbi).resolve_left hne

end MA3_PTKrein

/-! ## Archetype `MA₄`: Pais–Uhlenbeck Ghost Cancellation, $4\times 4$ Symplectic PT Similarity & Jordan Resonance -/

section MA4_PaisUhlenbeck

/-- Fourth-order scalar two-pole propagator `1 / ((k² - m₁²)(k² - m₂²))`. -/
def twoPolePropagator (kSq m1Sq m2Sq : ℝ) : ℝ :=
  1 / ((kSq - m1Sq) * (kSq - m2Sq))

/-- Canonical `4 × 4` symplectic matrix `J₄`. -/
def sympJ4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0;
     -1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, -1, 0]

/-- Bender–Mannheim PT-symmetric `4 × 4` quadratic Pais–Uhlenbeck Hamiltonian matrix `M_PT`. -/
def puMatrixPT (w₁ w₂ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(w₁ ^ 2 + w₂ ^ 2 : ℝ), 0, 0, Complex.I;
     0, 1, 0, 0;
     0, 0, (w₁ ^ 2 * w₂ ^ 2 : ℝ), 0;
     Complex.I, 0, 0, 0]

/-- Bender–Mannheim `Q`-metric generator matrix `A_Q = J₄ M_Q`. -/
def puGenAQ (w₁ w₂ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, ((w₁ * w₂ : ℝ) : ℂ)⁻¹;
     0, 0, -((w₁ * w₂ : ℝ) : ℂ), 0;
     0, ((w₁ * w₂ : ℝ) : ℂ)⁻¹, 0, 0;
     -((w₁ * w₂ : ℝ) : ℂ), 0, 0, 0]

/-- Symplectic similarity `S_half = exp(-Q/2)` transforming `M_PT` to positive diagonal form for `0 < w₂ < w₁`. -/
def puSympHalf (w₁ w₂ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let δ := Real.sqrt (w₁ ^ 2 - w₂ ^ 2)
  let c : ℂ := ((w₁ / δ : ℝ) : ℂ)
  let sh : ℂ := ((w₂ / δ : ℝ) : ℂ)
  c • (1 : Matrix (Fin 4) (Fin 4) ℂ) - (Complex.I * sh) • puGenAQ w₁ w₂

/-- Symplectic similarity `S_full = exp(-Q)` intertwining `M_PT` with `M_PTᴴ`. -/
def puSympFull (w₁ w₂ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let δ := Real.sqrt (w₁ ^ 2 - w₂ ^ 2)
  let c : ℂ := ((w₁ / δ : ℝ) : ℂ)
  let sh : ℂ := ((w₂ / δ : ℝ) : ℂ)
  (c ^ 2 + sh ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - (Complex.I * 2 * c * sh) • puGenAQ w₁ w₂

/-- Equal-frequency Pais–Uhlenbeck companion matrix for `(∂ₜ² + ω²)² x = 0`. -/
def paisUhlenbeckEqualDrift (ω : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1;
     -ω ^ 4, 0, -2 * ω ^ 2, 0]

/-- Secular equal-frequency Pais–Uhlenbeck resonance mode `(a + b t) cos (ω t)`. -/
def secularMode (a b ω t : ℝ) : ℝ :=
  (a + b * t) * Real.cos (ω * t)

/-- Second-order harmonic oscillator operator `(d²/dt² + ω²) f (t)`. -/
def oscOp (ω : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv f) t + ω ^ 2 * f t

/-- **Two-Pole Ghost Identity & Equal-Mass `d/d(m²)` Limit**:
1. Distinct-mass partial fractions separate with opposite residues `±1 / (m₁² - m₂²)`;
2. As `m₂² → m₁²`, the two-pole propagator converges to the double pole `1 / (k² - m₁²)² ≥ 0`,
   which equals the derivative `d/dm² [1 / (k² - m²)]` at `m² = m₁²`. -/
theorem paisUhlenbeck_propagator_limit_and_deriv
    {kSq m1Sq : ℝ} (hkm : kSq ≠ m1Sq) :
    (∀ m2Sq : ℝ, kSq ≠ m2Sq → m1Sq ≠ m2Sq →
      1 / ((m1Sq - m2Sq) * (kSq - m1Sq)) - 1 / ((m1Sq - m2Sq) * (kSq - m2Sq)) =
        twoPolePropagator kSq m1Sq m2Sq) ∧
    Filter.Tendsto (fun m2Sq : ℝ => twoPolePropagator kSq m1Sq m2Sq)
      (nhds m1Sq) (nhds (1 / (kSq - m1Sq) ^ 2)) ∧
    HasDerivAt (fun x : ℝ => 1 / (kSq - x)) (1 / (kSq - m1Sq) ^ 2) m1Sq := by
  have hdiff : kSq - m1Sq ≠ 0 := sub_ne_zero.mpr hkm
  refine ⟨?_, ?_, ?_⟩
  · intro m2Sq h2 h12
    have h2' : kSq - m2Sq ≠ 0 := sub_ne_zero.mpr h2
    have h12' : m1Sq - m2Sq ≠ 0 := sub_ne_zero.mpr h12
    unfold twoPolePropagator
    field_simp [hdiff, h2', h12']
    ring
  · have hcont : ContinuousAt (fun m2Sq : ℝ => twoPolePropagator kSq m1Sq m2Sq) m1Sq := by
      unfold twoPolePropagator
      refine ContinuousAt.div continuousAt_const ?_ (mul_ne_zero hdiff hdiff)
      exact continuousAt_const.mul (continuousAt_const.sub continuousAt_id)
    have hval : twoPolePropagator kSq m1Sq m1Sq = 1 / (kSq - m1Sq) ^ 2 := by
      unfold twoPolePropagator; ring
    simpa [hval] using hcont.tendsto
  · have hsub : HasDerivAt (fun x : ℝ => kSq - x) (-1) m1Sq := by
      convert (hasDerivAt_const m1Sq kSq).sub (hasDerivAt_id m1Sq) using 1
      · ext x; simp
      · ring
    have hinv : HasDerivAt (fun x : ℝ => 1 / (kSq - x)) ((-(-1 : ℝ)) / (kSq - m1Sq) ^ 2) m1Sq := by
      convert hsub.inv hdiff using 1
      ext x
      simp [one_div]
    refine hinv.congr_deriv ?_
    ring

/-- **Bender–Mannheim `4 × 4` Symplectic Similarity (`0 < ω₂ < ω₁`)**:
For unequal positive frequencies `0 < w₂ < w₁`:
1. `(puGenAQ w₁ w₂)² = -1`;
2. `puSympHalf` is symplectic (`Sᵀ J₄ S = J₄`) and similarity-congruence diagonalizes `puMatrixPT`
   to `diag(ω₁², 1, ω₁² ω₂², ω₁⁻²)` (every entry real and strictly positive);
3. `puSympFull` is symplectic (`Sᵀ J₄ S = J₄`) and maps `puMatrixPT w₁ w₂` to `(puMatrixPT w₁ w₂)ᴴ`. -/
theorem benderMannheim_pu_symplectic_diagonalization
    {w₁ w₂ : ℝ} (hw2 : 0 < w₂) (hw : w₂ < w₁) :
    (puGenAQ w₁ w₂) ^ 2 = -1 ∧
    (puSympHalf w₁ w₂)ᵀ * sympJ4 * (puSympHalf w₁ w₂) = sympJ4 ∧
    (puSympHalf w₁ w₂)ᵀ * (puMatrixPT w₁ w₂) * (puSympHalf w₁ w₂) =
      Matrix.diagonal ![((w₁ ^ 2 : ℝ) : ℂ), (1 : ℂ), ((w₁ ^ 2 * w₂ ^ 2 : ℝ) : ℂ),
        ((w₁ ^ 2 : ℝ) : ℂ)⁻¹] ∧
    (∀ i : Fin 4,
      0 < (![(w₁ ^ 2 : ℝ), (1 : ℝ), w₁ ^ 2 * w₂ ^ 2, (w₁ ^ 2)⁻¹] i)) ∧
    (puSympFull w₁ w₂)ᵀ * sympJ4 * (puSympFull w₁ w₂) = sympJ4 ∧
    (puSympFull w₁ w₂)ᵀ * (puMatrixPT w₁ w₂) * (puSympFull w₁ w₂) = (puMatrixPT w₁ w₂)ᴴ := by
  have hw1 : 0 < w₁ := lt_trans hw2 hw
  have hw1_ne : (w₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hw1)
  have hw2_ne : (w₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hw2)
  have hdiff_pos : 0 < w₁ ^ 2 - w₂ ^ 2 := by nlinarith
  have hδ_pos : 0 < Real.sqrt (w₁ ^ 2 - w₂ ^ 2) := Real.sqrt_pos.mpr hdiff_pos
  have hδ_ne : (Real.sqrt (w₁ ^ 2 - w₂ ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hδ_pos)
  have hδ_sq : (Real.sqrt (w₁ ^ 2 - w₂ ^ 2) : ℂ) ^ 2 = (w₁ : ℂ) ^ 2 - (w₂ : ℂ) ^ 2 := by
    exact_mod_cast Real.sq_sqrt hdiff_pos.le
  have hδ4 : (Real.sqrt (w₁ ^ 2 - w₂ ^ 2) : ℂ) ^ 4 = ((w₁ : ℂ) ^ 2 - (w₂ : ℂ) ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hδ_sq]
  have hI3 : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, Complex.I_sq]
    ring
  have hI4 : (Complex.I : ℂ) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Complex.I_sq]
    norm_num
  have hAQ : (puGenAQ w₁ w₂) ^ 2 = -1 := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [puGenAQ, Matrix.mul_apply, Fin.sum_univ_four]; try field_simp [hw1_ne, hw2_ne])
  have hJhalf : (puSympHalf w₁ w₂)ᵀ * sympJ4 * (puSympHalf w₁ w₂) = sympJ4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [puSympHalf, puGenAQ, sympJ4, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply]
    all_goals
      { field_simp [hw1_ne, hw2_ne, hδ_ne]
        ring_nf
        try rw [Complex.I_sq]
        try rw [hI3]
        try rw [hδ_sq]
        try ring }
  have hMhalf : (puSympHalf w₁ w₂)ᵀ * (puMatrixPT w₁ w₂) * (puSympHalf w₁ w₂) =
      Matrix.diagonal ![((w₁ ^ 2 : ℝ) : ℂ), (1 : ℂ), ((w₁ ^ 2 * w₂ ^ 2 : ℝ) : ℂ),
        ((w₁ ^ 2 : ℝ) : ℂ)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [puSympHalf, puGenAQ, puMatrixPT, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply]
    all_goals
      { field_simp [hw1_ne, hw2_ne, hδ_ne]
        ring_nf
        try rw [Complex.I_sq]
        try rw [hI3]
        try rw [hδ_sq]
        try ring }
  have hpos : ∀ i : Fin 4, 0 < (![(w₁ ^ 2 : ℝ), (1 : ℝ), w₁ ^ 2 * w₂ ^ 2, (w₁ ^ 2)⁻¹] i) := by
    intro i
    fin_cases i <;> simp <;> positivity
  have hJfull : (puSympFull w₁ w₂)ᵀ * sympJ4 * (puSympFull w₁ w₂) = sympJ4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [puSympFull, puGenAQ, sympJ4, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply]
    all_goals
      { field_simp [hw1_ne, hw2_ne, hδ_ne]
        ring_nf
        try rw [Complex.I_sq]
        try rw [hI3]
        try rw [hI4]
        try rw [hδ_sq]
        try rw [hδ4]
        try ring }
  have hMfull : (puSympFull w₁ w₂)ᵀ * (puMatrixPT w₁ w₂) * (puSympFull w₁ w₂) =
      (puMatrixPT w₁ w₂)ᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [puSympFull, puGenAQ, puMatrixPT, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_four, Matrix.sub_apply, Matrix.smul_apply]
    all_goals
      { field_simp [hw1_ne, hw2_ne, hδ_ne]
        ring_nf
        try rw [Complex.I_sq]
        try rw [hI3]
        try rw [hI4]
        try rw [hδ_sq]
        try rw [hδ4]
        try ring }
  exact ⟨hAQ, hJhalf, hMhalf, hpos, hJfull, hMfull⟩

/-- Involutive generator `G = -i A_Q` satisfying `G² = 1` for the Pais–Uhlenbeck similarity flow. -/
def puInvolutiveGen (w₁ w₂ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-Complex.I) • puGenAQ w₁ w₂

/-- Hyperbolic rapidity parameter `η = (1 / 2) log ((w₁ + w₂) / (w₁ - w₂))` for `0 < w₂ < w₁`. -/
def puRapidity (w₁ w₂ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((w₁ + w₂) / (w₁ - w₂))

private lemma ring_exp_involutive {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸]
    [CompleteSpace 𝔸] (G : 𝔸) (hG : G ^ 2 = 1) (t : ℝ) :
    NormedSpace.exp (t • G) = Real.cosh t • (1 : 𝔸) + Real.sinh t • G := by
  let E : ℝ → 𝔸 := fun s => NormedSpace.exp (s • (-G))
  let C : ℝ → 𝔸 := fun s => Real.cosh s • (1 : 𝔸) + Real.sinh s • G
  let F : ℝ → 𝔸 := fun s => E s * C s
  have hC_diff : ∀ s : ℝ, HasDerivAt C (Real.sinh s • (1 : 𝔸) + Real.cosh s • G) s := fun s =>
    ((Real.hasDerivAt_cosh s).smul_const (1 : 𝔸)).add ((Real.hasDerivAt_sinh s).smul_const G)
  have hE_diff : ∀ s : ℝ, HasDerivAt E (-(E s * G)) s := fun s => by
    simpa only [E, mul_neg] using hasDerivAt_exp_smul_const (𝕂 := ℝ) (-G) s
  have hG2 : G * G = 1 := by simpa only [pow_two] using hG
  have hF_diff : ∀ s : ℝ, HasDerivAt F 0 s := fun s => by
    have hprod := (hE_diff s).mul (hC_diff s)
    refine hprod.congr_deriv ?_
    have hGC : G * C s = Real.sinh s • (1 : 𝔸) + Real.cosh s • G := by
      dsimp only [C]
      rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, hG2, add_comm]
    rw [← hGC, neg_mul, ← mul_assoc, neg_add_cancel]
  have hF_const : F t = F 0 :=
    is_const_of_deriv_eq_zero (fun s => (hF_diff s).differentiableAt)
      (fun s => (hF_diff s).deriv) t 0
  have hF0 : F 0 = 1 := by
    dsimp only [F, E, C]
    simp [Real.cosh_zero, Real.sinh_zero, NormedSpace.exp_zero]
  have hEC : NormedSpace.exp ((-t) • G) * C t = 1 := by
    have h1 : NormedSpace.exp (t • (-G)) * C t = 1 := hF_const.trans hF0
    rwa [smul_neg, ← neg_smul] at h1
  have hcomm : Commute (t • G) ((-t) • G) := ((Commute.refl G).smul_left t).smul_right (-t)
  have hadd : NormedSpace.exp (t • G) * NormedSpace.exp ((-t) • G) = 1 := by
    rw [← NormedSpace.exp_add_of_commute hcomm, ← add_smul, add_neg_cancel, zero_smul,
      NormedSpace.exp_zero]
  calc
    NormedSpace.exp (t • G) = NormedSpace.exp (t • G) * 1 := (mul_one _).symm
    _ = NormedSpace.exp (t • G) * (NormedSpace.exp ((-t) • G) * C t) := by rw [hEC]
    _ = (NormedSpace.exp (t • G) * NormedSpace.exp ((-t) • G)) * C t := (mul_assoc _ _ _).symm
    _ = 1 * C t := by rw [hadd]
    _ = C t := one_mul _

private lemma matrix_exp_involutive {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G ^ 2 = 1) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • G) = (Real.cosh t : ℂ) • 1 + (Real.sinh t : ℂ) • G := by
  have hsmul : ∀ (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ), (r : ℂ) • M = r • M := by
    intro r M
    ext i j
    simp [Complex.real_smul]
  rw [hsmul t G, hsmul (Real.cosh t) 1, hsmul (Real.sinh t) G]
  open scoped Matrix.Norms.Operator in
  exact @ring_exp_involutive (Matrix (Fin n) (Fin n) ℂ) _ _
    (NormedAlgebra.restrictScalars ℚ ℝ (Matrix (Fin n) (Fin n) ℂ)) _ G hG t

/-- **Constructive Matrix Exponential Theorem for `puSympHalf` & `puSympFull` (`MA₄`)**:
For unequal positive frequencies `0 < w₂ < w₁`:
1. `puInvolutiveGen w₁ w₂ = -i A_Q` is a strict involution (`G² = 1`);
2. At rapidity `η := puRapidity w₁ w₂ = (1/2) log((w₁ + w₂)/(w₁ - w₂))`, `cosh η = w₁ / √(w₁² - w₂²)`
   and `sinh η = w₂ / √(w₁² - w₂²)`;
3. `NormedSpace.exp (η • puInvolutiveGen w₁ w₂) = puSympHalf w₁ w₂` and
   `NormedSpace.exp ((2 * η) • puInvolutiveGen w₁ w₂) = puSympFull w₁ w₂`, with
   `puSympHalf * puSympHalf = puSympFull` (genuine matrix exponential derivation replacing
   direct hyperbolic-entry parameterization). -/
theorem benderMannheim_pu_operator_exponential
    {w₁ w₂ : ℝ} (hw2 : 0 < w₂) (hw : w₂ < w₁) :
    (puInvolutiveGen w₁ w₂) ^ 2 = 1 ∧
    Real.cosh (puRapidity w₁ w₂) = w₁ / Real.sqrt (w₁ ^ 2 - w₂ ^ 2) ∧
    Real.sinh (puRapidity w₁ w₂) = w₂ / Real.sqrt (w₁ ^ 2 - w₂ ^ 2) ∧
    NormedSpace.exp ((puRapidity w₁ w₂ : ℂ) • puInvolutiveGen w₁ w₂) = puSympHalf w₁ w₂ ∧
    NormedSpace.exp (((2 * puRapidity w₁ w₂ : ℝ) : ℂ) • puInvolutiveGen w₁ w₂) = puSympFull w₁ w₂ ∧
    puSympHalf w₁ w₂ * puSympHalf w₁ w₂ = puSympFull w₁ w₂ := by
  have hw1 : 0 < w₁ := lt_trans hw2 hw
  have hplus_pos : 0 < w₁ + w₂ := add_pos hw1 hw2
  have hminus_pos : 0 < w₁ - w₂ := sub_pos.mpr hw
  have hdiff_pos : 0 < w₁ ^ 2 - w₂ ^ 2 := by nlinarith
  have hδ_pos : 0 < Real.sqrt (w₁ ^ 2 - w₂ ^ 2) := Real.sqrt_pos.mpr hdiff_pos
  have hAQ2 : (puGenAQ w₁ w₂) ^ 2 = -1 := (benderMannheim_pu_symplectic_diagonalization hw2 hw).1
  have hAQ_mul : puGenAQ w₁ w₂ * puGenAQ w₁ w₂ = -1 := by rwa [← pow_two]
  have hG2 : (puInvolutiveGen w₁ w₂) ^ 2 = 1 := by
    unfold puInvolutiveGen
    rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAQ_mul, smul_neg]
    simp
  set η := puRapidity w₁ w₂
  have hx_pos : 0 < (w₁ + w₂) / (w₁ - w₂) := div_pos hplus_pos hminus_pos
  have hη_pos_exp : Real.exp η = (w₁ + w₂) / Real.sqrt (w₁ ^ 2 - w₂ ^ 2) := by
    have hsq_eq : (Real.exp η) ^ 2 = ((w₁ + w₂) / Real.sqrt (w₁ ^ 2 - w₂ ^ 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have harg : (2 : ℝ) * η = Real.log ((w₁ + w₂) / (w₁ - w₂)) := by
        unfold η puRapidity
        ring
      rw [show ((2 : ℕ) : ℝ) * η = (2 : ℝ) * η by norm_num, harg, Real.exp_log hx_pos, div_pow,
        Real.sq_sqrt hdiff_pos.le]
      have hfac : w₁ ^ 2 - w₂ ^ 2 = (w₁ + w₂) * (w₁ - w₂) := by ring
      rw [hfac]
      field_simp [hplus_pos.ne', hminus_pos.ne']
    have hrhs_pos : 0 ≤ (w₁ + w₂) / Real.sqrt (w₁ ^ 2 - w₂ ^ 2) :=
      div_nonneg hplus_pos.le hδ_pos.le
    exact (sq_eq_sq₀ (Real.exp_pos η).le hrhs_pos).mp hsq_eq
  have hη_neg_exp : Real.exp (-η) = (w₁ - w₂) / Real.sqrt (w₁ ^ 2 - w₂ ^ 2) := by
    rw [Real.exp_neg, hη_pos_exp, inv_div]
    field_simp [hplus_pos.ne', hminus_pos.ne', hδ_pos.ne']
    have hsq := Real.sq_sqrt hdiff_pos.le
    nlinarith
  have hcosh : Real.cosh η = w₁ / Real.sqrt (w₁ ^ 2 - w₂ ^ 2) := by
    rw [Real.cosh_eq, hη_pos_exp, hη_neg_exp]
    field_simp [hδ_pos.ne']
    ring
  have hsinh : Real.sinh η = w₂ / Real.sqrt (w₁ ^ 2 - w₂ ^ 2) := by
    rw [Real.sinh_eq, hη_pos_exp, hη_neg_exp]
    field_simp [hδ_pos.ne']
    ring
  have hexp1 : NormedSpace.exp ((η : ℂ) • puInvolutiveGen w₁ w₂) = puSympHalf w₁ w₂ := by
    rw [matrix_exp_involutive (puInvolutiveGen w₁ w₂) hG2 η, hcosh, hsinh]
    unfold puSympHalf puInvolutiveGen
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_div]
    ring
  have hexp2 : NormedSpace.exp (((2 * η : ℝ) : ℂ) • puInvolutiveGen w₁ w₂) = puSympFull w₁ w₂ := by
    have hcomm : Commute ((η : ℂ) • puInvolutiveGen w₁ w₂) ((η : ℂ) • puInvolutiveGen w₁ w₂) :=
      Commute.refl _
    have h2 : (((2 * η : ℝ) : ℂ) • puInvolutiveGen w₁ w₂) =
        (η : ℂ) • puInvolutiveGen w₁ w₂ + (η : ℂ) • puInvolutiveGen w₁ w₂ := by
      rw [← add_smul]
      congr 1
      push_cast
      ring
    rw [h2, Matrix.exp_add_of_commute _ _ hcomm, hexp1]
    unfold puSympHalf puSympFull
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul]
    rw [hAQ_mul]
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hmul : puSympHalf w₁ w₂ * puSympHalf w₁ w₂ = puSympFull w₁ w₂ := by
    have hcomm : Commute ((η : ℂ) • puInvolutiveGen w₁ w₂) ((η : ℂ) • puInvolutiveGen w₁ w₂) :=
      Commute.refl _
    have h2 : (((2 * η : ℝ) : ℂ) • puInvolutiveGen w₁ w₂) =
        (η : ℂ) • puInvolutiveGen w₁ w₂ + (η : ℂ) • puInvolutiveGen w₁ w₂ := by
      rw [← add_smul]
      congr 1
      push_cast
      ring
    rw [← hexp1, ← Matrix.exp_add_of_commute _ _ hcomm, ← h2, hexp2]
  exact ⟨hG2, hcosh, hsinh, hexp1, hexp2, hmul⟩

lemma secularMode_deriv1 (a b ω t : ℝ) :
    deriv (secularMode a b ω) t = b * Real.cos (ω * t) - ω * (a + b * t) * Real.sin (ω * t) := by
  have h1 : HasDerivAt (fun x : ℝ => a + b * x) b t := by
    convert (hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul b) using 1
    · ext x; simp
    · ring
  have hlin : HasDerivAt (fun x : ℝ => ω * x) ω t := by
    convert (hasDerivAt_id t).const_mul ω using 1
    · ext x; simp
    · ring
  have h2 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * t) * ω) t :=
    (Real.hasDerivAt_cos (ω * t)).comp t hlin
  have htot : HasDerivAt (secularMode a b ω)
      (b * Real.cos (ω * t) + (a + b * t) * (-Real.sin (ω * t) * ω)) t :=
    h1.mul h2
  rw [htot.deriv]
  ring

lemma oscOp_secularMode (a b ω t : ℝ) :
    oscOp ω (secularMode a b ω) t = -2 * ω * b * Real.sin (ω * t) := by
  have hev : deriv (secularMode a b ω) =
      fun x : ℝ => b * Real.cos (ω * x) - ω * (a + b * x) * Real.sin (ω * x) := by
    ext x; exact secularMode_deriv1 a b ω x
  have hlin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ω * y) ω x := fun x => by
    convert (hasDerivAt_id x).const_mul ω using 1
    · ext y; simp
    · ring
  have hA : HasDerivAt (fun x : ℝ => b * Real.cos (ω * x))
      (b * (-Real.sin (ω * t) * ω)) t :=
    ((Real.hasDerivAt_cos (ω * t)).comp t (hlin t)).const_mul b
  have hL : HasDerivAt (fun x : ℝ => ω * (a + b * x)) (ω * b) t := by
    have h0 : HasDerivAt (fun x : ℝ => a + b * x) b t := by
      convert (hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul b) using 1
      · ext x; simp
      · ring
    exact h0.const_mul ω
  have hR : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * t) * ω) t :=
    (Real.hasDerivAt_sin (ω * t)).comp t (hlin t)
  have hB : HasDerivAt (fun x : ℝ => ω * (a + b * x) * Real.sin (ω * x))
      (ω * b * Real.sin (ω * t) + ω * (a + b * t) * (Real.cos (ω * t) * ω)) t :=
    hL.mul hR
  have htot : HasDerivAt (deriv (secularMode a b ω))
      (b * (-Real.sin (ω * t) * ω) -
        (ω * b * Real.sin (ω * t) + ω * (a + b * t) * (Real.cos (ω * t) * ω))) t := by
    rw [hev]
    exact hA.sub hB
  unfold oscOp
  rw [htot.deriv]
  unfold secularMode
  ring

/-- **Equal-Frequency Pais–Uhlenbeck Jordan Cell & Secular Linear-in-`t` Growth**:
1. The `4 × 4` companion matrix `A = paisUhlenbeckEqualDrift ω` satisfies
   `(A² + ω² I) ≠ 0` (`(0, 2)` entry is `1`) and `(A² + ω² I)² = 0` identically;
2. `A` is strictly non-diagonalizable: no `Q, R` with `Q * R = 1` satisfies `Q * A * R = diagonal d`;
3. In time domain, `secularMode a b ω t = (a + b t) cos (ω t)` solves `(∂ₜ² + ω²)² = 0`
   everywhere while failing `∂ₜ² + ω² = 0` at `t = π / (2 ω)` whenever `ω ≠ 0` and `b ≠ 0`. -/
theorem paisUhlenbeck_equalFreq_jordan_and_secular_resonance (ω : ℂ) :
    ((paisUhlenbeckEqualDrift ω) ^ 2 + ω ^ 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ) ≠ 0) ∧
    (((paisUhlenbeckEqualDrift ω) ^ 2 + ω ^ 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ^ 2 = 0) ∧
    (¬ ∃ (Q R : Matrix (Fin 4) (Fin 4) ℂ) (d : Fin 4 → ℂ),
        Q * R = 1 ∧ Q * paisUhlenbeckEqualDrift ω * R = Matrix.diagonal d) ∧
    (∀ a b ωr : ℝ,
      (∀ t : ℝ, oscOp ωr (oscOp ωr (secularMode a b ωr)) t = 0) ∧
      (ωr ≠ 0 → b ≠ 0 → oscOp ωr (secularMode a b ωr) (Real.pi / (2 * ωr)) ≠ 0)) := by
  let A := paisUhlenbeckEqualDrift ω
  let N := A ^ 2 + ω ^ 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ)
  have hN_ne : N ≠ 0 := by
    intro h0
    have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 2) h0
    simp [N, A, pow_two, paisUhlenbeckEqualDrift] at h02
  have hN_sq : N ^ 2 = 0 := by
    change (A ^ 2 + ω ^ 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ^ 2 = 0
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, pow_two, paisUhlenbeckEqualDrift, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  refine ⟨hN_ne, hN_sq, ?_, ?_⟩
  · rintro ⟨Q, R, d, hQR, hdiag⟩
    have hRQ : R * Q = 1 := right_inv_of_mul_eq_one hQR
    have hQNR : Q * N * R = Matrix.diagonal (fun i => d i ^ 2 + ω ^ 2) := by
      calc
        Q * N * R = Q * (A * A) * R + ω ^ 2 • (Q * R) := by
          simp [N, pow_two, Matrix.mul_add, Matrix.add_mul]
        _ = (Q * A * R) * (Q * A * R) + ω ^ 2 • 1 := by
          rw [hQR]
          have hassoc : Q * (A * A) * R = (Q * A * R) * (Q * A * R) := by
            calc
              Q * (A * A) * R = Q * (A * (1 * A)) * R := by rw [Matrix.one_mul]
              _ = Q * (A * ((R * Q) * A)) * R := by rw [hRQ]
              _ = (Q * A * R) * (Q * A * R) := by simp only [Matrix.mul_assoc]
          rw [hassoc]
        _ = Matrix.diagonal d * Matrix.diagonal d + Matrix.diagonal (fun _ => ω ^ 2) := by
          rw [hdiag]
          congr 1
          ext i j; by_cases hij : i = j <;> simp [hij]
        _ = Matrix.diagonal (fun i => d i ^ 2 + ω ^ 2) := by
          rw [Matrix.diagonal_mul_diagonal]
          ext i j; by_cases hij : i = j <;> simp [hij, pow_two]
    have hQNR_sq : (Q * N * R) ^ 2 = 0 := by
      calc
        (Q * N * R) ^ 2 = Q * (N * (R * Q) * N) * R := by
          simp only [pow_two, Matrix.mul_assoc]
        _ = Q * N ^ 2 * R := by rw [hRQ, Matrix.mul_one, ← pow_two]
        _ = 0 := by rw [hN_sq, Matrix.mul_zero, Matrix.zero_mul]
    have hD_zero : Q * N * R = 0 := by
      rw [hQNR, pow_two, Matrix.diagonal_mul_diagonal] at hQNR_sq
      ext i j
      by_cases hij : i = j
      · subst hij
        have hii := congrArg (fun X : Matrix (Fin 4) (Fin 4) ℂ => X i i) hQNR_sq
        simp at hii
        rw [hQNR]
        simp [hii]
      · rw [hQNR]; simp [hij]
    have hN_zero : N = 0 := by
      calc
        N = (R * Q) * N * (R * Q) := by rw [hRQ, Matrix.one_mul, Matrix.mul_one]
        _ = R * (Q * N * R) * Q := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hD_zero, Matrix.mul_zero, Matrix.zero_mul]
    exact hN_ne hN_zero
  · intro a b ωr
    have hev_osc : oscOp ωr (secularMode a b ωr) = fun t : ℝ => -2 * ωr * b * Real.sin (ωr * t) := by
      ext t; exact oscOp_secularMode a b ωr t
    refine ⟨?_, ?_⟩
    · intro t
      have hd1 : ∀ x : ℝ, deriv (oscOp ωr (secularMode a b ωr)) x =
          -2 * ωr ^ 2 * b * Real.cos (ωr * x) := by
        intro x
        have hlin : HasDerivAt (fun y : ℝ => ωr * y) ωr x := by
          convert (hasDerivAt_id x).const_mul ωr using 1
          · ext y; simp
          · ring
        have hder : HasDerivAt (fun y : ℝ => -2 * ωr * b * Real.sin (ωr * y))
            (-2 * ωr * b * (Real.cos (ωr * x) * ωr)) x :=
          ((Real.hasDerivAt_sin (ωr * x)).comp x hlin).const_mul (-2 * ωr * b)
        rw [hev_osc, hder.deriv]
        ring
      have hlin : HasDerivAt (fun y : ℝ => ωr * y) ωr t := by
        convert (hasDerivAt_id t).const_mul ωr using 1
        · ext y; simp
        · ring
      have hd2 : HasDerivAt (fun y : ℝ => -2 * ωr ^ 2 * b * Real.cos (ωr * y))
          (-2 * ωr ^ 2 * b * (-Real.sin (ωr * t) * ωr)) t :=
        ((Real.hasDerivAt_cos (ωr * t)).comp t hlin).const_mul (-2 * ωr ^ 2 * b)
      have hfun : deriv (oscOp ωr (secularMode a b ωr)) =
          fun x : ℝ => -2 * ωr ^ 2 * b * Real.cos (ωr * x) := funext hd1
      change deriv (deriv (oscOp ωr (secularMode a b ωr))) t +
        ωr ^ 2 * oscOp ωr (secularMode a b ωr) t = 0
      rw [hfun, hd2.deriv, hev_osc]
      ring
    · intro hω hb
      rw [hev_osc]
      dsimp only
      have harg : ωr * (Real.pi / (2 * ωr)) = Real.pi / 2 := by
        field_simp [hω]
      rw [harg, Real.sin_pi_div_two]
      intro hz
      have : -2 * ωr * b = 0 := by simpa using hz
      rcases mul_eq_zero.mp this with h2w | hb0
      · rcases mul_eq_zero.mp h2w with h2 | hw0
        · norm_num at h2
        · exact hω hw0
      · exact hb hb0

end MA4_PaisUhlenbeck

/-! ## Archetype `MA₅`: Conjugate Poles, Breit–Wigner HWHM & Negative Wigner Time Advance -/

section MA5_TimeAdvance

/-- Imaginary part from the difference of conjugate poles `(1 / (2 i)) ((z - iΓ)⁻¹ - (z + iΓ)⁻¹)`. -/
def conjPoleLorentzC (E E0 Γ₂ : ℝ) : ℂ :=
  (1 / (2 * Complex.I)) *
    (1 / (((E - E0 : ℝ) : ℂ) - Complex.I * (Γ₂ : ℂ)) -
     1 / (((E - E0 : ℝ) : ℂ) + Complex.I * (Γ₂ : ℂ)))

/-- Squared Breit–Wigner resonance profile `Γ₂⁴ / ((E - E₀)² + Γ₂²)²`. -/
def bwResonanceSq (E E0 Γ₂ : ℝ) : ℝ :=
  Γ₂ ^ 4 / ((E - E0) ^ 2 + Γ₂ ^ 2) ^ 2

/-- Standard Breit–Wigner scattering phase `arctan ((E - E₀) / Γ₂)`. -/
def breitWignerPhase (E0 Γ₂ E : ℝ) : ℝ :=
  Real.arctan ((E - E0) / Γ₂)

/-- Wrong-sign / PT anti-pole scattering phase `-arctan ((E - E₀) / Γ₂)`. -/
def ptAntiPolePhase (E0 Γ₂ E : ℝ) : ℝ :=
  -Real.arctan ((E - E0) / Γ₂)

/-- Cayley phase quotient `((E - E₀) - i Γ₂) / ((E - E₀) + i Γ₂)`. -/
def ptCayleyPhaseQuotient (E E0 Γ₂ : ℝ) : ℂ :=
  (((E - E0 : ℝ) : ℂ) - Complex.I * (Γ₂ : ℂ)) /
    (((E - E0 : ℝ) : ℂ) + Complex.I * (Γ₂ : ℂ))

/-- **PT Resonance Conjugate Poles, HWHM Scaling & Negative Wigner Time Advance**:
For any `Γ₂ > 0` and `(E, E₀ : ℝ)`:
1. The conjugate-pole difference has zero imaginary part and equals the real Lorentzian
   `Γ₂ / ((E - E₀)² + Γ₂²)`;
2. `bwResonanceSq E E₀ Γ₂ = 1 / 2` **if and only if** `(E - E₀)² = Γ₂² * (√2 - 1)`;
3. `breitWignerPhase` has positive `HasDerivAt` slope `+Γ₂ / ((E - E₀)² + Γ₂²) > 0` (time delay),
   while `ptAntiPolePhase` has strictly negative `HasDerivAt` slope
   `-Γ₂ / ((E - E₀)² + Γ₂²) < 0` (Wigner time advance);
4. Their sum vanishes (`breitWignerPhase + ptAntiPolePhase = 0`) and `‖ptCayleyPhaseQuotient E E₀ Γ₂‖ = 1`. -/
theorem pt_resonance_conjugate_poles_and_time_advance
    (E E0 Γ₂ : ℝ) (hΓ : 0 < Γ₂) :
    (conjPoleLorentzC E E0 Γ₂ = ((Γ₂ / ((E - E0) ^ 2 + Γ₂ ^ 2) : ℝ) : ℂ)) ∧
    (bwResonanceSq E E0 Γ₂ = 1 / 2 ↔ (E - E0) ^ 2 = Γ₂ ^ 2 * (Real.sqrt 2 - 1)) ∧
    HasDerivAt (breitWignerPhase E0 Γ₂) (Γ₂ / ((E - E0) ^ 2 + Γ₂ ^ 2)) E ∧
    HasDerivAt (ptAntiPolePhase E0 Γ₂) (-(Γ₂ / ((E - E0) ^ 2 + Γ₂ ^ 2))) E ∧
    (deriv (ptAntiPolePhase E0 Γ₂) E < 0 ∧ 0 < deriv (breitWignerPhase E0 Γ₂) E) ∧
    (breitWignerPhase E0 Γ₂ E + ptAntiPolePhase E0 Γ₂ E = 0 ∧
      ‖ptCayleyPhaseQuotient E E0 Γ₂‖ = 1) := by
  have hden_pos : 0 < (E - E0) ^ 2 + Γ₂ ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hΓ)
  have hden_ne : (E - E0) ^ 2 + Γ₂ ^ 2 ≠ 0 := ne_of_gt hden_pos
  have hΓ_ne : Γ₂ ≠ 0 := ne_of_gt hΓ
  have hm_ne : (((E - E0 : ℝ) : ℂ) - Complex.I * (Γ₂ : ℂ)) ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp at him
    exact hΓ_ne him
  have hp_ne : (((E - E0 : ℝ) : ℂ) + Complex.I * (Γ₂ : ℂ)) ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp at him
    exact hΓ_ne him
  have hdiffC : ((((E - E0 : ℝ) : ℂ) - Complex.I * (Γ₂ : ℂ)) *
      (((E - E0 : ℝ) : ℂ) + Complex.I * (Γ₂ : ℂ))) =
      (((E - E0) ^ 2 + Γ₂ ^ 2 : ℝ) : ℂ) := by
    push_cast
    calc
      ((E : ℂ) - (E0 : ℂ) - Complex.I * (Γ₂ : ℂ)) * ((E : ℂ) - (E0 : ℂ) + Complex.I * (Γ₂ : ℂ))
          = ((E : ℂ) - (E0 : ℂ)) ^ 2 - Complex.I ^ 2 * (Γ₂ : ℂ) ^ 2 := by ring
      _ = ((E : ℂ) - (E0 : ℂ)) ^ 2 + (Γ₂ : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
  have hconj : conjPoleLorentzC E E0 Γ₂ = ((Γ₂ / ((E - E0) ^ 2 + Γ₂ ^ 2) : ℝ) : ℂ) := by
    have hdenC : (((E - E0) ^ 2 + Γ₂ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden_ne
    have hnum : (1 / (((E - E0 : ℝ) : ℂ) - Complex.I * (Γ₂ : ℂ)) -
        1 / (((E - E0 : ℝ) : ℂ) + Complex.I * (Γ₂ : ℂ))) =
        (2 * Complex.I * (Γ₂ : ℂ)) / (((E - E0) ^ 2 + Γ₂ ^ 2 : ℝ) : ℂ) := by
      rw [div_sub_div _ _ hm_ne hp_ne, hdiffC]
      congr 1
      push_cast
      ring
    unfold conjPoleLorentzC
    rw [hnum]
    push_cast
    field_simp [Complex.I_ne_zero, hdenC]
  have hbw : bwResonanceSq E E0 Γ₂ = 1 / 2 ↔ (E - E0) ^ 2 = Γ₂ ^ 2 * (Real.sqrt 2 - 1) := by
    unfold bwResonanceSq
    have hsq_pos : 0 < ((E - E0) ^ 2 + Γ₂ ^ 2) ^ 2 := sq_pos_of_pos hden_pos
    have hsq_ne : ((E - E0) ^ 2 + Γ₂ ^ 2) ^ 2 ≠ 0 := ne_of_gt hsq_pos
    constructor
    · intro hEq
      have hcross : 2 * Γ₂ ^ 4 = ((E - E0) ^ 2 + Γ₂ ^ 2) ^ 2 := by
        rw [div_eq_div_iff hsq_ne (by norm_num)] at hEq
        linarith
      have hnonneg : 0 ≤ (E - E0) ^ 2 + Γ₂ ^ 2 := hden_pos.le
      have hrt : (E - E0) ^ 2 + Γ₂ ^ 2 = Real.sqrt (2 * Γ₂ ^ 4) := by
        rw [hcross, Real.sqrt_sq hnonneg]
      have hrt2 : Real.sqrt (2 * Γ₂ ^ 4) = Γ₂ ^ 2 * Real.sqrt 2 := by
        rw [mul_comm 2 (Γ₂ ^ 4), show Γ₂ ^ 4 = (Γ₂ ^ 2) ^ 2 by ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
      linarith
    · intro hdiff
      have hsum : (E - E0) ^ 2 + Γ₂ ^ 2 = Γ₂ ^ 2 * Real.sqrt 2 := by linarith
      rw [hsum]
      have hsq2 : (Γ₂ ^ 2 * Real.sqrt 2) ^ 2 = 2 * Γ₂ ^ 4 := by
        calc
          (Γ₂ ^ 2 * Real.sqrt 2) ^ 2 = Γ₂ ^ 4 * (Real.sqrt 2) ^ 2 := by ring
          _ = Γ₂ ^ 4 * 2 := by rw [Real.sq_sqrt (by norm_num)]
          _ = 2 * Γ₂ ^ 4 := by ring
      rw [hsq2]
      field_simp [hΓ_ne]
  have harg : HasDerivAt (fun x : ℝ => (x - E0) / Γ₂) (1 / Γ₂) E := by
    simpa [one_div] using ((hasDerivAt_id E).sub_const E0).div_const Γ₂
  have hderBW : HasDerivAt (breitWignerPhase E0 Γ₂) (Γ₂ / ((E - E0) ^ 2 + Γ₂ ^ 2)) E := by
    have hcomp := ((Real.hasDerivAt_arctan ((E - E0) / Γ₂)).comp E harg).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
    refine hcomp.congr_deriv ?_
    field_simp [hΓ_ne, hden_ne]
    ring
  have hderPT : HasDerivAt (ptAntiPolePhase E0 Γ₂) (-(Γ₂ / ((E - E0) ^ 2 + Γ₂ ^ 2))) E :=
    hderBW.neg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hslopes : deriv (ptAntiPolePhase E0 Γ₂) E < 0 ∧ 0 < deriv (breitWignerPhase E0 Γ₂) E := by
    rw [hderPT.deriv, hderBW.deriv]
    have hpos : 0 < Γ₂ / ((E - E0) ^ 2 + Γ₂ ^ 2) := div_pos hΓ hden_pos
    exact ⟨neg_lt_zero.mpr hpos, hpos⟩
  have hnorm : ‖ptCayleyPhaseQuotient E E0 Γ₂‖ = 1 := by
    unfold ptCayleyPhaseQuotient
    rw [norm_div, Complex.norm_def, Complex.norm_def]
    have hns_m : Complex.normSq (((E - E0 : ℝ) : ℂ) - Complex.I * (Γ₂ : ℂ)) =
        (E - E0) ^ 2 + Γ₂ ^ 2 := by
      have : (((E - E0 : ℝ) : ℂ) - Complex.I * (Γ₂ : ℂ)) = ⟨E - E0, -Γ₂⟩ := by
        apply Complex.ext <;> simp
      rw [this, Complex.normSq_apply]; ring
    have hns_p : Complex.normSq (((E - E0 : ℝ) : ℂ) + Complex.I * (Γ₂ : ℂ)) =
        (E - E0) ^ 2 + Γ₂ ^ 2 := by
      have : (((E - E0 : ℝ) : ℂ) + Complex.I * (Γ₂ : ℂ)) = ⟨E - E0, Γ₂⟩ := by
        apply Complex.ext <;> simp
      rw [this, Complex.normSq_apply]; ring
    rw [hns_m, hns_p]
    exact div_self (ne_of_gt (Real.sqrt_pos.mpr hden_pos))
  refine ⟨hconj, hbw, hderBW, hderPT, hslopes, ?_, hnorm⟩
  unfold breitWignerPhase ptAntiPolePhase
  ring

end MA5_TimeAdvance

/-! ## Archetype Registrations (`MA₃`, `MA₄`, `MA₅`) -/

section ArchetypeRegistrations

/-- Proved `TypedArchetype` for `MA₃`: Wigner antilinearity, Mostafazadeh/Krein equivalence,
and three-phase PT matrix trichotomy. -/
def archMA3AntilinearPTKrein : TypedArchetype Unit .proved where
  name := `archMA3AntilinearPTKrein
  phase := 3
  claim := fun _ =>
    (∀ {B : Type} [Ring B] [StarRing B] {γ₀ : B}, γ₀ * γ₀ = 1 →
      ∀ (n : ℕ) (H : ClTower B n),
      kreinAdjoint γ₀ n H = H ↔ star H * kroneckerGamma γ₀ n = kroneckerGamma γ₀ n * H) ∧
    (∀ r s θ : ℝ,
      let a := r * Real.sin θ
      let E₀ := r * Real.cos θ
      let H := benderPTMatrix r s θ
      (|a| < s → IsPseudoHermitian (ptMetricV a s) H ∧
        ∀ ψ : Fin 2 → ℂ, 0 ≤ (pseudoInner (ptMetricV a s) ψ ψ).re) ∧
      (s = a → s ≠ 0 →
        (H - (E₀ : ℂ) • 1) ^ 2 = 0 ∧ (H - (E₀ : ℂ) • 1) ≠ 0))
  evidence := fun _ =>
    ⟨fun hsq n H => mostafazadeh_krein_and_biorthogonal_pairing.1 hsq n H,
     fun r s θ =>
       let h := benderPT_three_phase_trichotomy r s θ
       ⟨fun ha => ⟨(h.1 ha).2.2.2.1, fun ψ => ((h.1 ha).2.2.2.2 ψ).2.1⟩,
        fun hsa hs0 => ⟨(h.2.1 hsa hs0).2.2.2.1, (h.2.1 hsa hs0).2.2.2.2.1⟩⟩⟩

/-- Proved `TypedArchetype` for `MA₄`: Pais–Uhlenbeck propagator limit, `4 × 4` symplectic
Bender–Mannheim diagonalization, and equal-frequency Jordan secular resonance. -/
def archMA4PaisUhlenbeckJordan : TypedArchetype Unit .proved where
  name := `archMA4PaisUhlenbeckJordan
  phase := 4
  claim := fun _ =>
    (∀ kSq m1Sq : ℝ, kSq ≠ m1Sq →
      HasDerivAt (fun x : ℝ => 1 / (kSq - x)) (1 / (kSq - m1Sq) ^ 2) m1Sq) ∧
    (∀ w₁ w₂ : ℝ, 0 < w₂ → w₂ < w₁ →
      NormedSpace.exp ((puRapidity w₁ w₂ : ℂ) • puInvolutiveGen w₁ w₂) = puSympHalf w₁ w₂ ∧
      NormedSpace.exp (((2 * puRapidity w₁ w₂ : ℝ) : ℂ) • puInvolutiveGen w₁ w₂) = puSympFull w₁ w₂ ∧
      (puSympHalf w₁ w₂)ᵀ * sympJ4 * (puSympHalf w₁ w₂) = sympJ4 ∧
      (puSympHalf w₁ w₂)ᵀ * (puMatrixPT w₁ w₂) * (puSympHalf w₁ w₂) =
        Matrix.diagonal ![((w₁ ^ 2 : ℝ) : ℂ), (1 : ℂ), ((w₁ ^ 2 * w₂ ^ 2 : ℝ) : ℂ),
          ((w₁ ^ 2 : ℝ) : ℂ)⁻¹] ∧
      (puSympFull w₁ w₂)ᵀ * (puMatrixPT w₁ w₂) * (puSympFull w₁ w₂) = (puMatrixPT w₁ w₂)ᴴ) ∧
    (∀ ω : ℂ,
      ((paisUhlenbeckEqualDrift ω) ^ 2 + ω ^ 2 • (1 : Matrix (Fin 4) (Fin 4) ℂ)) ^ 2 = 0 ∧
      ¬ ∃ (Q R : Matrix (Fin 4) (Fin 4) ℂ) (d : Fin 4 → ℂ),
          Q * R = 1 ∧ Q * paisUhlenbeckEqualDrift ω * R = Matrix.diagonal d)
  evidence := fun _ =>
    ⟨fun _ _ h => (paisUhlenbeck_propagator_limit_and_deriv h).2.2,
     fun _ _ hw2 hw =>
       let h := benderMannheim_pu_symplectic_diagonalization hw2 hw
       let hexp := benderMannheim_pu_operator_exponential hw2 hw
       ⟨hexp.2.2.2.1, hexp.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2.2⟩,
     fun ω =>
       let h := paisUhlenbeck_equalFreq_jordan_and_secular_resonance ω
       ⟨h.2.1, h.2.2.1⟩⟩

/-- Proved `TypedArchetype` for `MA₅`: PT conjugate-pole Lorentzian, HWHM scaling, and
negative Wigner phase-shift time advance. -/
def archMA5PTResonanceTimeAdvance : TypedArchetype Unit .proved where
  name := `archMA5PTResonanceTimeAdvance
  phase := 5
  claim := fun _ =>
    ∀ E E0 Γ₂ : ℝ, 0 < Γ₂ →
      conjPoleLorentzC E E0 Γ₂ = ((Γ₂ / ((E - E0) ^ 2 + Γ₂ ^ 2) : ℝ) : ℂ) ∧
      deriv (ptAntiPolePhase E0 Γ₂) E < 0 ∧
      0 < deriv (breitWignerPhase E0 Γ₂) E ∧
      ‖ptCayleyPhaseQuotient E E0 Γ₂‖ = 1
  evidence := fun _ E E0 Γ₂ hΓ =>
    let h := pt_resonance_conjugate_poles_and_time_advance E E0 Γ₂ hΓ
    ⟨h.1, h.2.2.2.2.1.1, h.2.2.2.2.1.2, h.2.2.2.2.2.2⟩

#register_archetype archMA3AntilinearPTKrein
#audit_archetype archMA3AntilinearPTKrein
#register_archetype archMA4PaisUhlenbeckJordan
#audit_archetype archMA4PaisUhlenbeckJordan
#register_archetype archMA5PTResonanceTimeAdvance
#audit_archetype archMA5PTResonanceTimeAdvance

end ArchetypeRegistrations

end InfoGeometry.Krein.BenderMannheimPTPaisUhlenbeckResonance
