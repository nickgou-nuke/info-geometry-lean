/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Noncommutative Tetraktys Flows, Clifford–Cayley Transform, and CPT Triad

Formalizes over an arbitrary noncommutative ring `[Ring A]` and star-ring
`[Ring A] [StarRing A]`:
1. The modular CPT automorphism triad `(P, T, C)` and Klein-four `Z₂ × Z₂`
   grading of `M₂(A) ≅ Cl(1,1) ⊗ A`.
2. The division-free Clifford–Cayley transform `C_Cayley = 1 + Ω` rotating
   clock `Γ₁` to shift `2•Σ` and mapping `(P₊, P₋)` to twin waves `1 ± Σ`.
3. Hyperbolic Mellin time-focusing `D(u) = diag(u, u⁻¹)` on `F₊, F₋`.
4. Noncommutative characteristic polynomial `X² = ι(c_Γ² + c_Σ² - c_Ω²) + Lie`
   and classification of hyperbolic, elliptic, parabolic, and loxodromic flows.
5. Two-stage chained Tetraktys 16-channel inversion on `M₂(M₂(A))`.
6. The Pythagorean `(1 + 2 + 3 + 4 = 10)` symplectic Tetraktys subalgebra
   `sp₄(A, ⋆) ⊂ M₂(M₂(A))` and its closure under the Lie bracket.
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeTetraktysFlows

/-!
## Foundational Infrastructure: 2 × 2 Noncommutative Operator Matrices & Cl(1,1) Atom
-/

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

/-- Explicit `2 × 2` matrix constructor avoiding `vecCons`/`vecMul` simp expansion. -/
def mat2 (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  fun i j => match i, j with
  | 0, 0 => a
  | 0, 1 => b
  | 1, 0 => c
  | 1, 1 => d

omit [Ring A] in @[simp] lemma mat2_00 (a b c d : A) : mat2 a b c d 0 0 = a := rfl
omit [Ring A] in @[simp] lemma mat2_01 (a b c d : A) : mat2 a b c d 0 1 = b := rfl
omit [Ring A] in @[simp] lemma mat2_10 (a b c d : A) : mat2 a b c d 1 0 = c := rfl
omit [Ring A] in @[simp] lemma mat2_11 (a b c d : A) : mat2 a b c d 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

omit [Ring A] in
@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
omit [Ring A] in
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
omit [Ring A] in
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
omit [Ring A] in
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

/-- The fundamental `Cl(1,1)` generators `(Γ₁, Σ, Ω)`, Source/Sink projectors `(P₊, P₋)`,
and Nilpotent Witt Twin-Wave operators `(F₊, F₋)`. -/
def gamma1Op : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp  : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp  : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def P_plus   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def P_minus  : Matrix (Fin 2) (Fin 2) A := mat2 0 0 0 1
def F_plus   : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def F_minus  : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

end Matrix2Simp

/-!
## Archetype T₁: Modular CPT Automorphism Triad & Klein-Four Z₂ × Z₂ Grading
-/

section ArchetypeT1_ModularCPTTriad

variable {A : Type*} [Ring A]

/-- Parity / Chirality involution `P(M) = Γ₁ M Γ₁`. -/
def cptP (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  gamma1Op * M * gamma1Op

/-- Time-reversal / Source-Sink swap involution `T(M) = Σ M Σ`. -/
def cptT (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  sigmaOp * M * sigmaOp

/-- Charge-conjugation / Symplectic inner involution `C(M) = -Ω M Ω = Ω M Ω⁻¹`. -/
def cptC (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  -(omegaOp * M * omegaOp)

/-- **Modular CPT Klein-Four Group Theorem (T₁)**:
In `M₂(A)` over any noncommutative ring `A`:
1. The `Cl(1,1)` triad satisfies the modular volume identity `Γ₁ Σ Ω = -1`,
2. `P, T, C` are involutions satisfying `P ∘ T = C`, `T ∘ C = P`, and `C ∘ P = T`,
3. The composite CPT action is the identity `P(T(C(M))) = M`. -/
theorem modular_cpt_klein_four_group (M : Matrix (Fin 2) (Fin 2) A) :
    (gamma1Op : Matrix (Fin 2) (Fin 2) A) * sigmaOp * omegaOp = 1 ∧
    cptP (cptP M) = M ∧
    cptT (cptT M) = M ∧
    cptC (cptC M) = M ∧
    cptP (cptT M) = cptC M ∧
    cptT (cptC M) = cptP M ∧
    cptC (cptP M) = cptT M ∧
    cptP (cptT (cptC M)) = M := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [cptP, cptT, cptC, gamma1Op, sigmaOp, omegaOp, Matrix.mul_apply, Fin.sum_univ_two])

end ArchetypeT1_ModularCPTTriad

/-!
## Archetype T₂: Clifford–Cayley Transform C_Cayley = 1 + Ω & Clock–Shift / Twin-Wave Duality
-/

section ArchetypeT2_CliffordCayleyTransform

variable {A : Type*} [Ring A] [StarRing A]

/-- Division-free Clifford–Cayley operator `C_Cayley = 1 + Ω`. -/
def cayleyOp : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp

/-- Symmetric and antisymmetric twin-wave defect projectors `Π_sym = 1 + Σ` and `Π_anti = 1 - Σ`. -/
def twinWaveSym  : Matrix (Fin 2) (Fin 2) A := 1 + sigmaOp
def twinWaveAnti : Matrix (Fin 2) (Fin 2) A := 1 - sigmaOp

/-- **Clifford–Cayley Clock–Shift & Source–Sink Twin-Wave Duality Theorem (T₂)**. -/
theorem clifford_cayley_clock_shift_and_twin_wave_duality :
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * cayleyOpᴴ = 2 • (1 : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A)ᴴ * cayleyOp = 2 • (1 : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * gamma1Op * cayleyOpᴴ = 2 • (sigmaOp : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * sigmaOp * cayleyOpᴴ = -(2 • (gamma1Op : Matrix (Fin 2) (Fin 2) A)) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * omegaOp * cayleyOpᴴ = 2 • (omegaOp : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * P_plus * cayleyOpᴴ = twinWaveSym ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * P_minus * cayleyOpᴴ = twinWaveAnti := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [cayleyOp, twinWaveSym, twinWaveAnti, gamma1Op, sigmaOp, omegaOp, P_plus, P_minus,
        two_smul])

end ArchetypeT2_CliffordCayleyTransform

/-!
## Archetype T₃: Hyperbolic Mellin Time-Focusing Flow on Source (0) & Sink (∞) Twin Waves
-/

section ArchetypeT3_HyperbolicTimeFocusingTwinWaves

variable {A : Type*} [Ring A]

/-- Noncommutative hyperbolic Mellin dilation / time-focusing operator `D(u) = diag(u, u⁻¹)`. -/
def mellinFocus (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  mat2 (u : A) 0 0 (↑u⁻¹ : A)

/-- **Hyperbolic Time-Focusing & Twin-Wave Casimir Theorem (T₃)**. -/
theorem hyperbolic_time_focusing_twin_waves (u : Aˣ) (a b : A) :
    mellinFocus u * (fiberEmbed a * F_plus) * mellinFocus u⁻¹ =
      fiberEmbed ((u : A) * a * (u : A)) * F_plus ∧
    mellinFocus u * (fiberEmbed b * F_minus) * mellinFocus u⁻¹ =
      fiberEmbed ((↑u⁻¹ : A) * b * (↑u⁻¹ : A)) * F_minus ∧
    (fiberEmbed ((u : A) * a * (u : A)) * F_plus) *
    (fiberEmbed ((↑u⁻¹ : A) * b * (↑u⁻¹ : A)) * F_minus) =
      fiberEmbed ((u : A) * a * b * (↑u⁻¹ : A)) * P_plus := by
  have h1 : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  refine ⟨?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_plus]
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_minus]
  · apply ext_fin2 <;> simp [fiberEmbed, F_plus, F_minus, P_plus]
    calc (u : A) * a * (u : A) * ((↑u⁻¹ : A) * b * (↑u⁻¹ : A))
      _ = (u : A) * a * ((u : A) * (↑u⁻¹ : A)) * b * (↑u⁻¹ : A) := by noncomm_ring
      _ = (u : A) * a * b * (↑u⁻¹ : A) := by rw [h1]; noncomm_ring

end ArchetypeT3_HyperbolicTimeFocusingTwinWaves

/-!
## Archetype T₄: Noncommutative Characteristic Polynomial & The Four Geometric Flows
-/

section ArchetypeT4_NoncommutativeCharpolyAndFourFlows

variable {A : Type*} [Ring A]

/-- General trace-free `Cl(1,1)` flow generator
`X_flow(cGamma, cSigma, cOmega) = ι(cGamma)Γ₁ + ι(cSigma)Σ + ι(cOmega)Ω`. -/
def flowGen (cGamma cSigma cOmega : A) : Matrix (Fin 2) (Fin 2) A :=
  fiberEmbed cGamma * gamma1Op + fiberEmbed cSigma * sigmaOp + fiberEmbed cOmega * omegaOp

/-- **Universal Noncommutative Characteristic Polynomial & Lie Cross-Product Obstruction (T₄ₐ)**. -/
theorem noncommutative_charpoly_casimir_and_lie_obstruction (cGamma cSigma cOmega : A) :
    flowGen cGamma cSigma cOmega * flowGen cGamma cSigma cOmega =
      fiberEmbed (cGamma * cGamma + cSigma * cSigma - cOmega * cOmega) * 1 +
      fiberEmbed ⁅cSigma, cOmega⁆ * gamma1Op +
      fiberEmbed ⁅cOmega, cGamma⁆ * sigmaOp -
      fiberEmbed ⁅cGamma, cSigma⁆ * omegaOp := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp] <;> noncomm_ring

/-- **Classification of the Four Canonical Geometric Operator Flows (T₄ᵦ)**. -/
theorem four_geometric_flows_classification (c_I a b : A) (hab : ⁅a, b⁆ = 0) :
    flowGen a 0 0 * flowGen a 0 0 = fiberEmbed (a * a) ∧
    flowGen 0 a 0 * flowGen 0 a 0 = fiberEmbed (a * a) ∧
    flowGen 0 0 a * flowGen 0 0 a = -fiberEmbed (a * a) ∧
    flowGen 0 a a = 2 • (fiberEmbed a * F_minus) ∧
    flowGen 0 a (-a) = 2 • (fiberEmbed a * F_plus) ∧
    flowGen 0 a a * flowGen 0 a a = 0 ∧
    (1 + flowGen 0 a a) * (1 - flowGen 0 a a) = 1 ∧
    ((fiberEmbed c_I + flowGen a 0 b) - fiberEmbed c_I) *
    ((fiberEmbed c_I + flowGen a 0 b) - fiberEmbed c_I) =
      fiberEmbed (a * a - b * b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp, F_minus, two_smul]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp, F_plus, two_smul]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · rw [add_sub_cancel_left, noncommutative_charpoly_casimir_and_lie_obstruction]
    have hba : ⁅b, a⁆ = 0 := by
      rw [Ring.lie_def] at hab ⊢
      calc b * a - a * b = -(a * b - b * a) := by noncomm_ring
      _ = 0 := by rw [hab, neg_zero]
    rw [hba]
    apply ext_fin2 <;> simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp, Ring.lie_def]

end ArchetypeT4_NoncommutativeCharpolyAndFourFlows

/-!
## Archetype T₅ & T₆: Chained Two-Stage Tetraktys Transform & The 10 + 6 = 16 Symplectic Split in M₂(M₂(A))
-/

section ArchetypeT5_T6_ChainedTetraktysAndSymplecticSplit

variable {A : Type*} [Ring A]

def peirceFiberLift (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * X * P_plus + sigmaOp * P_plus * X * P_plus * sigmaOp

def mellinCoeffI (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M + sigmaOp * M * sigmaOp)
def mellinCoeffGamma (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M - sigmaOp * M * sigmaOp)
def mellinCoeffSigma (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M * sigmaOp + sigmaOp * M)
def mellinCoeffOmega (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (sigmaOp * M - M * sigmaOp)

theorem clifford_mellin_walsh_inversion (M : Matrix (Fin 2) (Fin 2) A) :
    mellinCoeffI M * 1 +
    mellinCoeffGamma M * gamma1Op +
    mellinCoeffSigma M * sigmaOp +
    mellinCoeffOmega M * omegaOp = 2 • M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mellinCoeffI, mellinCoeffGamma, mellinCoeffSigma, mellinCoeffOmega,
      peirceFiberLift, P_plus, gamma1Op, sigmaOp, omegaOp, Matrix.mul_apply,
      Fin.sum_univ_two, two_smul] <;>
    noncomm_ring

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- Two-stage Chained Tetraktys mode extractor: applies an outer Mellin–Walsh projection `C_out`
followed by an inner Mellin–Walsh projection `C_in` on the `(0,0)` fiber block. -/
def tetraktysMode
    (C_out : NestedMat A → NestedMat A)
    (C_in : Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) A)
    (𝕄 : NestedMat A) : NestedMat A :=
  fiberEmbed (C_in (C_out 𝕄 0 0))

theorem outer_mode_inner_expansion
    (C_out : NestedMat A → NestedMat A) (𝕄 : NestedMat A)
    (h_diag : C_out 𝕄 = fiberEmbed (C_out 𝕄 0 0)) :
    tetraktysMode C_out mellinCoeffI 𝕄 * fiberEmbed 1 +
    tetraktysMode C_out mellinCoeffGamma 𝕄 * fiberEmbed gamma1Op +
    tetraktysMode C_out mellinCoeffSigma 𝕄 * fiberEmbed sigmaOp +
    tetraktysMode C_out mellinCoeffOmega 𝕄 * fiberEmbed omegaOp =
      2 • C_out 𝕄 := by
  have h_inv := clifford_mellin_walsh_inversion (C_out 𝕄 0 0)
  rw [h_diag]
  apply ext_fin2 <;> simp [tetraktysMode, fiberEmbed, two_smul]
  all_goals simpa [two_smul] using h_inv

/-- **Two-Stage Chained Tetraktys Reconstruction Theorem (T₅)**. -/
theorem chained_tetraktys_16_channel_inversion (𝕄 : NestedMat A) :
    (tetraktysMode mellinCoeffI mellinCoeffI 𝕄 * fiberEmbed 1 +
     tetraktysMode mellinCoeffI mellinCoeffGamma 𝕄 * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffI mellinCoeffSigma 𝕄 * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffI mellinCoeffOmega 𝕄 * fiberEmbed omegaOp) * 1 +
    (tetraktysMode mellinCoeffGamma mellinCoeffI 𝕄 * fiberEmbed 1 +
     tetraktysMode mellinCoeffGamma mellinCoeffGamma 𝕄 * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffGamma mellinCoeffSigma 𝕄 * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffGamma mellinCoeffOmega 𝕄 * fiberEmbed omegaOp) * gamma1Op +
    (tetraktysMode mellinCoeffSigma mellinCoeffI 𝕄 * fiberEmbed 1 +
     tetraktysMode mellinCoeffSigma mellinCoeffGamma 𝕄 * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffSigma mellinCoeffSigma 𝕄 * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffSigma mellinCoeffOmega 𝕄 * fiberEmbed omegaOp) * sigmaOp +
    (tetraktysMode mellinCoeffOmega mellinCoeffI 𝕄 * fiberEmbed 1 +
     tetraktysMode mellinCoeffOmega mellinCoeffGamma 𝕄 * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffOmega mellinCoeffSigma 𝕄 * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffOmega mellinCoeffOmega 𝕄 * fiberEmbed omegaOp) * omegaOp =
      4 • 𝕄 := by
  have hI : mellinCoeffI 𝕄 = fiberEmbed (mellinCoeffI 𝕄 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffI, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  have hGamma : mellinCoeffGamma 𝕄 = fiberEmbed (mellinCoeffGamma 𝕄 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffGamma, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  have hSigma : mellinCoeffSigma 𝕄 = fiberEmbed (mellinCoeffSigma 𝕄 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffSigma, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  have hOmega : mellinCoeffOmega 𝕄 = fiberEmbed (mellinCoeffOmega 𝕄 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffOmega, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  rw [outer_mode_inner_expansion mellinCoeffI 𝕄 hI,
      outer_mode_inner_expansion mellinCoeffGamma 𝕄 hGamma,
      outer_mode_inner_expansion mellinCoeffSigma 𝕄 hSigma,
      outer_mode_inner_expansion mellinCoeffOmega 𝕄 hOmega]
  have h_outer := clifford_mellin_walsh_inversion 𝕄
  calc (2 • mellinCoeffI 𝕄) * 1 + (2 • mellinCoeffGamma 𝕄) * gamma1Op +
       (2 • mellinCoeffSigma 𝕄) * sigmaOp + (2 • mellinCoeffOmega 𝕄) * omegaOp
    _ = 2 • (mellinCoeffI 𝕄 * 1 + mellinCoeffGamma 𝕄 * gamma1Op +
             mellinCoeffSigma 𝕄 * sigmaOp + mellinCoeffOmega 𝕄 * omegaOp) := by
        simp only [two_smul]; noncomm_ring
    _ = 2 • (2 • 𝕄) := by rw [h_outer]
    _ = 4 • 𝕄 := by rw [← mul_smul]; norm_num

section SymplecticTetraktysSplit

variable [StarRing A]

/-- Canonical 2-scale symplectic form `J = Ω ⊗ I ∈ M₂(M₂(A))`. -/
def J_sp : NestedMat A := omegaOp

/-- Predicate for an operator `𝕏 ∈ M₂(M₂(A))` to lie in the Hamiltonian symplectic Lie
algebra `sp₄(A, ⋆)`: `𝕏ᴴ * J + J * 𝕏 = 0`. -/
def IsSymplecticTetraktys (𝕏 : NestedMat A) : Prop :=
  𝕏ᴴ * J_sp + J_sp * 𝕏 = 0

/-- **The Pythagorean (1 + 2 + 3 + 4 = 10) Symplectic Tetraktys Theorem (T₆)**. -/
theorem pythagorean_ten_symplectic_tetraktys_generators :
    (∀ 𝕏 𝕐 : NestedMat A,
      IsSymplecticTetraktys 𝕏 → IsSymplecticTetraktys 𝕐 → IsSymplecticTetraktys ⁅𝕏, 𝕐⁆) ∧
    IsSymplecticTetraktys (fiberEmbed (omegaOp : Matrix (Fin 2) (Fin 2) A) * 1) ∧
    IsSymplecticTetraktys (fiberEmbed (1 : Matrix (Fin 2) (Fin 2) A) * gamma1Op) ∧
    IsSymplecticTetraktys (fiberEmbed (1 : Matrix (Fin 2) (Fin 2) A) * sigmaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (1 : Matrix (Fin 2) (Fin 2) A) * omegaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (gamma1Op : Matrix (Fin 2) (Fin 2) A) * omegaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (sigmaOp : Matrix (Fin 2) (Fin 2) A) * omegaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (gamma1Op : Matrix (Fin 2) (Fin 2) A) * gamma1Op) ∧
    IsSymplecticTetraktys (fiberEmbed (sigmaOp : Matrix (Fin 2) (Fin 2) A) * gamma1Op) ∧
    IsSymplecticTetraktys (fiberEmbed (gamma1Op : Matrix (Fin 2) (Fin 2) A) * sigmaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (sigmaOp : Matrix (Fin 2) (Fin 2) A) * sigmaOp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro 𝕏 𝕐 hX hY
    dsimp [IsSymplecticTetraktys] at *
    have hX' : 𝕏ᴴ * J_sp = -(J_sp * 𝕏) := eq_neg_of_add_eq_zero_left hX
    have hY' : 𝕐ᴴ * J_sp = -(J_sp * 𝕐) := eq_neg_of_add_eq_zero_left hY
    rw [Ring.lie_def]
    calc (𝕏 * 𝕐 - 𝕐 * 𝕏)ᴴ * J_sp + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏)
      _ = (𝕐ᴴ * 𝕏ᴴ - 𝕏ᴴ * 𝕐ᴴ) * J_sp + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by
          rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
      _ = 𝕐ᴴ * (𝕏ᴴ * J_sp) - 𝕏ᴴ * (𝕐ᴴ * J_sp) + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by noncomm_ring
      _ = 𝕐ᴴ * -(J_sp * 𝕏) - 𝕏ᴴ * -(J_sp * 𝕐) + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by rw [hX', hY']
      _ = -((𝕐ᴴ * J_sp) * 𝕏) + (𝕏ᴴ * J_sp) * 𝕐 + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by noncomm_ring
      _ = -(-(J_sp * 𝕐) * 𝕏) + -(J_sp * 𝕏) * 𝕐 + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by rw [hX', hY']
      _ = 0 := by noncomm_ring
  all_goals
    dsimp [IsSymplecticTetraktys, J_sp]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end SymplecticTetraktysSplit

end ArchetypeT5_T6_ChainedTetraktysAndSymplecticSplit


private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Algebra.NoncommutativeTetraktysFlows
