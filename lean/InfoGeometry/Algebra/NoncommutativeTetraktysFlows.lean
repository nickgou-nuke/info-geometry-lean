/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.Canonical.ChiralSuperderivationColimit

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

set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

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

/-- In an additive `2`-torsion-free coefficient ring, the noncommutative
Tetraktys square is its scalar Casimir channel exactly when all three
coefficient commutators vanish. The torsion hypothesis is needed for the
converse: in characteristic two the `Σ` and `Ω` matrix directions coincide,
so their two off-diagonal obstruction coefficients cannot be separated. -/
theorem flowGen_square_eq_casimir_iff_commutators_zero
    [NoZeroSMulDivisors ℤ A] (cGamma cSigma cOmega : A) :
    flowGen cGamma cSigma cOmega * flowGen cGamma cSigma cOmega =
        fiberEmbed (cGamma * cGamma + cSigma * cSigma - cOmega * cOmega) * 1 ↔
      ⁅cSigma, cOmega⁆ = 0 ∧ ⁅cOmega, cGamma⁆ = 0 ∧ ⁅cGamma, cSigma⁆ = 0 := by
  constructor
  · intro h
    rw [noncommutative_charpoly_casimir_and_lie_obstruction] at h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0) h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 1) h
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 1 0) h
    simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp, mat2, Matrix.mul_apply,
      Fin.sum_univ_two, Ring.lie_def] at h00 h01 h10
    have hSigmaOmega : cSigma * cOmega - cOmega * cSigma = 0 := h00
    have hOmegaGammaPlus :
        (cOmega * cGamma - cGamma * cOmega) +
          (cGamma * cSigma - cSigma * cGamma) = 0 := by
      simpa [sub_eq_add_neg, add_assoc] using h01
    have hOmegaGammaMinus :
        (cOmega * cGamma - cGamma * cOmega) -
          (cGamma * cSigma - cSigma * cGamma) = 0 := by
      simpa [sub_eq_add_neg, add_assoc] using h10
    have hTwiceOmegaGamma :
        (2 : ℤ) • (cOmega * cGamma - cGamma * cOmega) = 0 := by
      rw [two_smul]
      calc (cOmega * cGamma - cGamma * cOmega) +
            (cOmega * cGamma - cGamma * cOmega) =
            ((cOmega * cGamma - cGamma * cOmega) +
              (cGamma * cSigma - cSigma * cGamma)) +
            ((cOmega * cGamma - cGamma * cOmega) -
              (cGamma * cSigma - cSigma * cGamma)) := by noncomm_ring
        _ = 0 := by rw [hOmegaGammaPlus, hOmegaGammaMinus]; simp
    have hOmegaGamma : cOmega * cGamma - cGamma * cOmega = 0 :=
      (smul_eq_zero.mp hTwiceOmegaGamma).resolve_left (by decide)
    have hGammaSigma : cGamma * cSigma - cSigma * cGamma = 0 := by
      rw [hOmegaGamma, zero_add] at hOmegaGammaPlus
      exact hOmegaGammaPlus
    exact ⟨hSigmaOmega, hOmegaGamma, hGammaSigma⟩
  · rintro ⟨hSigmaOmega, hOmegaGamma, hGammaSigma⟩
    rw [noncommutative_charpoly_casimir_and_lie_obstruction]
    simp only [Ring.lie_def]
    simp only [Ring.lie_def] at hSigmaOmega hOmegaGamma hGammaSigma
    rw [hSigmaOmega, hOmegaGamma, hGammaSigma]
    apply ext_fin2 <;>
      simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp, mat2, Matrix.mul_apply,
        Fin.sum_univ_two]

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

variable {A : Type*} [CommRing A]

/-- Anti-multiplicative sheet swap `τ(M) = Σ Mᵀ Σ` over a commutative coefficient
ring, where matrix transpose is genuinely anti-multiplicative.  Unlike the multiplicative
sheet-swap adjoint, double reversal cancels projector swapping on the odd
Peirce corners, so those corners are preserved rather than exchanged. -/
def antiSheetSwap (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  sigmaOp * M.transpose * sigmaOp

private theorem sigmaOp_sq : sigmaOp * sigmaOp = (1 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sigmaOp, mat2, Matrix.mul_apply, Fin.sum_univ_two]

theorem antiSheetSwap_mul (M N : Matrix (Fin 2) (Fin 2) A) :
    antiSheetSwap (M * N) = antiSheetSwap N * antiSheetSwap M := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [antiSheetSwap, sigmaOp, mat2, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two] <;> ring

theorem antiSheetSwap_P_plus : antiSheetSwap (P_plus (A := A)) = P_minus (A := A) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [antiSheetSwap, sigmaOp, P_plus, P_minus, mat2, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two]

theorem antiSheetSwap_P_minus : antiSheetSwap (P_minus (A := A)) = P_plus (A := A) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [antiSheetSwap, sigmaOp, P_plus, P_minus, mat2, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two]

/-- Row 4 of the Peirce involution table: product reversal and projector swap
cancel on the upper odd corner. -/
theorem antiSheetSwap_upper_corner (M : Matrix (Fin 2) (Fin 2) A) :
    antiSheetSwap (P_plus * M * P_minus) =
      P_plus * antiSheetSwap M * P_minus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [antiSheetSwap, sigmaOp, P_plus, P_minus, mat2, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two]

/-- The lower odd corner is preserved as well. -/
theorem antiSheetSwap_lower_corner (M : Matrix (Fin 2) (Fin 2) A) :
    antiSheetSwap (P_minus * M * P_plus) =
      P_minus * antiSheetSwap M * P_plus := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [antiSheetSwap, sigmaOp, P_plus, P_minus, mat2, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two]

/-- Nonzero fixed states exist in the odd corners, unlike rows 1--3. -/
theorem antiSheetSwap_F_plus_fixed : antiSheetSwap (F_plus (A := A)) = F_plus (A := A) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [antiSheetSwap, sigmaOp, F_plus, mat2, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two]

theorem antiSheetSwap_F_minus_fixed : antiSheetSwap (F_minus (A := A)) = F_minus (A := A) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [antiSheetSwap, sigmaOp, F_minus, mat2, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two]

/-!
## Archetype T₇: Noncommutative Symmetric/Antisymmetric `xp` Dilaton Split & Peirce Spine Coupling
-/

section ArchetypeT7_XPDilatonAndPeirceSpine

variable {A : Type*} [Ring A]

/-- Division-free symmetric `xp` dilaton channel `symDilaton2 x p = x * p + p * x`. -/
def symDilaton2 (x p : A) : A := x * p + p * x

/-- Antisymmetric Heisenberg/symplectic commutator channel `antisymComm x p = x * p - p * x`. -/
def antisymComm (x p : A) : A := x * p - p * x

theorem symDilaton2_swap (x p : A) : symDilaton2 x p = symDilaton2 p x := by
  dsimp [symDilaton2]
  exact add_comm (x * p) (p * x)

theorem antisymComm_swap (x p : A) : antisymComm x p = -antisymComm p x := by
  dsimp [antisymComm]
  noncomm_ring

theorem antisymComm_eq_lie (x p : A) : antisymComm x p = ⁅x, p⁆ := by
  dsimp [antisymComm]
  rw [Ring.lie_def]

/-- Exact division-free decomposition `2 * (x * p) = {x, p} + [x, p]`. -/
theorem two_mul_xp_eq_symDilaton2_add_antisymComm (x p : A) :
    2 * (x * p) = symDilaton2 x p + antisymComm x p := by
  dsimp [symDilaton2, antisymComm]
  noncomm_ring

/-- Exact division-free decomposition `2 * (p * x) = {x, p} - [x, p]`. -/
theorem two_mul_px_eq_symDilaton2_sub_antisymComm (x p : A) :
    2 * (p * x) = symDilaton2 x p - antisymComm x p := by
  dsimp [symDilaton2, antisymComm]
  noncomm_ring

theorem symDilaton2_star [StarRing A] (x p : A) (hx : star x = x) (hp : star p = p) :
    star (symDilaton2 x p) = symDilaton2 x p := by
  dsimp [symDilaton2]
  rw [star_add, star_mul, star_mul, hx, hp, add_comm]

theorem antisymComm_star [StarRing A] (x p : A) (hx : star x = x) (hp : star p = p) :
    star (antisymComm x p) = -antisymComm x p := by
  dsimp [antisymComm]
  rw [star_sub, star_mul, star_mul, hx, hp]
  noncomm_ring

/-- Exact commutator between the symmetric dilaton `{x, p}` and the antisymmetric `[x, p]`:
their noncommutativity obstruction equals `2 * ⁅p * x, x * p⁆`. -/
theorem lie_symDilaton2_antisymComm (x p : A) :
    ⁅symDilaton2 x p, antisymComm x p⁆ = 2 * ⁅p * x, x * p⁆ := by
  dsimp [symDilaton2, antisymComm]
  simp only [Ring.lie_def]
  noncomm_ring

/-- Embedding `(symDilaton2 x p, antisymComm x p, cOmega)` into `flowGen` produces the exact
Casimir scalar channel plus the three Lie curvature obstructions. -/
theorem flowGen_xp_dilaton_square (x p cOmega : A) :
    flowGen (symDilaton2 x p) (antisymComm x p) cOmega *
      flowGen (symDilaton2 x p) (antisymComm x p) cOmega =
      fiberEmbed (symDilaton2 x p * symDilaton2 x p +
        antisymComm x p * antisymComm x p - cOmega * cOmega) * 1 +
      fiberEmbed ⁅antisymComm x p, cOmega⁆ * gamma1Op +
      fiberEmbed ⁅cOmega, symDilaton2 x p⁆ * sigmaOp -
      fiberEmbed (2 * ⁅p * x, x * p⁆) * omegaOp := by
  rw [noncommutative_charpoly_casimir_and_lie_obstruction, lie_symDilaton2_antisymComm]

/-- Conjugation by `mellinFocus u` acts hyperbolically on the `symDilaton2` source channel
and `antisymComm` sink channel, and contracts them into the `P_plus` channel. -/
theorem xp_dilaton_commutator_mellinFocus (u : Aˣ) (x p : A) :
    mellinFocus u * (fiberEmbed (symDilaton2 x p) * F_plus) * mellinFocus u⁻¹ =
      fiberEmbed ((u : A) * symDilaton2 x p * (u : A)) * F_plus ∧
    mellinFocus u * (fiberEmbed (antisymComm x p) * F_minus) * mellinFocus u⁻¹ =
      fiberEmbed ((↑u⁻¹ : A) * antisymComm x p * (↑u⁻¹ : A)) * F_minus ∧
    (fiberEmbed ((u : A) * symDilaton2 x p * (u : A)) * F_plus) *
      (fiberEmbed ((↑u⁻¹ : A) * antisymComm x p * (↑u⁻¹ : A)) * F_minus) =
      fiberEmbed ((u : A) * symDilaton2 x p * antisymComm x p * (↑u⁻¹ : A)) * P_plus := by
  have h1 : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  refine ⟨?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_plus]
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_minus]
  · apply ext_fin2 <;> simp [fiberEmbed, F_plus, F_minus, P_plus]
    calc (u : A) * symDilaton2 x p * (u : A) * ((↑u⁻¹ : A) * antisymComm x p * (↑u⁻¹ : A))
      _ = (u : A) * symDilaton2 x p * ((u : A) * (↑u⁻¹ : A)) *
          antisymComm x p * (↑u⁻¹ : A) := by noncomm_ring
      _ = (u : A) * symDilaton2 x p * antisymComm x p * (↑u⁻¹ : A) := by
          rw [h1]; noncomm_ring

/-- `P_plus` is an idempotent in `Matrix (Fin 2) (Fin 2) A`, activating the PeirceSpine
Tetraktys superoperators and chiral superderivations directly on `M₂(A)`. -/
theorem P_plus_idempotent :
    (P_plus : Matrix (Fin 2) (Fin 2) A) * P_plus = P_plus := by
  apply ext_fin2 <;> simp [P_plus]

theorem one_sub_P_plus_eq_P_minus :
    (1 : Matrix (Fin 2) (Fin 2) A) - P_plus = P_minus := by
  apply ext_fin2 <;> simp [P_plus, P_minus]

theorem invS_P_plus_eq_gamma1Op :
    InfoGeometry.OperatorAlgebra.PeirceSpine.invS (P_plus : Matrix (Fin 2) (Fin 2) A) =
      gamma1Op := by
  apply ext_fin2 <;> simp [InfoGeometry.OperatorAlgebra.PeirceSpine.invS, P_plus, gamma1Op]

theorem conePlus_P_plus_symDilaton2 (x p : A) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus
        (P_plus : Matrix (Fin 2) (Fin 2) A) (mat2 0 (symDilaton2 x p) 0 0) =
      fiberEmbed (symDilaton2 x p) * F_plus := by
  apply ext_fin2 <;> simp [InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
    P_plus, fiberEmbed, F_plus]

theorem coneMinus_P_plus_antisymComm (x p : A) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus
        (P_plus : Matrix (Fin 2) (Fin 2) A) (mat2 0 0 (antisymComm x p) 0) =
      fiberEmbed (antisymComm x p) * F_minus := by
  apply ext_fin2 <;> simp [InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
    P_plus, fiberEmbed, F_minus]

/-- Explicit realization of the PeirceSpine Tetraktys operators `(V, Σ, Φ, J)`, Casimir
derivation, graded superderivations, and `ChiralSuperderivationColimit.oddSuperAnticommutator`
on the `(symDilaton2 x p, antisymComm x p)` channels in `Matrix (Fin 2) (Fin 2) A`. -/
theorem peirce_xp_tetraktys_and_supercharge (x p : A)
    (X : Matrix (Fin 2) (Fin 2) A) (b : Bool) :
    let P : Matrix (Fin 2) (Fin 2) A := P_plus
    let A_op : Matrix (Fin 2) (Fin 2) A := fiberEmbed (symDilaton2 x p) * F_plus
    let C_op : Matrix (Fin 2) (Fin 2) A := fiberEmbed (antisymComm x p) * F_minus
    InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A_op = A_op ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C_op = C_op ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A_op C_op =
      mat2 (symDilaton2 x p * antisymComm x p) 0 0 (antisymComm x p * symDilaton2 x p) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P A_op C_op =
      mat2 (symDilaton2 x p * antisymComm x p) 0 0 (-(antisymComm x p * symDilaton2 x p)) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A_op C_op =
      mat2 0 (symDilaton2 x p) (antisymComm x p) 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A_op C_op =
      mat2 0 (symDilaton2 x p) (-antisymComm x p) 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.derivCasimir P A_op C_op
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A_op C_op) = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.derivCasimir P A_op C_op
      (InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P A_op C_op) =
      -((8 : ℤ) • (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A_op C_op *
        InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P A_op C_op)) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.superDerivPlus P A_op
      (InfoGeometry.OperatorAlgebra.PeirceSpine.superDerivMinus P C_op X) +
    InfoGeometry.OperatorAlgebra.PeirceSpine.superDerivMinus P C_op
      (InfoGeometry.OperatorAlgebra.PeirceSpine.superDerivPlus P A_op X) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A_op C_op) X ∧
    InfoGeometry.Canonical.ChiralSuperderivationColimit.oddSuperAnticommutator
      A_op C_op X b =
      InfoGeometry.Canonical.ChiralSuperderivationColimit.innerDerivation
        (InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A_op C_op) X := by
  intro P A_op C_op
  have hP : P * P = P := P_plus_idempotent
  have hPlus : InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus P A_op = A_op := by
    apply ext_fin2 <;> simp [InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      P, A_op, P_plus, fiberEmbed, F_plus]
  have hMinus : InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus P C_op = C_op := by
    apply ext_fin2 <;> simp [InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
      P, C_op, P_plus, fiberEmbed, F_minus]
  have hV : InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A_op C_op =
      mat2 (symDilaton2 x p * antisymComm x p) 0 0 (antisymComm x p * symDilaton2 x p) := by
    apply ext_fin2 <;> simp [InfoGeometry.OperatorAlgebra.PeirceSpine.genV,
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
      P, A_op, C_op, P_plus, fiberEmbed, F_plus, F_minus]
  have hSig : InfoGeometry.OperatorAlgebra.PeirceSpine.genSig P A_op C_op =
      mat2 (symDilaton2 x p * antisymComm x p) 0 0 (-(antisymComm x p * symDilaton2 x p)) := by
    apply ext_fin2 <;> simp [InfoGeometry.OperatorAlgebra.PeirceSpine.genSig,
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
      P, A_op, C_op, P_plus, fiberEmbed, F_plus, F_minus]
  have hPhi : InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi P A_op C_op =
      mat2 0 (symDilaton2 x p) (antisymComm x p) 0 := by
    apply ext_fin2 <;> simp [InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
      P, A_op, C_op, P_plus, fiberEmbed, F_plus, F_minus]
  have hJ : InfoGeometry.OperatorAlgebra.PeirceSpine.genJ P A_op C_op =
      mat2 0 (symDilaton2 x p) (-antisymComm x p) 0 := by
    apply ext_fin2 <;> simp [InfoGeometry.OperatorAlgebra.PeirceSpine.genJ,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
      P, A_op, C_op, P_plus, fiberEmbed, F_plus, F_minus]
  have hCas := InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A10_casimir_and_superoperator_commutators
    hP A_op C_op
  have hSuper := InfoGeometry.OperatorAlgebra.PeirceSpine.archetype_A28_graded_derivations
    hP A_op C_op X X
  have hOdd := InfoGeometry.Canonical.ChiralSuperderivationColimit.oddSuperAnticommutator_eq_innerDerivation
    A_op C_op X b
  have hSum : A_op * C_op + C_op * A_op =
      InfoGeometry.OperatorAlgebra.PeirceSpine.genV P A_op C_op := by
    simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.genV,
      InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm, hPlus, hMinus]
  refine ⟨hPlus, hMinus, hV, hSig, hPhi, hJ, hCas.1, hCas.2.1, hSuper.2.2.2.2.2.2.1, ?_⟩
  rw [hOdd, hSum]

end ArchetypeT7_XPDilatonAndPeirceSpine

end InfoGeometry.Algebra.NoncommutativeTetraktysFlows
