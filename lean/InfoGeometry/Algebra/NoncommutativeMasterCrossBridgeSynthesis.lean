/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Noncommutative Master Cross-Bridge Synthesis (`B₁`–`B₄`)

Locks together `NoncommutativeDikinTetraktysSynthesis` (`DT₁`–`DT₇`) and
`NoncommutativeAnalyticitySynthesis` (`H₁`–`H₅`) over arbitrary noncommutative rings
`[Ring B]` and `[Ring A] [StarRing A]` via four cross-pillar structural theorems:
1. `B₁` (`DT₁ ↔ H₄`): Dikin–Burg–Stein self-concordance derivative as the negative
   bimodule anticommutator with left and right Maurer–Cartan winding 1-forms, plus
   `GL₁(B)` gauge invariance of `windingForm`.
2. `B₂` (`DT₂, DT₆ ↔ H₂, H₅`): Klein-four triality of the three canonical `2 + 2`
   Tetraktys operator splittings (`P`-split Peirce–DeWitt, `T`-split Cantor Markov,
   `C`-split Hestenes Cauchy–Riemann).
3. `B₃` (`DT₃ ↔ H₂, H₅`): Clifford–Cayley conjugation `C_Cayley = 1 + Ω` intertwining
   Peirce–DeWitt parity `P` with Cantor Markov shift `T`, while preserving Hestenes CR.
4. `B₄` (`H₁, H₃ ↔ DT₆, DT₇`): Nested Witt sheet realization of square-zero chiral
   Hodge theory in `M₂(M₂(A))` and 4-channel Hilbert–Schmidt Helmholtz Pythagoras.
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeMasterCrossBridgeSynthesis

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
## Bridge B₁: Dikin–Burg–Stein Self-Concordance & Maurer–Cartan Winding 1-Form Bridge (`DT₁ ↔ H₄`)
-/

section BridgeB1_DikinBurgSteinWindingBridge

variable {B : Type*} [Ring B]

def IsRingDeriv (D : B →+ B) : Prop :=
  ∀ a b : B, D (a * b) = D a * b + a * D b

theorem IsRingDeriv.map_one {D : B →+ B} (hD : IsRingDeriv D) : D 1 = 0 := by
  have h : D (1 * 1) = D 1 * 1 + 1 * D 1 := hD 1 1
  simp only [mul_one, one_mul] at h
  calc D 1 = D 1 + D 1 - D 1 := by abel
    _ = D 1 - D 1 := by rw [← h]
    _ = 0 := sub_self (D 1)

theorem IsRingDeriv.map_units_inv {D : B →+ B} (hD : IsRingDeriv D) (X : Bˣ) :
    D (↑X⁻¹ : B) = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by
  have h1 : D ((X : B) * (↑X⁻¹ : B)) = D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B) :=
    hD (X : B) (↑X⁻¹ : B)
  rw [Units.mul_inv, hD.map_one] at h1
  have h2 : (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) = D (↑X⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc D (↑X⁻¹ : B)
    _ = (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) -
        (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by noncomm_ring

/-- Left-trivialized Maurer–Cartan winding 1-form `ω_D(X) = X⁻¹ D(X) ∈ B`. -/
def windingForm (D : B →+ B) (X : Bˣ) : B :=
  (↑X⁻¹ : B) * D (X : B)

/-- Right-trivialized Maurer–Cartan winding 1-form `W_D(X) = D(X) X⁻¹ ∈ B`. -/
def rightWindingForm (D : B →+ B) (X : Bˣ) : B :=
  D (X : B) * (↑X⁻¹ : B)

/-- Burg–Stein Hessian operator `H_X(V) = X⁻¹ V X⁻¹`. -/
def burgSteinHessian (X : Bˣ) (V : B) : B :=
  (↑X⁻¹ : B) * V * (↑X⁻¹ : B)

/-- **Dikin–Burg–Stein & Maurer–Cartan Winding Bridge Theorem (`B₁`)**:
1. For any constant left gauge transformation `G ∈ Bˣ` (`D G = 0`), `ω_D(G X) = ω_D(X)`.
2. The third-order Burg–Stein self-concordance derivative `D(H_X(V))` (`D V = 0`) is the
   negative bimodule anti-commutator of `H_X(V)` with `ω_D(X)` and `W_D(X)`.
3. Pullback by `X` gives `X D(H_X(V)) X = -(W_D(X) V + V ω_D(X))`. -/
theorem dikin_burg_stein_winding_self_concordance
    {D : B →+ B} (hD : IsRingDeriv D) {G : Bˣ} (hG : D (G : B) = 0)
    (X : Bˣ) {V : B} (hV : D V = 0) :
    windingForm D (G * X) = windingForm D X ∧
    D (burgSteinHessian X V) =
      -(windingForm D X * burgSteinHessian X V +
        burgSteinHessian X V * rightWindingForm D X) ∧
    (X : B) * D (burgSteinHessian X V) * (X : B) =
      -(rightWindingForm D X * V + V * windingForm D X) := by
  have h_self : D (burgSteinHessian X V) =
      -(windingForm D X * burgSteinHessian X V +
        burgSteinHessian X V * rightWindingForm D X) := by
    dsimp [burgSteinHessian, windingForm, rightWindingForm]
    rw [hD ((↑X⁻¹ : B) * V) (↑X⁻¹ : B), hD (↑X⁻¹ : B) V, hV, hD.map_units_inv X]
    noncomm_ring
  refine ⟨?_, h_self, ?_⟩
  · dsimp [windingForm]
    have h_inv : ((↑(G * X)⁻¹ : Bˣ) : B) = (↑X⁻¹ : B) * (↑G⁻¹ : B) := by
      rw [_root_.mul_inv_rev]; rfl
    have hGi : (↑G⁻¹ : B) * (G : B) = 1 := Units.inv_mul G
    rw [h_inv, hD (G : B) (X : B), hG, zero_mul, zero_add]
    calc (↑X⁻¹ : B) * (↑G⁻¹ : B) * ((G : B) * D (X : B))
      _ = (↑X⁻¹ : B) * ((↑G⁻¹ : B) * (G : B)) * D (X : B) := by noncomm_ring
      _ = (↑X⁻¹ : B) * D (X : B) := by rw [hGi]; noncomm_ring
  · rw [h_self]
    dsimp [burgSteinHessian, windingForm, rightWindingForm]
    have hX1 : (X : B) * (↑X⁻¹ : B) = 1 := Units.mul_inv X
    have hX2 : (↑X⁻¹ : B) * (X : B) = 1 := Units.inv_mul X
    calc (X : B) * -((↑X⁻¹ : B) * D (X : B) * ((↑X⁻¹ : B) * V * (↑X⁻¹ : B)) +
          ((↑X⁻¹ : B) * V * (↑X⁻¹ : B)) * (D (X : B) * (↑X⁻¹ : B))) * (X : B)
      _ = -(((X : B) * (↑X⁻¹ : B)) * D (X : B) * (↑X⁻¹ : B) * V * ((↑X⁻¹ : B) * (X : B)) +
            ((X : B) * (↑X⁻¹ : B)) * V * (↑X⁻¹ : B) * D (X : B) * ((↑X⁻¹ : B) * (X : B))) := by
          noncomm_ring
      _ = -(D (X : B) * (↑X⁻¹ : B) * V + V * ((↑X⁻¹ : B) * D (X : B))) := by
          rw [hX1, hX2]; noncomm_ring

end BridgeB1_DikinBurgSteinWindingBridge

/-!
## Bridge B₂ & B₃: Klein-Four Triality of Tetraktys Operator Splittings & Clifford–Cayley Intertwining
-/

section BridgeB2_B3_KleinFourTrialityAndCayleyIntertwining

variable {A : Type*} [Ring A]

def cptP (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A := gamma1Op * M * gamma1Op
def cptT (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A := sigmaOp * M * sigmaOp
def cptC (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A := -(omegaOp * M * omegaOp)

def holomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M - omegaOp * M * omegaOp

def antiholomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M + omegaOp * M * omegaOp

def cantorMarkovStep (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M + sigmaOp * M * sigmaOp

def cantorLaplacian (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  sigmaOp * M * sigmaOp - M

def peirceFiberLift (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  chiralSheetPlus * X * chiralSheetPlus + sigmaOp * chiralSheetPlus * X * chiralSheetPlus * sigmaOp

def mellinCoeffI (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M + sigmaOp * M * sigmaOp)
def mellinCoeffGamma (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M - sigmaOp * M * sigmaOp)
def mellinCoeffSigma (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M * sigmaOp + sigmaOp * M)
def mellinCoeffOmega (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (sigmaOp * M - M * sigmaOp)

/-- **Klein-Four Triality of Tetraktys Operator Splittings (`B₂`)**:
Every operator `M ∈ M₂(A)` admits three canonical `2 + 2` Tetraktys decompositions governed by
the three Klein-four involutions `(P, T, C)`:
1. *`P`-Split (Peirce–DeWitt)*: `(M + P(M)) = M_I I + M_Γ Γ₁` and `(M - P(M)) = M_Σ Σ + M_Ω Ω`.
2. *`T`-Split (Cantor Markov)*: `M_step(M) = M_I I + M_Σ Σ` and `-Δ_Cantor(M) = M_Γ Γ₁ + M_Ω Ω`.
3. *`C`-Split (Hestenes CR)*: `∂_hol(M) = M_I I + M_Ω Ω` and `∂̄_anti(M) = M_Γ Γ₁ + M_Σ Σ`. -/
theorem klein_four_triality_of_tetraktys_splittings (M : Matrix (Fin 2) (Fin 2) A) :
    M + cptP M = mellinCoeffI M * 1 + mellinCoeffGamma M * gamma1Op ∧
    M - cptP M = mellinCoeffSigma M * sigmaOp + mellinCoeffOmega M * omegaOp ∧
    cantorMarkovStep M = mellinCoeffI M * 1 + mellinCoeffSigma M * sigmaOp ∧
    -cantorLaplacian M = mellinCoeffGamma M * gamma1Op + mellinCoeffOmega M * omegaOp ∧
    holomorphicProj M = mellinCoeffI M * 1 + mellinCoeffOmega M * omegaOp ∧
    antiholomorphicProj M = mellinCoeffGamma M * gamma1Op + mellinCoeffSigma M * sigmaOp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [cptP, cantorMarkovStep, cantorLaplacian, holomorphicProj, antiholomorphicProj,
            mellinCoeffI, mellinCoeffGamma, mellinCoeffSigma, mellinCoeffOmega,
            peirceFiberLift, chiralSheetPlus, gamma1Op, sigmaOp, omegaOp] <;>
      abel)

variable [StarRing A]

def cayleyOp : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp

/-- **Clifford–Cayley Intertwining of Peirce–DeWitt Parity and Cantor Markov Laplacian (`B₃`)**:
Conjugating by `C_Cayley = 1 + Ω` intertwines `P` and `T`, mapping the Peirce–DeWitt even/odd
projections into the Cantor Markov step and Cantor Laplacian while preserving the Hestenes
Cauchy–Riemann projections. -/
theorem clifford_cayley_intertwines_dewitt_and_cantor_markov (M : Matrix (Fin 2) (Fin 2) A) :
    cayleyOp * cptP M * cayleyOpᴴ = cptT (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * cptT M * cayleyOpᴴ = cptP (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * (M + cptP M) * cayleyOpᴴ = cantorMarkovStep (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * (cptP M - M) * cayleyOpᴴ = cantorLaplacian (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * holomorphicProj M * cayleyOpᴴ = holomorphicProj (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * antiholomorphicProj M * cayleyOpᴴ = antiholomorphicProj (cayleyOp * M * cayleyOpᴴ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [cayleyOp, cptP, cptT, cantorMarkovStep, cantorLaplacian,
            holomorphicProj, antiholomorphicProj, gamma1Op, sigmaOp, omegaOp] <;>
      abel)

end BridgeB2_B3_KleinFourTrialityAndCayleyIntertwining

/-!
## Bridge B₄: Nested Witt Realization of Square-Zero Chiral Hodge Theory & 4-Channel Helmholtz Pythagoras
-/

section BridgeB4_NestedWittChiralHodgeAndPythagoras

variable {A : Type*} [Ring A]

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- Nested exterior differential `D = diag(I₊, 0)` and codifferential `Δ = diag(I₋, 0)` in `M₂(M₂(A))`. -/
def nestedD     : NestedMat A := mat2 isotropicSheetPlus 0 0 0
def nestedDelta : NestedMat A := mat2 isotropicSheetMinus 0 0 0
def nestedDirac : NestedMat A := nestedD + nestedDelta

/-- Exact, coexact, and harmonic projections in `M₂(M₂(A))`. -/
def nestedExactProj   : NestedMat A := mat2 chiralSheetPlus 0 0 0
def nestedCoexactProj : NestedMat A := mat2 chiralSheetMinus 0 0 0
def nestedHarmProj    : NestedMat A := mat2 0 0 0 1

/-- **Nested Witt Sheet Realization of Square-Zero Chiral Hodge Theory & 4-Channel Pythagoras (`B₄`)**:
1. `D` and `Δ` satisfy `D² = Δ² = 0`, `D Δ D = D`, `Δ D Δ = Δ`, with exact projection
   `diag(P₊, 0)`, coexact projection `diag(P₋, 0)`, and harmonic projection `diag(0, 1)`.
2. For any `X ∈ M₂(M₂(A))`, `(D + Δ) X = 0 ↔ nestedHarmProj * X = X`.
3. Over any `⋆`-ring `A`, all four Helmholtz–Tetraktys channels `M_I, M_Γ, M_Σ, M_Ω ∈ M₂(A)`
   satisfy the noncommutative Hilbert–Schmidt Pythagorean identity. -/
theorem nested_witt_sheets_realize_chiral_hodge_and_tetraktys
    [StarRing A] (X : NestedMat A) (cI cGamma cSigma cOmega : A) :
    let M_I     : Matrix (Fin 2) (Fin 2) A := fiberEmbed cI * 1
    let M_Gamma : Matrix (Fin 2) (Fin 2) A := fiberEmbed cGamma * gamma1Op
    let M_Sigma : Matrix (Fin 2) (Fin 2) A := fiberEmbed cSigma * sigmaOp
    let M_Omega : Matrix (Fin 2) (Fin 2) A := fiberEmbed cOmega * omegaOp
    (nestedD : NestedMat A) * nestedD = 0 ∧
    (nestedDelta : NestedMat A) * nestedDelta = 0 ∧
    (nestedD : NestedMat A) * nestedDelta * nestedD = nestedD ∧
    (nestedDelta : NestedMat A) * nestedD * nestedDelta = nestedDelta ∧
    (nestedD : NestedMat A) * nestedDelta = nestedExactProj ∧
    (nestedDelta : NestedMat A) * nestedD = nestedCoexactProj ∧
    1 - (nestedD * nestedDelta + nestedDelta * nestedD) = (nestedHarmProj : NestedMat A) ∧
    (nestedDirac * X = 0 ↔ nestedHarmProj * X = X) ∧
    Matrix.trace ((M_I + M_Gamma + M_Sigma + M_Omega)ᴴ * (M_I + M_Gamma + M_Sigma + M_Omega)) =
      Matrix.trace (M_Iᴴ * M_I) + Matrix.trace (M_Gammaᴴ * M_Gamma) +
      Matrix.trace (M_Sigmaᴴ * M_Sigma) + Matrix.trace (M_Omegaᴴ * M_Omega) := by
  have hD2 : (nestedD : NestedMat A) * nestedD = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedD, isotropicSheetPlus]
  have hDel2 : (nestedDelta : NestedMat A) * nestedDelta = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedDelta, isotropicSheetMinus]
  have hDDelD : (nestedD : NestedMat A) * nestedDelta * nestedD = nestedD := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]
  have hDelDDel : (nestedDelta : NestedMat A) * nestedD * nestedDelta = nestedDelta := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]
  have hEx : (nestedD : NestedMat A) * nestedDelta = nestedExactProj := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, nestedExactProj, isotropicSheetPlus, isotropicSheetMinus, chiralSheetPlus]
  have hCo : (nestedDelta : NestedMat A) * nestedD = nestedCoexactProj := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, nestedCoexactProj, isotropicSheetPlus, isotropicSheetMinus, chiralSheetMinus]
  have hHarm : 1 - ((nestedD : NestedMat A) * nestedDelta + nestedDelta * nestedD) = nestedHarmProj := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, nestedHarmProj, isotropicSheetPlus, isotropicSheetMinus]
  refine ⟨hD2, hDel2, hDDelD, hDelDDel, hEx, hCo, hHarm, ?_, ?_⟩
  · rw [← hHarm]; dsimp [nestedDirac]
    constructor
    · intro h
      have h1 : nestedD * X = 0 := by
        calc nestedD * X
          _ = (nestedD * nestedDelta * nestedD) * X + nestedD * (nestedDelta * nestedDelta) * X := by
              rw [hDDelD, hDel2]; noncomm_ring
          _ = nestedD * nestedDelta * ((nestedD + nestedDelta) * X) := by noncomm_ring
          _ = nestedD * nestedDelta * 0 := by rw [h]
          _ = 0 := mul_zero _
      have h2 : nestedDelta * X = 0 := by
        calc nestedDelta * X
          _ = nestedDelta * (nestedD * nestedD) * X + (nestedDelta * nestedD * nestedDelta) * X := by
              rw [hD2, hDelDDel]; noncomm_ring
          _ = nestedDelta * nestedD * ((nestedD + nestedDelta) * X) := by noncomm_ring
          _ = nestedDelta * nestedD * 0 := by rw [h]
          _ = 0 := mul_zero _
      calc (1 - (nestedD * nestedDelta + nestedDelta * nestedD)) * X
        _ = X - nestedD * (nestedDelta * X) - nestedDelta * (nestedD * X) := by noncomm_ring
        _ = X - nestedD * 0 - nestedDelta * 0 := by rw [h1, h2]
        _ = X := by noncomm_ring
    · intro hP
      calc (nestedD + nestedDelta) * X
        _ = (nestedD + nestedDelta) * ((1 - (nestedD * nestedDelta + nestedDelta * nestedD)) * X) := by
            rw [hP]
        _ = (nestedD - nestedD * nestedDelta * nestedD - (nestedD * nestedD) * nestedDelta +
             nestedDelta - (nestedDelta * nestedDelta) * nestedD -
             nestedDelta * nestedD * nestedDelta) * X := by noncomm_ring
        _ = (nestedD - nestedD - 0 * nestedDelta +
             nestedDelta - 0 * nestedD - nestedDelta) * X := by
            rw [hDDelD, hD2, hDel2, hDelDDel]
        _ = 0 := by noncomm_ring
  · simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp]
    noncomm_ring

end BridgeB4_NestedWittChiralHodgeAndPythagoras


private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Algebra.NoncommutativeMasterCrossBridgeSynthesis
