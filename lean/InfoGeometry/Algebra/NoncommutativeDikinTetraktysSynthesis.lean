/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Noncommutative Dikin–Burg–Stein Self-Concordance & Tetraktys Flows Synthesis

Formalizes over arbitrary noncommutative rings `[Ring B]`, `[Ring A]`, and `[StarRing A]`
the seven causally ordered archetypes `DT₁`–`DT₇`:
1. `DT₁`: Noncommutative Weyl–Dikin whitened displacement `W_X(Y) = X⁻¹(Y - X)`,
   `GL₁(B)`-gauge invariance of `Q_Dikin(X, Y)`, and third-order Burg–Stein operator
   self-concordance `d(X⁻¹ V X⁻¹) = -X⁻¹ d(X) (X⁻¹ V X⁻¹) - (X⁻¹ V X⁻¹) d(X) X⁻¹`.
2. `DT₂`: Modular CPT automorphism triad `(P, T, C)`, `Γ₁ Σ Ω = 1`, and Klein-four
   `Z₂ × Z₂` grading of `M₂(A)`.
3. `DT₃`: Division-free Clifford–Cayley transform `C_Cayley = 1 + Ω`, clock-to-shift
   rotation, and twin-wave duality `(P₊, P₋) ↔ (1 ± Σ)`.
4. `DT₄`: Hyperbolic Mellin time-focusing `D(u) = diag(u, u⁻¹)` on source/sink twin waves
   `(F₊, F₋)`.
5. `DT₅`: Noncommutative characteristic polynomial `X² = ι(c_Γ² + c_Σ² - c_Ω²) + Lie`
   and classification of hyperbolic, elliptic, parabolic, and loxodromic flows.
6. `DT₆`: Two-stage chained Tetraktys 16-channel inversion on `M₂(M₂(A))`.
7. `DT₇`: The Pythagorean `(1 + 2 + 3 + 4 = 10) + 6 = 16` symplectic Tetraktys split
   of `M₂(M₂(A))` and Lie-bracket closure.
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeDikinTetraktysSynthesis

/-!
## Archetype DT₁: Noncommutative Dikin–Burg–Stein Operator Metric & Self-Concordance
-/

section ArchetypeDT1_DikinBurgSteinBridge

variable {B : Type*} [Ring B]

/-- Additive group homomorphism satisfying the noncommutative Leibniz rule. -/
def IsRingDeriv (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

theorem IsRingDeriv.map_one {d : B →+ B} (hd : IsRingDeriv d) : d 1 = 0 := by
  have h : d (1 * 1) = d 1 * 1 + 1 * d 1 := hd 1 1
  simp only [mul_one, one_mul] at h
  calc d 1 = d 1 + d 1 - d 1 := by abel
    _ = d 1 - d 1 := by rw [← h]
    _ = 0 := sub_self (d 1)

theorem IsRingDeriv.map_units_inv {d : B →+ B} (hd : IsRingDeriv d) (X : Bˣ) :
    d (↑X⁻¹ : B) = -(↑X⁻¹ : B) * d (X : B) * (↑X⁻¹ : B) := by
  have h1 : d ((X : B) * (↑X⁻¹ : B)) = d (X : B) * (↑X⁻¹ : B) + (X : B) * d (↑X⁻¹ : B) :=
    hd (X : B) (↑X⁻¹ : B)
  rw [Units.mul_inv, hd.map_one] at h1
  have h2 : (↑X⁻¹ : B) * (d (X : B) * (↑X⁻¹ : B) + (X : B) * d (↑X⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑X⁻¹ : B) * (X : B) * d (↑X⁻¹ : B) = d (↑X⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc d (↑X⁻¹ : B)
    _ = (↑X⁻¹ : B) * (X : B) * d (↑X⁻¹ : B) -
        (↑X⁻¹ : B) * (d (X : B) * (↑X⁻¹ : B) + (X : B) * d (↑X⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑X⁻¹ : B) * d (X : B) * (↑X⁻¹ : B) := by noncomm_ring

/-- Weyl–Dikin whitened relative displacement `W_X(Y) = X⁻¹(Y - X) ∈ B`. -/
def dikinWhitened (X : Bˣ) (Y : B) : B :=
  (↑X⁻¹ : B) * (Y - (X : B))

/-- Dikin–Burg–Stein quadratic operator form `Q_Dikin(X, Y) = W_X(Y)⋆ W_X(Y)`. -/
def dikinQuadraticForm [StarRing B] (X : Bˣ) (Y : B) : B :=
  star (dikinWhitened X Y) * dikinWhitened X Y

/-- Burg–Stein Hessian quadratic operator `H_X(V) = X⁻¹ V X⁻¹`. -/
def burgSteinHessian (X : Bˣ) (V : B) : B :=
  (↑X⁻¹ : B) * V * (↑X⁻¹ : B)

/-- **Non-Abelian `GL₁(B)`-Gauge Invariance & Third-Order Operator Self-Concordance (`DT₁`)**:
1. Left scaling `(X, Y) ↦ (G X, G Y)` by any `G ∈ Bˣ` leaves `W_X(Y)` and `Q_Dikin(X, Y)`
   strictly invariant.
2. For any derivation `d : B →+ B` and `d`-constant tangent `V ∈ B` (`d V = 0`),
   `d(X⁻¹ V X⁻¹) = -X⁻¹ d(X) (X⁻¹ V X⁻¹) - (X⁻¹ V X⁻¹) d(X) X⁻¹`. -/
theorem dikin_gauge_invariance_and_burg_stein_self_concordance [StarRing B]
    {d : B →+ B} (hd : IsRingDeriv d) (G X : Bˣ) (Y V : B) (hV : d V = 0) :
    dikinWhitened (G * X) ((G : B) * Y) = dikinWhitened X Y ∧
    dikinQuadraticForm (G * X) ((G : B) * Y) = dikinQuadraticForm X Y ∧
    d (burgSteinHessian X V) =
      -(↑X⁻¹ : B) * d (X : B) * burgSteinHessian X V -
      burgSteinHessian X V * d (X : B) * (↑X⁻¹ : B) := by
  have h_whitened : dikinWhitened (G * X) ((G : B) * Y) = dikinWhitened X Y := by
    dsimp [dikinWhitened]
    have h_inv : ((↑(G * X)⁻¹ : Bˣ) : B) = (↑X⁻¹ : B) * (↑G⁻¹ : B) := by
      rw [_root_.mul_inv_rev]; rfl
    have hG : (↑G⁻¹ : B) * (G : B) = 1 := Units.inv_mul G
    rw [h_inv]
    calc (↑X⁻¹ : B) * (↑G⁻¹ : B) * ((G : B) * Y - (G : B) * (X : B))
      _ = (↑X⁻¹ : B) * ((↑G⁻¹ : B) * (G : B)) * (Y - (X : B)) := by noncomm_ring
      _ = (↑X⁻¹ : B) * (Y - (X : B)) := by rw [hG]; noncomm_ring
  refine ⟨h_whitened, by dsimp [dikinQuadraticForm]; rw [h_whitened], ?_⟩
  dsimp [burgSteinHessian]
  rw [hd ((↑X⁻¹ : B) * V) (↑X⁻¹ : B), hd (↑X⁻¹ : B) V, hV, hd.map_units_inv X]
  noncomm_ring

end ArchetypeDT1_DikinBurgSteinBridge

/-!
## Infrastructure: `mat2` Constructor & Simp Lemmas (Preventing `vecMul` Simp Blowups)
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

omit [Ring A] in @[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 0 0 = star (M 0 0) := rfl
omit [Ring A] in @[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 0 1 = star (M 1 0) := rfl
omit [Ring A] in @[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 1 0 = star (M 0 1) := rfl
omit [Ring A] in @[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    (star M) 1 1 = star (M 1 1) := rfl

def gamma1Op   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def P_plus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def P_minus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 0 1
def F_plus     : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def F_minus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

end Matrix2Simp

/-!
## Archetype DT₂: Modular CPT Automorphism Triad & Klein-Four Z₂ × Z₂ Grading
-/

section ArchetypeDT2_ModularCPTTriad

variable {A : Type*} [Ring A]

def cptP (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  gamma1Op * M * gamma1Op

def cptT (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  sigmaOp * M * sigmaOp

def cptC (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  -(omegaOp * M * omegaOp)

/-- **Modular CPT Klein-Four Group Theorem (`DT₂`)**:
Since `gamma1Op * sigmaOp = -omegaOp` and `omegaOp^2 = -1`, the modular volume identity is
`gamma1Op * sigmaOp * omegaOp = 1`, and `(P, T, C)` forms a Klein four-group on `M₂(A)`
with `P(T(C(M))) = M`. -/
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
    (apply ext_fin2 <;> simp [cptP, cptT, cptC, gamma1Op, sigmaOp, omegaOp])

end ArchetypeDT2_ModularCPTTriad

/-!
## Archetype DT₃: Clifford–Cayley Transform & Clock–Shift / Twin-Wave Duality
-/

section ArchetypeDT3_CliffordCayleyTransform

variable {A : Type*} [Ring A] [StarRing A]

def cayleyOp     : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp
def twinWaveSym  : Matrix (Fin 2) (Fin 2) A := 1 + sigmaOp
def twinWaveAnti : Matrix (Fin 2) (Fin 2) A := 1 - sigmaOp

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
      simp [cayleyOp, twinWaveSym, twinWaveAnti, gamma1Op, sigmaOp, omegaOp,
            P_plus, P_minus, two_smul])

end ArchetypeDT3_CliffordCayleyTransform

/-!
## Archetype DT₄: Hyperbolic Mellin Time-Focusing on Source (0) & Sink (∞) Twin Waves
-/

section ArchetypeDT4_HyperbolicTimeFocusingTwinWaves

variable {A : Type*} [Ring A]

def mellinFocus (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  mat2 (u : A) 0 0 (↑u⁻¹ : A)

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
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_plus, mul_assoc]
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_minus, mul_assoc]
  · apply ext_fin2
    · simp [fiberEmbed, F_plus, F_minus, P_plus]
      calc (u : A) * a * (u : A) * ((↑u⁻¹ : A) * b * (↑u⁻¹ : A))
        _ = (u : A) * a * ((u : A) * (↑u⁻¹ : A)) * b * (↑u⁻¹ : A) := by noncomm_ring
        _ = (u : A) * a * b * (↑u⁻¹ : A) := by rw [h1]; noncomm_ring
    · simp [fiberEmbed, F_plus, F_minus, P_plus]
    · simp [fiberEmbed, F_plus, F_minus, P_plus]
    · simp [fiberEmbed, F_plus, F_minus, P_plus]

end ArchetypeDT4_HyperbolicTimeFocusingTwinWaves

/-!
## Archetype DT₅: Noncommutative Characteristic Polynomial & The Four Geometric Flows
-/

section ArchetypeDT5_NoncommutativeCharpolyAndFourFlows

variable {A : Type*} [Ring A]

def flowGen (cGamma cSigma cOmega : A) : Matrix (Fin 2) (Fin 2) A :=
  fiberEmbed cGamma * gamma1Op + fiberEmbed cSigma * sigmaOp + fiberEmbed cOmega * omegaOp

theorem noncommutative_charpoly_casimir_and_lie_obstruction (cGamma cSigma cOmega : A) :
    flowGen cGamma cSigma cOmega * flowGen cGamma cSigma cOmega =
      fiberEmbed (cGamma * cGamma + cSigma * cSigma - cOmega * cOmega) * 1 +
      fiberEmbed ⁅cSigma, cOmega⁆ * gamma1Op +
      fiberEmbed ⁅cOmega, cGamma⁆ * sigmaOp -
      fiberEmbed ⁅cGamma, cSigma⁆ * omegaOp := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp] <;> noncomm_ring

theorem four_geometric_flows_classification (cI a b : A) (hab : ⁅a, b⁆ = 0) :
    flowGen a 0 0 * flowGen a 0 0 = fiberEmbed (a * a) ∧
    flowGen 0 a 0 * flowGen 0 a 0 = fiberEmbed (a * a) ∧
    flowGen 0 0 a * flowGen 0 0 a = -fiberEmbed (a * a) ∧
    flowGen 0 a a = 2 • (fiberEmbed a * F_minus) ∧
    flowGen 0 a (-a) = 2 • (fiberEmbed a * F_plus) ∧
    flowGen 0 a a * flowGen 0 a a = 0 ∧
    (1 + flowGen 0 a a) * (1 - flowGen 0 a a) = 1 ∧
    ((fiberEmbed cI + flowGen a 0 b) - fiberEmbed cI) *
    ((fiberEmbed cI + flowGen a 0 b) - fiberEmbed cI) =
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
      rw [← neg_eq_zero]
      calc -(b * a - a * b) = a * b - b * a := by abel
        _ = 0 := hab
    rw [hba]
    apply ext_fin2 <;> simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp, Ring.lie_def]

end ArchetypeDT5_NoncommutativeCharpolyAndFourFlows

/-!
## Archetype DT₆ & DT₇: Chained Tetraktys Transform & The 10 + 6 = 16 Symplectic Split
-/

section ArchetypeDT6_DT7_ChainedTetraktysAndSymplecticSplit

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
  apply ext_fin2 <;>
    simp [mellinCoeffI, mellinCoeffGamma, mellinCoeffSigma, mellinCoeffOmega,
      peirceFiberLift, P_plus, gamma1Op, sigmaOp, omegaOp, two_smul] <;>
    abel

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

def tetraktysMode
    (Cout : NestedMat A → NestedMat A)
    (Cin : Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) A)
    (M : NestedMat A) : NestedMat A :=
  fiberEmbed (Cin (Cout M 0 0))

theorem outer_mode_inner_expansion
    (Cout : NestedMat A → NestedMat A) (M : NestedMat A)
    (h_diag : Cout M = fiberEmbed (Cout M 0 0)) :
    tetraktysMode Cout mellinCoeffI M * fiberEmbed 1 +
    tetraktysMode Cout mellinCoeffGamma M * fiberEmbed gamma1Op +
    tetraktysMode Cout mellinCoeffSigma M * fiberEmbed sigmaOp +
    tetraktysMode Cout mellinCoeffOmega M * fiberEmbed omegaOp =
      2 • Cout M := by
  have h_inv := clifford_mellin_walsh_inversion (Cout M 0 0)
  rw [h_diag]
  apply ext_fin2 <;> simp [tetraktysMode, fiberEmbed, ← h_inv]

theorem chained_tetraktys_16_channel_inversion (M : NestedMat A) :
    (tetraktysMode mellinCoeffI mellinCoeffI M * fiberEmbed 1 +
     tetraktysMode mellinCoeffI mellinCoeffGamma M * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffI mellinCoeffSigma M * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffI mellinCoeffOmega M * fiberEmbed omegaOp) * 1 +
    (tetraktysMode mellinCoeffGamma mellinCoeffI M * fiberEmbed 1 +
     tetraktysMode mellinCoeffGamma mellinCoeffGamma M * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffGamma mellinCoeffSigma M * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffGamma mellinCoeffOmega M * fiberEmbed omegaOp) * gamma1Op +
    (tetraktysMode mellinCoeffSigma mellinCoeffI M * fiberEmbed 1 +
     tetraktysMode mellinCoeffSigma mellinCoeffGamma M * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffSigma mellinCoeffSigma M * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffSigma mellinCoeffOmega M * fiberEmbed omegaOp) * sigmaOp +
    (tetraktysMode mellinCoeffOmega mellinCoeffI M * fiberEmbed 1 +
     tetraktysMode mellinCoeffOmega mellinCoeffGamma M * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffOmega mellinCoeffSigma M * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffOmega mellinCoeffOmega M * fiberEmbed omegaOp) * omegaOp =
      4 • M := by
  have hI : mellinCoeffI M = fiberEmbed (mellinCoeffI M 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffI, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  have hG : mellinCoeffGamma M = fiberEmbed (mellinCoeffGamma M 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffGamma, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  have hS : mellinCoeffSigma M = fiberEmbed (mellinCoeffSigma M 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffSigma, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  have hO : mellinCoeffOmega M = fiberEmbed (mellinCoeffOmega M 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffOmega, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  rw [outer_mode_inner_expansion mellinCoeffI M hI,
      outer_mode_inner_expansion mellinCoeffGamma M hG,
      outer_mode_inner_expansion mellinCoeffSigma M hS,
      outer_mode_inner_expansion mellinCoeffOmega M hO]
  have h_outer := clifford_mellin_walsh_inversion M
  calc (2 • mellinCoeffI M) * 1 + (2 • mellinCoeffGamma M) * gamma1Op +
       (2 • mellinCoeffSigma M) * sigmaOp + (2 • mellinCoeffOmega M) * omegaOp
    _ = 2 • (mellinCoeffI M * 1 + mellinCoeffGamma M * gamma1Op +
             mellinCoeffSigma M * sigmaOp + mellinCoeffOmega M * omegaOp) := by
        simp only [two_smul]; noncomm_ring
    _ = 2 • (2 • M) := by rw [h_outer]
    _ = (2 * 2) • M := by rw [← mul_smul]
    _ = 4 • M := rfl

section SymplecticTetraktysSplit

variable [StarRing A]

def J_sp : NestedMat A := omegaOp

def IsSymplecticTetraktys (X : NestedMat A) : Prop :=
  Xᴴ * J_sp + J_sp * X = 0

theorem pythagorean_ten_symplectic_tetraktys_generators :
    (∀ X Y : NestedMat A,
      IsSymplecticTetraktys X → IsSymplecticTetraktys Y → IsSymplecticTetraktys ⁅X, Y⁆) ∧
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
  · intro X Y hX hY
    dsimp [IsSymplecticTetraktys] at *
    have hX' : Xᴴ * J_sp = -(J_sp * X) := eq_neg_of_add_eq_zero_left hX
    have hY' : Yᴴ * J_sp = -(J_sp * Y) := eq_neg_of_add_eq_zero_left hY
    rw [Ring.lie_def]
    calc (X * Y - Y * X)ᴴ * J_sp + J_sp * (X * Y - Y * X)
      _ = (Yᴴ * Xᴴ - Xᴴ * Yᴴ) * J_sp + J_sp * (X * Y - Y * X) := by
          rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
      _ = Yᴴ * (Xᴴ * J_sp) - Xᴴ * (Yᴴ * J_sp) + J_sp * (X * Y - Y * X) := by noncomm_ring
      _ = Yᴴ * -(J_sp * X) - Xᴴ * -(J_sp * Y) + J_sp * (X * Y - Y * X) := by rw [hX', hY']
      _ = -((Yᴴ * J_sp) * X) + (Xᴴ * J_sp) * Y + J_sp * (X * Y - Y * X) := by noncomm_ring
      _ = -(-(J_sp * Y) * X) + -(J_sp * X) * Y + J_sp * (X * Y - Y * X) := by rw [hX', hY']
      _ = 0 := by noncomm_ring
  all_goals
    dsimp [IsSymplecticTetraktys, J_sp]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end SymplecticTetraktysSplit

end ArchetypeDT6_DT7_ChainedTetraktysAndSymplecticSplit


private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Algebra.NoncommutativeDikinTetraktysSynthesis
