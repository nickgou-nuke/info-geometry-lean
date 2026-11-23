/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.GradedNullconeAlgebra
import InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge
import InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge
import InfoGeometry.Clifford.LochakRodichevFierzKrein

/-!
# Canonical Graded-Nullcone Unification (`Algebra ↔ Clifford`)

Reconciles the two graded-nullcone Daviau–Fierz bridges without disturbing existing downstream
audits:

1. **Spinor carrier & readout equivalence**: identifies `Clifford.GradedNullconeDaviauFierzBridge.ChiralDiracSpinor`
   (`EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)`) with
   `Algebra.GradedNullconeDaviauFierzBridge.ChiralDiracSpinor` (`structure { plus, minus }`), proving
   exact equality of all four Fierz/Krein readouts `(Ω₁, Ω₂, j⁰, k⁰)` and diagonal `U(2)` actions.
2. **Real `M₈(ℝ)` determinant-defect & current lift**: transports
   `Algebra.GradedNullconeDaviauFierzBridge.lochak_fierz_takabayasi_and_proca_coupling` and
   `daviau_vector_su2_preserves_chiral_pairing` back to `Φ : Vec8R`, sharpening the inequality into
   the exact Fierz–Pauli–Kofink determinant identity
   `Ω₁² + Ω₂² + (Σ⁰)² = (J⁰)² - 4 |ξ₀ η₁ - ξ₁ η₀|²`.
3. **Nullcone `2 × 2` generator alignment**: reindexes `Matrix (Fin 2) (Fin 2) ℝ` onto
   `Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ`, matching `gammaCut2 ↦ gammaCut 1`,
   `gammaMir2 ↦ mirrorJ 1`, `peirceY 1 ↦ [[0, 1], [0, 0]]`, and both `parabolicFlow` definitions.
-/

noncomputable section

open scoped Matrix
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Algebra.GradedNullconeAlgebra
open InfoGeometry.Clifford.LochakRodichevFierzKrein

namespace InfoGeometry.Clifford.DaviauGradedNullconeUnification

private abbrev CliffSpinor := InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.ChiralDiracSpinor
private abbrev AlgSpinor := InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.ChiralDiracSpinor

/-! ### 1. Closed Noncommutativity Witnesses (Trap T16) -/

theorem mat2R_mul_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  InfoGeometry.Algebra.GradedNullconeAlgebra.mat2R_mul_noncommutative

theorem mat2C_mul_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.mat2C_mul_noncommutative

theorem matNullcone1_mul_noncomm_witness :
    ∃ A B : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ, A * B ≠ B * A := by
  refine ⟨InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.gammaCut 1,
    InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.mirrorJ 1, ?_⟩
  exact (InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.gammaCut_ne_mirrorJ_and_noncomm
    1 Nat.zero_lt_one).2.1

/-! ### 2. Carrier & Bilinear Readout Equivalence -/

/-- Canonical bijection between the Clifford tuple carrier `ℂ² × ℂ²` and the Algebra structure
carrier `{ plus, minus }`. -/
def chiralSpinorCarrierEquiv : CliffSpinor ≃ AlgSpinor where
  toFun p := ⟨p.1, p.2⟩
  invFun s := (s.plus, s.minus)
  left_inv p := by ext <;> rfl
  right_inv s := by cases s; rfl

@[simp]
theorem chiralSpinorCarrierEquiv_plus (ψ : CliffSpinor) :
    (chiralSpinorCarrierEquiv ψ).plus = ψ.1 := rfl

@[simp]
theorem chiralSpinorCarrierEquiv_minus (ψ : CliffSpinor) :
    (chiralSpinorCarrierEquiv ψ).minus = ψ.2 := rfl

/-- All four bilinear readouts `(fierzScalar, fierzPseudoscalar, kreinProbDensity, chiralAxialDensity)`
agree verbatim between the `Clifford` and `Algebra` graded-nullcone bridges. -/
theorem chiralSpinorCarrierEquiv_readouts (ψ : CliffSpinor) :
    InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.fierzScalar (chiralSpinorCarrierEquiv ψ) =
      InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.fierzScalar ψ ∧
    InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.fierzPseudoscalar (chiralSpinorCarrierEquiv ψ) =
      InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.fierzPseudoscalar ψ ∧
    InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.kreinProbDensity (chiralSpinorCarrierEquiv ψ) =
      InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.kreinProbDensity ψ ∧
    InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.chiralAxialDensity (chiralSpinorCarrierEquiv ψ) =
      InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.chiralAxialDensity ψ := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Diagonal `2 × 2` matrix multiplication commutes across `chiralSpinorCarrierEquiv`. -/
theorem chiralSpinorCarrierEquiv_vectorGaugeAct (U : Matrix (Fin 2) (Fin 2) ℂ) (ψ : CliffSpinor) :
    InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.vectorGaugeAct U
        (chiralSpinorCarrierEquiv ψ) =
      chiralSpinorCarrierEquiv
        (WithLp.toLp 2 (U.mulVec ψ.1.ofLp), WithLp.toLp 2 (U.mulVec ψ.2.ofLp)) := by
  rfl

/-! ### 3. Real `M₈(ℝ)` Determinant-Defect & Unitary Lift -/

/-- Canonical embedding of a real 8-component Dirac spinor `Φ : Vec8R` into the `Algebra`
chiral Dirac spinor carrier. -/
def vec8ToAlgChiralSpinor (Φ : Vec8R) : AlgSpinor :=
  chiralSpinorCarrierEquiv
    (InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.vec8ToChiralDiracSpinor Φ)

/-- Real `M₈(ℝ)` determinant-defect Fierz–Pauli–Kofink identity and `U(2)` invariance obtained by
composing `Algebra.GradedNullconeDaviauFierzBridge` with `vec8ToChiralDiracSpinor`. -/
theorem realDirac8_algebra_fierz_determinant_defect (Φ : Vec8R) :
    (0 ≤ electricCurrentJ Φ 0) ∧
    (omega1 Φ ^ 2 + omega2 Φ ^ 2 + axialCurrentSigma Φ 0 ^ 2 =
      electricCurrentJ Φ 0 ^ 2 -
        4 * Complex.normSq (weylXi Φ 0 * weylEta Φ 1 - weylXi Φ 1 * weylEta Φ 0)) ∧
    (omega1 Φ ^ 2 + omega2 Φ ^ 2 + axialCurrentSigma Φ 0 ^ 2 ≤ electricCurrentJ Φ 0 ^ 2) ∧
    (∀ U : Matrix (Fin 2) (Fin 2) ℂ, Uᴴ * U = 1 →
      InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.fierzScalar
          (InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.vectorGaugeAct U
            (vec8ToAlgChiralSpinor Φ)) = omega1 Φ ∧
      InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.fierzPseudoscalar
          (InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.vectorGaugeAct U
            (vec8ToAlgChiralSpinor Φ)) = -omega2 Φ ∧
      InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.kreinProbDensity
          (InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.vectorGaugeAct U
            (vec8ToAlgChiralSpinor Φ)) = electricCurrentJ Φ 0 ∧
      InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.chiralAxialDensity
          (InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.vectorGaugeAct U
            (vec8ToAlgChiralSpinor Φ)) = axialCurrentSigma Φ 0) := by
  let ψC := InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.vec8ToChiralDiracSpinor Φ
  let ψA := vec8ToAlgChiralSpinor Φ
  have h1 :
      InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.fierzScalar ψA = omega1 Φ :=
    InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.fierzScalar_vec8ToChiralDiracSpinor Φ
  have h2 :
      InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.fierzPseudoscalar ψA = -omega2 Φ :=
    InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.fierzPseudoscalar_vec8ToChiralDiracSpinor Φ
  have hJ :
      InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.kreinProbDensity ψA =
        electricCurrentJ Φ 0 :=
    InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.kreinProbDensity_vec8ToChiralDiracSpinor Φ
  have hS :
      InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.chiralAxialDensity ψA =
        axialCurrentSigma Φ 0 :=
    InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.chiralAxialDensity_vec8ToChiralDiracSpinor Φ
  have hAlg :=
    InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.lochak_fierz_takabayasi_and_proca_coupling
      ψA
  have hp0 : ψA.plus 0 = weylXi Φ 0 := rfl
  have hp1 : ψA.plus 1 = weylXi Φ 1 := rfl
  have hm0 : ψA.minus 0 = weylEta Φ 0 := rfl
  have hm1 : ψA.minus 1 = weylEta Φ 1 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hJ] using hAlg.1
  · have hEq := hAlg.2.2.2.2.2.1
    rw [h1, h2, hS, hJ, hp0, hp1, hm0, hm1] at hEq
    simpa [neg_sq] using hEq
  · have hLe := hAlg.2.2.2.2.2.2.1
    rw [h1, h2, hS, hJ] at hLe
    simpa [neg_sq] using hLe
  · intro U hU
    have hInv :=
      InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.daviau_vector_su2_preserves_chiral_pairing
        U hU ψA
    refine ⟨hInv.2.1.trans h1, hInv.2.2.1.trans h2, hInv.2.2.2.1.trans hJ, hInv.2.2.2.2.trans hS⟩

/-! ### 4. Reindexing Alignment `M₂(ℝ) ≃ₐ[ℝ] Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ` -/

/-- Canonical index equivalence `Fin 2 ≃ Fin 1 ⊕ Fin 1`. -/
def fin2EquivFin1SumFin1 : Fin 2 ≃ Fin 1 ⊕ Fin 1 where
  toFun
    | 0 => Sum.inl 0
    | 1 => Sum.inr 0
  invFun
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  left_inv i := by fin_cases i <;> rfl
  right_inv x := by rcases x with i | i <;> fin_cases i <;> rfl

/-- Algebra isomorphism identifying `2 × 2` real matrices with `1 ⊕ 1` block-nullcone matrices. -/
def mat2REquivNullcone1 :
    Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ fin2EquivFin1SumFin1

/-- Reindexing `mat2REquivNullcone1` maps `gammaCut2`, `gammaMir2`, `peirceY 1`, and
`Algebra`'s `parabolicFlow t` verbatim to `gammaCut 1`, `mirrorJ 1`, `[[0, 1], [0, 0]]`, and
`Clifford`'s `parabolicFlow` on `Fin 1 ⊕ Fin 1`. -/
theorem mat2REquivNullcone1_generators (t : ℝ) :
    mat2REquivNullcone1 gammaCut2 =
      InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.gammaCut 1 ∧
    mat2REquivNullcone1 gammaMir2 =
      InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.mirrorJ 1 ∧
    mat2REquivNullcone1 (peirceY (1 : ℝ)) = Matrix.fromBlocks 0 1 0 0 ∧
    mat2REquivNullcone1 (InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.parabolicFlow t) =
      InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.parabolicFlow
        (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 0 0) t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [mat2REquivNullcone1, fin2EquivFin1SumFin1, gammaCut2,
        InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.gammaCut]
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [mat2REquivNullcone1, fin2EquivFin1SumFin1, gammaMir2,
        InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.mirrorJ]
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [mat2REquivNullcone1, fin2EquivFin1SumFin1, peirceY]
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [mat2REquivNullcone1, fin2EquivFin1SumFin1,
        InfoGeometry.Algebra.GradedNullconeDaviauFierzBridge.parabolicFlow,
        InfoGeometry.Clifford.GradedNullconeDaviauFierzBridge.parabolicFlow]

end InfoGeometry.Clifford.DaviauGradedNullconeUnification
