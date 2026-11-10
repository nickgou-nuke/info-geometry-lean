/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Holographic Bulk-to-Boundary Block Equivariance & Seiberg–Witten Curvature

Target: `InfoGeometry/Holography/HolographicBoundarySeibergWitten.lean`

This module epistemically compiles the Wave 17 Partition P2/P4 holographic
bulk-to-boundary dictionary from `1xHyRdU-TU8mjwZzKRRrzTAdvk8nPm7Or` (Turn 320):

1. **Four-Block Bulk-to-Boundary Operator Projections (`uvBoundaryBlock`, `irHorizonBlock`, `uvToIrBlock`, `irToUvBlock`):**
   - Replaces the raw transcript's custom `BulkOp` / `BoundaryOp` coordinate structs
     and zeroed-out off-diagonal `bulkGaugeTransform` with genuine Mathlib $4 \times 4$
     block matrices `Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R` and $2 \times 2$
     sector matrices `Matrix (Fin 2) (Fin 2) R`.
   - Proves exact block-diagonal and off-diagonal gauge covariance across all four
     holographic sectors (`bulk_four_sector_gauge_covariance`).
2. **Fefferman–Graham Radial Profile & Symplectic Wronskian Invariance:**
   - Defines `feffermanGrahamField J O z = J + z * O` and proves both boundary
     source/condensate extraction (`feffermanGrahamField_source_and_condensate`) and
     $z$-independence of the radial symplectic Wronskian
     `feffermanGrahamWronskian_z_independent`.
3. **Division-Free $2 \times 2$ Seiberg–Witten Self-Dual Spinor Curvature:**
   - Constructs `swSpinorCurvature ψ` on `Matrix (Fin 2) (Fin 2) R` and proves its
     exact tracelessness, determinant law $\det(F^+(\psi)) = -(\psi_0^2 + \psi_1^2)^2$,
     and Clifford norm-square identity $F^+(\psi)^2 = (\psi_0^2 + \psi_1^2)^2 I_2$
     (`swSpinorCurvature_trace_det_and_clifford_sq`).

### Three-Bucket Epistemic Audit Classification

* **BUCKET 1 — Constructively Proved Block-Matrix & Curvature Theorems (`[kernel_verified]`):**
  - `bulk_four_sector_gauge_covariance`, `feffermanGrahamField_source_and_condensate`,
    `feffermanGrahamWronskian_z_independent`, `swSpinorCurvature_trace_det_and_clifford_sq`,
    and `adscftBoundaryMat_noncommutative`.
* **BUCKET 2 — Eliminated Certificate Wrappers & Zeroed-Out Surrogates (Zero Remaining):**
  - `HolographicBoundaryCertificate : Prop` is eliminated; the zeroed-out off-diagonal
    `bulkGaugeTransform` in Turn 320 is replaced by full `Matrix.fromBlocks` multiplication.
* **BUCKET 3 — Asymptotically AdSPDE Boundary Value Problems (`[bucket_3_open_debt]`):**
  - Analytic elliptic regularity of the nonlinear Fefferman–Graham PDE expansion on
    infinite-dimensional asymptotically hyperbolic manifolds remains outside this
    finite block-matrix scope.
-/

namespace InfoGeometry.Holography.AdSCFT

open Matrix

variable {R : Type*} [Ring R]

/-- Upper-left UV boundary $2 \times 2$ block $\mathcal{B}_{\mathrm{UV}}(M)$ extracted
from a $4 \times 4$ bulk matrix $M \in \mathrm{Matrix}(\mathrm{Fin}\,2 \oplus \mathrm{Fin}\,2, \mathrm{Fin}\,2 \oplus \mathrm{Fin}\,2, R)$. -/
def uvBoundaryBlock (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  fun i j => M (Sum.inl i) (Sum.inl j)

/-- Lower-right IR horizon $2 \times 2$ block $\mathcal{B}_{\mathrm{IR}}(M)$ extracted
from a $4 \times 4$ bulk matrix $M$. -/
def irHorizonBlock (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  fun i j => M (Sum.inr i) (Sum.inr j)

/-- Upper-right UV-to-IR bulk-boundary propagator block $\mathcal{B}_{\mathrm{UV\to IR}}(M)$. -/
def uvToIrBlock (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  fun i j => M (Sum.inl i) (Sum.inr j)

/-- Lower-left IR-to-UV bulk-boundary propagator block $\mathcal{B}_{\mathrm{IR\to UV}}(M)$. -/
def irToUvBlock (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  fun i j => M (Sum.inr i) (Sum.inl j)

/-- Block-diagonal bulk gauge embedding $\mathcal{G}(U_{\mathrm{UV}}, U_{\mathrm{IR}}) = U_{\mathrm{UV}} \oplus U_{\mathrm{IR}}$. -/
def bulkGaugeBlockDiag (U_uv U_ir : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks U_uv 0 0 U_ir

/-- **Full Four-Sector Bulk-to-Boundary Gauge Covariance (`bulk_four_sector_gauge_covariance`):**
For any $4 \times 4$ bulk operator $M = \mathrm{fromBlocks}\;M_{11}\;M_{12}\;M_{21}\;M_{22}$
and any UV/IR gauge matrices $U_1, U_2, V_1, V_2 \in \mathrm{Matrix}(\mathrm{Fin}\,2, \mathrm{Fin}\,2, R)$:
1. $\mathcal{B}_{\mathrm{UV}}((U_1 \oplus U_2)\,M\,(V_1 \oplus V_2)) = U_1 M_{11} V_1$;
2. $\mathcal{B}_{\mathrm{IR}}((U_1 \oplus U_2)\,M\,(V_1 \oplus V_2)) = U_2 M_{22} V_2$;
3. $\mathcal{B}_{\mathrm{UV\to IR}}((U_1 \oplus U_2)\,M\,(V_1 \oplus V_2)) = U_1 M_{12} V_2$;
4. $\mathcal{B}_{\mathrm{IR\to UV}}((U_1 \oplus U_2)\,M\,(V_1 \oplus V_2)) = U_2 M_{21} V_1$. -/
theorem bulk_four_sector_gauge_covariance
    (M₁₁ M₁₂ M₂₁ M₂₂ U₁ U₂ V₁ V₂ : Matrix (Fin 2) (Fin 2) R) :
    uvBoundaryBlock
      (bulkGaugeBlockDiag U₁ U₂ * Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ *
        bulkGaugeBlockDiag V₁ V₂) = U₁ * M₁₁ * V₁ ∧
    irHorizonBlock
      (bulkGaugeBlockDiag U₁ U₂ * Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ *
        bulkGaugeBlockDiag V₁ V₂) = U₂ * M₂₂ * V₂ ∧
    uvToIrBlock
      (bulkGaugeBlockDiag U₁ U₂ * Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ *
        bulkGaugeBlockDiag V₁ V₂) = U₁ * M₁₂ * V₂ ∧
    irToUvBlock
      (bulkGaugeBlockDiag U₁ U₂ * Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ *
        bulkGaugeBlockDiag V₁ V₂) = U₂ * M₂₁ * V₁ := by
  unfold uvBoundaryBlock irHorizonBlock uvToIrBlock irToUvBlock bulkGaugeBlockDiag
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Asymptotic Fefferman–Graham radial field $\Phi(z) = J + z \cdot \mathcal{O}$ with
Dirichlet boundary source $J$ and Neumann holographic condensate $\mathcal{O}$. -/
def feffermanGrahamField (J O z : R) : R :=
  J + z * O

/-- **Boundary Source & Condensate Readout (`feffermanGrahamField_source_and_condensate`):**
Evaluating $\Phi(z)$ at $z = 0$ recovers the boundary source $J$, and the radial finite
difference $\Phi(1) - \Phi(0)$ recovers the holographic condensate $\mathcal{O}$. -/
theorem feffermanGrahamField_source_and_condensate (J O : R) :
    feffermanGrahamField J O 0 = J ∧
    feffermanGrahamField J O 1 - feffermanGrahamField J O 0 = O := by
  unfold feffermanGrahamField
  simp

/-- **Radial Symplectic Wronskian Invariance (`feffermanGrahamWronskian_z_independent`):**
For any two Fefferman–Graham radial profiles $\Phi_1(z) = J_1 + z O_1$ and
$\Phi_2(z) = J_2 + z O_2$, the symplectic radial Wronskian
$$W(\Phi_1, \Phi_2; z) = \Phi_1(z)\,O_2 - \Phi_2(z)\,O_1$$
is strictly independent of the radial coordinate $z$ and equals the boundary
symplectic pairing $J_1 O_2 - J_2 O_1$. -/
theorem feffermanGrahamWronskian_z_independent {R : Type*} [CommRing R] (J₁ O₁ J₂ O₂ z : R) :
    feffermanGrahamField J₁ O₁ z * O₂ - feffermanGrahamField J₂ O₂ z * O₁ =
      J₁ * O₂ - J₂ * O₁ := by
  unfold feffermanGrahamField
  ring

/-- Division-free $2 \times 2$ Seiberg–Witten self-dual spinor quadratic form
$$F^+(\psi) = \begin{pmatrix} \psi_0^2 - \psi_1^2 & 2\psi_0\psi_1 \\ 2\psi_1\psi_0 & \psi_1^2 - \psi_0^2 \end{pmatrix}.$$ -/
def swSpinorCurvature (ψ : Fin 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  !![ψ 0 ^ 2 - ψ 1 ^ 2, 2 * ψ 0 * ψ 1;
     2 * ψ 1 * ψ 0,     ψ 1 ^ 2 - ψ 0 ^ 2]

/-- **Trace, Determinant, & Clifford Square Law of `swSpinorCurvature`
(`swSpinorCurvature_trace_det_and_clifford_sq`):**
For every 2-component spinor $\psi : \mathrm{Fin}\,2 \to R$:
1. $\mathrm{Tr}(F^+(\psi)) = 0$ (traceless $\mathfrak{su}(2)_+$ endomorphism);
2. $\det(F^+(\psi)) = -(\psi_0^2 + \psi_1^2)^2$ (non-positive discriminant proportional to $-\|\psi\|^4$);
3. $F^+(\psi)^2 = (\psi_0^2 + \psi_1^2)^2 I_2$ (Clifford norm-square identity). -/
theorem swSpinorCurvature_trace_det_and_clifford_sq {R : Type*} [CommRing R] (ψ : Fin 2 → R) :
    Matrix.trace (swSpinorCurvature ψ) = 0 ∧
    Matrix.det (swSpinorCurvature ψ) = -((ψ 0 ^ 2 + ψ 1 ^ 2) ^ 2) ∧
    swSpinorCurvature ψ * swSpinorCurvature ψ =
      ((ψ 0 ^ 2 + ψ 1 ^ 2) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold swSpinorCurvature
    simp [Matrix.trace, Fin.sum_univ_two]
  · unfold swSpinorCurvature
    rw [Matrix.det_fin_two_of]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swSpinorCurvature, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Upper-triangular $2 \times 2$ boundary shear generator. -/
def adscftShearUpper : Matrix (Fin 2) (Fin 2) R :=
  !![1, 1; 0, 1]

/-- Lower-triangular $2 \times 2$ boundary shear generator. -/
def adscftShearLower : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 1, 1]

/-- Explicit non-commutativity witness on the $2 \times 2$ boundary matrix carrier
`Matrix (Fin 2) (Fin 2) R` (specialized at `R := ℤ`). -/
theorem adscftBoundaryMat_noncommutative :
    adscftShearUpper (R := ℤ) * adscftShearLower (R := ℤ) ≠
      adscftShearLower (R := ℤ) * adscftShearUpper (R := ℤ) := by
  intro hEq
  have h00 := congr_fun (congr_fun hEq 0) 0
  revert h00
  decide

end InfoGeometry.Holography.AdSCFT
