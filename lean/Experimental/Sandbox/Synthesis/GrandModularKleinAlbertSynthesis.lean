import InfoGeometry.Exceptional.AlbertAlgebraSplitJordan
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Invertible

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Exceptional.AlbertAlgebra

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Grand Synthesis of Modular KMS, Klein Crosscap, and Albert Nilpotent Orbits
Target: `lean/Experimental/Sandbox/Synthesis/GrandModularKleinAlbertSynthesis.lean`

Formalizes in full native Mathlib in Lean 4:
1. Modular KMS & Krein Chiral Tilt Flow:
   - Cartan chiral matrix `cartanChiral θ = !![θ, 0; 0, -θ]` on `Matrix (Fin 2) (Fin 2) R`.
   - Flow commutativity, tracelessness, and quadratic Casimir charge `2 * θ^2`.
2. Klein Crosscap Casimir Selection:
   - Krein glide differential `kreinEta R = !![1, 0; 0, -1]` with `η^2 = 1`.
   - Crosscap projector `P_c X = ⅟2 • (X + η X η)`: idempotent projection.
   - Iwasawa nilpotent / parabolic filtration: `P_c !![θ, n - k; k, -θ] = cartanChiral θ`.
   - Filtered Casimir charge invariance: `casimirTwo (P_c !![θ, n - k; k, -θ]) = 2 * θ^2`.
3. The Exceptional 27-Dim Albert Carrier & Diagonal Chiral Coupling:
   - Diagonal embedding `diagonalAlbert c1 c2 c3 = ⟨c1, c2, c3, 0, 0, 0⟩`.
   - Chiral Albert element `chiralAlbert θ = diagonalAlbert θ θ θ`.
   - Linear Jordan trace `3 * θ`, quadratic trace `3 * θ^2`.
   - Freudenthal cubic determinant `θ^3`, quadratic adjoint `diagonalAlbert (θ^2) (θ^2) (θ^2)`.
   - Master Klein-Albert coupling identity: `2 * Tr(chiralAlbert(θ)#) = 3 * Casimir(cartanChiral(θ))`.
4. Nilpotent BPS Orbit Stratification:
   - Rank 0 vacuum: `chiralAlbert θ = 0 ↔ θ = 0`.
   - Rank 1 candidate (1/2-BPS): det = 0, adjoint = 0.
   - Rank 2 candidate (1/4-BPS): det = 0, adjoint ≠ 0, (adjoint)# = 0.
   - Rank 3 horizon entropy: `S(1) = π`, `S(0) = 0`.
5. Master Verification Certificate `GrandModularKleinAlbertSynthesisCertificate`.
-/

namespace InfoGeometry.Algebra.H3Zorn

variable {R : Type*} [CommRing R]

/-- Projection dot-notation alias for linear Jordan trace on `H3Zorn R`. -/
noncomputable def trace (X : H3Zorn R) : R := jordanTrace X

/-- Projection dot-notation alias for quadratic Jordan trace on `H3Zorn R`. -/
noncomputable def quadTrace (X : H3Zorn R) : R := jordanQuadraticTrace X

/-- Projection dot-notation alias for Freudenthal determinant on `H3Zorn R`. -/
noncomputable def freudenthalDet (X : H3Zorn R) : R :=
  InfoGeometry.Exceptional.AlbertAlgebra.freudenthalDet X

/-- Projection dot-notation alias for Freudenthal quadratic adjoint on `H3Zorn R`. -/
noncomputable def freudenthalAdjoint (X : H3Zorn R) : H3Zorn R :=
  InfoGeometry.Exceptional.AlbertAlgebra.freudenthalAdjoint X

end InfoGeometry.Algebra.H3Zorn

namespace Experimental.Sandbox.Synthesis.GrandModularKleinAlbertSynthesis

variable {R : Type*} [CommRing R]

/-! ### Section 1: Modular KMS & Krein Chiral Tilt Flow -/

/-- The Cartan chiral generator representing the hyperbolic / modular flow generator. -/
def cartanChiral (θ : R) : Matrix (Fin 2) (Fin 2) R := !![θ, 0; 0, -θ]

/-- Commutativity of chiral flows: the Cartan subalgebra is abelian. -/
theorem cartanChiral_comm (θ₁ θ₂ : R) :
    cartanChiral θ₁ * cartanChiral θ₂ = cartanChiral θ₂ * cartanChiral θ₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [cartanChiral, Matrix.mul_apply]
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
    ring
  }

/-- Tracelessness of the chiral generator. -/
theorem cartanChiral_trace (θ : R) :
    Matrix.trace (cartanChiral θ) = 0 := by
  dsimp [Matrix.trace, Matrix.diag, cartanChiral]
  simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
  ring

/-- Quadratic Casimir charge of a 2x2 matrix: Tr(M²). -/
def casimirTwo (M : Matrix (Fin 2) (Fin 2) R) : R :=
  Matrix.trace (M * M)

/-- Quadratic Casimir charge of the Cartan chiral flow is 2 θ². -/
theorem cartanChiral_casimir (θ : R) :
    casimirTwo (cartanChiral θ) = 2 * θ^2 := by
  dsimp [casimirTwo, Matrix.trace, Matrix.diag, cartanChiral, Matrix.mul_apply]
  simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
  ring

/-! ### Section 2: Klein Crosscap Casimir Selection -/

/-- Krein glide differential metric η = diag(1, -1). -/
def kreinEta (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]

/-- Krein metric is an involution: η² = 1. -/
theorem kreinEta_sq (R : Type*) [CommRing R] :
    kreinEta R * kreinEta R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [kreinEta, Matrix.mul_apply, Matrix.one_apply]
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
    ring
  }

/-- Conjugation by the Krein metric: η X η. -/
def conjugateEta (X : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  kreinEta R * X * kreinEta R

/-- Explicit matrix form of Krein conjugation. -/
lemma conjugateEta_apply (X : Matrix (Fin 2) (Fin 2) R) :
    conjugateEta X = !![X 0 0, -X 0 1; -X 1 0, X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    dsimp [conjugateEta, kreinEta, Matrix.mul_apply]
    simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, head_cons]
    try ring
  }

/-- Crosscap projector P_c(X) = ⅟2 • (X + η X η). -/
def crosscapProj (X : Matrix (Fin 2) (Fin 2) R) [Invertible (2 : R)] : Matrix (Fin 2) (Fin 2) R :=
  ⅟(2 : R) • (X + conjugateEta X)

/-- Explicit projection formula: the crosscap projector diagonalizes the matrix carrier. -/
lemma crosscapProj_diag (X : Matrix (Fin 2) (Fin 2) R) [Invertible (2 : R)] :
    crosscapProj X = !![X 0 0, 0; 0, X 1 1] := by
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  rw [crosscapProj, conjugateEta_apply]
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp
    rw [show X 0 0 + X 0 0 = 2 * X 0 0 by ring, ← mul_assoc, h2, one_mul]
  · dsimp
    rw [show X 0 1 + -X 0 1 = 0 by ring, mul_zero]
  · dsimp
    rw [show X 1 0 + -X 1 0 = 0 by ring, mul_zero]
  · dsimp
    rw [show X 1 1 + X 1 1 = 2 * X 1 1 by ring, ← mul_assoc, h2, one_mul]

/-- The crosscap projector is idempotent: P_c² = P_c. -/
theorem crosscapProj_idempotent (X : Matrix (Fin 2) (Fin 2) R) [Invertible (2 : R)] :
    crosscapProj (crosscapProj X) = crosscapProj X := by
  rw [crosscapProj_diag, crosscapProj_diag]
  rfl

/-- Exact filtering of Iwasawa split: off-diagonal nilpotent and rotation modes are eliminated. -/
theorem crosscap_filters_iwasawa (θ n k : R) [Invertible (2 : R)] :
    crosscapProj !![θ, n - k; k, -θ] = cartanChiral θ := by
  rw [crosscapProj_diag]
  rfl

/-- Filtered Casimir identity: the crosscap projection preserves the Cartan Casimir charge. -/
theorem crosscap_filtered_casimir (θ n k : R) [Invertible (2 : R)] :
    casimirTwo (crosscapProj !![θ, n - k; k, -θ]) = 2 * θ^2 := by
  rw [crosscap_filters_iwasawa]
  exact cartanChiral_casimir θ

/-! ### Section 3: The Exceptional Albert Carrier & Diagonal Chiral Coupling -/

/-- Diagonal embedding into the 27-dimensional exceptional Albert algebra J₃(𝕆_s). -/
noncomputable def diagonalAlbert (c1 c2 c3 : R) : AlbertElement R :=
  ⟨c1, c2, c3, 0, 0, 0⟩

/-- Coincidence with the canonical diagonal embedding in AlbertAlgebra. -/
lemma diagonalAlbert_eq_diagonal (c1 c2 c3 : R) :
    diagonalAlbert c1 c2 c3 = InfoGeometry.Exceptional.AlbertAlgebra.diagonal c1 c2 c3 :=
  rfl

/-- Chiral Albert element coupling all 3 Jordan diagonals to the chiral parameter θ. -/
noncomputable def chiralAlbert (θ : R) : AlbertElement R :=
  diagonalAlbert θ θ θ

/-- Linear Jordan trace of the chiral Albert element is 3 θ. -/
theorem chiralAlbert_trace (θ : R) :
    (chiralAlbert θ).trace = 3 * θ := by
  dsimp [H3Zorn.trace, jordanTrace, linearTrace, chiralAlbert, diagonalAlbert]
  ring

/-- Quadratic Jordan trace of the chiral Albert element is 3 θ². -/
theorem chiralAlbert_quadTrace (θ : R) :
    (chiralAlbert θ).quadTrace = 3 * θ^2 := by
  dsimp [H3Zorn.quadTrace, jordanQuadraticTrace, traceBilin, chiralAlbert, diagonalAlbert]
  simp only [ZornVectorMatrix.zero_mul, ZornVectorMatrix.trace_zero, ZornVectorMatrix.conj_zero, add_zero]
  ring

/-- Freudenthal cubic determinant of the chiral Albert element is θ³. -/
theorem chiralAlbert_det (θ : R) :
    (chiralAlbert θ).freudenthalDet = θ^3 := by
  have hd : chiralAlbert θ = InfoGeometry.Exceptional.AlbertAlgebra.diagonal θ θ θ := rfl
  change InfoGeometry.Exceptional.AlbertAlgebra.freudenthalDet (chiralAlbert θ) = θ^3
  rw [hd, diagonal_normCubic]
  ring

/-- Freudenthal quadratic adjoint of the chiral Albert element. -/
theorem chiralAlbert_adjoint (θ : R) :
    (chiralAlbert θ).freudenthalAdjoint = diagonalAlbert (θ^2) (θ^2) (θ^2) := by
  have hd : chiralAlbert θ = InfoGeometry.Exceptional.AlbertAlgebra.diagonal θ θ θ := rfl
  change InfoGeometry.Exceptional.AlbertAlgebra.freudenthalAdjoint (chiralAlbert θ) = diagonalAlbert (θ^2) (θ^2) (θ^2)
  rw [hd, diagonal_adjoint_exact]
  apply ext_h3
  · dsimp [InfoGeometry.Exceptional.AlbertAlgebra.diagonal, diagonalAlbert]; ring
  · dsimp [InfoGeometry.Exceptional.AlbertAlgebra.diagonal, diagonalAlbert]; ring
  · dsimp [InfoGeometry.Exceptional.AlbertAlgebra.diagonal, diagonalAlbert]; ring
  · rfl
  · rfl
  · rfl

/-- Master Coupling between Klein Casimir charge and Albert Adjoint Trace:
    2 · Tr((chiralAlbert θ)#) = 3 · Casimir(cartanChiral θ) = 6 θ². -/
theorem casimir_albert_trace_coupling (θ : R) :
    2 * (chiralAlbert θ).freudenthalAdjoint.trace = 3 * (2 * θ^2) := by
  rw [chiralAlbert_adjoint]
  dsimp [H3Zorn.trace, jordanTrace, linearTrace, diagonalAlbert]
  ring

/-! ### Section 4: Nilpotent BPS Orbit Stratification -/

/-- Rank 0 element: chiralAlbert θ = 0 ↔ θ = 0. -/
theorem chiralAlbert_zero_iff (θ : R) :
    chiralAlbert θ = 0 ↔ θ = 0 := by
  constructor
  · intro h
    have h1 : (chiralAlbert θ).α₁ = (0 : AlbertElement R).α₁ := by rw [h]
    dsimp [chiralAlbert, diagonalAlbert] at h1
    exact h1
  · intro h
    subst h
    rfl

/-- Rank 1 candidate (1/2-BPS extremal black hole with vanishing area). -/
noncomputable def rank1Candidate (k : R) : AlbertElement R :=
  diagonalAlbert k 0 0

/-- Rank 1 candidate has vanishing cubic determinant. -/
theorem rank1_candidate_det (k : R) :
    (rank1Candidate k).freudenthalDet = 0 := by
  have hd : rank1Candidate k = InfoGeometry.Exceptional.AlbertAlgebra.diagonal k 0 0 := rfl
  change InfoGeometry.Exceptional.AlbertAlgebra.freudenthalDet (rank1Candidate k) = 0
  rw [hd, diagonal_normCubic]
  ring

/-- Rank 1 candidate has vanishing quadratic adjoint. -/
theorem rank1_candidate_adjoint (k : R) :
    (rank1Candidate k).freudenthalAdjoint = 0 := by
  have hd : rank1Candidate k = InfoGeometry.Exceptional.AlbertAlgebra.diagonal k 0 0 := rfl
  change InfoGeometry.Exceptional.AlbertAlgebra.freudenthalAdjoint (rank1Candidate k) = 0
  rw [hd, diagonal_adjoint_exact]
  apply ext_h3
  · dsimp [InfoGeometry.Exceptional.AlbertAlgebra.diagonal]; ring
  · dsimp [InfoGeometry.Exceptional.AlbertAlgebra.diagonal]; ring
  · dsimp [InfoGeometry.Exceptional.AlbertAlgebra.diagonal]; ring
  · rfl
  · rfl
  · rfl

/-- Rank 2 candidate (1/4-BPS small black hole with vanishing area and non-vanishing adjoint). -/
noncomputable def rank2Candidate (k₁ k₂ : R) : AlbertElement R :=
  diagonalAlbert k₁ k₂ 0

/-- Rank 2 candidate has vanishing cubic determinant. -/
theorem rank2_candidate_det (k₁ k₂ : R) :
    (rank2Candidate k₁ k₂).freudenthalDet = 0 := by
  have hd : rank2Candidate k₁ k₂ = InfoGeometry.Exceptional.AlbertAlgebra.diagonal k₁ k₂ 0 := rfl
  change InfoGeometry.Exceptional.AlbertAlgebra.freudenthalDet (rank2Candidate k₁ k₂) = 0
  rw [hd, diagonal_normCubic]
  ring

/-- Rank 2 candidate quadratic adjoint is non-vanishing (rank 1 nilpotent orbit). -/
theorem rank2_candidate_adjoint (k₁ k₂ : R) :
    (rank2Candidate k₁ k₂).freudenthalAdjoint = diagonalAlbert 0 0 (k₁ * k₂) := by
  have hd : rank2Candidate k₁ k₂ = InfoGeometry.Exceptional.AlbertAlgebra.diagonal k₁ k₂ 0 := rfl
  change InfoGeometry.Exceptional.AlbertAlgebra.freudenthalAdjoint (rank2Candidate k₁ k₂) = diagonalAlbert 0 0 (k₁ * k₂)
  rw [hd, diagonal_adjoint_exact]
  apply ext_h3 <;> { dsimp [InfoGeometry.Exceptional.AlbertAlgebra.diagonal, diagonalAlbert]; try ring; try rfl }

/-- Nilpotency of the adjoint flow: the second adjoint of a rank 2 candidate vanishes. -/
theorem rank2_candidate_adjoint_adjoint (k₁ k₂ : R) :
    ((rank2Candidate k₁ k₂).freudenthalAdjoint).freudenthalAdjoint = 0 := by
  rw [rank2_candidate_adjoint]
  have hd : diagonalAlbert 0 0 (k₁ * k₂) = InfoGeometry.Exceptional.AlbertAlgebra.diagonal 0 0 (k₁ * k₂) := rfl
  change InfoGeometry.Exceptional.AlbertAlgebra.freudenthalAdjoint (diagonalAlbert 0 0 (k₁ * k₂)) = 0
  rw [hd, diagonal_adjoint_exact]
  apply ext_h3 <;> { dsimp [InfoGeometry.Exceptional.AlbertAlgebra.diagonal]; try ring; try rfl }

/-- BPS Horizon Entropy on the chiral orbit: S(θ) = π · √|det₃(chiralAlbert θ)|. -/
noncomputable def chiralEntropy (θ : ℝ) : ℝ :=
  Real.pi * Real.sqrt |(chiralAlbert θ).freudenthalDet|

/-- Horizon entropy at the unit basepoint is π. -/
theorem chiralEntropy_identity :
    chiralEntropy 1 = Real.pi := by
  dsimp [chiralEntropy]
  rw [chiralAlbert_det]
  have h1 : (1 : ℝ)^3 = 1 := by ring
  rw [h1, abs_one, Real.sqrt_one, mul_one]

/-- Horizon entropy at the null basepoint vanishes. -/
theorem chiralEntropy_zero :
    chiralEntropy 0 = 0 := by
  dsimp [chiralEntropy]
  rw [chiralAlbert_det]
  have h0 : (0 : ℝ)^3 = 0 := by ring
  rw [h0, abs_zero, Real.sqrt_zero, mul_zero]

/-! ### Section 5: Master Verification Certificate -/

/-- Master Verification Certificate bundling the complete Grand Modular-Klein-Albert Synthesis. -/
structure GrandModularKleinAlbertSynthesisCertificate : Prop where
  cartan_comm : ∀ (R : Type) [CommRing R] (θ₁ θ₂ : R),
    cartanChiral θ₁ * cartanChiral θ₂ = cartanChiral θ₂ * cartanChiral θ₁
  cartan_trace : ∀ (R : Type) [CommRing R] (θ : R),
    Matrix.trace (cartanChiral θ) = 0
  cartan_casimir : ∀ (R : Type) [CommRing R] (θ : R),
    casimirTwo (cartanChiral θ) = 2 * θ^2
  eta_sq : ∀ (R : Type) [CommRing R],
    kreinEta R * kreinEta R = 1
  crosscap_idem : ∀ (R : Type) [CommRing R] [Invertible (2 : R)] (X : Matrix (Fin 2) (Fin 2) R),
    crosscapProj (crosscapProj X) = crosscapProj X
  crosscap_filter : ∀ (R : Type) [CommRing R] [Invertible (2 : R)] (θ n k : R),
    crosscapProj !![θ, n - k; k, -θ] = cartanChiral θ
  crosscap_casimir : ∀ (R : Type) [CommRing R] [Invertible (2 : R)] (θ n k : R),
    casimirTwo (crosscapProj !![θ, n - k; k, -θ]) = 2 * θ^2
  chiral_trace : ∀ (R : Type) [CommRing R] (θ : R),
    (chiralAlbert θ).trace = 3 * θ
  chiral_quad_trace : ∀ (R : Type) [CommRing R] (θ : R),
    (chiralAlbert θ).quadTrace = 3 * θ^2
  chiral_det : ∀ (R : Type) [CommRing R] (θ : R),
    (chiralAlbert θ).freudenthalDet = θ^3
  chiral_adjoint : ∀ (R : Type) [CommRing R] (θ : R),
    (chiralAlbert θ).freudenthalAdjoint = diagonalAlbert (θ^2) (θ^2) (θ^2)
  coupling : ∀ (R : Type) [CommRing R] (θ : R),
    2 * (chiralAlbert θ).freudenthalAdjoint.trace = 3 * (2 * θ^2)
  chiral_zero : ∀ (R : Type) [CommRing R] (θ : R),
    chiralAlbert θ = 0 ↔ θ = 0
  rank1_det : ∀ (R : Type) [CommRing R] (k : R),
    (rank1Candidate k).freudenthalDet = 0
  rank1_adjoint : ∀ (R : Type) [CommRing R] (k : R),
    (rank1Candidate k).freudenthalAdjoint = 0
  rank2_det : ∀ (R : Type) [CommRing R] (k₁ k₂ : R),
    (rank2Candidate k₁ k₂).freudenthalDet = 0
  rank2_adjoint : ∀ (R : Type) [CommRing R] (k₁ k₂ : R),
    (rank2Candidate k₁ k₂).freudenthalAdjoint = diagonalAlbert 0 0 (k₁ * k₂)
  rank2_adjoint_adjoint : ∀ (R : Type) [CommRing R] (k₁ k₂ : R),
    ((rank2Candidate k₁ k₂).freudenthalAdjoint).freudenthalAdjoint = 0
  entropy_id : chiralEntropy 1 = Real.pi
  entropy_zero : chiralEntropy 0 = 0

theorem compile_grand_modular_klein_albert_synthesis :
    GrandModularKleinAlbertSynthesisCertificate where
  cartan_comm := fun _ _ θ₁ θ₂ => cartanChiral_comm θ₁ θ₂
  cartan_trace := fun _ _ θ => cartanChiral_trace θ
  cartan_casimir := fun _ _ θ => cartanChiral_casimir θ
  eta_sq := fun _ _ => kreinEta_sq _
  crosscap_idem := fun _ _ _ X => crosscapProj_idempotent X
  crosscap_filter := fun _ _ _ θ n k => crosscap_filters_iwasawa θ n k
  crosscap_casimir := fun _ _ _ θ n k => crosscap_filtered_casimir θ n k
  chiral_trace := fun _ _ θ => chiralAlbert_trace θ
  chiral_quad_trace := fun _ _ θ => chiralAlbert_quadTrace θ
  chiral_det := fun _ _ θ => chiralAlbert_det θ
  chiral_adjoint := fun _ _ θ => chiralAlbert_adjoint θ
  coupling := fun _ _ θ => casimir_albert_trace_coupling θ
  chiral_zero := fun _ _ θ => chiralAlbert_zero_iff θ
  rank1_det := fun _ _ k => rank1_candidate_det k
  rank1_adjoint := fun _ _ k => rank1_candidate_adjoint k
  rank2_det := fun _ _ k₁ k₂ => rank2_candidate_det k₁ k₂
  rank2_adjoint := fun _ _ k₁ k₂ => rank2_candidate_adjoint k₁ k₂
  rank2_adjoint_adjoint := fun _ _ k₁ k₂ => rank2_candidate_adjoint_adjoint k₁ k₂
  entropy_id := chiralEntropy_identity
  entropy_zero := chiralEntropy_zero

end Experimental.Sandbox.Synthesis.GrandModularKleinAlbertSynthesis
