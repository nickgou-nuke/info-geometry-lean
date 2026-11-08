import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Section 59 / Super-Grassmannian: Operator Noncommutative Geometry of the Deformation Triad
Target: `InfoGeometry/SuperGrassmannian/WeylBerezinianDeformation.lean`

Grounds the deformation triad natively in the noncommutative operator algebra `Matrix (Fin 2) (Fin 2) R`:
1. Graded Supertrace of Matrix Operators: STr(M) = M₀₀ - M₁₁.
2. Z₂-Grading Projections: evenPart, oddPart, orthogonal direct sum decomposition M = evenPart M + oddPart M.
3. Supercommutator Cyclicity (Noncommutative Trace Identity): STr({X, Y}) = 0 for odd operators.
4. The Deformation Triad as Concrete Matrix Operators:
   - Scale Mode Operator S(p, q, σ) = !![p · σ, 0; 0, q · σ]
   - Chiral Mode Operator X(k₁, k₂) = !![0, k₁; k₂, 0]
   - Volume Mode Operator V(a) = !![a, 0; 0, a]
5. Noncommutative Lie Brackets of Deformations:
   - [S, X] = !![0, (p - q)σ k₁; -(p - q)σ k₂, 0] (scale and chiral modes do not commute unless p = q).
   - [S, X] = 0 when p = q (scale-invariant centralizer).
6. Chiral Nilpotence & Trace Property: X² = !![k₁ k₂, 0; 0, k₂ k₁], STr(X²) = 0.
7. Supertrace Mode Theorems:
   - STr(S(p, q, σ)) = (p - q) · σ
   - STr(S(p, p, σ)) = 0 (Balanced scale invariance)
   - STr(X(k₁, k₂)) = 0 (Chiral unimodularity)
   - STr(V(a)) = 0 (Volume unimodularity)
   - Total deformation splitting: STr(S + X + V) = (p - q) · σ.
8. Master verification certificate `WeylBerezinianDeformationCertificate`.
-/

namespace InfoGeometry.SuperGrassmannian.WeylBerezinian

open Matrix

variable {R : Type*} [CommRing R]

/-! ### 1. Graded Supertrace and Parity Projections on Matrix Operators -/

/-- The Graded Supertrace of a 2x2 matrix operator: STr(M) = M 0 0 - M 1 1. -/
def superTrace (M : Matrix (Fin 2) (Fin 2) R) : R :=
  M 0 0 - M 1 1

theorem superTrace_add (M N : Matrix (Fin 2) (Fin 2) R) :
    superTrace (M + N) = superTrace M + superTrace N := by
  dsimp [superTrace]
  ring

theorem superTrace_smul (r : R) (M : Matrix (Fin 2) (Fin 2) R) :
    superTrace (r • M) = r * superTrace M := by
  dsimp [superTrace]
  ring

theorem superTrace_neg (M : Matrix (Fin 2) (Fin 2) R) :
    superTrace (-M) = -superTrace M := by
  dsimp [superTrace]
  ring

/-- Even projection extracting diagonal blocks: !![M₀₀, 0; 0, M₁₁]. -/
def evenPart (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 0 0, 0; 0, M 1 1]

/-- Odd projection extracting off-diagonal blocks: !![0, M₀₁; M₁₀, 0]. -/
def oddPart (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, M 0 1; M 1 0, 0]

/-- Direct sum decomposition: M = evenPart M + oddPart M. -/
theorem even_add_odd (M : Matrix (Fin 2) (Fin 2) R) :
    evenPart M + oddPart M = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenPart, oddPart]

/-- Annihilation of supertrace on odd operators. -/
theorem superTrace_odd (M : Matrix (Fin 2) (Fin 2) R) :
    superTrace (oddPart M) = 0 := by
  dsimp [superTrace, oddPart]
  ring

/-- Noncommutative trace cyclicity: The supertrace of the anticommutator of any two odd operators vanishes. -/
theorem odd_anticommutator_superTrace (b1 c1 b2 c2 : R) :
    superTrace (!![(0:R), b1; c1, 0] * !![(0:R), b2; c2, 0] +
                !![(0:R), b2; c2, 0] * !![(0:R), b1; c1, 0]) = 0 := by
  dsimp [superTrace]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-! ### 2. The Three Deformation Modes as Concrete Operators -/

/-- Scale Mode Operator S(σ) on supercarrier (p | q): !![p · σ, 0; 0, q · σ]. -/
def scaleOperator (p q : R) (σ : R) : Matrix (Fin 2) (Fin 2) R :=
  !![p * σ, 0; 0, q * σ]

/-- Chiral Mode Operator X(k₁, k₂) mixing V⁺ and V⁻: !![0, k₁; k₂, 0]. -/
def chiralOperator (k₁ k₂ : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, k₁; k₂, 0]

/-- Volume Mode Operator V(a) preserving unimodular volume: !![a, 0; 0, a]. -/
def volumeOperator (a : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, 0; 0, a]

/-! ### 3. Noncommutative Lie Brackets and Operator Interactions -/

/-- Noncommutative Lie Bracket: The scale operator and chiral operator do NOT commute in general:
    [S, X] = !![0, (p - q)σ k₁; -(p - q)σ k₂, 0]. -/
theorem scale_chiral_commutator (p q σ k₁ k₂ : R) :
    scaleOperator p q σ * chiralOperator k₁ k₂ - chiralOperator k₁ k₂ * scaleOperator p q σ =
    !![0, (p - q) * σ * k₁; -(p - q) * σ * k₂, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [scaleOperator, chiralOperator, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  )

/-- Balanced Invariance: When p = q, the scale operator is central with respect to chiral mixing: [S, X] = 0. -/
theorem scale_chiral_commutator_balanced (p σ k₁ k₂ : R) :
    scaleOperator p p σ * chiralOperator k₁ k₂ - chiralOperator k₁ k₂ * scaleOperator p p σ = 0 := by
  rw [scale_chiral_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp
    try ring
  )

/-- Chiral operator square produces a diagonal even operator. -/
theorem chiral_square (k₁ k₂ : R) :
    chiralOperator (R := R) k₁ k₂ * chiralOperator (R := R) k₁ k₂ = !![k₁ * k₂, 0; 0, k₂ * k₁] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (
    simp [chiralOperator, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  )

/-- The supertrace of the square of any chiral operator vanishes identically: STr(X²) = 0. -/
theorem superTrace_chiral_square (k₁ k₂ : R) :
    superTrace (chiralOperator (R := R) k₁ k₂ * chiralOperator (R := R) k₁ k₂) = 0 := by
  rw [chiral_square]
  dsimp [superTrace]
  ring

/-! ### 4. The Supertrace Theorems on Matrix Operators -/

/-- The Weyl Scale Formula: STr(S(p, q, σ)) = (p - q) · σ. -/
theorem superTrace_scaleOperator (p q σ : R) :
    superTrace (scaleOperator (R := R) p q σ) = (p - q) * σ := by
  dsimp [superTrace, scaleOperator]
  ring

/-- The Balanced Super-Grassmannian Invariant: When p = q, STr(S) = 0. -/
theorem superTrace_scale_balanced (p σ : R) :
    superTrace (scaleOperator (R := R) p p σ) = 0 := by
  rw [superTrace_scaleOperator]
  ring

/-- Chiral Mode is Berezinian-Unimodular: STr(X) = 0. -/
theorem superTrace_chiralOperator (k₁ k₂ : R) :
    superTrace (chiralOperator (R := R) k₁ k₂) = 0 := by
  dsimp [superTrace, chiralOperator]
  ring

/-- Volume Mode is Berezinian-Unimodular: STr(V) = 0. -/
theorem superTrace_volumeOperator (a : R) :
    superTrace (volumeOperator (R := R) a) = 0 := by
  dsimp [superTrace, volumeOperator]
  ring

/-- Total Deformation Splitting Theorem:
    The supertrace isolates strictly the Weyl scale mode, while the chiral and volume modes drop out completely:
    STr(S + X + V) = (p - q) · σ. -/
theorem total_deformation_superTrace (p q σ k₁ k₂ a : R) :
    superTrace (scaleOperator p q σ + chiralOperator k₁ k₂ + volumeOperator a) = (p - q) * σ := by
  rw [superTrace_add, superTrace_add]
  rw [superTrace_scaleOperator, superTrace_chiralOperator, superTrace_volumeOperator]
  ring

/-! ### 5. Master Verification Certificate -/

/-- Certificate bundling all operator noncommutative geometry theorems of the deformation triad. -/
structure WeylBerezinianDeformationCertificate : Prop where
  superTrace_linear : ∀ (M N : Matrix (Fin 2) (Fin 2) ℝ), superTrace (M + N) = superTrace M + superTrace N
  even_odd_decomp : ∀ (M : Matrix (Fin 2) (Fin 2) ℝ), evenPart M + oddPart M = M
  anticommutator_trace : ∀ (b1 c1 b2 c2 : ℝ),
    superTrace (!![(0:ℝ), b1; c1, 0] * !![(0:ℝ), b2; c2, 0] +
                !![(0:ℝ), b2; c2, 0] * !![(0:ℝ), b1; c1, 0]) = 0
  commutator_bracket : ∀ (p q σ k₁ k₂ : ℝ),
    scaleOperator p q σ * chiralOperator k₁ k₂ - chiralOperator k₁ k₂ * scaleOperator p q σ =
    !![0, (p - q) * σ * k₁; -(p - q) * σ * k₂, 0]
  commutator_balanced : ∀ (p σ k₁ k₂ : ℝ),
    scaleOperator p p σ * chiralOperator k₁ k₂ - chiralOperator k₁ k₂ * scaleOperator p p σ = 0
  chiral_sq_superTrace : ∀ (k₁ k₂ : ℝ),
    superTrace (chiralOperator (R := ℝ) k₁ k₂ * chiralOperator (R := ℝ) k₁ k₂) = 0
  scale_mode : ∀ (p q σ : ℝ), superTrace (scaleOperator (R := ℝ) p q σ) = (p - q) * σ
  scale_balanced : ∀ (p σ : ℝ), superTrace (scaleOperator (R := ℝ) p p σ) = 0
  chiral_mode : ∀ (k₁ k₂ : ℝ), superTrace (chiralOperator (R := ℝ) k₁ k₂) = 0
  volume_mode : ∀ (a : ℝ), superTrace (volumeOperator (R := ℝ) a) = 0
  total_splitting : ∀ (p q σ k₁ k₂ a : ℝ),
    superTrace (scaleOperator p q σ + chiralOperator k₁ k₂ + volumeOperator a) = (p - q) * σ

/-- Master Compilation Theorem for the Noncommutative Operator Deformation Triad. -/
theorem compile_weyl_berezinian_deformation : WeylBerezinianDeformationCertificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M N; exact superTrace_add M N
  · intro M; exact even_add_odd M
  · intro b1 c1 b2 c2; exact odd_anticommutator_superTrace b1 c1 b2 c2
  · intro p q σ k₁ k₂; exact scale_chiral_commutator p q σ k₁ k₂
  · intro p σ k₁ k₂; exact scale_chiral_commutator_balanced p σ k₁ k₂
  · intro k₁ k₂; exact superTrace_chiral_square k₁ k₂
  · intro p q σ; exact superTrace_scaleOperator p q σ
  · intro p σ; exact superTrace_scale_balanced p σ
  · intro k₁ k₂; exact superTrace_chiralOperator k₁ k₂
  · intro a; exact superTrace_volumeOperator a
  · intro p q σ k₁ k₂ a; exact total_deformation_superTrace p q σ k₁ k₂ a

end InfoGeometry.SuperGrassmannian.WeylBerezinian
