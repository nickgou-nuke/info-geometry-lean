/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Erlangen 2.0: Algebraic Spin-Frame Identities on `M₂(ℂ)`

## Scope & Honest Manifest
This module proves concrete algebraic identities on the `2 × 2` complex matrix
algebra `M₂(ℂ)` equipped with the explicit Pauli spin-frame basis `sigma`:
- **BUCKET 1 (Closed Concrete Theorems)**: Jacobi identity, bracket
  antisymmetry, algebraic Bianchi identity, commutator tracelessness, Pauli
  squares, and explicit Pauli non-commutativity (`pauli_s1_s2_not_commute`) on
  `Matrix (Fin 2) (Fin 2) ℂ`.
- **Coordinate-Less `CliffordAlgebra Q` Invariance Owner**: Despite the
  historical filename `ErlangenCoordinateless`, this file does **not** formulate
  basis-free `O(Q)`-invariance on general `CliffordAlgebra Q`. In terms of Felix
  Klein's 1872 *Erlanger Programm* (Concluding Remarks & Footnote 37, Michigan
  `ABN7632.0001.001` / M. W. Haskell translation `arXiv:0807.3161v1`), this module
  proves basis-independent commutator/trace identities in the concrete `M₂(ℂ)` spin-frame
  representation (`sigma`), whereas the genuine coordinate-system-independent
  `CliffordAlgebra Q` invariant analytic formalism (including
  `CliffordAlgebra.equivOfIsometry` commutation with `involute`, `reverse`,
  `evenOdd`, `cliffordGradeProj`, `hTrace_cl`, `graceOperator`, `O(Q)`/`SO(Q)`
  invariant subalgebras, and `Cl(1,1)` `V₄`-invariance) lives in
  `InfoGeometry.Clifford.CoordinateLessCliffordInvariance` (together with
  `InfoGeometry.Clifford.GradedGraceContraction` and
  `InfoGeometry.Algebraic.CliffordSymmetryLift`).

## Key Theorems Proved Here
1. `jacobi_identity`: `[A,[B,C]] + [B,[C,A]] + [C,[A,B]] = 0`
2. `bracket_antisymm`: `[X, Y] = -[Y, X]`
3. `bianchi_is_jacobi`: `[[A,B],C] + [[B,C],A] + [[C,A],B] = 0`
4. `pauli_squares`: `σ_a² = I` for `a : Fin 4`
5. `pauli_s1_s2_not_commute`: `σ₁ * σ₂ ≠ σ₂ * σ₁`
6. `trace_of_commutator`: `Tr([A, B]) = 0`
-/

noncomputable section

namespace ErlangenCoordinateless

open Matrix

/-! ### Explicit Pauli spin-frame basis on `M₂(ℂ)` -/

def I2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def s1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def s3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def sigma : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => I2 | 1 => s1 | 2 => s2 | 3 => s3

/-! ### 1. Jacobi identity: basis-independent `M₂(ℂ)` Bianchi identity -/

/-- Commutator bracket [A, B] = A·B - B·A. -/
def bracket (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := A * B - B * A

/--
**Jacobi identity** (Genuine Proof):
  [A,[B,C]] + [B,[C,A]] + [C,[A,B]] = 0

This is the basis-independent `M₂(ℂ)` matrix-commutator counterpart of the
Bianchi identities (for genuine basis-free `O(Q)`-invariance on
`CliffordAlgebra Q`, see `InfoGeometry.Clifford.CoordinateLessCliffordInvariance`).
It holds for any associative algebra (here `M₂(ℂ)`) and is the defining
property of a Lie algebra.

Proof: expand all commutators and cancel terms by ring.
-/
theorem jacobi_identity (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    bracket A (bracket B C) + bracket B (bracket C A) + bracket C (bracket A B) = 0 := by
  dsimp [bracket]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two] <;>
    ring_nf

/-- Bracket antisymmetry: [A,B] = -[B,A]. -/
theorem bracket_antisymm (X Y : Matrix (Fin 2) (Fin 2) ℂ) : bracket X Y = -bracket Y X := by
  dsimp [bracket]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply, Fin.sum_univ_two]

/--
**Bianchi = Jacobi** (Genuine Proof):
  [[A,B],C] + [[B,C],A] + [[C,A],B] = 0

This is the algebraic Bianchi identity — the curvature consistency
condition expressed as a purely algebraic Jacobi identity.
-/
theorem bianchi_is_jacobi (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    bracket (bracket A B) C + bracket (bracket B C) A + bracket (bracket C A) B = 0 := by
  have h1 : bracket (bracket A B) C = -bracket C (bracket A B) := bracket_antisymm _ _
  have h2 : bracket (bracket C A) B = -bracket B (bracket C A) := bracket_antisymm _ _
  have h3 : bracket (bracket B C) A = -bracket A (bracket B C) := bracket_antisymm _ _
  rw [h1, h2, h3]
  have h := jacobi_identity A B C
  -- Goal: -[C,[A,B]] + -[B,[C,A]] + -[A,[B,C]] = 0
  -- But h says: [A,[B,C]] + [B,[C,A]] + [C,[A,B]] = 0
  -- So goal = -([A,[B,C]] + [B,[C,A]] + [C,[A,B]]) = -0 = 0 (by ring)
  calc
    (-bracket C (bracket A B)) + (-bracket A (bracket B C)) + (-bracket B (bracket C A))
        = -(bracket A (bracket B C) + bracket B (bracket C A) + bracket C (bracket A B)) := by
          ext i j; fin_cases i <;> fin_cases j <;>
            simp [Matrix.add_apply, Matrix.neg_apply, bracket,
              Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two] <;> ring
    _ = -(0 : Matrix (Fin 2) (Fin 2) ℂ) := by rw [h]
    _ = 0 := by simp

/-! ### 2. Pauli basis structure -/

/--
**Pauli squares**: σ_a² = I for all a ∈ {0,1,2,3}.
-/
theorem pauli_squares (a : Fin 4) : sigma a * sigma a = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sigma, I2, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit non-commutativity of the Pauli matrices `σ₁` and `σ₂` in `M₂(ℂ)`. -/
theorem pauli_s1_s2_not_commute : s1 * s2 ≠ s2 * s1 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).im) h
  simp [s1, s2, Matrix.mul_apply, Fin.sum_univ_two] at h00
  norm_num at h00

/-! ### 3. Trace as basis-independent `M₂(ℂ)` linear invariant -/

/--
**Trace of commutator** (Genuine Proof):
  Tr([A, B]) = 0

The matrix trace is a basis-independent `M₂(ℂ)` linear invariant (for genuine
basis-free `O(Q)`-invariance on `CliffordAlgebra Q`, see
`InfoGeometry.Clifford.CoordinateLessCliffordInvariance`). All commutators are
traceless — this is the algebraic reason curvature forms are traceless.
-/
theorem trace_of_commutator (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (bracket A B) = 0 := by
  dsimp [bracket, Matrix.trace]
  simp [Fin.sum_univ_two, Matrix.mul_apply]
  ring

/-! ### 4. Concrete `M₂(ℂ)` spin-frame capstone -/

/--
**Erlangen 2.0 Concrete `M₂(ℂ)` Spin-Frame Capstone** (Genuine Proofs):
assembles the Jacobi identity, bracket antisymmetry, algebraic Bianchi identity,
tracelessness of commutators, and Pauli involutivity on the concrete matrix
algebra `Matrix (Fin 2) (Fin 2) ℂ` (`pauli_s1_s2_not_commute` establishes
explicit Pauli non-commutativity alongside it).

In reference to Felix Klein's 1872 *Erlanger Programm* Concluding Remarks +
Footnote 37 (`ABN7632.0001.001` / `arXiv:0807.3161v1`), these are basis-independent
matrix identities in the concrete `M₂(ℂ)` spin-frame representation, whereas
the genuine coordinate-system-independent `O(Q)`-invariant `CliffordAlgebra Q`
analytic formalism is owned by
`InfoGeometry.Clifford.CoordinateLessCliffordInvariance`.
-/
theorem erlangen_coordinateless_capstone :
    (-- Jacobi identity: the coordinateless Bianchi
     ∀ A B C : Matrix (Fin 2) (Fin 2) ℂ,
       bracket A (bracket B C) + bracket B (bracket C A) + bracket C (bracket A B) = 0) ∧
    (-- Bracket antisymmetry: [A,B] = -[B,A]
     ∀ X Y : Matrix (Fin 2) (Fin 2) ℂ, bracket X Y = -bracket Y X) ∧
    (-- Bianchi = Jacobi: [[A,B],C] + [[B,C],A] + [[C,A],B] = 0
     ∀ A B C : Matrix (Fin 2) (Fin 2) ℂ,
       bracket (bracket A B) C + bracket (bracket B C) A + bracket (bracket C A) B = 0) ∧
    (-- Trace of commutator: tr([A,B]) = 0
     ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, Matrix.trace (bracket A B) = 0) ∧
    (-- Pauli squares: σ_a² = I for all a
     ∀ a : Fin 4, sigma a * sigma a = (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact jacobi_identity
  · exact bracket_antisymm
  · exact bianchi_is_jacobi
  · exact trace_of_commutator
  · exact pauli_squares

end ErlangenCoordinateless
