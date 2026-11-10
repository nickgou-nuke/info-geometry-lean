/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.H3ZornCubicNormStructure
import InfoGeometry.Algebra.H3ZornCarrierBasis

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

/-!
# Section 50: The Split Exceptional Albert Algebra J₃(𝕆_s) & Freudenthal Determinant
Target: `InfoGeometry/Exceptional/AlbertAlgebraSplitJordan.lean`

Formalizes the split Albert Jordan carrier via H₃(𝕆_s):
1. The carrier `H3Zorn R`; its actual real-vector-space dimension is established by
   `albert_algebra_dimension` below using the explicit 27-coordinate basis in
   `InfoGeometry.Algebra.H3ZornCarrierBasis`.
   - 3 real diagonal scalars: α₁, α₂, α₃.
   - 3 off-diagonal split-octonions: a, b, c ∈ ZornVectorMatrix R (8 dimensions each).
2. The Jordan Linear and Quadratic Traces:
   - Linear trace: Tr(X) = α₁ + α₂ + α₃.
   - Quadratic trace form: traceBilin X Y.
   - Tr(1) = 3 and Tr(1²) = 3.
3. The Freudenthal Cubic Determinant:
   - det₃(X) = normCubic X.
   - det₃(1) = 1.
   - Homogeneity: det₃(k • X) = k³ det₃(X).
4. The Freudenthal Quadratic Adjoint X#:
   - X# = adjointQuad X.
   - 1# = 1.
   - Homogeneity: (k • X)# = k² • X#.
   - Master cubic adjoint involution: (X#)# = N(X) • X.
5. Diagonal Subalgebra & Minors:
   - Exact minor matching on diagonal elements.
   - Diagonal contraction: Tr(X, X#) = 3 det₃(X).
6. Jordan Cross Product & Trace Complement:
   - X × 1 = Tr(X) • 1 - X.
   - X × X = 2 • X#.
-/

namespace InfoGeometry.Exceptional.AlbertAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem albertAlgebraSplitJordan_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

variable {R : Type*} [Ring R]

/-! ### 1. The Albert Carrier -/

/-- The exceptional Jordan algebra J₃(𝕆_s) carrier,
    structured as 3 diagonal scalars and 3 split-octonionic Zorn vector matrices. -/
abbrev AlbertElement (R : Type*) [Ring R] := H3Zorn R

/-- The real Albert carrier has dimension 27, by its explicit coordinate basis. -/
theorem albert_algebra_dimension : Module.finrank ℝ (AlbertElement ℝ) = 27 := by
  exact InfoGeometry.Algebra.finrank_h3zorn

/-! ### 2. The Jordan Linear and Quadratic Traces -/

/-- The Jordan linear trace: Tr(X) = α₁ + α₂ + α₃. -/
noncomputable def jordanTrace (X : AlbertElement R) : R := linearTrace X

/-- The Jordan quadratic trace: Tr(X²) via the canonical bilinear trace form. -/
noncomputable def jordanQuadraticTrace (X : AlbertElement R) : R := traceBilin X X

/-- Trace of the identity element is 3. -/
@[simp]
theorem trace_albert_identity : jordanTrace (1 : AlbertElement R) = 3 := by
  simp [jordanTrace, linearTrace, one_readback]
  norm_num

/-- Quadratic trace of the identity element is 3. -/
@[simp]
theorem quadTrace_albert_identity : jordanQuadraticTrace (1 : AlbertElement R) = 3 := by
  rw [jordanQuadraticTrace, traceBilin_one]
  exact trace_albert_identity

/-! ### 3. The Freudenthal Cubic Determinant -/

/-- The Freudenthal cubic determinant det₃(X) = N(X). -/
noncomputable def freudenthalDet (X : AlbertElement R) : R := normCubic X

/-- Identity element has Freudenthal determinant 1. -/
@[simp]
theorem det_albert_identity : freudenthalDet (1 : AlbertElement R) = 1 := by
  rw [freudenthalDet]
  exact normCubic_one

/-- Homogeneity of degree 3: det₃(k • X) = k³ det₃(X). -/
theorem freudenthalDet_homogeneity {R : Type*} [CommRing R] (k : R) (X : AlbertElement R) :
    freudenthalDet (k • X) = k^3 * freudenthalDet X := by
  simp only [freudenthalDet, normCubic, smul_readback, ZornVectorMatrix.norm_smul,
    ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul,
    ZornVectorMatrix.trace_smul]
  ring

/-! ### 4. The Freudenthal Adjoint (Cross-Product Matrix X#) -/

/-- The Freudenthal quadratic adjoint X#. -/
noncomputable def freudenthalAdjoint (X : AlbertElement R) : AlbertElement R := adjointQuad X

/-- Identity element is fixed by the Freudenthal adjoint. -/
@[simp]
theorem adjoint_albert_identity : freudenthalAdjoint (1 : AlbertElement R) = 1 := by
  exact adjointQuad_one

/-- Homogeneity of degree 2: (k • X)# = k² • X#. -/
theorem freudenthalAdjoint_homogeneity {R : Type*} [CommRing R] (k : R) (X : AlbertElement R) :
    freudenthalAdjoint (k • X) = (k^2) • freudenthalAdjoint X :=
  adjointQuad_smul k X

/-- The fundamental Freudenthal cubic adjoint identity: (X#)# = N(X) • X. -/
theorem master_adjoint_involution {R : Type*} [CommRing R] (X : AlbertElement R) :
    freudenthalAdjoint (freudenthalAdjoint X) = freudenthalDet X • X :=
  adjointQuad_adjointQuad X

/-- Diagonal embedding for H₃(𝕆_s). -/
noncomputable def diagonal (α₁ α₂ α₃ : R) : AlbertElement R :=
  ⟨α₁, α₂, α₃, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

/-- Cubic norm of diagonal elements matches scalar product. -/
theorem diagonal_normCubic (α₁ α₂ α₃ : R) :
    freudenthalDet (diagonal α₁ α₂ α₃) = α₁ * α₂ * α₃ := by
  simp [freudenthalDet, normCubic, diagonal, ZornVectorMatrix.norm,
    ZornVectorMatrix.zero, ZornVectorMatrix.mul, ZornVectorMatrix.trace,
    ZornVec3.dot, ZornVec3.cross]

/-- The Freudenthal adjoint on diagonal elements strictly reproduces matrix minors. -/
theorem diagonal_adjoint_exact (α₁ α₂ α₃ : R) :
    freudenthalAdjoint (diagonal α₁ α₂ α₃) = diagonal (α₂ * α₃) (α₁ * α₃) (α₁ * α₂) := by
  apply ext_h3
  · simp [freudenthalAdjoint, adjointQuad, diagonal, ZornVectorMatrix.norm,
      ZornVectorMatrix.zero, ZornVec3.dot]
  · simp [freudenthalAdjoint, adjointQuad, diagonal, ZornVectorMatrix.norm,
      ZornVectorMatrix.zero, ZornVec3.dot]
  · simp [freudenthalAdjoint, adjointQuad, diagonal, ZornVectorMatrix.norm,
      ZornVectorMatrix.zero, ZornVec3.dot]
  · ext i <;> simp [freudenthalAdjoint, adjointQuad, diagonal, ZornVectorMatrix.sub,
      ZornVectorMatrix.zero, ZornVectorMatrix.conj, ZornVectorMatrix.mul,
      ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVec3.dot, ZornVec3.cross]
  · ext i <;> simp [freudenthalAdjoint, adjointQuad, diagonal, ZornVectorMatrix.sub,
      ZornVectorMatrix.zero, ZornVectorMatrix.conj, ZornVectorMatrix.mul,
      ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVec3.dot, ZornVec3.cross]
  · ext i <;> simp [freudenthalAdjoint, adjointQuad, diagonal, ZornVectorMatrix.sub,
      ZornVectorMatrix.zero, ZornVectorMatrix.conj, ZornVectorMatrix.mul,
      ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVec3.dot, ZornVec3.cross]

/-- Trace contraction on diagonal elements: Tr(X, X#) = 3 det₃(X). -/
theorem diagonal_traceBilin_adjoint {R : Type*} [CommRing R] (α₁ α₂ α₃ : R) :
    traceBilin (diagonal α₁ α₂ α₃) (freudenthalAdjoint (diagonal α₁ α₂ α₃)) =
      3 * freudenthalDet (diagonal α₁ α₂ α₃) := by
  rw [diagonal_normCubic, diagonal_adjoint_exact]
  simp [traceBilin, diagonal, ZornVectorMatrix.trace_zero, ZornVectorMatrix.conj_zero]
  ring

/-! ### 5. Jordan Cross Product & Trace Complement -/

/-- The Jordan cross product X × Y (polarization of the adjoint). -/
noncomputable def jordanCrossProduct (X Y : AlbertElement R) : AlbertElement R :=
  crossProduct X Y

/-- Trace complement identity: X × 1 = Tr(X) • 1 - X. -/
theorem jordanCrossProduct_one (X : AlbertElement R) :
    jordanCrossProduct X 1 = jordanTrace X • (1 : AlbertElement R) - X :=
  H3Zorn.crossProduct_one X

/-- Self-polarization of the adjoint: X × X = 2 • X#. -/
theorem jordanCrossProduct_self {R : Type*} [CommRing R] (X : AlbertElement R) :
    jordanCrossProduct X X = (2 : R) • freudenthalAdjoint X :=
  H3Zorn.crossProduct_self X

end InfoGeometry.Exceptional.AlbertAlgebra
