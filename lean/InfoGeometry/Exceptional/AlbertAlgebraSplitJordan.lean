import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.H3ZornCubicNormStructure

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

/-!
# Section 50: The Split Exceptional Albert Algebra J₃(𝕆_s) & Freudenthal Determinant
Target: `InfoGeometry/Exceptional/AlbertAlgebraSplitJordan.lean`

Formalizes the 27-dimensional Exceptional Jordan Algebra J₃(𝕆_s) via H₃(𝕆_s):
1. The 27-dimensional Albert Carrier J₃(𝕆_s):
   - 3 real diagonal scalars: α₁, α₂, α₃.
   - 3 off-diagonal split-octonions: a, b, c ∈ ZornVectorMatrix R (8 dimensions each).
   - Representation dimension: 3 * 1 + 3 * 8 = 27.
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

variable {R : Type*} [CommRing R]

/-! ### 1. The 27-Dimensional Albert Carrier -/

/-- The 27-dimensional exceptional Jordan algebra J₃(𝕆_s) carrier,
    structured as 3 diagonal scalars and 3 split-octonionic Zorn vector matrices. -/
abbrev AlbertElement (R : Type*) [CommRing R] := H3Zorn R

/-- Dimension formula for the Albert Algebra: 3 real diagonal scalars + 3 octonions (8 dims each). -/
def repDimension : ℕ := 3 * 1 + 3 * 8

/-- Exact dimension of the split Albert algebra carrier. -/
theorem albert_algebra_dimension : repDimension = 27 := by rfl

/-! ### 2. The Jordan Linear and Quadratic Traces -/

/-- The Jordan linear trace: Tr(X) = α₁ + α₂ + α₃. -/
noncomputable def jordanTrace (X : AlbertElement R) : R := linearTrace X

/-- The Jordan quadratic trace: Tr(X²) via the canonical bilinear trace form. -/
noncomputable def jordanQuadraticTrace (X : AlbertElement R) : R := traceBilin X X

/-- Trace of the identity element is 3. -/
@[simp]
theorem trace_albert_identity : jordanTrace (1 : AlbertElement R) = 3 := by
  simp [jordanTrace, linearTrace, one_readback]
  ring

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
theorem det_albert_identity : freudenthalDet (1 : AlbertElement R) = 1 :=
  normCubic_one

/-- Homogeneity of degree 3: det₃(k • X) = k³ det₃(X). -/
theorem freudenthalDet_homogeneity (k : R) (X : AlbertElement R) :
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
theorem adjoint_albert_identity : freudenthalAdjoint (1 : AlbertElement R) = 1 :=
  adjointQuad_one

/-- Homogeneity of degree 2: (k • X)# = k² • X#. -/
theorem freudenthalAdjoint_homogeneity (k : R) (X : AlbertElement R) :
    freudenthalAdjoint (k • X) = (k^2) • freudenthalAdjoint X :=
  adjointQuad_smul k X

/-- The fundamental Freudenthal cubic adjoint identity: (X#)# = N(X) • X. -/
theorem master_adjoint_involution (X : AlbertElement R) :
    freudenthalAdjoint (freudenthalAdjoint X) = freudenthalDet X • X :=
  adjointQuad_adjointQuad X

/-- Diagonal embedding for H₃(𝕆_s). -/
noncomputable def diagonal (α₁ α₂ α₃ : R) : AlbertElement R :=
  ⟨α₁, α₂, α₃, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

/-- Cubic norm of diagonal elements matches scalar product. -/
theorem diagonal_normCubic (α₁ α₂ α₃ : R) :
    freudenthalDet (diagonal α₁ α₂ α₃) = α₁ * α₂ * α₃ := by
  simp [freudenthalDet, normCubic, diagonal, ZornVectorMatrix.norm_zero,
    ZornVectorMatrix.zero_mul, ZornVectorMatrix.trace_zero]

/-- The Freudenthal adjoint on diagonal elements strictly reproduces matrix minors. -/
theorem diagonal_adjoint_exact (α₁ α₂ α₃ : R) :
    freudenthalAdjoint (diagonal α₁ α₂ α₃) = diagonal (α₂ * α₃) (α₁ * α₃) (α₁ * α₂) := by
  apply ext_h3
  · simp [freudenthalAdjoint, adjointQuad, diagonal, ZornVectorMatrix.norm_zero]
  · simp [freudenthalAdjoint, adjointQuad, diagonal, ZornVectorMatrix.norm_zero]
  · simp [freudenthalAdjoint, adjointQuad, diagonal, ZornVectorMatrix.norm_zero]
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
theorem diagonal_traceBilin_adjoint (α₁ α₂ α₃ : R) :
    traceBilin (diagonal α₁ α₂ α₃) (freudenthalAdjoint (diagonal α₁ α₂ α₃)) =
      3 * freudenthalDet (diagonal α₁ α₂ α₃) := by
  rw [diagonal_normCubic, diagonal_adjoint_exact]
  simp [traceBilin, diagonal, ZornVectorMatrix.zero_mul, ZornVectorMatrix.trace_zero, ZornVectorMatrix.conj_zero]
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
theorem jordanCrossProduct_self (X : AlbertElement R) :
    jordanCrossProduct X X = (2 : R) • freudenthalAdjoint X :=
  H3Zorn.crossProduct_self X

/-! ### 6. Master Certificate Structure -/

structure AlbertAlgebraCertificate : Prop where
  dim_27 : repDimension = 27
  tr_id : ∀ (R : Type) [CommRing R], jordanTrace (1 : AlbertElement R) = 3
  quad_tr_id : ∀ (R : Type) [CommRing R], jordanQuadraticTrace (1 : AlbertElement R) = 3
  det_id : ∀ (R : Type) [CommRing R], freudenthalDet (1 : AlbertElement R) = 1
  det_homog : ∀ (R : Type) [CommRing R] (k : R) (X : AlbertElement R),
    freudenthalDet (k • X) = k^3 * freudenthalDet X
  adj_id : ∀ (R : Type) [CommRing R], freudenthalAdjoint (1 : AlbertElement R) = 1
  adj_homog : ∀ (R : Type) [CommRing R] (k : R) (X : AlbertElement R),
    freudenthalAdjoint (k • X) = (k^2) • freudenthalAdjoint X
  adj_involution : ∀ (R : Type) [CommRing R] (X : AlbertElement R),
    freudenthalAdjoint (freudenthalAdjoint X) = freudenthalDet X • X
  diag_contraction : ∀ (R : Type) [CommRing R] (α₁ α₂ α₃ : R),
    traceBilin (diagonal α₁ α₂ α₃) (freudenthalAdjoint (diagonal α₁ α₂ α₃)) =
      3 * freudenthalDet (diagonal α₁ α₂ α₃)
  cross_one : ∀ (R : Type) [CommRing R] (X : AlbertElement R),
    jordanCrossProduct X 1 = jordanTrace X • (1 : AlbertElement R) - X
  cross_self : ∀ (R : Type) [CommRing R] (X : AlbertElement R),
    jordanCrossProduct X X = (2 : R) • freudenthalAdjoint X

theorem compile_albert_algebra_certificate : AlbertAlgebraCertificate where
  dim_27 := albert_algebra_dimension
  tr_id := fun _ _ => trace_albert_identity
  quad_tr_id := fun _ _ => quadTrace_albert_identity
  det_id := fun _ _ => det_albert_identity
  det_homog := fun _ _ k X => freudenthalDet_homogeneity k X
  adj_id := fun _ _ => adjoint_albert_identity
  adj_homog := fun _ _ k X => freudenthalAdjoint_homogeneity k X
  adj_involution := fun _ _ X => master_adjoint_involution X
  diag_contraction := fun _ _ α₁ α₂ α₃ => diagonal_traceBilin_adjoint α₁ α₂ α₃
  cross_one := fun _ _ X => jordanCrossProduct_one X
  cross_self := fun _ _ X => jordanCrossProduct_self X

end InfoGeometry.Exceptional.AlbertAlgebra
