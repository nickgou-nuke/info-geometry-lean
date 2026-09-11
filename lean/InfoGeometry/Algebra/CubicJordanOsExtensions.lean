import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.CubicJordanOs

/-!
# Extensions to CubicJordanOs: Primitive Idempotents and Peirce Projections

This module extends `CubicJordanOs` with:
- Diagonal matrix units (primitive idempotents): $e_1, e_2, e_3$
- Completeness ($e_1 + e_2 + e_3 = 1$)
- Concrete Peirce Space projections ($J_{11}, J_{22}, J_{33}, J_{23}, J_{31}, J_{12}$)
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

attribute [ext] ext_albert

/-- Primitive diagonal idempotent $e_1 = \text{diag}(1, 0, 0)$. -/
def e₁ : AlbertMatrix := { α₁ := 1, α₂ := 0, α₃ := 0, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }

/-- Primitive diagonal idempotent $e_2 = \text{diag}(0, 1, 0)$. -/
def e₂ : AlbertMatrix := { α₁ := 0, α₂ := 1, α₃ := 0, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }

/-- Primitive diagonal idempotent $e_3 = \text{diag}(0, 0, 1)$. -/
def e₃ : AlbertMatrix := { α₁ := 0, α₂ := 0, α₃ := 1, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }

/-- The Identity Albert Matrix $1 = \text{diag}(1, 1, 1)$. -/
def eOne : AlbertMatrix := { α₁ := 1, α₂ := 1, α₃ := 1, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }

/-- Completeness: $e_1 + e_2 + e_3 = 1$. -/
theorem e_sum_one : e₁ + e₂ + e₃ = eOne := by
  apply albertMatrixEquiv.injective
  have h_add (X Y : AlbertMatrix) :
      albertMatrixEquiv (X + Y) = albertMatrixEquiv X + albertMatrixEquiv Y := rfl
  rw [h_add, h_add]
  have hz : (zeroZ : SplitOct) = 0 := rfl
  simp [albertMatrixEquiv, e₁, e₂, e₃, eOne, hz]

/-- Peirce diagonal projection $J_{11}$. -/
def peirceProj11 (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := X.α₁, α₂ := 0, α₃ := 0, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }

/-- Peirce diagonal projection $J_{22}$. -/
def peirceProj22 (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := 0, α₂ := X.α₂, α₃ := 0, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }

/-- Peirce diagonal projection $J_{33}$. -/
def peirceProj33 (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := 0, α₂ := 0, α₃ := X.α₃, z₁ := zeroZ, z₂ := zeroZ, z₃ := zeroZ }

/-- Peirce off-diagonal projection $J_{23}$ (Generation 1: $z_1$ slot). -/
def peirceProj23 (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := 0, α₂ := 0, α₃ := 0, z₁ := X.z₁, z₂ := zeroZ, z₃ := zeroZ }

/-- Peirce off-diagonal projection $J_{31}$ (Generation 2: $z_2$ slot). -/
def peirceProj31 (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := 0, α₂ := 0, α₃ := 0, z₁ := zeroZ, z₂ := X.z₂, z₃ := zeroZ }

/-- Peirce off-diagonal projection $J_{12}$ (Generation 3: $z_3$ slot). -/
def peirceProj12 (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := 0, α₂ := 0, α₃ := 0, z₁ := zeroZ, z₂ := zeroZ, z₃ := X.z₃ }

/-- The six coordinate components of the Peirce decomposition of `X`.

The off-diagonal labels follow the Albert-matrix convention
`J₂₃ = z₁`, `J₃₁ = z₂`, and `J₁₂ = z₃`. -/
structure PeirceDecomposition (X : AlbertMatrix) where
  diag₁ : ℝ
  diag₂ : ℝ
  diag₃ : ℝ
  off₂₃ : SplitOct
  off₃₁ : SplitOct
  off₁₂ : SplitOct

def peirceDecomposition (X : AlbertMatrix) : PeirceDecomposition X :=
  { diag₁ := X.α₁
    diag₂ := X.α₂
    diag₃ := X.α₃
    off₂₃ := X.z₁
    off₃₁ := X.z₂
    off₁₂ := X.z₃ }

@[simp] theorem peirceDecomposition_diag₁ (X : AlbertMatrix) :
    (peirceDecomposition X).diag₁ = X.α₁ := rfl

@[simp] theorem peirceDecomposition_diag₂ (X : AlbertMatrix) :
    (peirceDecomposition X).diag₂ = X.α₂ := rfl

@[simp] theorem peirceDecomposition_diag₃ (X : AlbertMatrix) :
    (peirceDecomposition X).diag₃ = X.α₃ := rfl

@[simp] theorem peirceDecomposition_off₂₃ (X : AlbertMatrix) :
    (peirceDecomposition X).off₂₃ = X.z₁ := rfl

@[simp] theorem peirceDecomposition_off₃₁ (X : AlbertMatrix) :
    (peirceDecomposition X).off₃₁ = X.z₂ := rfl

@[simp] theorem peirceDecomposition_off₁₂ (X : AlbertMatrix) :
    (peirceDecomposition X).off₁₂ = X.z₃ := rfl

theorem peirce_diag_proj (X : AlbertMatrix) :
    (peirceDecomposition X).diag₁ = traceBilin X e₁ ∧
    (peirceDecomposition X).diag₂ = traceBilin X e₂ ∧
    (peirceDecomposition X).diag₃ = traceBilin X e₃ := by
  dsimp [peirceDecomposition, traceBilin, e₁, e₂, e₃, octTrace, zeroZ]
  constructor
  · ring
  constructor
  · ring
  · ring

theorem peirce_off_proj (X : AlbertMatrix) :
    (peirceDecomposition X).off₁₂ = X.z₃ ∧
    (peirceDecomposition X).off₂₃ = X.z₁ ∧
    (peirceDecomposition X).off₃₁ = X.z₂ := by
  exact ⟨rfl, rfl, rfl⟩

@[simp] theorem peirceProj11_α₁ (X : AlbertMatrix) :
    (peirceProj11 X).α₁ = X.α₁ := rfl

@[simp] theorem peirceProj22_α₂ (X : AlbertMatrix) :
    (peirceProj22 X).α₂ = X.α₂ := rfl

@[simp] theorem peirceProj33_α₃ (X : AlbertMatrix) :
    (peirceProj33 X).α₃ = X.α₃ := rfl

@[simp] theorem peirceProj23_z₁ (X : AlbertMatrix) :
    (peirceProj23 X).z₁ = X.z₁ := rfl

@[simp] theorem peirceProj31_z₂ (X : AlbertMatrix) :
    (peirceProj31 X).z₂ = X.z₂ := rfl

@[simp] theorem peirceProj12_z₃ (X : AlbertMatrix) :
    (peirceProj12 X).z₃ = X.z₃ := rfl

theorem peirceProj23_other_slots_zero (X : AlbertMatrix) :
    (peirceProj23 X).z₂ = zeroZ ∧ (peirceProj23 X).z₃ = zeroZ := by
  constructor <;> rfl

theorem peirceProj31_other_slots_zero (X : AlbertMatrix) :
    (peirceProj31 X).z₁ = zeroZ ∧ (peirceProj31 X).z₃ = zeroZ := by
  constructor <;> rfl

theorem peirceProj12_other_slots_zero (X : AlbertMatrix) :
    (peirceProj12 X).z₁ = zeroZ ∧ (peirceProj12 X).z₂ = zeroZ := by
  constructor <;> rfl

/-- Concrete 27D Peirce Decomposition: $X = J_{11}(X) + J_{22}(X) + J_{33}(X) + J_{23}(X) + J_{31}(X) + J_{12}(X)$. -/
theorem peirce_full_decomposition (X : AlbertMatrix) :
    X = peirceProj11 X + peirceProj22 X + peirceProj33 X +
        peirceProj23 X + peirceProj31 X + peirceProj12 X := by
  apply albertMatrixEquiv.injective
  have h_add (X Y : AlbertMatrix) :
      albertMatrixEquiv (X + Y) = albertMatrixEquiv X + albertMatrixEquiv Y := rfl
  rw [h_add, h_add, h_add, h_add, h_add]
  have hz : (zeroZ : SplitOct) = 0 := rfl
  simp [albertMatrixEquiv, peirceProj11, peirceProj22, peirceProj33,
    peirceProj23, peirceProj31, peirceProj12, hz]

end InfoGeometry.Algebra.CubicJordanOs
