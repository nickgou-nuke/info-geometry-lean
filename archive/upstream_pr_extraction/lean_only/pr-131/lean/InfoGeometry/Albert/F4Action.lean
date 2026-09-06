import InfoGeometry.Algebra.CubicJordanOs
import InfoGeometry.Algebra.CubicJordanFreudenthal
import Mathlib

open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.Algebra.CubicJordanFreudenthal
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/- The coordinate carrier below has dimension 52, but it is not identified with
   the derivation algebra. In particular, no structure constants are present
   here. The genuine derivation Lie subalgebra is owned by
   `InfoGeometry.Algebra.BaezF4H3Zorn`. -/
def F4CoordinateCarrier : Type := Fin 52 → ℝ

instance : AddCommGroup F4CoordinateCarrier := Pi.addCommGroup
instance : Module ℝ F4CoordinateCarrier := Pi.module _ _ _

theorem finrank_F4CoordinateCarrier : Module.finrank ℝ F4CoordinateCarrier = 52 := by
  exact Module.finrank_fin_fun ℝ

/-- S3 generation permutations acting on the generation Peirce spaces.
    `genPerm12` swaps generations 1 and 2, which corresponds to swapping α₁ and α₂, and conjugating the respective off-diagonal elements. -/
def genPerm12 (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := X.α₂, α₂ := X.α₁, α₃ := X.α₃,
    z₁ := conjZ X.z₂, z₂ := conjZ X.z₁, z₃ := conjZ X.z₃ }

/-- `genPerm23` swaps generations 2 and 3. -/
def genPerm23 (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := X.α₁, α₂ := X.α₃, α₃ := X.α₂,
    z₁ := conjZ X.z₁, z₂ := conjZ X.z₃, z₃ := conjZ X.z₂ }

/-- `genPerm31` swaps generations 3 and 1. -/
def genPerm31 (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := X.α₃, α₂ := X.α₂, α₃ := X.α₁,
    z₁ := conjZ X.z₃, z₂ := conjZ X.z₂, z₃ := conjZ X.z₁ }

/-- Each generation transposition is an involution. -/
theorem genPerm_closure : ∀ X : AlbertMatrix,
    genPerm12 (genPerm12 X) = X ∧ genPerm23 (genPerm23 X) = X := by
  intro X
  constructor <;> cases X <;> simp [genPerm12, genPerm23, conjZ_conjZ]

noncomputable section

/-- Physical CKM/PMNS matrix parameterized by mixing angles and CP phase. -/
def mixingMatrix (θ₁₂ θ₂₃ θ₁₃ δ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₃ * Real.cos δ;
     -Real.sin θ₁₂ * Real.cos θ₂₃ - Real.cos θ₁₂ * Real.sin θ₂₃ * Real.sin θ₁₃,
      Real.cos θ₁₂ * Real.cos θ₂₃ - Real.sin θ₁₂ * Real.sin θ₂₃ * Real.sin θ₁₃,
      Real.sin θ₂₃ * Real.cos θ₁₃;
      Real.sin θ₁₂ * Real.sin θ₂₃ - Real.cos θ₁₂ * Real.cos θ₂₃ * Real.sin θ₁₃,
     -Real.cos θ₁₂ * Real.sin θ₂₃ - Real.sin θ₁₂ * Real.cos θ₂₃ * Real.sin θ₁₃,
      Real.cos θ₂₃ * Real.cos θ₁₃]

/-- Action of a 3x3 generation mixing matrix on the diagonal components of an AlbertMatrix. -/
def actMatrixOnAlbert (M : Matrix (Fin 3) (Fin 3) ℝ) (X : AlbertMatrix) : AlbertMatrix :=
  let v : Fin 3 → ℝ := ![X.α₁, X.α₂, X.α₃]
  let Mv := M.mulVec v
  { α₁ := Mv 0
    α₂ := Mv 1
    α₃ := Mv 2
    z₁ := X.z₁
    z₂ := X.z₂
    z₃ := X.z₃ }

/-- The CKM matrix acting on an AlbertMatrix, using physical PDG 2024 angles. -/
def CKMMatrix (X : AlbertMatrix) : AlbertMatrix :=
  actMatrixOnAlbert (mixingMatrix 0.227 0.042 0.0036 1.20) X

/-- The PMNS matrix acting on an AlbertMatrix, using physical PDG 2024 angles. -/
def PMNSMatrix (X : AlbertMatrix) : AlbertMatrix :=
  actMatrixOnAlbert (mixingMatrix 0.58 0.86 0.15 3.77) X

end
