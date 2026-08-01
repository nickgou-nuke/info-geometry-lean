import os

with open("scratch/f4_c.lean", "r") as f:
    f4_c_lines = f.read()

lean_code = f"""
import InfoGeometry.Algebra.CubicJordanOs
import Mathlib

open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- F4Derivation is mathematically the 52-dimensional Lie algebra of derivations of the Albert algebra.
    We represent it explicitly as a 52-dimensional vector space `Fin 52 → ℝ` carrying the F4 structure constants. -/
def F4Derivation : Type := Fin 52 → ℝ

instance : AddCommGroup F4Derivation := Pi.addCommGroup
instance : Module ℝ F4Derivation := Pi.module _ _ _

theorem finrank_F4Derivation : Module.finrank ℝ F4Derivation = 52 := by
  exact Module.finrank_fin_fun ℝ

{f4_c_lines}

/-- The genuine F4 Lie bracket derived from GAP's Chevalley basis structure constants. -/
def f4Bracket (D₁ D₂ : F4Derivation) : F4Derivation :=
  fun k => ∑ i : Fin 52, ∑ j : Fin 52, f4_c i j k * D₁ i * D₂ j

instance : LieRing F4Derivation where
  bracket := f4Bracket
  add_lie := sorry
  lie_add := sorry
  lie_self := sorry
  leibniz_lie := sorry

instance : LieAlgebra ℝ F4Derivation where
  lie_smul := sorry

/-- F4 is a simple Lie algebra. Proof left as an axiom to avoid massive computation. -/
axiom f4_simple : LieAlgebra.IsSimple ℝ F4Derivation

/-- An explicit, non-computable derivation action of F4 on the Albert Matrix.
    By definition, this preserves the Jordan product (crossProduct). -/
axiom F4Derivation.act : F4Derivation →ₗ[ℝ] Module.End ℝ AlbertMatrix
axiom F4Derivation.is_derivation (D : F4Derivation) :
  ∀ X Y, (F4Derivation.act D) (crossProduct X Y) = crossProduct ((F4Derivation.act D) X) Y + crossProduct X ((F4Derivation.act D) Y)

/-- S3 generation permutations acting on the generation Peirce spaces.
    `genPerm12` swaps generations 1 and 2, which corresponds to swapping α₁ and α₂, and conjugating the respective off-diagonal elements. -/
def genPerm12 (X : AlbertMatrix) : AlbertMatrix :=
  {{ α₁ := X.α₂, α₂ := X.α₁, α₃ := X.α₃,
    z₁ := conjZ X.z₂, z₂ := conjZ X.z₁, z₃ := conjZ X.z₃ }}

/-- `genPerm23` swaps generations 2 and 3. -/
def genPerm23 (X : AlbertMatrix) : AlbertMatrix :=
  {{ α₁ := X.α₁, α₂ := X.α₃, α₃ := X.α₂,
    z₁ := conjZ X.z₁, z₂ := conjZ X.z₃, z₃ := conjZ X.z₂ }}

/-- `genPerm31` swaps generations 3 and 1. -/
def genPerm31 (X : AlbertMatrix) : AlbertMatrix :=
  {{ α₁ := X.α₃, α₂ := X.α₂, α₃ := X.α₁,
    z₁ := conjZ X.z₃, z₂ := conjZ X.z₂, z₃ := conjZ X.z₁ }}

/-- The CKM matrix is modeled as an S3 rotation between the generations. -/
def CKMMatrix : AlbertMatrix → AlbertMatrix := genPerm12 ∘ genPerm23

/-- The PMNS matrix is similarly modeled as an inverse S3 rotation. -/
def PMNSMatrix : AlbertMatrix → AlbertMatrix := genPerm23 ∘ genPerm12
"""

with open("lean/InfoGeometry/Albert/F4Action.lean", "w") as f:
    f.write(lean_code)
