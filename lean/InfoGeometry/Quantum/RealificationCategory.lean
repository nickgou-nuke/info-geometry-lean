/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.RealificationStates
import InfoGeometry.Quantum.RealKCategory
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The realification matrices in the existing internal-complex category

This file connects the arbitrary finite matrix realification with the existing
`RealKVect` category. The internal operator is exactly the real block matrix
`internalJ`, and every rectangular realified matrix is a morphism intertwining
the two internal operators. The coordinate isomorphism is constructed from
`realifyVector` and `unrealifyVector`; its naturality identifies the matrix
construction with the existing `complexToRealK` functor.
-/

noncomputable section

open CategoryTheory Matrix
open InfoGeometry.Quantum.RealKCategory

universe u

namespace InfoGeometry.Quantum.Realification

variable {l m n : Type u}

/-- The doubled real coordinate space with its actual matrix complex structure. -/
def doubledRealK (n : Type u) [Fintype n] [DecidableEq n] : RealKVect.{u} where
  V := n ⊕ n → ℝ
  K := (internalJ (n := n)).mulVecLin
  K_sq := by
    apply LinearMap.ext
    intro x
    change internalJ *ᵥ (internalJ *ᵥ x) = -x
    simp [Matrix.mulVec_mulVec, internalJ_sq, Matrix.neg_mulVec]

/-- Rectangular matrices intertwine the internal axes at source and target. -/
theorem realify_intertwines_internalJ [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    realify A * internalJ (n := n) = internalJ (n := m) * realify A := by
  simp [realify, internalJ, Matrix.fromBlocks_multiply]

/-- A complex matrix represented as an actual morphism in `RealKVect`. -/
def realifiedHom [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) : doubledRealK n ⟶ doubledRealK m where
  hom := (realify A).mulVecLin
  comm := by
    change (realify A).mulVecLin.comp (internalJ (n := n)).mulVecLin =
      (internalJ (n := m)).mulVecLin.comp (realify A).mulVecLin
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul,
      realify_intertwines_internalJ]

@[simp] theorem realifiedHom_apply [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (x : n ⊕ n → ℝ) :
    (realifiedHom A).hom x = realify A *ᵥ x := rfl

@[simp] theorem realifiedHom_one [Fintype n] [DecidableEq n] :
    realifiedHom (1 : Matrix n n ℂ) = 𝟙 (doubledRealK n) := by
  apply RealKVect.Hom.ext
  change (realify (1 : Matrix n n ℂ)).mulVecLin = LinearMap.id
  simp

/-- Categorical composition has exactly the order of the matrix action. -/
theorem realifiedHom_mul [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix l m ℂ) :
    realifiedHom (B * A) = realifiedHom A ≫ realifiedHom B := by
  apply RealKVect.Hom.ext
  change (realify (B * A)).mulVecLin =
    (realify B).mulVecLin.comp (realify A).mulVecLin
  rw [realify_mul, Matrix.mulVecLin_mul]

/-- The categorical matrix morphism acts on the encoded vector as intended. -/
theorem realifiedHom_realifyVector [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (z : n → ℂ) :
    (realifiedHom A).hom (realifyVector z) = realifyVector (A *ᵥ z) :=
  realify_mulVec A z

/-- Encoding vectors is real linear on the original complex coordinates. -/
def realifyVectorLinear : (n → ℂ) →ₗ[ℝ] (n ⊕ n → ℝ) where
  toFun := realifyVector
  map_add' := by
    intro z w
    funext i
    cases i <;> simp [realifyVector]
  map_smul' := by
    intro r z
    funext i
    cases i <;> simp [realifyVector]

/-- The inverse coordinate map is also real linear. -/
def unrealifyVectorLinear : (n ⊕ n → ℝ) →ₗ[ℝ] (n → ℂ) where
  toFun := unrealifyVector
  map_add' := by
    intro x y
    ext i
    apply Complex.ext <;> simp [unrealifyVector]
  map_smul' := by
    intro r x
    ext i
    apply Complex.ext <;> simp [unrealifyVector]

/-- The concrete internal axis encodes multiplication by the imaginary unit. -/
theorem internalJ_realifyVector [Fintype n] [DecidableEq n] (z : n → ℂ) :
    internalJ *ᵥ realifyVector z = realifyVector (Complex.I • z) := by
  rw [internalJ_eq_realify, realify_mulVec]
  simp [Matrix.smul_mulVec]

theorem unrealifyVector_internalJ [Fintype n] [DecidableEq n]
    (x : n ⊕ n → ℝ) :
    unrealifyVector (internalJ *ᵥ x) = Complex.I • unrealifyVector x := by
  have h := congrArg unrealifyVector (internalJ_realifyVector (unrealifyVector x))
  simpa only [realifyVector_unrealifyVector, unrealifyVector_realifyVector] using h

/-- The coordinate realization is isomorphic to the existing categorical one. -/
def coordinateIso (n : Type u) [Fintype n] [DecidableEq n] :
    RealKVect.complexToRealK.obj (ModuleCat.of ℂ (n → ℂ)) ≅ doubledRealK n where
  hom :=
    { hom := realifyVectorLinear
      comm := by
        apply LinearMap.ext
        intro z
        exact (internalJ_realifyVector (n := n) z).symm }
  inv :=
    { hom := unrealifyVectorLinear
      comm := by
        apply LinearMap.ext
        intro x
        change unrealifyVector (internalJ *ᵥ x) = Complex.I • unrealifyVector x
        exact unrealifyVector_internalJ x }
  hom_inv_id := by
    apply RealKVect.Hom.ext
    apply LinearMap.ext
    intro z
    exact unrealifyVector_realifyVector z
  inv_hom_id := by
    apply RealKVect.Hom.ext
    apply LinearMap.ext
    intro x
    exact realifyVector_unrealifyVector x

/-- The coordinate isomorphisms intertwine the existing functor with `Γ`. -/
theorem coordinateIso_naturality [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) :
    RealKVect.complexToRealK.map (ModuleCat.ofHom A.mulVecLin) ≫
        (coordinateIso m).hom =
      (coordinateIso n).hom ≫ realifiedHom A := by
  apply RealKVect.Hom.ext
  apply LinearMap.ext
  intro z
  change realifyVector (A *ᵥ z) = realify A *ᵥ realifyVector z
  exact (realify_mulVec A z).symm

end InfoGeometry.Quantum.Realification
