/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55InternalComplex
import InfoGeometry.Quantum.RealificationCategory

/-!
# The matrix internal phase and the native Clifford right phase

The real coordinate plane is explicitly isomorphic to the existing
`Realification.doubledRealK (Fin 1)`, whose axis is the actual matrix
`internalJ`. Composing its inverse with the proved even-Clifford phase-plane
morphism gives one connected representation chain. The matrix action
`a • 1 + b • internalJ` is carried to right multiplication by `a • 1 + b • B`;
the trigonometric specialization carries matrix phase rotations to native
right phase action. The geometric plane interpretation applies to the
constructed orthogonal-plane bivector, including the `Cl(5,5)` specialization.

This identifies the selected phase plane and its action. It is not a claim
that the entire even Clifford algebra is two-dimensional or that every
Clifford observable has a two-by-two matrix representation.
-/

noncomputable section

namespace InfoGeometry.Quantum.CliffordPhaseRealification

open CategoryTheory Matrix
open InfoGeometry.Quantum.RealKCategory
open InfoGeometry.Quantum.Realification
open InfoGeometry.Clifford.EvenInternalComplex

/-- Real coordinates in the existing doubled one-dimensional matrix carrier. -/
def coordinatesToMatrix : (ℝ × ℝ) →ₗ[ℝ] (Fin 1 ⊕ Fin 1 → ℝ) where
  toFun p := Sum.elim (fun _ => p.1) (fun _ => p.2)
  map_add' p q := by
    funext i
    rcases i with i | i <;> rfl
  map_smul' r p := by
    funext i
    rcases i with i | i <;> rfl

/-- Coordinate readback from the two real matrix components. -/
def matrixToCoordinates : (Fin 1 ⊕ Fin 1 → ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (x (Sum.inl 0), x (Sum.inr 0))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem matrixToCoordinates_coordinatesToMatrix (p : ℝ × ℝ) :
    matrixToCoordinates (coordinatesToMatrix p) = p := by cases p; rfl

@[simp] theorem coordinatesToMatrix_matrixToCoordinates
    (x : Fin 1 ⊕ Fin 1 → ℝ) :
    coordinatesToMatrix (matrixToCoordinates x) = x := by
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl

/-- The canonical matrix `internalJ` is the coordinate quarter-turn. -/
theorem coordinatesToMatrix_intertwines (p : ℝ × ℝ) :
    coordinatesToMatrix (coordinateJ p) =
      internalJ (n := Fin 1) *ᵥ coordinatesToMatrix p := by
  rw [internalJ, Matrix.fromBlocks_mulVec]
  ext i
  rcases i with i | i <;>
    simp [coordinatesToMatrix, coordinateJ, Matrix.neg_mulVec]

theorem matrixToCoordinates_intertwines (x : Fin 1 ⊕ Fin 1 → ℝ) :
    matrixToCoordinates (internalJ (n := Fin 1) *ᵥ x) =
      coordinateJ (matrixToCoordinates x) := by
  have h := congrArg matrixToCoordinates
    (coordinatesToMatrix_intertwines (matrixToCoordinates x))
  simpa only [matrixToCoordinates_coordinatesToMatrix,
    coordinatesToMatrix_matrixToCoordinates] using h.symm

/-- Explicit coordinate isomorphism in the existing `RealKVect` category. -/
def coordinateMatrixIso : coordinatePlane ≅ doubledRealK (Fin 1) where
  hom :=
    { hom := coordinatesToMatrix
      comm := by
        apply LinearMap.ext
        intro p
        exact coordinatesToMatrix_intertwines p }
  inv :=
    { hom := matrixToCoordinates
      comm := by
        apply LinearMap.ext
        intro x
        exact matrixToCoordinates_intertwines x }
  hom_inv_id := by
    apply RealKVect.Hom.ext
    apply LinearMap.ext
    intro p
    exact matrixToCoordinates_coordinatesToMatrix p
  inv_hom_id := by
    apply RealKVect.Hom.ext
    apply LinearMap.ext
    intro x
    exact coordinatesToMatrix_matrixToCoordinates x

variable {M : Type} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

local notation "EvenQ" => CliffordAlgebra.even Q

/-- Compose the actual matrix coordinate isomorphism with the native phase map. -/
def matrixPhaseHom (B : EvenQ) (hB : B * B = -(1 : EvenQ)) :
    doubledRealK (Fin 1) ⟶ rightRealK Q B hB :=
  coordinateMatrixIso.inv ≫ phasePlaneHom Q B hB

@[simp] theorem matrixPhaseHom_apply
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (x : Fin 1 ⊕ Fin 1 → ℝ) :
    (matrixPhaseHom Q B hB).hom x =
      x (Sum.inl 0) • (1 : EvenQ) + x (Sum.inr 0) • B := rfl

/-- Matrix multiplication by `internalJ` becomes native right bivector action. -/
theorem matrixPhaseHom_internalJ
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (x : Fin 1 ⊕ Fin 1 → ℝ) :
    (matrixPhaseHom Q B hB).hom (internalJ (n := Fin 1) *ᵥ x) =
      ((matrixPhaseHom Q B hB).hom x : EvenQ) * B :=
  congrArg (fun T : (Fin 1 ⊕ Fin 1 → ℝ) →ₗ[ℝ] EvenQ => T x)
    (matrixPhaseHom Q B hB).comm

/-- The whole real scalar phase plane has the same action in both representations. -/
theorem matrix_internal_scalar_action
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (a b : ℝ)
    (x : Fin 1 ⊕ Fin 1 → ℝ) :
    (matrixPhaseHom Q B hB).hom
        ((a • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) +
          b • internalJ (n := Fin 1)) *ᵥ x) =
      ((matrixPhaseHom Q B hB).hom x : EvenQ) * phasePlaneMap Q B (a, b) := by
  have hJ : phasePlaneMap Q B (matrixToCoordinates (internalJ (n := Fin 1) *ᵥ x)) =
      phasePlaneMap Q B (matrixToCoordinates x) * B :=
    matrixPhaseHom_internalJ Q B hB x
  change phasePlaneMap Q B
      (matrixToCoordinates ((a • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) +
        b • internalJ (n := Fin 1)) *ᵥ x)) =
    phasePlaneMap Q B (matrixToCoordinates x) * phasePlaneMap Q B (a, b)
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  simp only [map_add, map_smul]
  rw [hJ]
  rw [phasePlaneMap_apply Q B (a, b), mul_add, mul_smul_comm, mul_smul_comm, mul_one]

/-- Matrix phase rotation is carried to right multiplication by the internal phase
element. For a general even `B` this asserts no spin-group membership. -/
theorem matrix_internal_rotor_action
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (θ : ℝ)
    (x : Fin 1 ⊕ Fin 1 → ℝ) :
    (matrixPhaseHom Q B hB).hom
        ((Real.cos θ • (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) +
          Real.sin θ • internalJ (n := Fin 1)) *ᵥ x) =
      ((matrixPhaseHom Q B hB).hom x : EvenQ) * rotorElement Q B θ :=
  matrix_internal_scalar_action Q B hB (Real.cos θ) (Real.sin θ) x

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55InternalComplex

/-- The connected matrix-to-native-Clifford phase representation at `Cl(5,5)`. -/
def matrixPhaseHom55 : doubledRealK (Fin 1) ⟶ nativeRealK55 :=
  matrixPhaseHom Q55 phaseBivector55 phaseBivector55_sq

theorem matrixPhaseHom55_internalJ (x : Fin 1 ⊕ Fin 1 → ℝ) :
    matrixPhaseHom55.hom (internalJ (n := Fin 1) *ᵥ x) =
      (matrixPhaseHom55.hom x : CliffordAlgebra.even Q55) * phaseBivector55 :=
  matrixPhaseHom_internalJ Q55 phaseBivector55 phaseBivector55_sq x

end InfoGeometry.Quantum.CliffordPhaseRealification
