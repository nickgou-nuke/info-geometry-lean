/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearFeshbachReduction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# A real three-configuration operator model

The three coordinates are two retained configurations and one eliminated
configuration. All matrices act through native real Euclidean continuous
linear maps. Their nuclear labels and a physical multipole assignment are
external model choices. This finite representation does not replace the
countable algebraic nuclear carrier.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfiguration

open scoped Matrix

abbrev ConfigurationSpace := EuclideanSpace ℝ (Fin 3)
abbrev ModelSpace := EuclideanSpace ℝ (Fin 2)

/-- Native continuous action of a real finite matrix on Euclidean spaces. -/
def matrixMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  A.toEuclideanLin.toContinuousLinearMap

@[simp] theorem matrixMap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    matrixMap A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

theorem matrixMap_adjoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixMap A).adjoint = matrixMap A.transpose := by
  apply ContinuousLinearMap.coe_injective
  change A.toEuclideanLin.adjoint = A.transpose.toEuclideanLin
  have htrans : A.conjTranspose = A.transpose := by
    ext i j
    simp
  simpa only [htrans] using A.toEuclideanLin_conjTranspose_eq_adjoint.symm

def hamiltonianMatrix (a c g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, 0, g; 0, a, g; g, g, c]

def hamiltonian (a c g : ℝ) : ConfigurationSpace →L[ℝ] ConfigurationSpace :=
  matrixMap (hamiltonianMatrix a c g)

def projection : ConfigurationSpace →L[ℝ] ConfigurationSpace :=
  matrixMap !![1, 0, 0; 0, 1, 0; 0, 0, 0]

def complement : ConfigurationSpace →L[ℝ] ConfigurationSpace := 1 - projection

def inclusion : ModelSpace →L[ℝ] ConfigurationSpace :=
  matrixMap !![1, 0; 0, 1; 0, 0]

def coordinates : ConfigurationSpace →L[ℝ] ModelSpace :=
  matrixMap !![1, 0, 0; 0, 1, 0]

/-- The reconstructed graph has the original model coordinates as its first
two coordinates; the denominator is interpreted only off its stated pole. -/
def graphMap (c g E : ℝ) : ModelSpace →L[ℝ] ConfigurationSpace :=
  matrixMap !![1, 0; 0, 1; g / (E - c), g / (E - c)]

@[simp] theorem hamiltonian_apply (a c g : ℝ) (x : ConfigurationSpace) :
    hamiltonian a c g x =
      WithLp.toLp 2 ![a * x 0 + g * x 2,
        a * x 1 + g * x 2, g * x 0 + g * x 1 + c * x 2] := by
  ext i
  fin_cases i <;>
    simp [hamiltonian, hamiltonianMatrix, dotProduct,
      Fin.sum_univ_succ, add_assoc]

@[simp] theorem projection_apply (x : ConfigurationSpace) :
    projection x = WithLp.toLp 2 ![x 0, x 1, 0] := by
  ext i
  fin_cases i <;> simp [projection, dotProduct, Fin.sum_univ_succ]

@[simp] theorem complement_apply (x : ConfigurationSpace) :
    complement x = WithLp.toLp 2 ![0, 0, x 2] := by
  ext i
  fin_cases i <;> simp [complement]

@[simp] theorem inclusion_apply (x : ModelSpace) :
    inclusion x = WithLp.toLp 2 ![x 0, x 1, 0] := by
  ext i
  fin_cases i <;> simp [inclusion, dotProduct, Fin.sum_univ_succ]

@[simp] theorem coordinates_apply (x : ConfigurationSpace) :
    coordinates x = WithLp.toLp 2 ![x 0, x 1] := by
  ext i
  fin_cases i <;> simp [coordinates, dotProduct, Fin.sum_univ_succ]

@[simp] theorem graphMap_apply (c g E : ℝ) (x : ModelSpace) :
    graphMap c g E x =
      WithLp.toLp 2 ![x 0, x 1, g * (x 0 + x 1) / (E - c)] := by
  ext i
  fin_cases i <;>
    simp [graphMap, dotProduct, Fin.sum_univ_succ] <;> ring

theorem projection_idempotent : projection * projection = projection := by
  ext x i
  fin_cases i <;> simp

theorem complement_idempotent : complement * complement = complement := by
  ext x i
  fin_cases i <;> simp

theorem hamiltonian_adjoint (a c g : ℝ) :
    (hamiltonian a c g).adjoint = hamiltonian a c g := by
  rw [hamiltonian, matrixMap_adjoint]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem projection_adjoint : projection.adjoint = projection := by
  rw [projection, matrixMap_adjoint]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coordinates_inclusion : coordinates.comp inclusion =
    ContinuousLinearMap.id ℝ ModelSpace := by
  ext x i
  fin_cases i <;> simp

theorem inclusion_coordinates : inclusion.comp coordinates = projection := by
  ext x i
  fin_cases i <;> simp

theorem coordinates_graphMap (c g E : ℝ) :
    coordinates.comp (graphMap c g E) = ContinuousLinearMap.id ℝ ModelSpace := by
  ext x i
  fin_cases i <;> simp

theorem projection_graphMap (c g E : ℝ) :
    projection.comp (graphMap c g E) = inclusion := by
  ext x i
  fin_cases i <;> simp

theorem graphMap_injective (c g E : ℝ) : Function.Injective (graphMap c g E) := by
  intro x y h
  have hxy := congrArg coordinates h
  have hx := congrArg (fun T : ModelSpace →L[ℝ] ModelSpace => T x)
    (coordinates_graphMap c g E)
  have hy := congrArg (fun T : ModelSpace →L[ℝ] ModelSpace => T y)
    (coordinates_graphMap c g E)
  exact hx.symm.trans (hxy.trans hy)

/-- The eliminated configuration has the scalar diagonal energy `c`, as an
identity of actual operators rather than a premise in a resolvent record. -/
theorem complement_hamiltonian_complement (a c g : ℝ) :
    complement * hamiltonian a c g * complement = c • complement := by
  ext x i
  fin_cases i <;> simp

end InfoGeometry.Physics.NuclearThreeConfiguration
