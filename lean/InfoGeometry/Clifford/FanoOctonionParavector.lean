import InfoGeometry.Clifford.OctonionParavectorBridge
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Fano-plane Clifford paravector octonion chart

This file instantiates the `OctonionParavectorData` interface on `Fin 7 → ℝ`
using the Fano plane cross product.

All proofs are native and closed without sorry.
-/

noncomputable section
namespace InfoGeometry.Clifford.FanoOctonionParavector

open OctonionParavectorBridge

/-- Coordinate model for the imaginary part of the real octonions. -/
abbrev R7 := Fin 7 → ℝ

/-- Standard coordinate basis vector. -/
def basisVector (i : Fin 7) : R7 :=
  Pi.single i 1

/-- Paravector carrier for real octonions in the Fano chart. -/
abbrev OctonionCarrier := Paravector R7

/-- The first Fano basis vector. -/
def e0 : R7 := fun i => if i.val = 0 then 1 else 0

/-- The second Fano basis vector. -/
def e1 : R7 := fun i => if i.val = 1 then 1 else 0

/-- The third Fano basis vector. -/
def e2 : R7 := fun i => if i.val = 2 then 1 else 0

/-- Euclidean coordinate dot product on `Fin 7 → ℝ`. -/
def dot7 : LinearMap.BilinForm ℝ R7 :=
  LinearMap.mk₂ ℝ (fun u v : R7 => ∑ i, u i * v i)
    (by intro x y z; simp [Finset.sum_add_distrib, add_mul])
    (by intro a x y; simp [Finset.mul_sum, mul_assoc])
    (by intro x y z; simp [Finset.sum_add_distrib, mul_add])
    (by intro a x y; simp [Finset.mul_sum, mul_assoc, mul_left_comm])

/-- Symmetry of the coordinate dot product. -/
theorem dot7_symm (u v : R7) :
    dot7 u v = dot7 v u := by
  simp [dot7, mul_comm]

/-- The raw coordinate Fano-plane cross product on `Fin 7 → ℝ`.

The coordinates correspond to the oriented lines listed in the module docstring. -/
def fanoCrossRaw (u v : R7) : R7 := ![
  (u 1 * v 2 - u 2 * v 1) + (u 3 * v 4 - u 4 * v 3) + (u 5 * v 6 - u 6 * v 5),
  (u 2 * v 0 - u 0 * v 2) + (u 3 * v 5 - u 5 * v 3) + (u 4 * v 6 - u 6 * v 4),
  (u 0 * v 1 - u 1 * v 0) + (u 3 * v 6 - u 6 * v 3) + (u 4 * v 5 - u 5 * v 4),
  (u 4 * v 0 - u 0 * v 4) + (u 5 * v 1 - u 1 * v 5) + (u 6 * v 2 - u 2 * v 6),
  (u 0 * v 3 - u 3 * v 0) + (u 6 * v 1 - u 1 * v 6) + (u 5 * v 2 - u 2 * v 5),
  (u 6 * v 0 - u 0 * v 6) + (u 1 * v 3 - u 3 * v 1) + (u 2 * v 4 - u 4 * v 2),
  (u 0 * v 5 - u 5 * v 0) + (u 1 * v 4 - u 4 * v 1) + (u 2 * v 3 - u 3 * v 2)
]

theorem fanoCrossRaw_add_left (u w v : R7) :
    fanoCrossRaw (u + w) v = fanoCrossRaw u v + fanoCrossRaw w v := by
  ext k <;> fin_cases k <;> simp [fanoCrossRaw] <;> ring

theorem fanoCrossRaw_smul_left (a : ℝ) (u v : R7) :
    fanoCrossRaw (a • u) v = a • fanoCrossRaw u v := by
  ext k <;> fin_cases k <;> simp [fanoCrossRaw] <;> ring

theorem fanoCrossRaw_add_right (u v w : R7) :
    fanoCrossRaw u (v + w) = fanoCrossRaw u v + fanoCrossRaw u w := by
  ext k <;> fin_cases k <;> simp [fanoCrossRaw] <;> ring

theorem fanoCrossRaw_smul_right (a : ℝ) (u v : R7) :
    fanoCrossRaw u (a • v) = a • fanoCrossRaw u v := by
  ext k <;> fin_cases k <;> simp [fanoCrossRaw] <;> ring

/-- The Fano-plane cross product bundled as a bilinear map. -/
def fanoCross : R7 →ₗ[ℝ] R7 →ₗ[ℝ] R7 :=
  LinearMap.mk₂ ℝ fanoCrossRaw
    fanoCrossRaw_add_left
    fanoCrossRaw_smul_left
    fanoCrossRaw_add_right
    fanoCrossRaw_smul_right

/-- The Fano cross product of a vector with itself vanishes. -/
theorem fanoCross_self (u : R7) :
    fanoCross u u = 0 := by
  ext k <;> fin_cases k <;> simp [fanoCross, fanoCrossRaw] <;> ring

/-- The Fano cross product is antisymmetric. -/
theorem fanoCross_anticomm (u v : R7) :
    fanoCross v u = - fanoCross u v := by
  ext k <;> fin_cases k <;> simp [fanoCross, fanoCrossRaw] <;> ring

/-- Concrete theorem-checked paravector data for the Fano-plane octonion chart. -/
def fanoOctonionParavectorData : OctonionParavectorData R7 where
  inner := dot7
  cross := fanoCross
  inner_symm := dot7_symm
  cross_self := fanoCross_self
  cross_anticomm := fanoCross_anticomm

/-- The Fano convention sends `e₀ × e₁` to `e₂`. -/
theorem fanoCross_basis_0_1 :
    fanoCross (basisVector 0) (basisVector 1) = basisVector 2 := by
  ext k <;> fin_cases k <;> simp [fanoCross, fanoCrossRaw, basisVector]

/-- The Fano convention sends `e₁ × e₀` to `-e₂`. -/
theorem fanoCross_basis_1_0 :
    fanoCross (basisVector 1) (basisVector 0) = -basisVector 2 := by
  rw [fanoCross_anticomm, fanoCross_basis_0_1]

/-- Representative pure-imaginary octonion product in the concrete Fano chart:
`(0,e₀)(0,e₁) = (0,e₂)`. -/
theorem imaginary_e0_mul_e1 :
    paravectorMul fanoOctonionParavectorData (imaginary e0) (imaginary e1) =
      imaginary e2 := by
  apply Prod.ext
  · norm_num [paravectorMul, imaginary, fanoOctonionParavectorData, dot7,
      fanoCross, fanoCrossRaw, e0, e1, e2, Fin.sum_univ_seven]
  · ext k
    fin_cases k <;>
      norm_num [paravectorMul, imaginary, fanoOctonionParavectorData, dot7,
        fanoCross, fanoCrossRaw, e0, e1, e2]

/-- Representative pure-imaginary square in the concrete Fano chart:
`(0,e₀)^2 = -1`. -/
theorem imaginary_e0_sq :
    paravectorMul fanoOctonionParavectorData (imaginary e0) (imaginary e0) =
      scalar (-1 : ℝ) := by
  rw [imaginary_sq]
  apply Prod.ext
  · norm_num [scalar, fanoOctonionParavectorData, dot7, e0, Fin.sum_univ_seven]
  · ext k
    fin_cases k <;>
      norm_num [scalar, fanoOctonionParavectorData, dot7, e0]

/-- Consolidated theorem-safe packet for the concrete Fano-plane paravector
instance. -/
theorem fano_octonion_paravector_synthesis :
    (∀ u : R7, fanoCross u u = 0) ∧
      (∀ u v : R7, fanoCross v u = -fanoCross u v) ∧
      fanoCross (basisVector 0) (basisVector 1) = basisVector 2 ∧
      paravectorMul fanoOctonionParavectorData (imaginary e0) (imaginary e1) =
        imaginary e2 ∧
      paravectorMul fanoOctonionParavectorData (imaginary e0) (imaginary e0) =
        scalar (-1 : ℝ) := by
  exact ⟨fanoCross_self,
    fanoCross_anticomm,
    fanoCross_basis_0_1,
    imaginary_e0_mul_e1,
    imaginary_e0_sq⟩

end InfoGeometry.Clifford.FanoOctonionParavector
