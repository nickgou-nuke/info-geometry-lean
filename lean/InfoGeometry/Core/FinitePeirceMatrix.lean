import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.External.Auto.FiniteProjectorSpectralCalculus
import Mathlib.Data.Matrix.Basic

/-! Finite constrained Peirce arrays for an associative algebra. -/

noncomputable section
namespace InfoGeometry.Core.FinitePeirceMatrix

open scoped BigOperators
open FiniteProjectorSpectralCalculus

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
variable [Fintype I] [DecidableEq I]

def blocks (e : I → A) (x : A) : Matrix I I A := fun i j => e i * x * e j

def assemble (B : Matrix I I A) : A := ∑ i, ∑ j, B i j

theorem assemble_blocks (e : I → A)
    (he : CompleteIdempotents e) (x : A) :
    assemble (blocks e x) = x := by
  simp only [assemble, blocks, ← Finset.mul_sum, ← Finset.sum_mul,
    he, one_mul, mul_one]

def cornerSpace (e : I → A) : Submodule K (Matrix I I A) where
  carrier := {B | ∀ i j, e i * B i j * e j = B i j}
  zero_mem' := by simp
  add_mem' hB hC := by
    intro i j
    simp only [Matrix.add_apply, mul_add, add_mul, hB i j, hC i j]
  smul_mem' r B hB := by
    intro i j
    simpa only [Matrix.smul_apply, mul_smul_comm, smul_mul_assoc] using
      congrArg (r • ·) (hB i j)

theorem blocks_mem (e : I → A) (he : OrthogonalIdempotents e) (x : A) :
    blocks e x ∈ cornerSpace (K := K) e := by
  intro i j
  change e i * (e i * x * e j) * e j = e i * x * e j
  calc
    _ = (e i * e i) * x * (e j * e j) := by simp only [mul_assoc]
    _ = e i * x * e j := by rw [orthogonal_idempotent_sq he i,
      orthogonal_idempotent_sq he j]

theorem blocks_injective (e : I → A)
    (he : CompleteIdempotents e) :
    Function.Injective (blocks e) := by
  intro x y h
  have hs := congrArg assemble h
  simpa only [assemble_blocks e he] using hs

end InfoGeometry.Core.FinitePeirceMatrix
