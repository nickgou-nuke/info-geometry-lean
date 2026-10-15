import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-!
# Square-zero law for a decomposable bivector

This is a statement about the exterior algebra only. It does not identify the
exterior product with split-octonion multiplication, a Clifford product, a
Klein quadric in a specified four-dimensional space, or a KKT Lie algebra.
The coordinate Klein-quadric realization is handled by its separate owner.
-/

namespace InfoGeometry.Canonical

/-- An exterior product of the vectors in a finite basis of a subspace remains
nonzero after those vectors are included in the ambient vector space. -/
theorem exteriorPower_ιMulti_coe_basis_ne_zero
    {K : Type*} [Field K] {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    {P : Submodule K V} (b : Module.Basis (Fin n) K P) :
    exteriorPower.ιMulti K n (fun i => (b i : V)) ≠ 0 := by
  choose g hg using fun i : Fin n => LinearMap.exists_extend (b.coord i)
  let f : Fin n → Module.Dual K V := g
  have hg_apply (i j : Fin n) :
      g i (b j : V) = (b.coord i) (b j) := by
    exact LinearMap.congr_fun (hg i) (b j)
  have heval :
      (exteriorPower.alternatingMapToDual K V n f)
          (exteriorPower.ιMulti K n (fun i => (b i : V))) = 1 := by
    rw [exteriorPower.alternatingMapToDual_apply_ιMulti]
    rw [show Matrix.of (fun i j => f j (b i : V)) = 1 by
      ext i j
      classical
      by_cases h : i = j <;>
        simp [f, hg_apply, h, Matrix.one_apply]]
    exact Matrix.det_one
  intro hzero
  rw [hzero, map_zero] at heval
  norm_num at heval

/-- A finite linearly independent family has nonzero exterior product. -/
theorem exteriorPower_ιMulti_ne_zero_of_linearIndependent
    {K : Type*} [Field K] {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (v : Fin n → V) (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K n v ≠ 0 := by
  simpa only [Module.Basis.span_apply] using
    (exteriorPower_ιMulti_coe_basis_ne_zero (Module.Basis.span hv))

end InfoGeometry.Canonical
