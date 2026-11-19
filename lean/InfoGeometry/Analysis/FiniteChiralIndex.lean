/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SpinorialCore.FiniteIndex
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The finite index as an adjoint-kernel difference

Connect the existing native kernel/cokernel index with the two actual adjoint
kernels. Rank-nullity and equality of adjoint ranks give the equality. A nonzero
index forces a nontrivial kernel on at least one side; the converse is false.
These are finite-dimensional Hilbert-space statements, not an elliptic index
theorem on a manifold.
-/

namespace InfoGeometry.Analysis.FiniteChiralIndex

open InfoGeometry.Canonical.SpinorialCore

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The cokernel in the existing index can be counted by the adjoint kernel. -/
theorem finiteIndex_eq_adjoint_kernel_difference (A : E →ₗ[𝕜] F) :
    finiteIndex A = (Module.finrank 𝕜 A.ker : ℤ) -
      (Module.finrank 𝕜 A.adjoint.ker : ℤ) := by
  rw [finiteIndex_eq_dimension_difference]
  have hA := LinearMap.finrank_range_add_finrank_ker A
  have hAdj := LinearMap.finrank_range_add_finrank_ker A.adjoint
  rw [LinearMap.finrank_range_adjoint] at hAdj
  omega

/-- A nonzero finite index forces at least one nontrivial adjoint kernel. -/
theorem nonzero_index_has_kernel (A : E →ₗ[𝕜] F) (hA : finiteIndex A ≠ 0) :
    A.ker ≠ ⊥ ∨ A.adjoint.ker ≠ ⊥ := by
  by_contra h
  push Not at h
  apply hA
  rw [finiteIndex_eq_adjoint_kernel_difference, h.1, h.2]
  simp

/-- The zero-index condition counts equal kernel dimensions, without asserting
that either kernel vanishes. -/
theorem index_zero_iff_kernel_finrank_eq (A : E →ₗ[𝕜] F) :
    finiteIndex A = 0 ↔ Module.finrank 𝕜 A.ker = Module.finrank 𝕜 A.adjoint.ker := by
  rw [finiteIndex_eq_adjoint_kernel_difference]
  omega

end InfoGeometry.Analysis.FiniteChiralIndex
