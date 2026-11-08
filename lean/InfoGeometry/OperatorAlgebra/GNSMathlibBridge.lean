import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace InfoGeometry.OperatorAlgebra.GNSMathlibBridge

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

/--
The canonical cyclic vector in the unital GNS representation of a positive
linear functional, namely the image of `1` in the Hilbert completion.
-/
noncomputable def cyclicVector : f.GNS :=
  (f.toPreGNS (1 : A) : f.GNS)

/--
The GNS representation sends the cyclic vector `Λ(1)` to `Λ(a)`.

This is the concrete cyclic-vector action missing from the current mathlib GNS
file's TODO list; it uses mathlib's completed representation
`PositiveLinearMap.gnsStarAlgHom`.
-/
@[simp]
theorem gnsStarAlgHom_apply_cyclicVector (a : A) :
    f.gnsStarAlgHom a (cyclicVector f) = (f.toPreGNS a : f.GNS) := by
  rw [cyclicVector]
  simp [PositiveLinearMap.gnsStarAlgHom,
    PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
    PositiveLinearMap.leftMulMapPreGNS]

/--
The cyclic vector recovers the original positive linear functional as a matrix
coefficient of the completed GNS representation.
-/
@[simp]
theorem cyclicVector_inner_gnsStarAlgHom (a : A) :
    ⟪cyclicVector f, f.gnsStarAlgHom a (cyclicVector f)⟫_ℂ = f a := by
  rw [gnsStarAlgHom_apply_cyclicVector]
  rw [cyclicVector]
  change ⟪((f.toPreGNS (1 : A) : f.PreGNS) : f.GNS),
      ((f.toPreGNS a : f.PreGNS) : f.GNS)⟫_ℂ = f a
  simp [PositiveLinearMap.preGNS_inner_def]

/--
The adjoint matrix coefficient reads the functional on `star a`.
-/
@[simp]
theorem gnsStarAlgHom_cyclicVector_inner (a : A) :
    ⟪f.gnsStarAlgHom a (cyclicVector f), cyclicVector f⟫_ℂ = f (star a) := by
  rw [gnsStarAlgHom_apply_cyclicVector]
  rw [cyclicVector]
  change ⟪((f.toPreGNS a : f.PreGNS) : f.GNS),
      ((f.toPreGNS (1 : A) : f.PreGNS) : f.GNS)⟫_ℂ = f (star a)
  simp [PositiveLinearMap.preGNS_inner_def]

end InfoGeometry.OperatorAlgebra.GNSMathlibBridge
