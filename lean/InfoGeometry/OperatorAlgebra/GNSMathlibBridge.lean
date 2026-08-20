import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

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

/-! The following lemmas expose the algebraic representation laws at the
level of the concrete GNS bridge.  Keeping these as named facts avoids
unfolding the completion construction in downstream operator arguments. -/

@[simp]
theorem gnsStarAlgHom_map_one :
    f.gnsStarAlgHom (1 : A) = 1 := by
  exact f.gnsStarAlgHom.map_one

@[simp]
theorem gnsStarAlgHom_map_mul (a b : A) :
    f.gnsStarAlgHom (a * b) = f.gnsStarAlgHom a * f.gnsStarAlgHom b := by
  exact f.gnsStarAlgHom.map_mul a b

@[simp]
theorem gnsStarAlgHom_map_smul (r : ℂ) (a : A) :
    f.gnsStarAlgHom (r • a) = r • f.gnsStarAlgHom a := by
  exact map_smul f.gnsStarAlgHom r a

@[simp]
theorem gnsStarAlgHom_map_add (a b : A) :
    f.gnsStarAlgHom (a + b) = f.gnsStarAlgHom a + f.gnsStarAlgHom b := by
  exact f.gnsStarAlgHom.map_add a b

@[simp]
theorem gnsStarAlgHom_map_zero :
    f.gnsStarAlgHom (0 : A) = 0 := by
  exact f.gnsStarAlgHom.map_zero

@[simp]
theorem gnsStarAlgHom_map_star (a : A) :
    f.gnsStarAlgHom (star a) = star (f.gnsStarAlgHom a) := by
  exact map_star f.gnsStarAlgHom a

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

/-- The cyclic-vector norm coefficient is the state evaluated at the unit. -/
@[simp]
theorem cyclicVector_inner_self :
    ⟪cyclicVector f, cyclicVector f⟫_ℂ = f 1 := by
  simpa using cyclicVector_inner_gnsStarAlgHom f (1 : A)

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

/-- General GNS matrix coefficients recover the positive functional on
    `star a * b`. -/
@[simp]
theorem gnsStarAlgHom_matrix_coefficient (a b : A) :
    ⟪f.gnsStarAlgHom a (cyclicVector f),
      f.gnsStarAlgHom b (cyclicVector f)⟫_ℂ = f (star a * b) := by
  rw [gnsStarAlgHom_apply_cyclicVector, gnsStarAlgHom_apply_cyclicVector]
  change ⟪((f.toPreGNS a : f.PreGNS) : f.GNS),
      ((f.toPreGNS b : f.PreGNS) : f.GNS)⟫_ℂ = f (star a * b)
  simp [PositiveLinearMap.preGNS_inner_def]

end InfoGeometry.OperatorAlgebra.GNSMathlibBridge
