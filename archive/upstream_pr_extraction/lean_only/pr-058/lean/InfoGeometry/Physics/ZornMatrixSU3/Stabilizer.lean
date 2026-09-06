import InfoGeometry.Physics.ZornMatrixSU3.ZornSU3Properties

namespace InfoGeometry.Physics.ZornMatrixSU3

/-!
# Bundled real cross-product stabilizers

This file bundles the real linear maps on `R^3` that preserve the dot and cross
products used by the Zorn multiplication.  The unbundled predicate
`IsRealCrossProductStabilizer` remains the low-level owner surface in
`ZornSU3Properties`; this module adds the corresponding nonempty bundled type
and proves that its action is the same Zorn algebra automorphism already proved
there.
-/

/--
A bundled real linear map on `R^3` preserving both the dot product and the
cross product.

This is a real cross-product stabilizer.  It is not a complex `SU(3)`
formalization; it is exactly the finite real structure needed by the Zorn
matrix multiplication lemmas.
-/
structure RealCrossProductStabilizer where
  /-- The underlying real linear map on `R^3`. -/
  toLinearMap : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)
  /-- Preservation of the dot product. -/
  preserves_dot :
    ∀ x y, dotProduct (toLinearMap x) (toLinearMap y) = dotProduct x y
  /-- Preservation of the cross product. -/
  preserves_cross :
    ∀ x y, toLinearMap (crossProduct x y) =
      crossProduct (toLinearMap x) (toLinearMap y)

namespace RealCrossProductStabilizer

instance : CoeFun RealCrossProductStabilizer
    (fun _ => (Fin 3 → ℝ) → Fin 3 → ℝ) where
  coe R := R.toLinearMap

/-- The bundled stabilizer determines the existing unbundled predicate. -/
theorem isRealCrossProductStabilizer (R : RealCrossProductStabilizer) :
    IsRealCrossProductStabilizer R.toLinearMap :=
  ⟨R.preserves_dot, R.preserves_cross⟩

/-- The identity map is a real cross-product stabilizer. -/
def id : RealCrossProductStabilizer where
  toLinearMap := LinearMap.id
  preserves_dot _ _ := rfl
  preserves_cross _ _ := rfl

/-- Bundled action on Zorn matrices. -/
def action (R : RealCrossProductStabilizer) (M : ZornMatrix) : ZornMatrix :=
  realCrossProductStabilizerAction R.toLinearMap M

/-- The bundled action preserves the split-octonion norm. -/
theorem action_preserves_norm
    (R : RealCrossProductStabilizer) (M : ZornMatrix) :
    norm (R.action M) = norm M :=
  realCrossProductStabilizerAction_preserves_norm
    R.toLinearMap R.isRealCrossProductStabilizer M

/-- The bundled action preserves Zorn multiplication. -/
theorem action_preserves_multiplication
    (R : RealCrossProductStabilizer) (M N : ZornMatrix) :
    R.action (M * N) = R.action M * R.action N :=
  realCrossProductStabilizerAction_preserves_multiplication
    R.toLinearMap R.isRealCrossProductStabilizer M N

@[simp] theorem id_action (M : ZornMatrix) :
    id.action M = M := by
  ext <;> rfl

end RealCrossProductStabilizer

/-- Backwards-compatible name for the identity real cross-product stabilizer. -/
def idRealCrossProductStabilizer : RealCrossProductStabilizer :=
  RealCrossProductStabilizer.id

end InfoGeometry.Physics.ZornMatrixSU3
