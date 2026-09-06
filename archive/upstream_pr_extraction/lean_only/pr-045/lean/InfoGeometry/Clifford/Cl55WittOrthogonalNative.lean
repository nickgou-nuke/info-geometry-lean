import InfoGeometry.Clifford.Cl55WittReflectionSubgroup
import InfoGeometry.Clifford.RealQuadraticReflection

namespace InfoGeometry.Clifford.Clifford55

noncomputable instance q55IsometryEquivGroup : Group (Q55.IsometryEquiv Q55) :=
  InfoGeometry.Clifford.quadraticIsometryEquivGroup Q55

/-!
# Native quadratic-isometry readout of `orthogonalGroup55`

`orthogonalGroup55` is the concrete subgroup used by the Pin action.  This
equivalence exposes exactly the same objects through Mathlib's native
`QuadraticMap.IsometryEquiv` interface, without introducing another carrier.
-/

noncomputable def orthogonalGroup55ToIsometry
    (g : orthogonalGroup55) : Q55.IsometryEquiv Q55 where
  __ := g.1
  map_app' := g.2

noncomputable def orthogonalGroup55FromIsometry
    (g : Q55.IsometryEquiv Q55) : orthogonalGroup55 where
  val := g.toLinearEquiv
  property := by
    intro x
    exact g.map_app x

noncomputable def orthogonalGroup55IsometryEquiv :
    orthogonalGroup55 ≃ Q55.IsometryEquiv Q55 where
  toFun := orthogonalGroup55ToIsometry
  invFun := orthogonalGroup55FromIsometry
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl
  right_inv g := by
    cases g
    rfl

noncomputable def orthogonalGroup55MulEquiv :
    orthogonalGroup55 ≃* Q55.IsometryEquiv Q55 where
  toEquiv := orthogonalGroup55IsometryEquiv
  map_mul' g h := by
    apply DFunLike.ext _ _
    intro x
    rfl

@[simp] theorem orthogonalGroup55IsometryEquiv_apply
    (g : orthogonalGroup55) :
    orthogonalGroup55IsometryEquiv g = orthogonalGroup55ToIsometry g :=
  rfl

@[simp] theorem orthogonalGroup55IsometryEquiv_symm_apply
    (g : Q55.IsometryEquiv Q55) :
    orthogonalGroup55IsometryEquiv.symm g =
      orthogonalGroup55FromIsometry g :=
  rfl

end InfoGeometry.Clifford.Clifford55
