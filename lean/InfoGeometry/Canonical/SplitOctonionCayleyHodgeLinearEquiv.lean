import InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge

theorem hodgeStar_involutive : Function.Involutive hodgeStar := by
  intro x
  ext <;> simp [hodgeStar]

theorem hodgeStar_bijective : Function.Bijective hodgeStar :=
  ⟨hodgeStar_involutive.injective, hodgeStar_involutive.surjective⟩

noncomputable def hodgeStarLinearEquiv : Coord ≃ₗ[ℝ] Coord :=
  { hodgeStar with
    invFun := hodgeStar
    left_inv := hodgeStar_involutive
    right_inv := hodgeStar_involutive }

@[simp] theorem hodgeStarLinearEquiv_apply (x : Coord) :
    hodgeStarLinearEquiv x = hodgeStar x := rfl

@[simp] theorem hodgeStarLinearEquiv_symm_apply (x : Coord) :
    hodgeStarLinearEquiv.symm x = hodgeStar x := rfl

@[simp] theorem hodgeStarLinearEquiv_symm :
    hodgeStarLinearEquiv.symm = hodgeStarLinearEquiv := by
  apply LinearEquiv.ext
  intro x
  rfl

@[simp] theorem hodgeStarLinearEquiv_apply_apply (x : Coord) :
    hodgeStarLinearEquiv (hodgeStarLinearEquiv x) = x :=
  hodgeStar_involutive x

theorem hodgeStarLinearEquiv_toLinearMap :
    hodgeStarLinearEquiv.toLinearMap = hodgeStar := rfl

end InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge
