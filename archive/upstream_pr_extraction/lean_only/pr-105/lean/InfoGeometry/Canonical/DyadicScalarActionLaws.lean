import InfoGeometry.Canonical.DyadicScalarAction

namespace InfoGeometry.Canonical

/-!
# Explicit scalar laws for the dyadic action

`DyadicRational` is kept as the existing additive-subgroup carrier, so this
owner exposes the scalar laws explicitly instead of installing an unproved
ring or module instance on that subtype.
-/

def dyadicOne : DyadicRational :=
  ⟨1, by refine ⟨1, 0, ?_⟩; norm_num⟩

@[simp] theorem dyadicOne_value : (dyadicOne : ℚ) = 1 := rfl

theorem dyadicScalarMul_one (a : DyadicRational) :
    dyadicScalarMul dyadicOne a = a := by
  apply Subtype.ext
  simp [dyadicScalarMul, dyadicOne]

theorem dyadicScalarMul_assoc
    (a b c : DyadicRational) :
    dyadicScalarMul a (dyadicScalarMul b c) =
      dyadicScalarMul (dyadicScalarMul a b) c := by
  apply Subtype.ext
  simp [dyadicScalarMul]
  ring

theorem dyadicScalarMul_add_left
    (a b c : DyadicRational) :
    dyadicScalarMul (a + b) c =
      dyadicScalarMul a c + dyadicScalarMul b c := by
  apply Subtype.ext
  simp [dyadicScalarMul]
  ring

theorem dyadicScalarMul_add_right
    (a b c : DyadicRational) :
    dyadicScalarMul a (b + c) =
      dyadicScalarMul a b + dyadicScalarMul a c := by
  apply Subtype.ext
  simp [dyadicScalarMul]
  ring

theorem dyadicDirectLimit_dyadic_smul_one
    (x : DyadicDirectLimit) :
    dyadicOne • x = x := by
  apply dyadicDirectLimitEquiv.injective
  rw [dyadicDirectLimitEquiv_dyadic_smul]
  apply Subtype.ext
  simp [dyadicScalarMul, dyadicOne]

theorem dyadicDirectLimit_dyadic_smul_assoc
    (a b : DyadicRational) (x : DyadicDirectLimit) :
    a • (b • x) = dyadicScalarMul a b • x := by
  apply dyadicDirectLimitEquiv.injective
  rw [dyadicDirectLimitEquiv_dyadic_smul,
    dyadicDirectLimitEquiv_dyadic_smul,
    dyadicDirectLimitEquiv_dyadic_smul]
  exact dyadicScalarMul_assoc a b (dyadicDirectLimitEquiv x)

theorem dyadicDirectLimit_dyadic_smul_add
    (a : DyadicRational) (x y : DyadicDirectLimit) :
    a • (x + y) = a • x + a • y := by
  apply dyadicDirectLimitEquiv.injective
  rw [dyadicDirectLimitEquiv_dyadic_smul a (x + y),
    dyadicDirectLimitEquiv_add (a • x) (a • y),
    dyadicDirectLimitEquiv_dyadic_smul a x,
    dyadicDirectLimitEquiv_dyadic_smul a y]
  apply Subtype.ext
  simp only [dyadicScalarMul, Subtype.coe_mk]
  rw [dyadicDirectLimitEquiv_add x y]
  change (a : ℚ) * ((dyadicDirectLimitEquiv x : ℚ) + (dyadicDirectLimitEquiv y : ℚ)) = (a : ℚ) * (dyadicDirectLimitEquiv x : ℚ) + (a : ℚ) * (dyadicDirectLimitEquiv y : ℚ)
  exact mul_add _ _ _
theorem dyadicDirectLimit_dyadic_add_smul
    (a b : DyadicRational) (x : DyadicDirectLimit) :
    (a + b) • x = a • x + b • x := by
  apply dyadicDirectLimitEquiv.injective
  simp only [dyadicDirectLimitEquiv_dyadic_smul,
    dyadicDirectLimitEquiv_add]
  apply Subtype.ext
  simp [dyadicScalarMul]
  ring

end InfoGeometry.Canonical
