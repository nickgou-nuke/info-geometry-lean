import InfoGeometry.Algebra.ZornDerivationBridge

/-! Native vector-carrier interface for the standard derivations of the split
octonion Zorn algebra.  The standard formula and its Leibniz proof remain
owned by `AlternativeDerivations`; this file only transports that result. -/

namespace InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear

open InfoGeometry.Algebra

abbrev VZ := ZornVectorMatrix ℝ
abbrev VDer := ZornVectorMatrix.Derivation (R := ℝ)

noncomputable def innerDerivation : VZ →ₗ[ℝ] VZ →ₗ[ℝ] VDer :=
  LinearMap.mk₂ ℝ
    (fun x y => fromNonAssocDerivation
      (zornStanDerivation x y))
    (fun x₁ x₂ y => by
      apply ZornVectorMatrix.Derivation.ext
      intro z
      change stanDerMap (R := ℝ) (x₁ + x₂) y z =
        stanDerMap (R := ℝ) x₁ y z + stanDerMap (R := ℝ) x₂ y z
      rw [stanDerMap_add_left]
      simp only [LinearMap.add_apply])
    (fun r x y => by
      apply ZornVectorMatrix.Derivation.ext
      intro z
      change stanDerMap (R := ℝ) (r • x) y z =
        r • stanDerMap (R := ℝ) x y z
      rw [stanDerMap_smul_left]
      simp only [LinearMap.smul_apply])
    (fun x y₁ y₂ => by
      apply ZornVectorMatrix.Derivation.ext
      intro z
      change stanDerMap (R := ℝ) x (y₁ + y₂) z =
        stanDerMap (R := ℝ) x y₁ z + stanDerMap (R := ℝ) x y₂ z
      rw [stanDerMap_add_right]
      simp only [LinearMap.add_apply])
    (fun r x y => by
      apply ZornVectorMatrix.Derivation.ext
      intro z
      change stanDerMap (R := ℝ) x (r • y) z =
        r • stanDerMap (R := ℝ) x y z
      rw [stanDerMap_smul_right]
      simp only [LinearMap.smul_apply])

@[simp] theorem innerDerivation_apply (x y : VZ) :
    innerDerivation x y = fromNonAssocDerivation (zornStanDerivation x y) := rfl

@[simp] theorem innerDerivation_apply_value (x y z : VZ) :
    innerDerivation x y z = stanDerMap (R := ℝ) x y z := rfl

theorem innerDerivation_isLeibniz (x y z w : VZ) :
    innerDerivation x y (ZornVectorMatrix.mul z w) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul (innerDerivation x y z) w)
        (ZornVectorMatrix.mul z (innerDerivation x y w)) := by
  exact (innerDerivation x y).map_mul z w

theorem innerDerivation_operatorial_normal_form (x y z : VZ) :
    innerDerivation x y z =
      ((x * y - y * x) * z - z * (x * y - y * x)) -
        3 • ((x * y) * z - x * (y * z)) := by
  rw [innerDerivation_apply_value,
    stanDerMap_apply_normal_form zorn_left_alternative zorn_right_alternative]
  rfl

theorem innerDerivation_swap (x y : VZ) :
    innerDerivation y x = -(innerDerivation x y) := by
  apply ZornVectorMatrix.Derivation.ext
  intro z
  change innerDerivation y x z = -innerDerivation x y z
  rw [innerDerivation_operatorial_normal_form,
    innerDerivation_operatorial_normal_form]
  have h := alternative_associator_swap12
    (A := VZ) zorn_left_alternative x y z
  have h' : (x * y) * z - x * (y * z) =
      -((y * x) * z - y * (x * z)) := by
    simpa [associator_apply] using h
  rw [h']
  simp only [sub_eq_add_neg, neg_add, neg_neg, smul_neg, neg_smul,
    add_mul, mul_add, neg_mul, mul_neg, smul_add, add_smul,
    smul_mul_assoc, mul_smul_comm]
  abel

/-! The following facts expose the algebraic image of the native bilinear map.
They deliberately stop short of a top-span claim: that claim requires an
independent finite witness calculation for the chosen eight-element basis. -/

@[simp] theorem innerDerivation_zero_left (y : VZ) :
    innerDerivation 0 y = 0 := by
  rw [innerDerivation.map_zero]
  rfl

@[simp] theorem innerDerivation_zero_right (x : VZ) :
    innerDerivation x 0 = 0 := by
  exact (innerDerivation x).map_zero

theorem innerDerivation_mem_pairSpan (x y : VZ) :
    innerDerivation x y ∈
      Submodule.span ℝ (Set.range (fun p : VZ × VZ => innerDerivation p.1 p.2)) := by
  exact Submodule.subset_span ⟨(x, y), rfl⟩

theorem innerDerivation_add_left (x₁ x₂ y : VZ) :
    innerDerivation (x₁ + x₂) y =
      innerDerivation x₁ y + innerDerivation x₂ y := by
  rw [innerDerivation.map_add]
  rfl

theorem innerDerivation_add_right (x y₁ y₂ : VZ) :
    innerDerivation x (y₁ + y₂) =
      innerDerivation x y₁ + innerDerivation x y₂ := by
  exact ((innerDerivation x).map_add y₁ y₂)

theorem innerDerivation_smul_left (r : ℝ) (x y : VZ) :
    innerDerivation (r • x) y = r • innerDerivation x y := by
  rw [innerDerivation.map_smul]
  rfl

theorem innerDerivation_smul_right (r : ℝ) (x y : VZ) :
    innerDerivation x (r • y) = r • innerDerivation x y := by
  exact (innerDerivation x).map_smul r y

theorem innerDerivation_range_span_eq_stanDerMap_range_span :
    Submodule.span ℝ (Set.range (fun p : VZ × VZ => innerDerivation p.1 p.2)) =
      Submodule.span ℝ (Set.range (fun p : VZ × VZ =>
        fromNonAssocDerivation (zornStanDerivation p.1 p.2))) := by
  rfl

end InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear
