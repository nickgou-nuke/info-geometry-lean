import InfoGeometry.Algebra.Zorn.RegularActionAssociator
import InfoGeometry.Algebra.Zorn.Associator
import InfoGeometry.Algebra.ZornDerivationBridge

namespace InfoGeometry.Algebra

noncomputable section

variable {A : Type*}
variable [NonUnitalNonAssocRing A] [Module ℝ A]
variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

structure CurvatureRegularActionSoldering
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (R0 : T → T → T → T) where
  parameterMap : T →ₗ[ℝ] A
  carrierMap : T →ₗ[ℝ] A
  carrier_injective : Function.Injective carrierMap
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  intertwining : ∀ X Y Z,
      carrierMap (R0 X Y Z) =
        scale •
          ((leftRightCommutator (R := ℝ) (A := A) (parameterMap X) (parameterMap Y) :
            A →ₗ[ℝ] A) (carrierMap Z))

structure MetricCurvatureRegularActionSoldering
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (R0 : T → T → T → T)
    extends CurvatureRegularActionSoldering (A := A) R0 where
  metricT : LinearMap.BilinForm ℝ T
  metricT_nondegenerate : metricT.Nondegenerate
  metricA : LinearMap.BilinForm ℝ A
  metricA_symm : metricA.IsSymm
  metric_transport : ∀ U V,
    metricA (carrierMap U) (carrierMap V) = metricT U V
  curvature_skew : ∀ X Y Z W,
    metricT (R0 X Y Z) W + metricT Z (R0 X Y W) = 0

noncomputable def rangeMetric
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : MetricCurvatureRegularActionSoldering (A := A) R0) :
    LinearMap.BilinForm ℝ (LinearMap.range B.carrierMap) :=
  LinearMap.mk₂ ℝ
    (fun (u v : LinearMap.range B.carrierMap) => B.metricA u.1 v.1)
    (by intro u₁ u₂ v; simp [map_add])
    (by intro r u v; simp [map_smul, smul_eq_mul])
    (by intro u v₁ v₂; simp [map_add])
    (by intro r u v; simp [map_smul, smul_eq_mul])

@[simp] theorem rangeMetric_apply
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : MetricCurvatureRegularActionSoldering (A := A) R0)
    (u v : LinearMap.range B.carrierMap) :
    rangeMetric B u v = B.metricA u.1 v.1 := by
  simp [rangeMetric]

theorem rangeMetric_carrierMap
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : MetricCurvatureRegularActionSoldering (A := A) R0)
    (U V : T) :
    rangeMetric B
        ⟨B.carrierMap U, ⟨U, rfl⟩⟩
        ⟨B.carrierMap V, ⟨V, rfl⟩⟩ = B.metricT U V := by
  rw [rangeMetric_apply, B.metric_transport]

theorem rangeMetric_isSymm
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
  (B : MetricCurvatureRegularActionSoldering (A := A) R0) :
    (rangeMetric B).IsSymm := by
  exact ⟨fun u v => B.metricA_symm.eq u.1 v.1⟩

theorem metricT_isSymm
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : MetricCurvatureRegularActionSoldering (A := A) R0) :
    B.metricT.IsSymm := by
  refine ⟨fun U V => ?_⟩
  rw [← B.metric_transport U V, ← B.metric_transport V U]
  exact B.metricA_symm.eq _ _

theorem rangeMetric_nondegenerate
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : MetricCurvatureRegularActionSoldering (A := A) R0) :
    (rangeMetric B).Nondegenerate := by
  constructor
  · intro u hu
    rcases u with ⟨u, ⟨U, rfl⟩⟩
    have hU : ∀ V : T, B.metricT U V = 0 := by
      intro V
      have h := hu ⟨B.carrierMap V, ⟨V, rfl⟩⟩
      simpa [rangeMetric, B.metric_transport U V] using h
    have hU0 : U = 0 := B.metricT_nondegenerate.1 U hU
    simp [hU0]
  · intro u hu
    rcases u with ⟨u, ⟨U, rfl⟩⟩
    have hU : ∀ V : T, B.metricT V U = 0 := by
      intro V
      have h := hu ⟨B.carrierMap V, ⟨V, rfl⟩⟩
      simpa [rangeMetric, B.metric_transport V U] using h
    have hU0 : U = 0 := B.metricT_nondegenerate.2 U hU
    simp [hU0]

theorem metric_skew_transport
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : MetricCurvatureRegularActionSoldering (A := A) R0)
    (X Y Z W : T) :
    B.metricA
        (leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
          (B.carrierMap Z)) (B.carrierMap W) +
      B.metricA (B.carrierMap Z)
        (leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
          (B.carrierMap W)) = 0 := by
  have h := B.curvature_skew X Y Z W
  rw [← B.metric_transport (R0 X Y Z) W,
    ← B.metric_transport Z (R0 X Y W)] at h
  rw [B.intertwining X Y Z, B.intertwining X Y W] at h
  simp only [map_smul, smul_eq_mul] at h
  have hscale : B.scale * (
      B.metricA
          (leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
            (B.carrierMap Z)) (B.carrierMap W) +
        B.metricA (B.carrierMap Z)
          (leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
            (B.carrierMap W))) = 0 := by
    rw [mul_add]
    exact h
  exact (mul_eq_zero.mp hscale).resolve_left B.scale_ne_zero

theorem carrier_image_preimage
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (X Y Z : T) :
    B.carrierMap ((B.scale⁻¹) • R0 X Y Z) =
    leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
        (B.carrierMap Z) := by
  rw [B.carrierMap.map_smul]
  calc
    B.scale⁻¹ • B.carrierMap (R0 X Y Z) =
        B.scale⁻¹ • (B.scale • leftRightCommutator (R := ℝ) (A := A)
          (B.parameterMap X) (B.parameterMap Y) (B.carrierMap Z)) := by
      rw [B.intertwining]
    _ = leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
          (B.carrierMap Z) := by
      rw [smul_smul]
      simp [B.scale_ne_zero]

theorem carrier_image_invariant
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (X Y Z : T) :
    ∃ W : T,
      leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
          (B.carrierMap Z) = B.carrierMap W := by
  refine ⟨(B.scale⁻¹) • R0 X Y Z, ?_⟩
  exact (carrier_image_preimage B X Y Z).symm

/-! The pointwise image statement above can be bundled without choosing
preimages: the domain is the submodule range of the carrier map and
`LinearMap.codRestrict` supplies the range-valued codomain. -/

noncomputable def restrictedLeftRight
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (X Y : T) :
    LinearMap.range B.carrierMap →ₗ[ℝ] LinearMap.range B.carrierMap := by
  let F : A →ₗ[ℝ] A :=
    leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
  have hmem : ∀ w : LinearMap.range B.carrierMap,
      F w.1 ∈ LinearMap.range B.carrierMap := by
    rintro ⟨w, hw⟩
    rcases hw with ⟨Z, rfl⟩
    rcases carrier_image_invariant B X Y Z with ⟨W, hW⟩
    exact ⟨W, hW.symm⟩
  exact (F.comp (LinearMap.range B.carrierMap).subtype).codRestrict
    (LinearMap.range B.carrierMap) hmem

@[simp] theorem restrictedLeftRight_apply_subtype
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (X Y : T) (w : LinearMap.range B.carrierMap) :
    ((restrictedLeftRight B X Y w : LinearMap.range B.carrierMap) : A) =
      leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y) w.1 := by
  rfl

theorem metric_skew_restricted
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : MetricCurvatureRegularActionSoldering (A := A) R0)
    (X Y : T) (u v : LinearMap.range B.carrierMap) :
    B.metricA
        ((restrictedLeftRight (A := A) B.toCurvatureRegularActionSoldering X Y u : A)) v.1 +
      B.metricA u.1
        ((restrictedLeftRight (A := A) B.toCurvatureRegularActionSoldering X Y v : A)) = 0 := by
  rcases u with ⟨u, ⟨U, rfl⟩⟩
  rcases v with ⟨v, ⟨V, rfl⟩⟩
  simpa only [restrictedLeftRight_apply_subtype] using
    metric_skew_transport B X Y U V

theorem rangeMetric_restricted_skew
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : MetricCurvatureRegularActionSoldering (A := A) R0)
    (X Y : T) (u v : LinearMap.range B.carrierMap) :
    rangeMetric B (restrictedLeftRight B.toCurvatureRegularActionSoldering X Y u) v +
        rangeMetric B u
          (restrictedLeftRight B.toCurvatureRegularActionSoldering X Y v) = 0 := by
  simpa only [rangeMetric_apply] using
    metric_skew_restricted B X Y u v

theorem restrictedLeftRight_carrierMap
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (X Y Z : T) :
    ((restrictedLeftRight B X Y
        ⟨B.carrierMap Z, ⟨Z, rfl⟩⟩ : LinearMap.range B.carrierMap) : A) =
      B.scale⁻¹ • B.carrierMap (R0 X Y Z) := by
  rw [restrictedLeftRight_apply_subtype]
  calc
    leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
          (B.carrierMap Z) =
        (1 : ℝ) • leftRightCommutator (R := ℝ) (A := A)
          (B.parameterMap X) (B.parameterMap Y) (B.carrierMap Z) := by simp
    _ = B.scale⁻¹ • (B.scale • leftRightCommutator (R := ℝ) (A := A)
          (B.parameterMap X) (B.parameterMap Y) (B.carrierMap Z)) := by
      rw [smul_smul]
      simp [B.scale_ne_zero]
    _ = B.scale⁻¹ • B.carrierMap (R0 X Y Z) := by
      rw [← B.intertwining X Y Z]

theorem restrictedLeftRight_first_bianchi
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (hBianchi : ∀ X Y Z,
      R0 X Y Z + R0 Y Z X + R0 Z X Y = 0)
    (X Y Z : T) :
    restrictedLeftRight B X Y ⟨B.carrierMap Z, ⟨Z, rfl⟩⟩ +
        restrictedLeftRight B Y Z ⟨B.carrierMap X, ⟨X, rfl⟩⟩ +
        restrictedLeftRight B Z X ⟨B.carrierMap Y, ⟨Y, rfl⟩⟩ = 0 := by
  apply Subtype.ext
  change
    (((restrictedLeftRight B X Y
        ⟨B.carrierMap Z, ⟨Z, rfl⟩⟩ : LinearMap.range B.carrierMap) : A) +
      ((restrictedLeftRight B Y Z
        ⟨B.carrierMap X, ⟨X, rfl⟩⟩ : LinearMap.range B.carrierMap) : A) +
      ((restrictedLeftRight B Z X
        ⟨B.carrierMap Y, ⟨Y, rfl⟩⟩ : LinearMap.range B.carrierMap) : A)) = 0
  rw [restrictedLeftRight_carrierMap, restrictedLeftRight_carrierMap,
    restrictedLeftRight_carrierMap]
  rw [← smul_add, ← smul_add, ← B.carrierMap.map_add,
    ← B.carrierMap.map_add, hBianchi]
  simp

theorem transported_first_bianchi
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (hBianchi : ∀ X Y Z,
      R0 X Y Z + R0 Y Z X + R0 Z X Y = 0)
    (X Y Z : T) :
    leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
        (B.carrierMap Z) +
      leftRightCommutator (R := ℝ) (A := A) (B.parameterMap Y) (B.parameterMap Z)
        (B.carrierMap X) +
      leftRightCommutator (R := ℝ) (A := A) (B.parameterMap Z) (B.parameterMap X)
        (B.carrierMap Y) = 0 := by
  have hscale : B.scale • (
      leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
          (B.carrierMap Z) +
        leftRightCommutator (R := ℝ) (A := A) (B.parameterMap Y) (B.parameterMap Z)
          (B.carrierMap X) +
        leftRightCommutator (R := ℝ) (A := A) (B.parameterMap Z) (B.parameterMap X)
          (B.carrierMap Y)) = 0 := by
    rw [smul_add, smul_add,
      ← B.intertwining X Y Z, ← B.intertwining Y Z X,
      ← B.intertwining Z X Y, ← map_add, ← map_add, hBianchi]
    simp
  exact (smul_eq_zero.mp hscale).resolve_left B.scale_ne_zero

theorem curvature_zero_iff_regular_action_zero
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (X Y Z : T) :
    R0 X Y Z = 0 ↔
      leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
        (B.carrierMap Z) = 0 := by
  constructor
  · intro hR
    have hs : B.scale •
        leftRightCommutator (R := ℝ) (A := A) (B.parameterMap X) (B.parameterMap Y)
          (B.carrierMap Z) = 0 := by
      rw [← B.intertwining X Y Z, hR, map_zero]
    exact (smul_eq_zero.mp hs).resolve_left B.scale_ne_zero
  · intro hC
    have hi : B.carrierMap (R0 X Y Z) = 0 := by
      rw [B.intertwining X Y Z, hC, smul_zero]
    apply B.carrier_injective
    simpa using hi

theorem regular_action_zero_iff_associator_zero
    (hright : ∀ x y : A, (x * y) * y = x * (y * y))
    (x y z : A) :
    leftRightCommutator (R := ℝ) (A := A) x y z = 0 ↔
      _root_.associator x y z = 0 := by
  rw [leftRightCommutator_apply_of_alternative (A := A)
    (fun x y => hright y x)]

theorem transported_first_bianchi_associator
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (hBianchi : ∀ X Y Z,
      R0 X Y Z + R0 Y Z X + R0 Z X Y = 0)
    (X Y Z : T) :
    _root_.associator (B.parameterMap X) (B.parameterMap Y) (B.carrierMap Z) +
      _root_.associator (B.parameterMap Y) (B.parameterMap Z) (B.carrierMap X) +
      _root_.associator (B.parameterMap Z) (B.parameterMap X) (B.carrierMap Y) = 0 := by
  have h1 := leftRightCommutator_apply_of_alternative
    (R := ℝ) (A := A) hright (B.parameterMap X) (B.parameterMap Y)
      (B.carrierMap Z)
  have h2 := leftRightCommutator_apply_of_alternative
    (R := ℝ) (A := A) hright (B.parameterMap Y) (B.parameterMap Z)
      (B.carrierMap X)
  have h3 := leftRightCommutator_apply_of_alternative
    (R := ℝ) (A := A) hright (B.parameterMap Z) (B.parameterMap X)
      (B.carrierMap Y)
  rw [← h1, ← h2, ← h3]
  exact transported_first_bianchi B hBianchi X Y Z

theorem transported_first_bianchi_forces_associator_zero_of_same_map
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    {R0 : T → T → T → T}
    (B : CurvatureRegularActionSoldering (A := A) R0)
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (hBianchi : ∀ X Y Z,
      R0 X Y Z + R0 Y Z X + R0 Z X Y = 0)
    (hmap : B.parameterMap = B.carrierMap)
    (X Y Z : T) :
    _root_.associator (B.carrierMap X) (B.carrierMap Y) (B.carrierMap Z) = 0 := by
  have hB := transported_first_bianchi_associator B hright hBianchi X Y Z
  rw [hmap] at hB
  have hcyc1 : _root_.associator (B.carrierMap Y) (B.carrierMap Z)
      (B.carrierMap X) =
      _root_.associator (B.carrierMap X) (B.carrierMap Y)
        (B.carrierMap Z) :=
    alternative_associator_cycle hleft hright
      (B.carrierMap X) (B.carrierMap Y) (B.carrierMap Z)
  have hcyc2 : _root_.associator (B.carrierMap Z) (B.carrierMap X)
      (B.carrierMap Y) =
      _root_.associator (B.carrierMap X) (B.carrierMap Y)
        (B.carrierMap Z) := by
    exact (alternative_associator_cycle hleft hright
      (B.carrierMap Y) (B.carrierMap Z) (B.carrierMap X)).trans hcyc1
  have hthree :
      _root_.associator (B.carrierMap X) (B.carrierMap Y)
          (B.carrierMap Z) +
        (_root_.associator (B.carrierMap X) (B.carrierMap Y)
          (B.carrierMap Z) +
          _root_.associator (B.carrierMap X) (B.carrierMap Y)
            (B.carrierMap Z)) = 0 := by
    simpa [hcyc1, hcyc2, add_assoc] using hB
  have hzero : (3 : ℝ) •
      _root_.associator (B.carrierMap X) (B.carrierMap Y) (B.carrierMap Z) = 0 := by
    convert hthree using 1 <;> module
  exact (smul_eq_zero.mp hzero).resolve_left (by norm_num)

theorem zorn_leftRightCommutator_apply_eq_associator
    (x y z : ZornVectorMatrix ℝ) :
    leftRightCommutator (R := ℝ) x y z = _root_.associator x y z := by
  exact leftRightCommutator_apply_of_alternative
    (A := ZornVectorMatrix ℝ)
    zorn_right_alternative x y z

end
end InfoGeometry.Algebra
