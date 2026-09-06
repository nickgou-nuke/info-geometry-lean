import Mathlib

/-!
# Native standard representation of `SO(4)`

This owner closes only the ordinary finite-dimensional orthogonal action of
the native Mathlib group `Matrix.specialOrthogonalGroup (Fin 4) ℝ` on
`Fin 4 → ℝ`.  It is deliberately separate from a spin representation on the
`Cl(5,5)` carrier: no spin double cover, Lie-group structure, or Kasparov
class is inferred here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SO4StandardRepresentationBridge

abbrev SO4 := Matrix.specialOrthogonalGroup (Fin 4) ℝ
abbrev Euclidean4 := EuclideanSpace ℝ (Fin 4)
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

/-- The standard representation of SO(4) on ℝ^4 represented as (Fin 4 → ℝ). -/
def so4VecAction (g : SO4) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  (g : Mat4).mulVec x

@[simp] theorem so4VecAction_one (x : Fin 4 → ℝ) :
    so4VecAction (1 : SO4) x = x := by
  dsimp [so4VecAction]
  simp [Matrix.one_mulVec]

theorem so4VecAction_mul (g h : SO4) (x : Fin 4 → ℝ) :
    so4VecAction (g * h) x = so4VecAction g (so4VecAction h x) := by
  dsimp [so4VecAction]
  simp [Matrix.mulVec_mulVec]

def so4VecActionLinear (g : SO4) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  Matrix.toLin' (g : Mat4)

@[simp] theorem so4VecActionLinear_apply (g : SO4) (x : Fin 4 → ℝ) :
    so4VecActionLinear g x = so4VecAction g x := rfl

noncomputable def so4VecActionEquiv (g : SO4) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofLinear
    (so4VecActionLinear g) (so4VecActionLinear g⁻¹)
    (by
      apply LinearMap.ext
      intro x
      calc
        (so4VecActionLinear g ∘ₗ so4VecActionLinear g⁻¹) x =
            so4VecAction g (so4VecAction (g⁻¹) x) := by
              simp only [LinearMap.comp_apply, so4VecActionLinear_apply]
        _ = so4VecAction (g * g⁻¹) x := (so4VecAction_mul g g⁻¹ x).symm
        _ = x := by simp [so4VecAction_one])
    (by
      apply LinearMap.ext
      intro x
      calc
        (so4VecActionLinear g⁻¹ ∘ₗ so4VecActionLinear g) x =
            so4VecAction (g⁻¹) (so4VecAction g x) := by
              simp only [LinearMap.comp_apply, so4VecActionLinear_apply]
        _ = so4VecAction (g⁻¹ * g) x := (so4VecAction_mul g⁻¹ g x).symm
        _ = x := by simp [so4VecAction_one])

@[simp] theorem so4VecActionEquiv_apply (g : SO4) (x : Fin 4 → ℝ) :
    so4VecActionEquiv g x = so4VecAction g x := rfl

noncomputable def so4StandardVectorRepresentation :
    SO4 →* ((Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) where
  toFun := so4VecActionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp [so4VecActionEquiv, so4VecActionLinear_apply, so4VecAction_one]
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro x
    simp [so4VecActionEquiv, so4VecAction_mul]

/-- The standard action on EuclideanSpace ℝ (Fin 4). -/
def so4Action (g : SO4) (x : Euclidean4) : Euclidean4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm (so4VecAction g (EuclideanSpace.equiv (Fin 4) ℝ x))

@[simp] theorem so4Action_one (x : Euclidean4) :
    so4Action (1 : SO4) x = x := by
  dsimp [so4Action]
  rw [so4VecAction_one]
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm_apply_apply x

theorem so4Action_mul (g h : SO4) (x : Euclidean4) :
    so4Action (g * h) x = so4Action g (so4Action h x) := by
  dsimp [so4Action]
  congr 1
  exact so4VecAction_mul g h (EuclideanSpace.equiv (Fin 4) ℝ x)

/-- Linear map form of the standard representation on EuclideanSpace. -/
def so4ActionLinear (g : SO4) : Euclidean4 →ₗ[ℝ] Euclidean4 :=
  ((EuclideanSpace.equiv (Fin 4) ℝ).symm.toLinearMap).comp
    ((Matrix.toLin' (g : Mat4)).comp (EuclideanSpace.equiv (Fin 4) ℝ).toLinearMap)

@[simp] theorem so4ActionLinear_apply (g : SO4) (x : Euclidean4) :
    so4ActionLinear g x = so4Action g x := rfl

theorem so4ActionLinear_one :
    so4ActionLinear (1 : SO4) = (1 : Module.End ℝ Euclidean4) := by
  apply LinearMap.ext
  intro x
  change so4ActionLinear (1 : SO4) x = x
  simpa only [so4ActionLinear_apply] using so4Action_one x

theorem so4ActionLinear_mul (g h : SO4) :
    so4ActionLinear (g * h) = so4ActionLinear g * so4ActionLinear h := by
  apply LinearMap.ext
  intro x
  simpa only [Module.End.mul_apply, so4ActionLinear_apply] using so4Action_mul g h x

/-- The standard finite-dimensional action packages as a monoid homomorphism
into the endomorphism algebra of the Euclidean carrier. -/
def so4ActionLinearHom : SO4 →* Module.End ℝ Euclidean4 where
  toFun := so4ActionLinear
  map_one' := so4ActionLinear_one
  map_mul' := so4ActionLinear_mul

/-- The standard action preserves the dot product. -/
theorem so4_dotProduct_invariant (g : SO4) (x y : Fin 4 → ℝ) :
    (so4VecAction g x) ⬝ᵥ (so4VecAction g y) = x ⬝ᵥ y := by
  have hG : (g : Mat4) ∈ Matrix.orthogonalGroup (Fin 4) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp g.property).1
  have hmul : (g : Mat4).transpose * (g : Mat4) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin 4) (R := ℝ)).1 hG
  dsimp [so4VecAction]
  calc
    (g : Mat4).mulVec x ⬝ᵥ (g : Mat4).mulVec y =
        Matrix.vecMul ((g : Mat4).mulVec x) (g : Mat4) ⬝ᵥ y := by
      simpa using
        (Matrix.dotProduct_mulVec ((g : Mat4).mulVec x) (g : Mat4) y)
    _ = Matrix.vecMul x ((g : Mat4).transpose * (g : Mat4)) ⬝ᵥ y := by
      simpa using congrArg (fun z => z ⬝ᵥ y)
        (Matrix.vecMul_mulVec (A := (g : Mat4)) (B := (g : Mat4)) x)
    _ = Matrix.vecMul x 1 ⬝ᵥ y := by rw [hmul]
    _ = x ⬝ᵥ y := by simp [Matrix.vecMul_one]

theorem so4_innerProduct_invariant (g : SO4) (x y : Euclidean4) :
    @inner ℝ Euclidean4 _ (so4Action g x) (so4Action g y) =
      @inner ℝ Euclidean4 _ x y := by
  have h_inner (v w : Euclidean4) :
      @inner ℝ Euclidean4 _ v w =
        (EuclideanSpace.equiv (Fin 4) ℝ v) ⬝ᵥ
          (EuclideanSpace.equiv (Fin 4) ℝ w) := by
    simp [PiLp.inner_apply, dotProduct, EuclideanSpace.equiv, mul_comm]
  calc
    @inner ℝ Euclidean4 _ (so4Action g x) (so4Action g y) =
        (EuclideanSpace.equiv (Fin 4) ℝ (so4Action g x)) ⬝ᵥ
          (EuclideanSpace.equiv (Fin 4) ℝ (so4Action g y)) := h_inner _ _
    _ = (EuclideanSpace.equiv (Fin 4) ℝ x) ⬝ᵥ
          (EuclideanSpace.equiv (Fin 4) ℝ y) := by
      dsimp [so4Action]
      exact so4_dotProduct_invariant g _ _
    _ = @inner ℝ Euclidean4 _ x y := (h_inner x y).symm

noncomputable def so4ActionEquiv (g : SO4) : Euclidean4 ≃ₗ[ℝ] Euclidean4 :=
  LinearEquiv.ofLinear
    (so4ActionLinear g) (so4ActionLinear g⁻¹)
    (by
      apply LinearMap.ext (fun x => ?_)
      calc
        (so4ActionLinear g ∘ₗ so4ActionLinear g⁻¹) x =
            so4Action g (so4Action (g⁻¹) x) := by
              simp only [LinearMap.comp_apply, so4ActionLinear_apply]
        _ = so4Action (g * g⁻¹) x := (so4Action_mul g g⁻¹ x).symm
        _ = x := by simp)
    (by
      apply LinearMap.ext (fun x => ?_)
      calc
        (so4ActionLinear g⁻¹ ∘ₗ so4ActionLinear g) x =
            so4Action (g⁻¹) (so4Action g x) := by
              simp only [LinearMap.comp_apply, so4ActionLinear_apply]
        _ = so4Action (g⁻¹ * g) x := (so4Action_mul g⁻¹ g x).symm
        _ = x := by simp)

@[simp] theorem so4ActionEquiv_apply (g : SO4) (x : Euclidean4) :
    so4ActionEquiv g x = so4Action g x := rfl

@[simp] theorem so4ActionEquiv_symm_apply (g : SO4) (x : Euclidean4) :
    (so4ActionEquiv g).symm x = so4Action (g⁻¹) x := rfl

theorem so4Action_norm (g : SO4) (x : Euclidean4) :
    ‖so4Action g x‖ = ‖x‖ := by
  have hsq : ‖so4Action g x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    have h_inner (v : Euclidean4) : @inner ℝ Euclidean4 _ v v =
        (EuclideanSpace.equiv (Fin 4) ℝ v) ⬝ᵥ (EuclideanSpace.equiv (Fin 4) ℝ v) := by
      rw [PiLp.inner_apply]
      dsimp [dotProduct]
      rfl
    rw [h_inner, h_inner]
    dsimp [so4Action]
    exact so4_dotProduct_invariant g _ _
  have hpos1 : 0 ≤ ‖so4Action g x‖ := norm_nonneg _
  have hpos2 : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith

noncomputable def so4ActionIsometry (g : SO4) :
    Euclidean4 ≃ₗᵢ[ℝ] Euclidean4 where
  toLinearEquiv := so4ActionEquiv g
  norm_map' x := so4Action_norm g x

/-! The standard action packaged as a native representation by linear
equivalences. -/
noncomputable def so4StandardRepresentation :
    SO4 →* (Euclidean4 ≃ₗ[ℝ] Euclidean4) where
  toFun := so4ActionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp [so4ActionEquiv]
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro x
    simp [so4ActionEquiv, so4Action_mul]

@[simp] theorem so4StandardRepresentation_apply
    (g : SO4) (x : Euclidean4) :
    so4StandardRepresentation g x = so4Action g x := by
  rfl

/-! The same standard representation, now with its native isometric target. -/

noncomputable def so4StandardIsometryRepresentation :
    SO4 →* (Euclidean4 ≃ₗᵢ[ℝ] Euclidean4) where
  toFun := so4ActionIsometry
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    simp [so4ActionIsometry, so4ActionEquiv]
  map_mul' := by
    intro g h
    apply LinearIsometryEquiv.ext
    intro x
    simp [so4ActionIsometry, so4ActionEquiv, so4Action_mul]

@[simp] theorem so4StandardIsometryRepresentation_apply
    (g : SO4) (x : Euclidean4) :
    so4StandardIsometryRepresentation g x = so4Action g x := by
  rfl

end InfoGeometry.Canonical.SO4StandardRepresentationBridge
