import InfoGeometry.Canonical.FilteredIsometricInnerProductColimit

/-!
# Inner product on a filtered isometric module direct limit

This file descends the common-stage inner pairing of a coherent isometric
system through both arguments of Mathlib's genuine `Module.DirectLimit`.
The resulting map is complex-valued and real-bilinear.  Compatible complex
scalar multiplication is then descended to the same carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (E : I → Type u)
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℂ (E i)]
variable (sys : IsometricDirectSystem E)

local notation "D∞" => RealDirectLimit E sys

/-- Additivity of the common-stage inner pairing in its first argument. -/
theorem commonStageInner_add_left
    (i j : I) (x₁ x₂ : E i) (y : E j) :
    commonStageInner E sys i j (x₁ + x₂) y =
      commonStageInner E sys i j x₁ y +
        commonStageInner E sys i j x₂ y := by
  unfold commonStageInner
  simp only [map_add, inner_add_left]

/-- Real homogeneity in the first argument. -/
theorem commonStageInner_smul_left_real
    (i j : I) (r : ℝ) (x : E i) (y : E j) :
    commonStageInner E sys i j (r • x) y =
      r • commonStageInner E sys i j x y := by
  unfold commonStageInner
  have h :=
    (sys.map
      (le_commonUpper_left i j)).toLinearMap.map_smul_of_tower r x
  change
    inner ℂ
        ((sys.map
          (le_commonUpper_left i j)).toLinearMap (r • x))
        (sys.map (le_commonUpper_right i j) y) =
      r •
        inner ℂ
          (sys.map (le_commonUpper_left i j) x)
          (sys.map (le_commonUpper_right i j) y)
  rw [h]
  change
    inner ℂ
        ((r : ℂ) •
          (sys.map
            (le_commonUpper_left i j)).toLinearMap x)
        (sys.map (le_commonUpper_right i j) y) =
      (r : ℂ) *
        inner ℂ
          (sys.map (le_commonUpper_left i j) x)
          (sys.map (le_commonUpper_right i j) y)
  rw [inner_smul_left]
  simp

/-- Additivity in the second argument. -/
theorem commonStageInner_add_right
    (i j : I) (x : E i) (y₁ y₂ : E j) :
    commonStageInner E sys i j x (y₁ + y₂) =
      commonStageInner E sys i j x y₁ +
        commonStageInner E sys i j x y₂ := by
  unfold commonStageInner
  simp only [map_add, inner_add_right]

/-- Real homogeneity in the second argument. -/
theorem commonStageInner_smul_right_real
    (i j : I) (r : ℝ) (x : E i) (y : E j) :
    commonStageInner E sys i j x (r • y) =
      r • commonStageInner E sys i j x y := by
  unfold commonStageInner
  have h :=
    (sys.map
      (le_commonUpper_right i j)).toLinearMap.map_smul_of_tower r y
  change
    inner ℂ
        (sys.map (le_commonUpper_left i j) x)
        ((sys.map
          (le_commonUpper_right i j)).toLinearMap (r • y)) =
      r •
        inner ℂ
          (sys.map (le_commonUpper_left i j) x)
          (sys.map (le_commonUpper_right i j) y)
  rw [h]
  change
    inner ℂ
        (sys.map (le_commonUpper_left i j) x)
        ((r : ℂ) •
          (sys.map
            (le_commonUpper_right i j)).toLinearMap y) =
      (r : ℂ) *
        inner ℂ
          (sys.map (le_commonUpper_left i j) x)
          (sys.map (le_commonUpper_right i j) y)
  rw [inner_smul_right]
  rfl

/-- For a fixed first representative, pairing against a later stage is
real-linear. -/
def pairingRightAtStage
    (i : I) (x : E i) (j : I) :
    E j →ₗ[ℝ] ℂ where
  toFun := commonStageInner E sys i j x
  map_add' := commonStageInner_add_right E sys i j x
  map_smul' := by
    intro r y
    exact commonStageInner_smul_right_real
      E sys i j r x y

/-- These stage functionals form a cocone in the second variable. -/
theorem pairingRightAtStage_compatible
    (i : I) (x : E i)
    (j k : I) (hjk : j ≤ k) (y : E j) :
    pairingRightAtStage E sys i x k
        (realTransition E sys hjk y) =
      pairingRightAtStage E sys i x j y := by
  exact commonStageInner_map_right E sys i j k hjk x y

/-- Pair one stage representative against the real module direct limit. -/
def pairStageAgainstDirectLimit
    (i : I) (x : E i) :
    D∞ →ₗ[ℝ] ℂ :=
  Module.DirectLimit.lift
    ℝ I E
    (fun _ _ hij => realTransition E sys hij)
    (pairingRightAtStage E sys i x)
    (pairingRightAtStage_compatible E sys i x)

@[simp] theorem pairStageAgainstDirectLimit_of
    (i j : I) (x : E i) (y : E j) :
    pairStageAgainstDirectLimit E sys i x
        (Module.DirectLimit.of
          ℝ I E
          (fun _ _ h => realTransition E sys h)
          j y) =
      commonStageInner E sys i j x y := by
  simpa only [pairingRightAtStage] using
    (Module.DirectLimit.lift_of
      (g := pairingRightAtStage E sys i x)
      (pairingRightAtStage_compatible E sys i x)
      (i := j) y)

/-- One first-stage representative determines a real-linear functional on the
direct limit. -/
def stageToDirectLimitFunctional
    (i : I) :
    E i →ₗ[ℝ] (D∞ →ₗ[ℝ] ℂ) where
  toFun := pairStageAgainstDirectLimit E sys i
  map_add' := by
    intro x₁ x₂
    apply LinearMap.ext
    intro z
    induction z using Module.DirectLimit.induction_on with
    | ih j y =>
        simp only [pairStageAgainstDirectLimit_of,
          LinearMap.add_apply]
        exact commonStageInner_add_left
          E sys i j x₁ x₂ y
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro z
    induction z using Module.DirectLimit.induction_on with
    | ih j y =>
        simp only [pairStageAgainstDirectLimit_of,
          LinearMap.smul_apply]
        exact commonStageInner_smul_left_real
          E sys i j r x y

/-- The first-stage functionals form a cocone in the first variable. -/
theorem stageToDirectLimitFunctional_compatible
    (i j : I) (hij : i ≤ j) (x : E i) :
    stageToDirectLimitFunctional E sys j
        (realTransition E sys hij x) =
      stageToDirectLimitFunctional E sys i x := by
  apply LinearMap.ext
  intro z
  induction z using Module.DirectLimit.induction_on with
  | ih k y =>
      change
        pairStageAgainstDirectLimit E sys j
            (sys.map hij x)
            (Module.DirectLimit.of
              ℝ I E
              (fun _ _ h => realTransition E sys h)
              k y) =
          pairStageAgainstDirectLimit E sys i x
            (Module.DirectLimit.of
              ℝ I E
              (fun _ _ h => realTransition E sys h)
              k y)
      rw [pairStageAgainstDirectLimit_of,
        pairStageAgainstDirectLimit_of]
      exact commonStageInner_map_left
        E sys i j k hij x y

/-- Full complex-valued real-bilinear pairing on the algebraic direct limit. -/
def realDirectLimitInner :
    D∞ →ₗ[ℝ] D∞ →ₗ[ℝ] ℂ :=
  Module.DirectLimit.lift
    ℝ I E
    (fun _ _ hij => realTransition E sys hij)
    (stageToDirectLimitFunctional E sys)
    (stageToDirectLimitFunctional_compatible E sys)

@[simp] theorem realDirectLimitInner_of_of
    (i j : I) (x : E i) (y : E j) :
    realDirectLimitInner E sys
        (Module.DirectLimit.of
          ℝ I E
          (fun _ _ h => realTransition E sys h)
          i x)
        (Module.DirectLimit.of
          ℝ I E
          (fun _ _ h => realTransition E sys h)
          j y) =
      commonStageInner E sys i j x y := by
  change
    (Module.DirectLimit.lift
      ℝ I E
      (fun _ _ h => realTransition E sys h)
      (stageToDirectLimitFunctional E sys)
      (stageToDirectLimitFunctional_compatible E sys))
      (Module.DirectLimit.of
        ℝ I E
        (fun _ _ h => realTransition E sys h)
        i x)
      (Module.DirectLimit.of
        ℝ I E
        (fun _ _ h => realTransition E sys h)
        j y) =
      commonStageInner E sys i j x y
  rw [Module.DirectLimit.lift_of]
  exact pairStageAgainstDirectLimit_of
    E sys i j x y

/-- Complex multiplication on one stage, considered as a real-linear map. -/
def stageComplexScalarMap
    (c : ℂ) (i : I) :
    E i →ₗ[ℝ] E i where
  toFun := fun x => c • x
  map_add' := smul_add c
  map_smul' := by
    intro r x
    change c • ((r : ℂ) • x) = (r : ℂ) • (c • x)
    simp only [smul_smul]
    rw [mul_comm]

/-- Scalar-multiplied canonical stage inclusion. -/
def complexScalarCoconeMap
    (c : ℂ) (i : I) :
    E i →ₗ[ℝ] D∞ :=
  (Module.DirectLimit.of
    ℝ I E
    (fun _ _ h => realTransition E sys h)
    i).comp (stageComplexScalarMap E c i)

/-- Compatibility of scalar-multiplied stage inclusions. -/
theorem complexScalarCoconeMap_compatible
    (c : ℂ) (i j : I) (hij : i ≤ j) (x : E i) :
    complexScalarCoconeMap E sys c j
        (realTransition E sys hij x) =
      complexScalarCoconeMap E sys c i x := by
  change
    Module.DirectLimit.of
        ℝ I E
        (fun _ _ h => realTransition E sys h)
        j (c • sys.map hij x) =
      Module.DirectLimit.of
        ℝ I E
        (fun _ _ h => realTransition E sys h)
        i (c • x)
  rw [← (sys.map hij).map_smul c x]
  exact Module.DirectLimit.of_f

/-- Complex scalar multiplication descended to the real direct-limit
carrier. -/
def complexScalarDirectLimit
    (c : ℂ) :
    D∞ →ₗ[ℝ] D∞ :=
  Module.DirectLimit.lift
    ℝ I E
    (fun _ _ h => realTransition E sys h)
    (complexScalarCoconeMap E sys c)
    (complexScalarCoconeMap_compatible E sys c)

@[simp] theorem complexScalarDirectLimit_of
    (c : ℂ) (i : I) (x : E i) :
    complexScalarDirectLimit E sys c
        (Module.DirectLimit.of
          ℝ I E
          (fun _ _ h => realTransition E sys h)
          i x) =
      Module.DirectLimit.of
        ℝ I E
        (fun _ _ h => realTransition E sys h)
        i (c • x) := by
  simpa only [complexScalarCoconeMap,
    stageComplexScalarMap] using
    (Module.DirectLimit.lift_of
      (g := complexScalarCoconeMap E sys c)
      (complexScalarCoconeMap_compatible E sys c)
      (i := i) x)

end InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit
