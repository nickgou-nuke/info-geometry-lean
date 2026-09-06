import InfoGeometry.Canonical.ChiralBoundarySheetReflectionTopological

/-!
# Finite cylinder functions on the chiral boundary

This owner realizes the finite diagonal stages `Fun(CausalWord n, ℝ)` and
their compatible lift to continuous functions on the symbolic boundary.  It
does not introduce a measure, Hilbert-space operators, or a Cuntz relation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCylinderFunctionStages

open InfoGeometry.Canonical.ChiralLightConeTensorTower
open InfoGeometry.Canonical.CantorCliffordFunctionModel

abbrev CylinderFunction (n : ℕ) := CausalWord n → ℝ

def truncateBoundary (n : ℕ) : ChiralBoundary → CausalWord n :=
  fun ξ i => ξ i.1

@[simp] theorem truncateBoundary_apply
    (n : ℕ) (ξ : ChiralBoundary) (i : Fin n) :
    truncateBoundary n ξ i = ξ i.1 := rfl

theorem continuous_truncateBoundary (n : ℕ) :
    Continuous (truncateBoundary n) := by
  apply continuous_pi
  intro i
  exact continuous_apply i.1

def liftCylinder {n : ℕ} (f : CylinderFunction n) :
    ContinuousBoundaryFunction ℝ where
  toFun ξ := f (truncateBoundary n ξ)
  continuous_toFun := by
    exact continuous_of_discreteTopology.comp
      (continuous_truncateBoundary n)

@[simp] theorem liftCylinder_apply
    {n : ℕ} (f : CylinderFunction n) (ξ : ChiralBoundary) :
    liftCylinder f ξ = f (truncateBoundary n ξ) := rfl

def cylinderStageEmbed (n : ℕ) :
    CylinderFunction n →ₐ[ℝ] CylinderFunction (n + 1) where
  toFun f w := f (fun i => w i.castSucc)
  map_one' := by
    rfl
  map_mul' f g := by
    rfl
  map_zero' := by
    rfl
  map_add' f g := by
    rfl
  commutes' r := by
    rfl

@[simp] theorem cylinderStageEmbed_apply
    (n : ℕ) (f : CylinderFunction n) (w : CausalWord (n + 1)) :
    cylinderStageEmbed n f w = f (fun i => w i.castSucc) := rfl

theorem cylinderStageEmbed_injective (n : ℕ) :
    Function.Injective (cylinderStageEmbed n) := by
  intro f g h
  funext w
  have hvalue := congrArg
    (fun F : CylinderFunction (n + 1) => F (Fin.snoc w ChiralArrow.plus)) h
  simpa [cylinderStageEmbed] using hvalue

def cylinderStageEmbedOfLe {n m : ℕ} (h : n ≤ m) :
    CylinderFunction n →ₐ[ℝ] CylinderFunction m where
  toFun f w := f (fun i => w ⟨i.1, lt_of_lt_of_le i.2 h⟩)
  map_one' := by rfl
  map_mul' f g := by rfl
  map_zero' := by rfl
  map_add' f g := by rfl
  commutes' r := by rfl

@[simp] theorem cylinderStageEmbedOfLe_apply
    {n m : ℕ} (h : n ≤ m) (f : CylinderFunction n)
    (w : CausalWord m) :
    cylinderStageEmbedOfLe h f w =
      f (fun i => w ⟨i.1, lt_of_lt_of_le i.2 h⟩) := rfl

theorem cylinderStageEmbedOfLe_refl
    (n : ℕ) (f : CylinderFunction n) :
    cylinderStageEmbedOfLe (le_refl n) f = f := by
  funext w
  rfl

theorem cylinderStageEmbedOfLe_comp
    {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k)
    (f : CylinderFunction n) :
    cylinderStageEmbedOfLe h₂ (cylinderStageEmbedOfLe h₁ f) =
      cylinderStageEmbedOfLe (h₁.trans h₂) f := by
  funext w
  rfl

theorem cylinderStageEmbedOfLe_injective
    {n m : ℕ} (h : n ≤ m) :
    Function.Injective (cylinderStageEmbedOfLe h) := by
  intro f g hfg
  funext w
  let w' : CausalWord m := fun i =>
    if hi : i.1 < n then w ⟨i.1, hi⟩ else ChiralArrow.plus
  have hvalue := congrArg
    (fun F : CylinderFunction m => F w') hfg
  have hrestrict :
      (fun i => w' ⟨i.1, lt_of_lt_of_le i.2 h⟩) = w := by
    funext i
    simp [w']
  simpa [cylinderStageEmbedOfLe, hrestrict] using hvalue

theorem liftCylinder_stageEmbedOfLe
    {n m : ℕ} (h : n ≤ m) (f : CylinderFunction n) :
    liftCylinder (cylinderStageEmbedOfLe h f) = liftCylinder f := by
  ext ξ
  change f (fun i => ξ i.1) = f (truncateBoundary n ξ)
  rfl

theorem liftCylinder_stageEmbed
    {n : ℕ} (f : CylinderFunction n) :
    liftCylinder (cylinderStageEmbed n f) = liftCylinder f := by
  ext ξ
  rfl

def mirrorCylinderFunction {n : ℕ} (f : CylinderFunction n) :
    CylinderFunction n :=
  fun w => f (mirrorCausalWord w)

@[simp] theorem mirrorCylinderFunction_apply
    {n : ℕ} (f : CylinderFunction n) (w : CausalWord n) :
    mirrorCylinderFunction f w = f (mirrorCausalWord w) := rfl

@[simp] theorem mirrorCylinderFunction_involutive
    {n : ℕ} (f : CylinderFunction n) :
    mirrorCylinderFunction (mirrorCylinderFunction f) = f := by
  funext w
  simp [mirrorCylinderFunction]

theorem mirrorCylinderFunction_mul
    {n : ℕ} (f g : CylinderFunction n) :
    mirrorCylinderFunction (f * g) =
      mirrorCylinderFunction f * mirrorCylinderFunction g := by
  funext w
  rfl

theorem mirrorCylinderFunction_add
    {n : ℕ} (f g : CylinderFunction n) :
    mirrorCylinderFunction (f + g) =
      mirrorCylinderFunction f + mirrorCylinderFunction g := by
  funext w
  rfl

theorem mirrorCylinderFunction_one
    (n : ℕ) :
    mirrorCylinderFunction (1 : CylinderFunction n) = 1 := by
  funext w
  rfl

theorem mirrorCylinderFunction_stageEmbed
    {n : ℕ} (f : CylinderFunction n) :
    mirrorCylinderFunction (cylinderStageEmbed n f) =
      cylinderStageEmbed n (mirrorCylinderFunction f) := by
  funext w
  change f (fun i => mirrorCausalWord w i.castSucc) =
    f (mirrorCausalWord (fun i => w i.castSucc))
  apply congrArg f
  funext i
  rfl

theorem boundaryMirrorPullback_liftCylinder
    {n : ℕ} (f : CylinderFunction n) :
    boundaryMirrorPullback (liftCylinder f) =
      liftCylinder (mirrorCylinderFunction f) := by
  ext ξ
  change f (truncateBoundary n (boundaryMirror ξ)) =
    f (mirrorCausalWord (truncateBoundary n ξ))
  apply congrArg f
  funext i
  rfl

def liftCylinderAlgHom (n : ℕ) :
    CylinderFunction n →ₐ[ℝ] ContinuousBoundaryFunction ℝ where
  toFun := liftCylinder
  map_one' := by
    ext ξ
    rfl
  map_mul' f g := by
    ext ξ
    rfl
  map_zero' := by
    ext ξ
    rfl
  map_add' f g := by
    ext ξ
    rfl
  commutes' r := by
    ext ξ
    rfl

@[simp] theorem liftCylinderAlgHom_apply
    {n : ℕ} (f : CylinderFunction n) :
    liftCylinderAlgHom n f = liftCylinder f := rfl

theorem liftCylinderAlgHom_injective (n : ℕ) :
    Function.Injective (liftCylinderAlgHom n) := by
  intro f g h
  funext w
  let ξ : ChiralBoundary :=
    prefixWordBoundary w (fun _ => ChiralArrow.plus)
  have hξ := congrArg
    (fun F : ContinuousBoundaryFunction ℝ => F ξ) h
  have htrunc : truncateBoundary n ξ = w := by
    funext i
    simp [ξ, truncateBoundary]
  simpa [liftCylinder, htrunc] using hξ

def cylinderCharacteristic {n : ℕ} (w : CausalWord n) :
    CylinderFunction n :=
  fun v => if v = w then 1 else 0

@[simp] theorem cylinderCharacteristic_sq
    {n : ℕ} (w : CausalWord n) :
    cylinderCharacteristic w * cylinderCharacteristic w =
      cylinderCharacteristic w := by
  funext v
  by_cases h : v = w <;> simp [cylinderCharacteristic, h]

theorem cylinderCharacteristic_mul_eq_zero
    {n : ℕ} {u v : CausalWord n} (h : u ≠ v) :
    cylinderCharacteristic u * cylinderCharacteristic v = 0 := by
  funext w
  by_cases hwu : w = u
  · subst w
    simp [cylinderCharacteristic, h]
  · by_cases hwv : w = v
    · subst w
      simp [cylinderCharacteristic, hwu]
    · simp [cylinderCharacteristic, hwu, hwv]

theorem sum_cylinderCharacteristic (n : ℕ) :
    ∑ w : CausalWord n, cylinderCharacteristic w = 1 := by
  classical
  funext v
  simp [cylinderCharacteristic]

theorem mirrorCylinderFunction_characteristic
    {n : ℕ} (w : CausalWord n) :
    mirrorCylinderFunction (cylinderCharacteristic w) =
      cylinderCharacteristic (mirrorCausalWord w) := by
  funext v
  have heq : mirrorCausalWord v = w ↔
      v = mirrorCausalWord w := by
    constructor
    · intro h
      have h' := congrArg mirrorCausalWord h
      simpa using h'
    · intro h
      have h' := congrArg mirrorCausalWord h
      simpa using h'
  simp [mirrorCylinderFunction, cylinderCharacteristic, heq]

def mirrorCylinderAlgEquiv (n : ℕ) :
    CylinderFunction n ≃ₐ[ℝ] CylinderFunction n where
  toFun := mirrorCylinderFunction
  invFun := mirrorCylinderFunction
  left_inv := mirrorCylinderFunction_involutive
  right_inv := mirrorCylinderFunction_involutive
  map_mul' f g := by
    funext w
    rfl
  map_add' f g := by
    funext w
    rfl
  commutes' r := by
    funext w
    rfl

@[simp] theorem mirrorCylinderAlgEquiv_apply
    {n : ℕ} (f : CylinderFunction n) :
    mirrorCylinderAlgEquiv n f = mirrorCylinderFunction f := rfl

end InfoGeometry.Canonical.CantorCylinderFunctionStages
