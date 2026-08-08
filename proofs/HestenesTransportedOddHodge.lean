import proofs.HestenesDistinctHodge

/-!
# The transported odd Hodge product structure

This owner keeps the real involution transported from the odd Clifford sector
separate from intrinsic even Hodge duality.  It proves that transported Hodge
exchanges the Hestenes self-adjoint and skew-adjoint real sectors.
-/

noncomputable section
namespace HestenesTransportedOddHodge

open HestenesCl14 HestenesCliffordCenter HestenesHermitianAdjoint
open HestenesHodgeEvenTransport HestenesDistinctHodge
open HestenesBivectorCarrier

abbrev Algebra := Cl14
abbrev EvenPart := CliffordAlgebra.evenOdd Q14 0

private theorem neg_smul_neg (x : ClPlus14) :
    (-1 : ℝ) • ((-1 : ℝ) • x) = x := by
  rw [smul_smul]
  norm_num

@[simp] theorem hestenesAdjoint_neg (x : ClPlus14) :
    hestenesAdjoint (-x) = -hestenesAdjoint x := by
  simpa only [neg_one_smul] using hestenesAdjoint_smul (-1 : ℝ) x

theorem neg_neg_mul_left (a b : ClPlus14) : -((-a) * b) = a * b := by
  change (-1 : ℝ) • (((-1 : ℝ) • a) * b) = a * b
  rw [smul_mul_assoc]
  module

/-- The adjoint of transported Hodge is `Ω₄ y`. -/
theorem hestenesAdjoint_paravectorHodge (y : EvenPart) :
    hestenesAdjoint (asEvenAlgebra (paravectorHodge y)) =
      asEvenAlgebra spacetimePseudoscalar * asEvenAlgebra y := by
  have hp : asEvenAlgebra (paravectorHodge y) =
      -(hestenesAdjoint (asEvenAlgebra y) *
        asEvenAlgebra spacetimePseudoscalar) := by
    apply Subtype.ext
    simpa [asEvenAlgebra] using paravectorHodge_val y
  rw [hp, hestenesAdjoint_neg, hestenesAdjoint_mul,
    hestenesAdjoint_involutive,
    HestenesDistinctHodge.hestenesAdjoint_spacetimePseudoscalar]
  exact neg_neg_mul_left (asEvenAlgebra spacetimePseudoscalar) (asEvenAlgebra y)

theorem omega_comm_asEvenAlgebra (y : EvenPart) :
    asEvenAlgebra spacetimePseudoscalar * asEvenAlgebra y =
      asEvenAlgebra y * asEvenAlgebra spacetimePseudoscalar := by
  apply Subtype.ext
  exact spacetimePseudoscalar_comm_even y.property

theorem paravectorHodge_eq_evenHodge (y : EvenPart) :
    paravectorHodge y = evenHodge y := by
  apply Subtype.ext
  rw [paravectorHodge_val, evenHodge_val]

def selfAdjointEven : Submodule ℝ EvenPart where
  carrier := {y | hestenesAdjoint (asEvenAlgebra y) = asEvenAlgebra y}
  zero_mem' := by
    change hestenesAdjoint (asEvenAlgebra 0) = asEvenAlgebra 0
    apply Subtype.ext
    simp [asEvenAlgebra, hestenesAdjoint, HestenesKreinMatrixBridge.reverseEven]
  add_mem' := by
    intro x y hx hy
    simpa using congrArg₂ (· + ·) hx hy
  smul_mem' := by
    intro r x hx
    simpa using congrArg (r • ·) hx

def skewAdjointEven : Submodule ℝ EvenPart where
  carrier := {y | hestenesAdjoint (asEvenAlgebra y) = -asEvenAlgebra y}
  zero_mem' := by
    change hestenesAdjoint (asEvenAlgebra 0) = -asEvenAlgebra 0
    apply Subtype.ext
    simp [asEvenAlgebra, hestenesAdjoint, HestenesKreinMatrixBridge.reverseEven]
  add_mem' := by
    intro x y hx hy
    change hestenesAdjoint (asEvenAlgebra (x + y)) = -asEvenAlgebra (x + y)
    rw [asEvenAlgebra_add, hestenesAdjoint_add, hx, hy]
    module
  smul_mem' := by
    intro r x hx
    change hestenesAdjoint (asEvenAlgebra (r • x)) = -asEvenAlgebra (r • x)
    rw [asEvenAlgebra_smul, hestenesAdjoint_smul, hx]
    module

theorem paravectorHodge_selfAdjoint_to_skew
    {y : EvenPart} (hy : y ∈ selfAdjointEven) :
    paravectorHodge y ∈ skewAdjointEven := by
  change hestenesAdjoint (asEvenAlgebra (paravectorHodge y)) =
    -asEvenAlgebra (paravectorHodge y)
  have hp : asEvenAlgebra (paravectorHodge y) =
      -(hestenesAdjoint (asEvenAlgebra y) *
        asEvenAlgebra spacetimePseudoscalar) := by
    apply Subtype.ext
    simpa [asEvenAlgebra] using paravectorHodge_val y
  rw [hestenesAdjoint_paravectorHodge, hp, hy]
  rw [omega_comm_asEvenAlgebra]
  simpa only [neg_neg] using
    neg_neg_mul_left (asEvenAlgebra y)
      (asEvenAlgebra spacetimePseudoscalar)

theorem paravectorHodge_skew_to_selfAdjoint
    {y : EvenPart} (hy : y ∈ skewAdjointEven) :
    paravectorHodge y ∈ selfAdjointEven := by
  change hestenesAdjoint (asEvenAlgebra (paravectorHodge y)) =
    asEvenAlgebra (paravectorHodge y)
  have hp : asEvenAlgebra (paravectorHodge y) =
      -(hestenesAdjoint (asEvenAlgebra y) *
        asEvenAlgebra spacetimePseudoscalar) := by
    apply Subtype.ext
    simpa [asEvenAlgebra] using paravectorHodge_val y
  rw [hestenesAdjoint_paravectorHodge, hp, hy]
  rw [omega_comm_asEvenAlgebra]
  exact (neg_neg_mul_left (asEvenAlgebra y)
    (asEvenAlgebra spacetimePseudoscalar)).symm

def paravectorHodgeLinear : EvenPart →ₗ[ℝ] EvenPart := evenHodgeLinear

@[simp] theorem paravectorHodgeLinear_apply (y : EvenPart) :
    paravectorHodgeLinear y = paravectorHodge y :=
  (paravectorHodge_eq_evenHodge y).symm

theorem paravectorHodgeLinear_sq :
    paravectorHodgeLinear.comp paravectorHodgeLinear = LinearMap.id := by
  apply LinearMap.ext
  intro y
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    paravectorHodgeLinear_apply] using paravectorHodge_sq y

@[simp] theorem paravectorHodgeLinear_sq_apply (y : EvenPart) :
    paravectorHodgeLinear (paravectorHodgeLinear y) = y := by
  simpa only [paravectorHodgeLinear_apply] using paravectorHodge_sq y

def selfAdjointSkewAdjointEquiv :
    selfAdjointEven ≃ₗ[ℝ] skewAdjointEven where
  toFun y := ⟨paravectorHodge y, paravectorHodge_selfAdjoint_to_skew y.property⟩
  invFun y := ⟨paravectorHodge y, paravectorHodge_skew_to_selfAdjoint y.property⟩
  left_inv y := by apply Subtype.ext; exact paravectorHodge_sq y
  right_inv y := by apply Subtype.ext; exact paravectorHodge_sq y
  map_add' x y := by
    apply Subtype.ext
    simpa only [Submodule.coe_add, paravectorHodgeLinear_apply] using
      paravectorHodgeLinear.map_add (x : EvenPart) (y : EvenPart)
  map_smul' r x := by
    apply Subtype.ext
    simpa only [Submodule.coe_smul, paravectorHodgeLinear_apply] using
      paravectorHodgeLinear.map_smul r (x : EvenPart)

def productProjPlus : EvenPart →ₗ[ℝ] EvenPart :=
  (2 : ℝ)⁻¹ • (LinearMap.id + paravectorHodgeLinear)

def productProjMinus : EvenPart →ₗ[ℝ] EvenPart :=
  (2 : ℝ)⁻¹ • (LinearMap.id - paravectorHodgeLinear)

@[simp] theorem productProjPlus_idempotent_apply (y : EvenPart) :
    productProjPlus (productProjPlus y) = productProjPlus y := by
  simp only [productProjPlus, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply, map_smul, map_add, paravectorHodgeLinear_apply,
    paravectorHodge_sq]
  module

@[simp] theorem productProjMinus_idempotent_apply (y : EvenPart) :
    productProjMinus (productProjMinus y) = productProjMinus y := by
  simp only [productProjMinus, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, map_smul, map_sub, paravectorHodgeLinear_apply,
    paravectorHodge_sq]
  module

@[simp] theorem productProjectors_add_apply (y : EvenPart) :
    productProjPlus y + productProjMinus y = y := by
  simp [productProjPlus, productProjMinus]
  module

@[simp] theorem productProjectors_cross_zero (y : EvenPart) :
    productProjPlus (productProjMinus y) = 0 ∧
      productProjMinus (productProjPlus y) = 0 := by
  constructor
  · simp only [productProjPlus, productProjMinus, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_smul, map_sub, paravectorHodgeLinear_sq_apply]
    module
  · simp only [productProjPlus, productProjMinus, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_smul, map_add, paravectorHodgeLinear_sq_apply]
    module

theorem transported_hodge_packet :
    paravectorHodgeLinear.comp paravectorHodgeLinear = LinearMap.id ∧
      (∀ y : selfAdjointEven,
        paravectorHodge y ∈ skewAdjointEven) ∧
      (∀ y : skewAdjointEven,
        paravectorHodge y ∈ selfAdjointEven) :=
  ⟨paravectorHodgeLinear_sq,
    fun y => paravectorHodge_selfAdjoint_to_skew y.property,
    fun y => paravectorHodge_skew_to_selfAdjoint y.property⟩

end HestenesTransportedOddHodge
end noncomputable section
