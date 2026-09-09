import proofs.HestenesTransportedOddHodge
import InfoGeometry.Canonical.HestenesEvenPauliEquiv

/-!
# Balanced eigenspaces of transported Hodge

The Hestenes adjoint anticommutes with the transported real Hodge involution.
It therefore exchanges the two product-projector ranges.  Together with the
eight-dimensional even carrier this proves that both eigenspaces have real
dimension four.
-/

noncomputable section
namespace HestenesParaComplexFinrank

open HestenesCl14 HestenesHermitianAdjoint HestenesHodgeEvenTransport
open HestenesTransportedOddHodge HestenesEvenPauliEquiv
open HestenesHodgeParityBridge
open HestenesDistinctHodge
open HestenesCliffordCenter

attribute [local instance high] Module.Free.of_divisionRing

abbrev EvenPart := CliffordAlgebra.evenOdd Q14 0

def adjointEven (y : EvenPart) : EvenPart :=
  ⟨hestenesAdjoint (asEvenAlgebra y),
    (hestenesAdjoint (asEvenAlgebra y)).property⟩

@[simp] theorem adjointEven_add (x y : EvenPart) :
    adjointEven (x + y) = adjointEven x + adjointEven y := by
  apply Subtype.ext
  exact congrArg Subtype.val (hestenesAdjoint_add (asEvenAlgebra x) (asEvenAlgebra y))

@[simp] theorem adjointEven_smul (r : ℝ) (x : EvenPart) :
    adjointEven (r • x) = r • adjointEven x := by
  apply Subtype.ext
  exact congrArg Subtype.val (hestenesAdjoint_smul r (asEvenAlgebra x))

@[simp] theorem adjointEven_sub (x y : EvenPart) :
    adjointEven (x - y) = adjointEven x - adjointEven y := by
  rw [sub_eq_add_neg, adjointEven_add]
  have hn : adjointEven (-y) = -adjointEven y := by
    simpa only [neg_one_smul] using adjointEven_smul (-1 : ℝ) y
  rw [hn]
  simp only [sub_eq_add_neg]

@[simp] theorem adjointEven_involutive (x : EvenPart) :
    adjointEven (adjointEven x) = x := by
  apply Subtype.ext
  exact congrArg Subtype.val (hestenesAdjoint_involutive (asEvenAlgebra x))

def adjointEvenLinear : EvenPart →ₗ[ℝ] EvenPart where
  toFun := adjointEven
  map_add' := adjointEven_add
  map_smul' := adjointEven_smul

theorem adjointEven_anticomm_hodge (y : EvenPart) :
    adjointEven (paravectorHodge y) = -paravectorHodge (adjointEven y) := by
  apply Subtype.ext
  change ((hestenesAdjoint (asEvenAlgebra (paravectorHodge y)) : ClPlus14) : Cl14) =
    -((paravectorHodge (adjointEven y) : EvenPart) : Cl14)
  rw [hestenesAdjoint_paravectorHodge, paravectorHodge_val]
  rw [omega_comm_asEvenAlgebra]
  change ((asEvenAlgebra y : ClPlus14) : Cl14) * spacetimePseudoscalar =
    -(-((hestenesAdjoint (hestenesAdjoint (asEvenAlgebra y)) : ClPlus14) : Cl14) *
      spacetimePseudoscalar)
  rw [hestenesAdjoint_involutive]
  exact congrArg Subtype.val <|
    (neg_neg_mul_left (asEvenAlgebra y)
      (asEvenAlgebra spacetimePseudoscalar)).symm

theorem adjointEven_productProjPlus (y : EvenPart) :
    adjointEven (productProjPlus y) = productProjMinus (adjointEven y) := by
  simp only [productProjPlus, productProjMinus, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    adjointEven_smul, adjointEven_add]
  rw [show adjointEven (paravectorHodgeLinear y) =
      -paravectorHodgeLinear (adjointEven y) by
    simpa only [paravectorHodgeLinear_apply] using adjointEven_anticomm_hodge y]
  module

theorem adjointEven_productProjMinus (y : EvenPart) :
    adjointEven (productProjMinus y) = productProjPlus (adjointEven y) := by
  simp only [productProjPlus, productProjMinus, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    adjointEven_smul, adjointEven_sub]
  rw [show adjointEven (paravectorHodgeLinear y) =
      -paravectorHodgeLinear (adjointEven y) by
    simpa only [paravectorHodgeLinear_apply] using adjointEven_anticomm_hodge y]
  module

def productRangeSwap : productProjPlus.range ≃ₗ[ℝ] productProjMinus.range where
  toFun x := ⟨adjointEven x, by
    rcases x with ⟨x, ⟨y, hy⟩⟩
    refine ⟨adjointEven y, ?_⟩
    calc
      productProjMinus (adjointEven y) = adjointEven (productProjPlus y) :=
        (adjointEven_productProjPlus y).symm
      _ = adjointEven x := by rw [hy]⟩
  invFun x := ⟨adjointEven x, by
    rcases x with ⟨x, ⟨y, hy⟩⟩
    refine ⟨adjointEven y, ?_⟩
    calc
      productProjPlus (adjointEven y) = adjointEven (productProjMinus y) :=
        (adjointEven_productProjMinus y).symm
      _ = adjointEven x := by rw [hy]⟩
  left_inv x := by apply Subtype.ext; exact adjointEven_involutive x
  right_inv x := by apply Subtype.ext; exact adjointEven_involutive x
  map_add' x y := by apply Subtype.ext; exact adjointEven_add x y
  map_smul' r x := by apply Subtype.ext; exact adjointEven_smul r x

def productSpectralEquiv :
    EvenPart ≃ₗ[ℝ] productProjPlus.range × productProjMinus.range where
  toFun y :=
    (⟨productProjPlus y, LinearMap.mem_range_self _ y⟩,
      ⟨productProjMinus y, LinearMap.mem_range_self _ y⟩)
  invFun p := p.1.1 + p.2.1
  left_inv y := productProjectors_add_apply y
  right_inv p := by
    rcases p with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨x0, rfl⟩ := hx
    obtain ⟨y0, rfl⟩ := hy
    apply Prod.ext <;> apply Subtype.ext
    · simp [map_add]
    · simp [map_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_smul' r x := by
    apply Prod.ext <;> apply Subtype.ext <;> simp

theorem finrank_productProjPlus_range :
    Module.finrank ℝ productProjPlus.range = 4 := by
  letI : Module.Free ℝ productProjPlus.range :=
    Module.Free.of_divisionRing (K := ℝ) (V := productProjPlus.range)
  letI : Module.Free ℝ productProjMinus.range :=
    Module.Free.of_divisionRing (K := ℝ) (V := productProjMinus.range)
  have hsum : 8 = Module.finrank ℝ productProjPlus.range +
      Module.finrank ℝ productProjMinus.range := by
    rw [← clPlus14_finrank]
    rw [← Module.finrank_prod]
    exact LinearEquiv.finrank_eq productSpectralEquiv
  have heq : Module.finrank ℝ productProjPlus.range =
      Module.finrank ℝ productProjMinus.range :=
    LinearEquiv.finrank_eq productRangeSwap
  omega

theorem finrank_productProjMinus_range :
    Module.finrank ℝ productProjMinus.range = 4 := by
  letI : Module.Free ℝ productProjPlus.range :=
    Module.Free.of_divisionRing (K := ℝ) (V := productProjPlus.range)
  letI : Module.Free ℝ productProjMinus.range :=
    Module.Free.of_divisionRing (K := ℝ) (V := productProjMinus.range)
  rw [← LinearEquiv.finrank_eq productRangeSwap]
  exact finrank_productProjPlus_range

theorem paraComplex_finrank_packet :
    Module.finrank ℝ productProjPlus.range = 4 ∧
      Module.finrank ℝ productProjMinus.range = 4 :=
  ⟨finrank_productProjPlus_range, finrank_productProjMinus_range⟩

end HestenesParaComplexFinrank
end noncomputable section
