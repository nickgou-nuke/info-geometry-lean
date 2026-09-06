import proofs.HestenesBivectorCarrier
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Complex self-dual and anti-self-dual bivectors

The complexification is `ℂ ⊗[ℝ] Bivector13`.  Hodge duality is extended
complex-linearly and its square is `-I`; the two standard polynomial
projectors therefore give the complementary `+i` and `-i` spectral sectors.
-/

noncomputable section
namespace HestenesBivectorSelfDuality

open HestenesBivectorCarrier

abbrev ComplexBivector := TensorProduct ℝ ℂ Bivector13

/-- Complex-linear extension of real bivector Hodge duality. -/
def complexHodgeStar : ComplexBivector →ₗ[ℂ] ComplexBivector :=
  hodgeBivector.baseChange ℂ

@[simp] theorem complexHodgeStar_tmul (z : ℂ) (B : Bivector) :
    complexHodgeStar (z ⊗ₜ[ℝ] B) = z ⊗ₜ[ℝ] hodgeBivector B := rfl

theorem complexHodgeStar_sq_apply (F : ComplexBivector) :
    complexHodgeStar (complexHodgeStar F) = -F := by
  induction F using TensorProduct.induction_on with
  | zero => simp
  | tmul z B =>
      rw [complexHodgeStar_tmul, complexHodgeStar_tmul,
        hodge_sq_bivector, TensorProduct.tmul_neg]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      module

theorem complexHodgeStar_sq :
    complexHodgeStar.comp complexHodgeStar =
      -(LinearMap.id : ComplexBivector →ₗ[ℂ] ComplexBivector) := by
  apply LinearMap.ext
  intro F
  exact complexHodgeStar_sq_apply F

def selfDualProj : ComplexBivector →ₗ[ℂ] ComplexBivector :=
  (2 : ℂ)⁻¹ •
    ((LinearMap.id : ComplexBivector →ₗ[ℂ] ComplexBivector) -
      Complex.I • complexHodgeStar)

def antiSelfDualProj : ComplexBivector →ₗ[ℂ] ComplexBivector :=
  (2 : ℂ)⁻¹ •
    ((LinearMap.id : ComplexBivector →ₗ[ℂ] ComplexBivector) +
      Complex.I • complexHodgeStar)

theorem selfDualProj_apply (F : ComplexBivector) :
    selfDualProj F = (2 : ℂ)⁻¹ • (F - Complex.I • complexHodgeStar F) := rfl

theorem antiSelfDualProj_apply (F : ComplexBivector) :
    antiSelfDualProj F = (2 : ℂ)⁻¹ • (F + Complex.I • complexHodgeStar F) := rfl

@[simp] theorem selfDualProj_idempotent_apply (F : ComplexBivector) :
    selfDualProj (selfDualProj F) = selfDualProj F := by
  rw [selfDualProj_apply, selfDualProj_apply, map_smul, map_sub,
    LinearMap.map_smul]
  rw [complexHodgeStar_sq_apply]
  match_scalars <;> (ring_nf <;> try norm_num [Complex.I_sq])

theorem selfDualProj_idempotent :
    selfDualProj.comp selfDualProj = selfDualProj := by
  apply LinearMap.ext
  intro F
  exact selfDualProj_idempotent_apply F

@[simp] theorem antiSelfDualProj_idempotent_apply (F : ComplexBivector) :
    antiSelfDualProj (antiSelfDualProj F) = antiSelfDualProj F := by
  rw [antiSelfDualProj_apply, antiSelfDualProj_apply, map_smul, map_add,
    LinearMap.map_smul]
  rw [complexHodgeStar_sq_apply]
  match_scalars <;> (ring_nf <;> try norm_num [Complex.I_sq])

theorem antiSelfDualProj_idempotent :
    antiSelfDualProj.comp antiSelfDualProj = antiSelfDualProj := by
  apply LinearMap.ext
  intro F
  exact antiSelfDualProj_idempotent_apply F

@[simp] theorem projectors_add_apply (F : ComplexBivector) :
    selfDualProj F + antiSelfDualProj F = F := by
  rw [selfDualProj_apply, antiSelfDualProj_apply]
  module

theorem projectors_add_eq_id :
    selfDualProj + antiSelfDualProj =
      (LinearMap.id : ComplexBivector →ₗ[ℂ] ComplexBivector) := by
  apply LinearMap.ext
  intro F
  exact projectors_add_apply F

@[simp] theorem selfDual_antiSelfDual_zero_apply (F : ComplexBivector) :
    selfDualProj (antiSelfDualProj F) = 0 := by
  rw [antiSelfDualProj_apply, selfDualProj_apply, map_smul, map_add,
    LinearMap.map_smul]
  rw [complexHodgeStar_sq_apply]
  match_scalars <;> (ring_nf <;> try norm_num [Complex.I_sq])

@[simp] theorem antiSelfDual_selfDual_zero_apply (F : ComplexBivector) :
    antiSelfDualProj (selfDualProj F) = 0 := by
  rw [selfDualProj_apply, antiSelfDualProj_apply, map_smul, map_sub,
    LinearMap.map_smul]
  rw [complexHodgeStar_sq_apply]
  match_scalars <;> (ring_nf <;> try norm_num [Complex.I_sq])

theorem projectors_comp_zero :
    selfDualProj.comp antiSelfDualProj = 0 ∧
      antiSelfDualProj.comp selfDualProj = 0 := by
  constructor
  · apply LinearMap.ext
    intro F
    exact selfDual_antiSelfDual_zero_apply F
  · apply LinearMap.ext
    intro F
    exact antiSelfDual_selfDual_zero_apply F

@[simp] theorem star_on_selfDual (F : ComplexBivector) :
    complexHodgeStar (selfDualProj F) = Complex.I • selfDualProj F := by
  rw [selfDualProj_apply, map_smul, map_sub, LinearMap.map_smul,
    complexHodgeStar_sq_apply]
  match_scalars <;> (ring_nf <;> try norm_num [Complex.I_sq])

@[simp] theorem star_on_antiSelfDual (F : ComplexBivector) :
    complexHodgeStar (antiSelfDualProj F) =
      -Complex.I • antiSelfDualProj F := by
  rw [antiSelfDualProj_apply, map_smul, map_add, LinearMap.map_smul,
    complexHodgeStar_sq_apply]
  match_scalars <;> (ring_nf <;> try norm_num [Complex.I_sq])

/-- Complementary spectral coordinates in the two projector ranges. -/
def complexBivectorSpectralEquiv :
    ComplexBivector ≃ₗ[ℂ] selfDualProj.range × antiSelfDualProj.range where
  toFun F :=
    (⟨selfDualProj F, LinearMap.mem_range_self _ F⟩,
      ⟨antiSelfDualProj F, LinearMap.mem_range_self _ F⟩)
  invFun p := p.1.1 + p.2.1
  left_inv F := projectors_add_apply F
  right_inv p := by
    rcases p with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨x0, rfl⟩ := hx
    obtain ⟨y0, rfl⟩ := hy
    apply Prod.ext <;> apply Subtype.ext
    · simp [map_add]
    · simp [map_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_smul' c x := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [map_smul]

theorem bivector_spectral_packet :
    complexHodgeStar.comp complexHodgeStar = -LinearMap.id ∧
    selfDualProj.comp selfDualProj = selfDualProj ∧
    antiSelfDualProj.comp antiSelfDualProj = antiSelfDualProj ∧
    selfDualProj + antiSelfDualProj = LinearMap.id :=
  ⟨complexHodgeStar_sq, selfDualProj_idempotent,
    antiSelfDualProj_idempotent, projectors_add_eq_id⟩

end HestenesBivectorSelfDuality
end noncomputable section
