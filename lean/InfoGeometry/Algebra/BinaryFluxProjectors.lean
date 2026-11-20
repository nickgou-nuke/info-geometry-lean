/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteGroupFourier
import InfoGeometry.LLM.WalshCharacterGeometry
import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# Real projectors for binary electric flux

The binary flux group is `Multiplicative (ι → ZMod 2)`. Its real characters
come from the existing Walsh owner. Normalized character kernels are sent
through the existing representation transform, so the resulting projectors
live in an arbitrary real algebra, which need not be commutative.

Character orthogonality proves the kernel convolution law. The representation
transform then proves the projector product law; completeness, charge
eigenrelations, and ordered charge transport follow from finite sums.

For three binary components the normalization is `1 / 8`, as in the `N = 2`
specialization of 't Hooft's electric-sector projector (5.2), printed p. 148.
No nonzero occupation of every sector, Hilbert-space orthogonal projection,
Gibbs trace, path integral, or confinement statement is asserted here.
See `docs/BINARY_FLUX_DUALITY_CONTRACT.md` for the source and scope.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Algebra.BinaryFluxProjectors

open InfoGeometry.Algebra.FiniteGroupFourier
open InfoGeometry.Algebra.NoncommutativePlaneWaveKernel
open InfoGeometry.LLM.WalshCharacterGeometry

abbrev Flux (ι : Type*) := ι → ZMod 2

abbrev FluxGroup (ι : Type*) := Multiplicative (Flux ι)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Native real Walsh character, regarded as a multiplicative-group character. -/
def character (e : Flux ι) : FluxGroup ι →* ℝ :=
  (walshCharacter e).toMonoidHom

omit [DecidableEq ι] in
theorem character_apply (e : Flux ι) (g : FluxGroup ι) :
    character e g = walshCharacter e g.toAdd := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- In the binary flux group, inversion is the identity. -/
@[simp] theorem flux_inv_eq_self (g : FluxGroup ι) : g⁻¹ = g := by
  apply Multiplicative.toAdd.injective
  ext i
  exact ZMod.neg_eq_self_mod_two (g.toAdd i)

omit [DecidableEq ι] in
theorem character_add (e f : Flux ι) (g : FluxGroup ι) :
    character (e + f) g = character e g * character f g := by
  change walshCharacter (e + f) g.toAdd =
    walshCharacter e g.toAdd * walshCharacter f g.toAdd
  rw [walshCharacter_symmetric (e + f) g.toAdd,
    AddChar.map_add_eq_mul, walshCharacter_symmetric g.toAdd e,
    walshCharacter_symmetric g.toAdd f]

theorem character_orthogonality (e f : Flux ι) :
    (∑ g : FluxGroup ι, character e g * character f g) =
      if e = f then (Fintype.card (Flux ι) : ℝ) else 0 := by
  calc
    (∑ g : FluxGroup ι, character e g * character f g) =
        ∑ x : Flux ι, walshCharacter e x * walshCharacter f x := by
      simpa only [character_apply] using
        (Multiplicative.toAdd : FluxGroup ι ≃ Flux ι).sum_comp
          (fun x => walshCharacter e x * walshCharacter f x)
    _ = _ := walshCharacter_orthogonality e f

/-- Dual character orthogonality, including the identity flux. -/
theorem sum_character (g : FluxGroup ι) :
    (∑ e : Flux ι, character e g) =
      if g = 1 then (Fintype.card (Flux ι) : ℝ) else 0 := by
  calc
    (∑ e : Flux ι, character e g) =
        ∑ e : Flux ι,
          walshCharacter g.toAdd e * walshCharacter (0 : Flux ι) e := by
      apply Finset.sum_congr rfl
      intro e he
      have hzero : walshCharacter (0 : Flux ι) e = 1 := by simp
      rw [hzero, mul_one]
      exact walshCharacter_symmetric e g.toAdd
    _ = if g.toAdd = 0 then (Fintype.card (Flux ι) : ℝ) else 0 :=
      walshCharacter_orthogonality g.toAdd 0
    _ = _ := by
      have hiff : g.toAdd = 0 ↔ g = 1 := by
        constructor
        · exact fun h => Multiplicative.toAdd.injective h
        · intro h
          subst g
          rfl
      simp only [hiff]

private theorem flux_card_ne_zero : (Fintype.card (Flux ι) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- The normalized binary Fourier coefficient kernel. -/
def characterKernel (e : Flux ι) (g : FluxGroup ι) : ℝ :=
  (Fintype.card (Flux ι) : ℝ)⁻¹ * character e g

theorem characterKernel_mul (e : Flux ι) (g h : FluxGroup ι) :
    characterKernel e (g * h) = character e g * characterKernel e h := by
  unfold characterKernel
  rw [map_mul]
  ring

/-- Orthogonal idempotent kernels for the native ordered convolution. -/
theorem characterKernel_convolution (e f : Flux ι) :
    finiteConvolution (characterKernel e) (characterKernel f) =
      if e = f then characterKernel e else 0 := by
  classical
  funext g
  have hfactor :
      finiteConvolution (characterKernel e) (characterKernel f) g =
        ((Fintype.card (Flux ι) : ℝ)⁻¹ *
          (Fintype.card (Flux ι) : ℝ)⁻¹ * character f g) *
          (∑ h : FluxGroup ι, character e h * character f h) := by
    unfold finiteConvolution characterKernel
    simp_rw [map_mul, flux_inv_eq_self]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [hfactor, character_orthogonality]
  by_cases hef : e = f
  · subst f
    simp only [ite_true, characterKernel]
    field_simp [flux_card_ne_zero]
  · simp [hef]

theorem sum_characterKernel (g : FluxGroup ι) :
    (∑ e : Flux ι, characterKernel e g) = if g = 1 then 1 else 0 := by
  classical
  simp only [characterKernel]
  rw [← Finset.mul_sum, sum_character]
  by_cases hg : g = 1
  · simp [hg]
  · simp [hg]

section OperatorAlgebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The character projector is a representation transform, not assumed data. -/
def projector (ρ : FluxGroup ι →* A) (e : Flux ι) : A :=
  finiteRepresentationTransform ρ (characterKernel e)

theorem projector_apply (ρ : FluxGroup ι →* A) (e : Flux ι) :
    projector ρ e = ∑ g : FluxGroup ι, characterKernel e g • ρ g :=
  finiteRepresentationTransform_apply ρ (characterKernel e)

theorem projector_eq_average (ρ : FluxGroup ι →* A) (e : Flux ι) :
    projector ρ e = (Fintype.card (Flux ι) : ℝ)⁻¹ •
      ∑ g : FluxGroup ι, character e g • ρ g := by
  simp only [projector_apply, characterKernel, mul_smul, Finset.smul_sum]

/-- The ambient algebra is not assumed commutative. -/
theorem projector_mul (ρ : FluxGroup ι →* A) (e f : Flux ι) :
    projector ρ e * projector ρ f = if e = f then projector ρ e else 0 := by
  classical
  unfold projector
  rw [← finiteRepresentationTransform_convolution, characterKernel_convolution]
  split_ifs <;> simp

theorem projector_idempotent (ρ : FluxGroup ι →* A) (e : Flux ι) :
    projector ρ e * projector ρ e = projector ρ e := by
  simp [projector_mul]

/-- Algebraic orthogonality; no adjoint or inner product is presupposed. -/
theorem projector_orthogonal (ρ : FluxGroup ι →* A) {e f : Flux ι}
    (hef : e ≠ f) : projector ρ e * projector ρ f = 0 := by
  simp [projector_mul, hef]

/-- The complete binary character family resolves the algebra identity. -/
theorem sum_projector (ρ : FluxGroup ι →* A) :
    (∑ e : Flux ι, projector ρ e) = 1 := by
  classical
  simp only [projector_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_characterKernel]
  simp

/-- Character eigenrelation, obtained by translation of the finite sum. -/
theorem representation_mul_projector (ρ : FluxGroup ι →* A)
    (g : FluxGroup ι) (e : Flux ι) :
    ρ g * projector ρ e = character e g • projector ρ e := by
  calc
    ρ g * projector ρ e =
        ∑ h : FluxGroup ι, characterKernel e h • ρ (g * h) := by
      simp only [projector_apply, Finset.mul_sum, mul_smul_comm, map_mul]
    _ = ∑ h : FluxGroup ι, characterKernel e (g⁻¹ * h) • ρ h := by
      simpa only [finiteHaarSum, inv_mul_cancel_left] using
        (finiteHaarSum_left_translate g
          (fun h : FluxGroup ι => characterKernel e (g⁻¹ * h) • ρ h))
    _ = character e g • projector ρ e := by
      simp only [characterKernel_mul, flux_inv_eq_self, mul_smul,
        projector_apply, Finset.smul_sum]

/-- Right multiplication has the same character value because only the flux
representation image is abelian; no commutativity of `A` is used. -/
theorem projector_mul_representation (ρ : FluxGroup ι →* A)
    (g : FluxGroup ι) (e : Flux ι) :
    projector ρ e * ρ g = character e g • projector ρ e := by
  calc
    projector ρ e * ρ g = ρ g * projector ρ e := by
      simp only [projector_apply, Finset.sum_mul, Finset.mul_sum,
        smul_mul_assoc, mul_smul_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [← map_mul, ← map_mul, mul_comm h g]
    _ = _ := representation_mul_projector ρ g e

/-- Ordered transport under an explicitly supplied character covariance law. -/
theorem projector_mul_charge (ρ : FluxGroup ι →* A) (e r : Flux ι) (T : A)
    (hcharge : ∀ g, ρ g * T = character r g • (T * ρ g)) :
    projector ρ e * T = T * projector ρ (e + r) := by
  rw [projector_apply, projector_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [smul_mul_assoc, hcharge, smul_smul, mul_smul_comm]
  congr 1
  unfold characterKernel
  rw [character_add]
  ring

/-- A charge `r` sends sector `e` to sector `e + r`, in this ordered form. -/
theorem charge_mul_projector (ρ : FluxGroup ι →* A) (e r : Flux ι) (T : A)
    (hcharge : ∀ g, ρ g * T = character r g • (T * ρ g)) :
    T * projector ρ e = projector ρ (e + r) * T := by
  have hrr : r + r = 0 := by
    ext i
    simpa only [Pi.add_apply, Pi.zero_apply, ZMod.neg_eq_self_mod_two] using
      add_neg_cancel (r i)
  have her : e + r + r = e := by rw [add_assoc, hrr, add_zero]
  simpa only [her] using (projector_mul_charge ρ (e + r) r T hcharge).symm

/-- A real linear measurement preserves the normalized finite character sum.
The supplied operator stays on the right; no trace cyclicity is assumed. -/
theorem measure_projector_mul (ρ : FluxGroup ι →* A) (e : Flux ι)
    (Λ : A →ₗ[ℝ] ℝ) (T : A) :
    Λ (projector ρ e * T) = (Fintype.card (Flux ι) : ℝ)⁻¹ *
      ∑ g : FluxGroup ι, character e g * Λ (ρ g * T) := by
  rw [projector_eq_average, smul_mul_assoc, map_smul]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    smul_eq_mul]

theorem sum_measure_projector_mul (ρ : FluxGroup ι →* A)
    (Λ : A →ₗ[ℝ] ℝ) (T : A) :
    (∑ e : Flux ι, Λ (projector ρ e * T)) = Λ T := by
  rw [← map_sum, ← Finset.sum_mul, sum_projector, one_mul]

end OperatorAlgebra

/-- The full electric-flux space has eight sectors for three binary components. -/
theorem card_flux_three : Fintype.card (Flux (Fin 3)) = 8 := by
  change Fintype.card (Fin 3 → ZMod 2) = 8
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  norm_num

theorem card_fluxGroup_three : Fintype.card (FluxGroup (Fin 3)) = 8 := by
  rw [Fintype.card_multiplicative, card_flux_three]

/-- Explicit `1 / 8` normalization for the three-component electric projector. -/
theorem projector_three_eq_average {A : Type*} [Ring A] [Algebra ℝ A]
    (ρ : FluxGroup (Fin 3) →* A) (e : Flux (Fin 3)) :
    projector ρ e = (1 / 8 : ℝ) •
      ∑ g : FluxGroup (Fin 3), character e g • ρ g := by
  rw [projector_eq_average, card_flux_three]
  norm_num

end InfoGeometry.Algebra.BinaryFluxProjectors
