/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealDualTwistor
import InfoGeometry.Krein.DoubledSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Real duality and the canonical doubled Krein form

An actual real linear self-duality gives an invertible lightcone change of
variables into the existing `DoubledSpace`.  In finite real dimension the
inner product constructs such a self-duality.  For this concrete choice,
the lightcone map preserves the genuine-dual hyperbolic pairing exactly as
the existing `hessian_indefinite_form`.  Transporting the existing fundamental
symmetry then produces a positive definite pairing.

These are algebraic equivalences and pairing identities, not a topological
completion or an infinite-dimensional algebraic self-duality.  No complex
scalar extension is used.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealDualTwistorKreinBridge

open InfoGeometry.Krein
open InfoGeometry.Twistor.RealDualTwistor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Unnormalized lightcone coordinates with a half-factor in the covector
direction. Their inverse requires no square roots. -/
def lightconeCoordinates (e : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Carrier E ≃ₗ[ℝ] (E × E) where
  toFun p := (p.1 + (1 / 2 : ℝ) • e.symm p.2,
    p.1 - (1 / 2 : ℝ) • e.symm p.2)
  invFun q := ((1 / 2 : ℝ) • (q.1 + q.2), e (q.1 - q.2))
  left_inv p := by
    apply Prod.ext
    · dsimp
      module
    · dsimp
      apply e.symm.injective
      simp only [LinearEquiv.symm_apply_apply]
      module
  right_inv q := by
    apply Prod.ext <;> simp only [LinearEquiv.symm_apply_apply] <;> module
  map_add' p q := by
    apply Prod.ext <;> dsimp <;> simp only [map_add] <;> module
  map_smul' c p := by
    apply Prod.ext <;> dsimp <;> simp only [map_smul] <;> module

/-- An actual equivalence into the repository's canonical doubled carrier. -/
def lightconeDoubled (e : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Carrier E ≃ₗ[ℝ] DoubledSpace E :=
  (lightconeCoordinates e).trans
    (WithLp.linearEquiv (2 : ENNReal) ℝ (E × E)).symm

omit [CompleteSpace E] in
@[simp] theorem lightconeDoubled_apply
    (e : E ≃ₗ[ℝ] Module.Dual ℝ E) (p : Carrier E) :
    lightconeDoubled e p = to_doubled
      (p.1 + (1 / 2 : ℝ) • e.symm p.2)
      (p.1 - (1 / 2 : ℝ) • e.symm p.2) := rfl

omit [CompleteSpace E] in
@[simp] theorem lightconeDoubled_symm_apply
    (e : E ≃ₗ[ℝ] Module.Dual ℝ E) (u : DoubledSpace E) :
    (lightconeDoubled e).symm u =
      ((1 / 2 : ℝ) • (WithLp.fst u + WithLp.snd u),
        e (WithLp.fst u - WithLp.snd u)) := rfl

/-- Transport the existing fundamental symmetry, without confusing its
square-plus-one relation with the square-minus-one clock. -/
def dualFundamentalSymmetry (e : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    Module.End ℝ (Carrier E) :=
  (lightconeDoubled e).symm.toLinearMap.comp
    ((spectral_epsilon (E := E)).toLinearMap.comp
      (lightconeDoubled e).toLinearMap)

omit [CompleteSpace E] in
theorem dualFundamentalSymmetry_intertwines
    (e : E ≃ₗ[ℝ] Module.Dual ℝ E) (p : Carrier E) :
    lightconeDoubled e (dualFundamentalSymmetry e p) =
      spectral_epsilon (lightconeDoubled e p) := by
  change lightconeDoubled e ((lightconeDoubled e).symm
    (spectral_epsilon (lightconeDoubled e p))) = _
  exact (lightconeDoubled e).apply_symm_apply _

@[simp] theorem dualFundamentalSymmetry_sq
    (e : E ≃ₗ[ℝ] Module.Dual ℝ E) :
    dualFundamentalSymmetry e * dualFundamentalSymmetry e = 1 := by
  apply LinearMap.ext
  intro p
  apply (lightconeDoubled e).injective
  simp only [Module.End.mul_apply, Module.End.one_apply,
    dualFundamentalSymmetry_intertwines]
  exact congrArg (fun A : DoubledSpace E →L[ℝ] DoubledSpace E =>
    A (lightconeDoubled e p)) (spectral_epsilon_involution E)

/-- The real inner-product form as a map into the algebraic dual. -/
def realInnerFlat : E →ₗ[ℝ] Module.Dual ℝ E :=
  LinearMap.mk₂ ℝ (fun x y : E => inner ℝ x y)
    (by intros; simp [inner_add_left])
    (by intros; simp [real_inner_smul_left])
    (by intros; simp [inner_add_right])
    (by intros; simp [real_inner_smul_right])

omit [CompleteSpace E] in
@[simp] theorem realInnerFlat_apply (x y : E) :
    realInnerFlat x y = inner ℝ x y := rfl

omit [CompleteSpace E] in
theorem realInnerFlat_injective : Function.Injective (realInnerFlat (E := E)) := by
  intro x y h
  apply ext_inner_right ℝ
  intro z
  exact congrArg (fun φ : Module.Dual ℝ E => φ z) h

section FiniteDimension

variable [FiniteDimensional ℝ E]

/-- A concrete positive self-duality in finite real dimension. -/
def realInnerDuality : E ≃ₗ[ℝ] Module.Dual ℝ E :=
  LinearEquiv.ofBijective realInnerFlat (by
    have hdim : Module.finrank ℝ E = Module.finrank ℝ (Module.Dual ℝ E) := by
      rw [Subspace.dual_finrank_eq]
    exact ⟨realInnerFlat_injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
        realInnerFlat_injective⟩)

omit [CompleteSpace E] in
@[simp] theorem realInnerDuality_apply (x y : E) :
    realInnerDuality x y = inner ℝ x y := rfl

/-- Exact form transport to the existing canonical indefinite pairing. -/
theorem hessian_lightconeDoubled (p q : Carrier E) :
    hessian_indefinite_form (lightconeDoubled realInnerDuality p)
      (lightconeDoubled realInnerDuality q) = neutralForm p q := by
  rw [hessian_indefinite_form_eq_doubledHilbertBilin_spectral_epsilon]
  simp only [lightconeDoubled_apply, spectral_epsilon_to_doubled,
    doubledHilbertBilin_to_doubled, inner_neg_right, neutralForm_apply,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  have hpq : inner ℝ ((realInnerDuality (E := E)).symm p.2) q.1 = p.2 q.1 := by
    change realInnerDuality (realInnerDuality.symm p.2) q.1 = p.2 q.1
    rw [LinearEquiv.apply_symm_apply]
  have hqp : inner ℝ p.1 ((realInnerDuality (E := E)).symm q.2) = q.2 p.1 := by
    rw [real_inner_comm]
    change realInnerDuality (realInnerDuality.symm q.2) p.1 = q.2 p.1
    rw [LinearEquiv.apply_symm_apply]
  rw [hpq, hqp]
  ring

/-- The transported fundamental symmetry recovers the positive doubled
Hilbert form exactly; its indefinite origin remains explicit. -/
theorem neutralForm_fundamental_eq_positive (p q : Carrier E) :
    neutralForm p (dualFundamentalSymmetry realInnerDuality q) =
      doubledHilbertBilin (lightconeDoubled realInnerDuality p)
        (lightconeDoubled realInnerDuality q) := by
  rw [← hessian_lightconeDoubled, dualFundamentalSymmetry_intertwines,
    hessian_indefinite_form_eq_doubledHilbertBilin_spectral_epsilon]
  have hε : spectral_epsilon (spectral_epsilon
      (lightconeDoubled realInnerDuality q)) = lightconeDoubled realInnerDuality q :=
    congrArg (fun A : DoubledSpace E →L[ℝ] DoubledSpace E =>
      A (lightconeDoubled realInnerDuality q)) (spectral_epsilon_involution E)
  rw [hε]

/-- Strict positivity on nonzero genuine-dual states, using a constructed
finite-dimensional duality rather than an assumed positivity certificate. -/
theorem realInnerDuality_physical_pos (p : Carrier E) (hp : p ≠ 0) :
    0 < neutralForm p (dualFundamentalSymmetry realInnerDuality p) := by
  rw [neutralForm_fundamental_eq_positive]
  change 0 < inner ℝ (lightconeDoubled realInnerDuality p)
    (lightconeDoubled realInnerDuality p)
  apply real_inner_self_pos.mpr
  intro h
  apply hp
  apply (lightconeDoubled realInnerDuality).injective
  simpa using h

end FiniteDimension

end InfoGeometry.Twistor.RealDualTwistorKreinBridge
