/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealDualTwistor
import InfoGeometry.LinearAlgebra.RegularDyadCompression
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Mixed logarithmic pairing on nonincident real dual pairs

For `p = (v, φ)` with `φ v ≠ 0`, the mixed directional derivative of
`log |φ v|` is the native bilinear map
`H(u, ψ) = ψ u / φ v - φ u * ψ v / (φ v)^2`.
It factors through the complement of the existing normalized rank-one dyad.
Its two radicals are precisely the independent radial directions, and its
restriction to `φ u = 0`, `ψ v = 0` is nondegenerate.

All derivative statements are derivatives of real scalar parameters on
explicit affine lines. No topology on the algebraic carrier is required.
Representative covariance is proved below; a descended projective manifold,
closed differential form, global para-Kähler structure, and boundary residue
are separate constructions.
-/

noncomputable section

namespace InfoGeometry.Twistor.NonincidentLogPairing

open RealDualTwistor
open InfoGeometry.LinearAlgebra.RegularDyadCompression
open scoped Topology

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The normalized dyad is the normalization of the existing incidence
operator, in the full endomorphism ring. -/
theorem normalizedDyad_eq_scaled_dyad (p : Carrier V) :
    normalizedDyad p.1 p.2 = (p.2 p.1)⁻¹ • dyad p := by
  ext u
  simp [normalizedDyad_apply, dyad_apply, smul_smul, div_eq_mul_inv, mul_comm]

/-- The normalized projector transforms by the actual contragredient frame
action and conjugation of endomorphisms. -/
theorem normalizedDyad_frameAction (e : V ≃ₗ[ℝ] W) (p : Carrier V) :
    normalizedDyad (frameAction e p).1 (frameAction e p).2 =
      e.toLinearMap.comp ((normalizedDyad p.1 p.2).comp e.symm.toLinearMap) := by
  ext u
  simp [normalizedDyad_apply]

/-- The mixed differential of the local logarithmic pairing. -/
def mixedLogKernel (p : Carrier V) : V →ₗ[ℝ] Module.Dual ℝ V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u ψ => ψ u / p.2 p.1 - p.2 u * ψ p.1 / (p.2 p.1)^2)
    (by intros; simp only [map_add]; ring)
    (by intros; simp only [map_smul, smul_eq_mul]; ring)
    (by intros; simp only [LinearMap.add_apply]; ring)
    (by intros; simp only [LinearMap.smul_apply, smul_eq_mul]; ring)

@[simp] theorem mixedLogKernel_apply (p : Carrier V) (u : V)
    (ψ : Module.Dual ℝ V) :
    mixedLogKernel p u ψ =
      ψ u / p.2 p.1 - p.2 u * ψ p.1 / (p.2 p.1)^2 := rfl

/-- The mixed differential reads the complementary endomorphism. -/
theorem mixedLogKernel_eq_complement (p : Carrier V) (h : p.2 p.1 ≠ 0)
    (u : V) (ψ : Module.Dual ℝ V) :
    mixedLogKernel p u ψ =
      ψ ((1 - normalizedDyad p.1 p.2) u) / p.2 p.1 := by
  simp only [mixedLogKernel_apply, LinearMap.sub_apply, Module.End.one_apply,
    normalizedDyad_apply, map_sub, map_smul, smul_eq_mul]
  field_simp [h]

/-- The equivalent covector-side factorization. -/
theorem mixedLogKernel_eq_dual_complement (p : Carrier V) (h : p.2 p.1 ≠ 0)
    (u : V) (ψ : Module.Dual ℝ V) :
    mixedLogKernel p u ψ =
      (ψ - (ψ p.1 / p.2 p.1) • p.2) u / p.2 p.1 := by
  simp only [mixedLogKernel_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  field_simp [h]

@[simp] theorem mixedLogKernel_radial_left (p : Carrier V) (h : p.2 p.1 ≠ 0)
    (ψ : Module.Dual ℝ V) : mixedLogKernel p p.1 ψ = 0 := by
  rw [mixedLogKernel_eq_complement p h]
  simp [normalizedDyad_self p.1 p.2 h]

@[simp] theorem mixedLogKernel_radial_right (p : Carrier V) (h : p.2 p.1 ≠ 0)
    (u : V) : mixedLogKernel p u p.2 = 0 := by
  rw [mixedLogKernel_eq_dual_complement p h]
  simp [h]

/-- Algebraic covectors detect exactly the primal radial degeneracy. -/
theorem mixedLogKernel_left_radical (p : Carrier V) (h : p.2 p.1 ≠ 0) (u : V) :
    (∀ ψ, mixedLogKernel p u ψ = 0) ↔ u ∈ ℝ ∙ p.1 := by
  constructor
  · intro hu
    have hzero : (1 - normalizedDyad p.1 p.2) u = 0 := by
      apply eq_zero_of_dual_vanishes
      intro ψ
      have hh := hu ψ
      rw [mixedLogKernel_eq_complement p h] at hh
      exact (div_eq_zero_iff.mp hh).resolve_right h
    have heq : u = (p.2 u / p.2 p.1) • p.1 := by
      simpa only [LinearMap.sub_apply, Module.End.one_apply,
        normalizedDyad_apply, sub_eq_zero] using hzero
    exact Submodule.mem_span_singleton.mpr ⟨_, heq.symm⟩
  · intro hu ψ
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      mixedLogKernel_radial_left p h, mul_zero]

/-- The other radical is exactly the dual radial direction. -/
theorem mixedLogKernel_right_radical (p : Carrier V) (h : p.2 p.1 ≠ 0)
    (ψ : Module.Dual ℝ V) :
    (∀ u, mixedLogKernel p u ψ = 0) ↔ ψ ∈ ℝ ∙ p.2 := by
  constructor
  · intro hψ
    have heq : ψ = (ψ p.1 / p.2 p.1) • p.2 := by
      ext u
      have hh := hψ u
      rw [mixedLogKernel_eq_dual_complement p h] at hh
      have hz := (div_eq_zero_iff.mp hh).resolve_right h
      exact sub_eq_zero.mp hz
    exact Submodule.mem_span_singleton.mpr ⟨_, heq.symm⟩
  · intro hψ u
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hψ
    simp only [map_smul, smul_eq_mul, mixedLogKernel_radial_right p h, mul_zero]

/-- On the chosen horizontal slices, the primal variable is separated by
horizontal covectors. No finite dimension is used. -/
theorem mixedLogKernel_horizontal_left (p : Carrier V) (h : p.2 p.1 ≠ 0)
    (u : V) (hu : p.2 u = 0)
    (huψ : ∀ ψ : Module.Dual ℝ V, ψ p.1 = 0 → mixedLogKernel p u ψ = 0) : u = 0 := by
  apply eq_zero_of_dual_vanishes
  intro ψ
  let χ := ψ - (ψ p.1 / p.2 p.1) • p.2
  have hχ : χ p.1 = 0 := by
    simp [χ, smul_eq_mul, div_mul_cancel₀ _ h]
  have hz := huψ χ hχ
  have hz' : ψ u / p.2 p.1 = 0 := by
    simpa [mixedLogKernel_apply, χ, hu] using hz
  exact (div_eq_zero_iff.mp hz').resolve_right h

/-- The same horizontal mixed pairing separates covectors. -/
theorem mixedLogKernel_horizontal_right (p : Carrier V) (h : p.2 p.1 ≠ 0)
    (ψ : Module.Dual ℝ V) (hψ : ψ p.1 = 0)
    (huψ : ∀ u : V, p.2 u = 0 → mixedLogKernel p u ψ = 0) : ψ = 0 := by
  ext u
  let w := u - normalizedDyad p.1 p.2 u
  have hw : p.2 w = 0 := by
    change p.2 (u - normalizedDyad p.1 p.2 u) = 0
    rw [map_sub, covector_normalizedDyad p.1 u p.2 h, sub_self]
  have hz := huψ w hw
  have hz' : ψ u / p.2 p.1 = 0 := by
    simpa [mixedLogKernel_apply, w, normalizedDyad_apply, hψ] using hz
  exact (div_eq_zero_iff.mp hz').resolve_right h

/-- Independent rescalings and their tangent rescalings leave the mixed
kernel unchanged. This is a representative law, not a manifold construction. -/
theorem mixedLogKernel_rescale (p : Carrier V) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : p.2 p.1 ≠ 0)
    (u : V) (ψ : Module.Dual ℝ V) :
    mixedLogKernel (a • p.1, b • p.2) (a • u) (b • ψ) = mixedLogKernel p u ψ := by
  simp only [mixedLogKernel_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
  field_simp [ha, hb, h]

theorem mixedLogKernel_frameAction (e : V ≃ₗ[ℝ] W) (p : Carrier V)
    (u : V) (ψ : Module.Dual ℝ V) :
    mixedLogKernel (frameAction e p) (e u) (ψ.comp e.symm.toLinearMap) =
      mixedLogKernel p u ψ := by
  simp [mixedLogKernel_apply]

/-- The local potential changes by separate scalar gauge terms. -/
theorem logPairing_rescale (p : Carrier V) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : p.2 p.1 ≠ 0) :
    Real.log |(b • p.2) (a • p.1)| =
      Real.log |a| + Real.log |b| + Real.log |p.2 p.1| := by
  simp only [Real.log_abs, LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [Real.log_mul ha (mul_ne_zero hb h), Real.log_mul hb h]
  ring

/-- Native differentiation of the logarithmic pairing along a primal affine
line, valid on either sign component of the nonincident locus. -/
theorem hasDerivAt_logPairing (p : Carrier V) (h : p.2 p.1 ≠ 0) (u : V) :
    HasDerivAt (fun t : ℝ => Real.log |p.2 (p.1 + t • u)|)
      (p.2 u / p.2 p.1) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => p.2 (p.1 + t • u)) (p.2 u) 0 := by
    simpa only [map_add, map_smul, smul_eq_mul] using
      (hasDerivAt_mul_const (x := (0 : ℝ)) (p.2 u)).const_add (p.2 p.1)
  simpa only [Real.log_abs, zero_smul, add_zero] using
    hlin.log (by simpa using h)

/-- Differentiating the first logarithmic derivative in the dual direction
gives the mixed kernel. -/
theorem hasDerivAt_logPairing_readout (p : Carrier V) (h : p.2 p.1 ≠ 0)
    (u : V) (ψ : Module.Dual ℝ V) :
    HasDerivAt (fun t : ℝ => (p.2 + t • ψ) u / (p.2 + t • ψ) p.1)
      (mixedLogKernel p u ψ) 0 := by
  have hn : HasDerivAt (fun t : ℝ => (p.2 + t • ψ) u) (ψ u) 0 := by
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] using
      (hasDerivAt_mul_const (x := (0 : ℝ)) (ψ u)).const_add (p.2 u)
  have hd : HasDerivAt (fun t : ℝ => (p.2 + t • ψ) p.1) (ψ p.1) 0 := by
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] using
      (hasDerivAt_mul_const (x := (0 : ℝ)) (ψ p.1)).const_add (p.2 p.1)
  convert hn.div hd (by simpa using h) using 1
  simp only [mixedLogKernel_apply, zero_smul, add_zero]
  field_simp [h]

/-- The kernel is an actual iterated mixed derivative of the logarithmic
potential. Nonincidence supplies the neighborhood on which the first
derivative formula is valid. -/
theorem hasDerivAt_mixed_logPairing (p : Carrier V) (h : p.2 p.1 ≠ 0)
    (u : V) (ψ : Module.Dual ℝ V) :
    HasDerivAt
      (fun t : ℝ => deriv (fun r : ℝ => Real.log |(p.2 + t • ψ) (p.1 + r • u)|) 0)
      (mixedLogKernel p u ψ) 0 := by
  apply (hasDerivAt_logPairing_readout p h u ψ).congr_of_eventuallyEq
  have hd : HasDerivAt (fun t : ℝ => (p.2 + t • ψ) p.1) (ψ p.1) 0 := by
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] using
      (hasDerivAt_mul_const (x := (0 : ℝ)) (ψ p.1)).const_add (p.2 p.1)
  have hne := hd.continuousAt.eventually
    (eventually_ne_nhds (show (p.2 + (0 : ℝ) • ψ) p.1 ≠ 0 by simpa using h))
  filter_upwards [hne] with t ht
  exact (hasDerivAt_logPairing (p.1, p.2 + t • ψ) ht u).deriv

/-- Nonincident rank-one projectors need not commute in the full operator
ring, already on a two-dimensional real carrier. -/
theorem nonincident_projectors_noncommute :
    ∃ p q : Carrier (ℝ × ℝ), p.2 p.1 ≠ 0 ∧ q.2 q.1 ≠ 0 ∧
      normalizedDyad p.1 p.2 * normalizedDyad q.1 q.2 ≠
        normalizedDyad q.1 q.2 * normalizedDyad p.1 p.2 := by
  let p : Carrier (ℝ × ℝ) := ((1, 0), LinearMap.fst ℝ ℝ ℝ)
  let q : Carrier (ℝ × ℝ) := ((1, 1), LinearMap.snd ℝ ℝ ℝ)
  refine ⟨p, q, by norm_num [p], by norm_num [q], ?_⟩
  intro h
  have hh := congrArg (fun A : Module.End ℝ (ℝ × ℝ) => (A (0, 1)).1) h
  norm_num [Module.End.mul_apply, normalizedDyad_apply, p, q] at hh

end InfoGeometry.Twistor.NonincidentLogPairing
