/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearFeshbachReduction

/-!
# Native complementary-space resolvents

For an idempotent `P`, the complementary space is the native submodule `ker P`.
An actual linear equivalence on this space supplies the inverse. Extending it
by zero yields both corner inverse equations used by Feshbach reduction.
The only spectral assumption is that the complementary shifted operator is
the forward map of the supplied equivalence.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearComplementaryResolvent

open InfoGeometry.Physics.NuclearFeshbachReduction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Complementary projection with its actual submodule as codomain. -/
def kerProjection (P : Module.End K V) (hP : P * P = P) : V →ₗ[K] LinearMap.ker P :=
  (1 - P).codRestrict (LinearMap.ker P) fun v => by
    change P (v - P v) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun hP v
    change P (P v) = P v at h
    rw [h, sub_self]

@[simp] theorem coe_kerProjection (P : Module.End K V) (hP : P * P = P) (v : V) :
    (kerProjection P hP v : V) = v - P v := rfl

@[simp] theorem kerProjection_subtype (P : Module.End K V) (hP : P * P = P)
    (v : LinearMap.ker P) : kerProjection P hP (v : V) = v := by
  apply Subtype.ext
  simp only [coe_kerProjection, LinearMap.mem_ker.mp v.property, sub_zero]

@[simp] theorem kerProjection_projection (P : Module.End K V) (hP : P * P = P)
    (v : V) : kerProjection P hP (P v) = 0 := by
  apply Subtype.ext
  have h := LinearMap.congr_fun hP v
  change P (P v) = P v at h
  simp only [coe_kerProjection, h, sub_self, ZeroMemClass.coe_zero]

@[simp] theorem kerProjection_complement (P : Module.End K V) (hP : P * P = P)
    (v : V) : kerProjection P hP ((1 - P) v) = kerProjection P hP v := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub,
    kerProjection_projection, sub_zero]

@[simp] theorem complement_subtype (P : Module.End K V) (v : LinearMap.ker P) :
    (1 - P) (v : V) = (v : V) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.mem_ker.mp v.property, sub_zero]

/-- `E id - Q H Q` as a native endomorphism of the complementary submodule. -/
def complementShift (P : Module.End K V) (hP : P * P = P)
    (H : Module.End K V) (E : K) : Module.End K (LinearMap.ker P) :=
  E • 1 - (kerProjection P hP).comp (H.comp (LinearMap.ker P).subtype)

theorem denominator_subtype (P H : Module.End K V) (E : K)
    (hP : P * P = P) (v : LinearMap.ker P) :
    denominator P H E (v : V) = (complementShift P hP H E v : V) := by
  simp only [denominator, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, complementShift,
    LinearMap.comp_apply, Submodule.subtype_apply, Module.End.one_apply,
    Submodule.coe_sub, Submodule.coe_smul, coe_kerProjection,
    LinearMap.mem_ker.mp v.property, sub_zero]

theorem kerProjection_denominator (P H : Module.End K V) (E : K)
    (hP : P * P = P) (v : V) :
    kerProjection P hP (denominator P H E v) =
      complementShift P hP H E (kerProjection P hP v) := by
  simp only [denominator, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_sub, map_smul, kerProjection_projection,
    complementShift, Module.End.one_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, coe_kerProjection, sub_zero]

/-- Extend the inverse of a complementary linear equivalence by zero. -/
def liftInverse (P : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P) : Module.End K V :=
  (LinearMap.ker P).subtype.comp (e.symm.toLinearMap.comp (kerProjection P hP))

@[simp] theorem liftInverse_apply (P : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P) (v : V) :
    liftInverse P hP e v = (e.symm (kerProjection P hP v) : V) := rfl

theorem complement_mul_liftInverse (P : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P) :
    (1 - P) * liftInverse P hP e = liftInverse P hP e := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, liftInverse_apply, complement_subtype]

theorem liftInverse_mul_complement (P : Module.End K V) (hP : P * P = P)
    (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P) :
    liftInverse P hP e * (1 - P) = liftInverse P hP e := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, liftInverse_apply, kerProjection_complement]

theorem denominator_mul_liftInverse (P H : Module.End K V) (E : K)
    (hP : P * P = P) (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P)
    (he : e.toLinearMap = complementShift P hP H E) :
    denominator P H E * liftInverse P hP e = 1 - P := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, liftInverse_apply, denominator_subtype P H E hP, ← he]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    coe_kerProjection, LinearMap.sub_apply, Module.End.one_apply]

theorem liftInverse_mul_denominator (P H : Module.End K V) (E : K)
    (hP : P * P = P) (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P)
    (he : e.toLinearMap = complementShift P hP H E) :
    liftInverse P hP e * denominator P H E = 1 - P := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, liftInverse_apply, kerProjection_denominator P H E hP,
    ← he]
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    coe_kerProjection, LinearMap.sub_apply, Module.End.one_apply]

/-- Native complementary invertibility gives the exact nuclear spectral
reduction without postulating an inverse on the full ambient space. -/
theorem eigen_equation_iff_of_equiv (P H : Module.End K V) (E : K)
    (hP : P * P = P) (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P)
    (he : e.toLinearMap = complementShift P hP H E) (v : V) (hv : P v = v) :
    H (waveOperator P H (liftInverse P hP e) v) =
        E • waveOperator P H (liftInverse P hP e) v ↔
      effectiveHamiltonian P H (liftInverse P hP e) v = E • v :=
  eigen_equation_iff P H _ E (complement_mul_liftInverse P hP e)
    (denominator_mul_liftInverse P H E hP e he) v hv

/-- The same native inverse reconstructs every full eigenvector. -/
theorem reconstruct_eigenvector_of_equiv (P H : Module.End K V) (E : K)
    (hP : P * P = P) (e : LinearMap.ker P ≃ₗ[K] LinearMap.ker P)
    (he : e.toLinearMap = complementShift P hP H E) (ψ : V) (hψ : H ψ = E • ψ) :
    waveOperator P H (liftInverse P hP e) (P ψ) = ψ :=
  reconstruct_eigenvector P H _ E hP (liftInverse_mul_complement P hP e)
    (liftInverse_mul_denominator P H E hP e he) ψ hψ

end InfoGeometry.Physics.NuclearComplementaryResolvent
