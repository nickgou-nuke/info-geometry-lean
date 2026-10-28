/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCoupledCorners
import InfoGeometry.Core.JordanMultiplicationClosure
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The graded inner differential on the full Peirce algebra

The existing reflection supplies the actual parity automorphism. The native
linear map `differential p u` uses its sign on the input, so its even and odd
restrictions are respectively the Lie and Jordan multiplication actions.
For an odd generator, its square is the inner action of `u * u`. A supported
directed corner thus gives a genuine square-zero map and a native cochain complex
on the full algebra.

The two-generator mixed anticommutator is an inner derivation. No positivity or
adjoint-codifferential identification is asserted for this graded construction.
-/

universe uR uA

namespace InfoGeometry.Canonical.PeirceBoundaryComplex

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory
open Core.PeirceDecomposition Core.PeirceGrading Core.PeirceCoupledCorners
open Core.JordanMultiplicationClosure

section Ring

variable {A : Type uA} [Ring A] {p x : A}

private theorem reflection_mul_nested (hp : IsIdempotentElem p) (x : A) :
    reflection p * (reflection p * x) = x := by
  rw [← mul_assoc, reflection_sq hp, one_mul]

private theorem conjugation_mul (hp : IsIdempotentElem p) (x y : A) :
    conjugation p (x * y) = conjugation p x * conjugation p y := by
  simp only [conjugation_apply, mul_assoc, reflection_mul_nested hp]

private theorem conjugation_involutive (hp : IsIdempotentElem p) (x : A) :
    conjugation p (conjugation p x) = x := by
  simp only [conjugation_apply, mul_assoc, reflection_mul_nested hp,
    reflection_sq hp, mul_one]

private theorem conjugation_eq_of_mem_even (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (even p)) : conjugation p x = x := by
  rw [conjugation_apply, (even_commutes_reflection hp hx).eq,
    mul_assoc, reflection_sq hp, mul_one]

private theorem conjugation_eq_neg_of_mem_odd (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (odd p)) : conjugation p x = -x := by
  rw [conjugation_apply,
    eq_neg_of_add_eq_zero_left (odd_anticommutes_reflection hp hx),
    neg_mul, mul_assoc, reflection_sq hp, mul_one]

end Ring

section Algebra

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
variable {p u v x : A}

/-- The full algebra's graded inner action, built from native multiplication maps. -/
def differential (p u : A) : Module.End R A :=
  LinearMap.mulLeft R u -
    LinearMap.mulLeftRight R (reflection p, reflection p * u)

theorem differential_apply (p u x : A) :
    differential (R := R) p u x = u * x - conjugation p x * u := by
  simp only [differential, LinearMap.sub_apply, LinearMap.mulLeft_apply,
    LinearMap.mulLeftRight_apply, conjugation_apply, mul_assoc]

/-- On the actual even submodule, the action is the native Lie adjoint action. -/
theorem differential_apply_of_even (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (even p)) :
    differential (R := R) p u x = LieAlgebra.ad R A u x := by
  rw [differential_apply, conjugation_eq_of_mem_even hp hx]
  rfl

/-- On the actual odd submodule, the sign changes to the existing Jordan action. -/
theorem differential_apply_of_odd (hp : IsIdempotentElem p)
    (hx : x ∈ LinearMap.range (odd p)) :
    differential (R := R) p u x = jordanLeft (R := R) u x := by
  rw [differential_apply, conjugation_eq_neg_of_mem_odd hp hx,
    neg_mul, sub_neg_eq_add]
  rfl

theorem differential_mem_odd (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) (hx : x ∈ LinearMap.range (even p)) :
    differential (R := R) p u x ∈ LinearMap.range (odd p) := by
  rw [differential_apply_of_even hp hx]
  change u * x - x * u ∈ LinearMap.range (odd p)
  exact (LinearMap.range (odd p)).sub_mem
    (odd_mul_even hp hu hx) (even_mul_odd hp hx hu)

theorem differential_mem_even (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) (hx : x ∈ LinearMap.range (odd p)) :
    differential (R := R) p u x ∈ LinearMap.range (even p) := by
  rw [differential_apply_of_odd hp hx]
  change u * x + x * u ∈ LinearMap.range (even p)
  exact (LinearMap.range (even p)).add_mem
    (odd_mul_odd hp hu hx) (odd_mul_odd hp hx hu)

/-- The reflection-twisted Leibniz rule holds for every generating element. -/
theorem differential_mul (hp : IsIdempotentElem p) (u x y : A) :
    differential (R := R) p u (x * y) =
      differential (R := R) p u x * y +
        conjugation p x * differential (R := R) p u y := by
  simp only [differential_apply, conjugation_mul hp]
  noncomm_ring

/-- An odd generator makes the full action switch the reflection parity. -/
theorem conjugation_differential (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) (x : A) :
    conjugation p (differential (R := R) p u x) =
      -differential (R := R) p u (conjugation p x) := by
  calc
    conjugation p (differential (R := R) p u x) =
        conjugation p u * conjugation p x - x * conjugation p u := by
      simp only [differential_apply, map_sub, conjugation_mul hp,
        conjugation_involutive hp]
    _ = -(u * conjugation p x - x * u) := by
      rw [conjugation_eq_neg_of_mem_odd hp hu]
      noncomm_ring
    _ = -differential (R := R) p u (conjugation p x) := by
      rw [differential_apply, conjugation_involutive hp]

/-- Its square is the ordinary inner action of the generator's square. -/
theorem differential_sq (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) :
    differential (R := R) p u ^ 2 = LieAlgebra.ad R A (u * u) := by
  rw [pow_two]
  apply LinearMap.ext
  intro x
  change differential (R := R) p u (differential (R := R) p u x) =
    (u * u) * x - x * (u * u)
  simp only [differential_apply, map_sub, conjugation_mul hp,
    conjugation_eq_neg_of_mem_odd hp hu, conjugation_involutive hp]
  noncomm_ring

/-- Two odd graded actions close on the native inner action of their symmetric product. -/
theorem differential_anticommutator (hp : IsIdempotentElem p)
    (hu : u ∈ LinearMap.range (odd p)) (hv : v ∈ LinearMap.range (odd p)) :
    differential (R := R) p u * differential (R := R) p v +
      differential (R := R) p v * differential (R := R) p u =
        LieAlgebra.ad R A (u * v + v * u) := by
  apply LinearMap.ext
  intro x
  change differential (R := R) p u (differential (R := R) p v x) +
    differential (R := R) p v (differential (R := R) p u x) =
      (u * v + v * u) * x - x * (u * v + v * u)
  simp only [differential_apply, map_sub, conjugation_mul hp,
    conjugation_eq_neg_of_mem_odd hp hu, conjugation_eq_neg_of_mem_odd hp hv,
    conjugation_involutive hp]
  noncomm_ring

theorem differential_sq_zero_of_mem_peirce10 (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) : differential (R := R) p u ^ 2 = 0 := by
  have huodd : u ∈ LinearMap.range (odd p) := by
    rw [mem_odd_iff hp, left_support10 hp hu, right_support10 hp hu, add_zero]
  rw [differential_sq hp huodd, peirce10_mul_peirce10_eq_zero p hp.eq hu hu, map_zero]

theorem differential_sq_zero_of_mem_peirce01 (hp : IsIdempotentElem p)
    (hu : u ∈ peirce01 p) : differential (R := R) p u ^ 2 = 0 := by
  have huodd : u ∈ LinearMap.range (odd p) := by
    rw [mem_odd_iff hp, left_support01 hp hu, right_support01 hp hu, zero_add]
  rw [differential_sq hp huodd, peirce01_mul_peirce01_eq_zero p hp.eq hu hu, map_zero]

/-- The differential of the projection detects the directed corner itself. -/
theorem differential_apply_idempotent (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) : differential (R := R) p u p = -u := by
  have hpeven : p ∈ LinearMap.range (even p) := (mem_even_iff hp).mpr rfl
  rw [differential_apply_of_even hp hpeven]
  change u * p - p * u = -u
  rw [right_support10 hp hu, left_support10 hp hu, zero_sub]

theorem differential_ne_zero (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hu0 : u ≠ 0) : differential (R := R) p u ≠ 0 := by
  intro h
  have hvalue : differential (R := R) p u p = 0 :=
    congrArg (fun f : Module.End R A => f p) h
  rw [differential_apply_idempotent hp hu] at hvalue
  exact hu0 (neg_eq_zero.mp hvalue)

/-- A native cochain complex whose differential is the proved full-algebra map. -/
noncomputable def cornerComplex (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p) :
    CochainComplex (ModuleCat.{uA} R) ℕ :=
  CochainComplex.of (fun _ : ℕ => ModuleCat.of R A)
    (fun _ => ModuleCat.ofHom (differential (R := R) p u))
    (fun _ => by
      apply ModuleCat.hom_ext
      change differential (R := R) p u * differential (R := R) p u = 0
      simpa only [pow_two] using differential_sq_zero_of_mem_peirce10 (R := R) hp hu)

@[simp] theorem cornerComplex_X (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p)
    (i : ℕ) : (cornerComplex (R := R) hp hu).X i = ModuleCat.of R A := rfl

@[simp] theorem cornerComplex_d (hp : IsIdempotentElem p) (hu : u ∈ peirce10 p)
    (i : ℕ) : (cornerComplex (R := R) hp hu).d i (i + 1) =
      ModuleCat.ofHom (differential (R := R) p u) := by
  exact CochainComplex.of_d (fun _ : ℕ => ModuleCat.of R A)
    (fun _ => ModuleCat.ofHom (differential (R := R) p u)) i

end Algebra

end InfoGeometry.Canonical.PeirceBoundaryComplex
