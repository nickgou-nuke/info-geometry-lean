/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceMatrixTracePairing
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! Opposite Peirce corners of full finite matrices are perfectly paired by
trace over a field. Corner modules are native ranges of multiplication maps;
their membership agrees with the existing Peirce sets. No orthogonality or
nonzero-rank assumption is required on the idempotent.
-/
noncomputable section
namespace InfoGeometry.Core.PeirceDecomposition
open Matrix
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def component10Linear (P : Matrix n n K) : Module.End K (Matrix n n K) :=
  (mulRightLinearMap n K (complementIdempotent P)).comp (mulLeftLinearMap n K P)

def component01Linear (P : Matrix n n K) : Module.End K (Matrix n n K) :=
  (mulRightLinearMap n K P).comp (mulLeftLinearMap n K (complementIdempotent P))

@[simp] theorem component10Linear_apply (P X : Matrix n n K) :
    component10Linear P X = component10 P X := rfl

@[simp] theorem component01Linear_apply (P X : Matrix n n K) :
    component01Linear P X = component01 P X := rfl

theorem mem_range_component10Linear (P X : Matrix n n K) :
    X ∈ LinearMap.range (component10Linear P) ↔ X ∈ peirce10 P := by
  change (∃ Y, P * Y * complementIdempotent P = X) ↔
    ∃ Y, X = P * Y * complementIdempotent P
  exact exists_congr fun _ => eq_comm

theorem mem_range_component01Linear (P X : Matrix n n K) :
    X ∈ LinearMap.range (component01Linear P) ↔ X ∈ peirce01 P := by
  change (∃ Y, complementIdempotent P * Y * P = X) ↔
    ∃ Y, X = complementIdempotent P * Y * P
  exact exists_congr fun _ => eq_comm

theorem component10_fixed_of_mem_range (P : Matrix n n K) (hP : P * P = P)
    (X : LinearMap.range (component10Linear P)) : component10 P X = X := by
  rcases X.property with ⟨Y, hY⟩
  change component10 P X.val = X.val
  rw [← hY, component10Linear_apply]
  unfold component10
  calc
    P * (P * Y * complementIdempotent P) * complementIdempotent P =
        (P * P) * Y * (complementIdempotent P * complementIdempotent P) := by
      noncomm_ring
    _ = P * Y * complementIdempotent P := by
      rw [hP, complementIdempotent_sq P hP]

theorem component01_fixed_of_mem_range (P : Matrix n n K) (hP : P * P = P)
    (X : LinearMap.range (component01Linear P)) : component01 P X = X := by
  rcases X.property with ⟨Y, hY⟩
  change component01 P X.val = X.val
  rw [← hY, component01Linear_apply]
  unfold component01
  calc
    complementIdempotent P * (complementIdempotent P * Y * P) * P =
        (complementIdempotent P * complementIdempotent P) * Y * (P * P) := by
      noncomm_ring
    _ = complementIdempotent P * Y * P := by
      rw [hP, complementIdempotent_sq P hP]

def oppositeCornerTracePairing (P : Matrix n n K) :
    LinearMap.range (component10Linear P) →ₗ[K]
      LinearMap.range (component01Linear P) →ₗ[K] K where
  toFun X :=
    { toFun := fun Y => trace (X.val * Y.val)
      map_add' := by intros; simp [mul_add, trace_add]
      map_smul' := by intros; simp [mul_smul_comm, trace_smul] }
  map_add' := by intros; ext; simp [add_mul, trace_add]
  map_smul' := by intros; ext; simp [smul_mul_assoc, trace_smul]

@[simp] theorem oppositeCornerTracePairing_apply (P : Matrix n n K)
    (X : LinearMap.range (component10Linear P))
    (Y : LinearMap.range (component01Linear P)) :
    oppositeCornerTracePairing P X Y = trace (X.val * Y.val) := rfl

theorem oppositeCornerTracePairing_injective (P : Matrix n n K) (hP : P * P = P) :
    Function.Injective (oppositeCornerTracePairing P) := by
  intro X Y h
  have hz : (X - Y : LinearMap.range (component10Linear P)).val = 0 := by
    apply component10_eq_zero_of_trace_pairing P _
      (component10_fixed_of_mem_range P hP (X - Y))
    intro Z
    have he := LinearMap.congr_fun h
      ⟨component01Linear P Z, LinearMap.mem_range_self _ Z⟩
    change trace (X.val * component01 P Z) = trace (Y.val * component01 P Z) at he
    simpa only [Submodule.coe_sub, sub_mul, trace_sub, sub_eq_zero] using he
  apply Subtype.ext
  exact sub_eq_zero.mp hz

theorem oppositeCornerTracePairing_flip_injective (P : Matrix n n K)
    (hP : P * P = P) : Function.Injective (oppositeCornerTracePairing P).flip := by
  intro X Y h
  have hz : (X - Y : LinearMap.range (component01Linear P)).val = 0 := by
    apply component01_eq_zero_of_trace_pairing P _
      (component01_fixed_of_mem_range P hP (X - Y))
    intro Z
    have he := LinearMap.congr_fun h
      ⟨component10Linear P Z, LinearMap.mem_range_self _ Z⟩
    change trace (component10 P Z * X.val) = trace (component10 P Z * Y.val) at he
    rw [trace_mul_comm (component10 P Z) X.val,
      trace_mul_comm (component10 P Z) Y.val] at he
    simpa only [Submodule.coe_sub, sub_mul, trace_sub, sub_eq_zero] using he
  apply Subtype.ext
  exact sub_eq_zero.mp hz

theorem oppositeCornerTracePairing_isPerfPair (P : Matrix n n K) (hP : P * P = P) :
    (oppositeCornerTracePairing P).IsPerfPair :=
  LinearMap.IsPerfPair.of_injective
    (oppositeCornerTracePairing_injective P hP)
    (oppositeCornerTracePairing_flip_injective P hP)

def oppositeCornerTraceDualEquiv (P : Matrix n n K) (hP : P * P = P) :
    LinearMap.range (component10Linear P) ≃ₗ[K]
      Module.Dual K (LinearMap.range (component01Linear P)) := by
  letI := oppositeCornerTracePairing_isPerfPair P hP
  exact (oppositeCornerTracePairing P).toPerfPair

@[simp] theorem oppositeCornerTraceDualEquiv_apply (P : Matrix n n K)
    (hP : P * P = P) (X : LinearMap.range (component10Linear P))
    (Y : LinearMap.range (component01Linear P)) :
    oppositeCornerTraceDualEquiv P hP X Y = trace (X.val * Y.val) := rfl

end InfoGeometry.Core.PeirceDecomposition
