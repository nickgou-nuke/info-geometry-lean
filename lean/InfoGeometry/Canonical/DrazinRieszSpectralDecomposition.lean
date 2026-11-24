/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinCoreFlow
import InfoGeometry.Canonical.DrazinInfiniteCore

/-!
# Fitting range/kernel identification of the Riesz–Drazin spectral projectors

Motivated by the retrieved Drazin/Riesz spectral-decomposition literature
(`2208.09149v1`, `on_drazin.pdf`; retrieval context only — every statement below
is proved in Lean).  For a Drazin witness `Aᴰ` of index `k` the core projector
`P = A Aᴰ` and the defect (zero-spectral) projector `Q = 1 - A Aᴰ` split the
space into stabilized range and generalized-kernel pieces.  The owner
`DrazinCoreFlow` already proves `range Q = ker(A^k)`.  This module adds the
three complementary Fitting identifications:

* `range (A Aᴰ) = range (A^k)`  (core projector range),
* `ker (A Aᴰ) = ker (A^k)`      (core projector kernel),
* `ker (1 - A Aᴰ) = range (A^k)` (defect projector kernel).

Together these give the full Fitting picture: `P` projects onto the stabilized
range and `Q` onto the stabilized kernel, and each is the kernel of the other.
No Drazin-index minimality is claimed; `k` is a witness index.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinRieszSpectralDecomposition

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable {A D : Module.End K V} {k : ℕ}

private theorem core_mul_pow_eq_pow (h : IsDrazinInverse A D k) :
    (A * D) * A ^ k = A ^ k := by
  have hc : Commute D (A ^ k) := (show Commute D A from h.comm.symm).pow_right k
  calc
    (A * D) * A ^ k = A * (D * A ^ k) := by rw [mul_assoc]
    _ = A * (A ^ k * D) := by rw [hc.eq]
    _ = (A * A ^ k) * D := by rw [mul_assoc]
    _ = A ^ (k + 1) * D := by rw [← pow_succ']
    _ = A ^ k := h.power

private theorem pow_mul_core_mul_eq_pow (h : IsDrazinInverse A D k) :
    A ^ k * (A * D) = A ^ k := by
  calc
    A ^ k * (A * D) = (A ^ k * A) * D := by rw [mul_assoc]
    _ = A ^ (k + 1) * D := by rw [pow_succ]
    _ = A ^ k := h.power

/--
The core projector `A Aᴰ` has the same range as the stabilized power `A^k`.

This is the range half of the Fitting identification dual to the already-owned
`complementaryProjection_range_eq_drazinCore`.
-/
@[rep_depth operator]
theorem projection_range_eq_pow_range (h : IsDrazinInverse A D k) :
    LinearMap.range (projection A D) = LinearMap.range (A ^ k) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨(A * D ^ (k + 1)) x, ?_⟩
    have hb_apply : D x = ((D ^ (k + 1)) * (A ^ k)) x := by
      simpa using congrArg (fun f : Module.End K V => f x)
        (inverse_eq_pow_mul_pow (h := h) k)
    have hAkA : Commute (A ^ k) A := (Commute.refl A).pow_left k
    have hAkD : Commute (A ^ k) (D ^ (k + 1)) :=
      (show Commute A D from h.comm).pow_right (k + 1) |>.pow_left k
    have hc : Commute (A ^ k) (A * D ^ (k + 1)) := hAkA.mul_right hAkD
    calc
      (A ^ k) ((A * D ^ (k + 1)) x) = ((A ^ k * (A * D ^ (k + 1))) x) := rfl
      _ = (((A * D ^ (k + 1)) * A ^ k) x) := by rw [hc.eq]
      _ = (A * D ^ (k + 1)) ((A ^ k) x) := rfl
      _ = A ((D ^ (k + 1)) ((A ^ k) x)) := rfl
      _ = A (((D ^ (k + 1)) * (A ^ k)) x) := rfl
      _ = A (D x) := by rw [hb_apply]
      _ = (A * D) x := rfl
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨(A ^ k) x, ?_⟩
    calc
      (projection A D) ((A ^ k) x) = ((A * D) * A ^ k) x := rfl
      _ = (A ^ k) x := by rw [core_mul_pow_eq_pow (h := h)]

/--
The core projector `A Aᴰ` has kernel exactly the stabilized kernel `ker(A^k)`.
-/
@[rep_depth operator]
theorem projection_ker_eq_pow_ker (h : IsDrazinInverse A D k) :
    LinearMap.ker (projection A D) = LinearMap.ker (A ^ k) := by
  ext x
  constructor
  · intro hx
    change (projection A D) x = 0 at hx
    change (A ^ k) x = 0
    calc
      (A ^ k) x = (A ^ k * (A * D)) x := by rw [pow_mul_core_mul_eq_pow (h := h)]
      _ = (A ^ k) ((A * D) x) := rfl
      _ = (A ^ k) 0 := by rw [show (A * D) x = 0 from hx]
      _ = 0 := by simp
  · intro hx
    change (A ^ k) x = 0 at hx
    change (projection A D) x = 0
    have hb_apply : D x = ((D ^ (k + 1)) * (A ^ k)) x := by
      simpa using congrArg (fun f : Module.End K V => f x)
        (inverse_eq_pow_mul_pow (h := h) k)
    calc
      (projection A D) x = (A * D) x := rfl
      _ = A (D x) := rfl
      _ = A (((D ^ (k + 1)) * (A ^ k)) x) := by rw [hb_apply]
      _ = A ((D ^ (k + 1)) ((A ^ k) x)) := rfl
      _ = A ((D ^ (k + 1)) 0) := by rw [hx]
      _ = 0 := by simp

/--
The defect projector `Q = 1 - A Aᴰ` has kernel exactly the stabilized range
`range(A^k)`.  Together with the owned `range Q = ker(A^k)` this says the two
Drazin projectors are mutually the range/kernel projections of the Fitting
split.
-/
@[rep_depth operator]
theorem complementaryProjection_ker_eq_pow_range (h : IsDrazinInverse A D k) :
    LinearMap.ker (complementaryProjection A D) = LinearMap.range (A ^ k) := by
  apply le_antisymm
  · intro y hy
    change (complementaryProjection A D) y = 0 at hy
    have hzero : y - (projection A D) y = 0 := by
      simpa [complementaryProjection] using hy
    have hy_eq : (projection A D) y = y := (sub_eq_zero.mp hzero).symm
    rw [← projection_range_eq_pow_range (h := h)]
    exact ⟨y, hy_eq⟩
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    change (complementaryProjection A D) ((A ^ k) x) = 0
    calc
      (complementaryProjection A D) ((A ^ k) x) =
          ((1 : Module.End K V) - A * D) ((A ^ k) x) := rfl
      _ = (A ^ k) x - ((A * D) * A ^ k) x := by rfl
      _ = (A ^ k) x - (A ^ k) x := by rw [core_mul_pow_eq_pow (h := h)]
      _ = 0 := sub_self _

end InfoGeometry.Canonical.DrazinRieszSpectralDecomposition
