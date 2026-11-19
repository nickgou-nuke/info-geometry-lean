/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ParaKahlerLagrangianDimension
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# Perfect cross pairing for projections exchanged by a bilinear adjoint

Let `p` be an idempotent real linear operator. If its bilinear adjoint is
`1 - p`, then its two complementary ranges are totally isotropic. An ambient
nondegenerate bilinear form restricts to a nondegenerate pairing between these
ranges. In finite dimension the cross pairing is perfect: every covector on
one range is represented uniquely by a vector in the other range.

The generic injectivity argument is reused from
`ParaKahlerLagrangianDimension.crossPairing_injective`; the new implication
starts from the exchanged-adjoint equation rather than a para-Kähler package.
No positivity, symmetry, finite matrix representation, or scalar complex
structure is assumed. Finite dimension is used only for perfectness and the
dimension conclusions. In particular, a perfect cross pairing does not mean
that every pair of nonzero vectors has nonzero pairing.
-/

noncomputable section

namespace InfoGeometry.Krein.ExchangedProjectionPairing

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : LinearMap.BilinForm ℝ V) (p : Module.End ℝ V)

/-- The bilinear form restricted to the actual complementary projector ranges. -/
def crossPairing :
    LinearMap.range p →ₗ[ℝ] LinearMap.range (1 - p) →ₗ[ℝ] ℝ :=
  B.domRestrict₁₂ (LinearMap.range p) (LinearMap.range (1 - p))

@[simp] theorem crossPairing_apply
    (x : LinearMap.range p) (y : LinearMap.range (1 - p)) :
    crossPairing B p x y = B x.val y.val := rfl

/-- The range of an idempotent with complementary adjoint is totally isotropic. -/
theorem range_pairing_eq_zero
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (x y : LinearMap.range p) : B x.val y.val = 0 := by
  have hx : p x.val = x.val := (LinearMap.IsIdempotentElem.mem_range_iff hp).mp x.property
  have hy : p y.val = y.val := (LinearMap.IsIdempotentElem.mem_range_iff hp).mp y.property
  calc
    B x.val y.val = B (p x.val) y.val := by rw [hx]
    _ = B x.val ((1 - p) y.val) := hAdj _ _
    _ = 0 := by simp only [LinearMap.sub_apply, Module.End.one_apply, hy,
      sub_self, map_zero]

/-- The complementary range is totally isotropic as well. -/
theorem complement_range_pairing_eq_zero
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (x y : LinearMap.range (1 - p)) : B x.val y.val = 0 := by
  have hx : p x.val = 0 := by
    have hfixed := (LinearMap.IsIdempotentElem.mem_range_iff hp.one_sub).mp x.property
    simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_self] using hfixed
  have hy : (1 - p) y.val = y.val :=
    (LinearMap.IsIdempotentElem.mem_range_iff hp.one_sub).mp y.property
  calc
    B x.val y.val = B x.val ((1 - p) y.val) := by rw [hy]
    _ = B (p x.val) y.val := (hAdj _ _).symm
    _ = 0 := by rw [hx, B.zero_left]

/-- Native complementary ranges with both restricted forms equal to zero. -/
theorem exchangedProjection_isotropic_split
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y)) :
    IsCompl (LinearMap.range p) (LinearMap.range (1 - p)) ∧
      B.restrict (LinearMap.range p) = 0 ∧
      B.restrict (LinearMap.range (1 - p)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp]
    exact LinearMap.IsIdempotentElem.isCompl hp
  · ext x y
    exact range_pairing_eq_zero B p hp hAdj x y
  · ext x y
    exact complement_range_pairing_eq_zero B p hp hAdj x y

/-- Left separation descends to the pairing with the opposite range. -/
theorem crossPairing_injective
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (hB : B.SeparatingLeft) : Function.Injective (crossPairing B p) := by
  apply InfoGeometry.Canonical.ParaKahlerLagrangianDimension.crossPairing_injective B hB
  · intro x hx y hy
    exact range_pairing_eq_zero B p hp hAdj ⟨x, hx⟩ ⟨y, hy⟩
  · exact (exchangedProjection_isotropic_split B p hp hAdj).1.sup_eq_top

/-- Right separation descends independently; symmetry is not required. -/
theorem crossPairing_flip_injective
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (hB : B.SeparatingRight) : Function.Injective (crossPairing B p).flip := by
  change Function.Injective
    (B.flip.domRestrict₁₂ (LinearMap.range (1 - p)) (LinearMap.range p))
  apply InfoGeometry.Canonical.ParaKahlerLagrangianDimension.crossPairing_injective B.flip hB
  · intro x hx y hy
    exact complement_range_pairing_eq_zero B p hp hAdj ⟨y, hy⟩ ⟨x, hx⟩
  · exact (exchangedProjection_isotropic_split B p hp hAdj).1.symm.sup_eq_top

/-- The cross pairing is nondegenerate, including in infinite dimension. -/
theorem crossPairing_nondegenerate
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (hB : B.Nondegenerate) : (crossPairing B p).Nondegenerate := by
  constructor
  · exact LinearMap.separatingLeft_iff_ker_eq_bot.mpr
      (LinearMap.ker_eq_bot_of_injective (crossPairing_injective B p hp hAdj hB.1))
  · exact LinearMap.separatingRight_iff_flip_ker_eq_bot.mpr
      (LinearMap.ker_eq_bot_of_injective (crossPairing_flip_injective B p hp hAdj hB.2))

section FiniteDimension

variable [FiniteDimensional ℝ V]

/-- Finite-dimensional nondegeneracy gives a native perfect cross pairing. -/
theorem crossPairing_isPerfPair
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (hB : B.Nondegenerate) : (crossPairing B p).IsPerfPair :=
  LinearMap.IsPerfPair.of_injective
    (crossPairing_injective B p hp hAdj hB.1)
    (crossPairing_flip_injective B p hp hAdj hB.2)

/-- The actual equivalence from one range to the algebraic dual of its twin. -/
def crossDualEquiv
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (hB : B.Nondegenerate) :
    LinearMap.range p ≃ₗ[ℝ] Module.Dual ℝ (LinearMap.range (1 - p)) := by
  letI := crossPairing_isPerfPair B p hp hAdj hB
  exact (crossPairing B p).toPerfPair

@[simp] theorem crossDualEquiv_apply
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (hB : B.Nondegenerate)
    (x : LinearMap.range p) (y : LinearMap.range (1 - p)) :
    crossDualEquiv B p hp hAdj hB x y = B x.val y.val := rfl

/-- Every covector on the opposite range has a unique bilinear representative. -/
theorem existsUnique_cross_representative
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (hB : B.Nondegenerate)
    (f : Module.Dual ℝ (LinearMap.range (1 - p))) :
    ∃! x : LinearMap.range p,
      ∀ y : LinearMap.range (1 - p), B x.val y.val = f y := by
  let e := crossDualEquiv B p hp hAdj hB
  refine ⟨e.symm f, ?_, ?_⟩
  · intro y
    change e (e.symm f) y = f y
    rw [e.apply_symm_apply]
  · intro x hx
    apply e.injective
    rw [e.apply_symm_apply]
    apply LinearMap.ext
    exact hx

/-- The two isotropic ranges have equal actual dimensions. -/
theorem ranges_finrank_eq
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (hB : B.Nondegenerate) :
    Module.finrank ℝ (LinearMap.range p) =
      Module.finrank ℝ (LinearMap.range (1 - p)) := by
  let := crossPairing_isPerfPair B p hp hAdj hB
  exact Module.finrank_of_isPerfPair (crossPairing B p)

/-- Each range has half the dimension of the ambient real space. -/
theorem two_mul_finrank_range
    (hp : IsIdempotentElem p)
    (hAdj : ∀ x y, B (p x) y = B x ((1 - p) y))
    (hB : B.Nondegenerate) :
    2 * Module.finrank ℝ (LinearMap.range p) = Module.finrank ℝ V := by
  have hsum := Submodule.finrank_add_eq_of_isCompl
    (exchangedProjection_isotropic_split B p hp hAdj).1
  rw [← ranges_finrank_eq B p hp hAdj hB] at hsum
  simpa only [two_mul] using hsum

end FiniteDimension

end InfoGeometry.Krein.ExchangedProjectionPairing
