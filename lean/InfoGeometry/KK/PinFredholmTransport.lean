/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.KK.PinLinearDiracTransport
import InfoGeometry.KK.LinearDiracExponentialTransport
import Mathlib.Analysis.Normed.Operator.Fredholm.Open

/-!
# Native Fredholm families under represented Pin transport

This file uses Mathlib's `ContinuousLinearMap.IsFredholm`, including strictness,
closed range, a finite-dimensional kernel, finite-dimensional cokernel, and a
topological complement of the kernel. The index is the native `LinearMap.index`,
with sign convention `dim ker - dim coker`.

Given a genuinely Fredholm bounded source operator, conjugation by the actual
represented Pin units preserves Fredholmness and index. Operator-norm continuity
of the represented unit values constructs a continuous map into the subtype of
Fredholm operators. The existing exponential family gives another such map
without an additional continuity hypothesis.

The source Fredholm hypothesis remains explicit. In particular it is not
inferred merely from compactness of an unbounded operator's resolvent, nor is
the compact resolvent used as the bounded Fredholm operator. No geometric
analytic-index bundle or differential KO class is asserted.
-/

noncomputable section

namespace InfoGeometry.KK.PinFredholmTransport

open InfoGeometry.Clifford.NormalizedVectorPin
open InfoGeometry.Clifford.FreedPinRepresentation
open InfoGeometry.KK.PinLinearDiracTransport
open InfoGeometry.KK.LinearDiracTransport
open Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Native Fredholmness is invariant under continuous linear conjugation. -/
theorem isFredholm_conjugate_iff (e : H ≃L[ℝ] H) (A : H →L[ℝ] H) :
    (e.conjContinuousAlgEquiv A).IsFredholm ↔ A.IsFredholm := by
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
  simp only [ContinuousLinearMap.isFredholm_equiv_comp,
    ContinuousLinearMap.isFredholm_comp_equiv]

/-- Index additivity and the zero index of both actual frame equivalences
give invariance of the native kernel-minus-cokernel index. -/
theorem index_conjugate (e : H ≃L[ℝ] H) (A : H →L[ℝ] H)
    (hA : A.IsFredholm) : (e.conjContinuousAlgEquiv A).index = A.index := by
  change ((e : H →L[ℝ] H).comp (A.comp (e.symm : H →L[ℝ] H))).index = A.index
  rw [e.isFredholm.index_comp (hA.comp e.symm.isFredholm),
    hA.index_comp e.symm.isFredholm]
  have he : (e : H →L[ℝ] H).index = 0 := LinearMap.index_of_bijective e.bijective
  have hi : (e.symm : H →L[ℝ] H).index = 0 :=
    LinearMap.index_of_bijective e.symm.bijective
  rw [he, hi, add_zero, zero_add]

/-- This transport includes actual closed range and finite kernel/cokernel
data, rather than only two chosen zero-mode dimensions. -/
theorem conjugate_fredholm_defects (e : H ≃L[ℝ] H) (A : H →L[ℝ] H)
    (hA : A.IsFredholm) :
    IsClosed ((e.conjContinuousAlgEquiv A).range : Set H) ∧
      FiniteDimensional ℝ (e.conjContinuousAlgEquiv A).ker ∧
      FiniteDimensional ℝ (H ⧸ (e.conjContinuousAlgEquiv A).range) := by
  have h := (isFredholm_conjugate_iff e A).mpr hA
  exact ⟨h.isClosed_range, h.finite_ker, h.finite_coker⟩

section Pin

variable {N : Type*} [AddCommGroup N] [Module ℝ N]
variable (Q : QuadraticForm ℝ N)
variable (ρ : CliffordAlgebra Q →ₐ[ℝ] (H →L[ℝ] H))

theorem pin_isFredholm (A : H →L[ℝ] H) (hA : A.IsFredholm) (g : pin Q) :
    ((continuousPinAction Q ρ g).conjContinuousAlgEquiv A).IsFredholm :=
  (isFredholm_conjugate_iff _ A).mpr hA

theorem pin_index_eq (A : H →L[ℝ] H) (hA : A.IsFredholm) (g : pin Q) :
    ((continuousPinAction Q ρ g).conjContinuousAlgEquiv A).index = A.index :=
  index_conjugate _ A hA

variable [CompleteSpace H]

/-- An actual continuous family valued in the native subtype of Fredholm
operators. A suspended Pin family is obtained by passing `positiveRepresentation`
or `negativeRepresentation` as the algebra action. -/
def pinFredholmFamily {B : Type*} [TopologicalSpace B]
    (g : B → pin Q)
    (hg : Continuous (fun b => (pinRepresentation Q ρ (g b) : H →L[ℝ] H)))
    (A : H →L[ℝ] H) (hA : A.IsFredholm) :
    ContinuousMap B {T : H →L[ℝ] H // T.IsFredholm} where
  toFun b := ⟨(continuousPinAction Q ρ (g b)).conjContinuousAlgEquiv A,
    pin_isFredholm Q ρ A hA (g b)⟩
  continuous_toFun := (continuous_pin_conjugate_family Q ρ g hg A).subtype_mk _

@[simp] theorem pinFredholmFamily_index {B : Type*} [TopologicalSpace B]
    (g : B → pin Q)
    (hg : Continuous (fun b => (pinRepresentation Q ρ (g b) : H →L[ℝ] H)))
    (A : H →L[ℝ] H) (hA : A.IsFredholm) (b : B) :
    (pinFredholmFamily Q ρ g hg A hA b).val.index = A.index :=
  pin_index_eq Q ρ A hA (g b)

/-- Native Banach Fredholm stability controls all sufficiently small operator
perturbations of a transported member, not only its Pin conjugacy orbit. -/
theorem pin_eventually_fredholm_index (A : H →L[ℝ] H) (hA : A.IsFredholm)
    (g : pin Q) :
    ∀ᶠ T in 𝓝 ((continuousPinAction Q ρ g).conjContinuousAlgEquiv A),
      T.IsFredholm ∧ T.index = A.index := by
  have h := pin_isFredholm Q ρ A hA g
  filter_upwards [h.eventually_nhds, h.eventually_nhds_index_eq] with T hT hindex
  exact ⟨hT, hindex.trans (pin_index_eq Q ρ A hA g)⟩

end Pin

section Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual exponential conjugation family is a continuous family of
native Fredholm operators whenever its bounded seed is Fredholm. -/
def exponentialFredholmFamily (G A : E →L[ℝ] E) (hA : A.IsFredholm) :
    ContinuousMap ℝ {T : E →L[ℝ] E // T.IsFredholm} where
  toFun t := ⟨(InfoGeometry.Krein.expAutomorphism G t).conjContinuousAlgEquiv A,
    (isFredholm_conjugate_iff _ A).mpr hA⟩
  continuous_toFun := (continuous_conjugate_expAutomorphism G A).subtype_mk _

@[simp] theorem exponentialFredholmFamily_index (G A : E →L[ℝ] E)
    (hA : A.IsFredholm) (t : ℝ) :
    (exponentialFredholmFamily G A hA t).val.index = A.index :=
  index_conjugate _ A hA

end Exponential

end InfoGeometry.KK.PinFredholmTransport
