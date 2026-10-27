/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DecomposableBivector
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Prod

/-!
# Exterior blades recover their incident subspaces

The carrier is Mathlib's exterior algebra.  A blade's support is the kernel
of the native linear map `x ↦ ι x * ω`; no incidence relation is supplied as
an assumption.  A nonzero decomposable blade recovers the span of its frame.
The meet of two recovered subspaces is the kernel of simultaneous wedge
annihilation.  This does not define a volume-dependent regressive product.

The nonvanishing theorem reuses the repository's existing exterior-power
owner rather than constructing another exterior algebra or independence
predicate.  Faithful operator representations may transport these identities
without changing their incidence content.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorBladeIncidence

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The existing exterior-power nonvanishing result, in the exterior algebra. -/
theorem ιMulti_ne_zero_of_linearIndependent {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent K v) :
    ExteriorAlgebra.ιMulti K n v ≠ 0 := by
  intro h
  apply InfoGeometry.Canonical.exteriorPower_ιMulti_ne_zero_of_linearIndependent v hv
  apply Subtype.ext
  exact h

/-- A finite exterior product vanishes exactly for a dependent family. -/
theorem ιMulti_eq_zero_iff {n : ℕ} (v : Fin n → V) :
    ExteriorAlgebra.ιMulti K n v = 0 ↔ ¬LinearIndependent K v := by
  constructor
  · intro h hv
    exact ιMulti_ne_zero_of_linearIndependent v hv h
  · intro h
    exact (ExteriorAlgebra.ιMulti K n).map_linearDependent v h

/-- An independent frame's exterior product detects membership in its span. -/
theorem ι_mul_ιMulti_eq_zero_iff {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent K v) (x : V) :
    ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K n v = 0 ↔
      x ∈ Submodule.span K (Set.range v) := by
  have hw : ExteriorAlgebra.ιMulti K (n + 1) (Matrix.vecCons x v) =
      ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K n v := by
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    rfl
  rw [← hw, ιMulti_eq_zero_iff, linearIndependent_finCons]
  simp only [hv, true_and, not_not]

/-- The linear map whose kernel consists of vectors incident to a blade. -/
def bladeMap (ω : ExteriorAlgebra K V) : V →ₗ[K] ExteriorAlgebra K V :=
  (LinearMap.mulRight K ω).comp (ExteriorAlgebra.ι K)

@[simp] theorem bladeMap_apply (ω : ExteriorAlgebra K V) (x : V) :
    bladeMap ω x = ExteriorAlgebra.ι K x * ω :=
  rfl

/-- Native submodule of vectors whose left exterior product with `ω` vanishes. -/
def bladeSupport (ω : ExteriorAlgebra K V) : Submodule K V :=
  (bladeMap ω).ker

@[simp] theorem mem_bladeSupport (ω : ExteriorAlgebra K V) (x : V) :
    x ∈ bladeSupport ω ↔ ExteriorAlgebra.ι K x * ω = 0 :=
  Iff.rfl

/-- The annihilator support of an independent blade is its actual frame span. -/
theorem bladeSupport_ιMulti {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent K v) :
    bladeSupport (ExteriorAlgebra.ιMulti K n v) =
      Submodule.span K (Set.range v) := by
  ext x
  exact ι_mul_ιMulti_eq_zero_iff v hv x

@[simp] theorem bladeSupport_zero :
    bladeSupport (0 : ExteriorAlgebra K V) = ⊤ := by
  ext x
  simp only [mem_bladeSupport, mul_zero, Submodule.mem_top, iff_self]

@[simp] theorem bladeSupport_one :
    bladeSupport (1 : ExteriorAlgebra K V) = ⊥ := by
  ext x
  simp only [mem_bladeSupport, mul_one, ExteriorAlgebra.ι_eq_zero_iff,
    Submodule.mem_bot]

/-- Nonzero rescaling preserves incidence; the zero scalar is excluded. -/
theorem bladeSupport_smul (ω : ExteriorAlgebra K V) {c : K} (hc : c ≠ 0) :
    bladeSupport (c • ω) = bladeSupport ω := by
  ext x
  simp only [mem_bladeSupport, mul_smul_comm, smul_eq_zero, hc, false_or]

/-- Proportional nonzero-scaled blades have the same annihilator support. -/
theorem bladeSupport_eq_of_proportional {ω η : ExteriorAlgebra K V}
    {c : K} (hc : c ≠ 0) (h : ω = c • η) :
    bladeSupport ω = bladeSupport η := by
  rw [h, bladeSupport_smul η hc]

/-- The native lattice meet is the kernel of simultaneous annihilation. -/
theorem ker_prod_bladeMap (ω η : ExteriorAlgebra K V) :
    ((bladeMap ω).prod (bladeMap η)).ker =
      bladeSupport ω ⊓ bladeSupport η :=
  LinearMap.ker_prod _ _

/-- Intersection of frame spans is detected by two exterior-product equations. -/
theorem mem_span_inf_iff {m n : ℕ} (v : Fin m → V) (w : Fin n → V)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) (x : V) :
    x ∈ Submodule.span K (Set.range v) ⊓ Submodule.span K (Set.range w) ↔
      ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K m v = 0 ∧
        ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K n w = 0 := by
  rw [Submodule.mem_inf,
    ← ι_mul_ιMulti_eq_zero_iff v hv x, ← ι_mul_ιMulti_eq_zero_iff w hw x]

/-- Equal blade rays recover equal subspaces, in arbitrary finite degree. -/
theorem span_eq_of_proportional {m n : ℕ} (v : Fin m → V) (w : Fin n → V)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w)
    {c : K} (hc : c ≠ 0)
    (h : ExteriorAlgebra.ιMulti K m v = c • ExteriorAlgebra.ιMulti K n w) :
    Submodule.span K (Set.range v) = Submodule.span K (Set.range w) := by
  rw [← bladeSupport_ιMulti v hv, ← bladeSupport_ιMulti w hw]
  exact bladeSupport_eq_of_proportional hc h

end InfoGeometry.Projective.ExteriorBladeIncidence
