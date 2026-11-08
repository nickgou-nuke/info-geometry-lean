/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionNullConeTopology

/-!
# Projective null rays of the real split-octonion cone

The nonzero null cone is quotiented by nonzero real rescaling.  This is the
native quotient-topology shadow of a projectivised null boundary.  The file
proves only quotient formation, the canonical projection, and its universal
continuity property; it does not identify the quotient with a homogeneous
space.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.OperatorAlgebra.KreinIsotropicCone
open InfoGeometry.Physics.ZornMatrixSU3
open Topology

abbrev SplitZornNonzeroNull :=
  {X : SplitZornMatrix // X ∈ splitZornNullCone ∧ X ≠ 0}

def splitZornNullRaySetoid : Setoid SplitZornNonzeroNull where
  r X Y := SameProjectiveRay X.1 Y.1
  iseqv := {
    refl := fun X => SameProjectiveRay.refl X.1
    symm := fun h => SameProjectiveRay.symm h
    trans := fun hXY hYZ => SameProjectiveRay.trans hXY hYZ }

instance : Setoid SplitZornNonzeroNull := splitZornNullRaySetoid

abbrev SplitZornNullRay := Quotient (inferInstance : Setoid SplitZornNonzeroNull)

def splitZornNullRayProjection :
    SplitZornNonzeroNull → SplitZornNullRay :=
  Quotient.mk'

theorem splitZornNullRayProjection_continuous :
    Continuous splitZornNullRayProjection := by
  exact continuous_quotient_mk'

theorem splitZornNullRayProjection_isQuotientMap :
    IsQuotientMap splitZornNullRayProjection := by
  exact isQuotientMap_quotient_mk'

theorem splitZornNullRayProjection_surjective :
    Function.Surjective splitZornNullRayProjection := by
  intro q
  refine Quotient.inductionOn q (fun X => ?_)
  exact ⟨X, by rfl⟩

theorem splitZornNullRayProjection_eq_iff
  (X Y : SplitZornNonzeroNull) :
    splitZornNullRayProjection X = splitZornNullRayProjection Y ↔
      SameProjectiveRay X.1 Y.1 := by
  change Quotient.mk' X = Quotient.mk' Y ↔ _
  exact Quotient.eq_iff_equiv

theorem splitZornNullRay_rep_is_null
    (X : SplitZornNonzeroNull) :
    X.1 ∈ splitZornNullCone :=
  X.2.1

theorem splitZornNullRay_rep_ne_zero
    (X : SplitZornNonzeroNull) :
    X.1 ≠ 0 :=
  X.2.2

theorem splitZornNullRay_projection_respects_scaling
    (X : SplitZornNonzeroNull) (r : ℝ) (hr : r ≠ 0)
    (hnull : r • X.1 ∈ splitZornNullCone) :
    splitZornNullRayProjection X =
      splitZornNullRayProjection
        ⟨r • X.1, hnull, smul_ne_zero hr X.2.2⟩ := by
  change Quotient.mk' X = Quotient.mk'
    ⟨r • X.1, hnull, smul_ne_zero hr X.2.2⟩
  apply Quotient.sound
  exact ⟨r, hr, rfl⟩

noncomputable def splitZornNullRayLift
    {Y : Type*} [TopologicalSpace Y]
    (f : SplitZornNonzeroNull → Y)
    (hconst : ∀ X Y,
      SameProjectiveRay X.1 Y.1 → f X = f Y) :
    SplitZornNullRay → Y :=
  Quotient.lift f (by
    intro X Y hXY
    exact hconst X Y hXY)

theorem splitZornNullRayLift_projection
    {Y : Type*} [TopologicalSpace Y]
    (f : SplitZornNonzeroNull → Y)
    (hconst : ∀ X Y,
      SameProjectiveRay X.1 Y.1 → f X = f Y)
    (X : SplitZornNonzeroNull) :
    splitZornNullRayLift f hconst
        (splitZornNullRayProjection X) = f X := by
  rfl

theorem splitZornNullRayLift_continuous
    {Y : Type*} [TopologicalSpace Y]
    (f : SplitZornNonzeroNull → Y)
    (hf : Continuous f)
    (hconst : ∀ X Y,
      SameProjectiveRay X.1 Y.1 → f X = f Y) :
    Continuous (splitZornNullRayLift f hconst) := by
  apply (isQuotientMap_quotient_mk'.continuous_iff).2
  change Continuous (splitZornNullRayLift f hconst ∘ splitZornNullRayProjection)
  have hcomp : splitZornNullRayLift f hconst ∘ splitZornNullRayProjection = f := by
    funext X
    exact splitZornNullRayLift_projection f hconst X
  rw [hcomp]
  exact hf

/-! ## Projective ray maps supplied by the nilpotent representatives

The upper and lower coordinate embeddings already have nullity, nonzero, and
square-zero proofs in `SplitOctonionNullCone`.  This section transports those
specific representatives into the existing ray quotient; it does not identify
the quotient with an ambient compactification boundary or with an operator
algebra carrier.
-/

def upperNullRepresentative (u : {u : Fin 3 → ℝ // u ≠ 0}) : SplitZornNonzeroNull :=
  ⟨upperNull u.1, upperNull_mem u.1, upperNull_ne_zero u.2⟩

def lowerNullRepresentative (u : {u : Fin 3 → ℝ // u ≠ 0}) : SplitZornNonzeroNull :=
  ⟨lowerNull u.1, lowerNull_mem u.1, lowerNull_ne_zero u.2⟩

def upperNullRay (u : {u : Fin 3 → ℝ // u ≠ 0}) : SplitZornNullRay :=
  splitZornNullRayProjection (upperNullRepresentative u)

def lowerNullRay (u : {u : Fin 3 → ℝ // u ≠ 0}) : SplitZornNullRay :=
  splitZornNullRayProjection (lowerNullRepresentative u)

theorem continuous_upperNull :
    Continuous (upperNull : (Fin 3 → ℝ) → SplitZornMatrix) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun u : Fin 3 → ℝ => ((0, 0), (u, 0)))
  exact (continuous_const.prodMk continuous_const).prodMk
    (continuous_id.prodMk continuous_const)

theorem continuous_lowerNull :
    Continuous (lowerNull : (Fin 3 → ℝ) → SplitZornMatrix) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun u : Fin 3 → ℝ => ((0, 0), (0, u)))
  exact (continuous_const.prodMk continuous_const).prodMk
    (continuous_const.prodMk continuous_id)

theorem continuous_upperNullRepresentative :
    Continuous upperNullRepresentative := by
  apply Continuous.subtype_mk
  exact continuous_upperNull.comp continuous_subtype_val

theorem continuous_lowerNullRepresentative :
    Continuous lowerNullRepresentative := by
  apply Continuous.subtype_mk
  exact continuous_lowerNull.comp continuous_subtype_val

theorem continuous_upperNullRay : Continuous upperNullRay :=
  splitZornNullRayProjection_continuous.comp continuous_upperNullRepresentative

theorem continuous_lowerNullRay : Continuous lowerNullRay :=
  splitZornNullRayProjection_continuous.comp continuous_lowerNullRepresentative

theorem upperNullRay_eq_iff (u v : {u : Fin 3 → ℝ // u ≠ 0}) :
    upperNullRay u = upperNullRay v ↔
      ∃ r : ℝ, r ≠ 0 ∧ v.1 = r • u.1 := by
  change splitZornNullRayProjection (upperNullRepresentative u) =
      splitZornNullRayProjection (upperNullRepresentative v) ↔ _
  rw [splitZornNullRayProjection_eq_iff]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, ?_⟩
    change upperNull v.1 = r • upperNull u.1 at h
    have hx := congrArg (fun X : SplitZornMatrix => X.x) h
    simpa [upperNull] using hx
  · rintro ⟨r, hr, hv⟩
    refine ⟨r, hr, ?_⟩
    change upperNull v.1 = r • upperNull u.1
    rw [hv]
    apply InfoGeometry.Physics.ZornMatrixSU3.ext <;>
      simp [upperNull]

theorem lowerNullRay_eq_iff (u v : {u : Fin 3 → ℝ // u ≠ 0}) :
    lowerNullRay u = lowerNullRay v ↔
      ∃ r : ℝ, r ≠ 0 ∧ v.1 = r • u.1 := by
  change splitZornNullRayProjection (lowerNullRepresentative u) =
      splitZornNullRayProjection (lowerNullRepresentative v) ↔ _
  rw [splitZornNullRayProjection_eq_iff]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, ?_⟩
    change lowerNull v.1 = r • lowerNull u.1 at h
    have hy := congrArg (fun X : SplitZornMatrix => X.y) h
    simpa [lowerNull] using hy
  · rintro ⟨r, hr, hv⟩
    refine ⟨r, hr, ?_⟩
    change lowerNull v.1 = r • lowerNull u.1
    rw [hv]
    apply InfoGeometry.Physics.ZornMatrixSU3.ext <;>
      simp [lowerNull]

theorem upperNullRepresentative_square_zero (u : {u : Fin 3 → ℝ // u ≠ 0}) :
    (upperNullRepresentative u).1 * (upperNullRepresentative u).1 = 0 :=
  upperNull_sq u.1

theorem lowerNullRepresentative_square_zero (u : {u : Fin 3 → ℝ // u ≠ 0}) :
    (lowerNullRepresentative u).1 * (lowerNullRepresentative u).1 = 0 :=
  lowerNull_sq u.1

end InfoGeometry.Canonical
