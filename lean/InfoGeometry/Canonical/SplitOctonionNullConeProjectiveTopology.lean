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
  simpa [Function.comp_def, splitZornNullRayProjection,
    splitZornNullRayLift] using hf

end InfoGeometry.Canonical
