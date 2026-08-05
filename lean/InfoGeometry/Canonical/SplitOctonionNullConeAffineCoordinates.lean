import Mathlib
import InfoGeometry.Canonical.SplitOctonionNullConeAffineChart

/-!
# Coordinates on the normalized affine null-cone section

The open projective patch `a ≠ 0` admits the canonical section `a = 1`.
This owner identifies that section algebraically with two colour vectors
`u,v : Fin 3 → ℝ`; the null equation determines the remaining scalar as
`b = u · v`.  It deliberately records a local chart, not a global atlas.
-/

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.OperatorAlgebra.KreinIsotropicCone
open InfoGeometry.Physics.ZornMatrixSU3

abbrev SplitZornNormalizedNull :=
  {X : SplitZornNonzeroNull // (X.1 : SplitZornMatrix).a = 1}

abbrev SplitZornAffineCoordinates :=
  (Fin 3 → ℝ) × (Fin 3 → ℝ)

def splitZornNormalizedCoordinates
    (X : SplitZornNormalizedNull) : SplitZornAffineCoordinates :=
  ((X.1 : SplitZornMatrix).x, (X.1 : SplitZornMatrix).y)

def splitZornAffineCoordinatesPoint
    (uv : SplitZornAffineCoordinates) : SplitZornNormalizedNull :=
  ⟨splitZornAffineNullPoint uv.1 uv.2, by
    rfl⟩

theorem continuous_splitZornNormalizedCoordinates :
    Continuous splitZornNormalizedCoordinates := by
  exact
    ((continuous_splitZorn_x.comp
        (continuous_subtype_val.comp continuous_subtype_val)).prodMk
      (continuous_splitZorn_y.comp
        (continuous_subtype_val.comp continuous_subtype_val)))

theorem continuous_splitZornDotProductCoordinates :
    Continuous (fun uv : SplitZornAffineCoordinates =>
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1 uv.2) := by
  have h00 : Continuous (fun uv : SplitZornAffineCoordinates => uv.1 0) :=
    (continuous_apply 0).comp continuous_fst
  have h01 : Continuous (fun uv : SplitZornAffineCoordinates => uv.2 0) :=
    (continuous_apply 0).comp continuous_snd
  have h10 : Continuous (fun uv : SplitZornAffineCoordinates => uv.1 1) :=
    (continuous_apply 1).comp continuous_fst
  have h11 : Continuous (fun uv : SplitZornAffineCoordinates => uv.2 1) :=
    (continuous_apply 1).comp continuous_snd
  have h20 : Continuous (fun uv : SplitZornAffineCoordinates => uv.1 2) :=
    (continuous_apply 2).comp continuous_fst
  have h21 : Continuous (fun uv : SplitZornAffineCoordinates => uv.2 2) :=
    (continuous_apply 2).comp continuous_snd
  simpa [InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3] using
    ((h00.mul h01).add (h10.mul h11) |>.add (h20.mul h21))

@[simp] theorem splitZornNormalizedCoordinates_point
    (uv : SplitZornAffineCoordinates) :
    splitZornNormalizedCoordinates
        (splitZornAffineCoordinatesPoint uv) = uv := by
  rfl

theorem splitZornNormalizedNull_eq_point
    (X : SplitZornNormalizedNull) :
    splitZornAffineCoordinatesPoint
        (splitZornNormalizedCoordinates X) = X := by
  apply Subtype.ext
  apply Subtype.ext
  apply InfoGeometry.Physics.ZornMatrixSU3.ext
  · simpa [splitZornAffineCoordinatesPoint, splitZornAffineNullPoint,
      splitZornAffineNullRepresentative] using X.2.symm
  · have hnull := (mem_splitZornNullCone_iff (X.1 : SplitZornMatrix)).mp X.1.2.1
    simpa [splitZornNormalizedCoordinates,
      splitZornAffineCoordinatesPoint, splitZornAffineNullPoint,
      splitZornAffineNullRepresentative, X.2] using hnull.symm
  · rfl
  · rfl

theorem continuous_splitZornAffineCoordinatesPoint :
    Continuous splitZornAffineCoordinatesPoint := by
  apply Continuous.subtype_mk
  · apply Continuous.subtype_mk
    · apply continuous_induced_rng.mpr
      change Continuous (fun uv : SplitZornAffineCoordinates =>
        ((1, InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1 uv.2), uv.1, uv.2))
      exact
        ((continuous_const.prodMk continuous_splitZornDotProductCoordinates).prodMk
          (continuous_fst.prodMk continuous_snd))

def splitZornNormalizedNullRayProjection :
    SplitZornNormalizedNull → SplitZornNullRay :=
  fun X => splitZornNullRayProjection X.1

theorem continuous_splitZornNormalizedNullRayProjection :
    Continuous splitZornNormalizedNullRayProjection := by
  exact splitZornNullRayProjection_continuous.comp continuous_subtype_val

theorem splitZornNormalizedNullRayProjection_injective :
    Function.Injective splitZornNormalizedNullRayProjection := by
  intro X Y hXY
  have hsame : SameProjectiveRay X.1.1 Y.1.1 :=
    (splitZornNullRayProjection_eq_iff X.1 Y.1).mp hXY
  rcases hsame with ⟨r, hr, hscale⟩
  have ha := congrArg (fun Z : SplitZornMatrix => Z.a) hscale
  have hr_one : r = 1 := by
    simpa [X.2, Y.2] using ha.symm
  subst r
  apply Subtype.ext
  apply Subtype.ext
  simpa using hscale.symm

theorem splitZornNormalizedNullRayProjection_range_iff
    (q : SplitZornNullRay) :
    q ∈ Set.range splitZornNormalizedNullRayProjection ↔
      ∃ X : SplitZornNonzeroNull,
        splitZornNullRayProjection X = q ∧
          (X : SplitZornMatrix).a ≠ 0 := by
  constructor
  · rintro ⟨Y, rfl⟩
    refine ⟨Y.1, rfl, ?_⟩
    rw [Y.2]
    norm_num
  · rintro ⟨X, hq, ha⟩
    let C : SplitZornAffineNullChart := ⟨X, ha⟩
    let Y : SplitZornNormalizedNull :=
      ⟨splitZornNullNormalize C, splitZornNullNormalize_a C⟩
    refine ⟨Y, ?_⟩
    change splitZornNullRayProjection Y.1 = q
    calc
      splitZornNullRayProjection Y.1 = splitZornNullRayProjection X := by
        simpa [Y] using (splitZornNullNormalize_projection_eq C).symm
      _ = q := hq

noncomputable def splitZornNormalizedNullEquiv :
    SplitZornNormalizedNull ≃ SplitZornAffineCoordinates where
  toFun := splitZornNormalizedCoordinates
  invFun := splitZornAffineCoordinatesPoint
  left_inv := splitZornNormalizedNull_eq_point
  right_inv := splitZornNormalizedCoordinates_point

noncomputable def splitZornNormalizedNullHomeomorph :
    SplitZornNormalizedNull ≃ₜ SplitZornAffineCoordinates :=
  { splitZornNormalizedNullEquiv with
    continuous_toFun := continuous_splitZornNormalizedCoordinates
    continuous_invFun := continuous_splitZornAffineCoordinatesPoint }

@[simp] theorem splitZornNormalizedNullHomeomorph_apply
    (X : SplitZornNormalizedNull) :
    splitZornNormalizedNullHomeomorph X =
      splitZornNormalizedCoordinates X :=
  rfl

@[simp] theorem splitZornNormalizedNullHomeomorph_symm_apply
    (uv : SplitZornAffineCoordinates) :
    splitZornNormalizedNullHomeomorph.symm uv =
      splitZornAffineCoordinatesPoint uv :=
  rfl

end

end InfoGeometry.Canonical
