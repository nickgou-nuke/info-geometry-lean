import Mathlib
import InfoGeometry.Canonical.SplitOctonionNullConeAffineCoordinates

/-!
# The second affine chart and the overlap transition

The chart `b ≠ 0` is normalized by `b = 1`.  Its null representatives are
`(u · v, 1, u, v)`.  On the overlap with the `a = 1` chart, the coordinate
transition is the common rescaling by `(u · v)⁻¹`; the transition is an
involution.  This is a local gluing statement, not a global projective atlas.
-/

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.OperatorAlgebra.KreinIsotropicCone
open InfoGeometry.Physics.ZornMatrixSU3

abbrev SplitZornBNormalizedNull :=
  {X : SplitZornNonzeroNull // (X.1 : SplitZornMatrix).b = 1}

def splitZornBNormalizedCoordinates
    (X : SplitZornBNormalizedNull) : SplitZornAffineCoordinates :=
  ((X.1 : SplitZornMatrix).x, (X.1 : SplitZornMatrix).y)

def splitZornBNormalizedRepresentative
    (u v : Fin 3 → ℝ) : SplitZornMatrix where
  a := InfoGeometry.Physics.ZornMatrixSU3.dotProduct u v
  b := 1
  x := u
  y := v

theorem splitZornBNormalizedRepresentative_mem
    (u v : Fin 3 → ℝ) :
    splitZornBNormalizedRepresentative u v ∈ splitZornNullCone := by
  rw [mem_splitZornNullCone_iff]
  simp [splitZornBNormalizedRepresentative]

theorem splitZornBNormalizedRepresentative_ne_zero
    (u v : Fin 3 → ℝ) :
    splitZornBNormalizedRepresentative u v ≠ 0 := by
  intro h
  have hb := congrArg (fun X : SplitZornMatrix => X.b) h
  simpa [splitZornBNormalizedRepresentative] using hb

def splitZornBNormalizedPoint
    (u v : Fin 3 → ℝ) : SplitZornBNormalizedNull :=
  ⟨⟨splitZornBNormalizedRepresentative u v,
      splitZornBNormalizedRepresentative_mem u v,
      splitZornBNormalizedRepresentative_ne_zero u v⟩, by rfl⟩

@[simp] theorem splitZornBNormalizedPoint_b
    (u v : Fin 3 → ℝ) :
    ((splitZornBNormalizedPoint u v).1 : SplitZornMatrix).b = 1 := by
  rfl

theorem splitZornBNormalizedNull_eq_point
    (X : SplitZornBNormalizedNull) :
    splitZornBNormalizedPoint
        (splitZornBNormalizedCoordinates X).1
        (splitZornBNormalizedCoordinates X).2 = X := by
  apply Subtype.ext
  apply Subtype.ext
  apply InfoGeometry.Physics.ZornMatrixSU3.ext
  · have hnull := (mem_splitZornNullCone_iff (X.1 : SplitZornMatrix)).mp X.1.2.1
    simpa [splitZornBNormalizedCoordinates,
      splitZornBNormalizedPoint, splitZornBNormalizedRepresentative, X.2]
      using hnull.symm
  · simpa [splitZornBNormalizedPoint,
      splitZornBNormalizedRepresentative] using X.2.symm
  · rfl
  · rfl

@[simp] theorem splitZornBNormalizedCoordinates_point
    (u v : Fin 3 → ℝ) :
    splitZornBNormalizedCoordinates (splitZornBNormalizedPoint u v) = (u, v) := by
  rfl

abbrev SplitZornAffineOverlapCoordinates :=
  {uv : SplitZornAffineCoordinates //
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1 uv.2 ≠ 0}

def splitZornAffineTransition
    (uv : SplitZornAffineOverlapCoordinates) : SplitZornAffineOverlapCoordinates := by
  let d := InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1.1 uv.1.2
  refine ⟨(d⁻¹ • uv.1.1, d⁻¹ • uv.1.2), ?_⟩
  rw [InfoGeometry.Physics.ZornMatrixSU3.dotProduct_smul_left,
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct_smul_right]
  rw [show InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1.1 uv.1.2 = d by rfl]
  change d⁻¹ * (d⁻¹ * d) ≠ 0
  exact mul_ne_zero (inv_ne_zero uv.2)
    (mul_ne_zero (inv_ne_zero uv.2) uv.2)

theorem continuous_splitZornAffineTransition :
    Continuous splitZornAffineTransition := by
  let hdot : Continuous (fun uv : SplitZornAffineOverlapCoordinates =>
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1.1 uv.1.2) :=
    continuous_splitZornDotProductCoordinates.comp continuous_subtype_val
  have hinv : Continuous (fun uv : SplitZornAffineOverlapCoordinates =>
      (InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1.1 uv.1.2)⁻¹) :=
    hdot.inv₀ (fun uv => uv.2)
  have hu : Continuous (fun uv : SplitZornAffineOverlapCoordinates =>
      (InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1.1 uv.1.2)⁻¹ • uv.1.1) :=
    hinv.smul (continuous_fst.comp continuous_subtype_val)
  have hv : Continuous (fun uv : SplitZornAffineOverlapCoordinates =>
      (InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1.1 uv.1.2)⁻¹ • uv.1.2) :=
    hinv.smul (continuous_snd.comp continuous_subtype_val)
  apply Continuous.subtype_mk
  · exact hu.prodMk hv

@[simp] theorem splitZornAffineTransition_involutive
    (uv : SplitZornAffineOverlapCoordinates) :
    splitZornAffineTransition (splitZornAffineTransition uv) = uv := by
  apply Subtype.ext
  let d := InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1.1 uv.1.2
  have hd : d ≠ 0 := uv.2
  have hdot : InfoGeometry.Physics.ZornMatrixSU3.dotProduct
      (d⁻¹ • uv.1.1) (d⁻¹ • uv.1.2) = d⁻¹ := by
    rw [InfoGeometry.Physics.ZornMatrixSU3.dotProduct_smul_left,
      InfoGeometry.Physics.ZornMatrixSU3.dotProduct_smul_right]
    rw [show InfoGeometry.Physics.ZornMatrixSU3.dotProduct uv.1.1 uv.1.2 = d by rfl]
    field_simp [hd]
  simp [splitZornAffineTransition, d, hdot, hd]

end

end InfoGeometry.Canonical
