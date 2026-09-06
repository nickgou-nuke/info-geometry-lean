import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/--
A Zorn cell representing split-octonion coordinates.

The coordinates represent the vector matrix

  [ r   x ]
  [ y   s ]

where `x = (x1,x2,x3)` and `y = (y1,y2,y3)`.
-/
structure ZornCell (R : Type*) where
  r : R
  s : R
  x1 : R
  x2 : R
  x3 : R
  y1 : R
  y2 : R
  y3 : R

namespace ZornCell

variable {R : Type*} [CommRing R]

/-- The Zorn determinant / split-octonion norm. -/
def detZ (X : ZornCell R) : R :=
  X.r * X.s - (X.x1 * X.y1 + X.x2 * X.y2 + X.x3 * X.y3)

/--
The Zorn product.

Important sign: the lower-left cross term is `- (X.x × Y.x)`.
With the opposite sign, determinant multiplicativity is false.
-/
def mulZ (X Y : ZornCell R) : ZornCell R :=
  {
    r := X.r * Y.r + (X.x1 * Y.y1 + X.x2 * Y.y2 + X.x3 * Y.y3)

    s := (X.y1 * Y.x1 + X.y2 * Y.x2 + X.y3 * Y.x3) + X.s * Y.s

    x1 := X.r * Y.x1 + Y.s * X.x1 + (X.y2 * Y.y3 - X.y3 * Y.y2)
    x2 := X.r * Y.x2 + Y.s * X.x2 + (X.y3 * Y.y1 - X.y1 * Y.y3)
    x3 := X.r * Y.x3 + Y.s * X.x3 + (X.y1 * Y.y2 - X.y2 * Y.y1)

    y1 := Y.r * X.y1 + X.s * Y.y1 - (X.x2 * Y.x3 - X.x3 * Y.x2)
    y2 := Y.r * X.y2 + X.s * Y.y2 - (X.x3 * Y.x1 - X.x1 * Y.x3)
    y3 := Y.r * X.y3 + X.s * Y.y3 - (X.x1 * Y.x2 - X.x2 * Y.x1)
  }

/--
The Zorn composition theorem:

  detZ (X ⋆ Y) = detZ X * detZ Y.
-/
theorem detZ_mulZ (X Y : ZornCell R) :
    detZ (mulZ X Y) = detZ X * detZ Y := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x'1, x'2, x'3, y'1, y'2, y'3⟩
  unfold detZ mulZ
  ring

/--
Negative logarithmic Zorn volume.

This is only geometrically a barrier on the non-isotropic positive/nonzero
determinant stratum. In Lean, `Real.log 0 = 0`, so domain conditions are
carried by theorems that use it.
-/
noncomputable def negLogVolume (X : ZornCell ℝ) : ℝ :=
  -Real.log (detZ X)

/--
Radon--Nikodym-type relative Zorn volume:
`relativeVolumeRN X Y = detZ Y / detZ X`.
-/
noncomputable def relativeVolumeRN (X Y : ZornCell ℝ) : ℝ :=
  detZ Y / detZ X

/--
The negative log Radon--Nikodym volume is the difference of the
negative log-volume potential.
-/
theorem negLog_relativeVolumeRN_eq_negLogVolume_sub
    (X Y : ZornCell ℝ)
    (hX : detZ X ≠ 0) (hY : detZ Y ≠ 0) :
    -Real.log (relativeVolumeRN X Y) =
      negLogVolume Y - negLogVolume X := by
  unfold relativeVolumeRN negLogVolume
  rw [Real.log_div hY hX]
  ring

/--
Multiplicativity of `detZ` turns the Zorn product into multiplicative
relative-volume transport:
`det(X ⋆ Y) / det(X) = det(Y)`.
-/
theorem relativeVolumeRN_mulZ_left
    (X Y : ZornCell ℝ)
    (hX : detZ X ≠ 0) :
    relativeVolumeRN X (mulZ X Y) = detZ Y := by
  unfold relativeVolumeRN
  rw [detZ_mulZ X Y]
  field_simp [hX]

/--
The negative logarithmic volume change under left Zorn multiplication is
the negative log determinant of the multiplier.
-/
theorem negLog_relativeVolumeRN_mulZ_left
    (X Y : ZornCell ℝ)
    (hX : detZ X ≠ 0)
    (hY : detZ Y ≠ 0) :
    -Real.log (relativeVolumeRN X (mulZ X Y)) = negLogVolume Y := by
  rw [relativeVolumeRN_mulZ_left X Y hX]
  rfl

/--
Additivity of `log detZ` on the non-isotropic Zorn stratum.
-/
theorem log_detZ_mulZ
    (X Y : ZornCell ℝ)
    (hX : detZ X ≠ 0) (hY : detZ Y ≠ 0) :
    Real.log (detZ (mulZ X Y)) =
      Real.log (detZ X) + Real.log (detZ Y) := by
  rw [detZ_mulZ X Y]
  exact Real.log_mul hX hY

/--
The negative log-volume is additive under Zorn composition on the
non-isotropic stratum.
-/
theorem negLogVolume_mulZ
    (X Y : ZornCell ℝ)
    (hX : detZ X ≠ 0) (hY : detZ Y ≠ 0) :
    negLogVolume (mulZ X Y) = negLogVolume X + negLogVolume Y := by
  unfold negLogVolume
  rw [log_detZ_mulZ X Y hX hY]
  ring

end ZornCell
