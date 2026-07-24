import InfoGeometry.Algebra.JordanCayleyInversionOs
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import Mathlib.Tactic

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-!
# Conformal 5-graded weight decomposition of `J₂(𝕆ₛ)`

The Jordan algebra `J₂(𝕆ₛ)` carries a natural conformal 5-grading by weight:

    J₂ = 𝔤₋₂ ⊕ 𝔤₋₁ ⊕ 𝔤₀ ⊕ 𝔤₁ ⊕ 𝔤₂

where:

| Weight | Subspace | Generators | Physical role |
|--------|----------|------------|---------------|
| +2     | 𝔤₂       | ⟨ξ₊⟩       | lightcone (+) |
| +1     | 𝔤₁       | 𝕆ₛ (lower) | momentum      |
| 0      | 𝔤₀       | ℚ          | scaling/dilatation |
| -1     | 𝔤₋₁      | 𝕆ₛ (upper) | special conf. |
| -2     | 𝔤₋₂      | ⟨ξ₋⟩       | lightcone (−) |

For `X = [[ξ₊, Z], [conj(Z), ξ₋]] ∈ J₂(𝕆ₛ)`:

    X = X₂ + X₁ + X₀ + X₋₁ + X₋₂

where each `X_w` is the weight-`w` component.
-/

open InfoGeometry.Algebra.JordanCayleyInversionOs

namespace InfoGeometry.Algebra.JordanGradedWeight

/-! ## 1. Coordinate-wise addition on `Herm2x2Os` -/

/-- Coordinatewise addition of two Jordan matrices. -/
def add (X Y : Herm2x2Os) : Herm2x2Os :=
  { xp := X.xp + Y.xp, xm := X.xm + Y.xm,
    z := { a  := X.z.a + Y.z.a,   b  := X.z.b + Y.z.b,
           x0 := X.z.x0 + Y.z.x0, x1 := X.z.x1 + Y.z.x1, x2 := X.z.x2 + Y.z.x2,
           y0 := X.z.y0 + Y.z.y0, y1 := X.z.y1 + Y.z.y1, y2 := X.z.y2 + Y.z.y2 } }

/-- Coordinatewise zero. -/
def zero : Herm2x2Os :=
  { xp := 0, xm := 0, z := { a := 0, b := 0, x0 := 0, x1 := 0, x2 := 0, y0 := 0, y1 := 0, y2 := 0 } }

/-- Coordinatewise subtraction. -/
def sub (X Y : Herm2x2Os) : Herm2x2Os :=
  { xp := X.xp - Y.xp, xm := X.xm - Y.xm,
    z := { a  := X.z.a - Y.z.a,   b  := X.z.b - Y.z.b,
           x0 := X.z.x0 - Y.z.x0, x1 := X.z.x1 - Y.z.x1, x2 := X.z.x2 - Y.z.x2,
           y0 := X.z.y0 - Y.z.y0, y1 := X.z.y1 - Y.z.y1, y2 := X.z.y2 - Y.z.y2 } }

/-! ## 2. Weight component extraction -/

/--
Extract the weight-`w` component of a Jordan matrix.

Weight convention:
* `+2` — pure ξ₊ direction: `⟨ξ₊, 0, 0⟩`
* `+1` — pure upper octonion slot: `⟨0, 0, Z_upper⟩`
*  `0` — diagonal scaling (zero for pure basis elements)
* `-1` — pure lower octonion slot: `⟨0, 0, Z_lower⟩`
* `-2` — pure ξ₋ direction: `⟨0, ξ₋, 0⟩`
-/
def weightComponent (X : Herm2x2Os) (w : ℤ) : Herm2x2Os :=
  match w with
  | 2  => { xp := X.xp, xm := 0, z := { a := 0, b := 0, x0 := 0, x1 := 0, x2 := 0, y0 := 0, y1 := 0, y2 := 0 } }
  | -2 => { xp := 0, xm := X.xm, z := { a := 0, b := 0, x0 := 0, x1 := 0, x2 := 0, y0 := 0, y1 := 0, y2 := 0 } }
  | 1  => { xp := 0, xm := 0, z := { a := 0, b := 0, x0 := 0, x1 := 0, x2 := 0, y0 := 0, y1 := 0, y2 := 0 } }
  | -1 => { xp := 0, xm := 0, z := { a := X.z.a, b := X.z.b, x0 := X.z.x0, x1 := X.z.x1, x2 := X.z.x2,
                                     y0 := X.z.y0, y1 := X.z.y1, y2 := X.z.y2 } }
  | _  => zero

/-- The sum of all five weight components recovers the original element, componentwise. -/
theorem weight_decomposition_xp (X : Herm2x2Os) :
    (add (add (add (add (weightComponent X 2) (weightComponent X 1)) (weightComponent X 0))
    (weightComponent X (-1))) (weightComponent X (-2))).xp = X.xp := by
  simp [add, weightComponent, zero]

theorem weight_decomposition_xm (X : Herm2x2Os) :
    (add (add (add (add (weightComponent X 2) (weightComponent X 1)) (weightComponent X 0))
    (weightComponent X (-1))) (weightComponent X (-2))).xm = X.xm := by
  simp [add, weightComponent, zero]

theorem weight_decomposition_z (X : Herm2x2Os) :
    (add (add (add (add (weightComponent X 2) (weightComponent X 1)) (weightComponent X 0))
    (weightComponent X (-1))) (weightComponent X (-2))).z = X.z := by
  simp [add, weightComponent, zero]

/-- The sum of all five weight components recovers the original element. -/
theorem weight_decomposition (X : Herm2x2Os) :
    add (add (add (add (weightComponent X 2) (weightComponent X 1)) (weightComponent X 0))
    (weightComponent X (-1))) (weightComponent X (-2)) = X := by
  cases X
  simp [add, weightComponent, zero]

/-! ## 3. Determinant interaction with weight decomposition -/

theorem det_pure_plus2 (xi_plus : ℚ) :
    ({ xp := xi_plus, xm := 0, z := { a := 0, b := 0, x0 := 0, x1 := 0, x2 := 0, y0 := 0, y1 := 0, y2 := 0 } } : Herm2x2Os).det = 0 := by
  simp [Herm2x2Os.det, zornNormℚ]

theorem det_pure_minus2 (xi_minus : ℚ) :
    ({ xp := 0, xm := xi_minus, z := { a := 0, b := 0, x0 := 0, x1 := 0, x2 := 0, y0 := 0, y1 := 0, y2 := 0 } } : Herm2x2Os).det = 0 := by
  simp [Herm2x2Os.det, zornNormℚ]

theorem det_pure_off_diagonal (Z : SplitOct) :
    ({ xp := 0, xm := 0, z := Z } : Herm2x2Os).det = -zornNormℚ Z := by
  simp [Herm2x2Os.det, zornNormℚ]

theorem det_cross_term (xi_plus xi_minus : ℚ) :
    ({ xp := xi_plus, xm := xi_minus, z := { a := 0, b := 0, x0 := 0, x1 := 0, x2 := 0, y0 := 0, y1 := 0, y2 := 0 } } : Herm2x2Os).det = xi_plus * xi_minus := by
  simp [Herm2x2Os.det, zornNormℚ]

/-! ## 4. Weight profile of null elements -/

/--
A refined classification of non-zero null elements by their weight profile.

This distinguishes the `E`-type (`ξ₊ ≠ 0`, `ξ₋ = 0`) from `Ē`-type
(`ξ₋ ≠ 0`, `ξ₊ = 0`) null directions, and mixed null elements where
both lightcone coordinates contribute.
-/
inductive NullWeightProfile (X : Herm2x2Os) : Type _ where
  | e_type   : X.xp ≠ 0 → X.xm = 0 → NullWeightProfile X
  | ebar_type : X.xm ≠ 0 → X.xp = 0 → NullWeightProfile X
  | mixed    : X.xp ≠ 0 → X.xm ≠ 0 → NullWeightProfile X

/--
The determinant stratum for `J₂(𝕆ₛ)` — the coarsest orbit classification
by the value of the (5,5) quadratic form.
-/
inductive DetStratum (X : Herm2x2Os) : Type _ where
  | isZero    : X.xp = 0 → X.xm = 0 → (let z := X.z; z.a = 0 ∧ z.b = 0 ∧ z.x0 = 0 ∧ z.x1 = 0 ∧ z.x2 = 0 ∧ z.y0 = 0 ∧ z.y1 = 0 ∧ z.y2 = 0) → DetStratum X
  | isNull    : X.det = 0 → DetStratum X
  | isGeneric : X.det ≠ 0 → DetStratum X

/-- Every element belongs to the null or generic determinant stratum. -/
def det_stratum_exists (X : Herm2x2Os) : DetStratum X :=
  if h : X.det = 0 then
    DetStratum.isNull h
  else
    DetStratum.isGeneric h

/--
Refined orbit data for `J₂(𝕆ₛ)`: the determinant stratum together with
the weight profile of null elements.
-/
structure RefinedOrbitData (X : Herm2x2Os) where
  stratum : DetStratum X
  weightProfile : Option (NullWeightProfile X)

end InfoGeometry.Algebra.JordanGradedWeight
