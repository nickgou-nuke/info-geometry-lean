import InfoGeometry.Topology.DelaunayFlipMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.RohozhkinProjectiveCrossRatio
import InfoGeometry.Projective.MobiusGauge

/-!
# Delaunay Möbius Flip

This file bridges the rational local Delaunay flip matrices with their underlying
projective-gauge structure.

#### BUCKET 1: CLOSED FINITE THEOREMS
- The two columns of `flipBlock` sum to `1`.
- The two columns are barycentric coordinates for `ζ l` and `ζ j` in the
  affine chart determined by `(ζ k, ζ i)`.
- The determinant and entry-ratio residue of `flipBlock` are the expected
  rational projective quantities.
- The induced ratio coordinate action is the corresponding fractional linear
  expression.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
- Full `PGL₂` gauge covariance under an arbitrary Möbius relabeling.  That
  theorem needs explicit nonzero denominator hypotheses for each transformed
  label and for the source/target gauge factors.
-/

namespace InfoGeometry.Topology.Delaunay

open InfoGeometry.Projective
open Matrix

variable {ι : Type*} [DecidableEq ι] (labels : FlipLabels ι)
variable (i k j l : ι) (hik : i ≠ k)

omit [DecidableEq ι] in
/-- The flipBlock is a barycentric transition: its left column sums to 1. -/
theorem flipBlock_column_sum_left :
    flipBlock labels i k j l hik 0 0 + flipBlock labels i k j l hik 1 0 = 1 := by
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  simpa [flipBlock, rohozhkinFlipBlock] using
    (rohozhkinFlipBlock_first_column_sum (labels.ζ i) (labels.ζ k) (labels.ζ j) (labels.ζ l) hd)

omit [DecidableEq ι] in
/-- The flipBlock is a barycentric transition: its right column sums to 1. -/
theorem flipBlock_column_sum_right :
    flipBlock labels i k j l hik 0 1 + flipBlock labels i k j l hik 1 1 = 1 := by
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  simpa [flipBlock, rohozhkinFlipBlock] using
    (rohozhkinFlipBlock_second_column_sum (labels.ζ i) (labels.ζ k) (labels.ζ j) (labels.ζ l) hd)

omit [DecidableEq ι] in
/-- The first column gives the barycentric coordinates of ζ l in the segment [ζ k, ζ i]. -/
theorem flipBlock_barycentric_l :
    flipBlock labels i k j l hik 0 0 * labels.ζ k + flipBlock labels i k j l hik 1 0 * labels.ζ i = labels.ζ l := by
  dsimp [flipBlock]
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  field_simp [hd]
  ring

omit [DecidableEq ι] in
/-- The second column gives the barycentric coordinates of ζ j in the segment [ζ k, ζ i]. -/
theorem flipBlock_barycentric_j :
    flipBlock labels i k j l hik 0 1 * labels.ζ k + flipBlock labels i k j l hik 1 1 * labels.ζ i = labels.ζ j := by
  dsimp [flipBlock]
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  field_simp [hd]
  ring

omit [DecidableEq ι] in
/-- The determinant of the flip block evaluates to the ratio of cross edges. -/
theorem flipBlock_det :
    Matrix.det (flipBlock labels i k j l hik) = (labels.ζ j - labels.ζ l) / (labels.ζ i - labels.ζ k) := by
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  simpa [flipBlock, rohozhkinFlipBlock, Matrix.det_fin_two] using
    (rohozhkinFlipBlock_det (labels.ζ i) (labels.ζ k) (labels.ζ j) (labels.ζ l) hd)

omit [DecidableEq ι] in
/-- The projective action of the flip block aligns perfectly with the Möbius evaluation. -/
theorem flipBlock_projective_action (r : ℚ) :
    let A := flipBlock labels i k j l hik
    (A 0 0 * r + A 0 1) / (A 1 0 * r + A 1 1) =
      ((labels.ζ i - labels.ζ l) * r + (labels.ζ i - labels.ζ j)) /
      ((labels.ζ l - labels.ζ k) * r + (labels.ζ j - labels.ζ k)) := by
  dsimp [flipBlock]
  have hd : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  field_simp [hd]

omit [DecidableEq ι] in
/-- The Möbius-invariant residue extracted from the matrix is exactly the cross ratio. -/
theorem flipBlock_crossRatio (a b c d : ℚ) (A : Matrix (Fin 2) (Fin 2) ℚ) (hA : A = flipBlock labels i k j l hik) :
    a = A 0 0 → b = A 0 1 → c = A 1 0 → d = A 1 1 →
    (a * d) / (b * c) =
      ((labels.ζ i - labels.ζ l) * (labels.ζ j - labels.ζ k)) /
      ((labels.ζ i - labels.ζ j) * (labels.ζ l - labels.ζ k)) := by
  intro ha hb hc hd'
  subst A
  subst a
  subst b
  subst c
  subst d
  dsimp [flipBlock]
  have hden : labels.ζ i - labels.ζ k ≠ 0 := labels.nonzero_den hik
  field_simp [hden]

/--
Open theorem target for the full gauge covariance formula.

This is intentionally a proposition, not a theorem.  The closed file above
proves the affine chart identities; the general Möbius relabeling theorem must
add the required nonzero gauge and transformed-denominator hypotheses before it
can be promoted.
-/
def flipBlock_mobius_gauge_covariant_target (T : MobiusMap ℚ) : Prop :=
    let ζ' : ι → ℚ := mobiusComp T labels.ζ
    let A' := !![(ζ' i - ζ' l) / (ζ' i - ζ' k), (ζ' i - ζ' j) / (ζ' i - ζ' k);
                 (ζ' l - ζ' k) / (ζ' i - ζ' k), (ζ' j - ζ' k) / (ζ' i - ζ' k)]
    A' = !![leftGauge T (labels.ζ k), 0; 0, leftGauge T (labels.ζ i)] *
         flipBlock labels i k j l hik *
         !![(leftGauge T (labels.ζ l))⁻¹, 0; 0, (leftGauge T (labels.ζ j))⁻¹]

end InfoGeometry.Topology.Delaunay
