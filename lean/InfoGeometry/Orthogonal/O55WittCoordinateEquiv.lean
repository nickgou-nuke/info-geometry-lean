import InfoGeometry.Orthogonal.O55WittRootRepresentation

/-!
# Coordinate presentation of the Witt-skew `O(5,5)` Lie algebra

Every Witt-skew `10 × 10` matrix has the block form

`[[A, B], [C, -Aᵀ]]`

with `A` arbitrary and `B,C` skew.  The independent coordinates are therefore
`25 + 10 + 10 = 45`.  This file constructs the actual linear equivalence,
rather than inferring dimension from a list of suggestive generator names.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55WittCoordinates

open scoped Matrix
open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt

/-- Independent coordinate carrier: unrestricted `A` and upper-triangular
coordinates for the two skew blocks. -/
abbrev Coordinates :=
  Matrix Axis Axis ℂ × ((AxisPair → ℂ) × (AxisPair → ℂ))

/-- Skew matrix reconstructed from its entries above the diagonal. -/
def skewFromPairs (b : AxisPair → ℂ) : Matrix Axis Axis ℂ := fun i j =>
  if hij : i < j then b ⟨(i, j), hij⟩
  else if hji : j < i then -b ⟨(j, i), hji⟩
  else 0

@[simp] theorem skewFromPairs_diag (b : AxisPair → ℂ) (i : Axis) :
    skewFromPairs b i i = 0 := by
  simp [skewFromPairs]

/-- The reconstructed block is genuinely skew. -/
theorem skewFromPairs_swap (b : AxisPair → ℂ) (i j : Axis) :
    skewFromPairs b j i = -skewFromPairs b i j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [skewFromPairs, hij, not_lt_of_ge (le_of_lt hij)]
  · subst j
    simp [skewFromPairs]
  · simp [skewFromPairs, hij, not_lt_of_ge (le_of_lt hij)]

@[simp] theorem skewFromPairs_pair (b : AxisPair → ℂ) (p : AxisPair) :
    skewFromPairs b p.1.1 p.1.2 = b p := by
  simp [skewFromPairs, p.2]

/-- Encode block coordinates as a Witt matrix. -/
def encodeMatrix (c : Coordinates) : Mat10 := fun p q =>
  if hp : p.1 = 0 then
    if hq : q.1 = 0 then c.1 p.2 q.2
    else skewFromPairs c.2.1 p.2 q.2
  else
    if hq : q.1 = 0 then skewFromPairs c.2.2 p.2 q.2
    else -c.1 q.2 p.2

/-- Encoded coordinates satisfy the split-orthogonal infinitesimal law. -/
theorem encodeMatrix_isSplitOrthogonal (c : Coordinates) :
    IsSplitOrthogonal (encodeMatrix c) := by
  unfold IsSplitOrthogonal
  ext p q
  rcases p with ⟨sp, i⟩
  rcases q with ⟨sq, j⟩
  fin_cases sp <;> fin_cases sq
  · simp [wittAdjoint, encodeMatrix, flipIndex]
  · simp [wittAdjoint, encodeMatrix, flipIndex,
      skewFromPairs_swap]
  · simp [wittAdjoint, encodeMatrix, flipIndex,
      skewFromPairs_swap]
  · simp [wittAdjoint, encodeMatrix, flipIndex]

/-- Linear encoding into the native split-orthogonal Lie carrier. -/
def encode : Coordinates →ₗ[ℂ] splitO55Lie where
  toFun c := ⟨encodeMatrix c, encodeMatrix_isSplitOrthogonal c⟩
  map_add' c d := by
    apply Subtype.ext
    ext p q
    rcases p with ⟨sp, i⟩
    rcases q with ⟨sq, j⟩
    fin_cases sp <;> fin_cases sq <;>
      simp [encodeMatrix, skewFromPairs, add_apply]
  map_smul' z c := by
    apply Subtype.ext
    ext p q
    rcases p with ⟨sp, i⟩
    rcases q with ⟨sq, j⟩
    fin_cases sp <;> fin_cases sq <;>
      simp [encodeMatrix, skewFromPairs]

/-- Extract the unrestricted upper-left block. -/
def extractA (X : splitO55Lie) : Matrix Axis Axis ℂ := fun i j =>
  (X : Mat10) (plus i) (plus j)

/-- Extract the upper-right skew coordinates. -/
def extractB (X : splitO55Lie) : AxisPair → ℂ := fun p =>
  (X : Mat10) (plus p.1.1) (minus p.1.2)

/-- Extract the lower-left skew coordinates. -/
def extractC (X : splitO55Lie) : AxisPair → ℂ := fun p =>
  (X : Mat10) (minus p.1.1) (plus p.1.2)

/-- Linear coordinate extraction. -/
def extract : splitO55Lie →ₗ[ℂ] Coordinates where
  toFun X := (extractA X, (extractB X, extractC X))
  map_add' X Y := rfl
  map_smul' z X := rfl

/-- Entry relation for the lower-right block. -/
theorem lowerRight_eq_neg_transpose (X : splitO55Lie) (i j : Axis) :
    (X : Mat10) (minus i) (minus j) =
      -(X : Mat10) (plus j) (plus i) := by
  have h := congrArg
    (fun M : Mat10 => M (plus j) (plus i)) X.property
  simpa [IsSplitOrthogonal, wittAdjoint] using h

/-- Upper-right block is skew. -/
theorem upperRight_skew (X : splitO55Lie) (i j : Axis) :
    (X : Mat10) (plus j) (minus i) =
      -(X : Mat10) (plus i) (minus j) := by
  have h := congrArg
    (fun M : Mat10 => M (plus i) (minus j)) X.property
  simpa [IsSplitOrthogonal, wittAdjoint] using h

/-- Lower-left block is skew. -/
theorem lowerLeft_skew (X : splitO55Lie) (i j : Axis) :
    (X : Mat10) (minus j) (plus i) =
      -(X : Mat10) (minus i) (plus j) := by
  have h := congrArg
    (fun M : Mat10 => M (minus i) (plus j)) X.property
  simpa [IsSplitOrthogonal, wittAdjoint] using h

@[simp] theorem upperRight_diag_zero (X : splitO55Lie) (i : Axis) :
    (X : Mat10) (plus i) (minus i) = 0 := by
  have h := upperRight_skew X i i
  linear_combination h

@[simp] theorem lowerLeft_diag_zero (X : splitO55Lie) (i : Axis) :
    (X : Mat10) (minus i) (plus i) = 0 := by
  have h := lowerLeft_skew X i i
  linear_combination h

/-- Reconstruct one upper-right entry from the extracted pair coordinates. -/
theorem skewFromPairs_extractB (X : splitO55Lie) (i j : Axis) :
    skewFromPairs (extractB X) i j =
      (X : Mat10) (plus i) (minus j) := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [skewFromPairs, hij, extractB]
  · subst j
    simp
  · have hskew := upperRight_skew X j i
    simp [skewFromPairs, hij, not_lt_of_ge (le_of_lt hij), extractB]
    exact hskew.symm

/-- Reconstruct one lower-left entry from the extracted pair coordinates. -/
theorem skewFromPairs_extractC (X : splitO55Lie) (i j : Axis) :
    skewFromPairs (extractC X) i j =
      (X : Mat10) (minus i) (plus j) := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [skewFromPairs, hij, extractC]
  · subst j
    simp
  · have hskew := lowerLeft_skew X j i
    simp [skewFromPairs, hij, not_lt_of_ge (le_of_lt hij), extractC]
    exact hskew.symm

/-- Extracting after encoding returns every coordinate. -/
theorem extract_encode (c : Coordinates) :
    extract (encode c) = c := by
  rcases c with ⟨A, B, C⟩
  ext i j <;> simp [extract, extractA, extractB, extractC,
    encode, encodeMatrix]

/-- Encoding after extraction returns every Witt-skew matrix. -/
theorem encode_extract (X : splitO55Lie) :
    encode (extract X) = X := by
  apply Subtype.ext
  ext p q
  rcases p with ⟨sp, i⟩
  rcases q with ⟨sq, j⟩
  fin_cases sp <;> fin_cases sq
  · rfl
  · exact skewFromPairs_extractB X i j
  · exact skewFromPairs_extractC X i j
  · exact lowerRight_eq_neg_transpose X i j

/-- Actual linear equivalence between the `25+10+10` coordinate model and the
native split-orthogonal Lie carrier. -/
def coordinateEquiv : Coordinates ≃ₗ[ℂ] splitO55Lie where
  toFun := encode
  invFun := extract
  left_inv := extract_encode
  right_inv := encode_extract
  map_add' := map_add encode
  map_smul' := map_smul encode

/-- Uniqueness of the block coordinates. -/
theorem encode_injective : Function.Injective encode :=
  coordinateEquiv.injective

/-- Surjectivity of the block presentation. -/
theorem encode_surjective : Function.Surjective encode :=
  coordinateEquiv.surjective

/-- Coordinate presentation packet. -/
theorem o55_coordinate_packet :
    Function.Injective encode ∧ Function.Surjective encode ∧
      (∀ X : splitO55Lie,
        encode (extract X) = X) :=
  ⟨encode_injective, encode_surjective, encode_extract⟩

end InfoGeometry.Orthogonal.O55WittCoordinates

end noncomputable section
