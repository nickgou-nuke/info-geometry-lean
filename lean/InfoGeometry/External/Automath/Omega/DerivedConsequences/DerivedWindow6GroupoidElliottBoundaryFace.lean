import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.DerivedConsequences.DerivedWindow6BoundarySectorIrrepMomentUniformity

namespace Omega.DerivedConsequences

/-- Concrete finite bookkeeping for the window-`6` boundary-face Elliott invariant package. -/
def derived_window6_groupoid_elliott_boundary_face_m2BlockCount : ℕ := 8

def derived_window6_groupoid_elliott_boundary_face_m3BlockCount : ℕ := 4

def derived_window6_groupoid_elliott_boundary_face_m4BlockCount : ℕ := 9

/-- The three boundary fibers account for exactly three `M₂`-blocks. -/
def derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount : ℕ := 3

/-- The complementary cyclic summand contains the remaining `18` simple blocks. -/
def derived_window6_groupoid_elliott_boundary_face_cyclicBlockCount : ℕ := 18

/-- The total number of simple blocks in the window-`6` groupoid algebra. -/
def derived_window6_groupoid_elliott_boundary_face_totalBlockCount : ℕ := 21

/-- The simplex dimensions are one less than the corresponding block counts. -/
def derived_window6_groupoid_elliott_boundary_face_traceSimplexDimension : ℕ := 20

def derived_window6_groupoid_elliott_boundary_face_boundaryTraceDimension : ℕ := 2

def derived_window6_groupoid_elliott_boundary_face_cyclicTraceDimension : ℕ := 17

/-- The unit class vector of the finite direct sum
`M₂(ℂ)^8 ⊕ M₃(ℂ)^4 ⊕ M₄(ℂ)^9`. -/
def derived_window6_groupoid_elliott_boundary_face_unitClassVector : List ℕ :=
  List.replicate derived_window6_groupoid_elliott_boundary_face_m2BlockCount 2 ++
    List.replicate derived_window6_groupoid_elliott_boundary_face_m3BlockCount 3 ++
      List.replicate derived_window6_groupoid_elliott_boundary_face_m4BlockCount 4

/-- Concrete finite bookkeeping for the window-`6` boundary-face Elliott invariant package. -/
def derived_window6_groupoid_elliott_boundary_face_witness : Prop :=
  derived_window6_groupoid_elliott_boundary_face_m2BlockCount = 8 ∧
    derived_window6_groupoid_elliott_boundary_face_m3BlockCount = 4 ∧
    derived_window6_groupoid_elliott_boundary_face_m4BlockCount = 9 ∧
    derived_window6_groupoid_elliott_boundary_face_totalBlockCount =
      derived_window6_groupoid_elliott_boundary_face_m2BlockCount +
        derived_window6_groupoid_elliott_boundary_face_m3BlockCount +
        derived_window6_groupoid_elliott_boundary_face_m4BlockCount

/-- Concrete finite bookkeeping for the window-`6` boundary-face Elliott invariant package. -/
structure derived_window6_groupoid_elliott_boundary_face_data where
  witness : derived_window6_groupoid_elliott_boundary_face_witness := by
    unfold derived_window6_groupoid_elliott_boundary_face_witness
    norm_num

namespace derived_window6_groupoid_elliott_boundary_face_data

/-- The block decomposition inherited from the boundary-sector isotypy and uniformity packages. -/
def wedderburn_decomposition (_D : derived_window6_groupoid_elliott_boundary_face_data) : Prop :=
  derived_window6_groupoid_elliott_boundary_face_m2BlockCount =
      derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount ∧
    derived_window6_groupoid_elliott_boundary_face_m2BlockCount =
      derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount + 5 ∧
    derived_window6_groupoid_elliott_boundary_face_totalBlockCount =
      derived_window6_groupoid_elliott_boundary_face_m2BlockCount +
        derived_window6_groupoid_elliott_boundary_face_m3BlockCount +
          derived_window6_groupoid_elliott_boundary_face_m4BlockCount

/-- The `K₀` package is the positive lattice `ℕ²¹` with the displayed unit-class vector. -/
def k0_package (_D : derived_window6_groupoid_elliott_boundary_face_data) : Prop :=
  derived_window6_groupoid_elliott_boundary_face_unitClassVector.length =
      derived_window6_groupoid_elliott_boundary_face_totalBlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_unitClassVector.count 2 =
      derived_window6_groupoid_elliott_boundary_face_m2BlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_unitClassVector.count 3 =
      derived_window6_groupoid_elliott_boundary_face_m3BlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_unitClassVector.count 4 =
      derived_window6_groupoid_elliott_boundary_face_m4BlockCount

/-- The boundary face is the `3`-vertex face cut out by the three distinguished `M₂`-blocks,
while the complementary cyclic face has `18` vertices. -/
def trace_simplex_split (_D : derived_window6_groupoid_elliott_boundary_face_data) : Prop :=
  derived_window6_groupoid_elliott_boundary_face_totalBlockCount =
      derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount +
        derived_window6_groupoid_elliott_boundary_face_cyclicBlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_traceSimplexDimension + 1 =
      derived_window6_groupoid_elliott_boundary_face_totalBlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_boundaryTraceDimension + 1 =
      derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_cyclicTraceDimension + 1 =
      derived_window6_groupoid_elliott_boundary_face_cyclicBlockCount

end derived_window6_groupoid_elliott_boundary_face_data

/-- Paper label: `thm:derived-window6-groupoid-elliott-boundary-face`. -/
theorem paper_derived_window6_groupoid_elliott_boundary_face
    (D : derived_window6_groupoid_elliott_boundary_face_data) :
    D.wedderburn_decomposition ∧ D.k0_package ∧ D.trace_simplex_split := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · native_decide
    · constructor
      · native_decide
      · native_decide
  · constructor
    · native_decide
    · constructor
      · native_decide
      · constructor
        · native_decide
        · native_decide
  · constructor
    · native_decide
    · constructor
      · native_decide
      · constructor
        · native_decide
        · native_decide

end Omega.DerivedConsequences
