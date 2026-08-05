import InfoGeometry.Canonical.PositiveGrassmannianAmplituhedron

/-!
# Topology of the finite positive Grassmannian matrix chart

The objects here are the finite matrix chart and its linear image from the
canonical owner.  The results concern continuity and closed inverse images of
individual maximal-minor constraints.  They do not assert topology on a
Grassmannian quotient or any canonical-form/residue theorem.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical
open Matrix

variable {k n m : ℕ}

theorem continuous_maximalMinor
    (s : Fin k → Fin n) :
    Continuous (fun C : Matrix (Fin k) (Fin n) ℝ => maximalMinor C s) := by
  unfold maximalMinor
  fun_prop

theorem isClosed_maximalMinor_sublevel
    (s : Fin k → Fin n) (a : ℝ) :
    IsClosed {C : Matrix (Fin k) (Fin n) ℝ | maximalMinor C s ≤ a} := by
  change IsClosed ((fun C : Matrix (Fin k) (Fin n) ℝ => maximalMinor C s) ⁻¹' Set.Iic a)
  exact isClosed_Iic.preimage (continuous_maximalMinor s)

theorem isClosed_maximalMinor_superlevel
    (s : Fin k → Fin n) (a : ℝ) :
    IsClosed {C : Matrix (Fin k) (Fin n) ℝ | a ≤ maximalMinor C s} := by
  change IsClosed ((fun C : Matrix (Fin k) (Fin n) ℝ => maximalMinor C s) ⁻¹' Set.Ici a)
  exact isClosed_Ici.preimage (continuous_maximalMinor s)

theorem isClosed_positiveGrassmannianChart :
    IsClosed (positiveGrassmannianChart (k := k) (n := n)) := by
  have hset : positiveGrassmannianChart (k := k) (n := n) =
      ⋂ s : Fin k → Fin n, ⋂ (_hs : StrictMono s),
        {C : Matrix (Fin k) (Fin n) ℝ | 0 ≤ maximalMinor C s} := by
    ext C
    simp [positiveGrassmannianChart, HasNonnegativeMaximalMinors]
  rw [hset]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro hs
  exact isClosed_maximalMinor_superlevel s 0

theorem isOpen_positiveGrassmannianInterior :
    IsOpen (positiveGrassmannianInterior (k := k) (n := n)) := by
  have hset : positiveGrassmannianInterior (k := k) (n := n) =
      ⋂ s : Fin k → Fin n,
        {C : Matrix (Fin k) (Fin n) ℝ |
          ¬ StrictMono s ∨ 0 < maximalMinor C s} := by
    ext C
    simp only [positiveGrassmannianInterior, Set.mem_setOf_eq,
      HasPositiveMaximalMinors, Set.mem_iInter]
    constructor
    · intro h s
      by_cases hs : StrictMono s
      · exact Or.inr (h s hs)
      · exact Or.inl hs
    · intro h s hs
      cases h s with
      | inl hnot => exact False.elim (hnot hs)
      | inr hpos => exact hpos
  rw [hset]
  apply isOpen_iInter_of_finite
  intro s
  by_cases hs : StrictMono s
  · simp only [hs, not_true_eq_false, false_or]
    exact isOpen_Ioi.preimage (continuous_maximalMinor s)
  · simp [hs]

theorem continuous_amplituhedronMap
    (Z : Matrix (Fin n) (Fin m) ℝ) :
    Continuous (amplituhedronMap (k := k) Z) := by
  unfold amplituhedronMap
  fun_prop

/-- A bounded finite chart slice, cut out by coordinate intervals. -/
def positiveGrassmannianCoordinateBox (B : ℝ) :
    Set (Matrix (Fin k) (Fin n) ℝ) :=
  Set.univ.pi (fun _ : Fin k =>
    Set.univ.pi (fun _ : Fin n => Set.Icc (-B) B))

def positiveGrassmannianBoundedSlice (B : ℝ) :
    Set (Matrix (Fin k) (Fin n) ℝ) :=
  positiveGrassmannianChart (k := k) (n := n) ∩
    positiveGrassmannianCoordinateBox (k := k) (n := n) B

theorem isCompact_positiveGrassmannianCoordinateBox (B : ℝ) :
    IsCompact (positiveGrassmannianCoordinateBox (k := k) (n := n) B) := by
  unfold positiveGrassmannianCoordinateBox
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))

theorem isCompact_positiveGrassmannianBoundedSlice (B : ℝ) :
    IsCompact (positiveGrassmannianBoundedSlice (k := k) (n := n) B) := by
  unfold positiveGrassmannianBoundedSlice
  simpa [Set.inter_comm] using
    (isCompact_positiveGrassmannianCoordinateBox (k := k) (n := n) B).inter_right
      isClosed_positiveGrassmannianChart

def boundedAmplituhedronImage
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    Set (Matrix (Fin k) (Fin m) ℝ) :=
  amplituhedronMap (k := k) Z ''
    positiveGrassmannianBoundedSlice (k := k) (n := n) B

theorem isCompact_boundedAmplituhedronImage
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    IsCompact (boundedAmplituhedronImage (k := k) (n := n) (m := m) Z B) := by
  unfold boundedAmplituhedronImage
  exact (isCompact_positiveGrassmannianBoundedSlice (k := k) (n := n) B).image
    (continuous_amplituhedronMap Z)

/-! A compact bounded chart has a closed amplituhedron image.  This is a
finite-dimensional topological result; it does not identify the image with a
quotient Grassmannian or with a canonical-form boundary. -/
theorem isClosed_boundedAmplituhedronImage
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    IsClosed (boundedAmplituhedronImage (k := k) (n := n) (m := m) Z B) := by
  exact (isCompact_boundedAmplituhedronImage (k := k) (n := n) (m := m) Z B).isClosed

theorem boundedAmplituhedronImage_subset_amplituhedronImage
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    boundedAmplituhedronImage (k := k) (n := n) (m := m) Z B ⊆
      amplituhedronImage (k := k) (n := n) (m := m) Z := by
  rintro Y ⟨C, hC, rfl⟩
  exact ⟨C, hC.1, rfl⟩

theorem closure_boundedAmplituhedronImage
    (Z : Matrix (Fin n) (Fin m) ℝ) (B : ℝ) :
    closure (boundedAmplituhedronImage (k := k) (n := n) (m := m) Z B) =
      boundedAmplituhedronImage (k := k) (n := n) (m := m) Z B := by
  exact (isClosed_boundedAmplituhedronImage (k := k) (n := n) (m := m) Z B).closure_eq

theorem isClosed_amplituhedronMap_coordinate_sublevel
    (Z : Matrix (Fin n) (Fin m) ℝ) (i : Fin k) (j : Fin m) (a : ℝ) :
    IsClosed {C : Matrix (Fin k) (Fin n) ℝ |
      (amplituhedronMap (k := k) Z C) i j ≤ a} := by
  change IsClosed ((fun C : Matrix (Fin k) (Fin n) ℝ =>
    (amplituhedronMap (k := k) Z C) i j) ⁻¹' Set.Iic a)
  exact isClosed_Iic.preimage ((continuous_apply j).comp
    ((continuous_apply i).comp (continuous_amplituhedronMap Z)))

theorem isClosed_amplituhedronMap_coordinate_superlevel
    (Z : Matrix (Fin n) (Fin m) ℝ) (i : Fin k) (j : Fin m) (a : ℝ) :
    IsClosed {C : Matrix (Fin k) (Fin n) ℝ |
      a ≤ (amplituhedronMap (k := k) Z C) i j} := by
  change IsClosed ((fun C : Matrix (Fin k) (Fin n) ℝ =>
    (amplituhedronMap (k := k) Z C) i j) ⁻¹' Set.Ici a)
  exact isClosed_Ici.preimage ((continuous_apply j).comp
    ((continuous_apply i).comp (continuous_amplituhedronMap Z)))

end InfoGeometry.Topology
