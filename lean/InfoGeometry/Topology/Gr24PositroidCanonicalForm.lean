import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The normalized positive Plücker model of `Gr(2,4)`

This file gives a concrete finite positroid stratification in Plücker
coordinates, rather than assuming a cell decomposition as structure fields.
The carrier is the nonnegative Klein quadric cut by `sum pᵢ = 1`; its strata
are indexed by their exact positive Plücker support and are proved to be
pairwise disjoint and exhaustive.  The top stratum has an explicit positive
four-coordinate chart.  In that chart the canonical top form is the actual
alternating determinant form `dlog a ∧ dlog b ∧ dlog c ∧ dlog e`, and its
coordinate-boundary residues are computed algebraically.

The scope is the finite `Gr(2,4)` Plücker model; this does not claim a general
`Gr(k,n)` positroid theorem or an amplituhedron BCFW triangulation.
-/

open scoped BigOperators

namespace InfoGeometry.Topology.Gr24PositroidCanonicalForm

noncomputable section

/-! ## Projective gauge slice and support decomposition -/

/-- A projective point of the nonnegative `Gr(2,4)` Plücker cone, normalized
by the sum of its six coordinates.  The Klein relation is the decomposability
equation in dimension four. -/
@[ext]
structure NormalizedPositivePluckerPoint where
  coord : Fin 6 → ℝ
  coord_nonneg : ∀ i, 0 ≤ coord i
  coord_sum_one : ∑ i : Fin 6, coord i = 1
  klein : coord 0 * coord 5 - coord 1 * coord 4 + coord 2 * coord 3 = 0

/-- The set of nonzero Plücker coordinates of a normalized nonnegative point. -/
def positiveSupport (P : NormalizedPositivePluckerPoint) : Finset (Fin 6) :=
  Finset.univ.filter fun i => 0 < P.coord i

/-- A support stratum: exactly the Plücker coordinates in `I` are positive.
Nonnegativity of the ambient point then makes all other coordinates zero. -/
def supportStratum (I : Finset (Fin 6)) : Set NormalizedPositivePluckerPoint :=
  {P | positiveSupport P = I}

/-- Only realized supports index cells.  This avoids adding empty sets to the
positroid decomposition. -/
abbrev PositroidSupport :=
  {I : Finset (Fin 6) // ∃ P : NormalizedPositivePluckerPoint, positiveSupport P = I}

noncomputable instance : Fintype PositroidSupport := Fintype.ofFinite PositroidSupport

theorem supportStrata_cover :
    (⋃ I : PositroidSupport, supportStratum I.1) = Set.univ := by
  ext P
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨⟨positiveSupport P, ⟨P, rfl⟩⟩, rfl⟩

theorem supportStrata_disjoint {I J : PositroidSupport} (hIJ : I ≠ J) :
    Disjoint (supportStratum I.1) (supportStratum J.1) := by
  rw [Set.disjoint_left]
  intro P hI hJ
  apply hIJ
  apply Subtype.ext
  exact hI.symm.trans hJ

/-- The characteristic weights of the realized support strata form an exact
finite partition of unity on the normalized nonnegative Grassmannian. -/
def supportStratumIndicator (I : PositroidSupport)
    (P : NormalizedPositivePluckerPoint) : ℝ :=
  if positiveSupport P = I.1 then 1 else 0

theorem supportStrata_indicator_sum (P : NormalizedPositivePluckerPoint) :
    ∑ I : PositroidSupport, supportStratumIndicator I P = 1 := by
  classical
  let I₀ : PositroidSupport := ⟨positiveSupport P, ⟨P, rfl⟩⟩
  rw [Finset.sum_eq_single I₀]
  · simp [supportStratumIndicator, I₀]
  · intro I hI hne
    have hsupport : positiveSupport P ≠ I.1 := by
      intro h
      apply hne
      exact Subtype.ext h.symm
    simp [supportStratumIndicator, hsupport]
  · intro hnot
    exact (hnot (Finset.mem_univ I₀)).elim

theorem mem_supportStratum_iff (P : NormalizedPositivePluckerPoint)
    (I : Finset (Fin 6)) :
    P ∈ supportStratum I ↔ positiveSupport P = I := Iff.rfl

theorem supportStratum_coordinate_pos {P : NormalizedPositivePluckerPoint}
    {I : Finset (Fin 6)} (hP : P ∈ supportStratum I) {i : Fin 6}
    (hi : i ∈ I) : 0 < P.coord i := by
  have hs : positiveSupport P = I := hP
  have hi' : i ∈ positiveSupport P := hs ▸ hi
  exact (Finset.mem_filter.mp hi').2

theorem supportStratum_coordinate_eq_zero {P : NormalizedPositivePluckerPoint}
    {I : Finset (Fin 6)} (hP : P ∈ supportStratum I) {i : Fin 6}
    (hi : i ∉ I) : P.coord i = 0 := by
  have hs : positiveSupport P = I := hP
  have hnot : ¬ 0 < P.coord i := by
    intro hpos
    apply hi
    rw [← hs]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
  exact le_antisymm (le_of_not_gt hnot) (P.coord_nonneg i)

/-- On a nonnegative Plücker vector, a product of two coordinates is positive
exactly when both coordinates belong to the positive support. -/
theorem plucker_pair_product_pos_iff (P : NormalizedPositivePluckerPoint)
    (i j : Fin 6) :
    0 < P.coord i * P.coord j ↔
      i ∈ positiveSupport P ∧ j ∈ positiveSupport P := by
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    constructor
    · by_contra hn
      have hi : P.coord i = 0 :=
        le_antisymm (le_of_not_gt hn) (P.coord_nonneg i)
      rw [hi, zero_mul] at h
      exact (not_lt_of_ge (le_rfl : (0 : ℝ) ≤ 0)) h
    · by_contra hn
      have hj : P.coord j = 0 :=
        le_antisymm (le_of_not_gt hn) (P.coord_nonneg j)
      rw [hj, mul_zero] at h
      exact (not_lt_of_ge (le_rfl : (0 : ℝ) ≤ 0)) h
  · rintro ⟨hi, hj⟩
    exact mul_pos hi hj

/-- The Plücker equation forces the support exchange rule for the three
complementary pair products in `Gr(2,4)`: the middle product is present iff
at least one of the two outer products is present. This is a concrete
restriction on attainable positroid supports, not merely a cover by arbitrary
Boolean patterns. -/
theorem support_plucker_exchange (P : NormalizedPositivePluckerPoint) :
    ((1 : Fin 6) ∈ positiveSupport P ∧ (4 : Fin 6) ∈ positiveSupport P) ↔
      (((0 : Fin 6) ∈ positiveSupport P ∧ (5 : Fin 6) ∈ positiveSupport P) ∨
       ((2 : Fin 6) ∈ positiveSupport P ∧ (3 : Fin 6) ∈ positiveSupport P)) := by
  rw [← plucker_pair_product_pos_iff P 1 4,
    ← plucker_pair_product_pos_iff P 0 5,
    ← plucker_pair_product_pos_iff P 2 3]
  have hklein : P.coord 1 * P.coord 4 =
      P.coord 0 * P.coord 5 + P.coord 2 * P.coord 3 := by
    have h := P.klein
    linarith
  rw [hklein]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have h05 : P.coord 0 * P.coord 5 = 0 :=
      le_antisymm hn.1 (mul_nonneg (P.coord_nonneg 0) (P.coord_nonneg 5))
    have h23 : P.coord 2 * P.coord 3 = 0 :=
      le_antisymm hn.2 (mul_nonneg (P.coord_nonneg 2) (P.coord_nonneg 3))
    rw [h05, h23, add_zero] at h
    exact (lt_irrefl 0 h)
  · rintro (h | h)
    · exact lt_of_lt_of_le h (le_add_of_nonneg_right
        (mul_nonneg (P.coord_nonneg 2) (P.coord_nonneg 3)))
    · exact lt_of_lt_of_le h (le_add_of_nonneg_left
        (mul_nonneg (P.coord_nonneg 0) (P.coord_nonneg 5)))

/-! ## Exact classification of the rank-two supports

For `Gr(2,4)`, the Grassmann--Plücker equation is the only circuit relation:
`p₀₁ p₂₃ + p₀₃ p₁₂ = p₀₂ p₁₃`. On nonnegative coordinates, its support
condition is exactly the basis-exchange condition below. We construct a
Plücker point for every support satisfying it; hence the realized-support
index above is equivalent to this explicit combinatorial type.
-/

/-- The rank-two support exchange condition in Plücker order
`01, 02, 03, 12, 13, 23`. -/
def IsGr24PositroidSupport (I : Finset (Fin 6)) : Prop :=
  (1 ∈ I ∧ 4 ∈ I) ↔ ((0 ∈ I ∧ 5 ∈ I) ∨ (2 ∈ I ∧ 3 ∈ I))

/-- A zero-one coordinate attached to a proposed set of Plücker bases. -/
private def supportWeight (I : Finset (Fin 6)) (i : Fin 6) : ℝ :=
  if i ∈ I then 1 else 0

/-- The sum of the two complementary outer products in the Klein relation. -/
private def outerSupportWeight (I : Finset (Fin 6)) : ℝ :=
  supportWeight I 0 * supportWeight I 5 + supportWeight I 2 * supportWeight I 3

private theorem outerSupportWeight_pos_iff (I : Finset (Fin 6)) :
    0 < outerSupportWeight I ↔
      ((0 : Fin 6) ∈ I ∧ (5 : Fin 6) ∈ I) ∨
        ((2 : Fin 6) ∈ I ∧ (3 : Fin 6) ∈ I) := by
  unfold outerSupportWeight supportWeight
  by_cases h0 : (0 : Fin 6) ∈ I <;> by_cases h5 : (5 : Fin 6) ∈ I <;>
    by_cases h2 : (2 : Fin 6) ∈ I <;> by_cases h3 : (3 : Fin 6) ∈ I <;>
    simp [h0, h5, h2, h3]

/-- A nonnegative Plücker vector with exactly the proposed support. When
both middle bases occur, the `02,13` product is chosen to equal the sum of
the two outer products. -/
private def rawPluckerOfSupport (I : Finset (Fin 6)) : Fin 6 → ℝ
  | 0 => supportWeight I 0
  | 1 => if 1 ∈ I ∧ 4 ∈ I then outerSupportWeight I else supportWeight I 1
  | 2 => supportWeight I 2
  | 3 => supportWeight I 3
  | 4 => if 1 ∈ I ∧ 4 ∈ I then 1 else supportWeight I 4
  | 5 => supportWeight I 5

private theorem rawPluckerOfSupport_nonneg (I : Finset (Fin 6)) (i : Fin 6) :
    0 ≤ rawPluckerOfSupport I i := by
  fin_cases i <;> simp [rawPluckerOfSupport, supportWeight,
    outerSupportWeight] <;> positivity

private theorem rawPluckerOfSupport_klein (I : Finset (Fin 6))
    (hI : IsGr24PositroidSupport I) :
    rawPluckerOfSupport I 0 * rawPluckerOfSupport I 5 -
      rawPluckerOfSupport I 1 * rawPluckerOfSupport I 4 +
      rawPluckerOfSupport I 2 * rawPluckerOfSupport I 3 = 0 := by
  have houter := outerSupportWeight_pos_iff I
  by_cases hmid : (1 : Fin 6) ∈ I ∧ (4 : Fin 6) ∈ I
  · have hout : 0 < outerSupportWeight I := by
      rw [houter]
      exact hI.mp hmid
    simp [rawPluckerOfSupport, hmid]
    unfold outerSupportWeight
    ring
  · have houterZero : outerSupportWeight I = 0 := by
      apply le_antisymm
      · exact le_of_not_gt (by
          intro hp
          exact hmid (hI.mpr (houter.mp hp)))
      · unfold outerSupportWeight supportWeight
        split_ifs <;> norm_num
    have hmiddleZero : supportWeight I 1 * supportWeight I 4 = 0 := by
      by_cases h1 : (1 : Fin 6) ∈ I <;> by_cases h4 : (4 : Fin 6) ∈ I
      · exact (hmid ⟨h1, h4⟩).elim
      · simp [supportWeight, h1, h4]
      · simp [supportWeight, h1, h4]
      · simp [supportWeight, h1, h4]
    simp [rawPluckerOfSupport, hmid]
    unfold outerSupportWeight at houterZero
    linarith [houterZero, hmiddleZero]

private theorem rawPluckerOfSupport_pos_iff (I : Finset (Fin 6))
    (hI : IsGr24PositroidSupport I) (i : Fin 6) :
    0 < rawPluckerOfSupport I i ↔ i ∈ I := by
  fin_cases i
  · by_cases hi : (0 : Fin 6) ∈ I <;>
      simp [rawPluckerOfSupport, supportWeight, hi]
  · by_cases hmid : (1 : Fin 6) ∈ I ∧ (4 : Fin 6) ∈ I
    · have hout : 0 < outerSupportWeight I :=
        (outerSupportWeight_pos_iff I).2 (hI.mp hmid)
      constructor
      · intro _
        exact hmid.1
      · intro _
        simpa [rawPluckerOfSupport, hmid] using hout
    · by_cases h1 : (1 : Fin 6) ∈ I <;> by_cases h4 : (4 : Fin 6) ∈ I
      · exact (hmid ⟨h1, h4⟩).elim
      · simp [rawPluckerOfSupport, supportWeight, h1, h4]
      · simp [rawPluckerOfSupport, supportWeight, h1, h4]
      · simp [rawPluckerOfSupport, supportWeight, h1, h4]
  · by_cases hi : (2 : Fin 6) ∈ I <;>
      simp [rawPluckerOfSupport, supportWeight, hi]
  · by_cases hi : (3 : Fin 6) ∈ I <;>
      simp [rawPluckerOfSupport, supportWeight, hi]
  · by_cases hmid : (1 : Fin 6) ∈ I ∧ (4 : Fin 6) ∈ I
    · constructor
      · intro _
        exact hmid.2
      · intro _
        simp [rawPluckerOfSupport, hmid]
    · by_cases h1 : (1 : Fin 6) ∈ I <;> by_cases h4 : (4 : Fin 6) ∈ I
      · exact (hmid ⟨h1, h4⟩).elim
      · simp [rawPluckerOfSupport, supportWeight, h1, h4]
      · simp [rawPluckerOfSupport, supportWeight, h1, h4]
      · simp [rawPluckerOfSupport, supportWeight, h1, h4]
  · by_cases hi : (5 : Fin 6) ∈ I <;>
      simp [rawPluckerOfSupport, supportWeight, hi]

private theorem positiveSupport_nonempty (P : NormalizedPositivePluckerPoint) :
    (positiveSupport P).Nonempty := by
  by_contra h
  have hz : ∀ i, P.coord i = 0 := by
    intro i
    have hnot : ¬ 0 < P.coord i := by
      intro hp
      exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
    exact le_antisymm (le_of_not_gt hnot) (P.coord_nonneg i)
  have hsum : (∑ i : Fin 6, P.coord i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hz i
  have h := P.coord_sum_one
  rw [hsum] at h
  norm_num at h

/-- Normalize the constructive zero-one realization of an admissible
support. The positive total mass makes this projective gauge well-defined. -/
private noncomputable def normalizedPointOfSupport (I : Finset (Fin 6))
    (hI : IsGr24PositroidSupport I) (hne : I.Nonempty) :
    NormalizedPositivePluckerPoint := by
  let c := rawPluckerOfSupport I
  have hcpos : ∃ i, 0 < c i := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, (rawPluckerOfSupport_pos_iff I hI i).2 hi⟩
  let mass := ∑ i : Fin 6, c i
  have hmass : 0 < mass := by
    dsimp [mass]
    exact Finset.sum_pos' (fun j _ => rawPluckerOfSupport_nonneg I j)
      (by obtain ⟨i, hi⟩ := hcpos; exact ⟨i, Finset.mem_univ i, hi⟩)
  refine ⟨fun i => c i / mass, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (rawPluckerOfSupport_nonneg I i) hmass.le
  · rw [← Finset.sum_div]
    dsimp [mass]
    exact div_self (ne_of_gt hmass)
  · have hklein := rawPluckerOfSupport_klein I hI
    change (c 0 / mass) * (c 5 / mass) -
      (c 1 / mass) * (c 4 / mass) + (c 2 / mass) * (c 3 / mass) = 0
    field_simp
    nlinarith [hklein]

/-- A nonempty six-bit support is realized by a normalized nonnegative
`Gr(2,4)` Plücker point exactly when it satisfies rank-two basis exchange. -/
theorem positroidSupport_iff_exchange (I : Finset (Fin 6)) :
    (∃ P : NormalizedPositivePluckerPoint, positiveSupport P = I) ↔
      I.Nonempty ∧ IsGr24PositroidSupport I := by
  constructor
  · rintro ⟨P, rfl⟩
    constructor
    · exact positiveSupport_nonempty P
    · simpa [IsGr24PositroidSupport] using support_plucker_exchange P
  · rintro ⟨hne, hI⟩
    refine ⟨normalizedPointOfSupport I hI hne, ?_⟩
    ext i
    simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    change 0 < rawPluckerOfSupport I i /
        (∑ j : Fin 6, rawPluckerOfSupport I j) ↔ i ∈ I
    have hmass : 0 < ∑ j : Fin 6, rawPluckerOfSupport I j :=
      Finset.sum_pos' (fun j _ => rawPluckerOfSupport_nonneg I j)
        (by obtain ⟨j, hj⟩ := hne
            exact ⟨j, Finset.mem_univ j,
              (rawPluckerOfSupport_pos_iff I hI j).2 hj⟩)
    rw [div_pos_iff_of_pos_right hmass]
    exact rawPluckerOfSupport_pos_iff I hI i

end

noncomputable section

/-- The realized-support index is exactly the finite subtype of nonempty
supports satisfying the concrete `Gr(2,4)` exchange law. -/
theorem positroidSupport_exchange_characterization (I : PositroidSupport) :
    IsGr24PositroidSupport I.1 := by
  rcases I.2 with ⟨P, hP⟩
  have h := support_plucker_exchange P
  rw [hP] at h
  exact h

/-- The combinatorial index set for the rank-two `Gr(2,4)` positroid cells:
nonempty basis supports satisfying the exact Grassmann--Plücker exchange law.
This is a finite, explicit cell index, rather than an arbitrary family of
subsets or a structure carrying assumed cell data. -/
abbrev AdmissiblePositroidSupport :=
  {I : Finset (Fin 6) // I.Nonempty ∧ IsGr24PositroidSupport I}

noncomputable instance : Fintype AdmissiblePositroidSupport :=
  Fintype.ofFinite AdmissiblePositroidSupport

/-- The geometric support strata are indexed bijectively by the explicit
nonempty supports satisfying rank-two positroid exchange. -/
noncomputable def positroidSupportEquiv : PositroidSupport ≃ AdmissiblePositroidSupport where
  toFun I := ⟨I.1, (positroidSupport_iff_exchange I.1).mp I.2⟩
  invFun I := ⟨I.1, (positroidSupport_iff_exchange I.1).mpr I.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Reindex the exact support partition by explicit rank-two positroid data:
every normalized point belongs to the cell of its positive Plücker support,
and that support is nonempty and satisfies basis exchange. -/
theorem positroidCells_cover_by_exchange_support :
    (Set.univ : Set NormalizedPositivePluckerPoint) =
      ⋃ I : AdmissiblePositroidSupport, supportStratum I.1 := by
  ext P
  constructor
  · intro _
    apply Set.mem_iUnion.mpr
    refine ⟨⟨positiveSupport P, ?_⟩, rfl⟩
    refine ⟨positiveSupport_nonempty P, ?_⟩
    simpa [IsGr24PositroidSupport] using support_plucker_exchange P
  · intro _
    exact Set.mem_univ P

/-! ## The top positroid cell in positive network coordinates -/

/-- Four positive parameters for the top cell of the normalized positive
`Gr(2,4)` Plücker model. -/
@[ext]
structure PositiveTopCoordinates where
  a : ℝ
  b : ℝ
  c : ℝ
  e : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  e_pos : 0 < e

/-- The standard positive-network chart, in Plücker order
`01, 02, 03, 12, 13, 23`. -/
def topCellPlucker (x : PositiveTopCoordinates) : Fin 6 → ℝ
  | 0 => 1
  | 1 => x.a
  | 2 => x.a * x.b
  | 3 => x.c
  | 4 => x.c * (x.b + x.e)
  | 5 => x.a * x.c * x.e

/-- A concrete `2 × 4` matrix representative for the top-cell chart.  Its
columns are `(1,0)`, `(0,1)`, `(-c,a)`, and `(-c(b+e),ab)`. -/
def topCellMatrix (x : PositiveTopCoordinates) : Matrix (Fin 2) (Fin 4) ℝ :=
  fun i j =>
    match i, j with
    | 0, 0 => 1
    | 1, 0 => 0
    | 0, 1 => 0
    | 1, 1 => 1
    | 0, 2 => -x.c
    | 1, 2 => x.a
    | 0, 3 => -x.c * (x.b + x.e)
    | 1, 3 => x.a * x.b

/-- The six Plücker coordinates of `topCellMatrix` are the advertised
positive-network coordinates. -/
theorem topCellMatrix_plucker_coordinates (x : PositiveTopCoordinates) :
    ((topCellMatrix x) 0 0 * (topCellMatrix x) 1 1 -
      (topCellMatrix x) 0 1 * (topCellMatrix x) 1 0 = 1) ∧
    ((topCellMatrix x) 0 0 * (topCellMatrix x) 1 2 -
      (topCellMatrix x) 0 2 * (topCellMatrix x) 1 0 = x.a) ∧
    ((topCellMatrix x) 0 0 * (topCellMatrix x) 1 3 -
      (topCellMatrix x) 0 3 * (topCellMatrix x) 1 0 = x.a * x.b) ∧
    ((topCellMatrix x) 0 1 * (topCellMatrix x) 1 2 -
      (topCellMatrix x) 0 2 * (topCellMatrix x) 1 1 = x.c) ∧
    ((topCellMatrix x) 0 1 * (topCellMatrix x) 1 3 -
      (topCellMatrix x) 0 3 * (topCellMatrix x) 1 1 = x.c * (x.b + x.e)) ∧
    ((topCellMatrix x) 0 2 * (topCellMatrix x) 1 3 -
      (topCellMatrix x) 0 3 * (topCellMatrix x) 1 2 = x.a * x.c * x.e) := by
  norm_num [topCellMatrix]; ring

theorem topCellPlucker_pos (x : PositiveTopCoordinates) (i : Fin 6) :
    0 < topCellPlucker x i := by
  fin_cases i
  · norm_num [topCellPlucker]
  · simpa [topCellPlucker] using x.a_pos
  · simpa [topCellPlucker] using mul_pos x.a_pos x.b_pos
  · simpa [topCellPlucker] using x.c_pos
  · simpa [topCellPlucker] using mul_pos x.c_pos (add_pos x.b_pos x.e_pos)
  · simpa [topCellPlucker] using mul_pos (mul_pos x.a_pos x.c_pos) x.e_pos

theorem topCellPlucker_klein (x : PositiveTopCoordinates) :
    topCellPlucker x 0 * topCellPlucker x 5
      - topCellPlucker x 1 * topCellPlucker x 4
      + topCellPlucker x 2 * topCellPlucker x 3 = 0 := by
  simp [topCellPlucker]
  ring

/-- The `p01 = 1` projective chart of the top positroid stratum. -/
@[ext]
structure UnitTopCellPoint where
  coord : Fin 6 → ℝ
  coord01 : coord 0 = 1
  coord_pos : ∀ i, 0 < coord i
  klein : coord 0 * coord 5 - coord 1 * coord 4 + coord 2 * coord 3 = 0

/-- The positive parameters produce a point of the `p01 = 1` top-cell chart. -/
noncomputable def topCellChartPoint (x : PositiveTopCoordinates) : UnitTopCellPoint :=
  ⟨topCellPlucker x, by simp [topCellPlucker], topCellPlucker_pos x,
    topCellPlucker_klein x⟩

/-- Recover network coordinates from a point in the `p01 = 1` chart. -/
noncomputable def topCellParameters (P : UnitTopCellPoint) : PositiveTopCoordinates :=
  ⟨P.coord 1, P.coord 2 / P.coord 1, P.coord 3,
    P.coord 5 / (P.coord 1 * P.coord 3),
    P.coord_pos 1,
    div_pos (P.coord_pos 2) (P.coord_pos 1),
    P.coord_pos 3,
    div_pos (P.coord_pos 5) (mul_pos (P.coord_pos 1) (P.coord_pos 3))⟩

/-- The positive network chart is a bijection onto the full-positive
`p01 = 1` Plücker chart. -/
noncomputable def topCellChartEquiv : PositiveTopCoordinates ≃ UnitTopCellPoint where
  toFun := topCellChartPoint
  invFun := topCellParameters
  left_inv := by
    intro x
    ext
    · rfl
    · simp [topCellParameters, topCellChartPoint, topCellPlucker]
      field_simp [ne_of_gt x.a_pos]
    · rfl
    · simp [topCellParameters, topCellChartPoint, topCellPlucker]
      field_simp [ne_of_gt x.a_pos, ne_of_gt x.c_pos]
  right_inv := by
    intro P
    have h1 : P.coord 1 ≠ 0 := ne_of_gt (P.coord_pos 1)
    have h3 : P.coord 3 ≠ 0 := ne_of_gt (P.coord_pos 3)
    apply UnitTopCellPoint.ext
    funext i
    fin_cases i
    · simpa [topCellChartPoint, topCellPlucker] using P.coord01.symm
    · rfl
    · change P.coord 1 * (P.coord 2 / P.coord 1) = P.coord 2
      field_simp [h1]
    · rfl
    · simp only [topCellParameters]
      have hp := P.klein
      rw [P.coord01] at hp
      have hp' : P.coord 2 * P.coord 3 + P.coord 5 = P.coord 1 * P.coord 4 := by
        nlinarith [hp]
      change P.coord 3 *
        (P.coord 2 / P.coord 1 + P.coord 5 / (P.coord 1 * P.coord 3)) = P.coord 4
      field_simp [h1, h3]
      nlinarith [hp']
    · change P.coord 1 * P.coord 3 *
        (P.coord 5 / (P.coord 1 * P.coord 3)) = P.coord 5
      field_simp [h1, h3]

/-- The normalized top-cell coordinates lie on the projective gauge slice. -/
noncomputable def topCellPoint (x : PositiveTopCoordinates) :
    NormalizedPositivePluckerPoint := by
  let s := ∑ i : Fin 6, topCellPlucker x i
  have hs : 0 < s := by
    dsimp [s]
    apply Finset.sum_pos
    · intro i hi
      exact topCellPlucker_pos x i
    · simp
  refine ⟨fun i => topCellPlucker x i / s, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (le_of_lt (topCellPlucker_pos x i)) (le_of_lt hs)
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hs)
  · have hs0 : s ≠ 0 := ne_of_gt hs
    simp only [topCellPlucker]
    field_simp
    nlinarith [topCellPlucker_klein x]

/-- The positive chart lands in the top support stratum, with all six
Plücker coordinates strictly positive after projective normalization. -/
theorem topCellPoint_positive_support (x : PositiveTopCoordinates) :
    positiveSupport (topCellPoint x) = Finset.univ := by
  ext i
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro _
    trivial
  · intro _
    have hpos := topCellPlucker_pos x i
    change 0 < (topCellPoint x).coord i
    unfold topCellPoint
    dsimp
    apply div_pos hpos
    apply Finset.sum_pos
    · intro j hj
      exact topCellPlucker_pos x j
    · simp

/-! ## The logarithmic canonical top form and its residues -/

/-- Evaluation of the top `dlog` form on four tangent vectors.  The determinant
is the alternating wedge of the four one-forms `dxᵢ / xᵢ`. -/
def topCellCanonicalForm (x : PositiveTopCoordinates)
    (v : Fin 4 → Fin 4 → ℝ) : ℝ :=
  Matrix.det fun i j => v j i / (![x.a, x.b, x.c, x.e] i)

/-- Coefficient of the logarithmic volume form in the standard coordinate
volume form. -/
def topCellCanonicalDensity (x : PositiveTopCoordinates) : ℝ :=
  ∏ i : Fin 4, (![x.a, x.b, x.c, x.e] i)⁻¹

theorem topCellCanonicalForm_standardFrame (x : PositiveTopCoordinates) :
    topCellCanonicalForm x (fun j i => if i = j then 1 else 0) =
      topCellCanonicalDensity x := by
  unfold topCellCanonicalForm topCellCanonicalDensity
  have hdiag : (fun i j : Fin 4 => (if i = j then (1 : ℝ) else 0) /
      (![x.a, x.b, x.c, x.e] i)) =
      Matrix.diagonal (fun i => (![x.a, x.b, x.c, x.e] i)⁻¹) := by
    funext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  rw [hdiag, Matrix.det_diagonal]

/-- The logarithmic volume density is strictly positive throughout the top
positroid cell. -/
theorem topCellCanonicalDensity_pos (x : PositiveTopCoordinates) :
    0 < topCellCanonicalDensity x := by
  unfold topCellCanonicalDensity
  apply Finset.prod_pos
  intro i hi
  fin_cases i
  · exact inv_pos.mpr x.a_pos
  · exact inv_pos.mpr x.b_pos
  · exact inv_pos.mpr x.c_pos
  · exact inv_pos.mpr x.e_pos

/-- The top-cell logarithmic canonical form is nonzero: it evaluates to a
strictly positive density on the standard oriented coordinate frame. -/
theorem topCellCanonicalForm_ne_zero (x : PositiveTopCoordinates) :
    topCellCanonicalForm x (fun j i => if i = j then 1 else 0) ≠ 0 := by
  rw [topCellCanonicalForm_standardFrame]
  exact ne_of_gt (topCellCanonicalDensity_pos x)

/-! ## The top-cell form on the projective Plücker stratum

The network parameters above describe a chart.  The following construction
recovers those parameters from any point of the all-positive stratum of the
normalized projective Plücker model.  Thus the canonical form is attached to
the point of the Grassmannian, not to an unrelated parameter supplied beside
it.
-/

/-- Recover the positive-network coordinates from an arbitrary point in the
all-positive projective Plücker stratum.  The `p₀₁` coordinate is used as the
projective pivot; the Klein equation recovers the remaining Plücker
coordinate. -/
noncomputable def topCellParametersOfPoint (P : NormalizedPositivePluckerPoint)
    (hP : positiveSupport P = Finset.univ) : PositiveTopCoordinates := by
  have hcoord : ∀ i : Fin 6, 0 < P.coord i := by
    intro i
    have hi : i ∈ positiveSupport P := by rw [hP]; simp
    exact (Finset.mem_filter.mp hi).2
  refine ⟨P.coord 1 / P.coord 0, P.coord 2 / P.coord 1,
    P.coord 3 / P.coord 0,
    P.coord 5 * P.coord 0 / (P.coord 1 * P.coord 3), ?_, ?_, ?_, ?_⟩
  · exact div_pos (hcoord 1) (hcoord 0)
  · exact div_pos (hcoord 2) (hcoord 1)
  · exact div_pos (hcoord 3) (hcoord 0)
  · exact div_pos (mul_pos (hcoord 5) (hcoord 0))
      (mul_pos (hcoord 1) (hcoord 3))

/-- The recovered network chart has exactly the Plücker coordinates of the
original point after fixing the pivot coordinate `p₀₁ = 1`. -/
theorem topCellPlucker_parametersOfPoint (P : NormalizedPositivePluckerPoint)
    (hP : positiveSupport P = Finset.univ) (i : Fin 6) :
    topCellPlucker (topCellParametersOfPoint P hP) i = P.coord i / P.coord 0 := by
  have hcoord : ∀ i : Fin 6, 0 < P.coord i := by
    intro i
    have hi : i ∈ positiveSupport P := by rw [hP]; simp
    exact (Finset.mem_filter.mp hi).2
  have h0 := ne_of_gt (hcoord 0)
  have h1 := ne_of_gt (hcoord 1)
  have h3 := ne_of_gt (hcoord 3)
  have hklein' : P.coord 1 * P.coord 4 =
      P.coord 0 * P.coord 5 + P.coord 2 * P.coord 3 := by
    linarith [P.klein]
  fin_cases i
  · simp [topCellPlucker, div_self h0]
  · rfl
  · simp only [topCellPlucker, topCellParametersOfPoint]
    field_simp [h0, h1]
    change P.coord 2 = P.coord 2
    rfl
  · rfl
  · simp only [topCellPlucker, topCellParametersOfPoint]
    field_simp [h0, h1, h3]
    have hklein'' : P.coord 1 * P.coord (⟨4, by omega⟩ : Fin 6) =
        P.coord 0 * P.coord 5 + P.coord 2 * P.coord 3 := by
      simpa using hklein'
    nlinarith [hklein'']
  · simp only [topCellPlucker, topCellParametersOfPoint]
    field_simp [h0, h1, h3]
    change P.coord 5 = P.coord 5
    rfl

/-- The global top-cell canonical form on a point of the projective
all-positive stratum.  Its value is obtained from that point's own pivot
coordinates, so changing an auxiliary matrix representative cannot change
the form. -/
noncomputable def projectiveTopCellCanonicalForm
    (P : NormalizedPositivePluckerPoint)
    (hP : positiveSupport P = Finset.univ)
    (v : Fin 4 → Fin 4 → ℝ) : ℝ :=
  topCellCanonicalForm (topCellParametersOfPoint P hP) v

/-- The coefficient of the projective top-cell form in the recovered
positive coordinates. -/
noncomputable def projectiveTopCellCanonicalDensity
    (P : NormalizedPositivePluckerPoint)
    (hP : positiveSupport P = Finset.univ) : ℝ :=
  topCellCanonicalDensity (topCellParametersOfPoint P hP)

/-- In its recovered coordinate frame, the projective top-cell form evaluates
to the positive logarithmic density. -/
theorem projectiveTopCellCanonicalForm_standardFrame
    (P : NormalizedPositivePluckerPoint)
    (hP : positiveSupport P = Finset.univ) :
    projectiveTopCellCanonicalForm P hP (fun j i => if i = j then 1 else 0) =
      projectiveTopCellCanonicalDensity P hP := by
  exact topCellCanonicalForm_standardFrame (topCellParametersOfPoint P hP)

/-- The canonical form on every point of the projective top positroid cell
has a strictly positive coefficient in its recovered orientation. -/
theorem projectiveTopCellCanonicalDensity_pos
    (P : NormalizedPositivePluckerPoint)
    (hP : positiveSupport P = Finset.univ) :
    0 < projectiveTopCellCanonicalDensity P hP := by
  exact topCellCanonicalDensity_pos (topCellParametersOfPoint P hP)

/-- The coefficient of the simple logarithmic pole on coordinate face `i`.
This is the residue density obtained by removing the `dxᵢ/xᵢ` factor. -/
def topCellBoundaryResidueDensity (x : PositiveTopCoordinates) (i : Fin 4) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (![x.a, x.b, x.c, x.e] j)⁻¹

theorem topCellCanonicalDensity_factor (x : PositiveTopCoordinates) (i : Fin 4) :
    topCellCanonicalDensity x =
      (![x.a, x.b, x.c, x.e] i)⁻¹ * topCellBoundaryResidueDensity x i := by
  unfold topCellCanonicalDensity topCellBoundaryResidueDensity
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

/-- Every coordinate boundary has a nonzero residue density on the positive
part of that boundary chart. -/
theorem topCellBoundaryResidueDensity_pos
    (x : PositiveTopCoordinates) (i : Fin 4) :
    0 < topCellBoundaryResidueDensity x i := by
  unfold topCellBoundaryResidueDensity
  have hx : ∀ j : Fin 4, 0 < (![x.a, x.b, x.c, x.e] j) := by
    intro j
    fin_cases j
    · simpa using x.a_pos
    · simpa using x.b_pos
    · simpa using x.c_pos
    · simpa using x.e_pos
  apply Finset.prod_pos
  intro j hj
  exact inv_pos.mpr (hx j)

end

end InfoGeometry.Topology.Gr24PositroidCanonicalForm
