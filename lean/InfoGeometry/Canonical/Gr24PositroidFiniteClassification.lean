import Mathlib
import InfoGeometry.Topology.Gr24PositroidCanonicalForm
import InfoGeometry.Canonical.Gr24PositroidClassificationAndCanonicalForm
import InfoGeometry.Canonical.Gr24ComplementaryKleinPositroidCellForm
import InfoGeometry.Canonical.Gr24KleinMiddlePositroidForms

/-!
# Explicit finite classification of the `Gr(2,4)` positroid strata

The normalized nonnegative Klein quadric has one nonempty support stratum for
each nonempty subset of its six Plücker coordinates satisfying the rank-two
exchange law.  There are exactly 33 such strata.  The support equivalence and
the canonical-form statements below reuse the concrete Plücker and differential
form owners; no generic cell decomposition or cell-sum axiom is introduced.

Canonical forms are attached cellwise in each cell's own coordinates: the 26
Klein-term-free cells are projective simplices, and the seven relation-bearing
cells use the `p02 > 0` chart with `p13` solved by the Klein equation.  These
are native logarithmic forms on the finite `Gr(2,4)` Plücker model; no claim
about a general `Gr(k,n)` or an amplituhedron BCFW form is made here.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.Gr24PositroidFiniteClassification

open InfoGeometry.Topology.Gr24PositroidCanonicalForm
open InfoGeometry.Canonical.Gr24PositroidClassificationAndCanonicalForm
open InfoGeometry.Canonical.Gr24PositroidDecompositionCanonicalForm
open InfoGeometry.Canonical.Gr24PositiveTopCell
open InfoGeometry.Canonical.Gr24PositroidChartFaceForms
open InfoGeometry.Canonical.Gr24ComplementaryKleinPositroidCellForm
open InfoGeometry.Canonical.Gr24KleinMiddlePositroidForms

/-- Explicit combinatorial index for the nonempty rank-two positroid supports
in Plücker order `01, 02, 03, 12, 13, 23`. -/
private def supportBits (I : Finset (Fin 6)) : Fin 6 → Bool :=
  fun i => decide (i ∈ I)

private def bitsSupport (b : Fin 6 → Bool) : Finset (Fin 6) :=
  Finset.univ.filter fun i => b i

/-- A Boolean support contains one of the three quadratic monomials in the
rank-two Klein relation. -/
private def bitsContainKleinPair (b : Fin 6 → Bool) (k : Fin 3) : Prop :=
  ∀ i ∈ kleinComplementaryPairs k, b i = true

private theorem bitsContainKleinPair_iff (b : Fin 6 → Bool) (k : Fin 3) :
    bitsContainKleinPair b k ↔ kleinComplementaryPairs k ⊆ bitsSupport b := by
  constructor
  · intro h i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i hi⟩
  · intro h i hi
    exact (Finset.mem_filter.mp (h hi)).2

/-- The Boolean simplex condition is exactly the termwise-zero Klein
condition on its corresponding Plücker support. -/
private theorem simplexBits_iff_support (b : Fin 6 → Bool) :
    (∀ k, ¬ bitsContainKleinPair b k) ↔
      simplexPositroidSupport (bitsSupport b) := by
  rw [simplexPositroidSupport]
  constructor
  · intro h k hsub
    apply h k
    exact (bitsContainKleinPair_iff b k).2 hsub
  · intro h k hpair
    apply h k
    exact (bitsContainKleinPair_iff b k).1 hpair

private def isAdmissibleBits (b : Fin 6 → Bool) : Prop :=
  (∃ i, b i = true) ∧
    ((b 1 = true ∧ b 4 = true) ↔
      ((b 0 = true ∧ b 5 = true) ∨ (b 2 = true ∧ b 3 = true)))

/-- Computable six-bit version of the nonempty rank-two exchange supports. -/
abbrev AdmissibleSupport := {b : Fin 6 → Bool // isAdmissibleBits b}

private instance admissibleBitsDecidable (b : Fin 6 → Bool) :
    Decidable (isAdmissibleBits b) := by
  unfold isAdmissibleBits
  infer_instance

private theorem bitsSupport_nonempty_iff (b : Fin 6 → Bool) :
    (bitsSupport b).Nonempty ↔ ∃ i, b i = true := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

private theorem bitsSupport_exchange_iff (b : Fin 6 → Bool) :
    IsGr24PositroidSupport (bitsSupport b) ↔
      ((b 1 = true ∧ b 4 = true) ↔
        ((b 0 = true ∧ b 5 = true) ∨ (b 2 = true ∧ b 3 = true))) := by
  simp [IsGr24PositroidSupport, bitsSupport]

/-- The exchange characterization identifies realized projective support
strata exactly with the nonempty combinatorial supports. -/
noncomputable def supportEquiv : PositroidSupport ≃ AdmissibleSupport where
  toFun I := ⟨supportBits I.1, by
    obtain ⟨hne, hex⟩ := (positroidSupport_iff_exchange I.1).mp I.2
    constructor
    · obtain ⟨i, hi⟩ := hne
      exact ⟨i, by simp [supportBits, hi]⟩
    · simpa [supportBits, IsGr24PositroidSupport] using hex⟩
  invFun I := ⟨bitsSupport I.1, (positroidSupport_iff_exchange _).2
    ⟨bitsSupport_nonempty_iff I.1 |>.2 I.2.1,
      bitsSupport_exchange_iff I.1 |>.2 I.2.2⟩⟩
  left_inv I := by
    apply Subtype.ext
    ext i
    simp [supportBits, bitsSupport]
  right_inv I := by
    apply Subtype.ext
    funext i
    simp [supportBits, bitsSupport]

/-- The `Gr(2,4)` rank-two exchange rule has exactly 33 nonempty supports.

For the three complementary coordinate pairs, the products have respectively
3, 1, and 1 truth patterns as zero/nonzero; the exchange biconditional
selects 34 patterns including the empty support, which normalization excludes.
The finite Boolean computation certifies the resulting exact count. -/
theorem admissibleSupport_card : Fintype.card AdmissibleSupport = 33 := by
  decide

/-- The admissible Plücker supports on which the Klein equation vanishes
termwise. These are exactly the open projective-simplex cells: the supported
coordinates are independent apart from the sum-one gauge. -/
abbrev SimplexAdmissibleSupport :=
  {b : AdmissibleSupport // ∀ k, ¬ bitsContainKleinPair b.1 k}

private instance simplexAdmissibleSupportDecidable (b : AdmissibleSupport) :
    Decidable (∀ k, ¬ bitsContainKleinPair b.1 k) := by
  unfold bitsContainKleinPair
  infer_instance

/-- The complementary admissible supports, where at least one Klein monomial
is nonzero and the Plücker equation imposes a genuine relation. -/
abbrev KleinCoupledAdmissibleSupport :=
  {b : AdmissibleSupport // ∃ k, bitsContainKleinPair b.1 k}

private instance kleinCoupledAdmissibleSupportDecidable (b : AdmissibleSupport) :
    Decidable (∃ k, bitsContainKleinPair b.1 k) := by
  unfold bitsContainKleinPair
  infer_instance

/-- Exactly 26 of the 33 nonempty `Gr(2,4)` positroid supports are simplex
cells. Their intrinsic forms are the `simplexPositroidCanonicalForm`s, with
the positivity and pivot-independence theorems in
`Gr24PositroidDecompositionCanonicalForm`. -/
theorem simplexAdmissibleSupport_card :
    Fintype.card SimplexAdmissibleSupport = 26 := by
  decide

/-- Under `supportEquiv`, the 26 Boolean simplex labels are exactly the
nonempty realized supports whose Klein monomials all vanish termwise. -/
theorem simplexAdmissibleSupport_matches_positroidCells
    (b : AdmissibleSupport) :
    (∀ k, ¬ bitsContainKleinPair b.1 k) ↔
      simplexPositroidSupport (supportEquiv.symm b).1 := by
  change (∀ k, ¬ bitsContainKleinPair b.1 k) ↔
    simplexPositroidSupport (bitsSupport b.1)
  exact simplexBits_iff_support b.1

/-- Every one of the 26 termwise-Klein-zero cells is an actual projective
simplex and carries its intrinsic positive logarithmic top form. -/
theorem simplex_support_has_canonical_form
    (b : SimplexAdmissibleSupport) :
    ∃ I : SimplexCellSupport, ∃ p : {p : Fin 6 // p ∈ I.1},
      ∃ P : SimplexPositroidCell I,
        0 < simplexPositroidCanonicalForm I p P (simplexCellFrame I p) := by
  let I₀ := supportEquiv.symm b.1
  have hsimplex : simplexPositroidSupport I₀.1 :=
    (simplexBits_iff_support b.1).mp b.2
  let I : SimplexCellSupport := ⟨I₀.1, hsimplex⟩
  obtain ⟨P, hP⟩ := I₀.2
  have hnonempty : I.1.Nonempty :=
    (positroidSupport_iff_exchange I₀.1).mp I₀.2 |>.1
  obtain ⟨p, hp⟩ := hnonempty
  exact ⟨I, ⟨p, hp⟩, ⟨P, hP⟩,
    simplexPositroidCanonicalForm_frame_pos I ⟨p, hp⟩ ⟨P, hP⟩⟩

/-- Exactly seven positroid supports have a nontrivial Klein-monomial
constraint. They are the top cell and six lower-dimensional relation-bearing
cells; the top cell and one lower cell currently have explicit projective
logarithmic-form charts in the canonical-form owners. -/
theorem kleinCoupledAdmissibleSupport_card :
    Fintype.card KleinCoupledAdmissibleSupport = 7 := by
  decide

/-- Every one of the seven relation-bearing positroid supports has a point
and a positive intrinsic logarithmic top form in the `p02` projective chart.
The Klein relation solves the dependent `p13` coordinate, while the other
supported Plücker ratios index the tangent directions. -/
theorem kleinCoupled_support_has_canonical_form
    (b : KleinCoupledAdmissibleSupport) :
    ∃ I : MiddleKleinSupport, ∃ P : MiddleCellPoint I,
      0 < middleCellCanonicalForm I P (middleCellFrame I) := by
  let I₀ := supportEquiv.symm b.1
  have hnotSimplex : ¬ simplexPositroidSupport I₀.1 := by
    intro hs
    have hbits := (simplexBits_iff_support b.1).2 hs
    obtain ⟨k, hk⟩ := b.2
    exact hbits k hk
  have hsplit := positroidSupport_simplex_or_middle I₀
  have hmiddle : (1 : Fin 6) ∈ I₀.1 ∧ (4 : Fin 6) ∈ I₀.1 := by
    rcases hsplit with hs | hm
    · exact (hnotSimplex hs).elim
    · exact hm
  let I : MiddleKleinSupport := ⟨I₀, hmiddle⟩
  obtain ⟨P, hP⟩ := I₀.2
  exact ⟨I, ⟨P, hP⟩,
    middleCellCanonicalForm_frame_pos I ⟨P, hP⟩⟩

/-- Cellwise canonical-form coverage for the entire finite `Gr(2,4)`
positroid decomposition. Each of the 33 admissible supports is either a
projective simplex with its simplex `dlog` form, or a relation-bearing cell
with its Klein-chart `dlog` form. -/
theorem every_positroid_cell_has_canonical_form
    (b : AdmissibleSupport) :
    (∃ I : SimplexCellSupport, ∃ p : {p : Fin 6 // p ∈ I.1},
      ∃ P : SimplexPositroidCell I,
        0 < simplexPositroidCanonicalForm I p P (simplexCellFrame I p)) ∨
    (∃ I : MiddleKleinSupport, ∃ P : MiddleCellPoint I,
      0 < middleCellCanonicalForm I P (middleCellFrame I)) := by
  classical
  by_cases hs : ∀ k, ¬ bitsContainKleinPair b.1 k
  · exact Or.inl (simplex_support_has_canonical_form ⟨b, hs⟩)
  · obtain ⟨k, hk⟩ := not_forall.mp hs
    exact Or.inr
      (kleinCoupled_support_has_canonical_form ⟨b, ⟨k, by simpa using hk⟩⟩)

/-- Every admissible support belongs to exactly one side of the simplex /
Klein-coupled split. -/
theorem admissibleSupport_simplex_or_kleinCoupled (b : AdmissibleSupport) :
    (∀ k, ¬ bitsContainKleinPair b.1 k) ∨
      (∃ k, bitsContainKleinPair b.1 k) := by
  classical
  by_cases h : ∀ k, ¬ bitsContainKleinPair b.1 k
  · exact Or.inl h
  · obtain ⟨k, hk⟩ := not_forall.mp h
    exact Or.inr ⟨k, by simpa using hk⟩

/-- There are exactly 33 nonempty positroid strata in the normalized
nonnegative `Gr(2,4)` Plücker model. -/
theorem positroidSupport_card : Fintype.card PositroidSupport = 33 := by
  rw [Fintype.card_congr supportEquiv]
  exact admissibleSupport_card

/-- Each of the 33 actual positroid cells is nonempty, and different support
labels give disjoint cells. -/
theorem cells_nonempty_and_pairwise_disjoint
    (I J : PositroidSupport) (hIJ : I ≠ J) :
    (supportStratum I.1).Nonempty ∧ Disjoint (supportStratum I.1)
      (supportStratum J.1) := by
  constructor
  · obtain ⟨P, hP⟩ := I.2
    exact ⟨P, hP⟩
  · exact supportStrata_disjoint hIJ

/-- The 33 support strata cover the full normalized nonnegative Grassmannian.
This is the finite, exhaustive positroid decomposition in Plücker support. -/
theorem positroid_decomposition :
    (⋃ I : PositroidSupport, supportStratum I.1) =
      (Set.univ : Set NormalizedPositivePluckerPoint) :=
  supportStrata_cover

/-- The cell indicators form a partition of unity on every normalized
nonnegative point, now with the exact 33-cell combinatorial index. -/
theorem positroid_partition_of_unity (P : NormalizedPositivePluckerPoint) :
    (∑ I : PositroidSupport, supportStratumIndicator I P) = 1 :=
  supportStrata_indicator_sum P

/-- The unique full-support stratum is parametrized by the positive-network
chart, and its genuine alternating top form has positive logarithmic density. -/
theorem topCell_chart_form_positive (t : PositiveParameters) :
    0 < canonicalTopForm t coordinateFrame :=
  top_cell_canonical_form_positive t

/-- On each exact-support face of the closed network chart, the existing
intrinsic canonical form evaluates to the product of the logarithmic factors
of its live coordinates. -/
theorem chartFace_form_value (I : Finset (Fin 4))
    (u : FaceParameters I) :
  positroidFaceCanonicalForm I u (positroidFaceFrame I) =
      positroidFaceDensity I u :=
  chart_face_canonical_form_value I u

/-- The second minimal Klein-coupled positroid support, `{01,02,13,23}`, is
one of the 33 realized cells in the exhaustive support decomposition. -/
def complementaryKleinPositroidSupport : PositroidSupport :=
  ⟨({0, 1, 4, 5} : Finset (Fin 6)),
    (positroidSupport_iff_exchange _).2 ⟨by simp,
      by norm_num [IsGr24PositroidSupport]⟩⟩

/-- The complementary minimal relation-bearing cell has its own genuine
two-form on the entire cell, obtained from its proved projective chart. -/
theorem complementaryKlein_cell_form_positive
    (P : ComplementaryKleinCell) :
    0 < complementaryKleinCellCanonicalForm P complementaryKleinFrame :=
  complementaryKleinCellCanonicalForm_positive P

end InfoGeometry.Canonical.Gr24PositroidFiniteClassification
