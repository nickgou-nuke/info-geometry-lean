import Mathlib
import InfoGeometry.Projective.MatrixPluckerPositiveBridge
import InfoGeometry.Canonical.Gr24PositiveTopCellCanonicalForm

/-!
# Projective Plücker-support decomposition of nonnegative Gr(2,4)

The carrier is the actual projective image of full-rank 2×4 matrices with
nonnegative ordered Plücker coordinates.  Quotienting by equality of normalized
Plücker vectors removes the common positive scale.  Its realized support fibers
are disjoint, nonempty, and cover the carrier.  Each support is, by definition,
the basis support of a rank-two nonnegative Plücker representative (the
positroid convention); this file does not claim BCFW coordinates for every
boundary stratum or a canonical differential form on the closed space.
-/

namespace InfoGeometry.Canonical.Gr24PositroidSupport

open InfoGeometry.Canonical
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.Canonical.Gr24PositiveTopCell

abbrev Matrix2x4 := Matrix (Fin 2) (Fin 4) ℝ

/-- A nonnegative matrix representative of a genuine projective 2-plane; the
positive minor excludes the rank-deficient zero Plücker vector. -/
abbrev NonnegativeFullRankRep :=
  {M : Matrix2x4 // M ∈ positiveGrassmannianChart (k := 2) (n := 4) ∧
    ∃ i : Fin 6, 0 < matrixPluckerCoords M i}

/-- Sum of all six ordered Plücker coordinates. -/
noncomputable def pluckerMass (M : NonnegativeFullRankRep) : ℝ :=
  ∑ i : Fin 6, matrixPluckerCoords M.1 i

theorem pluckerMass_pos (M : NonnegativeFullRankRep) : 0 < pluckerMass M := by
  obtain ⟨i, hi⟩ := M.2.2
  have hnonneg := positiveGrassmannianChart_mem_matrixPluckerNonnegative M.1 M.2.1
  unfold pluckerMass
  exact Finset.sum_pos' (fun j _ => hnonneg j) ⟨i, Finset.mem_univ i, hi⟩

/-- Gauge-fixed projective Plücker coordinates, normalized to have sum one. -/
noncomputable def normalizedPlucker (M : NonnegativeFullRankRep) : Fin 6 → ℝ :=
  fun i => matrixPluckerCoords M.1 i / pluckerMass M

theorem normalizedPlucker_sum_one (M : NonnegativeFullRankRep) :
    (∑ i : Fin 6, normalizedPlucker M i) = 1 := by
  change (∑ i : Fin 6, matrixPluckerCoords M.1 i / pluckerMass M) = 1
  rw [← Finset.sum_div]
  change pluckerMass M / pluckerMass M = 1
  exact div_self (ne_of_gt (pluckerMass_pos M))

/-- The projective gauge keeps every Plücker coordinate nonnegative. -/
theorem normalizedPlucker_nonneg (M : NonnegativeFullRankRep) (i : Fin 6) :
    0 ≤ normalizedPlucker M i := by
  exact div_nonneg
    (positiveGrassmannianChart_mem_matrixPluckerNonnegative M.1 M.2.1 i)
    (le_of_lt (pluckerMass_pos M))

/-- The normalized Plücker coordinates still lie on the Klein quadric.
This is the rank-two Grassmann-Plücker relation after projective gauge fixing. -/
theorem normalizedPlucker_klein_relation (M : NonnegativeFullRankRep) :
    normalizedPlucker M 1 * normalizedPlucker M 4 =
      normalizedPlucker M 0 * normalizedPlucker M 5 +
        normalizedPlucker M 2 * normalizedPlucker M 3 := by
  have hmass : pluckerMass M ≠ 0 := ne_of_gt (pluckerMass_pos M)
  have hklein := matrixPluckerCoords_klein_relation M.1
  have hscaled :
      normalizedPlucker M 0 * normalizedPlucker M 5 -
        normalizedPlucker M 1 * normalizedPlucker M 4 +
        normalizedPlucker M 2 * normalizedPlucker M 3 = 0 := by
    change (matrixPluckerCoords M.1 0 / pluckerMass M) *
        (matrixPluckerCoords M.1 5 / pluckerMass M) -
        (matrixPluckerCoords M.1 1 / pluckerMass M) *
        (matrixPluckerCoords M.1 4 / pluckerMass M) +
        (matrixPluckerCoords M.1 2 / pluckerMass M) *
        (matrixPluckerCoords M.1 3 / pluckerMass M) = 0
    field_simp [hmass]
    nlinarith [hklein]
  linarith [hscaled]

/-- Boolean support of the normalized Plücker vector. -/
noncomputable def pluckerSupport (M : NonnegativeFullRankRep) : Fin 6 → Bool :=
  fun i => decide (0 < normalizedPlucker M i)

/-- A necessary positroid basis-exchange condition forced by the positive
Grassmannian Plücker relation: if bases `02` and `13` occur, at least one of
the two exchanged basis pairs `(01,23)` or `(03,12)` occurs. -/
theorem pluckerSupport_exchange (M : NonnegativeFullRankRep)
    (h14 : pluckerSupport M 1 = true) (h24 : pluckerSupport M 4 = true) :
    (pluckerSupport M 0 = true ∧ pluckerSupport M 5 = true) ∨
      (pluckerSupport M 2 = true ∧ pluckerSupport M 3 = true) := by
  have h1 : 0 < normalizedPlucker M 1 := by
    simpa [pluckerSupport] using h14
  have h4 : 0 < normalizedPlucker M 4 := by
    simpa [pluckerSupport] using h24
  have hprod : 0 < normalizedPlucker M 1 * normalizedPlucker M 4 := mul_pos h1 h4
  have hrel := normalizedPlucker_klein_relation M
  by_cases h0 : 0 < normalizedPlucker M 0
  · by_cases h5 : 0 < normalizedPlucker M 5
    · left
      exact ⟨by simpa [pluckerSupport, h0], by simpa [pluckerSupport, h5]⟩
    · right
      have hz5 : normalizedPlucker M 5 = 0 :=
        le_antisymm (le_of_not_gt h5) (normalizedPlucker_nonneg M 5)
      have hsum : 0 < normalizedPlucker M 2 * normalizedPlucker M 3 := by
        simpa [hrel, hz5] using hprod
      have h2 : 0 < normalizedPlucker M 2 := by
        by_contra hn
        have hz : normalizedPlucker M 2 = 0 :=
          le_antisymm (le_of_not_gt hn) (normalizedPlucker_nonneg M 2)
        rw [hz, zero_mul] at hsum
        exact (lt_irrefl _ hsum)
      have h3 : 0 < normalizedPlucker M 3 := by
        by_contra hn
        have hz : normalizedPlucker M 3 = 0 :=
          le_antisymm (le_of_not_gt hn) (normalizedPlucker_nonneg M 3)
        rw [hz, mul_zero] at hsum
        exact (lt_irrefl _ hsum)
      exact ⟨by simpa [pluckerSupport, h2], by simpa [pluckerSupport, h3]⟩
  · have hz0 : normalizedPlucker M 0 = 0 :=
      le_antisymm (le_of_not_gt h0) (normalizedPlucker_nonneg M 0)
    have hsum : 0 < normalizedPlucker M 2 * normalizedPlucker M 3 := by
      simpa [hrel, hz0] using hprod
    have h2 : 0 < normalizedPlucker M 2 := by
      by_contra hn
      have hz : normalizedPlucker M 2 = 0 :=
        le_antisymm (le_of_not_gt hn) (normalizedPlucker_nonneg M 2)
      rw [hz, zero_mul] at hsum
      exact (lt_irrefl _ hsum)
    have h3 : 0 < normalizedPlucker M 3 := by
      by_contra hn
      have hz : normalizedPlucker M 3 = 0 :=
        le_antisymm (le_of_not_gt hn) (normalizedPlucker_nonneg M 3)
      rw [hz, mul_zero] at hsum
      exact (lt_irrefl _ hsum)
    exact Or.inr ⟨by simpa [pluckerSupport, h2], by simpa [pluckerSupport, h3]⟩

/-- In a nonnegative rank-two Plücker vector, the crossing bases `02` and
`13` occur together exactly when one of the two exchanged pairs `(01,23)` or
`(03,12)` occurs.  This is the support-level form of the Grassmann--Plücker
equation; both directions use the equation and nonnegativity, rather than an
abstract Boolean support axiom. -/
theorem pluckerSupport_exchange_iff (M : NonnegativeFullRankRep) :
    (pluckerSupport M 1 = true ∧ pluckerSupport M 4 = true) ↔
      (pluckerSupport M 0 = true ∧ pluckerSupport M 5 = true) ∨
        (pluckerSupport M 2 = true ∧ pluckerSupport M 3 = true) := by
  constructor
  · intro h
    exact pluckerSupport_exchange M h.1 h.2
  · intro h
    have hrel := normalizedPlucker_klein_relation M
    have hprod : 0 < normalizedPlucker M 1 * normalizedPlucker M 4 := by
      rcases h with h | h
      · have h0 : 0 < normalizedPlucker M 0 := by
          simpa [pluckerSupport] using h.1
        have h5 : 0 < normalizedPlucker M 5 := by
          simpa [pluckerSupport] using h.2
        have hleft : 0 < normalizedPlucker M 0 * normalizedPlucker M 5 :=
          mul_pos h0 h5
        have hright : 0 ≤ normalizedPlucker M 2 * normalizedPlucker M 3 :=
          mul_nonneg (normalizedPlucker_nonneg M 2) (normalizedPlucker_nonneg M 3)
        rw [hrel]
        exact add_pos_of_pos_of_nonneg hleft hright
      · have h2 : 0 < normalizedPlucker M 2 := by
          simpa [pluckerSupport] using h.1
        have h3 : 0 < normalizedPlucker M 3 := by
          simpa [pluckerSupport] using h.2
        have hleft : 0 < normalizedPlucker M 2 * normalizedPlucker M 3 :=
          mul_pos h2 h3
        have hright : 0 ≤ normalizedPlucker M 0 * normalizedPlucker M 5 :=
          mul_nonneg (normalizedPlucker_nonneg M 0) (normalizedPlucker_nonneg M 5)
        rw [hrel]
        linarith
    have h1 : 0 < normalizedPlucker M 1 := by
      by_contra hn
      have hz : normalizedPlucker M 1 = 0 :=
        le_antisymm (le_of_not_gt hn) (normalizedPlucker_nonneg M 1)
      rw [hz, zero_mul] at hprod
      exact (lt_irrefl 0) hprod
    have h4 : 0 < normalizedPlucker M 4 := by
      by_contra hn
      have hz : normalizedPlucker M 4 = 0 :=
        le_antisymm (le_of_not_gt hn) (normalizedPlucker_nonneg M 4)
      rw [hz, mul_zero] at hprod
      exact (lt_irrefl 0) hprod
    exact ⟨by simpa [pluckerSupport, h1], by simpa [pluckerSupport, h4]⟩

/-- Two representatives define the same projective Plücker point exactly
when their normalized Plücker vectors agree. -/
noncomputable def sameProjectivePlucker (M N : NonnegativeFullRankRep) : Prop :=
  normalizedPlucker M = normalizedPlucker N

noncomputable instance projectivePluckerSetoid : Setoid NonnegativeFullRankRep where
  r := sameProjectivePlucker
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The nonnegative Grassmannian in its projective Plücker-coordinate model. -/
abbrev ProjectiveTNNGr24 := Quotient projectivePluckerSetoid

/-- The support signature is well-defined on projective Plücker points. -/
noncomputable def projectiveSupport : ProjectiveTNNGr24 → Fin 6 → Bool :=
  Quotient.lift pluckerSupport (by
    intro M N h
    funext i
    exact congrArg (fun v : Fin 6 → ℝ => decide (0 < v i)) h)

theorem projectiveSupport_mk (M : NonnegativeFullRankRep) :
    projectiveSupport (Quotient.mk projectivePluckerSetoid M) = pluckerSupport M := rfl

/-- The support of every projective point satisfies the rank-two positroid
basis-exchange implication inherited from its Plücker representative. -/
theorem projectiveSupport_exchange (q : ProjectiveTNNGr24)
    (h02 : projectiveSupport q 1 = true) (h13 : projectiveSupport q 4 = true) :
    (projectiveSupport q 0 = true ∧ projectiveSupport q 5 = true) ∨
      (projectiveSupport q 2 = true ∧ projectiveSupport q 3 = true) := by
  revert h02 h13
  refine Quotient.inductionOn q ?_
  intro M h02 h13
  rw [projectiveSupport_mk] at h02 h13 ⊢
  exact pluckerSupport_exchange M h02 h13

/-- The crossing-basis exchange rule descends to projective points and is an
exact characterization of the corresponding support condition. -/
theorem projectiveSupport_exchange_iff (q : ProjectiveTNNGr24) :
    (projectiveSupport q 1 = true ∧ projectiveSupport q 4 = true) ↔
      (projectiveSupport q 0 = true ∧ projectiveSupport q 5 = true) ∨
        (projectiveSupport q 2 = true ∧ projectiveSupport q 3 = true) := by
  refine Quotient.inductionOn q ?_
  intro M
  rw [projectiveSupport_mk]
  exact pluckerSupport_exchange_iff M

/-- Every nonnegative projective `Gr(2,4)` support either contains a cyclically
adjacent basis (`01`, `03`, `12`, or `23`), or is one of the two coordinate
0-cells supported only on `02` or only on `13`.

This is a support-level coverage dichotomy.  It identifies the two isolated
non-adjacent supports that any global chart atlas must handle separately; it
does not itself construct the other cyclic charts. -/
theorem projectiveSupport_adjacent_basis_or_coordinate_point
    (q : ProjectiveTNNGr24) :
    (∃ i : Fin 6,
      (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 5) ∧ projectiveSupport q i = true) ∨
      projectiveSupport q = (fun i => decide (i = 1)) ∨
      projectiveSupport q = (fun i => decide (i = 4)) := by
  classical
  by_cases hadj : ∃ i : Fin 6,
      (i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 5) ∧ projectiveSupport q i = true
  · exact Or.inl hadj
  · have hzero (i : Fin 6) (hi : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 5) :
        projectiveSupport q i ≠ true := by
      intro h
      exact hadj ⟨i, hi, h⟩
    have h14 : ¬ (projectiveSupport q 1 = true ∧
        projectiveSupport q 4 = true) := by
      intro h
      rcases (projectiveSupport_exchange_iff q).mp h with h | h
      · exact hzero 0 (Or.inl rfl) h.1
      · exact hzero 2 (Or.inr (Or.inl rfl)) h.1
    by_cases h1 : projectiveSupport q 1 = true
    · have h4 : projectiveSupport q 4 = false := by
        cases h : projectiveSupport q 4 <;> simp_all
      refine Or.inr (Or.inl ?_)
      funext j
      fin_cases j <;> simp_all [hzero]
    · have h1' : projectiveSupport q 1 = false := by
        cases h : projectiveSupport q 1 <;> simp_all
      have h4 : projectiveSupport q 4 = true := by
        have hnonempty : ∃ i : Fin 6, projectiveSupport q i = true := by
          refine Quotient.inductionOn q ?_
          intro M
          obtain ⟨i, hi⟩ := M.2.2
          rw [projectiveSupport_mk]
          have hpos : 0 < normalizedPlucker M i :=
            div_pos hi (pluckerMass_pos M)
          exact ⟨i, by simp [pluckerSupport, hpos]⟩
        obtain ⟨i, hi⟩ := hnonempty
        fin_cases i <;> simp_all [hzero]
      refine Or.inr (Or.inr ?_)
      funext j
      fin_cases j <;> simp_all [hzero]

theorem projectiveSupport_nonempty (q : ProjectiveTNNGr24) :
    ∃ i : Fin 6, projectiveSupport q i = true := by
  refine Quotient.inductionOn q ?_
  intro M
  obtain ⟨i, hi⟩ := M.2.2
  rw [projectiveSupport_mk]
  have hpos : 0 < normalizedPlucker M i := div_pos hi (pluckerMass_pos M)
  exact ⟨i, by simp [pluckerSupport, hpos]⟩

/-- A realized positroid support signature. -/
noncomputable def RealizedSupport :=
  {σ : Fin 6 → Bool // ∃ q : ProjectiveTNNGr24, projectiveSupport q = σ}

/-- The realized support index is finite because it is a subtype of the
finite set of six-bit signatures. -/
noncomputable instance realizedSupportFintype : Fintype RealizedSupport := by
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The positroid stratum with support signature `σ`. -/
noncomputable def positroidCell (σ : RealizedSupport) : Set ProjectiveTNNGr24 :=
  {q | projectiveSupport q = σ.1}

theorem positroidCell_nonempty (σ : RealizedSupport) :
    (positroidCell σ).Nonempty := by
  rcases σ.2 with ⟨q, hq⟩
  exact ⟨q, hq⟩

theorem positroidCell_pairwise_disjoint {σ τ : RealizedSupport}
    (hστ : σ.1 ≠ τ.1) : Disjoint (positroidCell σ) (positroidCell τ) := by
  rw [Set.disjoint_left]
  intro q hσ hτ
  exact hστ (hσ.symm.trans hτ)

theorem positroidCell_cover (q : ProjectiveTNNGr24) :
    ∃ σ : RealizedSupport, q ∈ positroidCell σ := by
  refine ⟨⟨projectiveSupport q, ⟨q, rfl⟩⟩, ?_⟩
  rfl

/-- Every projective nonnegative `Gr(2,4)` point belongs to exactly one
realized support stratum.  This is the set-theoretic positroid decomposition:
the strata are nonempty by construction, pairwise disjoint, and cover the
whole projective Plücker carrier. -/
theorem existsUnique_positroidCell (q : ProjectiveTNNGr24) :
    ∃! σ : RealizedSupport, q ∈ positroidCell σ := by
  refine ⟨⟨projectiveSupport q, ⟨q, rfl⟩⟩, rfl, ?_⟩
  intro τ hτ
  apply Subtype.ext
  exact hτ.symm

/-- The projective nonnegative Grassmannian is the union of its realized
positroid support strata. -/
theorem projectiveTNN_eq_iUnion_positroidCells :
    (Set.univ : Set ProjectiveTNNGr24) = ⋃ σ : RealizedSupport, positroidCell σ := by
  ext q
  constructor
  · intro _
    exact Set.mem_iUnion.mpr (positroidCell_cover q)
  · intro _
    trivial

/-- Distinct realized supports give disjoint positroid cells. -/
theorem positroidCells_disjoint_or_eq {σ τ : RealizedSupport} :
    Disjoint (positroidCell σ) (positroidCell τ) ∨ σ = τ := by
  by_cases h : σ.1 = τ.1
  · exact Or.inr (Subtype.ext h)
  · exact Or.inl (positroidCell_pairwise_disjoint h)

/-- Every realized stratum has a support satisfying the rank-two Plücker
basis-exchange condition. Thus the finite partition indexes actual positroid
bases, rather than arbitrary Boolean labels. -/
theorem positroidCell_support_exchange (σ : RealizedSupport)
    (h02 : σ.1 1 = true) (h13 : σ.1 4 = true) :
    (σ.1 0 = true ∧ σ.1 5 = true) ∨
      (σ.1 2 = true ∧ σ.1 3 = true) := by
  obtain ⟨q, hq⟩ := σ.2
  have h02q : projectiveSupport q 1 = true := by
    rw [hq]
    exact h02
  have h13q : projectiveSupport q 4 = true := by
    rw [hq]
    exact h13
  rcases projectiveSupport_exchange q h02q h13q with h | h
  · exact Or.inl ⟨by rw [hq] at h; exact h.1, by rw [hq] at h; exact h.2⟩
  · exact Or.inr ⟨by rw [hq] at h; exact h.1, by rw [hq] at h; exact h.2⟩

noncomputable def chartRepresentative (t : PositiveParameters) : NonnegativeFullRankRep := by
  let g := chartToGaugeFixedTopCell t
  have hstrict : g.1 ∈ positiveGrassmannianInterior (k := 2) (n := 4) := g.2.2.2.2.2
  have hpos := positiveGrassmannianInterior_mem_matrixPluckerPositive g.1 hstrict
  refine ⟨g.1, ?_, ⟨0, hpos 0⟩⟩
  intro s hs
  exact (hstrict s hs).le

/-- The top positroid cell is precisely the support with all six bases present. -/
theorem topCell_support_all_true (t : PositiveParameters) :
    projectiveSupport
      (Quotient.mk projectivePluckerSetoid (chartRepresentative t)) = fun _ => true := by
  rw [projectiveSupport_mk]
  funext i
  have hpos : 0 < normalizedPlucker (chartRepresentative t) i := by
    exact div_pos
      (positiveGrassmannianInterior_mem_matrixPluckerPositive
        (chartToGaugeFixedTopCell t).1
        (chartToGaugeFixedTopCell t).2.2.2.2.2 i)
      (pluckerMass_pos (chartRepresentative t))
  simpa [pluckerSupport, hpos]

end InfoGeometry.Canonical.Gr24PositroidSupport
