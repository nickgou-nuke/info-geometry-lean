import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentSpace

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Topological projection of the observational symbolic-latent quotient

The observational quotient is already defined by the native setoid in
`SymbolicLatentSpace`.  This owner exposes its canonical observation readout
as a morphism in `TopCat`; no new quotient or feature-space carrier is
introduced.
-/

def symbolicObservationQuotientTopCatHom
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    TopCat.of (_root_.Quotient (symbolicObservationalSetoid S)) ⟶
      TopCat.of (ι → ℝ) :=
  TopCat.ofHom
    { toFun := symbolicObservationQuotientMap S
      continuous_toFun := continuous_symbolicObservationQuotientMap S }

theorem symbolicObservationQuotientTopCatHom_apply
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    symbolicObservationQuotientTopCatHom S q =
      symbolicObservationQuotientMap S q :=
  rfl

theorem symbolicObservationQuotientTopCatHom_injective
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Function.Injective (symbolicObservationQuotientTopCatHom S) := by
  exact injective_symbolicObservationQuotientMap S

noncomputable def symbolicObservationQuotientRangeMap
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    _root_.Quotient (symbolicObservationalSetoid S) →
      Set.range (symbolicObservationQuotientMap S) :=
  symbolicObservationQuotientRangeEquiv S

theorem continuous_symbolicObservationQuotientRangeMap
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Continuous (symbolicObservationQuotientRangeMap S) := by
  apply continuous_induced_rng.mpr
  simpa [symbolicObservationQuotientRangeMap] using
    continuous_symbolicObservationQuotientMap S

noncomputable def symbolicObservationQuotientRangeTopCatHom
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    TopCat.of (_root_.Quotient (symbolicObservationalSetoid S)) ⟶
      TopCat.of (Set.range (symbolicObservationQuotientMap S)) :=
  TopCat.ofHom
    { toFun := symbolicObservationQuotientRangeMap S
      continuous_toFun := continuous_symbolicObservationQuotientRangeMap S }

theorem symbolicObservationQuotientRangeTopCatHom_apply
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (q : _root_.Quotient (symbolicObservationalSetoid S)) :
    symbolicObservationQuotientRangeTopCatHom S q =
      symbolicObservationQuotientRangeMap S q :=
  rfl

noncomputable def symbolicObservationQuotientRangeHomeomorph
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (hquot : Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S)) :
    _root_.Quotient (symbolicObservationalSetoid S) ≃ₜ
      Set.range (symbolicObservationQuotientMap S) := by
  let e := symbolicObservationQuotientRangeEquiv S
  refine
    { toEquiv := e
      continuous_toFun := continuous_symbolicObservationQuotientRangeMap S
      continuous_invFun := ?_ }
  apply hquot.continuous_iff.mpr
  change Continuous (e.symm ∘ symbolicObservationQuotientRangeMap S)
  have hcomp : e.symm ∘ symbolicObservationQuotientRangeMap S = id := by
    funext q
    exact e.left_inv q
  rw [hcomp]
  exact continuous_id

noncomputable def symbolicObservationQuotientRangeInverseTopCatHom
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (hquot : Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S)) :
    TopCat.of (Set.range (symbolicObservationQuotientMap S)) ⟶
      TopCat.of (_root_.Quotient (symbolicObservationalSetoid S)) :=
  TopCat.ofHom
    { toFun := (symbolicObservationQuotientRangeHomeomorph S hquot).symm
      continuous_toFun :=
        (symbolicObservationQuotientRangeHomeomorph S hquot).symm.continuous_toFun }

theorem symbolicObservationQuotientRangeTopCatHom_isIso
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (hquot : Topology.IsQuotientMap (symbolicObservationQuotientRangeMap S)) :
    IsIso (symbolicObservationQuotientRangeTopCatHom S) := by
  refine IsIso.mk ⟨symbolicObservationQuotientRangeInverseTopCatHom S hquot, ?_, ?_⟩
  · apply TopCat.hom_ext
    ext q
    change (symbolicObservationQuotientRangeHomeomorph S hquot).symm
        ((symbolicObservationQuotientRangeHomeomorph S hquot) q) = q
    exact (symbolicObservationQuotientRangeHomeomorph S hquot).symm_apply_apply q
  · apply TopCat.hom_ext
    simp only [symbolicObservationQuotientRangeInverseTopCatHom,
      symbolicObservationQuotientRangeTopCatHom,
      TopCat.hom_comp, TopCat.hom_id, TopCat.hom_ofHom]
    apply ContinuousMap.ext
    intro y
    dsimp
    have hmap (q : _root_.Quotient (symbolicObservationalSetoid S)) :
        symbolicObservationQuotientRangeMap S q =
          symbolicObservationQuotientRangeHomeomorph S hquot q := by
      rfl
    rw [hmap]
    change (symbolicObservationQuotientRangeHomeomorph S hquot)
        ((symbolicObservationQuotientRangeHomeomorph S hquot).symm y) = y
    exact (symbolicObservationQuotientRangeHomeomorph S hquot).apply_symm_apply y

def symbolicObservationQuotientRangeInclusionTopCatHom
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    TopCat.of (Set.range (symbolicObservationQuotientMap S)) ⟶
      TopCat.of (ι → ℝ) :=
  TopCat.ofHom
    { toFun := (Subtype.val : Set.range (symbolicObservationQuotientMap S) → (ι → ℝ))
      continuous_toFun := continuous_subtype_val }

theorem symbolicObservationQuotientTopCatHom_factorization
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    symbolicObservationQuotientRangeTopCatHom S ≫
        symbolicObservationQuotientRangeInclusionTopCatHom S =
      symbolicObservationQuotientTopCatHom S := by
  ext q
  rfl

/-- The factorization through the range object is unique. -/
theorem symbolicObservationQuotientTopCatHom_factorization_unique
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    {u : TopCat.of (_root_.Quotient (symbolicObservationalSetoid S)) ⟶
      TopCat.of (Set.range (symbolicObservationQuotientMap S))}
    (h : u ≫ symbolicObservationQuotientRangeInclusionTopCatHom S =
      symbolicObservationQuotientTopCatHom S) :
    u = symbolicObservationQuotientRangeTopCatHom S := by
  ext q x
  have hq := congrArg (fun m => (m.hom) q) h
  have hqx := congrArg (fun y => y x) hq
  simpa [symbolicObservationQuotientRangeInclusionTopCatHom,
    symbolicObservationQuotientTopCatHom,
    symbolicObservationQuotientRangeTopCatHom] using hqx

theorem isCompact_symbolicObservationQuotient_range
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    IsCompact (Set.range (symbolicObservationQuotientMap S)) := by
  exact isCompact_range (continuous_symbolicObservationQuotientMap S)

theorem isClosed_symbolicObservationQuotient_range
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    IsClosed (Set.range (symbolicObservationQuotientMap S)) := by
  exact (isCompact_symbolicObservationQuotient_range S).isClosed

theorem symbolicObservationQuotientRangeInclusion_isClosedEmbedding
    {X ι : Type} [TopologicalSpace X] [CompactSpace X]
    [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    Topology.IsClosedEmbedding
      (Subtype.val : Set.range (symbolicObservationQuotientMap S) → (ι → ℝ)) := by
  exact (isClosed_symbolicObservationQuotient_range S).isClosedEmbedding_subtypeVal

end InfoGeometry.Topology
