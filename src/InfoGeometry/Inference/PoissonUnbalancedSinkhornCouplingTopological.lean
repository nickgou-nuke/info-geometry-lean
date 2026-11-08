import InfoGeometry.Inference.PoissonUnbalancedSinkhornTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Topological marginal readouts for finite couplings

The finite coupling space carries its product topology.  Its row and column
marginals are continuous finite-sum readouts.  This is the topological layer
needed before discussing any parameterized transport property; it does not
assert existence or convergence of an optimizer.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Row Col : Type*}
  [Fintype Row] [Nonempty Row] [Fintype Col] [Nonempty Col]

abbrev PositiveRowProfile (Row : Type*) :=
  {target : Row → ℝ // ∀ i, 0 < target i}
abbrev PositiveColProfile (Col : Type*) :=
  {target : Col → ℝ // ∀ j, 0 < target j}
abbrev PositiveProfile (X : Type*) :=
  {target : X → ℝ // ∀ x, 0 < target x}
abbrev FullObjectiveParameterSpace (Row Col : Type*) :=
  (PositiveRowProfile Row × PositiveColProfile Col) × ((ℝ × ℝ) × ℝ)

noncomputable def transportRowMassContinuousMap
    (i : Row) : C((Row → Col → ℝ), ℝ) :=
  ContinuousMap.mk
    (fun coupling => transportRowMass coupling i)
    (by
      unfold transportRowMass
      fun_prop)

@[simp] theorem transportRowMassContinuousMap_apply
    (i : Row) (coupling : Row → Col → ℝ) :
    transportRowMassContinuousMap i coupling = transportRowMass coupling i :=
  rfl

noncomputable def transportColMassContinuousMap
    (j : Col) : C((Row → Col → ℝ), ℝ) :=
  ContinuousMap.mk
    (fun coupling => transportColMass coupling j)
    (by
      unfold transportColMass
      fun_prop)

@[simp] theorem transportColMassContinuousMap_apply
    (j : Col) (coupling : Row → Col → ℝ) :
    transportColMassContinuousMap j coupling = transportColMass coupling j :=
  rfl

theorem transportRowMassContinuousMap_pos
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (i : Row) :
    0 < transportRowMassContinuousMap i T.coupling :=
  T.row_mass_pos i

theorem transportColMassContinuousMap_pos
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (j : Col) :
    0 < transportColMassContinuousMap j T.coupling :=
  T.col_mass_pos j

noncomputable def gklTermContinuousMap :
    C((({x : ℝ // 0 < x}) × {y : ℝ // 0 < y}), ℝ) :=
  ContinuousMap.mk
    (fun p => PositiveMeasure.gklTerm p.1.1 p.2.1)
    (by
      unfold PositiveMeasure.gklTerm
      fun_prop (disch := aesop))

@[simp] theorem gklTermContinuousMap_apply
    (p : ({x : ℝ // 0 < x}) × {y : ℝ // 0 < y}) :
    gklTermContinuousMap p = PositiveMeasure.gklTerm p.1.1 p.2.1 :=
  rfl

noncomputable def generalizedKLContinuousMap
    {X : Type*} [Fintype X] :
    C((PositiveProfile X × PositiveProfile X), ℝ) :=
  ContinuousMap.mk
    (fun p => ∑ x : X, PositiveMeasure.gklTerm (p.1.1 x) (p.2.1 x))
    (by
      refine continuous_finset_sum Finset.univ ?_
      intro x hx
      let first : C((PositiveProfile X × PositiveProfile X), {x : ℝ // 0 < x}) :=
        ContinuousMap.mk (fun p => ⟨p.1.1 x, p.1.2 x⟩) (by
          apply Continuous.subtype_mk
          exact (continuous_apply x).comp
            (continuous_subtype_val.comp continuous_fst))
      let second : C((PositiveProfile X × PositiveProfile X), {x : ℝ // 0 < x}) :=
        ContinuousMap.mk (fun p => ⟨p.2.1 x, p.2.2 x⟩) (by
          apply Continuous.subtype_mk
          exact (continuous_apply x).comp
            (continuous_subtype_val.comp continuous_snd))
      exact (gklTermContinuousMap.comp
        (ContinuousMap.prodMk first second)).continuous)

@[simp] theorem generalizedKLContinuousMap_apply
    {X : Type*} [Fintype X]
    (p : PositiveProfile X × PositiveProfile X) :
    generalizedKLContinuousMap p =
      ∑ x : X, PositiveMeasure.gklTerm (p.1.1 x) (p.2.1 x) :=
  rfl

noncomputable def unbalancedRowPenaltyContinuousMap
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    C(({target : Row → ℝ // ∀ i, 0 < target i}), ℝ) :=
  ContinuousMap.mk
    (fun target =>
      ∑ i : Row,
        PositiveMeasure.gklTerm (transportRowMass T.coupling i) (target.1 i))
    (by
      refine continuous_finset_sum Finset.univ ?_
      intro i hi
      let mass : {x : ℝ // 0 < x} :=
        ⟨transportRowMass T.coupling i, T.row_mass_pos i⟩
      let targetAt : C(({target : Row → ℝ // ∀ i, 0 < target i}),
          {x : ℝ // 0 < x}) :=
        ContinuousMap.mk (fun target => ⟨target.1 i, target.2 i⟩) (by
          apply Continuous.subtype_mk
          exact (continuous_apply i).comp continuous_subtype_val)
      let massMap : C(({target : Row → ℝ // ∀ i, 0 < target i}),
          {x : ℝ // 0 < x}) := ContinuousMap.const _ mass
      exact (gklTermContinuousMap.comp
        (ContinuousMap.prodMk massMap targetAt)).continuous)

@[simp] theorem unbalancedRowPenaltyContinuousMap_apply
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (target : {target : Row → ℝ // ∀ i, 0 < target i}) :
    unbalancedRowPenaltyContinuousMap T target =
      ∑ i : Row,
        PositiveMeasure.gklTerm (transportRowMass T.coupling i) (target.1 i) :=
  rfl

noncomputable def unbalancedColPenaltyContinuousMap
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    C(({target : Col → ℝ // ∀ j, 0 < target j}), ℝ) :=
  ContinuousMap.mk
    (fun target =>
      ∑ j : Col,
        PositiveMeasure.gklTerm (transportColMass T.coupling j) (target.1 j))
    (by
      refine continuous_finset_sum Finset.univ ?_
      intro j hj
      let mass : {x : ℝ // 0 < x} :=
        ⟨transportColMass T.coupling j, T.col_mass_pos j⟩
      let targetAt : C(({target : Col → ℝ // ∀ j, 0 < target j}),
          {x : ℝ // 0 < x}) :=
        ContinuousMap.mk (fun target => ⟨target.1 j, target.2 j⟩) (by
          apply Continuous.subtype_mk
          exact (continuous_apply j).comp continuous_subtype_val)
      let massMap : C(({target : Col → ℝ // ∀ j, 0 < target j}),
          {x : ℝ // 0 < x}) := ContinuousMap.const _ mass
      exact (gklTermContinuousMap.comp
        (ContinuousMap.prodMk massMap targetAt)).continuous)

@[simp] theorem unbalancedColPenaltyContinuousMap_apply
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (target : {target : Col → ℝ // ∀ j, 0 < target j}) :
    unbalancedColPenaltyContinuousMap T target =
      ∑ j : Col,
        PositiveMeasure.gklTerm (transportColMass T.coupling j) (target.1 j) :=
  rfl

theorem unbalancedRowPenaltyContinuousMap_target_eq
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    unbalancedRowPenaltyContinuousMap T
        ⟨T.targetRowMass, T.target_row_mass_pos⟩ =
      unbalancedRowPenalty T := by
  rfl

theorem unbalancedColPenaltyContinuousMap_target_eq
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    unbalancedColPenaltyContinuousMap T
        ⟨T.targetColMass, T.target_col_mass_pos⟩ =
      unbalancedColPenalty T := by
  rfl

noncomputable def fullUnbalancedTransportObjectiveProfilesContinuousMap
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ) :
    C(FullObjectiveParameterSpace (Row := Row) (Col := Col), ℝ) :=
  ContinuousMap.mk
    (fun p =>
      (∑ i : Row, ∑ j : Col, T.coupling i j * cost i j)
        + p.2.1.2 * unbalancedRowPenaltyContinuousMap T p.1.1
        + p.2.2 * unbalancedColPenaltyContinuousMap T p.1.2
        + p.2.1.1 * entropicTransportPenalty T reference)
    (by
      fun_prop)

@[simp] theorem fullUnbalancedTransportObjectiveProfilesContinuousMap_apply
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ)
    (p : FullObjectiveParameterSpace (Row := Row) (Col := Col)) :
    fullUnbalancedTransportObjectiveProfilesContinuousMap T cost reference p =
      (∑ i : Row, ∑ j : Col, T.coupling i j * cost i j)
        + p.2.1.2 * unbalancedRowPenaltyContinuousMap T p.1.1
        + p.2.2 * unbalancedColPenaltyContinuousMap T p.1.2
      + p.2.1.1 * entropicTransportPenalty T reference :=
  rfl

theorem fullUnbalancedTransportObjectiveProfilesContinuousMap_target_eq
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ)
    (epsilon rowPenalty colPenalty : ℝ) :
    fullUnbalancedTransportObjectiveProfilesContinuousMap T cost reference
        ((⟨T.targetRowMass, T.target_row_mass_pos⟩,
          ⟨T.targetColMass, T.target_col_mass_pos⟩),
          ((epsilon, rowPenalty), colPenalty)) =
      fullUnbalancedTransportObjective T cost reference epsilon rowPenalty colPenalty := by
  rfl

theorem fullUnbalancedTransportObjectiveProfilesContinuousMap_target_nonneg
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ)
    (hcost : ∀ i j, 0 ≤ cost i j)
    (href : ∀ i j, 0 < reference i j)
    {epsilon rowPenalty colPenalty : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hrowPenalty : 0 ≤ rowPenalty)
    (hcolPenalty : 0 ≤ colPenalty) :
    0 ≤ fullUnbalancedTransportObjectiveProfilesContinuousMap T cost reference
      ((⟨T.targetRowMass, T.target_row_mass_pos⟩,
        ⟨T.targetColMass, T.target_col_mass_pos⟩),
        ((epsilon, rowPenalty), colPenalty)) := by
  rw [fullUnbalancedTransportObjectiveProfilesContinuousMap_target_eq]
  exact fullUnbalancedTransportObjective_nonneg T cost reference hcost href
    hepsilon hrowPenalty hcolPenalty

theorem fullUnbalancedTransportObjectiveProfilesContinuousMap_sublevel_isClosed
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ) (c : ℝ) :
    IsClosed {p : FullObjectiveParameterSpace (Row := Row) (Col := Col) |
      fullUnbalancedTransportObjectiveProfilesContinuousMap T cost reference p ≤ c} := by
  change IsClosed
    ((fullUnbalancedTransportObjectiveProfilesContinuousMap T cost reference) ⁻¹'
      Set.Iic c)
  exact isClosed_Iic.preimage
    (fullUnbalancedTransportObjectiveProfilesContinuousMap T cost reference).continuous

theorem fullUnbalancedTransportObjectiveProfilesContinuousMap_levelSet_isClosed
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ) (c : ℝ) :
    IsClosed {p : FullObjectiveParameterSpace (Row := Row) (Col := Col) |
      fullUnbalancedTransportObjectiveProfilesContinuousMap T cost reference p = c} := by
  change IsClosed
    ((fullUnbalancedTransportObjectiveProfilesContinuousMap T cost reference) ⁻¹'
      ({c} : Set ℝ))
  exact isClosed_singleton.preimage
    (fullUnbalancedTransportObjectiveProfilesContinuousMap T cost reference).continuous

end InfoGeometry.Inference
