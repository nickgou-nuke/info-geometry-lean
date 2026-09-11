import InfoGeometry.Inference.PoissonUnbalancedSinkhornCouplingTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.PoissonUnbalancedSinkhornTopological

/-!
# Topology of finite unbalanced transport certificates

The property subtype carries nonnegative couplings and strictly positive
actual/target marginals.  This owner proves continuity of the transport cost
and marginal KL objective on that finite subtype.  The entropic Bregman term
is kept separate because its boundary behavior at zero coupling requires an
additional extension theorem.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Row Col : Type*}
  [Fintype Row] [Nonempty Row] [Fintype Col] [Nonempty Col]

abbrev Certificate (Row Col : Type*) [Fintype Row] [Fintype Col] :=
  UnbalancedTransportCertificate (Row := Row) (Col := Col)

theorem continuous_property_coupling :
    Continuous (fun T : Certificate Row Col => T.coupling) := by
  fun_prop

theorem continuous_property_row_mass (i : Row) :
    Continuous (fun T : Certificate Row Col => transportRowMass T.coupling i) := by
  exact (transportRowMassContinuousMap i).continuous.comp
    continuous_property_coupling

theorem continuous_property_col_mass (j : Col) :
    Continuous (fun T : Certificate Row Col => transportColMass T.coupling j) := by
  exact (transportColMassContinuousMap j).continuous.comp
    continuous_property_coupling

theorem continuous_property_row_penalty :
    Continuous (fun T : Certificate Row Col => unbalancedRowPenalty T) := by
  unfold unbalancedRowPenalty
  apply continuous_finset_sum
  intro i hi
  let mass : C(Certificate Row Col, {x : ℝ // 0 < x}) :=
    ContinuousMap.mk
      (fun T => ⟨transportRowMass T.coupling i, T.row_mass_pos i⟩) (by
        apply Continuous.subtype_mk
        exact continuous_property_row_mass i)
  let target : C(Certificate Row Col, {x : ℝ // 0 < x}) :=
    ContinuousMap.mk
      (fun T => ⟨T.targetRowMass i, T.target_row_mass_pos i⟩) (by
        apply Continuous.subtype_mk
        fun_prop)
  exact (gklTermContinuousMap.comp
    (ContinuousMap.prodMk mass target)).continuous

theorem continuous_property_col_penalty :
    Continuous (fun T : Certificate Row Col => unbalancedColPenalty T) := by
  unfold unbalancedColPenalty
  apply continuous_finset_sum
  intro j hj
  let mass : C(Certificate Row Col, {x : ℝ // 0 < x}) :=
    ContinuousMap.mk
      (fun T => ⟨transportColMass T.coupling j, T.col_mass_pos j⟩) (by
        apply Continuous.subtype_mk
        exact continuous_property_col_mass j)
  let target : C(Certificate Row Col, {x : ℝ // 0 < x}) :=
    ContinuousMap.mk
      (fun T => ⟨T.targetColMass j, T.target_col_mass_pos j⟩) (by
        apply Continuous.subtype_mk
        fun_prop)
  exact (gklTermContinuousMap.comp
    (ContinuousMap.prodMk mass target)).continuous

theorem continuous_property_transport_cost
    (cost : Row → Col → ℝ) :
    Continuous (fun T : Certificate Row Col =>
      ∑ i : Row, ∑ j : Col, T.coupling i j * cost i j) := by
  apply continuous_finset_sum
  intro i hi
  apply continuous_finset_sum
  intro j hj
  have hcoupling : Continuous
      (fun T : Certificate Row Col => T.coupling i j) := by
    exact (continuous_apply j).comp
      ((continuous_apply i).comp continuous_property_coupling)
  exact hcoupling.mul continuous_const

theorem continuous_unbalancedTransportObjective_property
    (cost : Row → Col → ℝ) (rowPenalty colPenalty : ℝ) :
    Continuous (fun T : Certificate Row Col =>
      unbalancedTransportObjective T cost rowPenalty colPenalty) := by
  unfold unbalancedTransportObjective
  have hcost := continuous_property_transport_cost cost
  have hrow : Continuous (fun T : Certificate Row Col =>
      rowPenalty * unbalancedRowPenalty T) :=
    continuous_const.mul continuous_property_row_penalty
  have hcol : Continuous (fun T : Certificate Row Col =>
      colPenalty * unbalancedColPenalty T) :=
    continuous_const.mul continuous_property_col_penalty
  exact (hcost.add hrow).add hcol

theorem unbalancedTransportObjective_property_sublevel_isClosed
    (cost : Row → Col → ℝ) (rowPenalty colPenalty c : ℝ) :
    IsClosed {T : Certificate Row Col |
      unbalancedTransportObjective T cost rowPenalty colPenalty ≤ c} := by
  change IsClosed
    ((fun T : Certificate Row Col =>
      unbalancedTransportObjective T cost rowPenalty colPenalty) ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage
    (continuous_unbalancedTransportObjective_property cost rowPenalty colPenalty)

end InfoGeometry.Inference
