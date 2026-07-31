/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.PoissonSinkhornTCSBridge
import InfoGeometry.PositiveMeasure

/-!
# Finite unbalanced Poisson transport contract

This module formalizes the relaxed-marginal semantics used by the Python
unbalanced Sinkhorn solver.  It certifies the finite objective but does not
claim convergence of an iterative update.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Row Col : Type*}
  [Fintype Row] [Nonempty Row] [Fintype Col] [Nonempty Col]

noncomputable def transportRowMass
    (coupling : Row → Col → ℝ) (i : Row) : ℝ :=
  ∑ j : Col, coupling i j

noncomputable def transportColMass
    (coupling : Row → Col → ℝ) (j : Col) : ℝ :=
  ∑ i : Row, coupling i j

/-- A finite coupling with strictly positive actual and target marginals. -/
structure UnbalancedTransportCertificate where
  coupling : Row → Col → ℝ
  targetRowMass : Row → ℝ
  targetColMass : Col → ℝ
  coupling_nonneg : ∀ i j, 0 ≤ coupling i j
  row_mass_pos : ∀ i, 0 < transportRowMass coupling i
  col_mass_pos : ∀ j, 0 < transportColMass coupling j
  target_row_mass_pos : ∀ i, 0 < targetRowMass i
  target_col_mass_pos : ∀ j, 0 < targetColMass j

noncomputable def unbalancedRowPenalty
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) : ℝ :=
  ∑ i : Row,
    PositiveMeasure.gklTerm (transportRowMass T.coupling i) (T.targetRowMass i)

noncomputable def unbalancedColPenalty
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) : ℝ :=
  ∑ j : Col,
    PositiveMeasure.gklTerm (transportColMass T.coupling j) (T.targetColMass j)

omit [Nonempty Row] [Nonempty Col] in
theorem unbalancedRowPenalty_nonneg
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    0 ≤ unbalancedRowPenalty T := by
  unfold unbalancedRowPenalty
  refine Finset.sum_nonneg ?_
  intro i hi
  exact PositiveMeasure.gklTerm_nonneg _ _
    (T.row_mass_pos i) (T.target_row_mass_pos i)

omit [Nonempty Row] [Nonempty Col] in
theorem unbalancedColPenalty_nonneg
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    0 ≤ unbalancedColPenalty T := by
  unfold unbalancedColPenalty
  refine Finset.sum_nonneg ?_
  intro j hj
  exact PositiveMeasure.gklTerm_nonneg _ _
    (T.col_mass_pos j) (T.target_col_mass_pos j)

/-- Transport cost plus KL penalties for relaxed row and column marginals. -/
noncomputable def unbalancedTransportObjective
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost : Row → Col → ℝ)
    (rowPenalty colPenalty : ℝ) : ℝ :=
  (∑ i : Row, ∑ j : Col, T.coupling i j * cost i j)
    + rowPenalty * unbalancedRowPenalty T
    + colPenalty * unbalancedColPenalty T

theorem unbalancedTransportObjective_nonneg
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost : Row → Col → ℝ)
    (hcost : ∀ i j, 0 ≤ cost i j)
    {rowPenalty colPenalty : ℝ}
    (hrowPenalty : 0 ≤ rowPenalty)
    (hcolPenalty : 0 ≤ colPenalty) :
    0 ≤ unbalancedTransportObjective T cost rowPenalty colPenalty := by
  unfold unbalancedTransportObjective
  have htransport :
      0 ≤ ∑ i : Row, ∑ j : Col, T.coupling i j * cost i j := by
    refine Finset.sum_nonneg ?_
    intro i hi
    refine Finset.sum_nonneg ?_
    intro j hj
    exact mul_nonneg (T.coupling_nonneg i j) (hcost i j)
  have hrow : 0 ≤ rowPenalty * unbalancedRowPenalty T :=
    mul_nonneg hrowPenalty (unbalancedRowPenalty_nonneg T)
  have hcol : 0 ≤ colPenalty * unbalancedColPenalty T :=
    mul_nonneg hcolPenalty (unbalancedColPenalty_nonneg T)
  linarith

end InfoGeometry.Inference
