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
def UnbalancedTransportCertificate : Type _ :=
  {p : (Row → Col → ℝ) × (Row → ℝ) × (Col → ℝ) //
    (∀ i j, 0 ≤ p.1 i j) ∧
    (∀ i, 0 < transportRowMass p.1 i) ∧
    (∀ j, 0 < transportColMass p.1 j) ∧
    (∀ i, 0 < p.2.1 i) ∧
    (∀ j, 0 < p.2.2 j)}

namespace UnbalancedTransportCertificate

/-- Native tuple projection for the coupling. -/
abbrev coupling
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    Row → Col → ℝ :=
  T.1.1

/-- Native tuple projection for the target row mass. -/
abbrev targetRowMass
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    Row → ℝ :=
  T.1.2.1

/-- Native tuple projection for the target column mass. -/
abbrev targetColMass
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    Col → ℝ :=
  T.1.2.2

/-- Native subtype proof of coupling nonnegativity. -/
theorem coupling_nonneg
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    ∀ i j, 0 ≤ T.coupling i j :=
  T.2.1

/-- Native subtype proof of positive row masses. -/
theorem row_mass_pos
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    ∀ i, 0 < transportRowMass T.coupling i :=
  T.2.2.1

/-- Native subtype proof of positive column masses. -/
theorem col_mass_pos
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    ∀ j, 0 < transportColMass T.coupling j :=
  T.2.2.2.1

/-- Native subtype proof of positive target row masses. -/
theorem target_row_mass_pos
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    ∀ i, 0 < T.targetRowMass i :=
  T.2.2.2.2.1

/-- Native subtype proof of positive target column masses. -/
theorem target_col_mass_pos
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    ∀ j, 0 < T.targetColMass j :=
  T.2.2.2.2.2

end UnbalancedTransportCertificate

noncomputable def unbalancedRowPenalty
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) : ℝ :=
  ∑ i : Row,
    PositiveMeasure.gklTerm (transportRowMass T.coupling i) (T.targetRowMass i)

noncomputable def unbalancedColPenalty
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) : ℝ :=
  ∑ j : Col,
    PositiveMeasure.gklTerm (transportColMass T.coupling j) (T.targetColMass j)

theorem unbalancedRowPenalty_nonneg
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col)) :
    0 ≤ unbalancedRowPenalty T := by
  unfold unbalancedRowPenalty
  refine Finset.sum_nonneg ?_
  intro i hi
  exact PositiveMeasure.gklTerm_nonneg _ _
    (T.row_mass_pos i) (T.target_row_mass_pos i)

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

/-- Entropic Poisson-Bregman regularizer relative to a positive reference plan. -/
noncomputable def entropicTransportPenalty
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (reference : Row → Col → ℝ) : ℝ :=
  ∑ i : Row, ∑ j : Col,
    poissonBregman (T.coupling i j) (reference i j)

theorem entropicTransportPenalty_nonneg
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (reference : Row → Col → ℝ)
    (href : ∀ i j, 0 < reference i j) :
    0 ≤ entropicTransportPenalty T reference := by
  unfold entropicTransportPenalty
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro j hj
  exact poissonBregman_nonneg (T.coupling_nonneg i j) (href i j)

/-- Full relaxed Sinkhorn objective, including the entropic regularizer. -/
noncomputable def fullUnbalancedTransportObjective
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ)
    (epsilon rowPenalty colPenalty : ℝ) : ℝ :=
  unbalancedTransportObjective T cost rowPenalty colPenalty
    + epsilon * entropicTransportPenalty T reference

theorem fullUnbalancedTransportObjective_nonneg
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ)
    (hcost : ∀ i j, 0 ≤ cost i j)
    (href : ∀ i j, 0 < reference i j)
    {epsilon rowPenalty colPenalty : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hrowPenalty : 0 ≤ rowPenalty)
    (hcolPenalty : 0 ≤ colPenalty) :
    0 ≤ fullUnbalancedTransportObjective
      T cost reference epsilon rowPenalty colPenalty := by
  unfold fullUnbalancedTransportObjective
  have hbase := unbalancedTransportObjective_nonneg
    (T := T) (cost := cost) hcost hrowPenalty hcolPenalty
  have hentropy : 0 ≤ epsilon * entropicTransportPenalty T reference :=
    mul_nonneg hepsilon (entropicTransportPenalty_nonneg T reference href)
  linarith

end InfoGeometry.Inference
