import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.InformationTorsion

set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.WeylPathHysteresis

Constructive Weyl-gauge order and path-dependence layer:

- Sinkhorn two-step as a two-sided Weyl gauge transform
- explicit update-order hysteresis witnesses
- torsion-driven path dependence of twisted inference
-/

namespace InfoGeometry.Canonical.WeylInformationGauge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.InformationTorsion

section SinkhornWeyl

variable (n : Nat)

/--
Canonical Weyl-gauge form of one Sinkhorn two-step update.
-/
private theorem sinkhornTwoStep_eq_informationWeylGauge
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colNormalize n (rowNormalize n M hrow) hcol
      = sinkhornScaledCoupling n M
          (leftWeylScale n M)
          (rightWeylScale n (rowNormalize n M hrow)) :=
  sinkhornTwoStep_eq_twoSidedGauge (n := n) M hrow hcol

/--
Gauge-fixing closure for Sinkhorn/Weyl update:
row closure holds after the left gauge step, and column closure holds after
the right gauge step.
-/
private theorem sinkhornGaugeFixing_is_marginal_closure
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    (∀ i : Fin n, rowSum n (rowNormalize n M hrow) i = 1)
      ∧ (∀ j : Fin n, colSum n (colNormalize n (rowNormalize n M hrow) hcol) j = 1)
      ∧ colNormalize n (rowNormalize n M hrow) hcol
          = sinkhornScaledCoupling n M
              (leftWeylScale n M)
              (rightWeylScale n (rowNormalize n M hrow)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact rowNormalize_has_unit_rowMarginal (n := n) M hrow
  · exact colNormalize_has_unit_colMarginal (n := n) (rowNormalize n M hrow) hcol
  · exact sinkhornTwoStep_eq_informationWeylGauge (n := n) M hrow hcol

end SinkhornWeyl

section OrderHysteresis

variable (n : Nat)

/-- Two-step update with row normalization first, then column normalization. -/
noncomputable def rowThenColUpdate
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) : Coupling n :=
  colNormalize n (rowNormalize n M hrow) hcol

/-- Two-step update with column normalization first, then row normalization. -/
noncomputable def colThenRowUpdate
    (M : Coupling n)
    (hcol : HasPositiveColSums n M)
    (hrow : HasPositiveRowSums n (colNormalize n M hcol)) : Coupling n :=
  rowNormalize n (colNormalize n M hcol) hrow

/-- Row-then-column update has zero column Lyapunov residual after the final column step. -/
theorem rowThenColUpdate_colLyapunov_eq_zero
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcol : HasPositiveColSums n (rowNormalize n M hrow)) :
    colLyapunov n (rowThenColUpdate n M hrow hcol) = 0 := by
  exact colLyapunov_colNormalize_eq_zero (n := n)
    (M := rowNormalize n M hrow) hcol

/-- Column-then-row update has zero row Lyapunov residual after the final row step. -/
theorem colThenRowUpdate_rowLyapunov_eq_zero
    (M : Coupling n)
    (hcol : HasPositiveColSums n M)
    (hrow : HasPositiveRowSums n (colNormalize n M hcol)) :
    rowLyapunov n (colThenRowUpdate n M hcol hrow) = 0 := by
  exact rowLyapunov_rowNormalize_eq_zero (n := n)
    (M := colNormalize n M hcol) hrow

/-- Explicit update-order hysteresis predicate. -/
def UpdateOrderHysteresis
    (M : Coupling n)
    (hrow : HasPositiveRowSums n M)
    (hcolRow : HasPositiveColSums n (rowNormalize n M hrow))
    (hcol : HasPositiveColSums n M)
    (hrowCol : HasPositiveRowSums n (colNormalize n M hcol)) : Prop :=
  rowThenColUpdate n M hrow hcolRow ≠ colThenRowUpdate n M hcol hrowCol

variable {n}

/-- Concrete `2 × 2` witness matrix for update-order noncommutation. -/
noncomputable def weylOrderWitnessMatrix2 : Coupling 2 :=
  fun i j =>
    match (i : Nat), (j : Nat) with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 0 => 3
    | 1, 1 => 4
    | _, _ => 0

/-- Lemma `weylOrderWitnessMatrix2_positiveRows`. -/
lemma weylOrderWitnessMatrix2_positiveRows :
    HasPositiveRowSums 2 weylOrderWitnessMatrix2 := by
  intro i
  fin_cases i <;> norm_num [rowSum, weylOrderWitnessMatrix2]

/-- Lemma `weylOrderWitnessMatrix2_positiveCols`. -/
lemma weylOrderWitnessMatrix2_positiveCols :
    HasPositiveColSums 2 weylOrderWitnessMatrix2 := by
  intro j
  fin_cases j <;> norm_num [colSum, weylOrderWitnessMatrix2]

/-- Lemma `weylOrderWitnessMatrix2_positiveCols_afterRow`. -/
lemma weylOrderWitnessMatrix2_positiveCols_afterRow :
    HasPositiveColSums 2
      (rowNormalize 2 weylOrderWitnessMatrix2 weylOrderWitnessMatrix2_positiveRows) := by
  intro j
  fin_cases j <;> norm_num [colSum, rowNormalize, rowSum, weylOrderWitnessMatrix2]

/-- Lemma `weylOrderWitnessMatrix2_positiveRows_afterCol`. -/
lemma weylOrderWitnessMatrix2_positiveRows_afterCol :
    HasPositiveRowSums 2
      (colNormalize 2 weylOrderWitnessMatrix2 weylOrderWitnessMatrix2_positiveCols) := by
  intro i
  fin_cases i <;> norm_num [rowSum, colNormalize, colSum, weylOrderWitnessMatrix2]

/--
Concrete noncommutation witness:
for the explicit `2 × 2` matrix `[[1,2],[3,4]]`, row→col and col→row
two-step updates are different.
-/
private theorem weylOrderHysteresis_on_witnessMatrix2 :
    UpdateOrderHysteresis 2
      weylOrderWitnessMatrix2
      weylOrderWitnessMatrix2_positiveRows
      weylOrderWitnessMatrix2_positiveCols_afterRow
      weylOrderWitnessMatrix2_positiveCols
      weylOrderWitnessMatrix2_positiveRows_afterCol := by
  unfold UpdateOrderHysteresis rowThenColUpdate colThenRowUpdate
  intro hEq
  have h00 := congrArg (fun A => A (0 : Fin 2) (0 : Fin 2)) hEq
  norm_num [colNormalize, rowNormalize, rowSum, colSum, weylOrderWitnessMatrix2] at h00

/--
Existence form of update-order hysteresis at `n = 2`.
-/
private theorem exists_updateOrderHysteresis_n2 :
    ∃ (M : Coupling 2)
      (hrow : HasPositiveRowSums 2 M)
      (hcolRow : HasPositiveColSums 2 (rowNormalize 2 M hrow))
      (hcol : HasPositiveColSums 2 M)
      (hrowCol : HasPositiveRowSums 2 (colNormalize 2 M hcol)),
      UpdateOrderHysteresis 2 M hrow hcolRow hcol hrowCol := by
  refine ⟨weylOrderWitnessMatrix2,
    weylOrderWitnessMatrix2_positiveRows,
    weylOrderWitnessMatrix2_positiveCols_afterRow,
    weylOrderWitnessMatrix2_positiveCols,
    weylOrderWitnessMatrix2_positiveRows_afterCol,
    weylOrderHysteresis_on_witnessMatrix2⟩

end OrderHysteresis

section TorsionPathDependence

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Path-dependence witness encoded by nonzero information torsion.
-/
def UpdateOrderPathDependent (conn : Connection E) : Prop :=
  ∃ u v : E, informationTorsion conn u v ≠ 0

/--
Any twisted inference system is path-dependent in the update-order sense.
-/
theorem twistedInference_updateOrderPathDependent
    (T : TwistedInference E) :
    UpdateOrderPathDependent T.dual.nabla := by
  classical
  unfold UpdateOrderPathDependent
  by_contra hNoWitness
  push_neg at hNoWitness
  exact T.has_torsion (by
    ext u v
    exact hNoWitness u v)

/--
Twisted inference cannot be torsion-free.
-/
private theorem twistedInference_not_torsionFree
    (T : TwistedInference E) :
    ¬ IsTorsionFree T.dual.nabla := by
  intro hFree
  exact T.has_torsion hFree

end TorsionPathDependence

end InfoGeometry.Canonical.WeylInformationGauge
