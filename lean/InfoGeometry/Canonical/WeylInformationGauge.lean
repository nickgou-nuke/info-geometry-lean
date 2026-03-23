import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Canonical.InformationTorsion
import InfoGeometry.Canonical.RicciMongeAmpere
set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.WeylInformationGauge

Constructive Weyl-gauge layer for information geometry:

- Sinkhorn two-step as two-sided Weyl gauge transform
- gauge-fixing closure as staged marginal closure
- path-dependence witness as nonzero information torsion
- dilation/chiral anomaly sourcing of transported Einstein residual
-/

namespace InfoGeometry.Canonical.WeylInformationGauge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.ConformalAlgebra
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.InformationTorsion
open InfoGeometry.Canonical.RicciMongeAmpere

section SinkhornWeyl

variable (n : Nat)

/--
Canonical Weyl-gauge form of one Sinkhorn two-step update.
-/
theorem sinkhornTwoStep_eq_informationWeylGauge
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
theorem sinkhornGaugeFixing_is_marginal_closure
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
theorem weylOrderHysteresis_on_witnessMatrix2 :
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
theorem exists_updateOrderHysteresis_n2 :
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
theorem twistedInference_not_torsionFree
    (T : TwistedInference E) :
    ¬ IsTorsionFree T.dual.nabla := by
  intro hFree
  exact T.has_torsion hFree

end TorsionPathDependence

section DilationSource

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Nonzero chiral-anomaly operator implies positive chiral scale (`IsChiralInference`).
-/
theorem chiralInferenceState_of_nonzero_anomaly
    (CI : ConformalInference E)
    (hAnom : CI.chiralAnomalyOperator ≠ 0) :
    CI.ChiralInferenceState := by
  have hAnom' : CI.chiralAnomaly ≠ 0 := by
    simpa [ConformalInference.chiralAnomalyOperator] using hAnom
  unfold ConformalInference.ChiralInferenceState ConformalInference.IsChiralInference
    ConformalInference.chiralScale ConformalInference.epsilon
  exact (NNReal.coe_pos).2 ((nnnorm_pos).2 hAnom')

/--
Dilation/anomaly sourcing statement:
if the induced chemical potential equals the chiral scale and the conformal
state is chiral, then the transported Einstein residual is nonzero.
-/
theorem dilationAnomaly_sources_transportedEinsteinResidual
    (CI : ConformalInference E)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CI.chiralScale)
    (hChiral : CI.ChiralInferenceState) :
    transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  have hμ_ne :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
    rw [hSource]
    exact ne_of_gt hChiral
  exact hμ_ne

/--
Strong sourcing form:
nonzero anomaly plus source relation forces nonzero transported Einstein residual.
-/
theorem nonzeroAnomaly_sources_transportedEinsteinResidual
    (CI : ConformalInference E)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CI.chiralScale)
    (hAnom : CI.chiralAnomalyOperator ≠ 0) :
    transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  exact dilationAnomaly_sources_transportedEinsteinResidual
    (CI := CI) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) hSource
    (chiralInferenceState_of_nonzero_anomaly (CI := CI) hAnom)

end DilationSource

section CartanWeylClosure

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Cartan generator split specialized to Weyl-gauge interpretation:
`M` is volume-preserving and `D` is Weyl-dilation.
-/
private theorem cartanWeyl_generator_split
    (CBA : ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition) :
    CBA.IsVolumePreservingPart CBA.M ∧ CBA.IsWeylDilationPart CBA.D := by
  exact CBA.cartan_generator_split hCartan

/--
Cartan/Weyl closure theorem:
if the conformal generators satisfy the Cartan split and the transported Einstein
residual is sourced by the chiral scale, then any nonzero anomaly forces a
nonzero transported Einstein residual.
-/
theorem cartanWeyl_dilation_sources_transportedEinsteinResidual
    (CBA : ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale)
    (hAnom : CBA.CI.chiralAnomalyOperator ≠ 0) :
    CBA.IsVolumePreservingPart CBA.M
      ∧ CBA.IsWeylDilationPart CBA.D
      ∧ transportedEinsteinResidual (R := R) (K := K) (x := x)
          (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  refine ⟨(CBA.M_in_volumePreserving_of_cartan hCartan),
    (CBA.D_in_weylDilation_of_cartan hCartan), ?_⟩
  exact nonzeroAnomaly_sources_transportedEinsteinResidual
    (CI := CBA.CI) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) hSource hAnom

/--
Cartan/Weyl closure in primitive form (no bundled split witness):
given explicit compact/non-compact sector hypotheses for `(M,D)`, nonzero
anomaly still forces nonzero transported Einstein residual under the same
source relation.
-/
private theorem cartanWeyl_dilation_sources_transportedEinsteinResidual_of_parts
    (CBA : ConformalBeliefAlgebra E)
    (hM : CBA.IsVolumePreservingPart CBA.M)
    (hD : CBA.IsWeylDilationPart CBA.D)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale)
    (hAnom : CBA.CI.chiralAnomalyOperator ≠ 0) :
    CBA.IsVolumePreservingPart CBA.M
      ∧ CBA.IsWeylDilationPart CBA.D
      ∧ transportedEinsteinResidual (R := R) (K := K) (x := x)
          (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  refine ⟨hM, hD, ?_⟩
  exact nonzeroAnomaly_sources_transportedEinsteinResidual
    (CI := CBA.CI) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) hSource hAnom

end CartanWeylClosure

end InfoGeometry.Canonical.WeylInformationGauge
