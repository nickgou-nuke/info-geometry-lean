import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RelativePotentialScalarBridge
import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Meta.Architecture
set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.OddDefectFunctional

Repo-native P3 defect functional on the owned seed-to-operator corridor:

`counts -> projective rays -> relative potential -> operator lift`.

This module intentionally avoids introducing an ad-hoc odd-sector norm as the
primary defect object. The owner defect is the normalization/partition cocycle
already present in the projective count lane (`countMassShift`), with operator
readout obtained by the existing canonical lift theorems.
-/

namespace InfoGeometry.Canonical.OddDefectFunctional

open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.RelativePotentialScalarBridge

section CountProjectiveDefect

variable {n : Nat} [Nonempty (Fin n)]

/--
Primary projective defect functional:
the scalar modular potential of the count relative-volume cocycle.
-/
@[rep_depth projective]
noncomputable def projectiveCountDefectFunctional
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) : ℝ :=
  scalarModularPotential
    (countRelativeVolumeChange counts ref hcounts href)
    (by
      unfold countRelativeVolumeChange
      exact div_pos (countMass_pos counts hcounts) (countMass_pos ref href))

/--
The primary defect functional is exactly the owned normalization cocycle.
-/
@[rep_depth projective]
theorem projectiveCountDefectFunctional_eq_countMassShift
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    projectiveCountDefectFunctional (n := n) counts ref hcounts href
      = countMassShift counts ref hcounts href := by
  symm
  exact countMassShift_eq_scalarModularPotential_relativeVolumeChange
    (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)

/-- Equivalent logarithmic form of the same primary defect. -/
@[rep_depth projective]
theorem projectiveCountDefectFunctional_eq_neg_log_relativeVolumeChange
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    projectiveCountDefectFunctional (n := n) counts ref hcounts href
      = -Real.log (countRelativeVolumeChange counts ref hcounts href) := by
  rw [projectiveCountDefectFunctional_eq_countMassShift (n := n)
    (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)]
  exact countMassShift_eq_neg_log_countRelativeVolumeChange
    (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)

/--
Barrier magnitude (nonnegative) associated to the primary signed cocycle.
-/
@[rep_depth projective]
noncomputable def projectiveCountDefectBarrier
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) : ℝ :=
  |projectiveCountDefectFunctional (n := n) counts ref hcounts href|

@[rep_depth projective]
theorem projectiveCountDefectBarrier_nonneg
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    0 ≤ projectiveCountDefectBarrier (n := n) counts ref hcounts href := by
  unfold projectiveCountDefectBarrier
  exact abs_nonneg _

end CountProjectiveDefect

section OperatorLiftDefect

variable {n : Nat} [Nonempty (Fin n)]

/--
Operator-lifted defect readout:
difference between the raw averaged modular Hamiltonian and the canonical
projective readout on count rays.
-/
@[rep_depth operator]
noncomputable def operatorLiftedCountDefectFunctional
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) : ℝ :=
  averagedModularHamiltonian n (relativeCountDensity n counts ref)
    - InfoGeometry.Canonical.RelativeModularOperator.relativeModularHamiltonianReadout
        (n := n) (countRay counts hcounts) (countRay ref href)

/--
The operator-lifted defect is exactly the same owned cocycle `countMassShift`.
-/
@[rep_depth operator]
theorem operatorLiftedCountDefectFunctional_eq_countMassShift
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    operatorLiftedCountDefectFunctional (n := n) counts ref hcounts href
      = countMassShift counts ref hcounts href := by
  unfold operatorLiftedCountDefectFunctional
  have h :=
    InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeModularHamiltonian_eq_relativeModularHamiltonianReadout_countRay_add_countMassShift
      (n := n) (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)
  linarith

/--
Compatibility theorem: projective defect and operator-lifted defect coincide.
-/
@[rep_depth operator]
theorem operatorLiftedCountDefectFunctional_eq_projectiveCountDefectFunctional
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    operatorLiftedCountDefectFunctional (n := n) counts ref hcounts href
      = projectiveCountDefectFunctional (n := n) counts ref hcounts href := by
  rw [operatorLiftedCountDefectFunctional_eq_countMassShift
    (n := n) (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)]
  symm
  exact projectiveCountDefectFunctional_eq_countMassShift
    (n := n) (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)

/--
Skew reciprocity on the operator-lift lane (Onsager/Casimir sign):
swapping source and reference flips the defect sign.
-/
@[rep_depth operator]
theorem operatorLiftedCountDefectFunctional_swap_neg
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    operatorLiftedCountDefectFunctional (n := n) ref counts href hcounts
      =
    -operatorLiftedCountDefectFunctional (n := n) counts ref hcounts href := by
  rw [operatorLiftedCountDefectFunctional_eq_countMassShift
    (n := n) (counts := ref) (ref := counts) (hcounts := href) (href := hcounts)]
  rw [operatorLiftedCountDefectFunctional_eq_countMassShift
    (n := n) (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)]
  exact countMassShift_symm (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)

/--
Additive cocycle law on the operator-lift lane:
the lifted defect composes along the projective count chain.
-/
@[rep_depth operator]
theorem operatorLiftedCountDefectFunctional_cocycle
    (counts ref base : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i)
    (hbase : ∀ i : Fin n, 0 < base i) :
    operatorLiftedCountDefectFunctional (n := n) counts base hcounts hbase
      =
    operatorLiftedCountDefectFunctional (n := n) counts ref hcounts href
      +
    operatorLiftedCountDefectFunctional (n := n) ref base href hbase := by
  rw [operatorLiftedCountDefectFunctional_eq_countMassShift
    (n := n) (counts := counts) (ref := base) (hcounts := hcounts) (href := hbase)]
  rw [operatorLiftedCountDefectFunctional_eq_countMassShift
    (n := n) (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)]
  rw [operatorLiftedCountDefectFunctional_eq_countMassShift
    (n := n) (counts := ref) (ref := base) (hcounts := href) (href := hbase)]
  exact countMassShift_cocycle
    (counts := counts) (ref := ref) (base := base)
    (hcounts := hcounts) (href := href) (hbase := hbase)

/-- Nonnegative barrier magnitude on the operator-lift lane. -/
@[rep_depth operator]
noncomputable def operatorLiftedCountDefectBarrier
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) : ℝ :=
  |operatorLiftedCountDefectFunctional (n := n) counts ref hcounts href|

@[rep_depth operator]
theorem operatorLiftedCountDefectBarrier_nonneg
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    0 ≤ operatorLiftedCountDefectBarrier (n := n) counts ref hcounts href := by
  unfold operatorLiftedCountDefectBarrier
  exact abs_nonneg _

end OperatorLiftDefect

section OnsagerLine

open InfoGeometry.Canonical.OnsagerReciprocity

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Trunk Onsager line (operator lane): the symmetric response coefficient is
reciprocal under channel swap.
-/
@[rep_depth transport]
theorem onsager_responseCoefficient_swap
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (X Y A : EndH) :
    responseCoefficient (E := E) P X Y A
      =
    responseCoefficient (E := E) P Y X A := by
  simpa using
    (InfoGeometry.Canonical.OnsagerReciprocity.responseCoefficient_swap
      (E := E) P X Y A)

end OnsagerLine

end InfoGeometry.Canonical.OddDefectFunctional
