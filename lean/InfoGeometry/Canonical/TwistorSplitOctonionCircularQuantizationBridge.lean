import InfoGeometry.Twistor.SplitClifford55PureSpinorOrbitGeometry
import InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Pure-spinor to circular split-octonion operator bridge

This owner closes the verified finite bridge between the twistor vacuum
readout and the circular Peirce operators.  Creation and annihilation here
mean the two square-zero circular *elements* and their left-multiplication
operator readouts.  No associativity claim, Fock representation theorem, or
quantization functor is inferred for the non-associative Zorn product.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwistorSplitOctonionCircularQuantizationBridge

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
open InfoGeometry.Clifford.SplitClifford55ZornCARComparison
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Clifford.SplitClifford55PureSpinorGrassmannianBridge
open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Twistor.SplitClifford55PureSpinorOrbitGeometry

abbrev CZ := CanonicalZorn
abbrev Coord := Fin 8 → ℝ

/-- The positive circular root elements, read in the native Zorn carrier. -/
def circularCreationElement (i : Fin 3) : CZ :=
  circularPeirceBasis ⟨i.1 + 1, by omega⟩

/-- The negative circular root elements, read in the native Zorn carrier. -/
def circularAnnihilationElement (i : Fin 3) : CZ :=
  circularPeirceBasis ⟨i.1 + 5, by omega⟩

/-- Left multiplication by the positive circular root element, transported to
the circular coordinate carrier. -/
def circularCreationOperator (i : Fin 3) : Module.End ℝ Coord :=
  circularL (circularCreationElement i)

/-- Left multiplication by the negative circular root element, transported to
the circular coordinate carrier. -/
def circularAnnihilationOperator (i : Fin 3) : Module.End ℝ Coord :=
  circularL (circularAnnihilationElement i)

@[simp] theorem circularCreationElement_eq_rootPlus (i : Fin 3) :
    circularCreationElement i =
      cartesianZornLinearEquiv (rootPlus i) := by
  rw [circularCreationElement, circularPeirceBasis_apply]
  have hframe : circularFrame ⟨i.1 + 1, by omega⟩ = rootPlus i := by
    fin_cases i <;> rfl
  rw [hframe]

@[simp] theorem circularAnnihilationElement_eq_rootMinus (i : Fin 3) :
    circularAnnihilationElement i =
      cartesianZornLinearEquiv (rootMinus i) := by
  rw [circularAnnihilationElement, circularPeirceBasis_apply]
  have hframe : circularFrame ⟨i.1 + 5, by omega⟩ = rootMinus i := by
    fin_cases i <;> rfl
  rw [hframe]

/-- Positive circular root elements are square-zero in the native Zorn
product. -/
theorem circularCreationElement_sq (i : Fin 3) :
    circularCreationElement i * circularCreationElement i = 0 := by
  rw [circularCreationElement_eq_rootPlus]
  exact cartesianZorn_rootPlus_sq i

/-- Negative circular root elements are square-zero in the native Zorn
product. -/
theorem circularAnnihilationElement_sq (i : Fin 3) :
    circularAnnihilationElement i * circularAnnihilationElement i = 0 := by
  rw [circularAnnihilationElement_eq_rootMinus]
  exact cartesianZorn_rootMinus_sq i

/-- The operator readout acts by native left multiplication on every circular
basis vector. -/
theorem circularCreationOperator_on_basis (i : Fin 3) (j : Fin 8) :
    circularCreationOperator i (circularCoordinateLinearEquiv
        (circularPeirceBasis j)) =
      circularCoordinateLinearEquiv
        (circularCreationElement i * circularPeirceBasis j) := by
  exact circularL_on_basis (circularCreationElement i) j

theorem circularAnnihilationOperator_on_basis (i : Fin 3) (j : Fin 8) :
    circularAnnihilationOperator i (circularCoordinateLinearEquiv
        (circularPeirceBasis j)) =
      circularCoordinateLinearEquiv
        (circularAnnihilationElement i * circularPeirceBasis j) := by
  exact circularL_on_basis (circularAnnihilationElement i) j

/-- The two circular operators are genuine linear readouts of the two
square-zero native channels; this theorem does not reassociate their
composition in the non-associative carrier. -/
theorem circular_creation_annihilation_readout (i : Fin 3) :
    circularCreationOperator i = circularL (circularCreationElement i) ∧
      circularAnnihilationOperator i = circularL (circularAnnihilationElement i) ∧
      circularCreationElement i * circularCreationElement i = 0 ∧
      circularAnnihilationElement i * circularAnnihilationElement i = 0 := by
  exact ⟨rfl, rfl, circularCreationElement_sq i,
    circularAnnihilationElement_sq i⟩

/-- The canonical twistor vacuum and its maximal-neutral annihilator are the
same readout used by the split-Clifford orbit lane. -/
theorem vacuum_twistor_circular_readout :
    maximalNeutralReadout vacuumProjectivePureSpinorPoint =
      ⟨neutralAnnihilator (1 : Spinor),
        vacuum_neutralAnnihilator_isMaximalNeutralTotallyNull⟩ := by
  exact vacuum_maximalNeutralReadout

/-- The first three dual channels are certified members of the vacuum
annihilator, providing the twistor-side annihilation interface. -/
theorem vacuum_annihilator_circular_channels (i : Fin 3) :
    (0, dualBasisVector (firstThreeIndex i)) ∈
      neutralAnnihilator (1 : Spinor) := by
  exact firstThree_dual_channels_mem_vacuum_annihilator i

end InfoGeometry.Canonical.TwistorSplitOctonionCircularQuantizationBridge
