import Mathlib
import proofs.CuntzKriegerPrimon
import InfoGeometry.Canonical.ChiralCausalCone

/-!
# Hameroff 1998 Orch OR / microtubule arithmetic

Theorem-honest digest of Stuart Hameroff,
"Quantum Computation in Brain Microtubules? The Penrose--Hameroff 'Orch OR'
Model of Consciousness", Phil. Trans. R. Soc. Lond. A 356 (1998), 1869--1896.

The formalization records only the explicit finite arithmetic and algebraic
forms appearing in the paper: the Penrose OR relation `E = h/T`, tubulin-count
scaling examples, microtubule lattice constants, Fibonacci helical periods,
six-neighbour lattice coupling, and the table-style figure of merit
`M = T_decohere / t_elem`.
-/

noncomputable section

namespace HameroffOrchORMicrotubule

/-! ## 1. Microtubule lattice constants -/

/-- Microtubule diameter quoted in the paper, in nanometres. -/
def microtubuleDiameterNm : ℕ := 25

/-- Number of tubulin protofilament columns in the cited microtubule lattice. -/
def protofilamentColumns : ℕ := 13

/-- Local asymmetric neighbours used in the cited automaton simulation. -/
def latticeNeighbourCount : ℕ := 6

/-- Automaton frame step shown in the paper's microtubule simulation, in ns. -/
def automatonStepNs : ℕ := 8

/-- Approximate Bjerrum length mentioned for the shielding charge phase, in tenths of nm. -/
def bjerrumLengthTenthsNm : ℕ := 7

@[simp] theorem microtubule_diameter_nm :
    microtubuleDiameterNm = 25 := rfl

@[simp] theorem protofilament_columns :
    protofilamentColumns = 13 := rfl

@[simp] theorem lattice_neighbour_count :
    latticeNeighbourCount = 6 := rfl

@[simp] theorem automaton_step_ns :
    automatonStepNs = 8 := rfl

@[simp] theorem bjerrum_length_tenths_nm :
    bjerrumLengthTenthsNm = 7 := rfl

/-! ## 2. OR energy/time relation and tubulin-count scaling -/

/-- Penrose OR energy-time relation as used in the paper: `E = h/T`. -/
def objectiveReductionEnergy (h T : ℝ) : ℝ := h / T

theorem objectiveReductionEnergy_eq (h T : ℝ) :
    objectiveReductionEnergy h T = h / T := rfl

/-- Tubulin-count scaling constant in tubulin·ms from the paper's examples:
`2×10¹⁰·25 = 5×10¹¹`. -/
def tubulinMillisecondConstant : ℕ := 500000000000

/-- Tubulin count predicted by the paper's inverse time scaling, with time in ms. -/
def predictedTubulinsForMs (Tms : ℕ) : ℕ :=
  tubulinMillisecondConstant / Tms

@[simp] theorem predicted_tubulins_25ms :
    predictedTubulinsForMs 25 = 20000000000 := by
  norm_num [predictedTubulinsForMs, tubulinMillisecondConstant]

@[simp] theorem predicted_tubulins_100ms :
    predictedTubulinsForMs 100 = 5000000000 := by
  norm_num [predictedTubulinsForMs, tubulinMillisecondConstant]

@[simp] theorem predicted_tubulins_500ms :
    predictedTubulinsForMs 500 = 1000000000 := by
  norm_num [predictedTubulinsForMs, tubulinMillisecondConstant]

/-- Estimated tubulins per neuron reported in the paper. -/
def tubulinsPerNeuron : ℕ := 10000000

/-- Ten percent coherent fraction used in the paper's neuron-count examples. -/
def coherentFractionDenominator : ℕ := 10

/-- Coherent tubulins per neuron under the paper's ten-percent example. -/
def coherentTubulinsPerNeuron : ℕ :=
  tubulinsPerNeuron / coherentFractionDenominator

/-- Number of neurons required at a given time scale under the ten-percent example. -/
def neuronsRequiredForMs (Tms : ℕ) : ℕ :=
  predictedTubulinsForMs Tms / coherentTubulinsPerNeuron

@[simp] theorem coherent_tubulins_per_neuron :
    coherentTubulinsPerNeuron = 1000000 := by
  norm_num [coherentTubulinsPerNeuron, tubulinsPerNeuron, coherentFractionDenominator]

@[simp] theorem neurons_required_25ms :
    neuronsRequiredForMs 25 = 20000 := by
  norm_num [neuronsRequiredForMs, predictedTubulinsForMs,
    coherentTubulinsPerNeuron, tubulinsPerNeuron, coherentFractionDenominator,
    tubulinMillisecondConstant]

@[simp] theorem neurons_required_100ms :
    neuronsRequiredForMs 100 = 5000 := by
  norm_num [neuronsRequiredForMs, predictedTubulinsForMs,
    coherentTubulinsPerNeuron, tubulinsPerNeuron, coherentFractionDenominator,
    tubulinMillisecondConstant]

@[simp] theorem neurons_required_500ms :
    neuronsRequiredForMs 500 = 1000 := by
  norm_num [neuronsRequiredForMs, predictedTubulinsForMs,
    coherentTubulinsPerNeuron, tubulinsPerNeuron, coherentFractionDenominator,
    tubulinMillisecondConstant]

/-! ## 3. Fibonacci helical pathways and figure of merit -/

/-- Fibonacci helical row periodicities quoted for microtubule pathways. -/
def helicalFibonacciPeriods : List ℕ := [3, 5, 8, 13]

@[simp] theorem helical_fibonacci_periods_length :
    helicalFibonacciPeriods.length = 4 := rfl

theorem helical_fibonacci_periods_recur :
    3 + 5 = 8 ∧ 5 + 8 = 13 := by
  norm_num

/-- Quantum-computing figure of merit `M = T_decohere / t_elem`. -/
def figureOfMerit (tElem Tdecohere : ℚ) : ℚ :=
  Tdecohere / tElem

/-- Paper table value for microtubule tubulins: `10^-1 / 10^-9 = 10^8`. -/
theorem microtubule_figure_of_merit :
    figureOfMerit (1 / 1000000000) (1 / 10) = 100000000 := by
  norm_num [figureOfMerit]

/-! ## 4. Six-neighbour dipole lattice skeleton -/

/-- A six-neighbour microtubule neighbourhood index. -/
abbrev NeighbourIndex := Fin latticeNeighbourCount

/-- Coulomb-like dipole coupling skeleton from the automaton description:
prefactor times a six-neighbour weighted inverse-distance sum. -/
def sixNeighbourCoupling
    (prefactor : ℝ) (weight invDistance : NeighbourIndex → ℝ) : ℝ :=
  prefactor * ∑ i : NeighbourIndex, weight i * invDistance i

theorem sixNeighbourCoupling_zero_prefactor
    (weight invDistance : NeighbourIndex → ℝ) :
    sixNeighbourCoupling 0 weight invDistance = 0 := by
  simp [sixNeighbourCoupling]

/-- If all six neighbour contributions are zero, the coupling is zero. -/
theorem sixNeighbourCoupling_zero_weights
    (prefactor : ℝ) (weight invDistance : NeighbourIndex → ℝ)
    (h : ∀ i, weight i * invDistance i = 0) :
    sixNeighbourCoupling prefactor weight invDistance = 0 := by
  simp [sixNeighbourCoupling, h]

end HameroffOrchORMicrotubule
