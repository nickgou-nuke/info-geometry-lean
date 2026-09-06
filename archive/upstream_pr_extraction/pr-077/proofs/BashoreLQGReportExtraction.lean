import Mathlib
import proofs.BashoreSpinNetworkQubit
import proofs.NMRQuantumSpacetimeSimulator

/-!
# Bashore LQG report extraction

This file records the finite mathematical content from
Erik Bashore, *Quantum Simulations of Spin Networks From the Perspective of
Loop Quantum Gravity* (Uppsala University, 2024).

Extracted finite core:
* `SU(2)` as special unitary `2 × 2` matrices with `|a|² + |b|² = 1`;
* the four-valent `j = 1/2` intertwiner qubit has dimension `2`;
* the chosen computational support for the intertwiner basis has length `6`;
* the minimal NMR tetrahedron model uses `4` qubits and `2` invariant-tensor
  states, with `5` tetrahedra and `10` pairwise links;
* the report's symmetric `|0_I⟩` and raw `|1_I⟩` coefficient functions have
  norms `1` and `3`, and are orthogonal.
-/

noncomputable section

namespace BashoreLQGReportExtraction

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Real coordinates for the standard `SU(2)` chart `a=x+iy`, `b=z+iw`. -/
structure SU2Chart where
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ

/-- The quadratic `S^3` constraint appearing in the report. -/
def su2SphereConstraint (p : SU2Chart) : Prop :=
  p.x^2 + p.y^2 + p.z^2 + p.w^2 = 1

/-- The `SU(2)` matrix in the standard `a,b` parametrization. -/
def su2Matrix (p : SU2Chart) : M2C :=
  !![(p.x : ℂ) + (p.y : ℂ) * Complex.I,
     -((p.z : ℂ) - (p.w : ℂ) * Complex.I);
     (p.z : ℂ) + (p.w : ℂ) * Complex.I,
     (p.x : ℂ) - (p.y : ℂ) * Complex.I]

/-- The report's standard `SU(2)` chart formula. -/
@[simp] theorem su2Matrix_formula (p : SU2Chart) :
    su2Matrix p =
      !![(p.x : ℂ) + (p.y : ℂ) * Complex.I,
        -((p.z : ℂ) - (p.w : ℂ) * Complex.I);
        (p.z : ℂ) + (p.w : ℂ) * Complex.I,
        (p.x : ℂ) - (p.y : ℂ) * Complex.I] := by
  rfl

/-- The doubled-spin convention used in the report: `2j` is stored as a natural
number, so the dimension is `2j + 1 = j2 + 1`. -/
def spinRepDimension (j2 : ℕ) : ℕ := j2 + 1

@[simp] theorem spinRepDimension_half : spinRepDimension 1 = 2 := rfl

/-- The paper's `j=1/2` intertwiner qubit has dimension `2`. -/
theorem intertwiner_qubit_dimension : BashoreSpinNetworkQubit.intertwinerQubitDimension = 2 := by
  simp [BashoreSpinNetworkQubit.intertwinerQubitDimension]

/-- The basis support of the report's intertwiner qubit has length `6`. -/
theorem intertwiner_support_length : BashoreSpinNetworkQubit.intertwinerSupport.length = 6 := by
  simp [BashoreSpinNetworkQubit.intertwinerSupport]

/-- The four-valent NMR tetrahedron uses four qubits and a two-dimensional
invariant tensor space. -/
theorem nmr_tetrahedron_qubit_count :
    NMRQuantumSpacetimeSimulator.qubitsPerQuantumTetrahedron = 4 := by
  exact NMRQuantumSpacetimeSimulator.qubits_per_quantum_tetrahedron

theorem nmr_spin_half_hilbert_dimension :
    NMRQuantumSpacetimeSimulator.spinHalfHilbertDimension = 2 := by
  exact NMRQuantumSpacetimeSimulator.spin_half_hilbert_dimension

theorem nmr_invariant_tensor_space_dimension :
    NMRQuantumSpacetimeSimulator.invariantTensorSpaceDimension = 2 := by
  exact NMRQuantumSpacetimeSimulator.invariant_tensor_space_dimension

theorem nmr_spinfoam_vertex_tetrahedra_count :
    NMRQuantumSpacetimeSimulator.tetrahedraPerSpinfoamVertex = 5 := by
  exact NMRQuantumSpacetimeSimulator.tetrahedra_per_spinfoam_vertex

theorem nmr_five_tetrahedra_bell_link_count :
    NMRQuantumSpacetimeSimulator.bellLinksPerFiveTetrahedra = 10 := by
  exact NMRQuantumSpacetimeSimulator.bell_links_per_five_tetrahedra

/-- The `|0_I⟩` rational coefficient function from the report. -/
def coeffZeroI : ℕ → ℚ
  | 5 => 1 / 2
  | 6 => -1 / 2
  | 9 => -1 / 2
  | 10 => 1 / 2
  | _ => 0

/-- Raw `|1_I⟩` coefficient function before the `1/√3` normalization. -/
def coeffOneIRaw : ℕ → ℚ
  | 3 => 1
  | 12 => 1
  | 5 => -1 / 2
  | 6 => -1 / 2
  | 9 => -1 / 2
  | 10 => -1 / 2
  | _ => 0

/-- Dot product on the six support points. -/
def supportDot (a b : ℕ → ℚ) : ℚ :=
  a 3 * b 3 + a 5 * b 5 + a 6 * b 6 + a 9 * b 9 + a 10 * b 10 + a 12 * b 12

/-- The `|0_I⟩` coefficient function has squared norm `1`. -/
theorem coeffZeroI_norm :
    supportDot coeffZeroI coeffZeroI = 1 := by
  norm_num [supportDot, coeffZeroI]

/-- The raw `|1_I⟩` coefficient function has squared norm `3`. -/
theorem coeffOneIRaw_norm :
    supportDot coeffOneIRaw coeffOneIRaw = 3 := by
  norm_num [supportDot, coeffOneIRaw]

/-- The `|0_I⟩` and raw `|1_I⟩` coefficient functions are orthogonal. -/
theorem coeffZeroI_coeffOneIRaw_orthogonal :
    supportDot coeffZeroI coeffOneIRaw = 0 := by
  norm_num [supportDot, coeffZeroI, coeffOneIRaw]

/-- Regge deficit angle in the paper's notation. -/
def deficitAngle (angles : List ℝ) : ℝ :=
  2 * Real.pi - angles.sum

/-- Product of the two entries of a real pair. -/
def pairProduct (p : ℝ × ℝ) : ℝ :=
  p.1 * p.2

/-- Regge action as the finite sum of paired area and deficit-angle products. -/
def reggeAction (areas deficits : List ℝ) : ℝ :=
  (List.zip areas deficits).map pairProduct |>.sum

/-- Finite BF/Holst list functional: pair each bivector weight with its
curvature weight and sum the resulting products. -/
def holstBFAction (bivectors curvatures : List ℝ) : ℝ :=
  (List.zip bivectors curvatures).map pairProduct |>.sum

/-- A one-face finite BF/Holst list evaluates to the single paired product. -/
theorem holstBFAction_single (b f : ℝ) :
    holstBFAction [b] [f] = b * f := by
  simp [holstBFAction, pairProduct]

/-- The Yγ matching condition from the report. -/
def yGammaMatch (γ p k j : ℝ) : Prop :=
  p = γ * k ∧ k = j

/-- Finite transition-amplitude product over supplied holonomy weights. -/
def spinFoamAmplitude (holonomies : List ℂ) : ℂ :=
  holonomies.prod

/-- The two-term finite amplitude product is ordinary multiplication. -/
theorem spinFoamAmplitude_pair (z w : ℂ) :
    spinFoamAmplitude [z, w] = z * w := by
  simp [spinFoamAmplitude]

end BashoreLQGReportExtraction

end noncomputable section
