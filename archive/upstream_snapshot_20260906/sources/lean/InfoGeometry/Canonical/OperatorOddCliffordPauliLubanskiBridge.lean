import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge
import InfoGeometry.Canonical.OperatorPauliLubanskiLift

/-!
# Operator odd-Clifford / Pauli--Lubanski bridge

This file composes two existing finite owners:

* the odd Clifford square on the native Dirac matrix carrier;
* the concrete spin-half Pauli--Lubanski readout and its operator-Zorn transport.

The common four-vector map is explicit.  No identification of the Dirac,
Zorn, and Pauli carriers is asserted: the bridge records equal scalar
quadratic readouts and keeps the operator equalities in their native carriers.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorOddCliffordPauliLubanskiBridge

open InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge
open InfoGeometry.Canonical.OperatorPauliLubanskiLift

/-- The common Fin 4 complex coordinate readout of a Pauli momentum. -/
def pauliMomentumVector (P : PauliMomentum) : ComplexFourVector :=
  ![P.E, P.px, P.py, P.pz]

@[simp] theorem pauliMomentumVector_zero :
    pauliMomentumVector
      ({ E := 0, px := 0, py := 0, pz := 0 } : PauliMomentum) = 0 := by
  funext i
  fin_cases i <;> rfl

/-- The two finite owners use the same mostly-minus quadratic readout. -/
theorem massCasimir_eq_minkowskiQuadratic (P : PauliMomentum) :
    massCasimir P = minkowskiQuadratic (pauliMomentumVector P) := by
  simp [massCasimir, pauliMomentumVector, minkowskiQuadratic]

/-- The pure odd Clifford lift of a Pauli momentum. -/
def oddPauliPotential (P : PauliMomentum) : DiracMatrix :=
  oddPotential (pauliMomentumVector P) 0

/-- The odd Clifford square is the Pauli momentum quadratic readout. -/
theorem oddPauliPotential_sq (P : PauliMomentum) :
    oddPauliPotential P * oddPauliPotential P =
      massCasimir P • (1 : DiracMatrix) := by
  unfold oddPauliPotential
  rw [pureVector_square_is_scalar]
  rw [massCasimir_eq_minkowskiQuadratic]

/-- The odd square is even in the existing Clifford grading. -/
theorem oddPauliPotential_sq_isCliffordEven (P : PauliMomentum) :
    IsCliffordEven (oddPauliPotential P * oddPauliPotential P) := by
  exact oddPotential_sq_isCliffordEven
    (pauliMomentumVector P) 0

/-- Finite bridge packet: the odd Clifford quadratic readout and the
Pauli--Lubanski second Casimir share the same mass scalar, while all
operator equalities remain in their native carriers. -/
theorem odd_clifford_pauliLubanski_packet (P : PauliMomentum) :
    oddPauliPotential P * oddPauliPotential P =
        massCasimir P • (1 : DiracMatrix) ∧
      momentumPauliLubanskiContraction P = 0 ∧
      pauliLubanskiSq P = -(massCasimir P) • spinHalfCasimir ∧
      zornPauliLubanskiSq P =
        -(massCasimir P) • zornSpinHalfCasimir := by
  refine ⟨oddPauliPotential_sq P, ?_⟩
  exact ⟨pauliLubanski_momentum_orthogonal P,
    pauliLubanski_sq_eq_mass_spin_casimir P,
    zornPauliLubanski_sq_eq_mass_spin P⟩

/-- Null common quadratic readout gives both finite null consequences. -/
theorem null_readout_packet (P : PauliMomentum)
    (hP : massCasimir P = 0) :
    oddPauliPotential P * oddPauliPotential P = 0 ∧
      pauliLubanskiSq P = 0 ∧
      zornPauliLubanskiSq P = 0 := by
  refine ⟨?_, pauliLubanski_null_limit P hP, ?_⟩
  · rw [oddPauliPotential_sq P, hP, zero_smul]
  · rw [zornPauliLubanski_sq_eq_mass_spin P, hP, zero_smul]

end InfoGeometry.Canonical.OperatorOddCliffordPauliLubanskiBridge
