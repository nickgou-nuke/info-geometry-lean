import InfoGeometry.Canonical.DiscreteCPTGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitQ11PhaseFlip
import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.Clifford.SplitQ11Equivariance

/-!
# Real `Cl(1,1)` CPT Emergence Seed

This file starts the CPT emergence package from the real split Clifford atom.
It connects the finite C/P/T bookkeeping bit `P` to the verified real
`Cl(1,1)` phase-flip automorphism.

#### BUCKET 1: CLOSED FINITE THEOREMS
The real split `Cl(1,1)` phase flip fixes the positive generator, negates the
negative generator, negates the pseudoscalar, swaps the two null generators, and
has order two on these named generators. It also swaps the two real
`ε = ±1` projectors, fixes their sum, and anti-fixes their difference.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove the analytic CPT theorem, antiunitarity of time
reversal, a charge-conjugation operator on fields, or a full Pin/O action.
Those require additional representation-level premises.
-/

noncomputable section

namespace InfoGeometry.Canonical.CPTRealCl11Emergence

open DiscreteCPTGroup
open InfoGeometry.Clifford.SplitQ11PhaseFlip
open InfoGeometry.Clifford.SplitQ11Projectors
open InfoGeometry.Clifford.SplitQ11Equivariance

/-- The real split `Cl(1,1)` carrier used by the emergence seed. -/
abbrev RealCl11 : Type :=
  Alg

/--
The real parity seed: the `K`-axis sign flip of split `Cl(1,1)`.

This is the algebraic `P`-bit action on the head `Cl(1,1)` atom. It is real and
does not introduce a complex scalar phase.
-/
abbrev realParityOperator : RealCl11 ≃ₐ[ℝ] RealCl11 :=
  phaseFlipAlg

/-- The finite bookkeeping label attached to the real split parity operator. -/
def realParityLabel : CPTElement :=
  P

/-- The real parity label is involutive in the finite CPT bookkeeping group. -/
@[simp] theorem realParityLabel_sq :
    cptMul realParityLabel realParityLabel = E := by
  simp [realParityLabel]

/-- Real split parity fixes the positive `J` generator. -/
@[simp] theorem realParityOperator_apply_jGen :
    realParityOperator jGen = jGen :=
  phaseFlip_apply_jGen

/-- Real split parity negates the negative `K` generator. -/
@[simp] theorem realParityOperator_apply_kGen :
    realParityOperator kGen = -kGen :=
  phaseFlip_apply_kGen

/-- Real split parity negates the real pseudoscalar `epsilon = JK`. -/
@[simp] theorem realParityOperator_apply_epsGen :
    realParityOperator epsGen = -epsGen :=
  phaseFlip_apply_epsGen

/-- Real split parity swaps the negative null generator with the positive one. -/
@[simp] theorem realParityOperator_apply_nullMinus :
    realParityOperator nullMinus = nullPlus :=
  phaseFlip_apply_nullMinus

/-- Real split parity swaps the positive null generator with the negative one. -/
@[simp] theorem realParityOperator_apply_nullPlus :
    realParityOperator nullPlus = nullMinus :=
  phaseFlip_apply_nullPlus

/-- The real parity seed has order two on the `J` generator. -/
@[simp] theorem realParityOperator_sq_jGen :
    realParityOperator (realParityOperator jGen) = jGen := by
  simp

/-- The real parity seed has order two on the `K` generator. -/
@[simp] theorem realParityOperator_sq_kGen :
    realParityOperator (realParityOperator kGen) = kGen := by
  simp

/-- The real parity seed has order two on the pseudoscalar. -/
@[simp] theorem realParityOperator_sq_epsGen :
    realParityOperator (realParityOperator epsGen) = epsGen := by
  simp

/-- The real parity seed has order two on the negative null generator. -/
@[simp] theorem realParityOperator_sq_nullMinus :
    realParityOperator (realParityOperator nullMinus) = nullMinus := by
  rw [realParityOperator_apply_nullMinus, realParityOperator_apply_nullPlus]

/-- The real parity seed has order two on the positive null generator. -/
@[simp] theorem realParityOperator_sq_nullPlus :
    realParityOperator (realParityOperator nullPlus) = nullPlus := by
  rw [realParityOperator_apply_nullPlus, realParityOperator_apply_nullMinus]

/-! ## Real graded sector action -/

/-- Real split parity swaps the `ε = -1` projector with the `ε = +1` projector. -/
@[simp] theorem realParityOperator_apply_epsMinusProjector :
    realParityOperator epsMinusProjector = epsPlusProjector :=
  phaseFlip_apply_epsMinusProjector

/-- Real split parity swaps the `ε = +1` projector with the `ε = -1` projector. -/
@[simp] theorem realParityOperator_apply_epsPlusProjector :
    realParityOperator epsPlusProjector = epsMinusProjector :=
  phaseFlip_apply_epsPlusProjector

/-- Real split parity fixes the complete `ε`-sector decomposition. -/
@[simp] theorem realParityOperator_apply_epsProjector_sum :
    realParityOperator (epsMinusProjector + epsPlusProjector) =
      epsMinusProjector + epsPlusProjector :=
  phaseFlip_apply_epsProjector_sum

/-- Real split parity anti-fixes the signed `ε`-sector difference. -/
@[simp] theorem realParityOperator_apply_epsProjector_diff :
    realParityOperator (epsMinusProjector - epsPlusProjector) =
      -(epsMinusProjector - epsPlusProjector) :=
  phaseFlip_apply_epsProjector_diff

/-- The real parity seed has order two on the `ε = -1` projector. -/
@[simp] theorem realParityOperator_sq_epsMinusProjector :
    realParityOperator (realParityOperator epsMinusProjector) = epsMinusProjector := by
  rw [realParityOperator_apply_epsMinusProjector, realParityOperator_apply_epsPlusProjector]

/-- The real parity seed has order two on the `ε = +1` projector. -/
@[simp] theorem realParityOperator_sq_epsPlusProjector :
    realParityOperator (realParityOperator epsPlusProjector) = epsPlusProjector := by
  rw [realParityOperator_apply_epsPlusProjector, realParityOperator_apply_epsMinusProjector]

/--
The real split `P` action is exactly the first finite CPT bookkeeping bit plus
the verified phase-flip action on the real `Cl(1,1)` sector decomposition.
-/
theorem realParity_seed_package :
    cptMul realParityLabel realParityLabel = E
      ∧ realParityOperator jGen = jGen
      ∧ realParityOperator kGen = -kGen
      ∧ realParityOperator epsGen = -epsGen
      ∧ realParityOperator epsMinusProjector = epsPlusProjector
      ∧ realParityOperator epsPlusProjector = epsMinusProjector
      ∧ realParityOperator (epsMinusProjector + epsPlusProjector) =
          epsMinusProjector + epsPlusProjector
      ∧ realParityOperator (epsMinusProjector - epsPlusProjector) =
          -(epsMinusProjector - epsPlusProjector) := by
  exact ⟨realParityLabel_sq, realParityOperator_apply_jGen,
    realParityOperator_apply_kGen, realParityOperator_apply_epsGen,
    realParityOperator_apply_epsMinusProjector, realParityOperator_apply_epsPlusProjector,
    realParityOperator_apply_epsProjector_sum, realParityOperator_apply_epsProjector_diff⟩

end InfoGeometry.Canonical.CPTRealCl11Emergence
