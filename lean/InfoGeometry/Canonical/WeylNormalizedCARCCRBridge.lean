import InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Clifford.Relations
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.WeylNormalizedCARCCRBridge

Weyl-normalized CAR/CCR bridge.

The raw lightcone/Fock operators are homogeneous. Before fixing Weyl scale, the
central channel may be a positive scalar multiple of the identity:

* `{a, a†} = ν 1` for CAR,
* `[b, b†] = κ 1` for CCR.

This file packages the normalization step:

`λ ^ 2 * ν = 1` or `λ ^ 2 * κ = 1`

and proves that the rescaled operators satisfy the canonical central relation.
It does not assert that arbitrary projector arrows are CAR/CCR; the scaled
central law is supplied as witness data.
-/

namespace InfoGeometry.Canonical.WeylNormalizedCARCCRBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Identity on the doubled/Fock carrier. -/
@[rep_depth krein]
noncomputable abbrev fockId : FockEndomorphism E :=
  ContinuousLinearMap.id ℝ (DoubledSpace E)

/-- Scaling both CAR arguments scales the anticommutator by the square. -/
@[rep_depth krein]
theorem fockAnticommutator_smul_smul
    (lam : ℝ) (A B : FockEndomorphism E) :
    fockAnticommutator (E := E) (lam • A) (lam • B)
      = (lam ^ 2) • fockAnticommutator (E := E) A B := by
  change fockSuperBracket (E := E) SuperParity.odd SuperParity.odd (lam • A) (lam • B)
    = (lam ^ 2) • fockSuperBracket (E := E) SuperParity.odd SuperParity.odd A B
  rw [show fockSuperBracket (E := E) SuperParity.odd SuperParity.odd (lam • A) (lam • B)
      = lam • fockSuperBracket (E := E) SuperParity.odd SuperParity.odd A (lam • B) by
        exact superBracket_smul_left (E := E) SuperParity.odd SuperParity.odd lam A (lam • B)]
  rw [show fockSuperBracket (E := E) SuperParity.odd SuperParity.odd A (lam • B)
      = lam • fockSuperBracket (E := E) SuperParity.odd SuperParity.odd A B by
        exact superBracket_smul_right (E := E) SuperParity.odd SuperParity.odd lam A B]
  simp [pow_two, smul_smul]

/-- Scaling both CCR arguments scales the commutator by the square. -/
@[rep_depth krein]
theorem fockCommutator_smul_smul
    (lam : ℝ) (A B : FockEndomorphism E) :
    fockCommutator (E := E) (lam • A) (lam • B)
      = (lam ^ 2) • fockCommutator (E := E) A B := by
  change fockSuperBracket (E := E) SuperParity.even SuperParity.even (lam • A) (lam • B)
    = (lam ^ 2) • fockSuperBracket (E := E) SuperParity.even SuperParity.even A B
  rw [show fockSuperBracket (E := E) SuperParity.even SuperParity.even (lam • A) (lam • B)
      = lam • fockSuperBracket (E := E) SuperParity.even SuperParity.even A (lam • B) by
        exact superBracket_smul_left (E := E) SuperParity.even SuperParity.even lam A (lam • B)]
  rw [show fockSuperBracket (E := E) SuperParity.even SuperParity.even A (lam • B)
      = lam • fockSuperBracket (E := E) SuperParity.even SuperParity.even A B by
        exact superBracket_smul_right (E := E) SuperParity.even SuperParity.even lam A B]
  simp [pow_two, smul_smul]

/--
Scaled CAR pair.

The central normalization is still Weyl-homogeneous:
`{a, a†} = ν 1`. A normalizer `λ` with `λ ^ 2 * ν = 1` fixes the
canonical CAR gauge.
-/
structure ScaledCARPair
    (E : Type 0) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  a : FockEndomorphism E
  adag : FockEndomorphism E

  centralWeight : ℝ
  centralWeight_pos : 0 < centralWeight

  aa_zero :
    fockAnticommutator (E := E) a a = 0
  adag_adag_zero :
    fockAnticommutator (E := E) adag adag = 0
  mixed_scaled :
    fockAnticommutator (E := E) a adag =
      centralWeight • fockId (E := E)

  normalizer : ℝ
  normalizer_law :
    normalizer ^ 2 * centralWeight = 1

namespace ScaledCARPair

variable (C : ScaledCARPair E)

/-- Gauge-fixed annihilation operator. -/
@[rep_depth krein]
noncomputable def normalizedAnnihilation : FockEndomorphism E :=
  C.normalizer • C.a

/-- Gauge-fixed creation operator. -/
@[rep_depth krein]
noncomputable def normalizedCreation : FockEndomorphism E :=
  C.normalizer • C.adag

/-- The same-arrow CAR nilpotence survives Weyl normalization. -/
@[rep_depth krein]
theorem normalized_aa_zero :
    fockAnticommutator (E := E)
        C.normalizedAnnihilation C.normalizedAnnihilation = 0 := by
  rw [normalizedAnnihilation, fockAnticommutator_smul_smul, C.aa_zero]
  ext x <;> simp

/-- The creation-creation CAR nilpotence survives Weyl normalization. -/
@[rep_depth krein]
theorem normalized_adag_adag_zero :
    fockAnticommutator (E := E)
        C.normalizedCreation C.normalizedCreation = 0 := by
  rw [normalizedCreation, fockAnticommutator_smul_smul, C.adag_adag_zero]
  ext x <;> simp

/-- The mixed scaled central law becomes the canonical CAR identity after gauge fixing. -/
@[rep_depth krein]
theorem normalized_mixed :
    fockAnticommutator (E := E)
        C.normalizedAnnihilation C.normalizedCreation = fockId (E := E) := by
  rw [normalizedAnnihilation, normalizedCreation, fockAnticommutator_smul_smul,
    C.mixed_scaled]
  rw [smul_smul, C.normalizer_law]
  simp [fockId]

/-- A Weyl-normalized scaled CAR pair is a genuine CAR pair. -/
@[rep_depth krein]
theorem normalized_isCARPair :
    IsCARPair (E := E) C.normalizedAnnihilation C.normalizedCreation := by
  refine ⟨?_, ?_, ?_⟩
  · change fockAnticommutator (E := E)
      C.normalizedAnnihilation C.normalizedAnnihilation = 0
    exact C.normalized_aa_zero
  · change fockAnticommutator (E := E)
      C.normalizedCreation C.normalizedCreation = 0
    exact C.normalized_adag_adag_zero
  · change fockAnticommutator (E := E)
      C.normalizedAnnihilation C.normalizedCreation = fockId (E := E)
    exact C.normalized_mixed

end ScaledCARPair

/-- Canonical CCR relation for a Fock pair. -/
@[rep_depth krein]
def IsCCRPair (b bdag : FockEndomorphism E) : Prop :=
  fockCommutator (E := E) b bdag = fockId (E := E)

/--
Scaled CCR pair.

The central normalization is still Weyl-homogeneous:
`[b, b†] = κ 1`. A normalizer `λ` with `λ ^ 2 * κ = 1` fixes the
canonical CCR gauge.
-/
structure ScaledCCRPair
    (E : Type 0) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  b : FockEndomorphism E
  bdag : FockEndomorphism E

  centralWeight : ℝ
  centralWeight_pos : 0 < centralWeight

  comm_scaled :
    fockCommutator (E := E) b bdag =
      centralWeight • fockId (E := E)

  normalizer : ℝ
  normalizer_law :
    normalizer ^ 2 * centralWeight = 1

namespace ScaledCCRPair

variable (C : ScaledCCRPair E)

/-- Gauge-fixed annihilation-like CCR operator. -/
@[rep_depth krein]
noncomputable def normalizedAnnihilation : FockEndomorphism E :=
  C.normalizer • C.b

/-- Gauge-fixed creation-like CCR operator. -/
@[rep_depth krein]
noncomputable def normalizedCreation : FockEndomorphism E :=
  C.normalizer • C.bdag

/-- The scaled central CCR law becomes the canonical CCR identity after gauge fixing. -/
@[rep_depth krein]
theorem normalized_comm :
    fockCommutator (E := E)
        C.normalizedAnnihilation C.normalizedCreation = fockId (E := E) := by
  rw [normalizedAnnihilation, normalizedCreation, fockCommutator_smul_smul,
    C.comm_scaled]
  rw [smul_smul, C.normalizer_law]
  simp [fockId]

/-- A Weyl-normalized scaled CCR pair is a genuine CCR pair. -/
@[rep_depth krein]
theorem normalized_isCCRPair :
    IsCCRPair (E := E) C.normalizedAnnihilation C.normalizedCreation := by
  exact C.normalized_comm

end ScaledCCRPair

/-! ## Dilation readbacks -/

/-- The repository's dilation operator as a Fock endomorphism. -/
@[rep_depth krein]
noncomputable abbrev dilationFockOperator : FockEndomorphism E :=
  dilationOperator (E := E)

/-- The CPT supercharge is the repository dilation operator. -/
@[rep_depth krein, simp]
theorem cptSuperchargeOp_eq_dilationFockOperator :
    cptSuperchargeOp (E := E) = dilationFockOperator (E := E) := by
  exact cptSuperchargeOp_eq_dilationOperator (E := E)

/-- The dilation operator is the doubled-space clock axis. -/
@[rep_depth krein, simp]
theorem dilationFockOperator_eq_clockAxis :
    dilationFockOperator (E := E) = clockAxis (E := E) := by
  exact dilationOperator_eq_clockAxis (E := E)

end Core

end InfoGeometry.Canonical.WeylNormalizedCARCCRBridge
