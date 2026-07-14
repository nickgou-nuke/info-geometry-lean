import InfoGeometry.Clifford.LogCftMonodromy
import Mathlib.Tactic

noncomputable section

/-!
# ExchangeSMatrixBridge

Finite matrix bridge from logarithmic monodromy blocks to an S-matrix-facing
lower-triangular exchange constraint.

The file does not formalize the full Todorov--Hadjiivanov analytic exchange
algebra.  It records the kernel-checked algebraic shadow used downstream:
once a local exchange/monodromy block is in the lower parabolic form
`phase • (1 + shear L)` with `L² = 0`, finite products of such blocks remain
in the same lower parabolic class.  The global S-block therefore has multiplied
phase and additively accumulated logarithmic shear.
-/

namespace ExchangeSMatrixBridge

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

/-- The concrete two-state scattering block used by the LCFT monodromy lane. -/
abbrev SBlock := Matrix (Fin 2) (Fin 2) ℂ

/--
Lower parabolic S-matrix block:
`phase` times the lower unipotent shear `1 + shear L`.
-/
def lowerParabolicSBlock (phase shear : ℂ) : SBlock :=
  phase • ((1 : SBlock) + shear • lowerJordanNilpotent)

/--
Predicate saying that a local exchange block has exactly the protected lower
parabolic form.
-/
def ExchangeLowerBlockConstraint (M : SBlock) (phase shear : ℂ) : Prop :=
  M = lowerParabolicSBlock phase shear

/-- The lower Jordan nilpotent matrix strictly squares to zero. -/
theorem lowerJordanNilpotent_sq :
    (lowerJordanNilpotent : SBlock) * lowerJordanNilpotent = 0 := by
  exact InfoGeometry.Clifford.LogCftMonodromy.lowerJordanNilpotent_sq (K := ℂ)

/-- The normalized lower parabolic block with unit phase and zero shear is the identity. -/
@[simp]
theorem lowerParabolicSBlock_one_zero :
    lowerParabolicSBlock 1 0 = (1 : SBlock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerParabolicSBlock, lowerJordanNilpotent]

/-- Coordinate form of a lower parabolic S-block. -/
theorem lowerParabolicSBlock_form (phase shear : ℂ) :
    lowerParabolicSBlock phase shear = lowerJordan phase (phase * shear) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerParabolicSBlock, lowerJordan, lowerJordanNilpotent]

/-- Exact entry-by-entry evaluation of the lower parabolic S-block. -/
theorem lowerParabolicSBlock_apply (phase shear : ℂ) :
    lowerParabolicSBlock phase shear =
      !![phase, 0; phase * shear, phase] := by
  rw [lowerParabolicSBlock_form]
  rfl

/-- A lower parabolic S-block has no upper-right leakage. -/
theorem lowerParabolicSBlock_upper_right_zero (phase shear : ℂ) :
    lowerParabolicSBlock phase shear 0 1 = 0 := by
  simp [lowerParabolicSBlock, lowerJordanNilpotent]

/-- No-leakage readout: the upper-right entry of a lower parabolic S-block vanishes. -/
theorem no_upper_right_leakage (phase shear : ℂ) :
    lowerParabolicSBlock phase shear 0 1 = 0 :=
  lowerParabolicSBlock_upper_right_zero phase shear

/-- A lower parabolic S-block has equal diagonal entries. -/
theorem lowerParabolicSBlock_equal_diagonal (phase shear : ℂ) :
    lowerParabolicSBlock phase shear 0 0 =
      lowerParabolicSBlock phase shear 1 1 := by
  simp [lowerParabolicSBlock, lowerJordanNilpotent]

/--
The product of two lower parabolic S-blocks is again lower parabolic: phases
multiply and logarithmic shears add.
-/
theorem lowerParabolicSBlock_mul (phase₁ phase₂ shear₁ shear₂ : ℂ) :
    lowerParabolicSBlock phase₁ shear₁ * lowerParabolicSBlock phase₂ shear₂ =
      lowerParabolicSBlock (phase₁ * phase₂) (shear₁ + shear₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerParabolicSBlock, lowerJordanNilpotent, Matrix.mul_apply]
  all_goals ring

/--
Hadjiivanov winding law for a local lower exchange block:
the phase exponentiates and the logarithmic shear accumulates linearly.
-/
theorem hadjiivanov_winding_law (phase shear : ℂ) (n : ℕ) :
    lowerParabolicSBlock phase shear ^ n =
      lowerParabolicSBlock (phase ^ n) ((n : ℂ) * shear) := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [lowerParabolicSBlock_apply]
  | succ n ih =>
      rw [pow_succ, ih, lowerParabolicSBlock_mul]
      congr 1
      rw [Nat.cast_succ]
      ring

/--
Local exchange constraints control the product S-block: multiplying two
constrained blocks produces another constrained lower parabolic block.
-/
theorem exchange_constraints_mul_control_smatrix
    {M₁ M₂ : SBlock} {phase₁ phase₂ shear₁ shear₂ : ℂ}
    (h₁ : ExchangeLowerBlockConstraint M₁ phase₁ shear₁)
    (h₂ : ExchangeLowerBlockConstraint M₂ phase₂ shear₂) :
    ExchangeLowerBlockConstraint (M₁ * M₂) (phase₁ * phase₂) (shear₁ + shear₂) := by
  unfold ExchangeLowerBlockConstraint at h₁ h₂ ⊢
  rw [h₁, h₂, lowerParabolicSBlock_mul]

/--
The lower Hadjiivanov monodromy after `n` wraps satisfies the exchange-block
constraint with accumulated phase `phase^n` and shear `n * (-2πi)`.
-/
theorem lowerHadjiivanov_winding_exchange_constraint (h : ℂ) (n : ℕ) :
    ExchangeLowerBlockConstraint
      (lowerHadjiivanovMonodromy h ^ n)
      (lcftPhase h ^ n)
      ((n : ℂ) * logShearBase) := by
  unfold ExchangeLowerBlockConstraint lowerParabolicSBlock
  exact lowerHadjiivanovMonodromy_pow_winding h n

/-- Phase accumulated by a finite list of local lower parabolic exchange blocks. -/
def lowerExchangePhase : List (ℂ × ℂ) → ℂ
  | [] => 1
  | b :: bs => b.1 * lowerExchangePhase bs

/-- Additive shear accumulated by a finite list of local lower parabolic exchange blocks. -/
def lowerExchangeShear : List (ℂ × ℂ) → ℂ
  | [] => 0
  | b :: bs => b.2 + lowerExchangeShear bs

/-- Ordered finite product of local lower parabolic exchange S-blocks. -/
def lowerExchangeSMatrix : List (ℂ × ℂ) → SBlock
  | [] => 1
  | b :: bs => lowerParabolicSBlock b.1 b.2 * lowerExchangeSMatrix bs

/--
Finite exchange/S-matrix composition theorem.

A global S-block assembled from lower parabolic local exchange blocks is again
a lower parabolic S-block.  This is the precise finite algebraic control
statement: no upper-right leakage appears, and the only nontrivial off-diagonal
datum is the accumulated logarithmic shear.
-/
theorem lowerExchangeSMatrix_eq_lowerParabolicSBlock (blocks : List (ℂ × ℂ)) :
    lowerExchangeSMatrix blocks =
      lowerParabolicSBlock (lowerExchangePhase blocks) (lowerExchangeShear blocks) := by
  induction blocks with
  | nil =>
      simp [lowerExchangeSMatrix, lowerExchangePhase, lowerExchangeShear]
  | cons b bs ih =>
      simp [lowerExchangeSMatrix, lowerExchangePhase, lowerExchangeShear, ih,
        lowerParabolicSBlock_mul]

/-- A finite exchange S-matrix assembled from constrained blocks has no upper-right leakage. -/
theorem lowerExchangeSMatrix_upper_right_zero (blocks : List (ℂ × ℂ)) :
    lowerExchangeSMatrix blocks 0 1 = 0 := by
  rw [lowerExchangeSMatrix_eq_lowerParabolicSBlock]
  exact lowerParabolicSBlock_upper_right_zero
    (lowerExchangePhase blocks) (lowerExchangeShear blocks)

end ExchangeSMatrixBridge
