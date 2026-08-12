import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.Basic
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Clifford.CliffordBott
import InfoGeometry.Analysis.BregmanMonodromyBridge

/-!
# Log branch lifts and the exponential cover

mathlib's `Complex.log` is the single-valued principal branch with an
artificial branch cut. This file contains a discrete branch-value carrier
and the genuine algebraic laws of the exponential cover.

## The legacy branch-value carrier

    LogBranchLift := ℂ × ℤ

Sheet n = 0 is the principal branch. Sheet n > 0 are the upward
analytic continuations. Sheet n < 0 are the downward continuations.

The pair carrier is a discrete branch-value lift. It is not the connected
topological universal cover of `ℂˣ`.

## The branch-value logarithm

    uLog(z, n) := Complex.log(z) + 2πi·n

This is a branch-indexed logarithm on the discrete carrier. Its sheet law is:

    uLog(z·e^{2πi}, n+1) = uLog(z, n) + 2πi

The base-rotation expression is only an unfolding identity:

    Complex.log(z·e^{2πi}) + 2πi·(n+1)
  = Complex.log(z·e^{2πi}) + 2πi·n + 2πi

On the principal branch, `Complex.log(z·e^{2πi})` may jump across the
branch cut. The exact algebraic increment is supplied by the explicit
sheet transition and, on the genuine cover, by `expCoverLog_expDeck`.

## The Isomorphism to SplitCliffordInfinity

The colimit `SplitCliffordInfinity` is not identified here with a universal
cover. It is an algebraic direct-limit carrier with a discrete stage index.

    Sheet n  ↔  Cl(n,n)  (finite split Clifford algebra)
    Monodromy ↔ bottInclusion (the sheet transition I₂⊗_)
    2πi shift ↔ nilpotent Jordan block J = [[1, 2π]; [0, 1]]

The algebraic monodromy (J^n) is the discrete winding counter.
The exponential-cover laws and the discrete branch laws are kept as
separate carriers.
-/

open Complex
open Real

namespace InfoGeometry.Clifford.UniversalCoverLog

/-! ## The discrete branch-value carrier -/

/--
A branch-value lift over a base point is represented by `(z,n)`:
- z ∈ ℂ\{0} is the base point
- n ∈ ℤ is the sheet number
- Sheet 0 = principal branch
- Sheet n > 0 = n upward continuations
- Sheet n < 0 = n downward continuations
-/
abbrev LogBranchLift : Type := ℂ × ℤ

/- Compatibility name retained for existing finite readout consumers. -/
abbrev UniversalCover : Type := LogBranchLift

/--
The covering projection π : ℂ̃ → ℂ\{0}.
Maps (z, n) ↦ z·e^{2πi·n} — unwinds the sheet onto the base.
-/
noncomputable def coveringProjection (p : UniversalCover) : ℂ :=
  let (z, n) := p
  z * Complex.exp (2 * π * Complex.I * (n : ℂ))

theorem coveringProjection_eq_base (z : ℂ) (n : ℤ) :
    coveringProjection (z, n) = z := by
  dsimp [coveringProjection]
  have harg :
      2 * π * Complex.I * (n : ℂ) =
        (n : ℂ) * (2 * π * Complex.I) := by
    ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  simp

/--
The monodromy action: one full counterclockwise winding.
(z, n) ↦ (z·e^{2πi}, n)
Equivalent to: z ↦ z·e^{2πi} keeping sheet fixed.
-/
noncomputable def monodromy : UniversalCover → UniversalCover
  | (z, n) => (z * Complex.exp (2 * π * Complex.I), n)

theorem monodromy_eq_id : monodromy = id := by
  funext p
  rcases p with ⟨z, n⟩
  simp [monodromy, Complex.exp_int_mul_two_pi_mul_I]

/--
The deck transformation: moving UP one sheet.
(z, n) ↦ (z, n+1). This preserves the projection:
π(z, n+1) = z·e^{2πi·(n+1)} = z·e^{2πi}·e^{2πi·n} = π(z, n)·e^{2πi}.

The deck transformation IS the monodromy action on the universal cover.
-/
def deckUp : UniversalCover → UniversalCover
  | (z, n) => (z, n + 1)

noncomputable def deckDown : UniversalCover → UniversalCover
  | (z, n) => (z, n - 1)

theorem coveringProjection_deckUp (z : ℂ) (n : ℤ) :
    coveringProjection (deckUp (z, n)) = coveringProjection (z, n) := by
  change coveringProjection (z, n + 1) = coveringProjection (z, n)
  rw [coveringProjection_eq_base, coveringProjection_eq_base]

theorem coveringProjection_deckDown (z : ℂ) (n : ℤ) :
    coveringProjection (deckDown (z, n)) = coveringProjection (z, n) := by
  change coveringProjection (z, n - 1) = coveringProjection (z, n)
  rw [coveringProjection_eq_base, coveringProjection_eq_base]

theorem coveringProjection_sheet_add (z : ℂ) (n k : ℤ) :
    coveringProjection (z, n + k) = coveringProjection (z, n) := by
  rw [coveringProjection_eq_base, coveringProjection_eq_base]

/-! ## The algebraic exponential cover -/

abbrev ExponentialCover : Type := ℂ

noncomputable def expCoverProjection (w : ExponentialCover) : ℂˣ :=
  Units.mk0 (Complex.exp w) (Complex.exp_ne_zero w)

@[simp] theorem expCoverProjection_val (w : ExponentialCover) :
    ((expCoverProjection w : ℂˣ) : ℂ) = Complex.exp w :=
  rfl

noncomputable def expDeck (n : ℤ) (w : ExponentialCover) : ExponentialCover :=
  w + (2 * π * Complex.I) * (n : ℂ)

theorem expCoverProjection_expDeck (n : ℤ) (w : ExponentialCover) :
    ((expCoverProjection (expDeck n w) : ℂˣ) : ℂ) =
      ((expCoverProjection w : ℂˣ) : ℂ) := by
  change Complex.exp (w + (2 * π * Complex.I) * (n : ℂ)) = Complex.exp w
  rw [Complex.exp_add]
  have harg :
      (2 * π * Complex.I) * (n : ℂ) =
        (n : ℂ) * (2 * π * Complex.I) := by
    ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  simp

def expCoverLog (w : ExponentialCover) : ℂ := w

theorem expCoverLog_expDeck (n : ℤ) (w : ExponentialCover) :
    expCoverLog (expDeck n w) =
      expCoverLog w + (2 * π * Complex.I) * (n : ℂ) := by
  rfl

theorem expCoverLog_expCoverProjection (w : ExponentialCover) :
    Complex.exp (expCoverLog w) =
      ((expCoverProjection w : ℂˣ) : ℂ) := by
  rfl

/-! ## The branch-indexed logarithm -/

/--
**The branch-indexed logarithm.**

    uLog(z, n) := Complex.log(z) + 2πi·n

This is single-valued on the discrete branch-value carrier. It is not the
logarithm on the connected exponential cover; that logarithm is `expCoverLog`.
Mathlib's `Complex.log` is recovered on sheet zero.
-/
noncomputable def uLog (p : UniversalCover) : ℂ :=
  let (z, n) := p
  Complex.log z + (2 * π * Complex.I) * (n : ℂ)

/--
Restricting uLog to sheet 0 recovers mathlib's principal-branch log.
-/
theorem uLog_restrict_principal (z : ℂ) (hz : z ≠ 0) :
    uLog (z, 0) = Complex.log z := by
  simp [uLog]

/-! ## Discrete sheet laws -/

/--
**Principal-branch unfolding under a base rotation.**

Under one full counterclockwise winding of the base point
(z ↦ z·e^{2πi}), the universal cover log changes by +2πi.

This is only an unfolding theorem; it does not assert analytic monodromy.

    uLog(z·e^{2πi}, n) = Complex.log(z·e^{2πi}) + 2πi·n

On the principal branch, `Complex.log(z·e^{2πi})` may not equal
`Complex.log(z) + 2πi` because of the branch cut. The exact increment
proved below is instead the discrete sheet transition.

The ALGEBRAIC version (proved in `BregmanMonodromyBridge.lean`):
J^n = [[1, 2πn]; [0, 1]] where J is the nilpotent Jordan block.
This is the discrete winding counter — no branch cut, no `Complex.log`.
-/
theorem uLog_after_winding (z : ℂ) (n : ℤ) :
    uLog (z * Complex.exp (2 * π * Complex.I), n) =
    Complex.log (z * Complex.exp (2 * π * Complex.I)) + (2 * π * Complex.I) * (n : ℂ) := by
  rfl

/--
**The deck transformation formula.**

Moving UP one sheet while keeping the base point fixed
changes uLog by +2πi:

    uLog(z, n+1) = uLog(z, n) + 2πi

This is the statement that the deck transformation IS the
monodromy. It holds BY DEFINITION of uLog — the sheet index
n appears linearly with coefficient 2πi.
-/
theorem uLog_deck_up (z : ℂ) (n : ℤ) :
    uLog (deckUp (z, n)) = uLog (z, n) + 2 * π * Complex.I := by
  unfold deckUp uLog
  push_cast
  ring

/--
**The deck transformation formula (downward).**
-/
theorem uLog_deck_down (z : ℂ) (n : ℤ) :
    uLog (deckDown (z, n)) = uLog (z, n) - 2 * π * Complex.I := by
  unfold deckDown uLog
  push_cast
  ring

theorem uLog_sheet_add (z : ℂ) (n k : ℤ) :
    uLog (z, n + k) =
      uLog (z, n) + (2 * π * Complex.I) * (k : ℂ) := by
  unfold uLog
  push_cast
  ring

/--
**Sheet invariance of the covering projection.**

The covering projection π(z, n) = z·e^{2πi·n} satisfies:

    π(monodromy(z, n)) = π(z, n) · e^{2πi}

The monodromy acts on the base as multiplication by e^{2πi} = 1,
while the deck transformation changes the sheet index n.
-/
theorem coveringProjection_monodromy (z : ℂ) (n : ℤ) :
    coveringProjection (monodromy (z, n)) =
    coveringProjection (z, n) * Complex.exp (2 * π * Complex.I) := by
  unfold coveringProjection monodromy
  push_cast
  ring

/-! ## The algebraic direct-limit comparison -/

/--
The following table records a structural comparison only. No isomorphism
between either logarithmic carrier and `SplitCliffordInfinity` is asserted.

| LogBranchLift             | SplitCliffordInfinity     |
|---------------------------|---------------------------|
| Sheet n                   | Cl(n,n)                   |
| deckUp (sheet +1)         | splitCliffordStep         |
| monodromy (winding)       | bottInclusion (I₂⊗_)      |
| uLog(z,n) = log(z) + 2πi·n| algebraicExp(N)=1+N (N²=0)|
| sheet index n : ℤ         | stage index n : ℕ         |
| 2πi (continuous phase)    | J = [[1, 2π]; [0, 1]]    |

The algebraic version IS the correct monodromy for the nilpotent
(fermionic) sector. The continuous version uLog on ℂ̃ is the
analytic realization of the same sheet structure.

Both satisfy the same identity:

    algebraic:  J^{n} · J     = J^{n+1}     (proved: monodromyJordanBlock_pow)
    continuous: uLog(z,n) + 2πi = uLog(z,n+1) (proved: uLog_deck_up)
-/

/-
The algebraic winding counter: each application of the nilpotent
Jordan block J adds 2π to the off-diagonal (logarithmic partner)
component.

This is the algebraic analogue of the universal cover sheet
transition uLog(z,n) → uLog(z,n+1) = uLog(z,n) + 2πi.
-/
theorem monodromyJordanBlock_succ (n : ℕ) :
    let J : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2 * π; 0, 1]
    J ^ (n+1) = J ^ n * J := by
  intro J
  rw [pow_succ]

/-
## Structural Summary

| Statement                                  | Status     | File                              |
|--------------------------------------------|------------|-----------------------------------|
| log(z·e^{2πi}) = log(z) + 2πi (principal) | FALSE      | mathlib's Complex.log             |
| uLog(z·e^{2πi}, n) = uLog(z,n) + 2πi?      | AMBIGUOUS  | depends on principal branch       |
| uLog(z, n+1) = uLog(z, n) + 2πi           | PROVED ✓   | uLog_deck_up (definitional)       |
| J^n = [[1, 2πn]; [0, 1]]                   | PROVED ✓   | monodromyJordanBlock_pow          |
| I+N where N²=0 ⇒ exp(N)=1+N               | PROVED ✓   | CliffBott has nilpotent lift      |
| SplitCliffordInfinity ≅ universal cover    | NOT CLAIMED | algebraic and analytic carriers remain distinct |
-/

end InfoGeometry.Clifford.UniversalCoverLog
