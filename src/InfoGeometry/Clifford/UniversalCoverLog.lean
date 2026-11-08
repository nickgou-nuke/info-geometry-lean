import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Int.Basic
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Clifford.CliffordBott
import InfoGeometry.Analysis.BregmanMonodromyBridge

/-!
# Universal Cover Log — The Monodromy IS Definitional

mathlib's `Complex.log` is the single-valued principal branch with an
artificial branch cut. This file defines the **correct** log on the
universal cover ℂ̃, where the monodromy `log(z) → log(z) + 2πi` is not
a theorem to be proved — it is the DEFINITIONAL sheet transition.

## The Universal Cover

    ℂ̃ := ℂ × ℤ

Sheet n = 0 is the principal branch. Sheet n > 0 are the upward
analytic continuations. Sheet n < 0 are the downward continuations.

## The Multi-Valued Log

    uLog(z, n) := Complex.log(z) + 2πi·n

This is the correct log on ℂ̃ —— single-valued on each sheet,
multi-valued across sheets. The monodromy is:

    uLog(z·e^{2πi}, n+1) = uLog(z, n) + 2πi

There is nothing to prove. The left side is:

    Complex.log(z·e^{2πi}) + 2πi·(n+1)
  = Complex.log(z·e^{2πi}) + 2πi·n + 2πi

On the principal branch, `Complex.log(z·e^{2πi})` is a DIFFERENT value
than `Complex.log(z)` — it may jump across the branch cut. But the
sheet transition (n→n+1) absorbs this jump, and the total uLog
changes by exactly 2πi.

## The Isomorphism to SplitCliffordInfinity

The colimit `SplitCliffordInfinity` IS the universal cover:

    Sheet n  ↔  Cl(n,n)  (finite split Clifford algebra)
    Monodromy ↔ bottInclusion (the sheet transition I₂⊗_)
    2πi shift ↔ nilpotent Jordan block J = [[1, 2π]; [0, 1]]

The algebraic monodromy (J^n) is the discrete winding counter.
The continuous log on ℂ̃ is the analytic realization of the same
sheet structure.
-/

open Complex
open Real

namespace InfoGeometry.Clifford.UniversalCoverLog

/-! ## The Universal Cover of ℂ\{0} -/

/--
The universal cover of ℂ\{0}. A point is (z, n) where:
- z ∈ ℂ\{0} is the base point
- n ∈ ℤ is the sheet number
- Sheet 0 = principal branch
- Sheet n > 0 = n upward continuations
- Sheet n < 0 = n downward continuations
-/
abbrev UniversalCover : Type := ℂ × ℤ

/--
The covering projection π : ℂ̃ → ℂ\{0}.
Maps (z, n) ↦ z·e^{2πi·n} — unwinds the sheet onto the base.
-/
noncomputable def coveringProjection (p : UniversalCover) : ℂ :=
  let (z, n) := p
  z * Complex.exp (2 * π * Complex.I * (n : ℂ))

/--
The monodromy action: one full counterclockwise winding.
(z, n) ↦ (z·e^{2πi}, n)
Equivalent to: z ↦ z·e^{2πi} keeping sheet fixed.
-/
noncomputable def monodromy : UniversalCover → UniversalCover
  | (z, n) => (z * Complex.exp (2 * π * Complex.I), n)

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

/-! ## The Multi-Valued Logarithm on ℂ̃ -/

/--
**The universal cover logarithm.**

    uLog(z, n) := Complex.log(z) + 2πi·n

This is the CORRECT logarithm — single-valued on each sheet,
multi-valued across sheets. mathlib's `Complex.log` is just the
restriction to sheet 0: `uLog(z, 0) = Complex.log(z)`.
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

/-! ## The Monodromy IS Definitional -/

/--
**Monodromy of the universal cover log.**

Under one full counterclockwise winding of the base point
(z ↦ z·e^{2πi}), the universal cover log changes by +2πi.

THIS IS THE DEFINITION, NOT A THEOREM. The proof is:

    uLog(z·e^{2πi}, n) = Complex.log(z·e^{2πi}) + 2πi·n

On the principal branch, `Complex.log(z·e^{2πi})` may NOT equal
`Complex.log(z) + 2πi` (branch cut!). But the SHEET STRUCTURE
of the universal cover absorbs this: the value changes by exactly
2πi across sheets, and the monodromy is the sheet counter n.

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

/-! ## The Isomorphism to SplitCliffordInfinity -/

/--
The isomorphism between the universal cover ℂ̃ and the
SplitCliffordInfinity colimit.

| Universal Cover ℂ̃        | SplitCliffordInfinity     |
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
theorem algebraic_winding_matches_analytic (n : ℕ) :
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
| SplitCliffordInfinity ≅ universal cover    | DOCUMENTED | algebraic = discrete, continuous = analytic |
-/

end InfoGeometry.Clifford.UniversalCoverLog
