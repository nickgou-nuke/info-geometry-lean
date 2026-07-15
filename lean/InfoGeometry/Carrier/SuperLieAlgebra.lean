/-
# SuperLieAlgebra.lean

ℤ₂-graded Lie superalgebra over ℝ (carrier-level typeclass).

This file re-exports `SuperLieRing` from `InfoGeometry.Algebra` and adds
carrier-level convenience proofs.

The typeclass hierarchy is:
  `SuperBracket` (minimal ℝ-bilinear bracket)
    ⤷ `SuperLieRing` (ℤ₂-grading + graded anti-commutativity + super Jacobi)
        ⤷ `SuperLieAlgebra` (carrier-level, may add carrier-specific results)
-/

import Mathlib
import InfoGeometry.Algebra.SuperLieRing
import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

set_option linter.dupNamespace false

noncomputable section

namespace InfoGeometry.Carrier

open FiveGradedInformationLedger

/--
A **super Lie algebra** over ℝ is the carrier-level alias for `SuperLieRing`.

See `InfoGeometry.Algebra.SuperLieRing` for the full axiom list.
-/
class SuperLieAlgebra (L : Type*) extends InfoGeometry.Algebra.SuperLieRing L

namespace SuperLieAlgebra

variable {L : Type*} [SuperLieAlgebra L]

open InfoGeometry.Algebra

/-- Every element splits into even + odd parts. -/
theorem exists_decomposition (x : L) :
    ∃ (e : L) (o : L), e ∈ SuperLieRing.evenPart ∧ o ∈ SuperLieRing.oddPart ∧ x = e + o :=
  SuperLieRing.exists_decomposition x

/-- Derived: odd-even skew follows from even-odd skew. -/
theorem odd_even_skew (x y : L) (hx : x ∈ SuperLieRing.oddPart) (hy : y ∈ SuperLieRing.evenPart) :
    ⁅x, y⁆ = -⁅y, x⁆ :=
  SuperLieRing.odd_even_skew x y hx hy

end SuperLieAlgebra

end InfoGeometry.Carrier
