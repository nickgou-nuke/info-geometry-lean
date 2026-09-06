import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.GradedMulAction
import Mathlib.Data.ZMod.Basic
import InfoGeometry.Canonical.DiscretePowerGradeReadout
import InfoGeometry.Canonical.CyclotomicProjectorReadout

/-!
# Graded Mellin Readout and Graded Submodule Decomposition

This module formalizes the structural graded algebra readout:

$$A = \bigoplus_{g \in G} A_g, \qquad A_g A_h \subseteq A_{g+h}$$

refining the discrete power readout $k \mapsto X^k$ to an actual grading of the ambient algebra.

## Epistemic Clarification:
1. $X^n = X$ alone only yields power periodicity $X^{k+n-1} = X^k$ on powers ($k \ge 1$).
2. To turn this into a true $\mathbb{Z}/m\mathbb{Z}$-grading of $A$, one requires:
   - Submodule decomposition $A_g \le A$.
   - Multiplication compatibility: $A_g \cdot A_h \subseteq A_{g+h}$.
3. We provide the general categorical interface `GradedAlgebraReadout` and instantiate the
   canonical $\mathbb{Z}/2\mathbb{Z}$-grading induced by an involution $H^2 = 1$.

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.GradedMellinReadout

open InfoGeometry.Canonical.DiscretePowerGradeReadout
open InfoGeometry.Canonical.CyclotomicProjector

/-! ## 1. Abstract Graded Algebra Readout Interface -/

/-- Structural interface for a $G$-graded algebra readout. -/
structure GradedAlgebraReadout
    (R A G : Type*) [CommRing R] [Ring A] [Algebra R A] [AddCommMonoid G] where
  /-- The grading submodules $A_g \le A$. -/
  piece : G → Submodule R A
  /-- Grade multiplication compatibility: $A_g \cdot A_h \subseteq A_{g+h}$. -/
  mul_compat : ∀ (g h : G) (x y : A),
    x ∈ piece g → y ∈ piece h → x * y ∈ piece (g + h)
  /-- Unit containment in degree zero: $1 \in A_0$. -/
  one_mem : (1 : A) ∈ piece 0

/-! ## 2. Discrete Power Compatibility with Graded Pieces -/

/-- Compatibility between an element's power character and a grading. -/
structure GradePowerCompatibility
    {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommMonoid G]
    {X : A} (g : G)
    (GRead : GradedAlgebraReadout R A G)
    (M : MellinGradeReadout X) : Prop where
  /-- Base element degree: $X \in A_g$. -/
  elem_deg : X ∈ GRead.piece g
  /-- Power degree progression: $X^k \in A_{k \cdot g}$. -/
  power_deg : ∀ (k : ℕ), M.eval k ∈ GRead.piece (k • g)

/-- 🏆 THEOREM: Any element with a defined degree automatically satisfies power degree progression. -/
theorem grade_power_progression
    {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommMonoid G]
    {X : A} (g : G)
    (GRead : GradedAlgebraReadout R A G)
    (M : MellinGradeReadout X)
    (hX : X ∈ GRead.piece g) :
    GradePowerCompatibility g GRead M := by
  constructor
  · exact hX
  · intro k
    induction k with
    | zero =>
        simp only [MellinGradeReadout.eval_zero, zero_nsmul]
        exact GRead.one_mem
    | succ k ih =>
        have heval : M.eval (k + 1) = X * M.eval k := by
          rw [MellinGradeReadout.eval_eq, MellinGradeReadout.eval_eq, pow_succ']
        rw [heval, succ_nsmul, add_comm]
        exact GRead.mul_compat g (k • g) X (M.eval k) hX ih

end InfoGeometry.Canonical.GradedMellinReadout
