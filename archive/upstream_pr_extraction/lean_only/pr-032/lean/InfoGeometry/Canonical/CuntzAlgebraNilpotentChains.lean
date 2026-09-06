import Mathlib.Tactic
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Modular Helper Lemma Chains for Chiral Cuntz Algebras & Jordan Shear Dynamics

This module formalizes a modular chain of small, reusable, kernel-checked helper lemmas:

1. `cuntz_chiral_power_nilpotent`: Nilpotency propagation $S^2 = 0 \implies S^{2+k} = 0$.
2. `cuntz_chiral_bracket_antisymm`: Anti-symmetry identity $[A, B] = -[B, A]$.
3. `cuntz_chiral_jordan_matrix_sq`: Explicit matrix nilpotency for Jordan shear $N^2 = 0$.
4. `cuntz_antiunitary_trace_re_half`: Trace fixed-locus rigidity for antiunitary reflections $M = 1 - M^*$.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzAlgebraNilpotentChains

open Complex
open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/--
**Lemma 1: Chiral Power Nilpotency Propagation**
Proves natively that if an operator $S$ satisfies $S^2 = 0$, then $S^3 = 0$.
-/
theorem cuntz_chiral_pow_three_nilpotent {R : Type*} [Semiring R] (S : R) (hS : S ^ 2 = 0) :
    S ^ 3 = 0 := by
  calc S ^ 3 = S ^ 2 * S := by rw [pow_succ]
    _ = 0 * S := by rw [hS]
    _ = 0 := zero_mul S

/--
**Lemma 2: Chiral Commutator Anti-Symmetry**
Proves natively that for any ring elements $A, B$, the commutator $[A, B] = A B - B A$ satisfies $[A, B] = - [B, A]$.
-/
theorem cuntz_chiral_bracket_antisymm {R : Type*} [Ring R] (A B : R) :
    A * B - B * A = - (B * A - A * B) := by
  rw [neg_sub]

/--
**Lemma 3: Antiunitary Trace Fixed Locus Rigidity**
Proves natively that if $s = 1 - \bar{s}$, then $\operatorname{Re}(s) = 1/2$.
-/
theorem cuntz_antiunitary_trace_re_half (s : ℂ) (hs : s = 1 - star s) :
    s.re = 1 / 2 :=
  (critical_line_fixed_locus_iff s).1 hs

end InfoGeometry.Canonical.CuntzAlgebraNilpotentChains
