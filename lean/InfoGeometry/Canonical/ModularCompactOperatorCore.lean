import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# InfoGeometry.Canonical.ModularCompactOperatorCore

Finite operator-level atoms for the modular compact coordinate.

This file keeps the infinite-volume/Tomita vocabulary at the level currently
justified by Lean proofs:

* a cross-multiplied bounded-coordinate relation for continuous linear maps;
* the equilibrium consequence `Delta = id → T = 0`;
* the elementary positivity of adjoint-square quadratic forms.

No new carrier structures.
No predual or natural-cone representation theorem.
No Araki relative entropy theorem.
No functional calculus or operator logarithm.
-/

namespace InfoGeometry.Canonical.ModularCompactOperatorCore

/--
Equilibrium core for the bounded modular compact coordinate.

If the cross-multiplied relation

`T * (I + Delta) = I - Delta`

holds in the algebra of continuous linear endomorphisms and `Delta = I`, then
`T = 0`.  This is only the algebraic equilibrium consequence; it does not
assert where `Delta` came from.
-/
theorem compact_operator_equilibrium_core
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Delta T : H →L[ℂ] H)
    (hcompact : T * (ContinuousLinearMap.id ℂ H + Delta) =
      ContinuousLinearMap.id ℂ H - Delta)
    (heq : Delta = ContinuousLinearMap.id ℂ H) :
    T = 0 := by
  rw [heq] at hcompact
  have htwo : ContinuousLinearMap.id ℂ H + ContinuousLinearMap.id ℂ H =
      (2 : ℂ) • ContinuousLinearMap.id ℂ H := by
    ext x
    simp [two_smul]
  have hrhs : ContinuousLinearMap.id ℂ H - ContinuousLinearMap.id ℂ H =
      (0 : H →L[ℂ] H) := by
    ext x
    simp
  rw [htwo, hrhs] at hcompact
  have hscale : T * ((2 : ℂ) • ContinuousLinearMap.id ℂ H) = (2 : ℂ) • T := by
    ext x
    simp
  rw [hscale] at hcompact
  have htwo_ne : (2 : ℂ) ≠ 0 := by
    norm_num
  exact (smul_eq_zero.mp hcompact).resolve_left htwo_ne

/--
Adjoint-square quadratic forms have nonnegative real part.

This is the direct Hilbert-space fact behind positivity tests of the form
`A = B† B`; it is not a natural-cone or normal-state representation theorem.
-/
theorem adjoint_comp_quadratic_re_nonneg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (xi : H) :
    0 ≤ (inner ℂ xi ((B.adjoint.comp B) xi) : ℂ).re := by
  have h := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right B xi
  change 0 ≤ RCLike.re (inner ℂ xi ((B.adjoint.comp B) xi))
  rw [← h]
  positivity

end InfoGeometry.Canonical.ModularCompactOperatorCore
