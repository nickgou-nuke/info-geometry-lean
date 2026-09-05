import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.H3ZornCarrierBasis
import Mathlib.LinearAlgebra.Trace

/-!
# Operator trace of arbitrary split-Albert derivations

This module advances the trace-zero frontier from explicitly generated inner
Jordan derivations to every bundled derivation of the verified real split
Albert algebra.

The key identity is structural and basis-free.  For a derivation `D`,

`[D, L_x] = L_(D x)`.

Finite-dimensional operator trace kills commutators by cyclicity, hence every
left multiplication operator `L_(D x)` has zero native `LinearMap.trace`.

To turn this into the scalar Albert statement
`linearTrace (D x) = 0`, it remains only to establish the intrinsic carrier
identity

`LinearMap.trace ℝ (H3Zorn ℝ) (jordanLmul x) = 9 * linearTrace x`.

No generation or dimension assumption on the derivation algebra is used here.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn

/-- Every bundled derivation of the split Albert Jordan algebra sends every
vector to an element whose left-multiplication operator has vanishing native
finite-dimensional operator trace. -/
theorem h3Zorn_derivation_jordanLmul_operatorTrace_zero
    (D : NonAssocDerivation.derivations ℝ (H3Zorn ℝ))
    (x : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ)
      (jordanLmul (R := ℝ)
        ((D : Module.End ℝ (H3Zorn ℝ)) x)) = 0 := by
  rw [← h3Zorn_derivation_lie_jordanLmul D x]
  simp only [Ring.lie_def]
  rw [map_sub, LinearMap.trace_mul_comm]
  exact sub_self _

/-- The native `H3ZornF4Derivations` Lie-subalgebra element, bundled as a
Mathlib nonassociative derivation. -/
noncomputable def h3ZornF4DerivationBundled
    (D : H3ZornF4Derivations) :
    NonAssocDerivation.derivations ℝ (H3Zorn ℝ) :=
  ⟨D.1, D.2⟩

@[simp] theorem h3ZornF4DerivationBundled_coe
    (D : H3ZornF4Derivations) :
    (h3ZornF4DerivationBundled D : Module.End ℝ (H3Zorn ℝ)) = D.1 := by
  rfl

/-- Consequently, every element of the full installed split-Albert derivation
Lie subalgebra has zero operator trace after evaluation and left
multiplication. -/
theorem h3ZornF4Derivation_jordanLmul_operatorTrace_zero
    (D : H3ZornF4Derivations)
    (x : H3Zorn ℝ) :
    LinearMap.trace ℝ (H3Zorn ℝ)
      (jordanLmul (R := ℝ) (D.1 x)) = 0 := by
  simpa using
    h3Zorn_derivation_jordanLmul_operatorTrace_zero
      (h3ZornF4DerivationBundled D) x

end InfoGeometry.Algebra
