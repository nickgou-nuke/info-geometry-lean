import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.SugawaraAlgebraicLemmas
import InfoGeometry.Meta.Architecture

/-!
# Associative-Algebra Identities for Un-Summed Sugawara Current Blocks

This module proves the associative $\mathbb{R}$-algebra identity
$[J_a J_b, J_n] = c(b, n)\,J_a + c(a, n)\,J_b$ for currents whose pairwise
commutators lie in the central scalar subalgebra `algebraMap ℝ Op`.

## 1. Real Math in This File
- `kacMoodyCentralCoeff`, `kacMoodyCentralElement`
- `mul_algebraMap_eq_smul`, `algebraMap_mul_eq_smul`
- `sugawara_bilinear_current_bracket`

## 2. Meaningful Mathematical Results Used
- `InfoGeometry.Canonical.SugawaraAlgebraicLemmas` (`comm`, `comm_mul_left`)
- `Algebra.smul_def`, `Algebra.commutes`

## 3. Excluded Wrapper Patterns
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KacMoodyAlgebraicLemmas

open InfoGeometry.Canonical.SugawaraAlgebraicLemmas

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

/-- Scalar coefficient $m k\,\delta_{m+n,0}$ of the central term in the one-current
Kac–Moody bracket. -/
@[rep_depth operator]
def kacMoodyCentralCoeff (k : ℝ) (m n : ℤ) : ℝ :=
  if m + n = 0 then (m :  ℝ) * k else 0

/-- Central algebra element `algebraMap ℝ Op (kacMoodyCentralCoeff k m n)` inside `Op`. -/
@[rep_depth operator]
def kacMoodyCentralElement (k : ℝ) (m n : ℤ) : Op :=
  algebraMap ℝ Op (kacMoodyCentralCoeff k m n)

/-- Right multiplication by an embedded real scalar equals scalar multiplication. -/
@[rep_depth operator]
theorem mul_algebraMap_eq_smul (A : Op) (r : ℝ) :
    A * algebraMap ℝ Op r = r • A := by
  rw [Algebra.smul_def]
  exact (Algebra.commutes r A).symm

/-- Left multiplication by an embedded real scalar equals scalar multiplication. -/
@[rep_depth operator]
theorem algebraMap_mul_eq_smul (A : Op) (r : ℝ) :
    algebraMap ℝ Op r * A = r • A := by
  rw [Algebra.smul_def]

/-- Un-summed Sugawara bilinear current commutator identity:
if $[J_b, J_n]$ and $[J_a, J_n]$ equal the central scalar elements
`kacMoodyCentralElement k b n` and `kacMoodyCentralElement k a n`, then
`comm (J a * J b) (J n) = kacMoodyCentralCoeff k b n • J a + kacMoodyCentralCoeff k a n • J b`. -/
@[rep_depth operator]
theorem sugawara_bilinear_current_bracket
    (J : ℤ → Op) (k : ℝ) (a b n : ℤ)
    (hbn : comm (J b) (J n) = kacMoodyCentralElement (Op := Op) k b n)
    (han : comm (J a) (J n) = kacMoodyCentralElement (Op := Op) k a n) :
    comm (J a * J b) (J n) =
      kacMoodyCentralCoeff k b n • J a + kacMoodyCentralCoeff k a n • J b := by
  rw [comm_mul_left, hbn, han]
  unfold kacMoodyCentralElement
  rw [mul_algebraMap_eq_smul, algebraMap_mul_eq_smul]

end InfoGeometry.OperatorAlgebra.KacMoodyAlgebraicLemmas
