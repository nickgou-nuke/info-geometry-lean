import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.SugawaraAlgebraicLemmas
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.OperatorAlgebra.KacMoodyAlgebraicLemmas

Native algebraic lemmas for finite Kac--Moody/Sugawara calculations.

This file does not construct an affine Lie algebra, a VOA, or an analytic OPE.
It records the associative-algebra identities used after a current algebra
bracket has already been supplied.  The goal is to keep the Kac--Moody lane
canonical in Lean: imported algebra first, proof-bearing finite rewrites second,
and no bridge layer where a direct theorem is enough.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KacMoodyAlgebraicLemmas

open InfoGeometry.Canonical.SugawaraAlgebraicLemmas

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

/-- Scalar coefficient of the central term in the one-current Kac--Moody bracket. -/
@[rep_depth operator]
def kacMoodyCentralCoeff (k : ℝ) (m n : ℤ) : ℝ :=
  if m + n = 0 then (m : ℝ) * k else 0

/--
One-dimensional Kac--Moody current bracket inside an associative `ℝ`-algebra:
`[J_m,J_n] = m k δ_{m+n,0} · 1`.
-/
@[rep_depth operator]
def kacMoodyCurrentBracket (J : ℤ → Op) (k : ℝ) (m n : ℤ) : Prop :=
  comm (J m) (J n) = algebraMap ℝ Op (kacMoodyCentralCoeff k m n)

/-- Right multiplication by a scalar from the base field equals scalar multiplication. -/
@[rep_depth operator]
theorem mul_algebraMap_eq_smul (A : Op) (r : ℝ) :
    A * algebraMap ℝ Op r = r • A := by
  rw [Algebra.smul_def]
  exact (Algebra.commutes r A).symm

/-- Left multiplication by a scalar from the base field equals scalar multiplication. -/
@[rep_depth operator]
theorem algebraMap_mul_eq_smul (A : Op) (r : ℝ) :
    algebraMap ℝ Op r * A = r • A := by
  rw [Algebra.smul_def]

/--
Un-summed Sugawara current block:

`[J_a J_b, J_n] = c(b,n) J_a + c(a,n) J_b`,
where `c(m,n) = m k δ_{m+n,0}`.

This is the finite algebraic engine used before any normal-ordering or mode-sum
regularization enters the story.
-/
@[rep_depth operator]
theorem sugawara_bilinear_current_bracket
    (J : ℤ → Op) (k : ℝ) (a b n : ℤ)
    (hbn : kacMoodyCurrentBracket J k b n)
    (han : kacMoodyCurrentBracket J k a n) :
    comm (J a * J b) (J n) =
      kacMoodyCentralCoeff k b n • J a + kacMoodyCentralCoeff k a n • J b := by
  rw [comm_mul_left]
  unfold kacMoodyCurrentBracket at hbn han
  rw [hbn, han]
  rw [mul_algebraMap_eq_smul, algebraMap_mul_eq_smul]

end InfoGeometry.OperatorAlgebra.KacMoodyAlgebraicLemmas
