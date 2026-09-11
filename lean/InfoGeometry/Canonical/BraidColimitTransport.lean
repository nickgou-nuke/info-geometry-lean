import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses

open InfoGeometry.Algebra.CuntzFibonacciFiveHypotheses
open CuntzFibonacciBraidInclusion

noncomputable section

namespace InfoGeometry.Canonical.BraidColimitTransport

/-!
# Braid Transport Across $A_\infty$ Tensor Colimits

This module proves the algebraic stability of non-abelian Yang-Baxter braid relations
$U V U = V U V$ under inductive $A_\infty$ colimit maps across tensor towers.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.GoldenMeanShift
open InfoGeometry.Canonical.YangBaxterProof

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [CommRing 𝕜]
variable (A : ℕ → Type*)
variable [∀ n, NonUnitalNonAssocRing (A n)] [∀ n, Module 𝕜 (A n)]
variable [∀ n, IsScalarTower 𝕜 (A n) (A n)] [∀ n, SMulCommClass 𝕜 (A n) (A n)]
variable (iota : ∀ n, A n →ₗ[𝕜] A (n + 1))
variable (iota_mul : ∀ (n : ℕ) (x y : A n), iota n (x * y) = iota n x * iota n y)

include iota_mul

/-- An element $x \in A_n$ satisfies the Artin Yang-Baxter braid relation with $y \in A_n$. -/
def IsBraidPair (n : ℕ) (x y : A n) : Prop :=
  x * y * x = y * x * y

/-- The inductive sequence preserves multiplication at every stage $m$. -/
theorem iota_seq_mul (n : ℕ) (x y : A n) : ∀ m : ℕ,
    iota_seq A iota n m (x * y) = iota_seq A iota n m x * iota_seq A iota n m y
| 0 => rfl
| m + 1 => by
    change iota (n + m) (iota_seq A iota n m (x * y)) =
      iota (n + m) (iota_seq A iota n m x) * iota (n + m) (iota_seq A iota n m y)
    rw [iota_seq_mul n x y m, iota_mul]

/-- **Theorem: Inductive Braid Stability**
    If $(U, V)$ form an Artin braid pair at stage $n$, their images under the $m$-step
    colimit map $\iota_{n \to n+m}(U), \iota_{n \to n+m}(V)$ form a braid pair at stage $n+m$. -/
theorem braid_pair_survives_colimit (n : ℕ) (U V : A n) (hUV : IsBraidPair A n U V) (m : ℕ) :
    IsBraidPair A (n + m) (iota_seq A iota n m U) (iota_seq A iota n m V) := by
  dsimp [IsBraidPair] at hUV ⊢
  have h_left : iota_seq A iota n m (U * V * U) =
      iota_seq A iota n m U * iota_seq A iota n m V * iota_seq A iota n m U := by
    rw [iota_seq_mul A iota iota_mul n (U * V) U m, iota_seq_mul A iota iota_mul n U V m]
  have h_right : iota_seq A iota n m (V * U * V) =
      iota_seq A iota n m V * iota_seq A iota n m U * iota_seq A iota n m V := by
    rw [iota_seq_mul A iota iota_mul n (V * U) V m, iota_seq_mul A iota iota_mul n V U m]
  rw [← h_left, ← h_right, hUV]

omit iota_mul

/-- **Theorem: Cuntz-Fibonacci Braid Pair Transport**
    The Fibonacci braid representation generators $U, V \in \mathcal{O}_2$ satisfy `IsBraidPair`. -/
theorem fibonacci_braid_is_braid_pair :
    IsBraidPair (fun _ => CuntzAlg 2) 0
      (fibonacciBraidCuntzRepresentation YangBaxterProof.R)
      (fibonacciBraidCuntzRepresentation YangBaxterProof.B) := by
  dsimp [IsBraidPair]
  exact hypothesis4_yang_baxter_relation

end InfoGeometry.Canonical.BraidColimitTransport
