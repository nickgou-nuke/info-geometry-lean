import InfoGeometry.Spectral.Algebra.DerivedDStabilization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Spectral.Algebra.IteratedDerivedCouple

/-!
# Stabilization of the `D` family in the iterated exact-couple tower

This is the direct Lean 4 analogue of the `Dstable` component of a bounded
exact couple.  It uses ordinary surjectivity hypotheses and returns actual
linear equivalences between stages; no convergence or evidence record is
introduced.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}

/-- The next `D` family is the incoming-image family of the current stage. -/
theorem iteratedStage_succ_D
    (S : Stage R I) (n : ℕ) (p : I) :
    (iteratedStage S (n + 1)).D p =
      ModuleCat.of R
        ((iteratedStage S n).couple.DirectDerivedD p) := by
  rw [iteratedStage_succ]
  rcases iteratedStage S n with
    ⟨D, E, iDeg, jDeg, kDeg, C⟩
  rfl

/-- If the incoming `i` map at stage `n` is surjective, the successor `D`
term is linearly equivalent to the current `D` term. -/
noncomputable def iteratedDSuccEquivOfIncomingISurjective
    (S : Stage R I) (n : ℕ) (p : I)
    (h :
      Function.Surjective
        ((iteratedStage S n).couple.incomingI p)) :
    ((iteratedStage S (n + 1)).D p : Type u) ≃ₗ[R]
      ((iteratedStage S n).D p : Type u) :=
  (LinearEquiv.cast
      (R := R)
      (M := fun X : ModuleCat R => (X : Type u))
      (iteratedStage_succ_D S n p)).trans
    ((iteratedStage S n).couple
      |>.directDerivedDEquivOfIncomingISurjective p h)

private noncomputable def iteratedDEquivFrom
    (S : Stage R I) (p : I) (N k : ℕ)
    (hSurjective :
      ∀ n, N ≤ n →
        Function.Surjective
          ((iteratedStage S n).couple.incomingI p)) :
    ((iteratedStage S (N + k)).D p : Type u) ≃ₗ[R]
      ((iteratedStage S N).D p : Type u) := by
  induction k with
  | zero =>
      simpa using
        LinearEquiv.refl R ((iteratedStage S N).D p : Type u)
  | succ k ih =>
      rw [Nat.add_succ]
      exact
        (iteratedDSuccEquivOfIncomingISurjective
          S (N + k) p
          (hSurjective (N + k) (Nat.le_add_right N k))).trans ih

/-- Eventual surjectivity of the incoming `i` maps makes every later `D` term
linearly equivalent to the first stable `D` term. -/
noncomputable def iteratedDEquivOfEventuallyIncomingISurjective
    (S : Stage R I) (p : I) (N m : ℕ) (hNm : N ≤ m)
    (hSurjective :
      ∀ n, N ≤ n →
        Function.Surjective
          ((iteratedStage S n).couple.incomingI p)) :
    ((iteratedStage S m).D p : Type u) ≃ₗ[R]
      ((iteratedStage S N).D p : Type u) :=
  (LinearEquiv.cast
      (R := R)
      (M := fun n : ℕ => ((iteratedStage S n).D p : Type u))
      (Nat.add_sub_of_le hNm).symm).trans
    (iteratedDEquivFrom S p N (m - N) hSurjective)

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
