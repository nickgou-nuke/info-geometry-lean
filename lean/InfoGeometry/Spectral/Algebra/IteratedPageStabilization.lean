import InfoGeometry.Spectral.Algebra.IteratedDerivedCouple
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Spectral.Algebra.PageStabilization

/-!
# Stabilization inside the iterated exact-couple tower

This module applies the one-step homology calculation to the actual iterated
stage tower.  It is the native Lean 4 analogue of the local stabilization
equivalence used in the convergence theorem for bounded exact couples.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}

/-- If the two differentials adjacent to `p` vanish on stage `n`, the
successor page at `p` is linearly equivalent to the current page. -/
noncomputable def iteratedPageSuccEquivOfAdjacentDifferentialsZero
    (S : Stage R I) (n : ℕ) (p : I)
    (hIncoming :
      (iteratedStage S n).couple.differential
        ((iteratedStage S n).couple.differentialDegree.symm p) = 0)
    (hOutgoing :
      (iteratedStage S n).couple.differential
        ((iteratedStage S n).couple.differentialDegree
          ((iteratedStage S n).couple.differentialDegree.symm p)) = 0) :
    (page S (n + 1) p : Type u) ≃ₗ[R] (page S n p : Type u) :=
  (LinearEquiv.cast
      (R := R)
      (M := fun X : ModuleCat R => (X : Type u))
      (iteratedStage_succ_E S n p)).trans
    ((iteratedStage S n).couple
      |>.directDerivedEEquivOfAdjacentDifferentialsZero
        p hIncoming hOutgoing)

private noncomputable def iteratedPageEquivFrom
    (S : Stage R I) (p : I) (N k : ℕ)
    (hIncoming :
      ∀ n, N ≤ n →
        (iteratedStage S n).couple.differential
          ((iteratedStage S n).couple.differentialDegree.symm p) = 0)
    (hOutgoing :
      ∀ n, N ≤ n →
        (iteratedStage S n).couple.differential
          ((iteratedStage S n).couple.differentialDegree
            ((iteratedStage S n).couple.differentialDegree.symm p)) = 0) :
    (page S (N + k) p : Type u) ≃ₗ[R] (page S N p : Type u) := by
  induction k with
  | zero =>
      simpa using LinearEquiv.refl R (page S N p : Type u)
  | succ k ih =>
      rw [Nat.add_succ]
      exact
        (iteratedPageSuccEquivOfAdjacentDifferentialsZero
          S (N + k) p
          (hIncoming (N + k) (Nat.le_add_right N k))
          (hOutgoing (N + k) (Nat.le_add_right N k))).trans ih

/-- Once the adjacent differentials vanish from page `N` onward, every later
page at `p` is linearly equivalent to page `N`. -/
noncomputable def iteratedPageEquivOfEventuallyAdjacentDifferentialsZero
    (S : Stage R I) (p : I) (N m : ℕ) (hNm : N ≤ m)
    (hIncoming :
      ∀ n, N ≤ n →
        (iteratedStage S n).couple.differential
          ((iteratedStage S n).couple.differentialDegree.symm p) = 0)
    (hOutgoing :
      ∀ n, N ≤ n →
        (iteratedStage S n).couple.differential
          ((iteratedStage S n).couple.differentialDegree
            ((iteratedStage S n).couple.differentialDegree.symm p)) = 0) :
    (page S m p : Type u) ≃ₗ[R] (page S N p : Type u) :=
  (LinearEquiv.cast
      (R := R)
      (M := fun n : ℕ => (page S n p : Type u))
      (Nat.add_sub_of_le hNm).symm).trans
    (iteratedPageEquivFrom S p N (m - N) hIncoming hOutgoing)

/-- Eventual vanishing of the two adjacent page terms implies eventual page
stabilization, without requiring zero-map equalities as input. -/
noncomputable def iteratedPageEquivOfEventuallyAdjacentTermsZero
    (S : Stage R I) (p : I) (N m : ℕ) (hNm : N ≤ m)
    (hIncomingTerm :
      ∀ n, N ≤ n →
        ∀ x : (page S n
          ((iteratedStage S n).couple.differentialDegree.symm p) : Type u),
          x = 0)
    (hOutgoingTerm :
      ∀ n, N ≤ n →
        ∀ x : (page S n
          ((iteratedStage S n).couple.differentialDegree p) : Type u),
          x = 0) :
    (page S m p : Type u) ≃ₗ[R] (page S N p : Type u) :=
  iteratedPageEquivOfEventuallyAdjacentDifferentialsZero
    S p N m hNm
    (fun n hn =>
      (iteratedStage S n).couple
        |>.differential_eq_zero_of_domain_eq_zero
          ((iteratedStage S n).couple.differentialDegree.symm p)
          (hIncomingTerm n hn))
    (fun n hn => by
      rw [(iteratedStage S n).couple.differentialDegree.apply_symm_apply p]
      exact
        (iteratedStage S n).couple
          |>.differential_eq_zero_of_codomain_eq_zero
            p
            (hOutgoingTerm n hn))

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
