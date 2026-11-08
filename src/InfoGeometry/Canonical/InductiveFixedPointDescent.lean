import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Fixed-point descent through an algebraic inductive colimit

`DirectLimitSuperClosureLemmas` is the categorical owner of the algebraic
direct limit used here.  This file adds the symmetry-family statement needed
by the Galois interface: a compatible endomorphism at every finite stage
induces an endomorphism of the colimit, and every stagewise fixed compatible
representative remains fixed there, simultaneously for all symmetry labels.

This is deliberately an algebraic theorem.  It does not introduce a
profinite topology or pretend that an inverse-limit group has already been
constructed.  Such a topological Galois owner would require an actual family
of finite quotient groups and restriction maps.
-/

noncomputable section

namespace InfoGeometry.Canonical.InductiveFixedPointDescent

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]

theorem directLimit_family_fixed_of_stagewise
    (G : Type*)
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (θ : G → ∀ n : Nat, Stage n →+* Stage n)
    (X : ∀ n : Nat, Stage n)
    (hθ : ∀ (g : G) (n : Nat) (x : Stage n),
      θ g (n + 1) (bond n x) = bond n (θ g n x))
    (h0 : ∀ g : G, θ g 0 (X 0) = X 0)
    (hX : ∀ n : Nat, bond n (X n) = X (n + 1)) :
    ∀ (g : G) (n : Nat),
      directLimitEndomorphism bond (θ g) (hθ g)
        (directLimitOf bond n (X n)) = directLimitOf bond n (X n) := by
  intro g n
  exact directLimitEndomorphism_fixed_all bond (θ g) X (hθ g) (h0 g) hX n

end InfoGeometry.Canonical.InductiveFixedPointDescent
