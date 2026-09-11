import InfoGeometry.Spectral.Algebra.ConvergenceCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Stable pages

This file is the first Route B boundary for convergence.  It packages the
eventual page equivalences already proved by `IteratedPageStabilization`; it
does not identify a stable page with an associated graded object or with a
colimit.  Those require separate filtration and compatibility data.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}

abbrev stablePage (S : Stage R I) (h : BoundedPageStabilization S) (p : I) : Type u :=
  page S (h.bound p) p

noncomputable def stablePageEquiv
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (m : ℕ)
    (hm : h.bound p ≤ m) :
    (page S m p : Type u) ≃ₗ[R] stablePage S h p :=
  h.equiv p m hm

theorem stablePageEquiv_apply
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (m : ℕ)
    (hm : h.bound p ≤ m) (x : page S m p) :
    stablePageEquiv S h p m hm x = h.equiv p m hm x :=
  rfl

noncomputable def stablePage_equiv_of_eventual_stabilization
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (m : ℕ)
    (hm : h.bound p ≤ m) :
    (page S m p : Type u) ≃ₗ[R] stablePage S h p :=
  stablePageEquiv S h p m hm

/-- Canonical transport between any two pages in the stabilized tail. -/
noncomputable def stablePageTransport
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (m k : ℕ) (hm : h.bound p ≤ m) (hk : h.bound p ≤ k) :
    (page S m p : Type u) ≃ₗ[R] (page S k p : Type u) :=
  (stablePageEquiv S h p m hm).trans (stablePageEquiv S h p k hk).symm

theorem stablePageTransport_apply
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (m k : ℕ) (hm : h.bound p ≤ m) (hk : h.bound p ≤ k)
    (x : page S m p) :
    stablePageTransport S h p m k hm hk x =
      (stablePageEquiv S h p k hk).symm
        (stablePageEquiv S h p m hm x) :=
  rfl

@[simp]
theorem stablePageTransport_self
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (m : ℕ) (hm : h.bound p ≤ m) :
    stablePageTransport S h p m m hm hm = LinearEquiv.refl R (page S m p) := by
  apply LinearEquiv.ext
  intro x
  simp [stablePageTransport]

theorem stablePageTransport_comp
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (m k l : ℕ) (hm : h.bound p ≤ m) (hk : h.bound p ≤ k)
    (hl : h.bound p ≤ l) :
    (stablePageTransport S h p m k hm hk).trans
        (stablePageTransport S h p k l hk hl) =
      stablePageTransport S h p m l hm hl := by
  apply LinearEquiv.ext
  intro x
  simp [stablePageTransport]

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
