import Mathlib
import InfoGeometry.Canonical.CoordinateFreeSouriau

/-!
# InfoGeometry.Canonical.SpinorLieDerivative

Coordinate-free spinor-side adapter over the Souriau conformal corridor.

This is a finite witness layer:

* no global spin connection construction is claimed,
* only local bilinear compatibility identities are formalized.
-/

namespace SpinorLieDerivative

open CoordinateFreeSouriau

section

variable {M T S : Type*}

/-- Spinor-side bilinear seed pairing two spinors into a scalar. -/
structure SpinorBilinear where
  pair : S → S → ℝ

/--
Local spinor Lie-action data over a conformal Souriau background.
`lieSpinor` is the action of the beta-generated derivation on spinors.
-/
structure SpinorLieAction
    (g : CoordinateFreeMetric (T := T))
    (C : ConformalSouriau (M := M) (T := T) g)
    (B : SpinorBilinear (S := S)) where
  lieSpinor : M → S → S
  /-- Conformal bilinear response law. -/
  bilinear_conformal :
    ∀ (p : M) (ψ χ : S),
      B.pair (lieSpinor p ψ) χ + B.pair ψ (lieSpinor p χ) = C.sigma p * B.pair ψ χ

/--
Equilibrium specialization on spinors:
if `sigma p = 0`, the spinor bilinear is Lie-invariant at `p`.
-/
theorem bilinear_equilibrium_of_sigma_zero
    (g : CoordinateFreeMetric (T := T))
    (C : ConformalSouriau (M := M) (T := T) g)
    (B : SpinorBilinear (S := S))
    (A : SpinorLieAction (M := M) (T := T) (S := S) g C B)
    (p : M)
    (hs : C.sigma p = 0)
    (ψ χ : S) :
    B.pair (A.lieSpinor p ψ) χ + B.pair ψ (A.lieSpinor p χ) = 0 := by
  rw [A.bilinear_conformal p ψ χ, hs]
  ring

/--
Global equilibrium specialization:
if `sigma = 0` pointwise, spinor bilinear is Lie-invariant everywhere.
-/
theorem bilinear_equilibrium_global
    (g : CoordinateFreeMetric (T := T))
    (C : ConformalSouriau (M := M) (T := T) g)
    (B : SpinorBilinear (S := S))
    (A : SpinorLieAction (M := M) (T := T) (S := S) g C B)
    (hs : ∀ p : M, C.sigma p = 0) :
    ∀ p : M, ∀ ψ χ : S,
      B.pair (A.lieSpinor p ψ) χ + B.pair ψ (A.lieSpinor p χ) = 0 := by
  intro p ψ χ
  exact bilinear_equilibrium_of_sigma_zero
    (g := g) (C := C) (B := B) (A := A) (p := p) (hs := hs p) (ψ := ψ) (χ := χ)

/--
Metric-side equilibrium witnesses imply spinor-side global Lie-bilinear
invariance through the conformal Souriau bridge.
-/
theorem bilinear_equilibrium_from_metric_equilibrium
    (g : CoordinateFreeMetric (T := T))
    (C : ConformalSouriau (M := M) (T := T) g)
    (B : SpinorBilinear (S := S))
    (A : SpinorLieAction (M := M) (T := T) (S := S) g C B)
    (hEq : ∀ p : M, ∃ X Y : T,
      g.inner X Y ≠ 0 ∧
      (g.inner (C.bracket p X) Y + g.inner X (C.bracket p Y) = 0)) :
    ∀ p : M, ∀ ψ χ : S,
      B.pair (A.lieSpinor p ψ) χ + B.pair ψ (A.lieSpinor p χ) = 0 := by
  have hsigma : ∀ p : M, C.sigma p = 0 :=
    sigma_eq_zero_of_equilibrium_with_nondegenerate_pair
      (g := g) (S := C) hEq
  exact bilinear_equilibrium_global
    (g := g) (C := C) (B := B) (A := A) hsigma

/--
Converse spinor-side extraction:
if at each point there is a nondegenerate spinor test pair and the bilinear
Lie-derivative expression vanishes on that pair, then `sigma = 0` pointwise.
-/
theorem sigma_zero_of_bilinear_equilibrium
    (g : CoordinateFreeMetric (T := T))
    (C : ConformalSouriau (M := M) (T := T) g)
    (B : SpinorBilinear (S := S))
    (A : SpinorLieAction (M := M) (T := T) (S := S) g C B)
    (hEq : ∀ p : M, ∃ ψ χ : S,
      B.pair ψ χ ≠ 0 ∧
      (B.pair (A.lieSpinor p ψ) χ + B.pair ψ (A.lieSpinor p χ) = 0)) :
    ∀ p : M, C.sigma p = 0 := by
  intro p
  rcases hEq p with ⟨ψ, χ, hpair, hLie⟩
  have hconf := A.bilinear_conformal p ψ χ
  have hs : C.sigma p * B.pair ψ χ = 0 := by
    rw [← hconf, hLie]
  exact (mul_eq_zero.mp hs).resolve_right hpair

/--
Two-way spinor equilibrium criterion under nondegenerate spinor witnesses.
-/
theorem sigma_zero_iff_bilinear_equilibrium
    (g : CoordinateFreeMetric (T := T))
    (C : ConformalSouriau (M := M) (T := T) g)
    (B : SpinorBilinear (S := S))
    (A : SpinorLieAction (M := M) (T := T) (S := S) g C B)
    (hpair : ∀ _ : M, ∃ ψ χ : S, B.pair ψ χ ≠ 0) :
    (∀ p : M, C.sigma p = 0) ↔
      (∀ p : M, ∃ ψ χ : S,
        B.pair ψ χ ≠ 0 ∧
        (B.pair (A.lieSpinor p ψ) χ + B.pair ψ (A.lieSpinor p χ) = 0)) := by
  constructor
  · intro hs p
    rcases hpair p with ⟨ψ, χ, hψχ⟩
    refine ⟨ψ, χ, hψχ, ?_⟩
    exact bilinear_equilibrium_of_sigma_zero
      (g := g) (C := C) (B := B) (A := A) (p := p) (hs := hs p) (ψ := ψ) (χ := χ)
  · intro hEq
    exact sigma_zero_of_bilinear_equilibrium
      (g := g) (C := C) (B := B) (A := A) hEq

end

end SpinorLieDerivative
