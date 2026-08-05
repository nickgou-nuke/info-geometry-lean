import Mathlib.Tactic
import Mathlib.RingTheory.Derivation.Basic

/-!
# InfoGeometry.Canonical.CoordinateFreeSouriau

Coordinate-free Souriau beta-field seed.

This file keeps the formalism index-free and witness-driven:

* beta is a tangent-bundle section (`M → T`),
* metric constraints are stated by bilinear pairings and bracket actions,
* out-of-equilibrium is encoded by a conformal anomaly scalar `sigma`.
-/

namespace InfoGeometry.Canonical.CoordinateFreeSouriau

section Core

variable {M T : Type*}

/-- Coordinate-free derivation on a commutative scalar algebra. -/
abbrev ScalarDerivation (F : Type*) [CommRing F] :=
  Derivation ℤ F F

namespace ScalarDerivation

variable {F : Type*} [CommRing F]

@[simp] theorem map_add (D : ScalarDerivation F) (a b : F) :
    D (a + b) = D a + D b := D.toLinearMap.map_add a b

@[simp] theorem map_mul (D : ScalarDerivation F) (a b : F) :
    D (a * b) = a * D b + b * D a := by
  simpa [smul_eq_mul] using D.leibniz' a b

end ScalarDerivation

/-- Coordinate-free metric seed on a model tangent fiber `T`. -/
abbrev CoordinateFreeMetric := T → T → ℝ

namespace CoordinateFreeMetric

abbrev inner (g : CoordinateFreeMetric (T := T)) : T → T → ℝ := g

end CoordinateFreeMetric

/--
Coordinate-free Souriau data:
`beta` is the generating section, `bracket` is the local commutator action,
and the Killing-style equilibrium condition is index-free.
-/
structure SouriauData (g : CoordinateFreeMetric (T := T)) where
  beta : M → T
  bracket : M → T → T
  localInvTemperature : M → ℝ
  temperature_def : ∀ p : M, localInvTemperature p = Real.sqrt (g.inner (beta p) (beta p))
  lie_derivative_metric_zero :
    ∀ (p : M) (X Y : T),
      g.inner (bracket p X) Y + g.inner X (bracket p Y) = 0

/-- Readback of the coordinate-free inverse temperature law. -/
theorem localInvTemperature_eq_sqrt_norm
    (g : CoordinateFreeMetric (T := T))
    (S : SouriauData (M := M) (T := T) g)
    (p : M) :
    S.localInvTemperature p = Real.sqrt (g.inner (S.beta p) (S.beta p)) :=
  S.temperature_def p

/-- Readback of the equilibrium Killing-style cancellation law. -/
theorem lie_derivative_metric_zero_readback
    (g : CoordinateFreeMetric (T := T))
    (S : SouriauData (M := M) (T := T) g)
    (p : M) (X Y : T) :
    g.inner (S.bracket p X) Y + g.inner X (S.bracket p Y) = 0 :=
  S.lie_derivative_metric_zero p X Y

end Core

section Conformal

variable {M T : Type*}

/--
Out-of-equilibrium conformal extension:
`sigma` measures failure of strict metric invariance via `L_β g = sigma * g`.
-/
structure ConformalSouriau
    (g : CoordinateFreeMetric (T := T))
    extends SouriauData (M := M) (T := T) g where
  sigma : M → ℝ
  lie_derivative_metric_conformal :
    ∀ (p : M) (X Y : T),
      g.inner (bracket p X) Y + g.inner X (bracket p Y) = sigma p * g.inner X Y

/-- Equilibrium specialization of conformal Souriau data (`sigma = 0`). -/
theorem conformal_reduces_to_equilibrium
    (g : CoordinateFreeMetric (T := T))
    (S : ConformalSouriau (M := M) (T := T) g)
    (hsigma : ∀ p : M, S.sigma p = 0)
    (p : M) (X Y : T) :
    g.inner (S.bracket p X) Y + g.inner X (S.bracket p Y) = 0 := by
  rw [S.lie_derivative_metric_conformal p X Y, hsigma p]
  ring

/--
Conformal anomaly scalar is uniquely read back from a nondegenerate test pair.
This is a local algebraic extraction lemma.
-/
theorem sigma_readback_of_nonzero_metric
    (g : CoordinateFreeMetric (T := T))
    (S : ConformalSouriau (M := M) (T := T) g)
    (p : M) (X Y : T)
    (hXY : g.inner X Y ≠ 0) :
    S.sigma p
      = (g.inner (S.bracket p X) Y + g.inner X (S.bracket p Y)) / (g.inner X Y) := by
  have h := S.lie_derivative_metric_conformal p X Y
  apply (eq_div_iff hXY).2
  simpa [mul_comm] using h.symm

/--
At a fixed point/pair `(p, X, Y)`, the conformal anomaly is equivalent to
strict equilibrium whenever `g.inner X Y ≠ 0`.
-/
theorem sigma_zero_iff_equilibrium_at_pair
    (g : CoordinateFreeMetric (T := T))
    (S : ConformalSouriau (M := M) (T := T) g)
    (p : M) (X Y : T)
    (hXY : g.inner X Y ≠ 0) :
    S.sigma p = 0 ↔
      g.inner (S.bracket p X) Y + g.inner X (S.bracket p Y) = 0 := by
  constructor
  · intro hs
    rw [S.lie_derivative_metric_conformal p X Y, hs]
    ring
  · intro hLie
    have hsigma :=
      sigma_readback_of_nonzero_metric (g := g) (S := S) (p := p) (X := X) (Y := Y) hXY
    rw [hsigma, hLie]
    simp

/--
Global closure theorem (witnessed nondegeneracy):
if every point admits a test pair with nonzero metric pairing and the
Lie-derivative expression vanishes on that pair, then the conformal anomaly
scalar vanishes pointwise.
-/
theorem sigma_eq_zero_of_equilibrium_with_nondegenerate_pair
    (g : CoordinateFreeMetric (T := T))
    (S : ConformalSouriau (M := M) (T := T) g)
    (hEq : ∀ p : M, ∃ X Y : T,
      g.inner X Y ≠ 0 ∧
      (g.inner (S.bracket p X) Y + g.inner X (S.bracket p Y) = 0)) :
    ∀ p : M, S.sigma p = 0 := by
  intro p
  rcases hEq p with ⟨X, Y, hXY, hLie⟩
  have hs_pair :
      S.sigma p = 0 := (sigma_zero_iff_equilibrium_at_pair
        (g := g) (S := S) (p := p) (X := X) (Y := Y) hXY).2 hLie
  exact hs_pair

/--
Global equivalence under nondegenerate local test-pair witnesses:
`sigma = 0` pointwise iff each point admits a nondegenerate pair with vanishing
Lie-derivative metric expression.
-/
theorem sigma_zero_iff_exists_equilibrium_pair
    (g : CoordinateFreeMetric (T := T))
    (S : ConformalSouriau (M := M) (T := T) g)
    (hpair : ∀ _ : M, ∃ X Y : T, g.inner X Y ≠ 0) :
    (∀ p : M, S.sigma p = 0) ↔
      (∀ p : M, ∃ X Y : T,
        g.inner X Y ≠ 0 ∧
        (g.inner (S.bracket p X) Y + g.inner X (S.bracket p Y) = 0)) := by
  constructor
  · intro hs p
    rcases hpair p with ⟨X, Y, hXY⟩
    refine ⟨X, Y, hXY, ?_⟩
    rw [S.lie_derivative_metric_conformal p X Y, hs p]
    ring
  · intro hEq
    exact sigma_eq_zero_of_equilibrium_with_nondegenerate_pair
      (g := g) (S := S) hEq

end Conformal

end InfoGeometry.Canonical.CoordinateFreeSouriau
