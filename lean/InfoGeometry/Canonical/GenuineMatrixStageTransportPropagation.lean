import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Propagation of a finite-stage transport witness

The BitWord and `Fin (2^n)` presentations use different index equivalences.
Consequently their one-step identification is an explicit transport datum,
not a definitional equality.  This file records the reusable induction which
propagates such a datum to arbitrary stage jumps.
-/

namespace InfoGeometry.Canonical.GenuineMatrixStageTransportPropagation

variable {S T : ℕ → Type*}

/-! The proposition is deliberately pointwise: it avoids imposing algebraic
structure on carriers that is irrelevant to the propagation argument. -/
theorem map_iterate_transport
    (bondS : ∀ n, S n → S (n + 1))
    (bondT : ∀ n, T n → T (n + 1))
    (transport : ∀ n, S n → T n)
    (hstep : ∀ n x,
      transport (n + 1) (bondS n x) = bondT n (transport n x))
    (mapS : ∀ {m n : ℕ}, m ≤ n → S m → S n)
    (mapT : ∀ {m n : ℕ}, m ≤ n → T m → T n)
    (mapS_refl : ∀ n x, mapS (le_refl n) x = x)
    (mapT_refl : ∀ n x, mapT (le_refl n) x = x)
    (mapS_step : ∀ {m n : ℕ} (h : m ≤ n) (x : S m),
      mapS (Nat.le.step h) x = bondS n (mapS h x))
    (mapT_step : ∀ {m n : ℕ} (h : m ≤ n) (x : T m),
      mapT (Nat.le.step h) x = bondT n (mapT h x))
    {m n : ℕ} (h : m ≤ n) (x : S m) :
    transport n (mapS h x) = mapT h (transport m x) := by
  induction h with
  | refl =>
      rw [mapS_refl, mapT_refl]
  | @step n h ih =>
      rw [mapS_step h, hstep, ih, mapT_step]

end InfoGeometry.Canonical.GenuineMatrixStageTransportPropagation
