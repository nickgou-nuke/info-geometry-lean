import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Projective.SplitOctonions.SplitOctonionsLegendre

Concrete algebraic dually-flat metric inversion.

This file proves the metric inversion identity associated with the one-dimensional
diagonal Zorn barrier coordinate:

  η = -1/a,
  g = 1/a²,
  g* = 1/η²,

encoded without division by the equations:

  a * η = -1,
  a² * g = 1,
  η² * g* = 1.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Projective.SplitOctonions.SplitOctonionsLegendre

/--
Dually-flat metric inversion, purely algebraic.

If `η` is the Legendre-dual coordinate to `a`, encoded by `a * η = -1`,
and if `g` and `gStar` are the primal and dual metric entries encoded by

* `a² * g = 1`,
* `η² * gStar = 1`,

then the two metric entries are exact inverses:

`g * gStar = 1`.
-/
theorem zornSlice_metric_inversion
    {R : Type*} [CommRing R]
    (a eta g gStar : R)
    (hLegendre : a * eta = -1)
    (hPrimal : a ^ 2 * g = 1)
    (hDual : eta ^ 2 * gStar = 1) :
    g * gStar = 1 := by
  have hScale : a ^ 2 * eta ^ 2 = 1 := by
    calc
      a ^ 2 * eta ^ 2 = (a * eta) ^ 2 := by ring
      _ = (-1 : R) ^ 2 := by rw [hLegendre]
      _ = 1 := by ring
  have hMetrics : (a ^ 2 * eta ^ 2) * (g * gStar) = 1 := by
    calc
      (a ^ 2 * eta ^ 2) * (g * gStar)
          = (a ^ 2 * g) * (eta ^ 2 * gStar) := by ring
      _ = 1 * 1 := by rw [hPrimal, hDual]
      _ = 1 := by ring
  rw [hScale] at hMetrics
  simpa using hMetrics

/--
Equivalent right-inverse form.

This is separate only because some downstream matrix-style code rewrites
inverse metric entries in the opposite order.
-/
theorem zornSlice_metric_inversion_right
    {R : Type*} [CommRing R]
    (a eta g gStar : R)
    (hLegendre : a * eta = -1)
    (hPrimal : a ^ 2 * g = 1)
    (hDual : eta ^ 2 * gStar = 1) :
    gStar * g = 1 := by
  rw [mul_comm]
  exact zornSlice_metric_inversion a eta g gStar hLegendre hPrimal hDual

end InfoGeometry.Projective.SplitOctonions.SplitOctonionsLegendre
