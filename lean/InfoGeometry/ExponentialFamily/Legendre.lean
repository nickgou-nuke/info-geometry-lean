import InfoGeometry.ExponentialFamily.Analytic.LogSumExp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Convex.Legendre

/-!
# Exponential Family to Legendre Potential

Bridge from finite log-sum-exp potentials to the 1D Legendre potential
package, given a strict-convexity witness.
-/

namespace InfoGeometry.ExponentialFamily

open InfoGeometry.Analytic
open InfoGeometry.Convex

/-- Build a `LegendrePotential` from a finite log-sum-exp potential. -/
noncomputable def logSumExpLegendre
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hstrict : StrictConvexOn ℝ Set.univ (logSumExp w a)) :
    LegendrePotential :=
  { f := logSumExp w a
    smooth := logSumExp_contDiff w a hw
    strict_convex := hstrict }

@[simp] lemma logSumExpLegendre_f
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hstrict : StrictConvexOn ℝ Set.univ (logSumExp w a)) :
    (logSumExpLegendre w a hw hstrict).f = logSumExp w a := rfl

@[simp] lemma logSumExpLegendre_smooth
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hstrict : StrictConvexOn ℝ Set.univ (logSumExp w a)) :
    (logSumExpLegendre w a hw hstrict).smooth = logSumExp_contDiff w a hw := rfl

@[simp] lemma logSumExpLegendre_strictConvex
    {ι : Type _} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (a : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hstrict : StrictConvexOn ℝ Set.univ (logSumExp w a)) :
    (logSumExpLegendre w a hw hstrict).strict_convex = hstrict := rfl

end InfoGeometry.ExponentialFamily
