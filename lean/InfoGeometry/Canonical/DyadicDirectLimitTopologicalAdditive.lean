import InfoGeometry.Canonical.DyadicDirectLimitTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Continuous additive operations on the transported dyadic carrier

The topology on `DyadicDirectLimit` is transported through the additive
equivalence with `DyadicRational`.  Addition and negation are therefore
continuous, with no completion or analytic limit involved.
-/

theorem continuous_dyadicDirectLimit_add :
    Continuous (fun p : DyadicDirectLimit × DyadicDirectLimit => p.1 + p.2) := by
  apply continuous_induced_rng.mpr
  have h : Continuous
      (fun p : DyadicDirectLimit × DyadicDirectLimit =>
        dyadicDirectLimitEquiv p.1 + dyadicDirectLimitEquiv p.2) :=
    (continuous_dyadicDirectLimitEquiv.comp continuous_fst).add
      (continuous_dyadicDirectLimitEquiv.comp continuous_snd)
  convert h using 1
  funext p
  exact dyadicDirectLimitEquiv_add p.1 p.2

theorem continuous_dyadicDirectLimit_neg :
    Continuous (fun x : DyadicDirectLimit => -x) := by
  apply continuous_induced_rng.mpr
  have h : Continuous
      (fun x : DyadicDirectLimit => -dyadicDirectLimitEquiv x) :=
    continuous_neg.comp continuous_dyadicDirectLimitEquiv
  convert h using 1
  funext x
  exact dyadicDirectLimitEquiv_neg x

theorem continuous_dyadicDirectLimit_zero :
    Continuous (fun _ : Unit => (0 : DyadicDirectLimit)) := by
  exact continuous_const

end InfoGeometry.Canonical
