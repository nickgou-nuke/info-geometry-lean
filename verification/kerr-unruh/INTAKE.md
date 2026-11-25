# Intake provenance — 2026-11-25

The source is the user's chat message accompanying the GitHub connector. This
record preserves the mathematical claims and requested module inventory;
the original escaped Markdown/HTML and Lean proposal remain in that message.
The entries below describe the intake, not the verification result.

## Submitted mathematical claims

- A loxodromic generator `Λ(κ, Ω_H) = κ K₃ + Ω_H J₃`, with `κ > 0` and
  `β_H = 2π/κ`, is paired with a mode to give `x = β_H(E - Ω_H m_z)`.
- Creation `c = [[0,1],[0,0]]`, annihilation `a = [[0,0],[1,0]]`,
  number `N = c a`, and hole `Ñ = a c` satisfy the two-state CAR.
- The submitted unnormalized Gibbs matrix is `exp(-x) N + Ñ`, with trace
  `1+exp(-x)` and normalized number expectation `1/(1+exp x)`.
- The three proposed named regimes are “Exterior Normal Sector”,
  “Superradiant Fermi Horizon Center”, and
  “Interior / Ergosphere Superradiant Sector”. The scalar claims are,
  respectively, occupation below one half, equal to one half, and above
  one half when `E-Ω_H*m_z` is positive, zero, and negative.
- At the central threshold the claimed susceptibility is `1/4` and entropy
  is `log 2`; these were stated in prose but absent from the submitted Lean.
- Sign reversal of inverse temperature or both mode labels was called
  “Twin Thermal Wave / CPT Particle–Hole Duality”.
- The submitted six-by-six Lorentz Poisson matrix annihilates every
  `(0,0,b,0,0,a)` at a longitudinal state `(0,0,J₃,0,0,K₃)`.
- The interpretation identifies the Lorentz kernel with `P₀` and with the
  half-occupation condition. The contract and formal counterexample explain
  why the latter identification does not follow.
- The input claimed a “Complete Native Mathlib4 Formalization” with
  “0 sorry”, using `Fin.sum_univ_six` and `mul_neg_iff_of_pos_left`. Those
  names were not found in the pinned Mathlib source; compilation remains a
  separate obligation from the absence of a textual placeholder.

## Submitted umbrella inventory

The heading said “All 18 Modules”; the supplied list has 21 imports:

```lean
import InfoGeometryUnification.SouriauNeebMetriplecticFoliation
import InfoGeometryUnification.ZornCl44TrialityAndG22
import InfoGeometryUnification.TrialitySymplecticGroupoidFull
import InfoGeometryUnification.SplitOctonionCl44Complete
import InfoGeometryUnification.KirillovWeylCharacterAndGaussLaw
import InfoGeometryUnification.MusicalLegendreNaturalGradientBridge
import InfoGeometryUnification.WeinsteinGroupoidTargetPushforwardAndGENERIC
import InfoGeometryUnification.PoissonAntiPoissonCliffordSynthesis
import InfoGeometryUnification.CourantDrinfeldDiracCapstone
import InfoGeometryUnification.TwistorPlabicSpinNetCPTBridge
import InfoGeometryUnification.PlabicDiracCourantUnification
import InfoGeometryUnification.KleinSouriauCasimirFixedPointBridge
import InfoGeometryUnification.MetriplecticSchurPlabicBridge
import InfoGeometryUnification.PoincarePauliLubanskiCasimirBridge
import InfoGeometryUnification.HorizonThreeProjectorTomitaBridge
import InfoGeometryUnification.LoxodromicTwinThermalWaves
import InfoGeometryUnification.FermionicMassieuPauliHorizonBridge
import InfoGeometryUnification.KerrUnruhFermionicHorizonBridge
import InfoGeometryUnification.TransformerAttentionLoxodromicRoPEBridge
import InfoGeometryUnification.WilsonModelApplicationBridge
import InfoGeometryUnification.WilsonHolonomyCoadjointGroupoidBridge
```

The inspected repository uses the `InfoGeometry` library. The literal
`InfoGeometryUnification.*` module paths are not substituted for its existing
owners and are not presented as a verified package inventory.
