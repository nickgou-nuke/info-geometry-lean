import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.FenchelConjugation
import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Krein.InvolutiveSelfDualCarrier
import InfoGeometry.OperatorAlgebra.SelfDualChiralConeBoundary
import InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry
import InfoGeometry.Canonical.KleinBottleOrientifold

/-!
# SelfDualWeylKleinBridge

SymPy witness: `tools/sympy/selfdual_weyl_klein_bridge.py`

Connects self-dual cones, Fenchel-Legendre operator duality, root systems,
Weyl symmetry, maximal torus, and Klein bottle symmetry through the shared
V4 / Weyl group action.

## Bridge table

| Concept | SymPy | Lean surface |
|---------|-------|-------------|
| Self-dual cone | K = K* (positive orthant, Lorentz) | `Krein/InvolutiveSelfDualCarrier` |
| Cone boundary | self-dual cone + dual | `OperatorAlgebra/SelfDualChiralConeBoundary` |
| Fenchel-Legendre | f** = f (reflexivity) | `Quantum/FenchelConjugation` |
| Legendre transform | f*(y) = sup_x(⟨x,y⟩-f(x)) | `Geometry/LegendreDuality` |
| Root system A₁×A₁ | Cartan matrix [[2,0],[0,2]] | — |
| Weyl group V4 | r₁² = r₂² = I, r₁r₂ = r₂r₁ | `AsanoKleinFourSymmetry` |
| Maximal torus | Cartan H fixed under V4 | `KleinBottleOrientifold` |
| Klein bottle | T² / V4 quotient | `KleinBottleOrientifold` |

All existing Lean surfaces compile.
-/
