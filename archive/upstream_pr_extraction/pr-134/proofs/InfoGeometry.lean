import Mathlib
import proofs.SplitCliffordAlgebras
import proofs.ProjectiveCuntzToeplitzCARCCR
import proofs.ProjectivePenrosePGA
import proofs.NoncommutativeTilingAlgebra
import proofs.ConvexAlgebraicDuality
import proofs.GoldenCCR
import proofs.FractalHamiltonian
import proofs.BlackHoleHolography
import proofs.GoldenSpectralTriple
import proofs.InformationGeometricCutoff
import proofs.EinsteinThermodynamicBridge
import proofs.UnifiedGaugeField
import proofs.DiracKreinMetriplectic
import proofs.SuperBerezinianKlein
import proofs.GlideSymmetricInvariant
import proofs.CubicJordanPeirceDecomposition
import proofs.MinkowskiBiquaternion
import proofs.DiracFourierMellin
import proofs.PolynomialSymmetryOperators
import InfoGeometry.Canonical.BiquaternionKANnilpotent
import proofs.CptFractalClosure
import proofs.GravitySoldering
import proofs.WallpaperIsometry
import proofs.BraidIdealDescent
import proofs.GohbergKreinIndex
import proofs.ArtinCentralizerMonodromy
import proofs.QCDConfinementISDivergence
-- import EinsteinTKK
-- import LegendreFenchelSpectralGap
-- import ChiralTwinBands
-- import MirrorCoulombEnergyGap
-- import IsospinMixingA35
-- import MirrorInversionA39

/-!
# InfoGeometry: master architecture manifest

This file aggregates Lean modules for the current
information-geometric quantum-gravity architecture.

## Layers

1. **Split Clifford / CPT kinematics**
   `SplitCliffordAlgebras`
2. **Cuntz--Toeplitz / q-CCR corridor**
   `ProjectiveCuntzToeplitzCARCCR`
3. **Projective Penrose/PGA geometry**
   `ProjectivePenrosePGA`
4. **Noncommutative tiling, K₀ trace and gap labels**
   `NoncommutativeTilingAlgebra`
5. **Convex algebraic duality and spectrahedral data**
   `ConvexAlgebraicDuality`
6. **Golden q-CCR thermodynamic parameter**
   `GoldenCCR`
7. **Finite Fibonacci Hamiltonian dynamics**
   `FractalHamiltonian`
8. **Black-hole entropy scalar holography**
   `BlackHoleHolography`
9. **Golden Fock / spectral triple data**
   `GoldenSpectralTriple`
10. **Information-geometric thermodynamic UV cutoff**
   `InformationGeometricCutoff`
11. **Scalar thermodynamic Einstein bridge**
   `EinsteinThermodynamicBridge`
12. **Unified gauge-field / TKK data**
   `UnifiedGaugeField`
13. **Dirac/Krein metriplectic modular bridge**
   `DiracKreinMetriplectic`
14. **Super-Berezinian / Klein-glide finite identities**
   `SuperBerezinianKlein`
15. **Glide-symmetric Z₂ eigensector invariance**
   `GlideSymmetricInvariant`
16. **Canonical Peirce tripotent identities**
   `CubicJordanPeirceDecomposition`
17. **Braid ideal descent / q-cross map**
   `BraidIdealDescent`
18. **Finite Gohberg--Krein / EP winding index**
   `GohbergKreinIndex`
19. **Artin monodromy into the `{I,-I}` TKK/Pin centralizer**
   `ArtinCentralizerMonodromy`, `ArtinMonodromyPin55`
20. **Topological thermodynamic strong force (Itakura-Saito confinement)**
   `QCDConfinementISDivergence`
21. **Emergent Gravity via TKK g_2 Sector**
   `EinsteinTKK`
22. **Legendre-Fenchel Duality and Lie Group Spectral Gap**
   `LegendreFenchelSpectralGap`
23. **Dynamical Chiral Twin Bands and Triality**
   `ChiralTwinBands`
24. **Coulomb Energy Differences as Topological Mass Gaps**
   `MirrorCoulombEnergyGap`
25. **Isospin Mixing in A=35 Mirror Nuclei**
   `IsospinMixingA35`
26. **Topological Inversion in A=39 Mirror Nuclei**
   `MirrorInversionA39`
27. **Restored thesis-cited finite modules**
   `MinkowskiBiquaternion`, `DiracFourierMellin`, `PolynomialSymmetryOperators`
28. **Recovered quarantined finite atoms**
   `BiquaternionKANnilpotent`, `CptFractalClosure`, `GravitySoldering`,
   `WallpaperIsometry`

The analytic C*-algebra, von Neumann algebra, infinite spectral, and physical
classification statements are represented by imported modules.  The
finite algebraic, scalar, and matrix facts are supplied by those modules.
-/

noncomputable section

namespace InfoGeometryMaster

/-- A mathematically rigorous typeclass for strictly positive real numbers,
essential for defining non-degenerate Fisher metrics in information geometry. -/
class IsStrictlyPositive (x : ℝ) : Prop where
  pos : 0 < x

/-- The sum of two strictly positive real numbers is strictly positive. -/
theorem sum_of_strictly_positives (x y : ℝ) [hx : IsStrictlyPositive x] [hy : IsStrictlyPositive y] : IsStrictlyPositive (x + y) :=
  ⟨add_pos hx.pos hy.pos⟩

/-- The product of two strictly positive real numbers is strictly positive. -/
theorem mul_of_strictly_positives (x y : ℝ) [hx : IsStrictlyPositive x] [hy : IsStrictlyPositive y] : IsStrictlyPositive (x * y) :=
  ⟨mul_pos hx.pos hy.pos⟩

/-- Information-geometric Fisher metric coefficient, which must be strictly positive. -/
class FisherMetricCoefficient (g : ℝ) extends IsStrictlyPositive g

theorem fisher_metric_additive (g1 g2 : ℝ) [FisherMetricCoefficient g1] [FisherMetricCoefficient g2] : IsStrictlyPositive (g1 + g2) :=
  sum_of_strictly_positives g1 g2

end InfoGeometryMaster
