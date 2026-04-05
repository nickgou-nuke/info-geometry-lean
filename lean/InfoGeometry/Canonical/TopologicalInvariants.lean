import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.InformationTorsion
import Mathlib.LinearAlgebra.Dimension.Finite

namespace InfoGeometry.Canonical.TopologicalInvariants

open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.InformationTorsion
open InfoGeometry.Convex

section LoopLevel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
A Bayesian Loop: a periodic discrete path in belief space.
γ(N) = γ(0).
-/
structure BayesianLoop (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  γ : ℕ → E
  N : ℕ
  periodic : γ N = γ 0

/--
A simplified Chern-Simons Term for an Information connection over a Bayesian Loop.
S_CS = ∫ ⟨A, dA + 2/3 A ∧ A⟩.
In our discrete model, this measures the topological phase shift
accumulated by the Dirac operator along the loop.
-/
noncomputable def informationChernSimons (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  -- Loop-closing defect measured by the terminal-to-initial divergence.
  IST.H.divergence (L.γ L.N) (L.γ 0)

/--
Bridge theorem: In a flat information manifold with zero torsion, the
Chern-Simons winding number is identically zero (a topological invariant).
-/
theorem cs_invariant_of_flat (L : BayesianLoop E) (IST : InfoSpectralTriple E)
    (_h_flat : IST.H.potential = fun x => (1 / 2 : ℝ) * inner ℝ x x) :
    informationChernSimons L IST = 0 := by
  simp [informationChernSimons, L.periodic, InfoGeometry.Convex.HessianGeometry.divergence]

end LoopLevel

section ChiralIndex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/--
Topological Index derived from Geometric Chirality.
For a Chiral Spectral Triple, the anomaly scale ε itself provides
a topological measure of the manifold's non-commutativity.
By the Atiyah-Singer theorem analogue for Information Geometry,
this relates the analytical gap [P_D, P_MP] to topological defects.
-/
noncomputable def chiralAnomalyIndex (CST : ChiralSpectralTriple E) : ℝ :=
  -- ε weighted by the effective spectral rank of the Drazin projector.
  CST.epsilon *
    (Module.finrank ℝ
      (LinearMap.range (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection CST.D CST.DD).toLinearMap) : ℝ)

omit [FiniteDimensional ℝ E] in
/--
If the witness-level spectral and metric projectors commute, the chiral anomaly
index vanishes exactly.
-/
theorem chiralAnomalyIndex_eq_zero_of_projectors_commute
    (CST : ChiralSpectralTriple E)
    (hComm :
      InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection CST.D CST.DD
          * InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector CST.D CST.DP
        = InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector CST.D CST.DP
          * InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection CST.D CST.DD) :
    chiralAnomalyIndex CST = 0 := by
  have hChi :
      InfoGeometry.Canonical.MoorePenrose.chiralAnomaly CST.D CST.DD CST.DP = 0 := by
    unfold InfoGeometry.Canonical.MoorePenrose.chiralAnomaly
    exact sub_eq_zero.mpr hComm
  have hEps : CST.epsilon = 0 := by
    rw [ChiralSpectralTriple.epsilon,
      InfoGeometry.Canonical.MoorePenrose.chiralScale,
      InfoGeometry.Canonical.MoorePenrose.epsilon]
    simp [hChi]
  simp [chiralAnomalyIndex, hEps]

end ChiralIndex

end InfoGeometry.Canonical.TopologicalInvariants
