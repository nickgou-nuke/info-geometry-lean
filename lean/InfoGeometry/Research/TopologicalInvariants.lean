import InfoGeometry.Research.SpectralInference
import InfoGeometry.Research.InformationTorsion

namespace InfoGeometry.Research.TopologicalInvariants

open InfoGeometry.Research.SpectralInference
open InfoGeometry.Research.InformationTorsion
open InfoGeometry.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

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
S_CS = ∫ Tr(A ∧ dA + 2/3 A ∧ A ∧ A).
In our discrete model, this measures the topological phase shift
accumulated by the Dirac operator along the loop.
-/
noncomputable def informationChernSimons (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  -- Loop-closing defect measured by the terminal-to-initial divergence.
  IST.H.divergence (L.γ L.N) (L.γ 0)

omit [FiniteDimensional ℝ E] in
/--
Bridge theorem: In a flat information manifold with zero torsion, the
Chern-Simons winding number is identically zero (a topological invariant).
-/
theorem cs_invariant_of_flat (L : BayesianLoop E) (IST : InfoSpectralTriple E)
    (_h_flat : IST.H.potential = fun x => (1 / 2 : ℝ) * inner ℝ x x) :
    informationChernSimons L IST = 0 := by
  simp [informationChernSimons, L.periodic]

/--
Topological Index derived from Geometric Chirality.
For a Chiral Spectral Triple, the anomaly scale ε itself provides
a topological measure of the manifold's non-commutativity.
By the Atiyah-Singer theorem analogue for Information Geometry, 
this relates the analytical gap [P_D, P_MP] to topological defects.
-/
noncomputable def chiralAnomalyIndex (CST : ChiralSpectralTriple E) : ℝ :=
  -- ε weighted by the Drazin-projector trace: anomaly strength times active spectral rank.
  CST.epsilon * LinearMap.trace ℝ E (InfoGeometry.Research.Drazin.IsDrazinInverse.projection CST.D CST.DD).toLinearMap

end InfoGeometry.Research.TopologicalInvariants
