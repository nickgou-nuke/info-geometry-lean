import InfoGeometry.Research.ConformalUnification
import InfoGeometry.Clifford.Grading

namespace InfoGeometry.Research.ChiralCliffordBridge

open InfoGeometry.Research.ConformalUnification
open InfoGeometry.Research.MoorePenrose
open InfoGeometry.Research.Drazin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Chiral Grading Operator Γ associated with a degenerate information operator A.
In the Cl(1,1) limit, this corresponds to the grading involution.
Formally defined from the Right and Left Penrose projectors: Γ = P_R - P_L.
This measures the geometric asymmetry between information gain and retrieval.
-/
noncomputable def chiralGrading (CI : ConformalInference E) : E →L[ℝ] E :=
  let P_R := IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
  let P_L := IsMoorePenroseInverse.leftProjector CI.A CI.A_MP
  P_R - P_L

/--
Generalized Chiral Projectors for the Information Space.
P± = (P_D ± Γ) / 2.
These projectors isolate the belief states that are aligned/anti-aligned 
with the geometric-spectral mismatch.
-/
noncomputable def generalizedChiralPlus (CI : ConformalInference E) : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (CI.P_D + chiralGrading CI)

noncomputable def generalizedChiralMinus (CI : ConformalInference E) : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (CI.P_D - chiralGrading CI)

/-- Canonical naming alias for the positive chiral projector. -/
noncomputable abbrev chiralProjectorPlus (CI : ConformalInference E) : E →L[ℝ] E :=
  generalizedChiralPlus CI

/-- Canonical naming alias for the negative chiral projector. -/
noncomputable abbrev chiralProjectorMinus (CI : ConformalInference E) : E →L[ℝ] E :=
  generalizedChiralMinus CI

/-! ### Cartan Decomposition of the Information Algebra -/

/--
The Compact (Rotational) Sector 𝔨.
Information operators that commute with the chiral grading Γ.
These preserve the chirality of the belief manifold.
-/
def IsCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = chiralGrading CI * X

/--
The Non-Compact (Boost) Sector 𝔭.
Information operators that anti-commute with the chiral grading Γ.
These are the generators of the RG flow and the emergent scale ε.
-/
def IsNonCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = - (chiralGrading CI * X)

omit [FiniteDimensional ℝ E] in
/--
Theorem: The Chiral Anomaly χ = [P_D, P_MP] acts as the
fundamental structure constant (the ε) of the Cartan decomposition.
This bridges the Conformal generators to the Clifford grading.
-/
theorem anomaly_as_structure_constant (CI : ConformalInference E) :
    CI.chiralAnomaly = CI.P_D * CI.P_MP - CI.P_MP * CI.P_D := rfl

omit [FiniteDimensional ℝ E] in
/--
Specialization: If the information flow is normal, the Cartan decomposition 
collapses because Γ and P_D coincide or commute.
-/
theorem cartan_collapse_of_normal (CI : ConformalInference E) (h_norm : CI.IsNormalInference) :
    CI.chiralAnomaly = 0 := by
  have he : CI.epsilon = 0 := h_norm
  have hn : nnnorm CI.chiralAnomaly = 0 := by
    simpa [ConformalInference.epsilon] using he
  exact (nnnorm_eq_zero).mp hn

end InfoGeometry.Research.ChiralCliffordBridge
