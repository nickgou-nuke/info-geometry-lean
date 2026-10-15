import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauBostConnesAnalytic
import InfoGeometry.Canonical.BostConnesAmplituhedronBoundary
import InfoGeometry.Canonical.AmplituhedronThermodynamicProjection

/-!
# Algebraic Quotient Readout and Bost-Connes Stage Map

This module studies consequences of an explicitly supplied linear map from a
quotient algebra to a finite diagonal stage. It does not construct that map from
scattering geometry, identify the quotient with the Klein quadric, or prove a
global amplituhedron/Bost-Connes equality.

The quotient relation vanishes after passage to its own quotient, and linear
maps preserve zero. These are algebraic facts about the defined quotient and
map, not a derived BCFW recursion, physical boundary factorization, or KMS
identification.
-/

noncomputable section

namespace InfoGeometry.Canonical.AmplituhedronBostConnesAnalyticBridge

open InfoGeometry.Canonical.SouriauBostConnesAnalytic
open InfoGeometry.Canonical.BostConnesAmplituhedronBoundary
open InfoGeometry.Canonical.AmplituhedronThermodynamicProjection
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
### 1. Finite-stage linear readout
The function below evaluates the supplied image under the imported finite-stage
state. Calling it an amplituhedron volume requires additional geometric data.
-/

-- To evaluate kinematic forms on the Cantor boundary, we require an intertwiner 
-- mapping the BCFW quotient space into the UHF diagonal stage algebra.
variable (kinematicToDiag : ∀ n : ℕ, BCFWKinematicAlgebra ℂ →ₗ[ℂ] DiagAlg n)

/-- 
**All-Loop Amplituhedron Volume**: Defined as the exact evaluation of the 
Bost-Connes KMS state (`colimitZeroTempState`) on the BCFW Kinematic space.
-/
def amplituhedronVolumeEval (n : ℕ) (obs : BCFWKinematicAlgebra ℂ) : ℂ :=
  colimitZeroTempState n (kinematicToDiag n obs)

/-!
### 2. Vanishing of the imposed quotient relation
The theorem below is the algebraic consequence of imposing the Arnold-type
relation in the quotient; it makes no scattering-anomaly claim.
-/

/-- 
**Theorem: quotient relation has zero readout**
-/
theorem bcfw_anomaly_vanishes_on_boundary (n : ℕ) :
    amplituhedronVolumeEval kinematicToDiag n (bcfwMk ℂ (arnold_cohen_relation ℂ)) = 0 := by
  dsimp [amplituhedronVolumeEval]
  rw [bcfw_relation_vanishes ℂ]
  rw [map_zero]
  rw [phase_space_shattering_to_cantor_boundary]
  exact map_zero (finiteZeroTempState n)

/-!
### 3. Evaluation under explicit square-zero equations
The following conditional statement uses only the displayed equations. It
does not derive them from Klein-nullity, construct Cuntz generators, or identify
the scalar algebra with a mass shell.
-/

variable (quadricToDiag : ∀ n : ℕ, ℂ →ₗ[ℂ] DiagAlg n)

/-- The volume evaluation of an abstract chiral scalar. -/
def quadricVolumeEval (n : ℕ) (x : ℂ) : ℂ :=
  colimitZeroTempState n (quadricToDiag n x)

/-- 
**Evaluation of the supplied square-zero equations**
-/
theorem square_zero_pair_evaluates_to_zero (n : ℕ) (S_plus S_minus : ℂ)
    (h_plus : S_plus * S_plus = 0) (h_minus : S_minus * S_minus = 0) :
    quadricVolumeEval quadricToDiag n (S_plus * S_plus) = 0 ∧
    quadricVolumeEval quadricToDiag n (S_minus * S_minus) = 0 := by
  constructor
  · dsimp [quadricVolumeEval]
    rw [h_plus]
    rw [map_zero]
    rw [phase_space_shattering_to_cantor_boundary]
    exact map_zero (finiteZeroTempState n)
  · dsimp [quadricVolumeEval]
    rw [h_minus]
    rw [map_zero]
    rw [phase_space_shattering_to_cantor_boundary]
    exact map_zero (finiteZeroTempState n)

/-!
### 4. Conditional finite-stage coherence
The following result needs the stated compatibility of the supplied maps at
successive stages. It is not an infinite-limit or zeta/volume theorem.
-/

/-- 
**Analytic Zeta/Volume Shattering Resolution**:
The amplituhedron volume is formally invariant under the Colimit Continuum 
embeddings because the phase-space shatters perfectly onto the boundary.
-/
theorem amplituhedron_volume_colimit_coherence 
    (n : ℕ) (obs : BCFWKinematicAlgebra ℂ) 
    (h_intertwine : kinematicToDiag (n + 1) obs = diagEmbedSucc n (kinematicToDiag n obs)) :
    amplituhedronVolumeEval kinematicToDiag (n + 1) obs = amplituhedronVolumeEval kinematicToDiag n obs := by
  dsimp [amplituhedronVolumeEval]
  rw [h_intertwine]
  exact colimit_crystallization_resolves_closure_debt n (kinematicToDiag n obs)

end InfoGeometry.Canonical.AmplituhedronBostConnesAnalyticBridge
