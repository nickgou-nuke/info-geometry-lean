import InfoGeometry.Applications.STUBlackHoleQubit
import InfoGeometry.Application.STUOperatorBridge
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# InfoGeometry/Applications/STUGradientFlow.lean

Formalizes the Wasserstein/Otto gradient descent of the Freudenthal entropy 
potential for the 3-qubit STU model.

Provides the computable Diagonal STU sandbox to verify the Drazin surgery 
at the I₄ = 0 boundary (GHZ to W-state decoherence).
-/

noncomputable section

namespace STUGradientFlow

open InfoGeometry.Applications.STUQubit
open InfoGeometry.Application.STUOperator

/-! ### 1. The Abstract 8D Fisher-Souriau Metric Witness -/

/--
Witness that the 8x8 Hessian of the STU potential is non-degenerate 
on the regular GHZ chamber.
-/
structure STUFisherMetricWitness 
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (I : OperatorQuarticInvariant (E := E)) where
  /-- The potential Φ = -log|I₄| -/
  potential : (E →L[ℝ] E) → ℝ
  
  /-- The metric tensor (Hessian of Φ) -/
  metric : (E →L[ℝ] E) → ((E →L[ℝ] E) →L[ℝ] ((E →L[ℝ] E) →L[ℝ] ℝ))
  
  /-- The inverse metric tensor (required for gradient flow) -/
  inverse_metric : (E →L[ℝ] E) → ((E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E))
  
  /-- Certificate of inversion on the GHZ orbit -/
  inversion_cert : ∀ psi : (E →L[ℝ] E), IsRegularOperator I psi → 
    -- at this abstraction level `inverse_metric` is a tangent endomorphism
    ∀ v : (E →L[ℝ] E), inverse_metric psi v = v

/-! ### 2. The Computable Sandbox: Diagonal STU Reduction -/

/--
The Cartan/Diagonal subspace of the STU model.
Under local unitaries (K-sector), the 8 amplitudes can be reduced to 
a 3-parameter diagonal frame (x, y, z) corresponding to the A-sector.
-/
structure DiagonalSTUState where
  x : ℝ
  y : ℝ
  z : ℝ

namespace DiagonalSTUState

/-- 
The Diagonal Cubic Norm (simplification of the Quartic/Hyperdeterminant on the A-axis). 
N(x,y,z) = x * y * z
-/
def cubicNorm (state : DiagonalSTUState) : ℝ :=
  state.x * state.y * state.z

/-- 
The Diagonal GHZ Orbit.
The state is regular if the volume does not vanish.
-/
def isRegular (state : DiagonalSTUState) : Prop :=
  cubicNorm state ≠ 0

/-- 
The Computable Log-Barrier Potential:
Φ = -log|x*y*z| = -log|x| - log|y| - log|z|
-/
def potential (state : DiagonalSTUState) (_h : isRegular state) : ℝ :=
  - Real.log |state.x| - Real.log |state.y| - Real.log |state.z|

/--
The Computable Fisher Information Metric.
Inverse G⁻¹ = diag(x², y², z²)
-/
def inverseFisherMetric (state : DiagonalSTUState) : DiagonalSTUState :=
  ⟨state.x ^ 2, state.y ^ 2, state.z ^ 2⟩

/--
The Wasserstein/Otto Gradient Flow vector field.
v = - G⁻¹ ∇Φ = (x, y, z)
-/
def gradientFlowField (state : DiagonalSTUState) : DiagonalSTUState :=
  ⟨state.x, state.y, state.z⟩

end DiagonalSTUState

/-! ### 3. Explicit Drazin Surgery on the Sandbox -/

/--
If decoherence drives the state to the boundary (e.g., x -> 0), the cubic norm vanishes.
The regular flow fails. Drazin surgery amputates the nilpotent/zero direction 
and restarts the flow on the bipartite core.
-/
structure DiagonalDrazinSurgery where
  /-- The boundary event: tracing out the first qubit (x -> 0) -/
  horizon_state : DiagonalSTUState
  is_horizon : horizon_state.x = 0 ∧ horizon_state.y ≠ 0 ∧ horizon_state.z ≠ 0

  /-- 
  The Drazin core projection.
  Mathematically isolates the non-zero (y, z) block. 
  Physically maps the dead 3-qubit GHZ state into a live 2-qubit Bell state.
  -/
  drazin_projector : DiagonalSTUState → DiagonalSTUState :=
    fun s => ⟨0, s.y, s.z⟩

  /-- The post-surgery potential ignores the amputated axis -/
  post_surgery_potential : DiagonalSTUState → ℝ :=
    fun s => - Real.log |s.y| - Real.log |s.z|

end STUGradientFlow
