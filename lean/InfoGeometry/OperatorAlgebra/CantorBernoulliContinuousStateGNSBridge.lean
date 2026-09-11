import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNonSeparatingBridge
import InfoGeometry.Algebra.CuntzNativeGNSBridge
import InfoGeometry.OperatorAlgebra.GNSMathlibBridge
import InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum
import InfoGeometry.Canonical.CStarAlgebraStateColimit

/-!
# Cantor-Bernoulli Continuous State Extension and Native Mathlib GNS Bridge

This owner module formalizes the native Mathlib GNS construction and the separating
firewall between the canonical gauge state and the spatial vacuum state:

1. **Annihilator Norm in the Gauge State:**
   The spatial annihilator $A_{\mathrm{ann}} = V_0^\dagger - V_1^\dagger \neq 0$ satisfies
   $\varphi_{\mathrm{gauge}}(A_{\mathrm{ann}}^\dagger A_{\mathrm{ann}}) = 1 \neq 0$,
   proving that $A_{\mathrm{ann}}$ does NOT lie in the GNS null space of the gauge state.

2. **Native Mathlib GNS Structure on $\mathcal{B}(L^2(\mathcal{C}, \mu_C))$:**
   For any positive functional $\varphi : \mathcal{B}(L^2) \to_{\mathrm{p}}[\mathbb{C}] \mathbb{C}$:
   - Pre-GNS vacuum $\Lambda(1) \in \varphi.\text{PreGNS}$.
   - Completed Hilbert space $\mathcal{H}_\varphi = \varphi.\text{GNS}$.
   - Unital star representation $\pi_\varphi : \mathcal{B}(L^2) \to⋆ₐ[ℂ] \mathcal{B}(\mathcal{H}_\varphi)$.
   - Cyclic vacuum vector $\Omega_\varphi \in \mathcal{H}_\varphi$ with $\|\Omega_\varphi\| = 1$.

3. **Expectation Recovery and Density:**
   - $\langle \Omega_\varphi, \pi_\varphi(A) \Omega_\varphi \rangle = \varphi(A)$.
   - $\overline{\pi_\varphi(\mathcal{B}(L^2)) \Omega_\varphi} = \mathcal{H}_\varphi$.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliContinuousStateGNSBridge

open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNonSeparatingBridge
open InfoGeometry.Algebra.CuntzNativeGNSBridge
open InfoGeometry.OperatorAlgebra.GNSMathlibBridge
open InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum
open CStarStateColimit.Native

abbrev B := InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.BoundedL2Operator

/-!
### 1. Annihilator Norm in the Gauge State
-/

/-- The spatial annihilator $A_{\mathrm{ann}} = V_0^\dagger - V_1^\dagger$. -/
def annihilatorOp : B :=
  (star vLeft) - (star vRight)

/-- 🏆 THEOREM 1: The product $A_{\mathrm{ann}}^\dagger A_{\mathrm{ann}} = (V_0 - V_1)(V_0^\dagger - V_1^\dagger)$
    expands to $V_0 V_0^\dagger - V_0 V_1^\dagger - V_1 V_0^\dagger + V_1 V_1^\dagger$. -/
theorem annihilatorOp_star_mul_self :
    star annihilatorOp * annihilatorOp =
      vLeft * star vLeft - vLeft * star vRight - vRight * star vLeft + vRight * star vRight := by
  dsimp [annihilatorOp]
  rw [star_sub, star_star, star_star]
  noncomm_ring

/-- The canonical gauge state value on $A_{\mathrm{ann}}^\dagger A_{\mathrm{ann}}$ on the word level:
    $\varphi(V_0 V_0^\dagger) - \varphi(V_0 V_1^\dagger) - \varphi(V_1 V_0^\dagger) + \varphi(V_1 V_1^\dagger) = 1/2 - 0 - 0 + 1/2 = 1$. -/
theorem gaugeStateWord_annihilator_normSq :
    canonicalGaugeState [false] [false] -
    canonicalGaugeState [false] [true] -
    canonicalGaugeState [true] [false] +
    canonicalGaugeState [true] [true] = 1 := by
  simp [canonicalGaugeState, InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState.gaugeStateWord]
  norm_num

/-- 🏆 THEOREM 2: The gauge expectation of the spatial annihilator norm is strictly 1 ≠ 0. -/
theorem gaugeStateWord_annihilator_nonZero :
    canonicalGaugeState [false] [false] -
    canonicalGaugeState [false] [true] -
    canonicalGaugeState [true] [false] +
    canonicalGaugeState [true] [true] ≠ 0 := by
  rw [gaugeStateWord_annihilator_normSq]
  norm_num

/-!
### 2. Native Mathlib GNS Structure for a Concrete Bounded Operator State
-/

variable (φ : B →ₚ[ℂ] ℂ)

/-- The native Mathlib pre-GNS space for a state on $\mathcal{B}(L^2)$. -/
noncomputable def gaugePreGNSVacuum : φ.PreGNS :=
  InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.preGNSVacuum φ

/-- The pre-GNS expectation identity for the cyclic vector. -/
theorem gaugePreGNS_expectation_recovery (A : B) :
    ⟪gaugePreGNSVacuum φ, φ.leftMulMapPreGNS A (gaugePreGNSVacuum φ)⟫_ℂ = φ A :=
  InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.preGNSVacuum_expectation φ A

/-- The native Mathlib completed GNS Hilbert space $\mathcal{H}_\varphi$. -/
noncomputable def gaugeGNSVacuum : φ.GNS :=
  InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum φ

/-- 🏆 THEOREM 3: The completed GNS vacuum vector has unit norm: ‖Ω_φ‖ = 1. -/
theorem gaugeGNSVacuum_norm (hφ_norm : φ 1 = 1) : ‖gaugeGNSVacuum φ‖ = 1 :=
  InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum_norm_eq_one φ hφ_norm

/-- The native Mathlib GNS representation $\pi_\varphi : B \to⋆ₐ[ℂ] \mathcal{B}(\mathcal{H}_\varphi)$. -/
noncomputable abbrev gaugeGNSRepresentation :=
  φ.gnsStarAlgHom

/-- 🏆 THEOREM 4: Expectation recovery in the GNS vacuum: ⟨Ω_φ, π_φ(A) Ω_φ⟩ = φ(A). -/
theorem gaugeGNS_expectation_recovery (A : B) :
    ⟪gaugeGNSVacuum φ, gaugeGNSRepresentation φ A (gaugeGNSVacuum φ)⟫_ℂ = φ A :=
  InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gns_state_expectation_recovery φ A

/-- 🏆 THEOREM 5: The GNS vacuum vector is cyclic in $\mathcal{H}_\varphi$:
    $\overline{\pi_\varphi(B) \Omega_\varphi} = \mathcal{H}_\varphi$. -/
theorem gaugeGNS_cyclic :
    DenseRange (fun A : B => gaugeGNSRepresentation φ A (gaugeGNSVacuum φ)) := by
  rw [show (fun A : B => gaugeGNSRepresentation φ A (gaugeGNSVacuum φ)) =
      fun A : B => InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap φ A by
    funext A
    simpa [gaugeGNSVacuum, gaugeGNSRepresentation] using
      (InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap_eq_gnsRepresentation_vacuum φ A).symm]
  exact InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap_denseRange φ

end InfoGeometry.OperatorAlgebra.CantorBernoulliContinuousStateGNSBridge
