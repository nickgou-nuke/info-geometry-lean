import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Krein.DoubledSpace

/-!
# Souriau Dirac-Hodge Coupling & Anomaly Elimination

This file contains proof-carrying operator lanes for the Souriau Dirac-Hodge
coupling.

The primary lane is real Hestenes/Krein: the carrier has a Krein fundamental
symmetry `KreinSpace.jCLM`, the phase axis is a real endomorphism, and traces are
real signed/Krein readouts.  A legacy complex Hilbert auxiliary lane is retained
below because several older modules still import it.
-/

universe u

namespace InfoGeometry.Dynamics.SouriauDiracHodge

open scoped InnerProductSpace
open InfoGeometry.Krein

/-! ## Real Hestenes/Krein operator lane -/

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [KreinSpace H]

noncomputable section

/-- Proof-carrying Dirac-Hodge data on a real Hestenes/Krein carrier. -/
structure KreinOperatorData where
  /-- Chiral Hestenes phase-axis / tilt operator. -/
  K : H →L[ℝ] H
  /-- The Hestenes phase axis squares to the real replacement of `-1`. -/
  K_sq : K * K = -(1 : H →L[ℝ] H)
  /-- The Krein/Tomita fundamental symmetry flips the phase axis. -/
  J_K_anticommute :
    KreinSpace.jCLM (H := H) * K = -(K * KreinSpace.jCLM (H := H))
  /-- Left Cuntz shift, read as the exterior derivative branch. -/
  S_left : H →L[ℝ] H
  /-- Real modular/rotor observable flow on the carrier. -/
  modularAutomorphism : ℝ → H →L[ℝ] H
  /-- Modular covariance of the left Cuntz branch. -/
  modular_dilation_L :
    ∀ t : ℝ, modularAutomorphism t * S_left = S_left * modularAutomorphism t
  /-- Projection onto twisted / orientation-reversing sectors. -/
  twistedSectorProjection : H →L[ℝ] H
  /-- Thermal density endomorphism at inverse temperature `beta`. -/
  thermalDensityMatrix : ℝ → H →L[ℝ] H
  /-- KMS `J`-invariance of the thermal state. -/
  thermal_J_commute :
    ∀ beta : ℝ,
      thermalDensityMatrix beta * KreinSpace.jCLM (H := H) =
        KreinSpace.jCLM (H := H) * thermalDensityMatrix beta
  /-- Zero-temperature spectral convergence of the chiral channel. -/
  thermal_zero_temp_spectral_convergence :
    Filter.Tendsto (fun beta : ℝ => ‖thermalDensityMatrix beta * K‖)
      Filter.atTop (nhds 0)

namespace KreinOperatorData

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [KreinSpace H]
variable (D : KreinOperatorData H)

/-! ### Cuntz shifts and chiral charge -/

/-- The real Krein/Tomita fundamental symmetry. -/
noncomputable def J (_D : KreinOperatorData H) : H →L[ℝ] H :=
  KreinSpace.jCLM (H := H)

/-- The right Cuntz shift is the Hodge dual codifferential. -/
noncomputable def S_right : H →L[ℝ] H :=
  D.J * D.S_left * D.J

/-- Chiral charge density operator. -/
noncomputable def chiralChargeOperator : H →L[ℝ] H :=
  D.K

/-! ### Cyclic cocycle twisted sectors -/

/-- Index pairing of the Dirac-Hodge operator over the twisted sectors. -/
noncomputable def indexPairing (trace : (H →L[ℝ] H) → ℝ) : ℝ :=
  trace (D.chiralChargeOperator * D.twistedSectorProjection)

/--
Topological index vanishing over the twisted sectors in the real
Hestenes/Krein lane.

The proof uses only real linearity, Krein/Tomita trace invariance,
projection-`J` commutation, and the supplied Hestenes anticommutation
`J K = - K J`.
-/
theorem twisted_index_vanishing (trace : (H →L[ℝ] H) → ℝ)
    (h_trace_linear : ∀ (c : ℝ) (A : H →L[ℝ] H), trace (c • A) = c * trace A)
    (h_trace_J_inv : ∀ A, trace (D.J * A * D.J) = trace A)
    (h_proj_J_comm : D.twistedSectorProjection * D.J = D.J * D.twistedSectorProjection) :
    D.indexPairing trace = 0 := by
  unfold indexPairing chiralChargeOperator
  set A := D.K * D.twistedSectorProjection
  have hJ2 : D.J * D.J = (1 : H →L[ℝ] H) := by
    change D.J.comp D.J = ContinuousLinearMap.id ℝ H
    simp [J]
  have hJK : D.J * D.K = -(D.K * D.J) := by
    simpa [J] using D.J_K_anticommute
  have hJ_A_J_eq_neg_A : D.J * A * D.J = -A := by
    dsimp [A]
    set P := D.twistedSectorProjection
    have hP_J_comm : P * D.J = D.J * P := by
      simpa [P] using h_proj_J_comm
    have hmiddle :
        ((D.K * D.J) * P) * D.J = D.K * P := by
      calc
        ((D.K * D.J) * P) * D.J
            = D.K * ((D.J * P) * D.J) := by noncomm_ring
        _ = D.K * ((P * D.J) * D.J) := by rw [← hP_J_comm]
        _ = D.K * (P * (D.J * D.J)) := by noncomm_ring
        _ = D.K * (P * 1) := by rw [hJ2]
        _ = D.K * P := by simp
    calc
      D.J * (D.K * P) * D.J
          = ((D.J * D.K) * P) * D.J := by noncomm_ring
      _ = ((-(D.K * D.J)) * P) * D.J := by
            rw [hJK]
      _ = -(((D.K * D.J) * P) * D.J) := by noncomm_ring
      _ = -(D.K * P) := by rw [hmiddle]
  have h_trace_eq : trace A = -trace A := by
    calc
      trace A = trace (D.J * A * D.J) := by rw [h_trace_J_inv A]
      _ = trace (-A) := by rw [hJ_A_J_eq_neg_A]
      _ = trace ((-1 : ℝ) • A) := by simp
      _ = (-1 : ℝ) * trace A := by rw [h_trace_linear]
      _ = -trace A := by ring
  linarith

/-- Hodge-star conjugation executes the Hestenes phase-axis flip. -/
theorem hodge_star_executes_legendre_transform :
    D.J * D.chiralChargeOperator * D.J = -D.chiralChargeOperator := by
  dsimp [chiralChargeOperator]
  have hJ2 : D.J * D.J = (1 : H →L[ℝ] H) := by
    change D.J.comp D.J = ContinuousLinearMap.id ℝ H
    simp [J]
  have hJK : D.J * D.K = -(D.K * D.J) := by
    simpa [J] using D.J_K_anticommute
  calc
    D.J * D.K * D.J = (-(D.K * D.J)) * D.J := by rw [hJK]
    _ = -(D.K * (D.J * D.J)) := by noncomm_ring
    _ = -(D.K * 1) := by rw [hJ2]
    _ = -D.K := by simp

/--
Zero-temperature anomaly cancellation in the supplied real Krein context.
-/
theorem zero_temperature_anomaly_cancellation :
    Filter.Tendsto
      (fun beta : ℝ => ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) := by
  simpa [chiralChargeOperator] using D.thermal_zero_temp_spectral_convergence

/--
Zero-temperature convergence from an explicit scalar spectral/Dikin estimate.
-/
theorem zero_temperature_convergence_of_eventual_bound
    {error : ℝ → ℝ}
    (h_bound :
      ∀ᶠ beta : ℝ in Filter.atTop,
        ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖ ≤ error beta)
    (h_error : Filter.Tendsto error Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun beta : ℝ => ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) := by
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun beta : ℝ =>
      norm_nonneg (D.thermalDensityMatrix beta * D.chiralChargeOperator))
    h_bound h_error

/--
Quadratic Dikin/spectral estimate implies zero-temperature convergence.
-/
theorem zero_temperature_convergence_of_quadratic_bound
    (epsilon : ℝ → ℝ) (C : ℝ)
    (h_bound :
      ∀ᶠ beta : ℝ in Filter.atTop,
        ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖ ≤
          C * epsilon beta ^ 2)
    (h_epsilon : Filter.Tendsto epsilon Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun beta : ℝ => ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) := by
  have h_error :
      Filter.Tendsto (fun beta : ℝ => C * epsilon beta ^ 2)
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (h_epsilon.pow 2))
  exact D.zero_temperature_convergence_of_eventual_bound h_bound h_error

end KreinOperatorData

/--
Constructor for real `KreinOperatorData` when the zero-temperature law is
obtained from an explicit quadratic spectral/Dikin estimate.
-/
def KreinOperatorData.ofQuadraticSpectralEstimate
    (K : H →L[ℝ] H)
    (K_sq : K * K = -(1 : H →L[ℝ] H))
    (J_K_anticommute : KreinSpace.jCLM (H := H) * K = -(K * KreinSpace.jCLM (H := H)))
    (S_left : H →L[ℝ] H)
    (modularAutomorphism : ℝ → H →L[ℝ] H)
    (modular_dilation_L :
      ∀ t : ℝ, modularAutomorphism t * S_left = S_left * modularAutomorphism t)
    (twistedSectorProjection : H →L[ℝ] H)
    (thermalDensityMatrix : ℝ → H →L[ℝ] H)
    (thermal_J_commute :
      ∀ beta : ℝ,
        thermalDensityMatrix beta * KreinSpace.jCLM (H := H) =
          KreinSpace.jCLM (H := H) * thermalDensityMatrix beta)
    (epsilon : ℝ → ℝ) (C : ℝ)
    (h_bound :
      ∀ᶠ beta : ℝ in Filter.atTop,
        ‖thermalDensityMatrix beta * K‖ ≤ C * epsilon beta ^ 2)
    (h_epsilon : Filter.Tendsto epsilon Filter.atTop (nhds 0)) :
    KreinOperatorData H where
  K := K
  K_sq := K_sq
  J_K_anticommute := J_K_anticommute
  S_left := S_left
  modularAutomorphism := modularAutomorphism
  modular_dilation_L := modular_dilation_L
  twistedSectorProjection := twistedSectorProjection
  thermalDensityMatrix := thermalDensityMatrix
  thermal_J_commute := thermal_J_commute
  thermal_zero_temp_spectral_convergence := by
    exact squeeze_zero'
      (Filter.Eventually.of_forall fun beta : ℝ =>
        norm_nonneg (thermalDensityMatrix beta * K))
      h_bound
      (by
        have h_error :
            Filter.Tendsto (fun beta : ℝ => C * epsilon beta ^ 2)
              Filter.atTop (nhds 0) := by
          simpa using (tendsto_const_nhds.mul (h_epsilon.pow 2))
        exact h_error)

end

/-! ## Legacy complex Hilbert auxiliary lane -/

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable section

/-- Proof-carrying operator data for the Hilbert-space Dirac-Hodge lane. -/
structure OperatorData where
  /-- Tomita-Takesaki modular conjugation / real-structure involution. -/
  J : H →L[ℂ] H
  /-- `J` is involutive. -/
  J_involution : J ∘L J = ContinuousLinearMap.id ℂ H
  /-- Chiral phase-axis / tilt operator. -/
  K : H →L[ℂ] H
  /-- `K` is involutive. -/
  K_involution : K ∘L K = ContinuousLinearMap.id ℂ H
  /-- Tomita conjugation flips the phase axis. -/
  J_K_anticommute : J ∘L K = -(K ∘L J)
  /-- Left Cuntz shift, read as the exterior derivative branch. -/
  S_left : H →L[ℂ] H
  /-- Modular automorphism flow. -/
  modularAutomorphism : ℝ → H →L[ℂ] H
  /-- Modular dilation law for the left Cuntz branch. -/
  modular_dilation_L :
    ∀ t : ℝ, modularAutomorphism t ∘L S_left = (2 : ℂ) ^ (t * Complex.I) • S_left
  /-- Projection onto twisted / orientation-reversing sectors. -/
  twistedSectorProjection : H →L[ℂ] H
  /-- Thermal density matrix at inverse temperature `beta`. -/
  thermalDensityMatrix : ℝ → H →L[ℂ] H
  /-- KMS `J`-invariance of the thermal state. -/
  thermal_J_commute :
    ∀ beta : ℝ, thermalDensityMatrix beta ∘L J = J ∘L thermalDensityMatrix beta
  /-- Zero-temperature spectral convergence of the chiral channel. -/
  thermal_zero_temp_spectral_convergence :
    Filter.Tendsto (fun beta : ℝ => ‖thermalDensityMatrix beta ∘L K‖)
      Filter.atTop (nhds 0)

namespace OperatorData

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (D : OperatorData H)

/-! ### Cuntz shifts and chiral charge -/

/-- The right Cuntz shift is the Hodge dual codifferential. -/
noncomputable def S_right : H →L[ℂ] H :=
  D.J ∘L D.S_left ∘L D.J

/-- Chiral charge density operator. -/
noncomputable def chiralChargeOperator : H →L[ℂ] H :=
  D.K

/-! ### Cyclic cocycle twisted sectors -/

/-- Index pairing of the Dirac-Hodge operator over the twisted sectors. -/
noncomputable def indexPairing (trace : (H →L[ℂ] H) → ℂ) : ℂ :=
  trace (D.chiralChargeOperator ∘L D.twistedSectorProjection)

/--
Topological index vanishing over the twisted sectors.

The proof uses only the supplied `J`-invariance of the trace, the supplied
commutation of the twisted projection with `J`, and the supplied
anticommutation `J K = - K J`.
-/
theorem twisted_index_vanishing (trace : (H →L[ℂ] H) → ℂ)
    (h_trace_linear : ∀ (c : ℂ) (A : H →L[ℂ] H), trace (c • A) = c * trace A)
    (h_trace_J_inv : ∀ A, trace (D.J ∘L A ∘L D.J) = trace A)
    (h_proj_J_comm : D.twistedSectorProjection ∘L D.J = D.J ∘L D.twistedSectorProjection) :
    D.indexPairing trace = 0 := by
  unfold indexPairing chiralChargeOperator
  set A := D.K ∘L D.twistedSectorProjection
  have hJ_A_J_eq_neg_A : D.J ∘L A ∘L D.J = -A := by
    dsimp [A]
    set P := D.twistedSectorProjection
    have hP_J_comm : P ∘L D.J = D.J ∘L P := by
      simpa [P] using h_proj_J_comm
    have hmiddle :
        ((D.K ∘L D.J) ∘L P) ∘L D.J = D.K ∘L P := by
      calc
        ((D.K ∘L D.J) ∘L P) ∘L D.J
            = (D.K ∘L (D.J ∘L P)) ∘L D.J := by
              exact congrArg (fun T => T ∘L D.J)
                (ContinuousLinearMap.comp_assoc D.K D.J P)
        _ = (D.K ∘L (P ∘L D.J)) ∘L D.J := by
              exact congrArg (fun T => (D.K ∘L T) ∘L D.J) hP_J_comm.symm
        _ = D.K ∘L ((P ∘L D.J) ∘L D.J) := by
              exact ContinuousLinearMap.comp_assoc D.K (P ∘L D.J) D.J
        _ = D.K ∘L (P ∘L (D.J ∘L D.J)) := by
              exact congrArg (fun T => D.K ∘L T)
                (ContinuousLinearMap.comp_assoc P D.J D.J)
        _ = D.K ∘L (P ∘L ContinuousLinearMap.id ℂ H) := by
              rw [D.J_involution]
        _ = D.K ∘L P := by
              simp
    calc
      D.J ∘L (D.K ∘L P) ∘L D.J
          = ((D.J ∘L D.K) ∘L P) ∘L D.J := by
            simp [ContinuousLinearMap.comp_assoc]
      _ = ((-(D.K ∘L D.J)) ∘L P) ∘L D.J := by
            rw [D.J_K_anticommute]
      _ = -(((D.K ∘L D.J) ∘L P) ∘L D.J) := by
            rw [ContinuousLinearMap.neg_comp, ContinuousLinearMap.neg_comp]
      _ = -(D.K ∘L P) := by
            rw [hmiddle]
  have h_trace_eq : trace A = -trace A := by
    calc
      trace A = trace (D.J ∘L A ∘L D.J) := by rw [h_trace_J_inv A]
      _ = trace (-A) := by rw [hJ_A_J_eq_neg_A]
      _ = trace ((-1 : ℂ) • A) := by simp
      _ = (-1 : ℂ) * trace A := by rw [h_trace_linear]
      _ = -trace A := by ring
  have h_add : trace A + trace A = 0 := by
    calc
      trace A + trace A = -trace A + trace A := by nth_rw 1 [h_trace_eq]
      _ = 0 := by simp
  have h_two_mul_zero : (2 : ℂ) * trace A = 0 := by
    simpa [two_mul] using h_add
  have h_two_ne_zero : (2 : ℂ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h_two_mul_zero with (h | h)
  · exact absurd h h_two_ne_zero
  · exact h

/-- Hodge-star conjugation executes the Legendre phase-axis flip. -/
theorem hodge_star_executes_legendre_transform :
    D.J ∘L D.chiralChargeOperator ∘L D.J = -D.chiralChargeOperator := by
  dsimp [chiralChargeOperator]
  calc
    (D.J ∘L D.K) ∘L D.J = (-(D.K ∘L D.J)) ∘L D.J := by
      rw [D.J_K_anticommute]
    _ = -((D.K ∘L D.J) ∘L D.J) := by rw [ContinuousLinearMap.neg_comp]
    _ = -(D.K ∘L (D.J ∘L D.J)) := by rw [ContinuousLinearMap.comp_assoc]
    _ = -(D.K ∘L ContinuousLinearMap.id ℂ H) := by rw [D.J_involution]
    _ = -D.K := by simp

/--
Zero-temperature anomaly cancellation in the supplied operator context.

The analytic convergence is not asserted globally: it is the
`thermal_zero_temp_spectral_convergence` field of `OperatorData`.
-/
theorem zero_temperature_anomaly_cancellation :
    Filter.Tendsto
      (fun beta : ℝ => ‖D.thermalDensityMatrix beta ∘L D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) := by
  simpa [chiralChargeOperator] using D.thermal_zero_temp_spectral_convergence

/--
Zero-temperature convergence from an explicit scalar spectral/Dikin estimate.

This is the proof step that avoids using the convergence field directly:
if the chiral thermal channel is eventually bounded by a scalar error tending
to zero, then the channel norm tends to zero.
-/
theorem zero_temperature_convergence_of_eventual_bound
    {error : ℝ → ℝ}
    (h_bound :
      ∀ᶠ beta : ℝ in Filter.atTop,
        ‖D.thermalDensityMatrix beta ∘L D.chiralChargeOperator‖ ≤ error beta)
    (h_error : Filter.Tendsto error Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun beta : ℝ => ‖D.thermalDensityMatrix beta ∘L D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) := by
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun beta : ℝ =>
      norm_nonneg (D.thermalDensityMatrix beta ∘L D.chiralChargeOperator))
    h_bound h_error

/--
Quadratic Dikin/spectral estimate implies zero-temperature convergence.

The concrete model supplies `epsilon beta` and an eventual bound
`‖ρ(beta)K‖ ≤ C * epsilon(beta)^2`; the proof only needs
`epsilon beta → 0`.
-/
theorem zero_temperature_convergence_of_quadratic_bound
    (epsilon : ℝ → ℝ) (C : ℝ)
    (h_bound :
      ∀ᶠ beta : ℝ in Filter.atTop,
        ‖D.thermalDensityMatrix beta ∘L D.chiralChargeOperator‖ ≤
          C * epsilon beta ^ 2)
    (h_epsilon : Filter.Tendsto epsilon Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun beta : ℝ => ‖D.thermalDensityMatrix beta ∘L D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) := by
  have h_error :
      Filter.Tendsto (fun beta : ℝ => C * epsilon beta ^ 2)
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (h_epsilon.pow 2))
  exact D.zero_temperature_convergence_of_eventual_bound h_bound h_error

end OperatorData

/--
Constructor for `OperatorData` when the zero-temperature law is obtained from
an explicit quadratic spectral/Dikin estimate rather than supplied directly.
-/
def OperatorData.ofQuadraticSpectralEstimate
    (J : H →L[ℂ] H)
    (J_involution : J ∘L J = ContinuousLinearMap.id ℂ H)
    (K : H →L[ℂ] H)
    (K_involution : K ∘L K = ContinuousLinearMap.id ℂ H)
    (J_K_anticommute : J ∘L K = -(K ∘L J))
    (S_left : H →L[ℂ] H)
    (modularAutomorphism : ℝ → H →L[ℂ] H)
    (modular_dilation_L :
      ∀ t : ℝ, modularAutomorphism t ∘L S_left = (2 : ℂ) ^ (t * Complex.I) • S_left)
    (twistedSectorProjection : H →L[ℂ] H)
    (thermalDensityMatrix : ℝ → H →L[ℂ] H)
    (thermal_J_commute :
      ∀ beta : ℝ, thermalDensityMatrix beta ∘L J = J ∘L thermalDensityMatrix beta)
    (epsilon : ℝ → ℝ) (C : ℝ)
    (h_bound :
      ∀ᶠ beta : ℝ in Filter.atTop,
        ‖thermalDensityMatrix beta ∘L K‖ ≤ C * epsilon beta ^ 2)
    (h_epsilon : Filter.Tendsto epsilon Filter.atTop (nhds 0)) :
    OperatorData H where
  J := J
  J_involution := J_involution
  K := K
  K_involution := K_involution
  J_K_anticommute := J_K_anticommute
  S_left := S_left
  modularAutomorphism := modularAutomorphism
  modular_dilation_L := modular_dilation_L
  twistedSectorProjection := twistedSectorProjection
  thermalDensityMatrix := thermalDensityMatrix
  thermal_J_commute := thermal_J_commute
  thermal_zero_temp_spectral_convergence := by
    exact squeeze_zero'
      (Filter.Eventually.of_forall fun beta : ℝ =>
        norm_nonneg (thermalDensityMatrix beta ∘L K))
      h_bound
      (by
        have h_error :
            Filter.Tendsto (fun beta : ℝ => C * epsilon beta ^ 2)
              Filter.atTop (nhds 0) := by
          simpa using (tendsto_const_nhds.mul (h_epsilon.pow 2))
        exact h_error)

end

end InfoGeometry.Dynamics.SouriauDiracHodge
