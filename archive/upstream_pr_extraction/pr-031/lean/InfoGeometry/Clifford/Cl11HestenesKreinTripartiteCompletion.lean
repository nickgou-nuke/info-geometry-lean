import InfoGeometry.Clifford.Cl11InfiniteCarrier
import InfoGeometry.Krein.HestenesModularKMSBridge
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Dynamics.ModularThermalState

open scoped InnerProductSpace

/-!
# Cl(1,1) finite carrier with Hestenes--Krein tripartite analytic flow

The previous finite-to-infinite carrier remains algebraic:

* `Cl11InfiniteCarrier.CompatibleCarrier = Cl11TensorTowerLimit.Limit`;
* `Cl11InfiniteCarrier.intoCarrier n` is the compatible cone from stage `n`;
* `Cl11InfiniteCarrier.finiteAdvance m k` is finite induction through `k` bonds.

The intended analytic completion is not a bare Banach/von-Neumann completion of
that direct limit.  In this repository it is expressed by explicit
Hestenes--Krein phase-axis analyticity and modular-flow data, together with the
elliptic/hyperbolic/parabolic tripartite geometry.  This file records that
composition theorem-safely: finite tower compatibility is one component, and
Hestenes--Krein/tripartite flow compatibility is supplied by the existing flow
APIs.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11HestenesKreinTripartiteCompletion

open InfoGeometry.Clifford.Cl11InfiniteCarrier
open InfoGeometry.Krein.HestenesModularKMSBridge

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [InfoGeometry.Krein.KreinSpace E]

local notation "EndH" => E →L[ℝ] E

/-- Hestenes--Krein analyticity of the modular flow: the flow commutes with the real phase axis. -/
theorem hestenesKrein_flow_phase_analytic
    (P : HestenesKreinKMSPacket (E := E)) (t : ℝ) (A : EndH) :
    P.modularFlow.flow t (P.phaseAxis * A) =
      P.phaseAxis * P.modularFlow.flow t A :=
  P.hestenes_flow_to_abstract_flow t A

/-- The observable flow is the supplied real rotor-conjugation action. -/
theorem hestenesKrein_flow_rotor_conjugation
    (P : HestenesKreinKMSPacket (E := E)) (t : ℝ) (A : EndH) :
    P.modularFlow.flow t A = P.rotor t * A * P.rotorInv t :=
  P.modularFlow_eq_rotor_conjugation_theorem t A

/-- The Hestenes--Krein rotor preserves the nonnegative Krein cone used by the packet. -/
theorem hestenesKrein_rotor_preserves_naturalCone
    (P : HestenesKreinKMSPacket (E := E)) (t : ℝ) {ξ : E}
    (hξ : ξ ∈ P.HestenesNaturalCone) :
    P.rotor t ξ ∈ P.HestenesNaturalCone :=
  P.rotor_preserves_HestenesNaturalCone t hξ

/-- The Hestenes--Krein rotor preserves the Krein null cone. -/
theorem hestenesKrein_rotor_preserves_nullCone
    (P : HestenesKreinKMSPacket (E := E)) (t : ℝ) {ξ : E}
    (hξ : InfoGeometry.Krein.KreinSpace.kreinInner (H := E) ξ ξ = 0) :
    InfoGeometry.Krein.KreinSpace.kreinInner (H := E) (P.rotor t ξ) (P.rotor t ξ) = 0 :=
  P.modular_rotor_preserves_null_cone t hξ

/-- The tripartite finite geometry: elliptic square `-1`, hyperbolic square `+1`, parabolic square `0`. -/
theorem tripartite_local_flow_atom :
    InfoGeometry.Algebra.HypercomplexTriad.I * InfoGeometry.Algebra.HypercomplexTriad.I =
        -(1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) ∧
      InfoGeometry.Algebra.HypercomplexTriad.E * InfoGeometry.Algebra.HypercomplexTriad.E =
        (1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) ∧
      InfoGeometry.Algebra.HypercomplexTriad.N * InfoGeometry.Algebra.HypercomplexTriad.N =
        (0 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) := by
  rcases InfoGeometry.Algebra.HypercomplexTriad.local_cayley_klein_atom with
    ⟨hI, hE, hN, _hPp, _hPm, _hOrth, _hSum⟩
  exact ⟨hI, hE, hN⟩

/-- Parabolic tripartite flow unit: `(1 + N)` has right inverse `(1 - N)`. -/
theorem tripartite_unipotent_flow_right_inverse :
    ((1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) + InfoGeometry.Algebra.HypercomplexTriad.N) *
        ((1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) - InfoGeometry.Algebra.HypercomplexTriad.N) =
      (1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) :=
  InfoGeometry.Algebra.HypercomplexTriad.one_add_N_mul_one_sub_N

/-- Parabolic tripartite flow unit: `(1 - N)` has right inverse `(1 + N)`. -/
theorem tripartite_unipotent_flow_left_inverse :
    ((1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) - InfoGeometry.Algebra.HypercomplexTriad.N) *
        ((1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) + InfoGeometry.Algebra.HypercomplexTriad.N) =
      (1 : InfoGeometry.Algebra.HypercomplexTriad.Mat2) :=
  InfoGeometry.Algebra.HypercomplexTriad.one_sub_N_mul_one_add_N

/-- Real-axis readout of a supplied Hestenes--Krein analytic-continuation datum. -/
theorem hestenesKrein_sigmaC_real_axis
    {A : Type*} [Monoid A]
    (H : InfoGeometry.Dynamics.HestenesKreinAnalyticContinuationData A)
    (t : ℝ) (a : A) :
    H.sigmaC (t : ℂ) a =
      InfoGeometry.Dynamics.ModularAutomorphismFamily.sigma H.modular t a :=
  InfoGeometry.Dynamics.sigmaC_real_axis_eq_sigma H t a

/-- Top-strip readout of a supplied Hestenes--Krein analytic-continuation datum. -/
theorem hestenesKrein_sigmaC_top_strip
    {A : Type*} [Monoid A]
    (H : InfoGeometry.Dynamics.HestenesKreinAnalyticContinuationData A)
    (t : ℝ) (a : A) :
    H.sigmaC (InfoGeometry.Dynamics.complexClockPoint t H.beta) a =
      InfoGeometry.Dynamics.ModularAutomorphismFamily.sigma H.modular (t + H.beta) a :=
  InfoGeometry.Dynamics.sigmaC_top_strip_eq_sigma_shift H t a

/--
The corrected finite-to-infinite statement has two compatible components:
finite Clifford/tensor induction lands in the algebraic direct-limit carrier,
and the intended analytic completion is the supplied Hestenes--Krein phase-axis
flow.
-/
theorem finiteCarrier_and_hestenesKreinFlow
    (m k : ℕ) (A : Stage m)
    (P : HestenesKreinKMSPacket (E := E)) (t : ℝ) (B : EndH) :
    intoCarrier (m + k) (finiteAdvance m k A) = intoCarrier m A ∧
      P.modularFlow.flow t (P.phaseAxis * B) =
        P.phaseAxis * P.modularFlow.flow t B := by
  exact ⟨intoCarrier_finiteAdvance m k A, hestenesKrein_flow_phase_analytic P t B⟩

end InfoGeometry.Clifford.Cl11HestenesKreinTripartiteCompletion
