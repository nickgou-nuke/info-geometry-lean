import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.ModularSourceBridge
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.TransportLieDerivative
import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace InfoGeometry.Canonical.DiscreteModularSpectrum

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ModularSourceBridge
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Krein

/-- Additive modular scale group surface for Type-III flow restrictions. -/
@[rep_depth transport]
structure TypeIIIScaleGroup where
  G : Set ℝ
  zero_mem : 0 ∈ G
  add_closed : ∀ a b : ℝ, a ∈ G → b ∈ G → a + b ∈ G
  neg_closed : ∀ a : ℝ, a ∈ G → -a ∈ G

/--
Discrete Type-IIIλ scale data.
Period is log q; parameter lambda = q⁻¹.
-/
@[rep_depth transport]
structure DiscreteTypeIIILambdaScale where
  q : ℝ
  hq : 1 < q

namespace DiscreteTypeIIILambdaScale
noncomputable def period (S : DiscreteTypeIIILambdaScale) : ℝ := Real.log S.q
noncomputable def spectrum (S : DiscreteTypeIIILambdaScale) : Set ℝ := {t | ∃ k : ℤ, t = (k : ℝ) * S.period}
end DiscreteTypeIIILambdaScale

section TypeIIIGLattice

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Proof-carrying Type-IIIg modular/Mellin lattice interface.
Strictly coordinate-free. Finite-dimensional scalar diagonal matrices are NOT allowed.
-/
@[rep_depth operator]
structure ModularMellinLattice (E : Type 0) [NormedAddCommGroup E] 
    [InnerProductSpace ℝ E] [CompleteSpace E] (CIK : CertifiedInverseKernel (DoubledSpace E)) where
  K0 : DoubledSpace E →L[ℝ] DoubledSpace E
  q : ℝ
  hq : q > 1
  commutes_with_drazin : Commute K0 (CertifiedInverseKernel.spectralProjector (E := DoubledSpace E) CIK)
  phaseAxis_commutes_with_drazin :
    Commute
      (InfoGeometry.Krein.clockAxis (E := E))
      (CertifiedInverseKernel.spectralProjector (E := DoubledSpace E) CIK)

namespace ModularMellinLattice

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {CIK : CertifiedInverseKernel (DoubledSpace E)}
variable (L : ModularMellinLattice E CIK)

local notation "H₂_loc" => DoubledSpace E
local notation "EndH_loc" => H₂_loc →L[ℝ] H₂_loc

noncomputable local instance : NormedRing EndH_loc := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH_loc := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH_loc :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH_loc
local instance : IsTopologicalRing EndH_loc := inferInstance
local instance : CompleteSpace EndH_loc := inferInstance

/--
Local finite-time exponential transport fixedness gate.

This mirrors the owner theorem in `TransportLieDerivative`; it is kept local
here because this module is compiled in a mixed fusion/base import graph where
the older imported owner surface may not export the finite-time lemma.
-/
private theorem expTransport_eq_self_of_commute_local
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (X A₀ : A) (t : ℝ) (hComm : Commute A₀ X) :
    expTransport (A := A) X A₀ t = A₀ := by
  have hCommScaled : Commute A₀ (t • X) := by
    simpa using hComm.smul_right t
  have hCommExp : Commute A₀ (NormedSpace.exp (t • X)) := by
    simpa using hCommScaled.exp_right
  have hScaledNeg : Commute (t • X) (t • (-X)) := by
    rw [smul_neg]
    exact (Commute.refl (t • X)).neg_right
  unfold expTransport
  calc
    (NormedSpace.exp (t • X) * A₀) * NormedSpace.exp (t • (-X))
        = (A₀ * NormedSpace.exp (t • X)) * NormedSpace.exp (t • (-X)) := by
            rw [hCommExp.eq]
    _ = A₀ * (NormedSpace.exp (t • X) * NormedSpace.exp (t • (-X))) := by
          rw [mul_assoc]
    _ = A₀ * NormedSpace.exp (t • X + t • (-X)) := by
          rw [← NormedSpace.exp_add_of_commute hScaledNeg]
    _ = A₀ * 1 := by
          simp
    _ = A₀ := by
          simp

noncomputable def thermalTimeStep (k : ℤ) : ℝ := (k : ℝ) * Real.log L.q

@[rep_depth operator]
noncomputable def discreteBoost (k : ℤ) (A : EndH_loc) : EndH_loc :=
  let X : EndH_loc := modularTransportGenerator (E := E) L.K0
  expTransport (A := EndH_loc) X A (L.thermalTimeStep k)

@[rep_depth operator]
theorem modularTransportGenerator_commutes_drazin :
    Commute
      (modularTransportGenerator (E := E) L.K0)
      (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK) := by
  have hPhase :
      (InfoGeometry.Krein.clockAxis (E := E)).comp
          (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK)
        =
      (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK).comp
          (InfoGeometry.Krein.clockAxis (E := E)) := by
    simpa using L.phaseAxis_commutes_with_drazin.eq
  have hK0 :
      L.K0.comp (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK)
        =
      (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK).comp L.K0 := by
    simpa using L.commutes_with_drazin.eq
  unfold modularTransportGenerator
  rw [Commute, SemiconjBy]
  calc
    (L.K0.comp (InfoGeometry.Krein.clockAxis (E := E))).comp
        (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK)
        =
      L.K0.comp
        ((InfoGeometry.Krein.clockAxis (E := E)).comp
          (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK)) := by
            rw [ContinuousLinearMap.comp_assoc]
    _ =
      L.K0.comp
        ((CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK).comp
          (InfoGeometry.Krein.clockAxis (E := E))) := by
            rw [hPhase]
    _ =
      (L.K0.comp (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK)).comp
        (InfoGeometry.Krein.clockAxis (E := E)) := by
            rw [ContinuousLinearMap.comp_assoc]
    _ =
      ((CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK).comp L.K0).comp
        (InfoGeometry.Krein.clockAxis (E := E)) := by
            rw [hK0]
    _ =
      (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK).comp
        (L.K0.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
            rw [ContinuousLinearMap.comp_assoc]

@[rep_depth operator]
theorem drazin_projector_invariant (k : ℤ) :
    L.discreteBoost k (CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK) = 
      CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK :=
  expTransport_eq_self_of_commute_local
    (X := modularTransportGenerator (E := E) L.K0)
    (A₀ := CertifiedInverseKernel.spectralProjector (E := H₂_loc) CIK)
    (t := L.thermalTimeStep k)
    (modularTransportGenerator_commutes_drazin (L := L)).symm

end ModularMellinLattice
end TypeIIIGLattice
end InfoGeometry.Canonical.DiscreteModularSpectrum
