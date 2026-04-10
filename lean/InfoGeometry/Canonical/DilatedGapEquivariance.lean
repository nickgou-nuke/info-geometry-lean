import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.SuperchargeGapBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DilatedGapEquivariance

Operatorial bridge from phase-flip equivariance to gap/obstruction residuals.

This file stays entirely non-coordinate:
- fixed-grading sector-swap residual on the analytical-index lane,
- Drazin/Moore-Penrose projector-obstruction residual on the ring lane,
- transported parity/modular gap residual on the doubled-carrier lane.
-/

namespace InfoGeometry.Canonical.DilatedGapEquivariance

open InfoGeometry.Canonical.AnalyticalIndex
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.SuperchargeGapBridge
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein

section FixedGrading

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/--
Fixed-grading projector-equivariance residual:
the sum of opposite-grading analytical indices.
-/
@[rep_depth krein]
noncomputable def fixedGradingIndexResidual
    (D Γ : V →ₗ[ℝ] V) : ℤ :=
  analyticalIndex D (-Γ) + analyticalIndex D Γ

/--
The fixed-grading residual vanishes exactly because grading negation swaps
chiral sectors and flips the analytical-index sign.
-/
@[rep_depth krein]
theorem fixedGradingIndexResidual_eq_zero
    (D Γ : V →ₗ[ℝ] V) :
    fixedGradingIndexResidual D Γ = 0 := by
  unfold fixedGradingIndexResidual
  rw [analyticalIndex_neg_grading_eq_neg]
  simp

end FixedGrading

section ProjectorMismatch

variable {R : Type*} [Ring R] [StarRing R]

/-- Drazin/Moore-Penrose projector obstruction residual. -/
@[rep_depth transport]
def projectorObstruction
    (a a_d a_mp : R) : R :=
  projectorMismatch a a_d a_mp

/--
Vanishing projector obstruction implies vanishing chiral anomaly.
-/
@[rep_depth transport]
theorem chiralAnomaly_eq_zero_of_projectorObstruction_eq_zero
    {a a_d a_mp : R}
    (hObs : projectorObstruction a a_d a_mp = 0) :
    chiralAnomaly a a_d a_mp = 0 := by
  exact chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero hObs

end ProjectorMismatch

section TransportedGap

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Residual between the transported gap seed and its phase-antilinear channel.
-/
@[rep_depth transport]
noncomputable def transportedParityModularGapObstruction
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E)) : EndH :=
  transportedParityModularGapSeed (E := E) V
    -
  fockAnticommutator (E := E)
    (transportCommutator (E := E)
      (phaseAntilinearPart (E := E) V.connectionGenerator)
      (modular_j (E := E)))
    (spectral_epsilon (E := E))

/--
If the phase-linear channel commutes with `J`, the transported gap obstruction
vanishes.
-/
@[rep_depth transport]
theorem transportedParityModularGapObstruction_eq_zero_of_commute_phaseLinearPart
    (V : BogoliubovVielbein.BogoliubovVielbeinBundle (E := E))
    (hComm :
      Commute (modular_j (E := E))
        (phaseLinearPart (E := E) V.connectionGenerator)) :
    transportedParityModularGapObstruction (E := E) V = 0 := by
  unfold transportedParityModularGapObstruction
  rw [transportedParityModularGapSeed_eq_phaseAntilinearSeed_of_commute_phaseLinearPart
    (E := E) V hComm]
  simp

end TransportedGap

end InfoGeometry.Canonical.DilatedGapEquivariance
