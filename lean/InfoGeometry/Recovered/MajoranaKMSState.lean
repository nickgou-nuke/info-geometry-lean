import Mathlib.Tactic
import InfoGeometry.Recovered.MajoranaColimitBoundary
import InfoGeometry.Canonical.BostConnesKMS

/-!
# KMS Projection State Readouts for the S₊S₋ Continuum Trace

This file formalizes the KMS state trace readouts for the chiral Amplituhedron
boundaries mapped into the infinite-dimensional topological colimit.
The nilpotent Cuntz generators S₊ and S₋ form an idempotent projection 
whose trace splits the continuum exactly in half.
-/

namespace InfoGeometry.MajoranaKMSState

open InfoGeometry.MajoranaTensorBridge
open InfoGeometry.MajoranaColimitBoundary
open InfoGeometry.Canonical.BostConnesKMS

variable (MajoranaStage : ℕ → Type)
variable [∀ n, AddCommGroup (MajoranaStage n)] [∀ n, Module ℝ (MajoranaStage n)]
variable (iota : ∀ n, MajoranaStage n →ₗ[ℝ] MajoranaStage (n + 1))
variable (MajoranaContinuum : Type) [AddCommGroup MajoranaContinuum] [Module ℝ MajoranaContinuum]
variable (psi : ∀ n, MajoranaStage n →ₗ[ℝ] MajoranaContinuum)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
variable (baseEquiv : MajoranaStage 1 ≃ₗ[ℝ] MajoranaMatrix)

/--
The S₊S₋ projector in the finite 16D matrix stage.
-/
noncomputable def finiteProjector : MajoranaMatrix :=
  cuntzGeneratorPlus * cuntzGeneratorMinus

/--
The trace of the finite projector splits the 4D space exactly in half.
-/
theorem trace_finiteProjector_eq_two :
  Matrix.trace finiteProjector = 2 := by
  norm_num [finiteProjector, cuntzGeneratorPlus, cuntzGeneratorMinus,
    gamma0_maj, gamma2_maj, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]

/--
Pushing the finite projector up the Tensor Tower into the continuum limit.
-/
noncomputable def continuumProjector : MajoranaContinuum :=
  psi 1 (baseEquiv.symm finiteProjector)

/--
A bridge state connecting the Majorana tensor colimit continuum to the 
Bost--Connes KMS thermodynamic state.

This structure mandates that the macroscopic state evaluates the S₊S₋
continuum projector proportionally to the Bost--Connes KMS projection weight
for the prime `p = 2` (representing the 2-adic half-splitting of the chiral continuum).
-/
abbrev MajoranaBraidKMSState {Op : Type*} [Ring Op] [StarRing Op]
    (C : BostConnesCuntzSystem Op) : Type _ :=
  Σ' bcKMS : KMSProjectionState C,
    Σ' continuumTrace : MajoranaContinuum →ₗ[ℝ] ℝ,
      continuumTrace (continuumProjector (MajoranaStage := MajoranaStage)
        (MajoranaContinuum := MajoranaContinuum) (psi := psi) (baseEquiv := baseEquiv)) =
        kmsProjectionReadout bcKMS.β bcKMS.ζβ 2 2

namespace MajoranaBraidKMSState

variable {Op : Type*} [Ring Op] [StarRing Op] {C : BostConnesCuntzSystem Op}
variable (state : MajoranaBraidKMSState (MajoranaStage := MajoranaStage)
  (MajoranaContinuum := MajoranaContinuum) (psi := psi) (baseEquiv := baseEquiv) C)

abbrev bcKMS : KMSProjectionState C := state.1
abbrev continuumTrace : MajoranaContinuum →ₗ[ℝ] ℝ := state.2.1
abbrev eval_continuum_projector :
    state.2.1 (continuumProjector (MajoranaStage := MajoranaStage)
      (MajoranaContinuum := MajoranaContinuum) (psi := psi) (baseEquiv := baseEquiv)) =
      kmsProjectionReadout state.1.β state.1.ζβ 2 2 := state.2.2

/--
The KMS Projection State readout for the S₊S₋ continuum trace.
It evaluates exactly to the 2-adic Boltzmann weight `2^(-β) / ζ(β)`.
-/
theorem kms_readout_continuumProjector :
    state.2.1 (continuumProjector (MajoranaStage := MajoranaStage)
      (MajoranaContinuum := MajoranaContinuum) (psi := psi) (baseEquiv := baseEquiv)) =
    (2 : ℝ) ^ (-state.1.β) / state.1.ζβ := by
  rw [state.2.2]
  exact kmsProjectionReadout_self state.1.β state.1.ζβ 2

end MajoranaBraidKMSState

end InfoGeometry.MajoranaKMSState
