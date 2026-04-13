import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Canonical.OperatorDictionary
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Krein.Prelude
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ModularOrientationContract

Canonical sign/orientation contract for the doubled-real modular lane.

The contract records one fixed orientation and the explicit equivalence under:
- phase-axis flip `K ↦ -K`,
- time-parameter reversal `τ ↦ -τ`,
- plus/minus polarization relabeling,
- dictionary-vs-owner commutator orientation on projector fluxes.
-/

namespace InfoGeometry.Canonical.ModularOrientationContract

open InfoGeometry.Krein
open InfoGeometry.Krein.Prelude
open InfoGeometry.Canonical.StandardFormCore
open InfoGeometry.Canonical.OperatorDictionary
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovProjectorFlux

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Canonical orientation contract: the standard-form seed phase axis is `K`. -/
@[rep_depth krein]
theorem canonical_seed_phaseAxis_eq_phaseAxisK :
    (tomitaAtomSeed (H := E)).phaseAxis = phaseAxisK (E := E) := by
  calc
    (tomitaAtomSeed (H := E)).phaseAxis = complex_i (E := E) := by
      simpa using (tomitaAtomSeed_phaseAxis_eq_complex_i (H := E))
    _ = phaseAxisK (E := E) := by rfl

/-- Canonical orientation contract: `K = J ∘ ε`. -/
@[rep_depth krein]
theorem canonical_phaseAxis_eq_modular_j_comp_spectral_epsilon :
    phaseAxisK (E := E)
      = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
  simpa using phaseAxisK_eq_modular_j_comp_spectral_epsilon (E := E)

/-- Phase-axis flip preserves the complex-structure law: `(-K)^2 = -Id`. -/
@[rep_depth krein]
theorem phaseAxis_flip_sq_eq_neg_id :
    (-(phaseAxisK (E := E))).comp (-(phaseAxisK (E := E)))
      = -(ContinuousLinearMap.id ℝ H₂) := by
  calc
    (-(phaseAxisK (E := E))).comp (-(phaseAxisK (E := E)))
        = (phaseAxisK (E := E)).comp (phaseAxisK (E := E)) := by
            simp
    _ = -(ContinuousLinearMap.id ℝ H₂) := by
          simpa using phaseAxisK_sq_eq_neg_id (E := E)

/-- Commutant action by `J` on doubled-carrier endomorphisms. -/
@[rep_depth operator]
noncomputable def commutantAction (A : EndH) : EndH :=
  (modular_j (E := E)) * A * (modular_j (E := E))

/-- Flipping `J ↦ -J` leaves the commutant action unchanged. -/
@[rep_depth operator]
theorem commutantAction_invariant_under_modular_j_flip
    (A : EndH) :
    ((-(modular_j (E := E))) * A * (-(modular_j (E := E))))
      = commutantAction (E := E) A := by
  calc
    (-(modular_j (E := E))) * A * (-(modular_j (E := E)))
        = ((-(modular_j (E := E))) * A) * (-(modular_j (E := E))) := by
            simp [mul_assoc]
    _ = (-(modular_j (E := E) * A)) * (-(modular_j (E := E))) := by
          simp [neg_mul]
    _ = (modular_j (E := E) * A) * (modular_j (E := E)) := by
          simpa using neg_mul_neg (modular_j (E := E) * A) (modular_j (E := E))
    _ = commutantAction (E := E) A := by
          simp [commutantAction, mul_assoc]

/-- The modular transport generator flips sign when the seed flips sign. -/
@[rep_depth transport]
theorem modularTransportGenerator_neg
    (hMod : EndH) :
    modularTransportGenerator (E := E) (-hMod)
      = -(modularTransportGenerator (E := E) hMod) := by
  unfold modularTransportGenerator
  simp

/-- Time-reversal equivalence for modular transport under seed sign flip. -/
@[rep_depth transport]
theorem modularTransportFlow_neg_generator_eq_time_reverse
    (hMod : EndH) (τ : ℝ) :
    modularTransportFlow (E := E) (-hMod) τ
      = modularTransportFlow (E := E) hMod (-τ) := by
  unfold modularTransportFlow
  rw [modularTransportGenerator_neg (E := E) hMod]
  congr 1
  simp [smul_neg, neg_smul]

/-- Intrinsic `K`-rotation is equivalent under `K ↦ -K, τ ↦ -τ`. -/
@[rep_depth transport]
theorem phaseAxisFlow_flip_eq_time_reverse
    (τ : ℝ) :
    NormedSpace.exp (τ • (-(phaseAxisK (E := E))))
      = NormedSpace.exp ((-τ) • (phaseAxisK (E := E))) := by
  simp [smul_neg, neg_smul]

/-- Vacuum-orientation flip swaps plus/minus polarizations. -/
@[rep_depth krein]
theorem orientationFlip_swaps_vacuum_polarizations_plus :
    InfoGeometry.Krein.Prelude.vacuumPolarizationPlus
        (E := E) (InfoGeometry.Krein.Prelude.vacuumChoicePlus (E := E))
      =
    InfoGeometry.Krein.Prelude.vacuumPolarizationMinus
        (E := E) (InfoGeometry.Krein.Prelude.vacuumChoiceMinus (E := E)) := by
  simpa using
    (InfoGeometry.Krein.Prelude.vacuumChoice_switch_swaps_polarizations_plus (E := E))

/-- Vacuum-orientation flip swaps minus/plus polarizations. -/
@[rep_depth krein]
theorem orientationFlip_swaps_vacuum_polarizations_minus :
    InfoGeometry.Krein.Prelude.vacuumPolarizationMinus
        (E := E) (InfoGeometry.Krein.Prelude.vacuumChoicePlus (E := E))
      =
    InfoGeometry.Krein.Prelude.vacuumPolarizationPlus
        (E := E) (InfoGeometry.Krein.Prelude.vacuumChoiceMinus (E := E)) := by
  simpa using
    (InfoGeometry.Krein.Prelude.vacuumChoice_switch_swaps_polarizations_minus (E := E))

/-- Projector-flux orientation contract for the dictionary `[T, P±]` convention. -/
@[rep_depth transport]
theorem projectorFlux_orientation_contract (T : EndH) :
    (InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux (E := E) T
      = -(sectorExchangeObservablePlus (E := E) T))
      ∧
    (InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux (E := E) T
      = -(sectorExchangeObservableMinus (E := E) T)) := by
  exact ⟨
    plusProjectorFlux_eq_neg_sectorExchangeObservablePlus (E := E) T,
    minusProjectorFlux_eq_neg_sectorExchangeObservableMinus (E := E) T
  ⟩

/-- One-shot orientation-flip package (`K`, `τ`, and plus/minus labels). -/
@[rep_depth transport]
theorem orientationFlip_equivalence_package
    (hMod T : EndH) (τ : ℝ) :
    (-(phaseAxisK (E := E))).comp (-(phaseAxisK (E := E)))
      = -(ContinuousLinearMap.id ℝ H₂)
      ∧
    modularTransportFlow (E := E) (-hMod) τ
      = modularTransportFlow (E := E) hMod (-τ)
      ∧
    ((InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux (E := E) T
      = -(sectorExchangeObservablePlus (E := E) T))
      ∧
    (InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux (E := E) T
      = -(sectorExchangeObservableMinus (E := E) T))) := by
  refine ⟨phaseAxis_flip_sq_eq_neg_id (E := E), ?_, ?_⟩
  · exact modularTransportFlow_neg_generator_eq_time_reverse (E := E) hMod τ
  · exact projectorFlux_orientation_contract T

end Core

end InfoGeometry.Canonical.ModularOrientationContract
