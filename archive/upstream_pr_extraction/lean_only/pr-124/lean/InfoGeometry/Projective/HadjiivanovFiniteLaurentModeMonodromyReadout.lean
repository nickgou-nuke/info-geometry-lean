import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeTower
import InfoGeometry.Projective.HadjiivanovFiniteLaurentZeroModeReadout
import InfoGeometry.Projective.HadjiivanovLogConnectionReadoutCommutationBridge

/-!
# Finite Laurent-mode Hadjiivanov readout

The fiber Hadjiivanov readout is applied independently to every Laurent mode.
Because it commutes with the residue and is complex-linear, it commutes with
the finite logarithmic connection.  Pointwise action also preserves the
zero-boundary successor embeddings.

This is a finite algebraic naturality statement, not analytic monodromy or
parallel transport.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeMonodromyReadout

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionReadoutBridge
open HadjiivanovLogConnectionReadoutCommutationBridge
open HadjiivanovFiniteLaurentModeTower
open HadjiivanovFiniteLaurentZeroModeReadout

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Apply the phase-decorated residue readout independently at every mode of a
finite symmetric Laurent window. -/
def finiteModeMonodromyReadout (R : LogResidue V) (n : ℕ) :
    FiniteModeSection n V →ₗ[ℂ] FiniteModeSection n V where
  toFun x i := residueMonodromyEnd R (x i)
  map_add' x y := by
    funext i
    simp
    abel
  map_smul' c x := by
    funext i
    simp

@[simp] theorem finiteModeMonodromyReadout_apply
    (R : LogResidue V) (n : ℕ) (x : FiniteModeSection n V)
    (i : Fin (2 * n + 1)) :
    finiteModeMonodromyReadout R n x i = residueMonodromyEnd R (x i) := rfl

/-- The pointwise Hadjiivanov readout commutes with the finite logarithmic
connection on every Laurent window. -/
theorem finiteModeConnection_monodromyReadout
    (R : LogResidue V) (n : ℕ) :
    (finiteModeConnection R n).comp (finiteModeMonodromyReadout R n) =
      (finiteModeMonodromyReadout R n).comp (finiteModeConnection R n) := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [LinearMap.comp_apply, finiteModeConnection_apply,
    finiteModeMonodromyReadout_apply, map_add, map_smul]
  rw [residueOperator_monodromyReadout_commute]

/-- Pointwise Hadjiivanov readout is compatible with the zero-boundary
successor embeddings of symmetric Laurent windows. -/
theorem finiteModeMonodromyReadout_modeBond
    (R : LogResidue V) (n : ℕ) :
    (finiteModeMonodromyReadout R (n + 1)).comp (modeBond n) =
      (modeBond n).comp (finiteModeMonodromyReadout R n) := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases h : IsInterior n i
  · rw [LinearMap.comp_apply, LinearMap.comp_apply,
      finiteModeMonodromyReadout_apply,
      modeBond_apply_interior n x i h,
      modeBond_apply_interior n (finiteModeMonodromyReadout R n x) i h,
      finiteModeMonodromyReadout_apply]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply,
      finiteModeMonodromyReadout_apply,
      modeBond_apply_boundary n x i h,
      modeBond_apply_boundary n (finiteModeMonodromyReadout R n x) i h]
    simp

/-- Central-mode extraction of the finite readout is the original fiber
Hadjiivanov readout. -/
theorem centralModeReadout_finiteModeMonodromyReadout
    (R : LogResidue V) (n : ℕ) (x : FiniteModeSection n V) :
    centralModeReadout n (finiteModeMonodromyReadout R n x) =
      residueMonodromyEnd R (centralModeReadout n x) := rfl

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeMonodromyReadout
