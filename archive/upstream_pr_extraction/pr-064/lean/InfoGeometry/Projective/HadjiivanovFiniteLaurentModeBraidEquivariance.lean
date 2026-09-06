import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeMonodromyReadout
import InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge

/-!
# Braid equivariance of finite Laurent-mode frames

The common-fiber braid representation is applied pointwise to every Laurent
mode.  It intertwines both the color-indexed finite logarithmic connections and
their Hadjiivanov readouts, and it is compatible with successor embeddings.

This is conditional operator equivariance on the declared common carrier.  It
does not identify the braid group with a boundary fundamental group.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeBraidEquivariance

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionBraidBridge
open HadjiivanovLogConnectionReadoutBridge
open HadjiivanovFiniteLaurentModeTower
open HadjiivanovFiniteLaurentModeMonodromyReadout
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Pointwise braid transport on a finite Laurent window. -/
def finiteModeBraidTransport
    (F : LogResidueBraidFrame V) (g : BraidGroup) (n : ℕ) :
    FiniteModeSection n V →ₗ[ℂ] FiniteModeSection n V where
  toFun x i := F.representation g (x i)
  map_add' x y := by
    funext i
    simp
  map_smul' c x := by
    funext i
    simp

@[simp] theorem finiteModeBraidTransport_apply
    (F : LogResidueBraidFrame V) (g : BraidGroup) (n : ℕ)
    (x : FiniteModeSection n V) (i : Fin (2 * n + 1)) :
    finiteModeBraidTransport F g n x i = F.representation g (x i) := rfl

theorem finiteModeBraidTransport_one
    (F : LogResidueBraidFrame V) (n : ℕ) :
    finiteModeBraidTransport F 1 n = LinearMap.id := by
  ext x i
  simp

theorem finiteModeBraidTransport_mul
    (F : LogResidueBraidFrame V) (g k : BraidGroup) (n : ℕ) :
    finiteModeBraidTransport F (g * k) n =
      (finiteModeBraidTransport F g n).comp
        (finiteModeBraidTransport F k n) := by
  ext x i
  simp

/-- Braid transport intertwines the color-indexed finite logarithmic
connections. -/
theorem finiteModeConnection_braid
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3) (n : ℕ) :
    (finiteModeConnection (frameResidue F (braidPermutation g a)) n).comp
        (finiteModeBraidTransport F g n) =
      (finiteModeBraidTransport F g n).comp
        (finiteModeConnection (frameResidue F a) n) := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [LinearMap.comp_apply, finiteModeConnection_apply,
    finiteModeBraidTransport_apply, map_add, map_smul]
  rw [residueOperator_intertwines]

/-- Braid transport intertwines the color-indexed finite Hadjiivanov
readouts. -/
theorem finiteModeMonodromyReadout_braid
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3) (n : ℕ) :
    (finiteModeMonodromyReadout
        (frameResidue F (braidPermutation g a)) n).comp
        (finiteModeBraidTransport F g n) =
      (finiteModeBraidTransport F g n).comp
        (finiteModeMonodromyReadout (frameResidue F a) n) := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [LinearMap.comp_apply, finiteModeMonodromyReadout_apply,
    finiteModeBraidTransport_apply]
  exact (residueMonodromyEnd_braid F g a (x i)).symm

/-- Pointwise braid transport is compatible with finite-window bonding. -/
theorem finiteModeBraidTransport_modeBond
    (F : LogResidueBraidFrame V) (g : BraidGroup) (n : ℕ) :
    (finiteModeBraidTransport F g (n + 1)).comp (modeBond n) =
      (modeBond n).comp (finiteModeBraidTransport F g n) := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases h : IsInterior n i
  · rw [LinearMap.comp_apply, LinearMap.comp_apply,
      finiteModeBraidTransport_apply,
      modeBond_apply_interior n x i h,
      modeBond_apply_interior n (finiteModeBraidTransport F g n x) i h,
      finiteModeBraidTransport_apply]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply,
      finiteModeBraidTransport_apply,
      modeBond_apply_boundary n x i h,
      modeBond_apply_boundary n (finiteModeBraidTransport F g n x) i h]
    simp

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeBraidEquivariance
