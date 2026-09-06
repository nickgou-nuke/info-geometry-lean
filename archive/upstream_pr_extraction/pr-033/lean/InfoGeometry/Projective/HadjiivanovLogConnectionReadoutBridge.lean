import InfoGeometry.Projective.HadjiivanovLogConnectionRankTwoBridge
import InfoGeometry.Projective.HadjiivanovLogConnectionSynthesisBridge

/-!
# Residue readouts for algebraic logarithmic connections

The square-zero residue determines a finite unipotent shear and a
phase-decorated Hadjiivanov readout on the same fiber.  These constructions
are natural under the already contracted braid transport.  Klein reversal is
recorded at the unipotent level by reversing both residue and period.

These are explicit algebraic readouts, not analytic holonomy operators.
-/

namespace InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge

open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionKleinBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionRankTwoBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance
open InfoGeometry.Clifford.LogCftMonodromy

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Finite unipotent residue readout `I + pN`. -/
def unipotentResidueReadout (R : LogResidue V) (p : ℂ) : V →ₗ[ℂ] V :=
  LinearMap.id + p • R.nilpotent

@[simp] theorem unipotentResidueReadout_apply
    (R : LogResidue V) (p : ℂ) (v : V) :
    unipotentResidueReadout R p v = v + p • R.nilpotent v := by
  simp [unipotentResidueReadout]

/-- Reversing residue and period leaves the unipotent shear unchanged. -/
theorem unipotentResidueReadout_reverse
    (R : LogResidue V) (p : ℂ) :
    unipotentResidueReadout (reverseResidue R) (-p) =
      unipotentResidueReadout R p := by
  ext v
  simp [unipotentResidueReadout]

theorem unipotentResidueReadout_comp
    (R : LogResidue V) (p q : ℂ) :
    (unipotentResidueReadout R p).comp
        (unipotentResidueReadout R q) =
      unipotentResidueReadout R (p + q) := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, unipotentResidueReadout_apply,
    map_add, map_smul, nilpotent_apply_twice, smul_zero]
  module

theorem unipotentResidueReadout_reverse_comp
    (R : LogResidue V) (p : ℂ) :
    (unipotentResidueReadout (reverseResidue R) p).comp
        (unipotentResidueReadout R p) = LinearMap.id := by
  have hreverse : unipotentResidueReadout (reverseResidue R) p =
      unipotentResidueReadout R (-p) := by
    simpa using (unipotentResidueReadout_reverse R (-p))
  rw [hreverse, unipotentResidueReadout_comp]
  simp [unipotentResidueReadout]

theorem unipotentResidueReadout_eq_id_iff
    (R : LogResidue V) (hN : R.nilpotent ≠ 0) (p : ℂ) :
    unipotentResidueReadout R p = LinearMap.id ↔ p = 0 := by
  constructor
  · intro h
    have hs : p • R.nilpotent = 0 := by
      have h' : LinearMap.id + p • R.nilpotent =
          LinearMap.id + 0 := by
        simpa [unipotentResidueReadout] using h
      exact add_left_cancel h'
    by_contra hp
    have hzero : R.nilpotent = 0 := by
      have h' := congrArg (fun L : V →ₗ[ℂ] V => p⁻¹ • L) hs
      simpa [smul_smul, hp] using h'
    exact hN hzero
  · intro hp
    simp [hp, unipotentResidueReadout]

/-- One-wrap phase-decorated Hadjiivanov readout on a generic fiber. -/
def residueMonodromyEnd (R : LogResidue V) : V →ₗ[ℂ] V :=
  lcftPhase R.weight • unipotentResidueReadout R logShearBase

@[simp] theorem residueMonodromyEnd_apply (R : LogResidue V) (v : V) :
    residueMonodromyEnd R v =
      lcftPhase R.weight • (v + logShearBase • R.nilpotent v) := by
  simp [residueMonodromyEnd]

/-- Braid transport intertwines every unipotent frame readout. -/
theorem unipotentResidueReadout_braid
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3)
    (p : ℂ) (v : V) :
    F.representation g (unipotentResidueReadout (frameResidue F a) p v) =
      unipotentResidueReadout (frameResidue F (braidPermutation g a)) p
        (F.representation g v) := by
  simp only [unipotentResidueReadout_apply, map_add, map_smul,
    frameResidue_nilpotent]
  rw [F.nilpotent_intertwines]

/-- Braid transport intertwines the phase-decorated frame readout. -/
theorem residueMonodromyEnd_braid
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3) (v : V) :
    F.representation g (residueMonodromyEnd (frameResidue F a) v) =
      residueMonodromyEnd (frameResidue F (braidPermutation g a))
        (F.representation g v) := by
  simp [residueMonodromyEnd, unipotentResidueReadout,
    F.nilpotent_intertwines]

/-- On the native rank-two fiber the generic readout is matrix action by the
existing Hadjiivanov monodromy. -/
theorem rankTwo_residueMonodromyEnd_eq_mulVecLin (h : ℂ) :
    residueMonodromyEnd (rankTwoLogResidue h) =
      Matrix.mulVecLin (hadjiivanovMonodromy h) := by
  rw [hadjiivanovMonodromy_phase_nilpotent]
  apply LinearMap.ext
  intro v
  ext i
  fin_cases i <;>
    simp [residueMonodromyEnd, unipotentResidueReadout,
      rankTwoLogResidue, nativeNilpotentEnd, jordanNilpotent] <;> ring

end

end InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge
