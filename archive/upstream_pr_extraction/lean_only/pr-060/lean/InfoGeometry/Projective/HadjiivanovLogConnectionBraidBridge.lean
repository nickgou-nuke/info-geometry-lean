import InfoGeometry.Projective.HadjiivanovLogConnectionBridge
import InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameEquivariance

/-!
# Braid transport of algebraic Hadjiivanov logarithmic connections

This owner supplies the explicit common-fiber contract needed to transport a
color-indexed family of square-zero residues.  A `B₃` representation acts by
linear equivalences on the finite fiber, and each nilpotent direction obeys an
intertwining law with the underlying color permutation.

The resulting connection naturality is algebraic on
`ℂ[T,T⁻¹] ⊗ V`.  No identification with a separately owned Jones carrier,
fundamental group, analytic holonomy, or physical braid transport is asserted.
-/

namespace InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge

open scoped TensorProduct
open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

abbrev BraidGroup :=
  InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance.BoundaryBraidGroup

/-- A common finite fiber carrying braid-equivariant nilpotent residues. -/
structure LogResidueBraidFrame (V : Type*) [AddCommGroup V] [Module ℂ V] where
  representation : BraidGroup →* (V ≃ₗ[ℂ] V)
  weight : ℂ
  nilpotent : Fin 3 → V →ₗ[ℂ] V
  nilpotent_sq : ∀ a, (nilpotent a).comp (nilpotent a) = 0
  nilpotent_intertwines : ∀ g a v,
    representation g (nilpotent a v) =
      nilpotent (braidPermutation g a) (representation g v)

/-- The logarithmic residue selected by one color/frame direction. -/
def frameResidue (F : LogResidueBraidFrame V) (a : Fin 3) : LogResidue V where
  weight := F.weight
  nilpotent := F.nilpotent a
  nilpotent_sq := F.nilpotent_sq a

@[simp] theorem frameResidue_weight (F : LogResidueBraidFrame V) (a : Fin 3) :
    (frameResidue F a).weight = F.weight := rfl

@[simp] theorem frameResidue_nilpotent
    (F : LogResidueBraidFrame V) (a : Fin 3) :
    (frameResidue F a).nilpotent = F.nilpotent a := rfl

/-- Residue intertwining follows from the explicit nilpotent-frame contract. -/
theorem residueOperator_intertwines
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3) (v : V) :
    F.representation g (residueOperator (frameResidue F a) v) =
      residueOperator (frameResidue F (braidPermutation g a))
        (F.representation g v) := by
  simp only [residueOperator_apply, frameResidue_weight, frameResidue_nilpotent,
    map_add, map_smul]
  rw [F.nilpotent_intertwines]

/-- Fiber braid transport lifted trivially across the Laurent base. -/
def sectionBraidTransport (F : LogResidueBraidFrame V) (g : BraidGroup) :
    LogSection V →ₗ[ℂ] LogSection V :=
  TensorProduct.map LinearMap.id (F.representation g).toLinearMap

@[simp] theorem sectionBraidTransport_tmul
    (F : LogResidueBraidFrame V) (g : BraidGroup)
    (f : HadjiivanovLogConnectionBridge.LaurentRing) (v : V) :
    sectionBraidTransport F g (f ⊗ₜ[ℂ] v) =
      f ⊗ₜ[ℂ] F.representation g v := by
  simp [sectionBraidTransport]

theorem sectionBraidTransport_one
    (F : LogResidueBraidFrame V) (x : LogSection V) :
    sectionBraidTransport F 1 x = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro f v
    simp
  · intro x y hx hy
    simp [map_add, hx, hy]

theorem sectionBraidTransport_mul
    (F : LogResidueBraidFrame V) (g k : BraidGroup) (x : LogSection V) :
    sectionBraidTransport F (g * k) x =
      sectionBraidTransport F g (sectionBraidTransport F k x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro f v
    simp
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Connection naturality on a pure Laurent/fiber tensor. -/
theorem logarithmicConnection_braid_tmul
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3)
    (f : HadjiivanovLogConnectionBridge.LaurentRing) (v : V) :
    logarithmicConnection (frameResidue F (braidPermutation g a))
        (sectionBraidTransport F g (f ⊗ₜ[ℂ] v)) =
      sectionBraidTransport F g
        (logarithmicConnection (frameResidue F a) (f ⊗ₜ[ℂ] v)) := by
  simp only [sectionBraidTransport_tmul, logarithmicConnection_tmul,
    frameResidue_weight, frameResidue_nilpotent, map_add]
  rw [F.nilpotent_intertwines]
  simp

/-- Full-carrier braid equivariance of the algebraic logarithmic connection. -/
theorem logarithmicConnection_braid
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3)
    (x : LogSection V) :
    logarithmicConnection (frameResidue F (braidPermutation g a))
        (sectionBraidTransport F g x) =
      sectionBraidTransport F g (logarithmicConnection (frameResidue F a) x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · exact logarithmicConnection_braid_tmul F g a
  · intro x y hx hy
    simp [map_add, hx, hy]

theorem logarithmicConnection_braid_comp
    (F : LogResidueBraidFrame V) (g : BraidGroup) (a : Fin 3) :
    (logarithmicConnection (frameResidue F (braidPermutation g a))).comp
        (sectionBraidTransport F g) =
      (sectionBraidTransport F g).comp
        (logarithmicConnection (frameResidue F a)) := by
  apply LinearMap.ext
  intro x
  exact logarithmicConnection_braid F g a x

end

end InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge
