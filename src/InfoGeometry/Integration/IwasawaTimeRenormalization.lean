import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic

namespace InfoGeometry.Integration.IwasawaTimeRenormalization

variable {R : Type*} [Ring R]

/-! # Algebraic scale normalization

The carrier below is only a ring-level triple: a scalar prefactor, an
invertible scale, and a unipotent component. It does not assert a Lie-group
Iwasawa decomposition. The normalization theorem states precisely the
commutation hypothesis needed to cancel the scale and its inverse. -/

structure RenormalizationData (R : Type*) [Ring R] where
  prefactor : R
  scale : Rˣ
  unipotent : R

/-- The unipotent deviation from the multiplicative identity. -/
def ghost (Ops : RenormalizationData R) : R := Ops.unipotent - 1

/-- A vanishing-square deviation gives the corresponding quadratic
accumulation formula. -/
theorem unipotent_time_accumulation (Ops : RenormalizationData R)
    (hN : ghost Ops * ghost Ops = 0) :
    Ops.unipotent * Ops.unipotent = 1 + 2 * ghost Ops := by
  have hNrep : Ops.unipotent = 1 + ghost Ops := by
    dsimp [ghost]
    noncomm_ring
  rw [hNrep]
  calc
    (1 + ghost Ops) * (1 + ghost Ops) =
        1 + 2 * ghost Ops + ghost Ops * ghost Ops := by noncomm_ring
    _ = 1 + 2 * ghost Ops := by rw [hN]; noncomm_ring

/-- Conjugation of the unipotent component by the invertible scale. -/
def normalizedStep (Ops : RenormalizationData R) : R :=
  (Ops.scale : R) * Ops.unipotent * (↑Ops.scale⁻¹ : R)

/-- The scale cancels when it commutes with the unipotent component. -/
theorem normalizedStep_eq_unipotent (Ops : RenormalizationData R)
    (hcomm : (Ops.scale : R) * Ops.unipotent =
      Ops.unipotent * (Ops.scale : R)) :
    normalizedStep Ops = Ops.unipotent := by
  unfold normalizedStep
  calc
    (Ops.scale : R) * Ops.unipotent * (↑Ops.scale⁻¹ : R) =
        (Ops.unipotent * (Ops.scale : R)) * (↑Ops.scale⁻¹ : R) := by rw [hcomm]
    _ = Ops.unipotent * ((Ops.scale : R) * (↑Ops.scale⁻¹ : R)) := by rw [mul_assoc]
    _ = Ops.unipotent := by rw [Units.mul_inv, mul_one]

/-- The prefactor times the normalized step reduces to the prefactor times
the unipotent component under the same commutation condition. -/
theorem renormalizedState_eq_prefactor_mul_unipotent (Ops : RenormalizationData R)
    (hcomm : (Ops.scale : R) * Ops.unipotent =
      Ops.unipotent * (Ops.scale : R)) :
    Ops.prefactor * normalizedStep Ops = Ops.prefactor * Ops.unipotent := by
  rw [normalizedStep_eq_unipotent Ops hcomm]

end InfoGeometry.Integration.IwasawaTimeRenormalization
