import Omega.Zeta.CyclotomicSectorIdentity
import InfoGeometry.Canonical.CyclotomicProjectorReadout

noncomputable section

namespace InfoGeometry.Algebra.CyclotomicPhasePolarization

open InfoGeometry.Canonical.CyclotomicProjector
open Omega.Zeta.CyclotomicSectorIdentity

def cyclotomicPhase (order : ℕ) : ℂ := rootOfUnity order 1

theorem cyclotomicPhase_primitive (order : ℕ) (positive : 0 < order) :
    IsPrimitiveRoot (cyclotomicPhase order) order := by
  simpa [cyclotomicPhase, rootOfUnity] using
    Complex.isPrimitiveRoot_exp order (ne_of_gt positive)

theorem cyclotomicPhase_pow_self (order : ℕ) (positive : 0 < order) :
    cyclotomicPhase order ^ order = 1 :=
  (cyclotomicPhase_primitive order positive).pow_eq_one

theorem cyclotomicPhase_ne_one (order : ℕ) (nontrivial : 1 < order) :
    cyclotomicPhase order ≠ 1 :=
  (cyclotomicPhase_primitive order (by omega)).ne_one nontrivial

theorem cyclotomic_sum_vanishing (order : ℕ) (nontrivial : 1 < order) :
    ∑ index ∈ Finset.range order, cyclotomicPhase order ^ index = 0 :=
  (cyclotomicPhase_primitive order (by omega)).geom_sum_eq_zero nontrivial

theorem triangular_root_identity :
    cyclotomicPhase 3 ^ 2 + cyclotomicPhase 3 + 1 = 0 := by
  have balanced := cyclotomic_sum_vanishing 3 (by omega)
  norm_num [Finset.sum_range_succ] at balanced
  linear_combination balanced

def phaseWeight (order index : ℕ) : ℂ :=
  (order : ℂ)⁻¹ * cyclotomicPhase order ^ index

theorem phaseWeight_two_zero_not_idempotent :
    phaseWeight 2 0 * phaseWeight 2 0 ≠ phaseWeight 2 0 := by
  norm_num [phaseWeight]

def coordinateProjector {order : ℕ} (sector : Fin order) : Fin order → ℂ :=
  fun coordinate => if coordinate = sector then 1 else 0

def phaseOperator (order : ℕ) : Fin order → ℂ :=
  fun coordinate => cyclotomicPhase order ^ coordinate.val

theorem coordinateProjector_idempotent {order : ℕ} (sector : Fin order) :
    coordinateProjector sector * coordinateProjector sector = coordinateProjector sector := by
  funext coordinate
  by_cases equal : coordinate = sector <;> simp [coordinateProjector, equal]

theorem coordinateProjectors_orthogonal {order : ℕ} (left right : Fin order)
    (distinct : left ≠ right) :
    coordinateProjector left * coordinateProjector right = 0 := by
  funext coordinate
  by_cases equal : coordinate = left
  · subst coordinate
    simp [coordinateProjector, distinct]
  · simp [coordinateProjector, equal]

theorem coordinateProjectors_complete (order : ℕ) :
    ∑ sector : Fin order, coordinateProjector sector = 1 := by
  funext coordinate
  simp [coordinateProjector, Finset.sum_apply]

theorem phaseOperator_eigen {order : ℕ} (sector : Fin order) :
    phaseOperator order * coordinateProjector sector =
      algebraMap ℂ (Fin order → ℂ) (cyclotomicPhase order ^ sector.val) *
        coordinateProjector sector := by
  funext coordinate
  by_cases equal : coordinate = sector
  · subst coordinate
    simp [phaseOperator, coordinateProjector]
  · simp [phaseOperator, coordinateProjector, equal]

def coordinateReadout (order : ℕ) :
    FourierCyclotomicReadout (K := ℂ) (phaseOperator order) order where
  ζ := cyclotomicPhase order
  projector := coordinateProjector
  idempotent := coordinateProjector_idempotent
  orthogonal := coordinateProjectors_orthogonal
  complete := coordinateProjectors_complete order
  eigen := phaseOperator_eigen

theorem phaseOperator_reconstruction (order : ℕ) :
    phaseOperator order = ∑ sector : Fin order,
      algebraMap ℂ (Fin order → ℂ) (cyclotomicPhase order ^ sector.val) *
        coordinateProjector sector :=
  spectral_reconstruction (coordinateReadout order)

theorem phaseOperator_periodic (order : ℕ) (positive : 0 < order) :
    phaseOperator order ^ order = 1 := by
  funext coordinate
  change (cyclotomicPhase order ^ coordinate.val) ^ order = 1
  rw [← pow_mul, Nat.mul_comm coordinate.val order, pow_mul,
    cyclotomicPhase_pow_self order positive, one_pow]

theorem state_reconstruction {order : ℕ} (state : Fin order → ℂ) :
    ∑ sector : Fin order, coordinateProjector sector * state = state := by
  rw [← Finset.sum_mul, coordinateProjectors_complete, one_mul]

end InfoGeometry.Algebra.CyclotomicPhasePolarization
