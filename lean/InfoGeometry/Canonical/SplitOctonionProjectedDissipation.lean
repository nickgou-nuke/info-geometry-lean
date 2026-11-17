/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionRegularOperators
import InfoGeometry.Physics.ProjectedOnsagerGram
import Mathlib.LinearAlgebra.Pi

/-!
# Projected associator dissipation on the full real split octonions

Multiplication and associators are computed in the existing quaternion-pair
`SplitOctonion` carrier. A faithful real linear coordinate chart supplies a
positive auxiliary dot product; it does not turn the split norm positive or
identify this nonassociative algebra with an associative matrix algebra.

The finite matrix below represents a family of first-slot associator maps,
not octonion multiplication. Applying the energy projector before those maps
produces genuine Gram/Onsager data and an exact strict-production criterion.
-/

noncomputable section

namespace SplitOctonion.ProjectedDissipation

open Matrix
open InfoGeometry.Physics.ProjectedOnsagerGram

abbrev Coordinate := Fin 4 ⊕ Fin 4

/-- The two quaternion components of the existing carrier, as a linear chart. -/
def quaternionPairEquiv : SplitOctonion ≃ₗ[ℝ] H × H where
  toFun x := (x.a, x.b)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- All eight real coordinates, via Mathlib's actual quaternion equivalence. -/
def coordinates : SplitOctonion ≃ₗ[ℝ] (Coordinate → ℝ) :=
  let q := QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1 : ℝ)
  (quaternionPairEquiv.trans (LinearEquiv.prodCongr q q)).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 4) ℝ ℝ).symm

@[simp] theorem coordinates_inl (x : SplitOctonion) (i : Fin 4) :
    coordinates x (Sum.inl i) = ![x.a.re, x.a.imI, x.a.imJ, x.a.imK] i := rfl

@[simp] theorem coordinates_inr (x : SplitOctonion) (i : Fin 4) :
    coordinates x (Sum.inr i) = ![x.b.re, x.b.imI, x.b.imJ, x.b.imK] i := rfl

/-- The positive coordinate pairing is definite on the actual octonion carrier. -/
theorem coordinate_square_eq_zero_iff (x : SplitOctonion) :
    dotProduct (coordinates x) (coordinates x) = 0 ↔ x = 0 := by
  rw [dotProduct_self_eq_zero]
  exact coordinates.map_eq_zero_iff

/-- The first-slot associator map is a difference of actual right regular maps.
Composition order is fixed: first multiply by `a`, then by `b`. -/
def firstSlotAssociator (a b : SplitOctonion) : Module.End ℝ SplitOctonion :=
  (rightRegular b).comp (rightRegular a) - rightRegular (a * b)

@[simp] theorem firstSlotAssociator_apply (a b v : SplitOctonion) :
    firstSlotAssociator a b v = associator v a b := rfl

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Stack all coordinates of a finite family of actual associator outputs. -/
def associatorFamily (a b : κ → SplitOctonion) :
    (Coordinate → ℝ) →ₗ[ℝ] ((κ × Coordinate) → ℝ) where
  toFun v p := coordinates
    (firstSlotAssociator (a p.1) (b p.1) (coordinates.symm v)) p.2
  map_add' v w := by
    ext p
    simp only [map_add, Pi.add_apply]
  map_smul' r v := by
    ext p
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- A matrix of linear associator operators, not an algebra representation. -/
def associatorMatrix (a b : κ → SplitOctonion) :
    Matrix (κ × Coordinate) Coordinate ℝ :=
  LinearMap.toMatrix' (associatorFamily a b)

omit [Fintype κ] [DecidableEq κ] in
theorem associatorMatrix_mulVec (a b : κ → SplitOctonion) (v : Coordinate → ℝ) :
    associatorMatrix a b *ᵥ v = fun p =>
      coordinates (associator (coordinates.symm v) (a p.1) (b p.1)) p.2 := by
  rw [associatorMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem associatorMatrix_mulVec_eq_zero_iff
    (a b : κ → SplitOctonion) (v : Coordinate → ℝ) :
    associatorMatrix a b *ᵥ v = 0 ↔
      ∀ k, associator (coordinates.symm v) (a k) (b k) = 0 := by
  rw [associatorMatrix_mulVec]
  constructor
  · intro hz k
    apply coordinates.injective
    rw [map_zero]
    ext i
    exact congrFun hz (k, i)
  · intro hz
    ext p
    simp [hz p.1]

/-- Projection is taken in the positive auxiliary coordinate pairing. -/
def projectedForce (h v : SplitOctonion) : SplitOctonion :=
  coordinates.symm (energyProjector (coordinates h) *ᵥ coordinates v)

/-- The explicit matrix `γ (R P)ᵀ (R P)` for a family of split associators. -/
def associatorGram (γ : ℝ) (a b : κ → SplitOctonion) (h : SplitOctonion) :
    Matrix Coordinate Coordinate ℝ :=
  projectedGram γ (associatorMatrix a b) (coordinates h)

/-- The sum of squares consists of genuine octonion associator coordinates. -/
theorem associator_production (γ : ℝ) (a b : κ → SplitOctonion)
    (h v : SplitOctonion) :
    dotProduct (coordinates v) (associatorGram γ a b h *ᵥ coordinates v) =
      γ * ∑ p : κ × Coordinate,
        (coordinates (associator (projectedForce h v) (a p.1) (b p.1)) p.2) ^ 2 := by
  unfold associatorGram
  rw [projectedGram_contraction, associatorMatrix_mulVec]
  rfl

@[simp] theorem associatorGram_energy (γ : ℝ) (a b : κ → SplitOctonion)
    (h : SplitOctonion) :
    associatorGram γ a b h *ᵥ coordinates h = 0 :=
  projectedGram_energy γ (associatorMatrix a b) (coordinates h)

theorem associator_production_eq_zero_iff (γ : ℝ) (hγ : 0 < γ)
    (a b : κ → SplitOctonion) (h v : SplitOctonion) :
    dotProduct (coordinates v) (associatorGram γ a b h *ᵥ coordinates v) = 0 ↔
      ∀ k, associator (projectedForce h v) (a k) (b k) = 0 := by
  exact (projectedGram_contraction_eq_zero_iff γ hγ
    (associatorMatrix a b) (coordinates h) (coordinates v)).trans
      (associatorMatrix_mulVec_eq_zero_iff a b _)

/-- Nonassociativity produces strict dissipation precisely when some selected
associator detects the projected force. Merely naming a subalgebra is insufficient. -/
theorem associator_production_pos_iff (γ : ℝ) (hγ : 0 < γ)
    (a b : κ → SplitOctonion) (h v : SplitOctonion) :
    0 < dotProduct (coordinates v) (associatorGram γ a b h *ᵥ coordinates v) ↔
      ∃ k, associator (projectedForce h v) (a k) (b k) ≠ 0 := by
  classical
  change 0 < dotProduct (coordinates v)
    (projectedGram γ (associatorMatrix a b) (coordinates h) *ᵥ coordinates v) ↔ _
  rw [projectedGram_contraction_pos_iff γ hγ, ne_eq,
    associatorMatrix_mulVec_eq_zero_iff]
  simp only [not_forall, projectedForce]

/-- A concrete existing Onsager interface, with its laws derived from the actual
associator maps and a nonnegative real rate. -/
def associatorMetricData (γ : ℝ) (hγ : 0 ≤ γ)
    (a b : κ → SplitOctonion) (h : SplitOctonion) :
    InfoGeometry.SuperMetriplectic.OnsagerMetricData (Coordinate → ℝ) :=
  projectedGramMetricData γ hγ (associatorMatrix a b) (coordinates h)

/-- Parenthesized computation in the actual quaternion multiplication convention. -/
theorem associator_ell_il_j :
    associator (J_g 1) (J_g (⟨0, 1, 0, 0⟩ : H))
      (⟨(⟨0, 0, 1, 0⟩ : H), 0⟩ : SplitOctonion) =
        (⟨(⟨0, 0, 0, -2⟩ : H), 0⟩ : SplitOctonion) := by
  apply SplitOctonion.ext <;> ext <;>
    norm_num [associator, J_g, mul_a, mul_b, sub_a, sub_b]

/-- The nonzero energy force `1` is perpendicular to `ell` in the auxiliary
positive pairing, so energy projection retains this associator witness. -/
theorem projectedForce_one_ell : projectedForce 1 (J_g 1) = J_g 1 := by
  unfold projectedForce
  rw [energyProjector_mulVec]
  have horth : dotProduct (coordinates (1 : SplitOctonion))
      (coordinates (J_g 1)) = 0 := by
    simp [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, J_g]
  rw [horth, zero_div, zero_smul, sub_zero, coordinates.symm_apply_apply]

/-- A concrete nonzero production witness with a nonzero energy covector.
All factors use the full nonassociative carrier; no leakage is postulated. -/
theorem positive_associator_production_witness (γ : ℝ) (hγ : 0 < γ) :
    0 < dotProduct (coordinates (J_g 1))
      (associatorGram γ
        (fun _ : Unit => J_g (⟨0, 1, 0, 0⟩ : H))
        (fun _ : Unit => (⟨(⟨0, 0, 1, 0⟩ : H), 0⟩ : SplitOctonion))
        1 *ᵥ coordinates (J_g 1)) := by
  apply (associator_production_pos_iff γ hγ _ _ _ _).mpr
  refine ⟨(), ?_⟩
  rw [projectedForce_one_ell, associator_ell_il_j]
  intro hz
  have hk := congrArg (fun x : SplitOctonion => x.a.imK) hz
  norm_num at hk

end SplitOctonion.ProjectedDissipation
