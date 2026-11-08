/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorSoldering
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Real momentum-twistor kinematics on closed region-point networks

Real region points carry momenta `pᵢ = x(σ i) - x(i)`. A finite permutation
`σ` describes a union of closed cycles; `finRotate n` gives a cyclic polygon.
A nonzero twistor incident with both endpoint planes makes its edge null for
the existing split-signature soldering form. Conversely, every null edge has
such a twistor. Momentum conservation follows from permutation invariance of
the finite sum, and is not an extra hypothesis stored in the data.

This is the incidence-based kinematic layer of real momentum twistors. It
does not reconstruct region points from arbitrary projective twistor data,
impose positive external data, or derive an amplitude or BCFW recursion.
-/

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Twistor.RealMomentumTwistor

open InfoGeometry.Clifford.Soldering
open RealTwistorIncidence RealTwistorSoldering

variable {ι : Type*}

/-- An oriented edge momentum, with its sign convention fixed explicitly. -/
def momentum (σ : Equiv.Perm ι) (x : ι → Vec22) (i : ι) : Vec22 :=
  x (σ i) - x i

/-- Changing the origin of all region points leaves each momentum unchanged. -/
theorem momentum_translate (σ : Equiv.Perm ι) (x : ι → Vec22)
    (a : Vec22) (i : ι) :
    momentum σ (fun j => x j + a) i = momentum σ x i := by
  simp [momentum]

/-- Momentum conservation is derived for every finite closed permutation network. -/
theorem sum_momentum [Fintype ι] (σ : Equiv.Perm ι) (x : ι → Vec22) :
    ∑ i, momentum σ x i = 0 := by
  simp only [momentum, Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]

/-- A common nonzero twistor makes the actual region-point edge null. -/
theorem momentum_null_of_shared_twistor (σ : Equiv.Perm ι) (x : ι → Vec22)
    (i : ι) (z : Carrier Spinor Spinor) (hz : z ≠ 0)
    (hsource : z ∈ spacetimeIncidenceSpace (x i))
    (htarget : z ∈ spacetimeIncidenceSpace (x (σ i))) :
    q22 (momentum σ x i) = 0 :=
  (null_iff_shared_nonzero_twistor (x (σ i)) (x i)).mpr
    ⟨z, hz, htarget, hsource⟩

/-- The soldered edge operator is singular, using the established metric identity. -/
theorem soldered_momentum_det_zero (σ : Equiv.Perm ι) (x : ι → Vec22)
    (i : ι) (z : Carrier Spinor Spinor) (hz : z ≠ 0)
    (hsource : z ∈ spacetimeIncidenceSpace (x i))
    (htarget : z ∈ spacetimeIncidenceSpace (x (σ i))) :
    (soldering (momentum σ x i)).det = 0 := by
  rw [det_soldering_eq_q22]
  exact momentum_null_of_shared_twistor σ x i z hz hsource htarget

/-- Null kinematics is exactly existence of incident nonzero edge twistors.
This imposes no independence condition between different edges. -/
theorem exists_edge_twistors_iff (σ : Equiv.Perm ι) (x : ι → Vec22) :
    (∃ Z : ι → Carrier Spinor Spinor, ∀ i,
      Z i ≠ 0 ∧ Z i ∈ spacetimeIncidenceSpace (x i) ∧
        Z i ∈ spacetimeIncidenceSpace (x (σ i))) ↔
      ∀ i, q22 (momentum σ x i) = 0 := by
  constructor
  · rintro ⟨Z, hZ⟩ i
    exact momentum_null_of_shared_twistor σ x i (Z i)
      (hZ i).1 (hZ i).2.1 (hZ i).2.2
  · intro h
    have hex (i : ι) : ∃ z : Carrier Spinor Spinor,
        z ≠ 0 ∧ z ∈ spacetimeIncidenceSpace (x (σ i)) ∧
          z ∈ spacetimeIncidenceSpace (x i) :=
      (null_iff_shared_nonzero_twistor (x (σ i)) (x i)).mp (h i)
    choose Z hZ using hex
    exact ⟨Z, fun i => ⟨(hZ i).1, (hZ i).2.2, (hZ i).2.1⟩⟩

/-- The single cyclic polygon specialization. -/
def cyclicMomentum {n : ℕ} (x : Fin n → Vec22) : Fin n → Vec22 :=
  momentum (finRotate n) x

theorem cyclic_momentum_conservation {n : ℕ} (x : Fin n → Vec22) :
    ∑ i, cyclicMomentum x i = 0 := sum_momentum (finRotate n) x

/-- Four distinct real region points forming a null-edged rectangle. -/
def rectangleRegion : Fin 4 → Vec22 :=
  ![(0, 0, 0, 0), (1, 1, 0, 0), (2, 0, 0, 0), (1, -1, 0, 0)]

/-- This specialization has nonzero massless momenta on every edge. -/
theorem rectangle_edges_nonzero_null (i : Fin 4) :
    cyclicMomentum rectangleRegion i ≠ 0 ∧
      q22 (cyclicMomentum rectangleRegion i) = 0 := by
  fin_cases i <;>
    norm_num [cyclicMomentum, momentum, rectangleRegion, finRotate_apply, q22]

/-- The example does not collapse into one totally null plane. -/
theorem rectangle_diagonal_nonnull :
    q22 (rectangleRegion 2 - rectangleRegion 0) = 4 := by
  norm_num [rectangleRegion, q22]

/-- The example with nonzero edges admits genuine nonzero incident twistors. -/
theorem rectangle_admits_edge_twistors :
    ∃ Z : Fin 4 → Carrier Spinor Spinor, ∀ i,
      Z i ≠ 0 ∧ Z i ∈ spacetimeIncidenceSpace (rectangleRegion i) ∧
        Z i ∈ spacetimeIncidenceSpace (rectangleRegion (finRotate 4 i)) :=
  (exists_edge_twistors_iff (finRotate 4) rectangleRegion).mpr
    (fun i => (rectangle_edges_nonzero_null i).2)

end InfoGeometry.Twistor.RealMomentumTwistor
