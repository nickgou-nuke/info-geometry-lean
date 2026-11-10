/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Topology.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

/-!
# The singleton vacuum space and its two-term cochain model

This file records only consequences of the explicit singleton space `Unit`.
Its contraction and the vanishing of the displayed degree-one cochain space are
proved directly.  The cochain calculation is algebraic: it does not identify
this model with analytic de Rham cohomology or with a physical vacuum.
-/

namespace VacuumTopology

/-- The topological space consisting of one point. -/
abbrev VacuumSpace := Unit

/-- Every two points of the chosen space agree. -/
theorem vacuum_points_equal (x y : VacuumSpace) : x = y := by
  cases x
  cases y
  rfl

/-- Every function out of the singleton space is constant at its value there. -/
theorem vacuum_function_is_constant {α : Sort*} (f : VacuumSpace → α) :
    f = fun _ => f () := by
  funext x
  cases x
  rfl

/-- The explicit constant homotopy from the singleton to its distinguished point. -/
def vacuumContraction : ℝ × VacuumSpace → VacuumSpace := fun _ => ()

/-- The contraction map is continuous. -/
theorem vacuumContraction_continuous : Continuous vacuumContraction :=
  continuous_const

/-- At time zero the contraction fixes every point. -/
theorem vacuumContraction_zero (x : VacuumSpace) : vacuumContraction (0, x) = x := by
  cases x
  rfl

/-- At time one the contraction lands at the distinguished point. -/
theorem vacuumContraction_one (x : VacuumSpace) : vacuumContraction (1, x) = () := by
  rfl

/-- The underlying singleton space is contractible via `vacuumContraction`. -/
theorem vacuum_is_contractible :
    ∃ H : ℝ × VacuumSpace → VacuumSpace,
      Continuous H ∧ (∀ x, H (0, x) = x) ∧ (∀ x, H (1, x) = ()) := by
  exact ⟨vacuumContraction, vacuumContraction_continuous,
    vacuumContraction_zero, vacuumContraction_one⟩

/-- The singleton has one element. -/
theorem vacuum_singleton_cardinality : Fintype.card VacuumSpace = 1 :=
  Fintype.card_unit

/-! ## A finite cochain model -/

/-- Degree-zero cochains on the one-point set, with real coefficients. -/
abbrev VacuumZeroForm := VacuumSpace → ℝ

/-- Degree-one cochains are functions on the empty set, hence form the zero space. -/
abbrev VacuumOneForm := Empty → ℝ

/-- The degree-zero differential into the zero degree-one space. -/
def exterior_derivative (_f : VacuumZeroForm) : VacuumOneForm := fun e => nomatch e

/-- A chosen degree-zero cochain. -/
def ln_Omega : VacuumZeroForm := fun _ => 0

/-- Its degree-one differential. -/
def d_ln_Omega : VacuumOneForm := exterior_derivative ln_Omega

/-- Every degree-one cochain in this explicit model is zero. -/
theorem vacuum_one_form_eq_zero (ω : VacuumOneForm) : ω = 0 := by
  funext e
  exact Empty.elim e

/-- Every degree-one cochain is exact in the displayed two-term cochain model. -/
theorem vacuum_degree_one_exact (ω : VacuumOneForm) :
    ∃ f : VacuumZeroForm, exterior_derivative f = ω := by
  refine ⟨ln_Omega, ?_⟩
  exact (vacuum_one_form_eq_zero d_ln_Omega).trans (vacuum_one_form_eq_zero ω).symm

/-- The chosen cochain has zero differential, as a function on the empty set. -/
theorem vacuum_d_ln_Omega_eq_zero : d_ln_Omega = 0 :=
  vacuum_one_form_eq_zero d_ln_Omega

end VacuumTopology
