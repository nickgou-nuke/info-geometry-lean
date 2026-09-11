import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Canonical modular rotor flow identities

This file avoids local rotor, trace-functional, trace-algebra, commutator, and
eigenstate wrapper definitions.  The finite algebraic statements are written
directly with functions, multiplication, subtraction, `algebraMap`, and explicit
hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.ModularRotorFlow

/-- Rotor conjugation composes as a one-parameter action under explicit homomorphism laws. -/
theorem modular_flow_group_action {A : Type*} [Ring A]
    (rotor rotorInv : ℝ → A)
    (hom : ∀ t1 t2, rotor (t1 + t2) = rotor t1 * rotor t2)
    (hom_inv : ∀ t1 t2, rotorInv (t1 + t2) = rotorInv t2 * rotorInv t1)
    (t1 t2 : ℝ) (X : A) :
    rotor (t1 + t2) * X * rotorInv (t1 + t2) =
      rotor t1 * (rotor t2 * X * rotorInv t2) * rotorInv t1 := by
  rw [hom, hom_inv]
  simp only [mul_assoc]

/-- The trace of a commutator vanishes under explicit subtraction and cyclicity laws. -/
theorem trace_commutator_zero {A : Type*} [Ring A]
    (tau : A → ℝ)
    (map_sub : ∀ x y : A, tau (x - y) = tau x - tau y)
    (map_cyclic : ∀ x y : A, tau (x * y) = tau (y * x))
    (H X : A) :
    tau (H * X - X * H) = 0 := by
  rw [map_sub]
  have h_cyc : tau (H * X) = tau (X * H) := map_cyclic H X
  rw [h_cyc]
  ring

/-- Nonzero modular eigenvalue forces zero trace expectation, from explicit laws. -/
theorem modular_spectral_selection_rule {A : Type*} [Ring A] [Algebra ℝ A]
    (tau : A → ℝ)
    (map_sub : ∀ x y : A, tau (x - y) = tau x - tau y)
    (map_cyclic : ∀ x y : A, tau (x * y) = tau (y * x))
    (map_scale : ∀ (c : ℝ) (x : A), tau ((algebraMap ℝ A c) * x) = c * tau x)
    (H X : A) (lam : ℝ)
    (h_eigen : H * X - X * H = (algebraMap ℝ A lam) * X)
    (h_nonzero : lam ≠ 0) :
    tau X = 0 := by
  have h_tr := trace_commutator_zero tau map_sub map_cyclic H X
  rw [h_eigen] at h_tr
  rw [map_scale lam X] at h_tr
  exact (mul_eq_zero.mp h_tr).resolve_left h_nonzero

end InfoGeometry.Canonical.ModularRotorFlow
