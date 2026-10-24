/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KleinBottleSewing
import InfoGeometry.Canonical.AndreevReflectionKreinHorizonBridge
import InfoGeometry.Canonical.KleinSewingDefect

/-! # Andreev–Klein Chiral Grading Bridge

Connects the existing Andreev particle-hole channel exchange with the existing
Klein sewing chiral grading. Proves that the channel exchange conjugates the
chiral grading to its negative, and derives the resulting defect law. This is
an algebraic identity on the existing carriers; it does not assert a physical
BdG Hamiltonian, superconducting boundary, or particle-production theorem.
-/
namespace InfoGeometry.Canonical.AndreevKleinChiralBridge

open Matrix Complex
open AndreevReflectionKreinHorizonBridge

section General
variable {A G : Type*} [Ring A] [AddCommGroup G]

/-- Channel exchange conjugates a grading to its negative. -/
theorem channel_exchange_conjugates_grading (q γ : A)
    (hq : q * q = 1) (hanti : q * γ = - (γ * q)) :
    q * γ * q = - γ := by
  rw [hanti, neg_mul, mul_assoc, hq, mul_one]

/-- The same conjugation law for the product of two anticommuting involutions. -/
theorem double_exchange_identity (q γ : A)
    (hq : q * q = 1) (hanti : q * γ = - (γ * q)) :
    q * γ * q * q = - γ * q := by
  rw [channel_exchange_conjugates_grading q γ hq hanti]

/-- The Klein sewing defect is governed by the channel-exchange law:
    conjugation by the sewing involution reverses the chiral trace. -/
theorem sewing_defect_from_exchange (τ : A →+ G)
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) (q γ ρ : A)
    (hq : q * q = 1) (hanti : q * γ = - (γ * q)) :
    τ (γ * (q * ρ * q - ρ)) = - (2 • τ (γ * ρ)) :=
  InfoGeometry.Canonical.KleinSewingDefect.trace_sewing_defect τ hτ q γ ρ hq hanti

end General

/-- The concrete Klein sewing switch conjugates the tilt to its negative,
    which is the Andreev–Klein channel-exchange law. -/
theorem concrete_switch_tilt_exchange :
    switch * tilt * switch = - tilt := by
  exact channel_exchange_conjugates_grading switch tilt
    (by simpa only [pow_two] using switch_sq) switch_tilt_anticomm

/-- The concrete Andreev particle-hole matrix is an involution. -/
theorem concrete_particle_hole_involution :
    Andreev.particleHoleC * Andreev.particleHoleC = 1 := by
  exact Andreev.particle_hole_C_squared_is_identity

/-- The concrete Krein metric is an involution. -/
theorem concrete_krein_involution :
    kreinJ * kreinJ = 1 := by
  exact krein_J_squared_is_identity

/-- The concrete sewing defect trace, restated through the exchange law. -/
theorem concrete_defect_trace (s : BoundaryState) :
    Matrix.trace (tilt * (switch * s.rho * switch - s.rho)) = - (2 • chiralIndex s) := by
  exact InfoGeometry.Canonical.KleinSewingDefect.boundary_defect_trace s

/-- Nonvacuity: the existing normalized pure boundary state has nonzero defect. -/
theorem concrete_nonzero_defect :
    Matrix.trace (tilt * (switch * concreteBoundaryState.rho * switch - concreteBoundaryState.rho)) = (-2 : ℂ) := by
  exact InfoGeometry.Canonical.KleinSewingDefect.concrete_boundary_defect

end InfoGeometry.Canonical.AndreevKleinChiralBridge
