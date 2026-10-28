/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornJordanIdentity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polarization of the full split Albert cubic norm

Preservation of the actual cubic polynomial is equivalent to preservation of
its existing native symmetric trilinear form.  The proofs apply to arbitrary
linear endomorphisms of the full split Albert carrier; invertibility is not
needed for this equivalence.
-/

namespace InfoGeometry.Algebra

open H3Zorn

/-- The existing Albert norm trilinear form is reconstructed from the seven
values in the complete cubic polarization identity. -/
theorem h3zornNormTrilin_polarization (x y z : H3Zorn ℝ) :
    6 * h3zornNormTrilin x y z =
      normCubic (x + y + z) - normCubic (x + y) - normCubic (x + z) -
        normCubic (y + z) + normCubic x + normCubic y + normCubic z := by
  dsimp [h3zornNormTrilin]
  simp only [normCubic_add, adjointQuad_add, traceBilin_add_left,
    traceBilin_add_right, traceBilin_crossProduct_assoc]
  ring

/-- A scalar similitude of the cubic polynomial transports its polarized
form by exactly the same factor. The scalar need not be invertible here. -/
theorem h3zornNormTrilin_similitude_of_normCubic_similitude
    (f : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ) (r : ℝ)
    (hN : ∀ x : H3Zorn ℝ, normCubic (f x) = r * normCubic x)
    (x y z : H3Zorn ℝ) :
    h3zornNormTrilin (f x) (f y) (f z) = r * h3zornNormTrilin x y z := by
  have hscaled : 6 * h3zornNormTrilin (f x) (f y) (f z) =
      r * (6 * h3zornNormTrilin x y z) := by
    rw [h3zornNormTrilin_polarization, h3zornNormTrilin_polarization]
    simp only [← map_add, hN]
    ring
  linarith

/-- A linear endomorphism preserving the actual Albert cubic norm preserves
its full polarized trilinear form. -/
theorem h3zornNormTrilin_preserved_of_normCubic_preserved
    (f : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ)
    (hN : ∀ x : H3Zorn ℝ, normCubic (f x) = normCubic x)
    (x y z : H3Zorn ℝ) :
    h3zornNormTrilin (f x) (f y) (f z) = h3zornNormTrilin x y z := by
  have hxyz := hN (x + y + z)
  have hxy := hN (x + y)
  have hxz := hN (x + z)
  have hyz := hN (y + z)
  simp only [map_add] at hxyz hxy hxz hyz
  have hscaled :
      6 * h3zornNormTrilin (f x) (f y) (f z) =
        6 * h3zornNormTrilin x y z := by
    rw [h3zornNormTrilin_polarization, h3zornNormTrilin_polarization,
      hxyz, hxy, hxz, hyz, hN x, hN y, hN z]
  linarith

/-- Preservation of the polarized Albert norm implies preservation of the
cubic norm by evaluation on the triple diagonal. -/
theorem normCubic_preserved_of_h3zornNormTrilin_preserved
    (f : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ)
    (hT : ∀ x y z : H3Zorn ℝ,
      h3zornNormTrilin (f x) (f y) (f z) = h3zornNormTrilin x y z)
    (x : H3Zorn ℝ) : normCubic (f x) = normCubic x := by
  calc
    normCubic (f x) = h3zornNormTrilin (f x) (f x) (f x) :=
      (h3zornCubicJordanDatum.normTrilin_self (f x)).symm
    _ = h3zornNormTrilin x x x := hT x x x
    _ = normCubic x := h3zornCubicJordanDatum.normTrilin_self x

/-- The cubic polynomial and the native symmetric trilinear form determine
exactly the same linear endomorphisms of the full Albert carrier. -/
theorem normCubic_preserved_iff_h3zornNormTrilin_preserved
    (f : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ) :
    (∀ x : H3Zorn ℝ, normCubic (f x) = normCubic x) ↔
      ∀ x y z : H3Zorn ℝ,
        h3zornNormTrilin (f x) (f y) (f z) = h3zornNormTrilin x y z := by
  constructor
  · exact fun hN => h3zornNormTrilin_preserved_of_normCubic_preserved f hN
  · exact fun hT => normCubic_preserved_of_h3zornNormTrilin_preserved f hT

end InfoGeometry.Algebra
