/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornAutomorphismConjugation
import InfoGeometry.Algebra.H3ZornInfinitesimalReconstruction
import InfoGeometry.Algebra.H3ZornOperatorNoncommutativity

/-!
# Cubic geometry acting on full Albert operator Lie algebras

This module connects the polynomial geometry to the native noncommutative
operator constructions. A cubic-norm similitude conjugates the infinitesimal
cubic stabilizer. A cubic-norm isometry fixing the distinguished identity
reconstructs a Jordan automorphism and hence conjugates every derivation.

The actual inclusion order is Mathlib's `LieSubalgebra` partial order. The
proved infinitesimal reconstruction inclusion is one direction only; no
exceptional dimension, simplicity, or automorphism-classification conclusion
is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn TrilinearStabilizer

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The infinitesimal stabilizer of the full Albert cubic norm in the native
endomorphism Lie algebra. -/
def h3zornCubicStabilizer : LieSubalgebra ℝ (Module.End ℝ (H3Zorn ℝ)) :=
  trilinearStabilizer h3zornNormTrilin

/-- A similitude of the actual cubic polynomial transports its infinitesimal
stabilizer, with no fixed-unit hypothesis. -/
theorem h3zornCubicStabilizer_map_of_normSimilitude
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) :
    h3zornCubicStabilizer.map e.lieConj.toLieHom = h3zornCubicStabilizer :=
  map_trilinearStabilizer_lieConj h3zornNormTrilin h3zornNormTrilin e u
    (h3zornNormTrilin_similitude_of_normCubic_similitude e.toLinearMap u hN)

/-- The resulting equivalence is a native Lie equivalence, with bracket
preservation inherited from genuine noncommutative operator conjugation. -/
def h3zornCubicStabilizerLieEquivOfNormSimilitude
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) :
    h3zornCubicStabilizer ≃ₗ⁅ℝ⁆ h3zornCubicStabilizer :=
  e.lieConj.ofSubalgebras _ _ (h3zornCubicStabilizer_map_of_normSimilitude e u hN)

@[simp] theorem h3zornCubicStabilizerLieEquivOfNormSimilitude_apply
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x)
    (D : h3zornCubicStabilizer) :
    (h3zornCubicStabilizerLieEquivOfNormSimilitude e u hN D :
      Module.End ℝ (H3Zorn ℝ)) = e.lieConj (D : Module.End ℝ (H3Zorn ℝ)) := rfl

/-- A cubic-norm isometry fixing the unit transports every multiplication
operator of the actual Albert product. -/
theorem h3zorn_lieConj_jordanLmul_of_norm_and_unit
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (hN : ∀ x, normCubic (e x) = normCubic x) (h1 : e 1 = 1) (x : H3Zorn ℝ) :
    e.lieConj (jordanLmul (R := ℝ) x) = jordanLmul (R := ℝ) (e x) :=
  (h3zornJordanAutOfNorm e hN h1).lieConj_jordanLmul x

/-- The polynomial/basepoint assumptions alone produce a native equivalence
of the full derivation Lie algebra. -/
def h3zornDerivationLieEquivOfNorm
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (hN : ∀ x, normCubic (e x) = normCubic x) (h1 : e 1 = 1) :
    H3ZornF4Derivations ≃ₗ⁅ℝ⁆ H3ZornF4Derivations :=
  (h3zornJordanAutOfNorm e hN h1).derivationLieEquiv

@[simp] theorem h3zornDerivationLieEquivOfNorm_apply
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (hN : ∀ x, normCubic (e x) = normCubic x) (h1 : e 1 = 1)
    (D : H3ZornF4Derivations) :
    (h3zornDerivationLieEquivOfNorm e hN h1 D : Module.End ℝ (H3Zorn ℝ)) =
      e.lieConj (D : Module.End ℝ (H3Zorn ℝ)) := rfl

end InfoGeometry.Algebra
