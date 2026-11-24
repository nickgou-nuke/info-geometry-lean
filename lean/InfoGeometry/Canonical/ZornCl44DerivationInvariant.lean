/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCl44TrialityOrthogonal
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge

/-!
# The norm pairing and composition tensor of canonical Zorn derivations

The existing native Witt-skew theorem covers every canonical Zorn derivation.
Its proof transports to the vector-matrix carrier, recovers the full fourteen
parameters through `parameterLinearEquiv.right_inv`, and applies the proved
coordinate identity for `parameterAction`.  This owner reuses that theorem.

The native Witt pairing is twice the associated bilinear form used by the
Clifford representation.  After fixing this normalization, the derivation law
proves infinitesimal invariance of the native trilinear form
`C x y z = zornBilin (x * y) z` under the diagonal derivation action.

These are finite algebraic identities.  No invariant-form hypothesis, Lie
group integration, connection, or differential gauge field is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCl44DerivationInvariant

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornCl44Triality
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge

local instance : LieRing EndCZ := LieRing.ofAssociativeRing

/-- The trace-based native Witt pairing has twice the Clifford polarization. -/
theorem nativeCanonicalWittPairing_eq_two_zornBilin (x y : ZornMatrix ℝ) :
    nativeCanonicalWittPairing x y = 2 * zornBilin x y := by
  rw [zornBilin_apply]
  dsimp [nativeCanonicalWittPairing, canonicalVectorEquiv,
    InfoGeometry.Algebra.ZornVectorMatrix.trace,
    InfoGeometry.Algebra.ZornVectorMatrix.mul,
    InfoGeometry.Algebra.ZornVectorMatrix.conj,
    InfoGeometry.Algebra.ZornVec3.dot, dot]
  simp only [Fin.sum_univ_three]
  ring

/-- Every canonical derivation is infinitesimally orthogonal for the norm pairing. -/
theorem canonicalDerivation_bilin_skew
    (D : canonicalZornDerivations) (x y : ZornMatrix ℝ) :
    zornBilin (D.1 x) y + zornBilin x (D.1 y) = 0 := by
  have h := derivation_native_witt_skew D x y
  simp only [nativeCanonicalWittPairing_eq_two_zornBilin] at h
  linarith

/-- In particular, a derivation value pairs to zero with its input. -/
theorem canonicalDerivation_bilin_self_zero
    (D : canonicalZornDerivations) (x : ZornMatrix ℝ) :
    zornBilin (D.1 x) x = 0 := by
  have h := canonicalDerivation_bilin_skew D x x
  rw [zornBilin_symm x (D.1 x), ← two_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (two_ne_zero : (2 : ℝ) ≠ 0)

/-- Every native derivation lies in the orthogonal Lie algebra for the same form. -/
theorem canonicalDerivations_le_skewAdjoint :
    canonicalZornDerivations ≤ skewAdjointLieSubalgebra zornBilin := by
  intro D hD
  change D ∈ zornBilin.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro x y
  change zornBilin (D x) y = zornBilin x (-(D y))
  rw [map_neg]
  have h := canonicalDerivation_bilin_skew ⟨D, hD⟩ x y
  linarith only [h]

/-- The actual native inclusion of derivations into the split-form orthogonal Lie algebra. -/
def derivationOrthogonalLieHom :
    canonicalZornDerivations →ₗ⁅ℝ⁆ skewAdjointLieSubalgebra zornBilin :=
  LieSubalgebra.inclusion canonicalDerivations_le_skewAdjoint

theorem derivationOrthogonalLieHom_injective :
    Function.Injective derivationOrthogonalLieHom :=
  LieSubalgebra.inclusion_injective canonicalDerivations_le_skewAdjoint

/-- The composition tensor as three nested native linear maps. -/
def zornStructureTensor :
    ZornMatrix ℝ →ₗ[ℝ] ZornMatrix ℝ →ₗ[ℝ] ZornMatrix ℝ →ₗ[ℝ] ℝ where
  toFun x := LinearMap.comp zornBilin (leftMulLinear x)
  map_add' x y := by
    ext z w
    change zornBilin ((x + y) * z) w =
      zornBilin (x * z) w + zornBilin (y * z) w
    rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul,
      map_add, LinearMap.add_apply]
  map_smul' r x := by
    ext z w
    change zornBilin ((r • x) * z) w = r • zornBilin (x * z) w
    rw [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul,
      map_smul, LinearMap.smul_apply]

@[simp] theorem zornStructureTensor_apply (x y z : ZornMatrix ℝ) :
    zornStructureTensor x y z = zornBilin (x * y) z := rfl

/-- The composition tensor is invariant under the diagonal infinitesimal derivation action. -/
theorem canonicalDerivation_structureTensor_invariant
    (D : canonicalZornDerivations) (x y z : ZornMatrix ℝ) :
    zornStructureTensor (D.1 x) y z +
      zornStructureTensor x (D.1 y) z +
      zornStructureTensor x y (D.1 z) = 0 := by
  change zornBilin (D.1 x * y) z + zornBilin (x * D.1 y) z +
    zornBilin (x * y) (D.1 z) = 0
  have h := canonicalDerivation_bilin_skew D (x * y) z
  rw [D.property x y, map_add, LinearMap.add_apply] at h
  exact h

end InfoGeometry.Canonical.ZornCl44DerivationInvariant
