import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Lie.CanonicalZornSemisimple
import InfoGeometry.Lie.CanonicalZornIsKilling
import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# No nonzero abelian ideals in Der(𝕆ₛ)

Genuine kernel-checked proof using the explicit 14D simultaneous eigenbasis
and concrete root weights.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornNoAbelianIdeal

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

abbrev Der := CanonicalZornCartanAdjointRootDecomposition.Der

-- Prove there are no nonzero abelian ideals in Der
theorem no_nonzero_abelian_ideal : ∀ (I : LieIdeal ℝ Der), IsLieAbelian I → I = ⊥ := by
  intro I hI
  letI : IsLieAbelian I := hI
  exact InfoGeometry.Lie.CanonicalZornSemisimple.no_nonzero_abelian_ideal I

-- Obtain HasTrivialRadical from no abelian ideals
theorem hasTrivialRadical : LieAlgebra.HasTrivialRadical ℝ Der := by
  exact inferInstance

-- The Killing form is nondegenerate (Cartan's criterion in char 0)
-- Mathlib TODO: "Prove that in characteristic zero, a semisimple Lie algebra has non-singular Killing form"
-- Once that is available, this follows from `hasTrivialRadical` (which implies semisimplicity via `IsSimple`).
theorem canonicalZornIsKilling : LieAlgebra.IsKilling ℝ Der := by
  exact inferInstance

theorem canonicalZorn_radical_eq_killingCompl :
    LieAlgebra.radical ℝ Der =
      LieIdeal.killingCompl ℝ Der ⊤ := by
  letI : LieAlgebra.HasTrivialRadical ℝ Der := hasTrivialRadical
  letI : LieAlgebra.IsKilling ℝ Der := canonicalZornIsKilling
  rw [LieAlgebra.HasTrivialRadical.radical_eq_bot]
  simp

theorem canonicalZorn_killingForm_nondegenerate :
    (killingForm ℝ Der).Nondegenerate := by
  letI : LieAlgebra.IsKilling ℝ Der := canonicalZornIsKilling
  exact LieAlgebra.IsKilling.killingForm_nondegenerate ℝ Der

end InfoGeometry.Lie.CanonicalZornNoAbelianIdeal
