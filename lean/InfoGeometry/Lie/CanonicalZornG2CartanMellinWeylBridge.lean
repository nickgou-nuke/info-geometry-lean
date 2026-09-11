import InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornCartanRootReflections

/-!
# Weyl covariance of the native Cartan Mellin character

The existing reflection owner supplies the two simple G₂ reflections on the
traceless rank-two Cartan model.  This file transports those reflections to
the canonical Cartan carrier and records the contragredient action on Mellin
spectral functionals.  No named Weyl-group quotient or analytic transform is
introduced here.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge

open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Lie.CanonicalZornCartanRootReflections
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
open InfoGeometry.Lie.CanonicalZornRootPairing
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

abbrev Cartan := CanonicalZornRootSystemComparison.Cartan

def tracelessCartanMellinCharacter
    (s : TracelessWeight →ₗ[ℝ] ℂ) (x : TracelessWeight) : ℂ :=
  Complex.exp (-(s x))

@[simp] theorem tracelessCartanMellinCharacter_zero
    (s : TracelessWeight →ₗ[ℝ] ℂ) :
    tracelessCartanMellinCharacter s 0 = 1 := by
  simp [tracelessCartanMellinCharacter]

theorem tracelessCartanMellinCharacter_add
    (s : TracelessWeight →ₗ[ℝ] ℂ) (x y : TracelessWeight) :
    tracelessCartanMellinCharacter s (x + y) =
      tracelessCartanMellinCharacter s x * tracelessCartanMellinCharacter s y := by
  unfold tracelessCartanMellinCharacter
  rw [map_add, neg_add, Complex.exp_add]

def tracelessCartanMellinDualAction
    (r : TracelessWeight →ₗ[ℝ] TracelessWeight)
    (s : TracelessWeight →ₗ[ℝ] ℂ) : TracelessWeight →ₗ[ℝ] ℂ :=
  s.comp r

theorem tracelessCartanMellinCharacter_covariant
    (r : TracelessWeight →ₗ[ℝ] TracelessWeight)
    (s : TracelessWeight →ₗ[ℝ] ℂ) (x : TracelessWeight) :
    tracelessCartanMellinCharacter s (r x) =
      tracelessCartanMellinCharacter (tracelessCartanMellinDualAction r s) x := rfl

theorem shortReflection_tracelessCartanMellin_covariant
    (s : TracelessWeight →ₗ[ℝ] ℂ) (x : TracelessWeight) :
    tracelessCartanMellinCharacter s (shortReflectionOnCartan x) =
      tracelessCartanMellinCharacter
        (tracelessCartanMellinDualAction shortReflectionOnCartan s) x :=
  tracelessCartanMellinCharacter_covariant _ _ _

theorem longReflection_tracelessCartanMellin_covariant
    (s : TracelessWeight →ₗ[ℝ] ℂ) (x : TracelessWeight) :
    tracelessCartanMellinCharacter s (longReflectionOnCartan x) =
      tracelessCartanMellinCharacter
        (tracelessCartanMellinDualAction longReflectionOnCartan s) x :=
  tracelessCartanMellinCharacter_covariant _ _ _

/-- Equivalence from canonical Cartan to TracelessWeight. -/
def cartanToTraceless : Cartan ≃ₗ[ℝ] TracelessWeight :=
  axialCartanLieEquiv.symm

/-- The native short reflection on the canonical Cartan subalgebra. -/
def canonicalShortReflection : Cartan →ₗ[ℝ] Cartan :=
  cartanToTraceless.symm.toLinearMap.comp
    (shortReflectionOnCartan.comp cartanToTraceless.toLinearMap)

/-- The native long reflection on the canonical Cartan subalgebra. -/
def canonicalLongReflection : Cartan →ₗ[ℝ] Cartan :=
  cartanToTraceless.symm.toLinearMap.comp
    (longReflectionOnCartan.comp cartanToTraceless.toLinearMap)

/-- The dual action of the short reflection on the Mellin character parameters. -/
def canonicalShortReflectionDual (s : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![ -s 0 + 3 * s 1, s 1 ]

/-- The dual action of the long reflection on the Mellin character parameters. -/
def canonicalLongReflectionDual (s : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![ s 0, s 0 - s 1 ]

theorem canonicalG2CartanMellinCharacter_short_covariant
    (s : Fin 2 → ℂ) (x : Cartan) :
    CanonicalZornG2CartanMellinBridge.canonicalG2CartanMellinCharacter s (canonicalShortReflection x) =
      CanonicalZornG2CartanMellinBridge.canonicalG2CartanMellinCharacter (canonicalShortReflectionDual s) x := by
  unfold CanonicalZornG2CartanMellinBridge.canonicalG2CartanMellinCharacter
  unfold rankTwoCartanMellinCharacter
  unfold simpleWeightOnCartan
  unfold canonicalShortReflection
  unfold cartanToTraceless
  unfold canonicalShortReflectionDual
  congr 1
  apply neg_inj.mpr
  dsimp only [LinearEquiv.coe_toLinearMap, LinearMap.comp_apply, LinearEquiv.symm_symm]
  rw [LinearEquiv.symm_apply_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
  change s 0 * ↑((simpleWeight 0) (shortReflectionOnCartan (axialCartanLieEquiv.symm x))) + s 1 * ↑((simpleWeight 1) (shortReflectionOnCartan (axialCartanLieEquiv.symm x))) = (-s 0 + 3 * s 1) * ↑((simpleWeight 0) (axialCartanLieEquiv.symm x)) + s 1 * ↑((simpleWeight 1) (axialCartanLieEquiv.symm x))
  simp only [simpleWeight, if_pos, Fin.reduceEq]
  change s 0 * ↑((coordWeight 0) (shortReflectionOnCartan (axialCartanLieEquiv.symm x))) + s 1 * ↑((coordWeight 1 - coordWeight 0) (shortReflectionOnCartan (axialCartanLieEquiv.symm x))) = (-s 0 + 3 * s 1) * ↑((coordWeight 0) (axialCartanLieEquiv.symm x)) + s 1 * ↑((coordWeight 1 - coordWeight 0) (axialCartanLieEquiv.symm x))
  rw [LinearMap.sub_apply, LinearMap.sub_apply]
  have h0 : (coordWeight 0) (shortReflectionOnCartan (axialCartanLieEquiv.symm x)) = - (coordWeight 0) (axialCartanLieEquiv.symm x) := by
    have h := shortReflection_coordWeight 0
    exact congr_fun (congr_arg DFunLike.coe h) (axialCartanLieEquiv.symm x)
  have h1 : (coordWeight 1) (shortReflectionOnCartan (axialCartanLieEquiv.symm x)) = - (coordWeight 2) (axialCartanLieEquiv.symm x) := by
    have h := shortReflection_coordWeight 1
    exact congr_fun (congr_arg DFunLike.coe h) (axialCartanLieEquiv.symm x)
  rw [h0, h1]
  have h2 : (coordWeight 2) (axialCartanLieEquiv.symm x) = - (coordWeight 0) (axialCartanLieEquiv.symm x) - (coordWeight 1) (axialCartanLieEquiv.symm x) := by
    have h_val : weightSum (axialCartanLieEquiv.symm x).1 = 0 := (axialCartanLieEquiv.symm x).2
    change ∑ i, (axialCartanLieEquiv.symm x).1 i = 0 at h_val
    rw [Fin.sum_univ_three] at h_val
    change (coordWeight 0) (axialCartanLieEquiv.symm x) + (coordWeight 1) (axialCartanLieEquiv.symm x) + (coordWeight 2) (axialCartanLieEquiv.symm x) = 0 at h_val
    linarith
  rw [h2]
  push_cast
  ring

theorem canonicalG2CartanMellinCharacter_long_covariant
    (s : Fin 2 → ℂ) (x : Cartan) :
    CanonicalZornG2CartanMellinBridge.canonicalG2CartanMellinCharacter s (canonicalLongReflection x) =
      CanonicalZornG2CartanMellinBridge.canonicalG2CartanMellinCharacter (canonicalLongReflectionDual s) x := by
  unfold CanonicalZornG2CartanMellinBridge.canonicalG2CartanMellinCharacter
  unfold rankTwoCartanMellinCharacter
  unfold simpleWeightOnCartan
  unfold canonicalLongReflection
  unfold cartanToTraceless
  unfold canonicalLongReflectionDual
  congr 1
  apply neg_inj.mpr
  dsimp only [LinearEquiv.coe_toLinearMap, LinearMap.comp_apply, LinearEquiv.symm_symm]
  rw [LinearEquiv.symm_apply_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
  change s 0 * ↑((simpleWeight 0) (longReflectionOnCartan (axialCartanLieEquiv.symm x))) + s 1 * ↑((simpleWeight 1) (longReflectionOnCartan (axialCartanLieEquiv.symm x))) = s 0 * ↑((simpleWeight 0) (axialCartanLieEquiv.symm x)) + (s 0 - s 1) * ↑((simpleWeight 1) (axialCartanLieEquiv.symm x))
  simp only [simpleWeight, if_pos, Fin.reduceEq]
  change s 0 * ↑((coordWeight 0) (longReflectionOnCartan (axialCartanLieEquiv.symm x))) + s 1 * ↑((coordWeight 1 - coordWeight 0) (longReflectionOnCartan (axialCartanLieEquiv.symm x))) = s 0 * ↑((coordWeight 0) (axialCartanLieEquiv.symm x)) + (s 0 - s 1) * ↑((coordWeight 1 - coordWeight 0) (axialCartanLieEquiv.symm x))
  rw [LinearMap.sub_apply, LinearMap.sub_apply]
  have h0 : (coordWeight 0) (longReflectionOnCartan (axialCartanLieEquiv.symm x)) = (coordWeight 1) (axialCartanLieEquiv.symm x) := by
    have h := longReflection_coordWeight 0
    exact congr_fun (congr_arg DFunLike.coe h) (axialCartanLieEquiv.symm x)
  have h1 : (coordWeight 1) (longReflectionOnCartan (axialCartanLieEquiv.symm x)) = (coordWeight 0) (axialCartanLieEquiv.symm x) := by
    have h := longReflection_coordWeight 1
    exact congr_fun (congr_arg DFunLike.coe h) (axialCartanLieEquiv.symm x)
  rw [h0, h1]
  push_cast
  ring

end InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
