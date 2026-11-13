/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.EvenTranslationOperators
import InfoGeometry.Quantum.KoszulThreeExtension

/-!
# Even-translation splitting of the eight constant Koszul extensions

This specializes the constructed three-generator Koszul extension to the
actual Laurent module `TranslationRing` over its even-translation coefficient
ring `CoarseRing`. The coupling vector has three binary coefficients. Those
coefficients act through the original `ZMod 2` scalar action, as proved by
`constantCoupling_smul`.

For every coupling vector, the parity-lowering maps of
`EvenTranslationOperators` supply the explicit triangular changes of
coordinates. The result is a native short-complex isomorphism to the uncoupled
complex, together with the induced native middle-homology isomorphism.
`splittingIso_middle_apply` exposes the actual middle coordinate shear.

These are Appendix G's algebraic splitting equations G6--G8 in Hao Song,
arXiv:2608.09913v1. No regular-sequence exactness, dagger-dual sector,
pre-blocking nonsplitting, superselection classification, or finite-depth
Clifford circuit is inferred from the short-complex isomorphism alone.
-/

noncomputable section

namespace InfoGeometry.Quantum.KoszulEvenTranslationSplitting

open CategoryTheory
open EvenTranslationOperators

/-- The three binary coupling coefficients embedded as constant coarse Laurent polynomials. -/
def constantCoupling (a : Fin 3 → ZMod 2) : Fin 3 → CoarseRing :=
  fun i => algebraMap (ZMod 2) CoarseRing (a i)

/-- Restriction of scalars preserves the original binary coefficient action. -/
@[simp] theorem constantCoupling_smul (a : Fin 3 → ZMod 2) (i : Fin 3)
    (r : TranslationRing) : constantCoupling a i • r = a i • r :=
  IsScalarTower.algebraMap_smul CoarseRing (a i) r

/-- The coupled degree-(1,2) Koszul complex on the actual blocked Laurent module. -/
def blockedExtension (a : Fin 3 → ZMod 2) : ShortComplex (ModuleCat CoarseRing) :=
  KoszulThree.extension difference difference_commute (constantCoupling a)

/-- The ordinary direct sum on the same even-translation module. -/
def splitExtension : ShortComplex (ModuleCat CoarseRing) :=
  KoszulThree.uncoupled difference difference_commute

/-- The actual parity operators split every constant binary coupling after even blocking. -/
def splittingIso (a : Fin 3 → ZMod 2) : blockedExtension a ≅ splitExtension :=
  KoszulThree.coarseSplittingIso difference lowering
    lowering_mul_difference_add_difference_mul_lowering
    (fun j l h => lowering_commute_difference_of_ne (j := j) (l := l) h)
    difference_commute (constantCoupling a)

/-- The middle component is the explicit upper-triangular shear from Appendix G. -/
@[simp] theorem splittingIso_middle_apply (a : Fin 3 → ZMod 2)
    (x y : Fin 3 → TranslationRing) :
    (splittingIso a).hom.τ₂ (x, y) =
      (x + KoszulThree.H lowering (constantCoupling a) y, y) := rfl

/-- The inverse middle component uses the inverse of that same shear. -/
@[simp] theorem splittingIso_inv_middle_apply (a : Fin 3 → ZMod 2)
    (x y : Fin 3 → TranslationRing) :
    (splittingIso a).inv.τ₂ (x, y) =
      (x - KoszulThree.H lowering (constantCoupling a) y, y) := rfl

/-- Mathlib's native middle homology is transported by the explicit splitting. -/
def splittingHomologyIso (a : Fin 3 → ZMod 2) :
    (blockedExtension a).homology ≅ splitExtension.homology :=
  ShortComplex.homologyMapIso (splittingIso a)

/-- The induced homology isomorphism as an equivalence of coarse modules. -/
def splittingHomologyLinearEquiv (a : Fin 3 → ZMod 2) :
    (blockedExtension a).homology ≃ₗ[CoarseRing] splitExtension.homology :=
  (splittingHomologyIso a).toLinearEquiv

end InfoGeometry.Quantum.KoszulEvenTranslationSplitting
