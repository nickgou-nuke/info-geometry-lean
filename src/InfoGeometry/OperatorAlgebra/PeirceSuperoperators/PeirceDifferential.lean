/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.PeirceParity
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# The intrinsic differential on the actual Peirce submodules

An odd charge exchanges the existing even and odd submodules. When its square
vanishes, the two restrictions form native short complexes. No exactness of
these complexes is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open InfoGeometry.Core
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem gradedAdjoint_even_mem_odd {p N x : A} (hp : IsIdempotentElem p)
    (hN : N ∈ LinearMap.range (PeirceGrading.odd p))
    (hx : x ∈ LinearMap.range (PeirceGrading.even p)) :
    gradedAdjoint (parityEquiv (R := R) p hp) N x ∈
      LinearMap.range (PeirceGrading.odd p) := by
  rw [gradedAdjoint_of_even _ _ _ (parityEquiv_of_even hp hx)]
  exact (LinearMap.range (PeirceGrading.odd p)).sub_mem
    (PeirceGrading.odd_mul_even hp hN hx) (PeirceGrading.even_mul_odd hp hx hN)

theorem gradedAdjoint_odd_mem_even {p N x : A} (hp : IsIdempotentElem p)
    (hN : N ∈ LinearMap.range (PeirceGrading.odd p))
    (hx : x ∈ LinearMap.range (PeirceGrading.odd p)) :
    gradedAdjoint (parityEquiv (R := R) p hp) N x ∈
      LinearMap.range (PeirceGrading.even p) := by
  rw [gradedAdjoint_of_odd _ _ _ (parityEquiv_of_odd hp hx)]
  exact (LinearMap.range (PeirceGrading.even p)).add_mem
    (PeirceGrading.odd_mul_odd hp hN hx) (PeirceGrading.odd_mul_odd hp hx hN)

/-- Square-zero of the charge gives square-zero of the full graded endomorphism. -/
theorem peirce_graded_square_zero {p N : A} (hp : IsIdempotentElem p)
    (hN : N ∈ LinearMap.range (PeirceGrading.odd p)) (hsq : N * N = 0) :
    gradedAdjoint (parityEquiv (R := R) p hp) N *
      gradedAdjoint (parityEquiv (R := R) p hp) N = 0 := by
  rw [gradedAdjoint_square _ (parityEquiv_involutive p hp) N
    (parityEquiv_of_odd hp hN), hsq]
  ext x
  simp

theorem peirce_graded_range_le_ker {p N : A} (hp : IsIdempotentElem p)
    (hN : N ∈ LinearMap.range (PeirceGrading.odd p)) (hsq : N * N = 0) :
    (gradedAdjoint (parityEquiv (R := R) p hp) N).range ≤
      (gradedAdjoint (parityEquiv (R := R) p hp) N).ker :=
  LinearMap.range_le_ker_iff.mpr (peirce_graded_square_zero hp hN hsq)

section Restrictions

variable {p N : A} (hp : IsIdempotentElem p)
    (hN : N ∈ LinearMap.range (PeirceGrading.odd p))

/-- The even-to-odd restriction of the same ambient graded action. -/
def evenToOdd : LinearMap.range (PeirceGrading.even p) →ₗ[ℤ]
    LinearMap.range (PeirceGrading.odd p) :=
  LinearMap.codRestrict _
    ((gradedAdjoint (parityEquiv (R := ℤ) p hp) N).domRestrict _) fun x =>
      gradedAdjoint_even_mem_odd hp hN x.property

/-- The odd-to-even restriction uses the same action, now its Jordan part. -/
def oddToEven : LinearMap.range (PeirceGrading.odd p) →ₗ[ℤ]
    LinearMap.range (PeirceGrading.even p) :=
  LinearMap.codRestrict _
    ((gradedAdjoint (parityEquiv (R := ℤ) p hp) N).domRestrict _) fun x =>
      gradedAdjoint_odd_mem_even hp hN x.property

@[simp] theorem evenToOdd_apply (x : LinearMap.range (PeirceGrading.even p)) :
    (evenToOdd hp hN x : A) = N * x - x * N :=
  gradedAdjoint_of_even _ _ _ (parityEquiv_of_even hp x.property)

@[simp] theorem oddToEven_apply (x : LinearMap.range (PeirceGrading.odd p)) :
    (oddToEven hp hN x : A) = N * x + x * N :=
  gradedAdjoint_of_odd _ _ _ (parityEquiv_of_odd hp x.property)

theorem oddToEven_comp_evenToOdd (hsq : N * N = 0) :
    (oddToEven hp hN).comp (evenToOdd hp hN) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change gradedAdjoint (parityEquiv (R := ℤ) p hp) N
    (gradedAdjoint (parityEquiv (R := ℤ) p hp) N (x : A)) = 0
  exact congrArg (fun T : Module.End ℤ A => T x) (peirce_graded_square_zero hp hN hsq)

theorem evenToOdd_comp_oddToEven (hsq : N * N = 0) :
    (evenToOdd hp hN).comp (oddToEven hp hN) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change gradedAdjoint (parityEquiv (R := ℤ) p hp) N
    (gradedAdjoint (parityEquiv (R := ℤ) p hp) N (x : A)) = 0
  exact congrArg (fun T : Module.End ℤ A => T x) (peirce_graded_square_zero hp hN hsq)

/-- A native short complex on the actual complementary Peirce submodules. -/
def evenShortComplex (hsq : N * N = 0) : CategoryTheory.ShortComplex (ModuleCat ℤ) where
  X₁ := ModuleCat.of ℤ (LinearMap.range (PeirceGrading.even p))
  X₂ := ModuleCat.of ℤ (LinearMap.range (PeirceGrading.odd p))
  X₃ := ModuleCat.of ℤ (LinearMap.range (PeirceGrading.even p))
  f := ModuleCat.ofHom (evenToOdd hp hN)
  g := ModuleCat.ofHom (oddToEven hp hN)
  zero := ModuleCat.hom_ext (oddToEven_comp_evenToOdd hp hN hsq)

def oddShortComplex (hsq : N * N = 0) : CategoryTheory.ShortComplex (ModuleCat ℤ) where
  X₁ := ModuleCat.of ℤ (LinearMap.range (PeirceGrading.odd p))
  X₂ := ModuleCat.of ℤ (LinearMap.range (PeirceGrading.even p))
  X₃ := ModuleCat.of ℤ (LinearMap.range (PeirceGrading.odd p))
  f := ModuleCat.ofHom (oddToEven hp hN)
  g := ModuleCat.ofHom (evenToOdd hp hN)
  zero := ModuleCat.hom_ext (evenToOdd_comp_oddToEven hp hN hsq)

end Restrictions

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
