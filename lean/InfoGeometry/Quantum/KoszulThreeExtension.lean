/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.TriangularShortComplex
import InfoGeometry.Quantum.KoszulThree
import Mathlib.Algebra.CharP.Two

/-!
# Coupled Koszul complexes and explicit characteristic-two splitting

`extension` is the native short complex of Construction 2 in
Hao Song, arXiv:2608.09913v1. Its exactness theorem retains the two adjacent
Koszul exactness hypotheses explicitly.

The second part implements the actual formulas (G4)--(G8) of Appendix G.
The coefficient operators `F` commute with each other. The lowering operators
`T` instead satisfy `T j * F j + F j * T j = 1` and commute with the other
axes. No commutative replacement of their endomorphism algebra is made.
The resulting explicitly computed shear maps give a native short-complex
isomorphism and its native homology isomorphism. Physical Clifford circuits,
the dagger-dual sector, and Ext superselection layers are not asserted here.
-/

namespace InfoGeometry.KoszulThree

open CategoryTheory

universe u v

variable {A : Type u} {M : Type v}
variable [CommRing A] [AddCommGroup M] [Module A M]

/-- Construction 2 on three commuting operator coefficients. -/
def extension (F : Fin 3 → Module.End A M)
    (hF : ∀ i j, Commute (F i) (F j)) (a : Fin 3 → A) :
    ShortComplex (ModuleCat A) :=
  TriangularShortComplex.complex (d1 F) (d2 F) (d3 F) (column a) (row a)
    (d1_comp_d2 F hF) (d2_comp_d3 F hF) (coupling_compatible F a)

/-- The ordinary direct sum, with both off-diagonal coupling maps zero. -/
def uncoupled (F : Fin 3 → Module.End A M)
    (hF : ∀ i j, Commute (F i) (F j)) : ShortComplex (ModuleCat A) :=
  TriangularShortComplex.complex (d1 F) (d2 F) (d3 F) 0 0
    (d1_comp_d2 F hF) (d2_comp_d3 F hF) (by simp)

/-- Fact 9's Z-sector exactness transfer, with its actual hypotheses displayed. -/
theorem extension_exact (F : Fin 3 → Module.End A M)
    (hF : ∀ i j, Commute (F i) (F j)) (a : Fin 3 → A)
    (hExact₁ : LinearMap.range (d2 F) = LinearMap.ker (d1 F))
    (hExact₂ : LinearMap.range (d3 F) = LinearMap.ker (d2 F)) :
    (extension F hF a).Exact :=
  TriangularShortComplex.exact (d1 F) (d2 F) (d3 F) (column a) (row a)
    (d1_comp_d2 F hF) (d2_comp_d3 F hF) (coupling_compatible F a)
    hExact₁ hExact₂

/-- Appendix G's source shear, summed against the scalar coupling vector. -/
def G (T : Fin 3 → Module.End A M) (a : Fin 3 → A) :
    M →ₗ[A] (Fin 3 → M) :=
  LinearMap.pi ![a 1 • T 2, a 2 • T 0, a 0 • T 1]

/-- Appendix G's middle shear in the cyclic degree-two basis. -/
def H (T : Fin 3 → Module.End A M) (a : Fin 3 → A) :
    Module.End A (Fin 3 → M) :=
  LinearMap.pi ![
    a 0 • (T 1).comp (LinearMap.proj 1) +
      a 2 • (T 0).comp (LinearMap.proj 2),
    a 0 • (T 1).comp (LinearMap.proj 0) +
      a 1 • (T 2).comp (LinearMap.proj 2),
    a 1 • (T 2).comp (LinearMap.proj 1) +
      a 2 • (T 0).comp (LinearMap.proj 0)]

/-- Appendix G's target shear. -/
def Q (T : Fin 3 → Module.End A M) (a : Fin 3 → A) :
    (Fin 3 → M) →ₗ[A] M :=
  a 0 • (T 1).comp (LinearMap.proj 2) +
    a 1 • (T 2).comp (LinearMap.proj 0) +
    a 2 • (T 0).comp (LinearMap.proj 1)

@[simp] theorem G_apply_zero (T : Fin 3 → Module.End A M)
    (a : Fin 3 → A) (x : M) : G T a x 0 = a 1 • T 2 x := rfl

@[simp] theorem G_apply_one (T : Fin 3 → Module.End A M)
    (a : Fin 3 → A) (x : M) : G T a x 1 = a 2 • T 0 x := rfl

@[simp] theorem G_apply_two (T : Fin 3 → Module.End A M)
    (a : Fin 3 → A) (x : M) : G T a x 2 = a 0 • T 1 x := rfl

@[simp] theorem H_apply_zero (T : Fin 3 → Module.End A M)
    (a : Fin 3 → A) (x : Fin 3 → M) :
    H T a x 0 = a 0 • T 1 (x 1) + a 2 • T 0 (x 2) := rfl

@[simp] theorem H_apply_one (T : Fin 3 → Module.End A M)
    (a : Fin 3 → A) (x : Fin 3 → M) :
    H T a x 1 = a 0 • T 1 (x 0) + a 1 • T 2 (x 2) := rfl

@[simp] theorem H_apply_two (T : Fin 3 → Module.End A M)
    (a : Fin 3 → A) (x : Fin 3 → M) :
    H T a x 2 = a 1 • T 2 (x 1) + a 2 • T 0 (x 0) := rfl

@[simp] theorem Q_apply (T : Fin 3 → Module.End A M)
    (a : Fin 3 → A) (x : Fin 3 → M) :
    Q T a x = a 0 • T 1 (x 2) + a 1 • T 2 (x 0) + a 2 • T 0 (x 1) := rfl

section CharacteristicTwo

variable [CharP A 2]

include A in
private theorem module_neg_eq (x : M) : -x = x := by
  rw [← neg_one_smul A x, CharTwo.neg_eq (1 : A), one_smul]

include A in
private theorem module_sub_eq_add (x y : M) : x - y = x + y := by
  rw [sub_eq_add_neg, module_neg_eq (A := A)]

include A in
private theorem module_add_self_eq_zero (x : M) : x + x = 0 := by
  simpa only [module_neg_eq (A := A)] using neg_add_cancel x

variable (F T : Fin 3 → Module.End A M)
variable (hAnti : ∀ j, T j * F j + F j * T j = 1)
variable (hOff : ∀ j l, j ≠ l → Commute (T j) (F l))

include hAnti in
omit [CharP A 2] in
private theorem anticommutator_apply (j : Fin 3) (x : M) :
    T j (F j x) + F j (T j x) = x :=
  LinearMap.congr_fun (hAnti j) x

include hOff in
omit [CharP A 2] in
private theorem offAxis_apply (j l : Fin 3) (hjl : j ≠ l) (x : M) :
    F l (T j x) = T j (F l x) :=
  (LinearMap.congr_fun (hOff j l hjl).eq x).symm

include hAnti hOff in
/-- The first explicitly computed splitting identity, equation (G6). -/
theorem G_H_identity (a : Fin 3 → A) :
    (d2 F).comp (G T a) + (H T a).comp (d3 F) = column a := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i
  · change
      (F 2 (a 2 • T 0 x) - F 1 (a 0 • T 1 x)) +
        (a 0 • T 1 (F 1 x) + a 2 • T 0 (F 2 x)) = a 0 • x
    simp only [map_smul, module_sub_eq_add (A := A)]
    rw [offAxis_apply F T hOff 0 2 (by decide) x]
    calc
      _ = a 0 • (T 1 (F 1 x) + F 1 (T 1 x)) +
          (a 2 • T 0 (F 2 x) + a 2 • T 0 (F 2 x)) := by
            simp only [smul_add]
            abel
      _ = a 0 • x := by
        rw [anticommutator_apply F T hAnti 1 x,
          module_add_self_eq_zero (A := A), add_zero]
  · change
      (F 0 (a 0 • T 1 x) - F 2 (a 1 • T 2 x)) +
        (a 0 • T 1 (F 0 x) + a 1 • T 2 (F 2 x)) = a 1 • x
    simp only [map_smul, module_sub_eq_add (A := A)]
    rw [offAxis_apply F T hOff 1 0 (by decide) x]
    calc
      _ = a 1 • (T 2 (F 2 x) + F 2 (T 2 x)) +
          (a 0 • T 1 (F 0 x) + a 0 • T 1 (F 0 x)) := by
            simp only [smul_add]
            abel
      _ = a 1 • x := by
        rw [anticommutator_apply F T hAnti 2 x,
          module_add_self_eq_zero (A := A), add_zero]
  · change
      (F 1 (a 1 • T 2 x) - F 0 (a 2 • T 0 x)) +
        (a 1 • T 2 (F 1 x) + a 2 • T 0 (F 0 x)) = a 2 • x
    simp only [map_smul, module_sub_eq_add (A := A)]
    rw [offAxis_apply F T hOff 2 1 (by decide) x]
    calc
      _ = a 2 • (T 0 (F 0 x) + F 0 (T 0 x)) +
          (a 1 • T 2 (F 1 x) + a 1 • T 2 (F 1 x)) := by
            simp only [smul_add]
            abel
      _ = a 2 • x := by
        rw [anticommutator_apply F T hAnti 0 x,
          module_add_self_eq_zero (A := A), add_zero]

include hAnti hOff in
/-- The second explicitly computed splitting identity, equation (G6). -/
theorem Q_H_identity (a : Fin 3 → A) :
    (Q T a).comp (d2 F) + (d1 F).comp (H T a) = row a := by
  apply LinearMap.ext
  intro x
  change
    (a 0 • T 1 (F 1 (x 0) - F 0 (x 1)) +
      a 1 • T 2 (F 2 (x 1) - F 1 (x 2)) +
      a 2 • T 0 (F 0 (x 2) - F 2 (x 0))) +
    (F 0 (a 0 • T 1 (x 1) + a 2 • T 0 (x 2)) +
      F 1 (a 0 • T 1 (x 0) + a 1 • T 2 (x 2)) +
      F 2 (a 1 • T 2 (x 1) + a 2 • T 0 (x 0))) =
        a 0 • x 0 + a 1 • x 1 + a 2 • x 2
  simp only [module_sub_eq_add (A := A), map_add, map_smul, smul_add]
  rw [offAxis_apply F T hOff 1 0 (by decide) (x 1),
    offAxis_apply F T hOff 2 1 (by decide) (x 2),
    offAxis_apply F T hOff 0 2 (by decide) (x 0)]
  calc
    _ =
        (a 0 • (T 1 (F 1 (x 0)) + F 1 (T 1 (x 0))) +
          a 1 • (T 2 (F 2 (x 1)) + F 2 (T 2 (x 1))) +
          a 2 • (T 0 (F 0 (x 2)) + F 0 (T 0 (x 2)))) +
        ((a 0 • T 1 (F 0 (x 1)) + a 0 • T 1 (F 0 (x 1))) +
          (a 1 • T 2 (F 1 (x 2)) + a 1 • T 2 (F 1 (x 2))) +
          (a 2 • T 0 (F 2 (x 0)) + a 2 • T 0 (F 2 (x 0)))) := by
      simp only [smul_add]
      abel
    _ = a 0 • x 0 + a 1 • x 1 + a 2 • x 2 := by
      rw [anticommutator_apply F T hAnti 1 (x 0),
        anticommutator_apply F T hAnti 2 (x 1),
        anticommutator_apply F T hAnti 0 (x 2)]
      simp only [module_add_self_eq_zero (A := A), add_zero]

include hAnti hOff in
/-- The incoming splitting identity in the signed form of the general shear theorem. -/
theorem column_splitting (a : Fin 3 → A) :
    column a = (d2 F).comp (G T a) - (H T a).comp (d3 F) := by
  apply LinearMap.ext
  intro x
  funext i
  have h := congrArg (fun f : M →ₗ[A] (Fin 3 → M) => f x i)
    (G_H_identity F T hAnti hOff a)
  simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    Pi.add_apply, Pi.sub_apply, module_sub_eq_add (A := A)] using h.symm

include hAnti hOff in
/-- The outgoing splitting identity in the signed form of the general shear theorem. -/
theorem row_splitting (a : Fin 3 → A) :
    row a = (Q T a).comp (d2 F) - (d1 F).comp (H T a) := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (Q_H_identity F T hAnti hOff a) x
  simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    module_sub_eq_add (A := A)] using h.symm

include hAnti hOff in
/-- The explicitly constructed shears split the native short complex. -/
def coarseSplittingIso (hF : ∀ i j, Commute (F i) (F j)) (a : Fin 3 → A) :
    extension F hF a ≅ uncoupled F hF :=
  TriangularShortComplex.splittingIso (d1 F) (d2 F) (d3 F) (column a) (row a)
    (d1_comp_d2 F hF) (d2_comp_d3 F hF) (coupling_compatible F a)
    (G T a) (H T a) (Q T a)
    (column_splitting F T hAnti hOff a) (row_splitting F T hAnti hOff a)

include hAnti hOff in
/-- The splitting transports mathlib's native middle homology. -/
noncomputable def coarseSplittingHomologyIso
    (hF : ∀ i j, Commute (F i) (F j)) (a : Fin 3 → A) :
    (extension F hF a).homology ≅ (uncoupled F hF).homology :=
  ShortComplex.homologyMapIso (coarseSplittingIso F T hAnti hOff hF a)

end CharacteristicTwo

end InfoGeometry.KoszulThree
