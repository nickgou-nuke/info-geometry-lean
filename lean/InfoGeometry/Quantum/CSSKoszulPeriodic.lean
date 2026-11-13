/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.CSSKoszulBaseChange
import InfoGeometry.Quantum.CSSKoszulHomology
import InfoGeometry.Quantum.LatticeTranslationRing
import Mathlib.Algebra.Field.ZMod

/-!
# A periodic homology obstruction for coupled lattice complexes

The toric sequence lives in the full translation group algebra `k[ℤ³]`.
One-cell periodic reduction is actual tensor extension along the quotient
by `(x₁ - 1, x₂ - 1, x₃ - 1)`, identified with `k` by the proved quotient
equivalence. The resulting native homology has rank six for zero coupling
and rank four for coupling by the first coordinate vector.

Functorial scalar extension then rules out a chain isomorphism of the two
original translation-ring complexes. This is not a theorem about arbitrary
physical finite-depth circuits, coarse graining, or the other six nonzero
couplings in the paper.
-/

namespace InfoGeometry.Quantum.CSSKoszulPeriodic

open CategoryTheory
open CSSKoszulExtension LatticeTranslationRing

universe u

variable (k : Type u) [CommRing k]

/-- The three toric-code difference operators in the full lattice ring. -/
noncomputable def toricSequence : Vec3 (Coefficients k 3) :=
  fun i => coordinate k 3 i - 1

@[simp] theorem augmentation_toricSequence :
    augmentation k 3 ∘ toricSequence k = (0 : Vec3 k) := by
  ext i
  simp [toricSequence]

@[simp] theorem augmentation_unitCoupling :
    augmentation k 3 ∘ unitCoupling (Coefficients k 3) = unitCoupling k := by
  ext i
  fin_cases i <;> simp [unitCoupling]

/-- The one-cell map is explicitly the quotient projection followed by its
proved identification with the coefficient ring. -/
noncomputable def oneCellMap : Coefficients k 3 →+* k :=
  (oneCellEquiv k 3).toRingHom.comp (Ideal.Quotient.mk (oneCellIdeal k 3))

theorem oneCellMap_eq_augmentation :
    oneCellMap k = (augmentation k 3).toRingHom := by
  apply RingHom.ext
  intro p
  exact oneCellEquiv_mk k 3 p

/-- The actual scalar-extended complex on the one-cell periodic quotient. -/
noncomputable def oneCellComplex (a : Vec3 (Coefficients k 3)) :
    ShortComplex (ModuleCat k) :=
  (complex (toricSequence k) a).map (ModuleCat.extendScalars (oneCellMap k))

/-- Comparison of the tensor-extended complex with its evaluated presentation. -/
noncomputable def oneCellIso (a : Vec3 (Coefficients k 3)) :
    oneCellComplex k a ≅ complex (0 : Vec3 k) (augmentation k 3 ∘ a) := by
  have hs : oneCellComplex k a =
      (complex (toricSequence k) a).map
        (ModuleCat.extendScalars (augmentation k 3).toRingHom) :=
    congrArg (fun φ : Coefficients k 3 →+* k =>
      (complex (toricSequence k) a).map (ModuleCat.extendScalars φ))
      (oneCellMap_eq_augmentation k)
  have hf : (augmentation k 3).toRingHom ∘ toricSequence k = (0 : Vec3 k) :=
    augmentation_toricSequence k
  exact eqToIso hs ≪≫ baseChangeIso (augmentation k 3).toRingHom (toricSequence k) a ≪≫
    eqToIso (congrArg₂ complex hf (show (augmentation k 3).toRingHom ∘ a =
      augmentation k 3 ∘ a from rfl))

noncomputable def zeroOneCellIso :
    oneCellComplex k 0 ≅ complex (0 : Vec3 k) 0 := by
  have h : augmentation k 3 ∘ (0 : Vec3 (Coefficients k 3)) = (0 : Vec3 k) := by
    ext i
    exact map_zero _
  exact oneCellIso k 0 ≪≫ eqToIso (congrArg (complex (0 : Vec3 k)) h)

noncomputable def unitOneCellIso :
    oneCellComplex k (unitCoupling (Coefficients k 3)) ≅
      complex (0 : Vec3 k) (unitCoupling k) := by
  simpa only [augmentation_unitCoupling] using
    oneCellIso k (unitCoupling (Coefficients k 3))

/-- All six coordinates survive in zero-coupled one-cell logical homology. -/
noncomputable def zeroOneCellHomologyEquiv :
    (oneCellComplex k 0).homology ≃ₗ[k] (Vec3 k × Vec3 k) :=
  (ShortComplex.homologyMapIso (zeroOneCellIso k)).toLinearEquiv.trans
    (zeroHomologyEquiv k)

/-- Exactly four coordinates survive in unit-coupled one-cell logical homology. -/
noncomputable def unitOneCellHomologyEquiv :
    (oneCellComplex k (unitCoupling (Coefficients k 3))).homology ≃ₗ[k]
      ((Fin 2 → k) × (Fin 2 → k)) :=
  (ShortComplex.homologyMapIso (unitOneCellIso k)).toLinearEquiv.trans
    (unitHomologyEquiv k)

section Field

variable (K : Type u) [Field K]

theorem finrank_zero_oneCell :
    Module.finrank K (oneCellComplex K 0).homology = 6 := by
  rw [(zeroOneCellHomologyEquiv K).finrank_eq]
  simp [Vec3, Module.finrank_prod]

theorem finrank_unit_oneCell :
    Module.finrank K
      (oneCellComplex K (unitCoupling (Coefficients K 3))).homology = 4 := by
  rw [(unitOneCellHomologyEquiv K).finrank_eq]
  simp [Module.finrank_prod]

/-- The original translation-ring complexes are not isomorphic: an
isomorphism would survive scalar extension and preserve the unequal homology
dimensions. This obstruction is proved on the full Laurent-ring carrier. -/
theorem not_nonempty_toric_zero_unit_iso :
    ¬ Nonempty
      (complex (toricSequence K) 0 ≅
        complex (toricSequence K) (unitCoupling (Coefficients K 3))) := by
  rintro ⟨e⟩
  let e' : oneCellComplex K 0 ≅ oneCellComplex K (unitCoupling (Coefficients K 3)) :=
    (ModuleCat.extendScalars (oneCellMap K)).mapShortComplex.mapIso e
  have h := (ShortComplex.homologyMapIso e').toLinearEquiv.finrank_eq
  rw [finrank_zero_oneCell, finrank_unit_oneCell] at h
  norm_num at h

end Field

/-- The characteristic-two application retains the complete translation ring. -/
theorem qubit_toric_zero_unit_not_iso :
    ¬ Nonempty
      (complex (toricSequence (ZMod 2)) 0 ≅
        complex (toricSequence (ZMod 2)) (unitCoupling (Coefficients (ZMod 2) 3))) :=
  not_nonempty_toric_zero_unit_iso (ZMod 2)

end InfoGeometry.Quantum.CSSKoszulPeriodic
