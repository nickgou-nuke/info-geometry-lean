/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl55SpinorRepresentationGeneration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.SplitCliffordNativeTensorFinrank
open InfoGeometry.Clifford.SpinorRep
open scoped TensorProduct

noncomputable section

private noncomputable def splitOneToPair :
    InfoGeometry.CliffordTower.SplitSpace 1 ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun := fun x => x.1
  invFun := fun x => (x, 0)
  left_inv := by
    intro x
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.elim0 i
  right_inv := by
    intro x
    rfl
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl

private noncomputable def splitOneToPairIsometry :
    QuadraticMap.IsometryEquiv (Qsplit 1)
      InfoGeometry.CliffordTower.Q11 where
  toLinearEquiv := splitOneToPair
  map_app' := by
    intro x
    simp [splitOneToPair, Qsplit,
      InfoGeometry.CliffordTower.Q11,
      InfoGeometry.Clifford.Cl11Matrix.q11,
      InfoGeometry.Clifford.splitQ11_apply]

private noncomputable def splitCl11Equiv :
    SplitClNNAlg 1 ≃ₐ[ℝ]
      CliffordAlgebra InfoGeometry.CliffordTower.Q11 :=
  CliffordAlgebra.equivOfIsometry splitOneToPairIsometry

theorem splitClNNAlg_finrank_one :
    Module.finrank ℝ (SplitClNNAlg 1) = 4 := by
  rw [splitCl11Equiv.toLinearEquiv.finrank_eq]
  have hq : InfoGeometry.CliffordTower.Q11 =
      InfoGeometry.Clifford.Cl11Matrix.q11 := by
    ext v
    simp [InfoGeometry.CliffordTower.Q11,
      InfoGeometry.Clifford.Cl11Matrix.q11,
      InfoGeometry.Clifford.splitQ11_apply,
      CliffordAlgebraQuaternion.Q]
    ring
  rw [hq]
  exact InfoGeometry.Clifford.Cl11Matrix.finrank_cl11

theorem splitClNNAlg_finrank_four :
    Module.finrank ℝ (SplitClNNAlg 4) = 256 := by
  calc
    Module.finrank ℝ (SplitClNNAlg 4) =
        4 * Module.finrank ℝ (SplitClNNAlg 3) := by
      simpa using splitClNNAlg_finrank_succ 3
    _ = 4 * (4 * Module.finrank ℝ (SplitClNNAlg 2)) := by
      rw [splitClNNAlg_finrank_succ 2]
    _ = 4 * (4 * (4 * Module.finrank ℝ (SplitClNNAlg 1))) := by
      rw [splitClNNAlg_finrank_succ 1]
    _ = 256 := by
      rw [splitClNNAlg_finrank_one]

theorem splitClNNAlg_finrank_five :
    Module.finrank ℝ (SplitClNNAlg 5) = 1024 := by
  calc
    Module.finrank ℝ (SplitClNNAlg 5) =
        4 * Module.finrank ℝ (SplitClNNAlg 4) := by
      simpa using splitClNNAlg_finrank_succ 4
    _ = 4 * (4 * Module.finrank ℝ (SplitClNNAlg 3)) := by
      rw [splitClNNAlg_finrank_succ 3]
    _ = 4 * (4 * (4 * Module.finrank ℝ (SplitClNNAlg 2))) := by
      rw [splitClNNAlg_finrank_succ 2]
    _ = 4 * (4 * (4 * (4 * Module.finrank ℝ (SplitClNNAlg 1)))) := by
      rw [splitClNNAlg_finrank_succ 1]
    _ = 1024 := by
      rw [splitClNNAlg_finrank_one]


theorem splitClNNAlg_finiteDimensional_five :
    FiniteDimensional ℝ (SplitClNNAlg 5) := by
  letI : FiniteDimensional ℝ
      (CliffordAlgebra InfoGeometry.CliffordTower.Q11) := by
    have hq : InfoGeometry.CliffordTower.Q11 =
        InfoGeometry.Clifford.Cl11Matrix.q11 := by
      ext v
      simp [InfoGeometry.CliffordTower.Q11,
        InfoGeometry.Clifford.Cl11Matrix.q11,
        InfoGeometry.Clifford.splitQ11_apply,
        CliffordAlgebraQuaternion.Q]
      ring
    rw [hq]
    exact LinearEquiv.finiteDimensional
      InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.toLinearEquiv.symm
  have gradedFinite (n : ℕ) [FiniteDimensional ℝ (SplitClNNAlg n)] :
      FiniteDimensional ℝ (SplitClNNTensorStep n) := by
    let e : SplitClNNTensorStep n ≃ₗ[ℝ]
        TensorProduct ℝ
          (CliffordAlgebra InfoGeometry.CliffordTower.Q11)
          (CliffordAlgebra (Qsplit n)) :=
      (GradedTensorProduct.of ℝ
        (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
        (CliffordAlgebra.evenOdd (Qsplit n))).symm
    exact LinearEquiv.finiteDimensional e.symm
  letI : FiniteDimensional ℝ (SplitClNNAlg 1) := by
    exact LinearEquiv.finiteDimensional splitCl11Equiv.symm.toLinearEquiv
  letI : FiniteDimensional ℝ (SplitClNNTensorStep 1) := gradedFinite 1
  letI : FiniteDimensional ℝ (SplitClNNAlg 2) := by
    exact LinearEquiv.finiteDimensional
      (splitCliffordTensorStepEquiv 1).symm.toLinearEquiv
  letI : FiniteDimensional ℝ (SplitClNNTensorStep 2) := gradedFinite 2
  letI : FiniteDimensional ℝ (SplitClNNAlg 3) := by
    exact LinearEquiv.finiteDimensional
      (splitCliffordTensorStepEquiv 2).symm.toLinearEquiv
  letI : FiniteDimensional ℝ (SplitClNNTensorStep 3) := gradedFinite 3
  letI : FiniteDimensional ℝ (SplitClNNAlg 4) := by
    exact LinearEquiv.finiteDimensional
      (splitCliffordTensorStepEquiv 3).symm.toLinearEquiv
  letI : FiniteDimensional ℝ (SplitClNNTensorStep 4) := gradedFinite 4
  exact LinearEquiv.finiteDimensional
    (splitCliffordTensorStepEquiv 4).symm.toLinearEquiv

theorem cl55_finrank :
    Module.finrank ℝ Cl55 = 1024 := by
  rw [cl55ToSplitCl55.toLinearEquiv.finrank_eq]
  exact splitClNNAlg_finrank_five

theorem spinorMatrix_finrank :
    Module.finrank ℝ (SpinorMatrix 5) = 1024 := by
  simp [SpinorMatrix, Module.finrank_matrix]

noncomputable def cl55SpinorAlgEquiv :
    Cl55 ≃ₐ[ℝ] SpinorMatrix 5 :=
  letI : FiniteDimensional ℝ (SplitClNNAlg 5) :=
    splitClNNAlg_finiteDimensional_five
  letI : FiniteDimensional ℝ Cl55 :=
    LinearEquiv.finiteDimensional cl55ToSplitCl55.toLinearEquiv.symm
  cl55SpinorAlgEquiv_of_surjective
    cl55SpinorRepresentation_surjective (by
      rw [cl55_finrank, spinorMatrix_finrank])

/-- Finite dimensionality transported from the actual spinor matrix algebra. -/
theorem cl55_finiteDimensional : FiniteDimensional ℝ Cl55 :=
  LinearEquiv.finiteDimensional cl55SpinorAlgEquiv.toLinearEquiv.symm

/-- The native Clifford algebra is semisimple via its spinor algebra isomorphism. -/
theorem cl55_isSemisimpleRing : IsSemisimpleRing Cl55 :=
  cl55SpinorAlgEquiv.symm.toRingEquiv.isSemisimpleRing

/-- Ungraded real-linear Morita equivalence, constructed from the spinor
isomorphism and Mathlib's matrix-module equivalence. This does not identify
a TQFT wall algebra or assert a graded Morita equivalence. -/
noncomputable def cl55MoritaEquivalence : MoritaEquivalence ℝ Cl55 ℝ :=
  (MoritaEquivalence.ofAlgEquiv cl55SpinorAlgEquiv).trans ℝ
    ((moritaEquivalenceMatrix ℝ ℝ (0 : Fin (2 ^ 5))).symm ℝ)

theorem cl55_isMoritaEquivalent : IsMoritaEquivalent ℝ Cl55 ℝ :=
  ⟨⟨cl55MoritaEquivalence⟩⟩

section FiniteModules

open CategoryTheory
open scoped Matrix.Module

/-- The real module underlying a Clifford module, with its canonical scalar action. -/
abbrev cl55RealModule (M : ModuleCat Cl55) : ModuleCat ℝ :=
  (ModuleCat.restrictScalars (algebraMap ℝ Cl55)).obj M

/-- The Morita corner is a real subspace of the original Clifford module. -/
theorem cl55Morita_functor_finiteDimensional (M : ModuleCat Cl55)
    [FiniteDimensional ℝ (cl55RealModule M)] :
    FiniteDimensional ℝ (cl55MoritaEquivalence.eqv.functor.obj M) := by
  let f : cl55MoritaEquivalence.eqv.functor.obj M →ₗ[ℝ] cl55RealModule M :=
    { toFun := fun x => x.1
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        change (cl55SpinorAlgEquiv.symm (algebraMap ℝ _ r)) • (show M from x.1) =
          (algebraMap ℝ Cl55 r) • (show M from x.1)
        rw [AlgEquiv.commutes] }
  exact FiniteDimensional.of_injective f Subtype.val_injective

/-- The inverse Morita functor has the real carrier of a finite power of its input. -/
def cl55MoritaInverseLinearEquiv (V : ModuleCat ℝ) :
    cl55RealModule (cl55MoritaEquivalence.eqv.inverse.obj V) ≃ₗ[ℝ]
      (Fin (2 ^ 5) → V) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r x
        change (cl55SpinorAlgEquiv (algebraMap ℝ Cl55 r)) •
          (show Fin (2 ^ 5) → V from x) = r • (show Fin (2 ^ 5) → V from x)
        rw [AlgEquiv.commutes]
        exact Matrix.Module.scalar_smul r x }

/-- The inverse Morita functor preserves finite-dimensional real carriers. -/
theorem cl55Morita_inverse_finiteDimensional (V : ModuleCat ℝ)
    [FiniteDimensional ℝ V] :
    FiniteDimensional ℝ (cl55RealModule (cl55MoritaEquivalence.eqv.inverse.obj V)) :=
  LinearEquiv.finiteDimensional (cl55MoritaInverseLinearEquiv V).symm

/-- Exact real dimension of the inverse Morita image. -/
theorem cl55Morita_inverse_finrank (V : ModuleCat ℝ) [FiniteDimensional ℝ V] :
    Module.finrank ℝ (cl55RealModule (cl55MoritaEquivalence.eqv.inverse.obj V)) =
      32 * Module.finrank ℝ V := by
  rw [(cl55MoritaInverseLinearEquiv V).finrank_eq]
  simp [Module.finrank_pi_fintype]

/-- Clifford modules finite-dimensional over the base field, not merely finitely generated. -/
def cl55FiniteModules : ObjectProperty (ModuleCat Cl55) := fun M =>
  FiniteDimensional ℝ (cl55RealModule M)

/-- Finite-dimensional real modules as an existing-category object property. -/
def finiteRealModules : ObjectProperty (ModuleCat ℝ) := fun V => FiniteDimensional ℝ V

/-- Restriction of the actual ungraded Morita equivalence to finite-dimensional modules.
The unit and counit are inherited from the full module-category equivalence. -/
def cl55FiniteModuleEquivalence :
    cl55FiniteModules.FullSubcategory ≌ finiteRealModules.FullSubcategory where
  functor := finiteRealModules.lift (cl55FiniteModules.ι ⋙ cl55MoritaEquivalence.eqv.functor)
    (fun X => by
      let : FiniteDimensional ℝ (cl55RealModule X.obj) := X.property
      exact cl55Morita_functor_finiteDimensional X.obj)
  inverse := cl55FiniteModules.lift (finiteRealModules.ι ⋙ cl55MoritaEquivalence.eqv.inverse)
    (fun X => by
      let : FiniteDimensional ℝ X.obj := X.property
      exact cl55Morita_inverse_finiteDimensional X.obj)
  unitIso := (cl55FiniteModules.fullyFaithfulι.whiskeringRight _).preimageIso
    (cl55FiniteModules.ι.isoWhiskerLeft cl55MoritaEquivalence.eqv.unitIso)
  counitIso := (finiteRealModules.fullyFaithfulι.whiskeringRight _).preimageIso
    (finiteRealModules.ι.isoWhiskerLeft cl55MoritaEquivalence.eqv.counitIso)
  functor_unitIso_comp X :=
    ObjectProperty.hom_ext _ (cl55MoritaEquivalence.eqv.functor_unit_comp X.obj)

open scoped ModuleCat.Algebra

-- Prove the lift law before specializing, avoiding expansion of the Clifford
-- equivalence during elaboration of its scalar action on morphisms.
private theorem finiteModule_lift_linear
    {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [Linear ℝ C] [Linear ℝ D]
    (P : ObjectProperty D) (F : C ⥤ D) [F.Linear ℝ]
    (h : ∀ X, P (F.obj X)) : (P.lift F h).Linear ℝ where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    exact F.map_smul r f

/-- The finite-dimensional restriction retains real-linearity on morphisms. -/
instance cl55FiniteModuleEquivalence_functor_linear :
    cl55FiniteModuleEquivalence.functor.Linear ℝ :=
  finiteModule_lift_linear _ _ _

/-- The inverse finite-dimensional restriction is real-linear as well. -/
instance cl55FiniteModuleEquivalence_inverse_linear :
    cl55FiniteModuleEquivalence.inverse.Linear ℝ :=
  finiteModule_lift_linear _ _ _

end FiniteModules

theorem cl55SpinorAlgEquiv_toAlgHom_eq_representation :
    cl55SpinorAlgEquiv.toAlgHom = cl55SpinorRepresentation := by
  change (AlgEquiv.ofBijective cl55SpinorRepresentation _).toAlgHom =
    cl55SpinorRepresentation
  rfl

theorem realSplitPinSpinorUnitRepresentation_injective :
    Function.Injective realSplitPinSpinorUnitRepresentation := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  have hcoe := congrArg
      (fun u : (InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)ˣ =>
        (u : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5)) hgh
  have hrep :
      cl55SpinorRepresentation ((g : Cl55ˣ) : Cl55) =
        cl55SpinorRepresentation ((h : Cl55ˣ) : Cl55) := by
    simpa only [realSplitPinSpinorUnitRepresentation_coe] using hcoe
  rw [← cl55SpinorAlgEquiv_toAlgHom_eq_representation] at hrep
  exact cl55SpinorAlgEquiv.injective hrep

end

end InfoGeometry.Clifford.Clifford55
