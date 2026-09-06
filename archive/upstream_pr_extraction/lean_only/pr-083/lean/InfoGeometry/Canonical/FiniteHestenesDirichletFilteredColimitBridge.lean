import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Tactic
import InfoGeometry.Canonical.HestenesRealModularRealizationBridge

/-!
# Finite Hestenes--Dirichlet readouts as a filtered colimit

This is the real bilingual replacement for an analytic extension of the
finite Dirichlet operator.  The coefficient stages are connected by
append-zero maps, while the readout at each stage is a finite sum of the
existing Hestenes modular-flow samples.  Compatibility is transported by the
native `ModuleCat` filtered colimit.

No infinite series, norm convergence, functional calculus, or analytic
continuation is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteHestenesDirichletFilteredColimitBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.HestenesRealModularRealizationBridge

abbrev HestenesDirichletStage (n : ℕ) := Fin (n + 1) → ℝ

def hestenesDirichletAppendZero (n : ℕ) :
    HestenesDirichletStage n →ₗ[ℝ] HestenesDirichletStage (n + 1) where
  toFun a i := if h : i.1 ≤ n then a ⟨i.1, Nat.lt_succ_of_le h⟩ else 0
  map_add' a b := by
    funext i
    by_cases h : i.1 ≤ n <;> simp [h]
  map_smul' c a := by
    funext i
    by_cases h : i.1 ≤ n <;> simp [h]

@[simp] theorem hestenesDirichletAppendZero_apply_castSucc
    (n : ℕ) (a : HestenesDirichletStage n) (i : Fin (n + 1)) :
    hestenesDirichletAppendZero n a i.castSucc = a i := by
  have hi : i.1 ≤ n := by omega
  simp [hestenesDirichletAppendZero, hi]

@[simp] theorem hestenesDirichletAppendZero_apply_finLast
    (n : ℕ) (a : HestenesDirichletStage n) :
    hestenesDirichletAppendZero n a (Fin.last (n + 1)) = 0 := by
  have hi : ¬ n + 1 ≤ n := by omega
  simp [hestenesDirichletAppendZero, hi]

def hestenesDirichletStageFunctor : ℕ ⥤ ModuleCat ℝ :=
  Functor.ofSequence (fun n =>
    ModuleCat.ofHom (hestenesDirichletAppendZero n))

def hestenesDirichletStageReadout
    {M : Type} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (n : ℕ) :
    HestenesDirichletStage n →ₗ[ℝ] Module.End ℝ M where
  toFun a := ∑ j : Fin (n + 1),
    (a j) • D.realFlow (Real.log (j.1 + 1 : ℕ))
  map_add' a b := by
    ext f
    simp [Finset.sum_add_distrib, add_smul]
  map_smul' c a := by
    ext f
    simp [Finset.smul_sum, smul_smul]

theorem hestenesDirichletStageReadout_compatible
    {M : Type} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (n : ℕ) (a : HestenesDirichletStage n) :
    hestenesDirichletStageReadout D (n + 1)
        (hestenesDirichletAppendZero n a) =
      hestenesDirichletStageReadout D n a := by
  ext f
  dsimp [hestenesDirichletStageReadout]
  rw [Fin.sum_univ_castSucc]
  simp [hestenesDirichletAppendZero_apply_castSucc,
    hestenesDirichletAppendZero_apply_finLast, Fin.val_castSucc, Fin.val_last]

def hestenesDirichletTargetFunctor
    {M : Type} [AddCommGroup M] [Module ℝ M] : ℕ ⥤ ModuleCat ℝ :=
  (Functor.const ℕ).obj (ModuleCat.of ℝ (M →ₗ[ℝ] M))

def hestenesDirichletReadoutNatTrans
    {M : Type} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) :
    hestenesDirichletStageFunctor ⟶ hestenesDirichletTargetFunctor (M := M) :=
  NatTrans.ofSequence
    (fun n => ModuleCat.ofHom (hestenesDirichletStageReadout D n))
    (by
      intro n
      apply ModuleCat.hom_ext
      ext a
      simpa [hestenesDirichletStageFunctor, hestenesDirichletTargetFunctor,
        Functor.ofSequence_map_homOfLE_succ, ModuleCat.comp_apply] using
        hestenesDirichletStageReadout_compatible D n a)

abbrev HestenesDirichletCoefficientColimit :=
  colimit hestenesDirichletStageFunctor

def hestenesDirichletReadoutColimitMap
    {M : Type} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) :
    HestenesDirichletCoefficientColimit ⟶
      colimit (hestenesDirichletTargetFunctor (M := M)) :=
  colim.map (hestenesDirichletReadoutNatTrans D)

theorem hestenesDirichletReadoutColimit_on_stage
    {M : Type} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (n : ℕ) (a : HestenesDirichletStage n) :
    hestenesDirichletReadoutColimitMap D
        ((colimit.ι hestenesDirichletStageFunctor n).hom a) =
      (colimit.ι (hestenesDirichletTargetFunctor (M := M)) n).hom
        (hestenesDirichletStageReadout D n a) := by
  exact congrArg (fun f => f a)
    (colimit.ι_map (hestenesDirichletReadoutNatTrans D) n)

/-- The filtered readout is uniquely determined by its finite-stage maps. -/
theorem hestenesDirichletReadoutColimitMap_unique
    {M : Type} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M)
    (g : HestenesDirichletCoefficientColimit ⟶
      colimit (hestenesDirichletTargetFunctor (M := M)))
    (hg : ∀ n : ℕ,
      (colimit.ι hestenesDirichletStageFunctor n) ≫ g =
        (hestenesDirichletReadoutNatTrans D).app n ≫
          colimit.ι (hestenesDirichletTargetFunctor (M := M)) n) :
    g = hestenesDirichletReadoutColimitMap D := by
  apply colimit.hom_ext
  intro n
  rw [hg n]
  exact (colimit.ι_map (hestenesDirichletReadoutNatTrans D) n).symm

theorem hestenesDirichletStageReadout_apply
    {M : Type} [AddCommGroup M] [Module ℝ M]
    (D : HestenesModularDatum M) (n : ℕ) (a : HestenesDirichletStage n)
    (x : M) :
    hestenesDirichletStageReadout D n a x =
      ∑ j : Fin (n + 1),
        (a j) • D.realFlow (Real.log (j.1 + 1 : ℕ)) x := by
  simp [hestenesDirichletStageReadout]

end InfoGeometry.Canonical.FiniteHestenesDirichletFilteredColimitBridge
