import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Tactic
import InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

/-!
# Finite Dirichlet readouts as a native filtered colimit

The coefficient space at depth `n` is `Fin (n+1) → ℂ`.  The bonding map appends
a zero coefficient.  Finite logarithmic translation sums are compatible with
this bonding map, so the readout is transported by `NatTrans` and `colim.map`.
This is the algebraic substitute for an infinite operator extension.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteDirichletFilteredColimitBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Analysis.FiniteDirichletShiftOperatorBridge

abbrev DirichletStage (n : ℕ) := Fin (n + 1) → ℂ
abbrev DirichletTarget := ScaleEnd

def dirichletAppendZero (n : ℕ) :
    DirichletStage n →ₗ[ℂ] DirichletStage (n + 1) where
  toFun a i := if h : i.1 < n + 1 then a ⟨i.1, h⟩ else 0
  map_add' a b := by
    funext i
    by_cases h : i.1 ≤ n <;> simp [h]
  map_smul' c a := by
    funext i
    by_cases h : i.1 ≤ n <;> simp [h]

@[simp] theorem dirichletAppendZero_apply_old
    (n : ℕ) (a : DirichletStage n) (i : Fin (n + 1)) :
    dirichletAppendZero n a ⟨i.1, Nat.lt_succ_of_lt i.2⟩ = a i := by
  have hi : i.1 ≤ n := by omega
  simp [dirichletAppendZero, hi]

@[simp] theorem dirichletAppendZero_apply_last
    (n : ℕ) (a : DirichletStage n) :
    dirichletAppendZero n a ⟨n + 1, Nat.lt_succ_self _⟩ = 0 := by
  have hi : ¬ n + 1 ≤ n := by omega
  simp [dirichletAppendZero, hi]

@[simp] theorem dirichletAppendZero_apply_castSucc
    (n : ℕ) (a : DirichletStage n) (i : Fin (n + 1)) :
    dirichletAppendZero n a i.castSucc = a i := by
  exact dirichletAppendZero_apply_old n a i

@[simp] theorem dirichletAppendZero_apply_finLast
    (n : ℕ) (a : DirichletStage n) :
    dirichletAppendZero n a (Fin.last (n + 1)) = 0 := by
  simp [dirichletAppendZero]

theorem dirichletAppendZero_injective (n : ℕ) :
    Function.Injective (dirichletAppendZero n) := by
  intro a b h
  funext i
  have h' := congrArg (fun x : DirichletStage (n + 1) => x i.castSucc) h
  simpa using h'

def dirichletStageFunctor : ℕ ⥤ ModuleCat ℂ :=
  Functor.ofSequence (fun n =>
    ModuleCat.ofHom (dirichletAppendZero n))

def finiteDirichletStageReadout (n : ℕ) :
    DirichletStage n →ₗ[ℂ] DirichletTarget where
  toFun a := ∑ j : Fin (n + 1),
    (a j) • translationShift (Real.log (j.1 + 1 : ℕ))
  map_add' a b := by
    ext f t
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c a := by
    ext f t
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem finiteDirichletStageReadout_compatible (n : ℕ) (a : DirichletStage n) :
    finiteDirichletStageReadout (n + 1) (dirichletAppendZero n a) =
      finiteDirichletStageReadout n a := by
  ext f t
  dsimp [finiteDirichletStageReadout]
  rw [Fin.sum_univ_castSucc]
  simp [dirichletAppendZero_apply_castSucc,
    dirichletAppendZero_apply_finLast, Fin.val_castSucc, Fin.val_last]

def dirichletReadoutTargetFunctor : ℕ ⥤ ModuleCat ℂ :=
  (Functor.const ℕ).obj (ModuleCat.of ℂ DirichletTarget)

def dirichletReadoutNatTrans :
    dirichletStageFunctor ⟶ dirichletReadoutTargetFunctor :=
  NatTrans.ofSequence
    (fun n => ModuleCat.ofHom (finiteDirichletStageReadout n))
    (by
      intro n
      apply ModuleCat.hom_ext
      ext a
      simpa [dirichletStageFunctor, dirichletReadoutTargetFunctor,
        Functor.ofSequence_map_homOfLE_succ, ModuleCat.comp_apply] using
        finiteDirichletStageReadout_compatible n a)

abbrev DirichletCoefficientColimit := colimit dirichletStageFunctor
abbrev DirichletReadoutColimit := colimit dirichletReadoutTargetFunctor

def dirichletReadoutColimitMap :
    DirichletCoefficientColimit ⟶ DirichletReadoutColimit :=
  colim.map dirichletReadoutNatTrans

@[simp] theorem dirichletReadoutColimit_on_stage (n : ℕ) (a : DirichletStage n) :
    dirichletReadoutColimitMap ((colimit.ι dirichletStageFunctor n).hom a) =
      (colimit.ι dirichletReadoutTargetFunctor n).hom
        (finiteDirichletStageReadout n a) := by
  exact congrArg (fun f => f a) (colimit.ι_map dirichletReadoutNatTrans n)

theorem finiteDirichlet_stage_readout_is_logarithmic_shift (n : ℕ)
    (a : DirichletStage n) (s : ℂ) (t : ℝ) :
    (finiteDirichletStageReadout n a) (exponentialTest s) t =
      (∑ j : Fin (n + 1),
        a j * Complex.exp (-s * (Real.log (j.1 + 1 : ℕ) : ℂ))) *
        exponentialTest s t := by
  simp only [finiteDirichletStageReadout, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [translationShift_exponentialTest]
  ring

end InfoGeometry.Canonical.FiniteDirichletFilteredColimitBridge
