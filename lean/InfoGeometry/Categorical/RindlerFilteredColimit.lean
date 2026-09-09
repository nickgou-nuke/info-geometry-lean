import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Filtered
import InfoGeometry.Categorical.TwoSheetKreinFilteredColimit
import InfoGeometry.Dynamics.RindlerWedge

/-!
# Finite Rindler boosts through a filtered module colimit

This file transports the already verified finite real light-cone boost law to a
filtered colimit.  The diagram is constant, so the result is deliberately an
algebraic colimit statement: it does not assert an analytic Rindler wedge,
KMS condition, Unruh theorem, or Bisognano--Wichmann theorem.
-/

noncomputable section

namespace InfoGeometry.Categorical.RindlerFilteredColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Categorical.TwoSheetKreinFilteredColimit
open InfoGeometry.Dynamics.HyperbolicComponent
open InfoGeometry.Dynamics.RapiditySpace

abbrev RindlerStage := Matrix (Fin 2) (Fin 2) ℝ

abbrev StageFunctor : ℕ ⥤ ModuleCat ℝ :=
  (Functor.const ℕ).obj (ModuleCat.of ℝ RindlerStage)

def stageMap (lam : ℝ) : RindlerStage →ₗ[ℝ] RindlerStage :=
  LinearMap.mulLeft ℝ (componentAReal lam)

def stageFlow (lam : ℝ) : StageFunctor ⟶ StageFunctor :=
  NatTrans.ofSequence
    (fun _ => ModuleCat.ofHom (stageMap lam))
    (by
      intro n
      apply ModuleCat.hom_ext
      rfl)

def colimitFlow (lam : ℝ) : Module.End ℝ (Carrier StageFunctor) :=
  colimitEnd (stageFlow lam)

@[simp] theorem colimitFlow_on_stage (lam : ℝ) (n : ℕ) (x : RindlerStage) :
    colimitFlow lam ((colimit.ι StageFunctor n).hom x) =
      (colimit.ι StageFunctor n).hom (componentAReal lam * x) := by
  exact colimitEnd_on_stage (stageFlow lam) n x

theorem colimitFlow_preserves_lightcone_product_on_stage
    (lam : ℝ) (n : ℕ) (x : RindlerStage) :
    (colimitFlow lam ((colimit.ι StageFunctor n).hom x)) =
      (colimit.ι StageFunctor n).hom (componentAReal lam * x) := by
  exact colimitFlow_on_stage lam n x

end InfoGeometry.Categorical.RindlerFilteredColimit
