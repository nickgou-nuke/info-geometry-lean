import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyHestenesWittGradedConcreteBridge

/-!
# Filtered-colimit transport of the graded Witt Cayley--Hestenes packet

The finite Witt realization is transported through the native `ModuleCat`
colimit API.  This owner records only algebraic transport: it makes no claim
about completion, topology, spectrum, or analytic convergence.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyHestenesWittGradedFilteredColimitBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CayleyHestenesGradedIntertwinerBridge
open InfoGeometry.Canonical.CayleyHestenesWittGradedConcreteBridge

abbrev WittConstantFunctor : ℕ ⥤ ModuleCat ℝ :=
  (Functor.const ℕ).obj (ModuleCat.of ℝ WittCarrier)

abbrev WittColimit := colimit WittConstantFunctor

def constantEndNatTrans (T : WittEnd) :
    WittConstantFunctor ⟶ WittConstantFunctor :=
  NatTrans.ofSequence
    (fun _ => ModuleCat.ofHom T)
    (by
      intro n
      apply ModuleCat.hom_ext
      ext x
      rfl)

def colimitEnd (T : WittEnd) :
    Module.End ℝ WittColimit :=
  (colim.map (constantEndNatTrans T)).hom

theorem colimitEnd_on_stage (T : WittEnd) (j : ℕ) (x : WittCarrier) :
    colimitEnd T ((colimit.ι WittConstantFunctor j).hom x) =
      (colimit.ι WittConstantFunctor j).hom (T x) := by
  have h := colimit.ι_map (constantEndNatTrans T) j
  exact congrArg (fun f => f x) h

theorem colimitEnd_mul (S T : WittEnd) :
    colimitEnd (S * T) = colimitEnd S * colimitEnd T := by
  have hcat :
      colim.map (constantEndNatTrans (S * T)) =
        colim.map (constantEndNatTrans T) ≫
          colim.map (constantEndNatTrans S) := by
    apply colimit.hom_ext
    intro j
    apply ModuleCat.Hom.ext
    ext x
    change colimitEnd (S * T)
        ((colimit.ι WittConstantFunctor j).hom x) =
      (colimitEnd S * colimitEnd T)
        ((colimit.ι WittConstantFunctor j).hom x)
    simp only [Module.End.mul_apply, colimitEnd_on_stage]
  simpa [colimitEnd, Module.End.mul_apply, ModuleCat.comp_apply] using
    congrArg ModuleCat.Hom.hom hcat

theorem colimitEnd_one :
    colimitEnd (1 : WittEnd) = (1 : Module.End ℝ WittColimit) := by
  have hcat : colim.map (constantEndNatTrans (1 : WittEnd)) =
      𝟙 (colimit WittConstantFunctor) := by
    apply colimit.hom_ext
    intro j
    apply ModuleCat.Hom.ext
    ext x
    change colimitEnd (1 : WittEnd)
        ((colimit.ι WittConstantFunctor j).hom x) =
      (colimit.ι WittConstantFunctor j).hom x
    rw [colimitEnd_on_stage]
    rfl
  simpa [colimitEnd] using congrArg ModuleCat.Hom.hom hcat

theorem colimitEnd_neg (T : WittEnd) :
    colimitEnd (-T) = -colimitEnd T := by
  have hcat : colim.map (constantEndNatTrans (-T)) =
      -(colim.map (constantEndNatTrans T)) := by
    apply colimit.hom_ext
    intro j
    apply ModuleCat.Hom.ext
    ext x
    change colimitEnd (-T)
        ((colimit.ι WittConstantFunctor j).hom x) =
      -(colimitEnd T ((colimit.ι WittConstantFunctor j).hom x))
    simp only [colimitEnd_on_stage]
    simp
  simpa [colimitEnd, LinearMap.neg_apply] using congrArg ModuleCat.Hom.hom hcat

def wittGradedColimitDatum :
    CayleyHestenesGradedDatum WittColimit := by
  let D := wittGradedDatum
  refine {
    K := colimitEnd D.K
    C := colimitEnd D.C
    M := colimitEnd D.M
    K_sq := ?_
    C_sq := ?_
    M_sq := ?_
    M_K_comm := ?_
    M_C_comm := ?_
    cayley_hestenes_twisted := ?_ }
  · calc
      colimitEnd D.K * colimitEnd D.K = colimitEnd (D.K * D.K) :=
        (colimitEnd_mul D.K D.K).symm
      _ = colimitEnd (-1) := congrArg colimitEnd D.K_sq
      _ = -colimitEnd 1 := colimitEnd_neg _
      _ = -(1 : Module.End ℝ WittColimit) := by rw [colimitEnd_one]
  · calc
      colimitEnd D.C * colimitEnd D.C = colimitEnd (D.C * D.C) :=
        (colimitEnd_mul D.C D.C).symm
      _ = colimitEnd 1 := congrArg colimitEnd D.C_sq
      _ = (1 : Module.End ℝ WittColimit) := colimitEnd_one
  · calc
      colimitEnd D.M * colimitEnd D.M = colimitEnd (D.M * D.M) :=
        (colimitEnd_mul D.M D.M).symm
      _ = colimitEnd 1 := congrArg colimitEnd D.M_sq
      _ = (1 : Module.End ℝ WittColimit) := colimitEnd_one
  · calc
      colimitEnd D.M * colimitEnd D.K = colimitEnd (D.M * D.K) :=
        (colimitEnd_mul D.M D.K).symm
      _ = colimitEnd (D.K * D.M) := congrArg colimitEnd D.M_K_comm
      _ = colimitEnd D.K * colimitEnd D.M := colimitEnd_mul _ _
  · calc
      colimitEnd D.M * colimitEnd D.C = colimitEnd (D.M * D.C) :=
        (colimitEnd_mul D.M D.C).symm
      _ = colimitEnd (D.C * D.M) := congrArg colimitEnd D.M_C_comm
      _ = colimitEnd D.C * colimitEnd D.M := colimitEnd_mul _ _
  · calc
      colimitEnd D.C * colimitEnd D.K = colimitEnd (D.C * D.K) :=
        (colimitEnd_mul D.C D.K).symm
      _ = colimitEnd (-(D.M * D.K * D.C)) :=
        congrArg colimitEnd D.cayley_hestenes_twisted
      _ = -colimitEnd (D.M * D.K * D.C) := colimitEnd_neg _
      _ = -(colimitEnd D.M * colimitEnd D.K * colimitEnd D.C) := by
        rw [colimitEnd_mul, colimitEnd_mul]

theorem wittGradedColimitDatum_on_stage (j : ℕ) (x : WittCarrier) :
    (wittGradedColimitDatum.C)
        ((colimit.ι WittConstantFunctor j).hom x) =
      (colimit.ι WittConstantFunctor j).hom (wittGradedDatum.C x) ∧
    (wittGradedColimitDatum.K)
        ((colimit.ι WittConstantFunctor j).hom x) =
      (colimit.ι WittConstantFunctor j).hom (wittGradedDatum.K x) ∧
    (wittGradedColimitDatum.M)
        ((colimit.ι WittConstantFunctor j).hom x) =
      (colimit.ι WittConstantFunctor j).hom (wittGradedDatum.M x) := by
  exact ⟨colimitEnd_on_stage _ j x, colimitEnd_on_stage _ j x,
    colimitEnd_on_stage _ j x⟩

theorem wittGradedColimit_plus_packet :
    (wittGradedColimitDatum.C * wittGradedColimitDatum.K +
        wittGradedColimitDatum.K * wittGradedColimitDatum.C) *
        ((1 : Module.End ℝ WittColimit) +
          wittGradedColimitDatum.M) = 0 :=
  twisted_cayley_plus_projector_packet wittGradedColimitDatum

theorem wittGradedColimit_minus_packet :
    (wittGradedColimitDatum.C * wittGradedColimitDatum.K -
        wittGradedColimitDatum.K * wittGradedColimitDatum.C) *
        ((1 : Module.End ℝ WittColimit) -
          wittGradedColimitDatum.M) = 0 :=
  twisted_cayley_minus_projector_packet wittGradedColimitDatum

end InfoGeometry.Canonical.CayleyHestenesWittGradedFilteredColimitBridge
