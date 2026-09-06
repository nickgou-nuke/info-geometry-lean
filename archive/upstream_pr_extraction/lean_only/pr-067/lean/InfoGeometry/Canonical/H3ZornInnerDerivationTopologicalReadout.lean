import InfoGeometry.Algebra.JordanInnerDerivations
import InfoGeometry.Canonical.H3ZornF4BasisTopologicalReadout
import InfoGeometry.Canonical.H3ZornTopCatReadout
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topology of the native inner Jordan derivation action

The algebraic owner proves that `[L_a,L_b]` is a genuine Jordan derivation.
Here we prove continuity of its action from the already continuous Jordan
product and package both the full-carrier action and its restriction to the
trace-zero input subtype.  No claim that the image preserves `traceZero` is
made in this file.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn

theorem continuous_h3ZornJordanInnerDerivation_action
    (a b : H3Zorn ℝ) :
    Continuous (fun x : H3Zorn ℝ =>
      a * (b * x) - b * (a * x)) := by
  have hid : Continuous (fun x : H3Zorn ℝ => x) := continuous_id
  have hconst_a : Continuous (fun _ : H3Zorn ℝ => a) := continuous_const
  have hconst_b : Continuous (fun _ : H3Zorn ℝ => b) := continuous_const
  have hpair_b : Continuous (fun x : H3Zorn ℝ => (b, x)) :=
    hconst_b.prodMk hid
  have hpair_a : Continuous (fun x : H3Zorn ℝ => (a, x)) :=
    hconst_a.prodMk hid
  have hbx : Continuous (fun x : H3Zorn ℝ => b * x) :=
    by
      simpa only [Function.comp_apply] using
        continuous_h3Zorn_jordanMul.comp hpair_b
  have hax : Continuous (fun x : H3Zorn ℝ => a * x) :=
    by
      simpa only [Function.comp_apply] using
        continuous_h3Zorn_jordanMul.comp hpair_a
  have hpair_a_bx : Continuous (fun x : H3Zorn ℝ => (a, b * x)) :=
    hconst_a.prodMk hbx
  have hpair_b_ax : Continuous (fun x : H3Zorn ℝ => (b, a * x)) :=
    hconst_b.prodMk hax
  have hab : Continuous (fun x : H3Zorn ℝ => a * (b * x)) :=
    by
      simpa only [Function.comp_apply] using
        continuous_h3Zorn_jordanMul.comp hpair_a_bx
  have hba : Continuous (fun x : H3Zorn ℝ => b * (a * x)) :=
    by
      simpa only [Function.comp_apply] using
        continuous_h3Zorn_jordanMul.comp hpair_b_ax
  exact hab.sub hba

def h3ZornJordanInnerDerivationContinuousMap (a b : H3Zorn ℝ) :
    ContinuousMap (H3Zorn ℝ) (H3Zorn ℝ) :=
  ContinuousMap.mk
    (fun x : H3Zorn ℝ => a * (b * x) - b * (a * x))
    (continuous_h3ZornJordanInnerDerivation_action a b)

@[simp] theorem h3ZornJordanInnerDerivationContinuousMap_apply
    (a b x : H3Zorn ℝ) :
    h3ZornJordanInnerDerivationContinuousMap a b x =
      (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) x := by
  change a * (b * x) - b * (a * x) = _
  exact (h3ZornJordanInnerDerivation_apply a b x).symm

def h3ZornJordanInnerDerivationTopCat (a b : H3Zorn ℝ) :
    TopCat.of (H3Zorn ℝ) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun x : H3Zorn ℝ => a * (b * x) - b * (a * x)
      continuous_toFun := continuous_h3ZornJordanInnerDerivation_action a b }

@[simp] theorem h3ZornJordanInnerDerivationTopCat_apply
    (a b x : H3Zorn ℝ) :
    h3ZornJordanInnerDerivationTopCat a b x =
      (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) x := by
  change a * (b * x) - b * (a * x) = _
  exact (h3ZornJordanInnerDerivation_apply a b x).symm

def h3ZornJordanInnerDerivationOnTraceZeroTopCat
    (a b : H3Zorn ℝ) :
    TopCat.of (traceZero (R := ℝ)) ⟶ TopCat.of (H3Zorn ℝ) :=
  TopCat.ofHom
    { toFun := fun x : traceZero (R := ℝ) =>
        a * (b * (x : H3Zorn ℝ)) - b * (a * (x : H3Zorn ℝ))
      continuous_toFun :=
        (continuous_h3ZornJordanInnerDerivation_action a b).comp
          continuous_subtype_val }

@[simp] theorem h3ZornJordanInnerDerivationOnTraceZeroTopCat_apply
    (a b x : traceZero (R := ℝ)) :
    h3ZornJordanInnerDerivationOnTraceZeroTopCat a b x =
      (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) (x : H3Zorn ℝ) := by
  change a * (b * (x : H3Zorn ℝ)) - b * (a * (x : H3Zorn ℝ)) = _
  exact (h3ZornJordanInnerDerivation_apply a b (x : H3Zorn ℝ)).symm

end InfoGeometry.Algebra
