import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

/-!
# MITF: Orientability-preserving flows

This file formalizes the split induced by a linear involution and proves that
any linear map commuting with the involution preserves the `+1` and `-1`
sectors.  The corresponding cross-sector leakage map vanishes.

The development is finite-dimensional in spirit but does not require
finite-dimensional hypotheses.
-/

noncomputable section

namespace MITF
namespace OrientabilityFlow

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Real-linear endomorphism abbreviation. -/
abbrev EndR (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  Module.End ℝ V

/-- Pointwise involution condition: `Ω² = 1`. -/
def IsInvolution (Ω : EndR V) : Prop :=
  ∀ x : V, Ω (Ω x) = x

/-- Positive orientability projector: `(1 + Ω)/2`. -/
def Splus (Ω : EndR V) : EndR V :=
  (1 / 2 : ℝ) • (1 + Ω)

/-- Negative orientability projector: `(1 - Ω)/2`. -/
def Sminus (Ω : EndR V) : EndR V :=
  (1 / 2 : ℝ) • (1 - Ω)

@[simp]
theorem Splus_apply (Ω : EndR V) (x : V) :
    Splus Ω x = (1 / 2 : ℝ) • (x + Ω x) := by
  simp [Splus]

@[simp]
theorem Sminus_apply (Ω : EndR V) (x : V) :
    Sminus Ω x = (1 / 2 : ℝ) • (x - Ω x) := by
  simp [Sminus]

lemma half_smul_add_self (x : V) : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x = x := by
  calc
    (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x
        = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • x := by
            simp [add_smul]
    _ = (1 : ℝ) • x := by
            rw [show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num]
    _ = x := by
            exact one_smul ℝ x

/-- The two orientability projectors sum to the identity. -/
theorem Splus_add_Sminus (Ω : EndR V) :
    Splus Ω + Sminus Ω = 1 := by
  ext x
  calc
    Splus Ω x + Sminus Ω x
        = (1 / 2 : ℝ) • (x + Ω x) + (1 / 2 : ℝ) • (x - Ω x) := by
            simp [Splus_apply, Sminus_apply]
    _ = (1 / 2 : ℝ) • ((x + Ω x) + (x - Ω x)) := by
            rw [← smul_add]
    _ = (1 / 2 : ℝ) • (x + x) := by
            congr 1
            abel
    _ = x := by
            simpa [smul_add] using half_smul_add_self x

/-- `Splus x` lies in the `+1` sector of the involution. -/
theorem involution_apply_Splus
    (Ω : EndR V) (hΩ : IsInvolution Ω) (x : V) :
    Ω (Splus Ω x) = Splus Ω x := by
  have hΩx : Ω (Ω x) = x := hΩ x
  simp [Splus_apply, hΩx, add_comm]

/-- `Sminus x` lies in the `-1` sector of the involution. -/
theorem involution_apply_Sminus
    (Ω : EndR V) (hΩ : IsInvolution Ω) (x : V) :
    Ω (Sminus Ω x) = - Sminus Ω x := by
  have hΩx : Ω (Ω x) = x := hΩ x
  have hswap : Ω x - x = -(x - Ω x) := by
    abel
  have hmain : Ω (Sminus Ω x) = (1 / 2 : ℝ) • (Ω x - Ω (Ω x)) := by
    rw [Sminus_apply, map_smul, map_sub]
  rw [hmain, hΩx, hswap, Sminus_apply]
  rw [smul_neg]

/-- `Splus` is idempotent. -/
theorem Splus_idempotent
    (Ω : EndR V) (hΩ : IsInvolution Ω) :
    (Splus Ω).comp (Splus Ω) = Splus Ω := by
  ext x
  have hfix : Ω (Splus Ω x) = Splus Ω x := by
    exact involution_apply_Splus Ω hΩ x
  calc
    Splus Ω (Splus Ω x)
        = (1 / 2 : ℝ) • (Splus Ω x + Ω (Splus Ω x)) := by
            simp [Splus_apply]
    _ = (1 / 2 : ℝ) • (Splus Ω x + Splus Ω x) := by
            rw [hfix]
    _ = Splus Ω x := by
            simpa [Splus_apply, smul_add] using half_smul_add_self (Splus Ω x)

/-- `Sminus` is idempotent. -/
theorem Sminus_idempotent
    (Ω : EndR V) (hΩ : IsInvolution Ω) :
    (Sminus Ω).comp (Sminus Ω) = Sminus Ω := by
  ext x
  have hanti : Ω (Sminus Ω x) = - Sminus Ω x := by
    exact involution_apply_Sminus Ω hΩ x
  calc
    Sminus Ω (Sminus Ω x)
        = (1 / 2 : ℝ) • (Sminus Ω x - Ω (Sminus Ω x)) := by
            rw [Sminus_apply]
    _ = (1 / 2 : ℝ) • (Sminus Ω x - - Sminus Ω x) := by
            rw [hanti]
    _ = (1 / 2 : ℝ) • (Sminus Ω x + Sminus Ω x) := by
            rw [sub_neg_eq_add]
    _ = Sminus Ω x := by
            simpa [Sminus_apply, smul_add] using half_smul_add_self (Sminus Ω x)

/-- The positive projector kills the negative sector. -/
theorem Splus_comp_Sminus
    (Ω : EndR V) (hΩ : IsInvolution Ω) :
    (Splus Ω).comp (Sminus Ω) = 0 := by
  ext x
  have hanti : Ω (Sminus Ω x) = - Sminus Ω x := by
    exact involution_apply_Sminus Ω hΩ x
  calc
    Splus Ω (Sminus Ω x)
        = (1 / 2 : ℝ) • (Sminus Ω x + Ω (Sminus Ω x)) := by
            rw [Splus_apply]
    _ = (1 / 2 : ℝ) • (Sminus Ω x + - Sminus Ω x) := by
            rw [hanti]
    _ = 0 := by
            simp

/-- The negative projector kills the positive sector. -/
theorem Sminus_comp_Splus
    (Ω : EndR V) (hΩ : IsInvolution Ω) :
    (Sminus Ω).comp (Splus Ω) = 0 := by
  ext x
  have hfix : Ω (Splus Ω x) = Splus Ω x := by
    exact involution_apply_Splus Ω hΩ x
  calc
    Sminus Ω (Splus Ω x)
        = (1 / 2 : ℝ) • (Splus Ω x - Ω (Splus Ω x)) := by
            rw [Sminus_apply]
    _ = (1 / 2 : ℝ) • (Splus Ω x - Splus Ω x) := by
            rw [hfix]
    _ = 0 := by
            simp

/-- A linear flow preserves the orientability split if it commutes with the involution. -/
def PreservesSplit (Ω F : EndR V) : Prop :=
  F.comp Ω = Ω.comp F

/-- The split leakage map: send the `+1` sector through `F` and then project to `-1`. -/
def splitLeakage (Ω F : EndR V) : EndR V :=
  (Sminus Ω).comp (F.comp (Splus Ω))

/-- A commuting flow preserves the positive sector. -/
theorem preserves_plus_sector
    (Ω F : EndR V) (hΩ : IsInvolution Ω)
    (hcomm : PreservesSplit Ω F) (x : V) :
    Ω (F (Splus Ω x)) = F (Splus Ω x) := by
  have hcomm_apply : ∀ y : V, F (Ω y) = Ω (F y) := by
    intro y
    simpa [PreservesSplit, LinearMap.comp_apply] using
      congrArg (fun T : EndR V => T y) hcomm
  calc
    Ω (F (Splus Ω x))
        = F (Ω (Splus Ω x)) := by
            simpa using (hcomm_apply (Splus Ω x)).symm
    _ = F (Splus Ω x) := by
            rw [involution_apply_Splus Ω hΩ x]

/-- A commuting flow preserves the negative sector. -/
theorem preserves_minus_sector
    (Ω F : EndR V) (hΩ : IsInvolution Ω)
    (hcomm : PreservesSplit Ω F) (x : V) :
    Ω (F (Sminus Ω x)) = - F (Sminus Ω x) := by
  have hcomm_apply : ∀ y : V, F (Ω y) = Ω (F y) := by
    intro y
    simpa [PreservesSplit, LinearMap.comp_apply] using
      congrArg (fun T : EndR V => T y) hcomm
  calc
    Ω (F (Sminus Ω x))
        = F (Ω (Sminus Ω x)) := by
            simpa using (hcomm_apply (Sminus Ω x)).symm
    _ = F (- Sminus Ω x) := by
            rw [involution_apply_Sminus Ω hΩ x]
    _ = - F (Sminus Ω x) := by
            simp

/-- The cross-sector leakage of a commuting flow vanishes. -/
theorem splitLeakage_eq_zero
    (Ω F : EndR V) (hΩ : IsInvolution Ω)
    (hcomm : PreservesSplit Ω F) :
    splitLeakage Ω F = 0 := by
  ext x
  change Sminus Ω (F (Splus Ω x)) = 0
  have hfix : Ω (F (Splus Ω x)) = F (Splus Ω x) :=
    preserves_plus_sector Ω F hΩ hcomm x
  calc
    Sminus Ω (F (Splus Ω x))
        = (1 / 2 : ℝ) • (F (Splus Ω x) - Ω (F (Splus Ω x))) := by
            simp [Sminus_apply]
    _ = (1 / 2 : ℝ) • (F (Splus Ω x) - F (Splus Ω x)) := by
            rw [hfix]
    _ = 0 := by
            simp

/-- If the flow preserves the split, it commutes with the orientability projectors. -/
theorem commutes_with_projectors
    (Ω F : EndR V)
    (hcomm : PreservesSplit Ω F) :
    F.comp (Splus Ω) = (Splus Ω).comp F ∧
    F.comp (Sminus Ω) = (Sminus Ω).comp F := by
  have hcomm_apply : ∀ y : V, F (Ω y) = Ω (F y) := by
    intro y
    simpa [PreservesSplit, LinearMap.comp_apply] using
      congrArg (fun T : EndR V => T y) hcomm
  constructor
  · ext x
    calc
      F (Splus Ω x) = (1 / 2 : ℝ) • (F x + Ω (F x)) := by
        simp [Splus_apply, hcomm_apply]
      _ = Splus Ω (F x) := by
        simp [Splus_apply]
  · ext x
    calc
      F (Sminus Ω x) = (1 / 2 : ℝ) • (F x - Ω (F x)) := by
        simp [Sminus_apply, hcomm_apply]
      _ = Sminus Ω (F x) := by
        simp [Sminus_apply]

/-- The orientability split defines a loss term that vanishes under symmetry. -/
theorem splitLoss_vanishes
    (Ω F : EndR V) (hΩ : IsInvolution Ω)
    (hcomm : PreservesSplit Ω F) :
    splitLeakage Ω F = 0 := by
  exact splitLeakage_eq_zero Ω F hΩ hcomm

end OrientabilityFlow
end MITF
