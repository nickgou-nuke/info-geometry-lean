import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

/-!
# MITF: Orientability projectors from a linear involution

Given a real-linear involution `Ω`, define

  `Splus = (1 + Ω)/2`
  `Sminus = (1 - Ω)/2`

and prove:

* `Splus + Sminus = 1`;
* `Splus` and `Sminus` are idempotent projectors;
* `Splus ∘ Sminus = 0` and `Sminus ∘ Splus = 0`;
* the range of `Splus` is the `+1` eigenspace of `Ω`;
* the range of `Sminus` is the `-1` eigenspace of `Ω`.

This is the theorem-honest algebraic core of the orientability/chiral parity split.
-/

noncomputable section

namespace MITF
namespace Orientability

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
  have h : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • x := by
    rw [← add_smul]
  rw [h]
  norm_num

/-- The two orientability projectors sum to the identity. -/
theorem Splus_add_Sminus (Ω : EndR V) :
    Splus Ω + Sminus Ω = 1 := by
  ext x
  simp [Splus, Sminus, smul_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  module

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
  module

/-- `Splus` is idempotent. -/
theorem Splus_idempotent
    (Ω : EndR V) (hΩ : IsInvolution Ω) :
    (Splus Ω).comp (Splus Ω) = Splus Ω := by
  ext x
  have hfix : Ω (Splus Ω x) = Splus Ω x := by
    have hΩx : Ω (Ω x) = x := hΩ x
    simp [Splus_apply, hΩx, add_comm]
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
    have hΩx : Ω (Ω x) = x := hΩ x
    have hswap : Ω x - x = -(x - Ω x) := by
      abel
    have hmain : Ω (Sminus Ω x) = (1 / 2 : ℝ) • (Ω x - Ω (Ω x)) := by
      rw [Sminus_apply, map_smul, map_sub]
    rw [hmain, hΩx, hswap, Sminus_apply]
    module
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
    have hΩx : Ω (Ω x) = x := hΩ x
    have hswap : Ω x - x = -(x - Ω x) := by
      abel
    have hmain : Ω (Sminus Ω x) = (1 / 2 : ℝ) • (Ω x - Ω (Ω x)) := by
      rw [Sminus_apply, map_smul, map_sub]
    rw [hmain, hΩx, hswap, Sminus_apply]
    module
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
    have hΩx : Ω (Ω x) = x := hΩ x
    simp [Splus_apply, hΩx, add_comm]
  calc
    Sminus Ω (Splus Ω x)
        = (1 / 2 : ℝ) • (Splus Ω x - Ω (Splus Ω x)) := by
            rw [Sminus_apply]
    _ = (1 / 2 : ℝ) • (Splus Ω x - Splus Ω x) := by
            rw [hfix]
    _ = 0 := by
            simp

/-- The range of `Splus` is exactly the `+1` eigenspace of `Ω`. -/
theorem range_Splus_eq_eigenspace_one
    (Ω : EndR V) (hΩ : IsInvolution Ω) :
    LinearMap.range (Splus Ω) = Ω.eigenspace (1 : ℝ) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    have hΩx : Ω (Ω x) = x := hΩ x
    simpa [Splus_apply, hΩx, add_comm]
  · intro y hy
    rw [Module.End.mem_eigenspace_iff] at hy
    refine ⟨y, ?_⟩
    have hfix : Ω y = y := by
      simpa using hy
    calc
      Splus Ω y
          = (1 / 2 : ℝ) • (y + Ω y) := by
              simp [Splus_apply]
      _ = (1 / 2 : ℝ) • (y + y) := by
              rw [hfix]
      _ = y := by
              simpa [smul_add] using half_smul_add_self y

/-- The range of `Sminus` is exactly the `-1` eigenspace of `Ω`. -/
theorem range_Sminus_eq_eigenspace_neg_one
    (Ω : EndR V) (hΩ : IsInvolution Ω) :
    LinearMap.range (Sminus Ω) = Ω.eigenspace (-1 : ℝ) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [one_smul] using (involution_apply_Sminus Ω hΩ x)
  · intro y hy
    rw [Module.End.mem_eigenspace_iff] at hy
    refine ⟨y, ?_⟩
    have hanti : Ω y = - y := by
      simpa using hy
    calc
      Sminus Ω y
          = (1 / 2 : ℝ) • (y - Ω y) := by
              simp [Sminus_apply]
      _ = (1 / 2 : ℝ) • (y - - y) := by
              rw [hanti]
      _ = (1 / 2 : ℝ) • (y + y) := by
              rw [sub_neg_eq_add]
      _ = y := by
              simpa [smul_add] using half_smul_add_self y


end Orientability
end MITF
