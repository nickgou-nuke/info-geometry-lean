import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import InfoGeometry.Meta.Architecture

open scoped ComplexConjugate

/-!
# A finite involution packet on `ℂ`

This module defines four explicit maps (identity, inversion, conjugation, and
their composite) and the predicate that a set is closed under them.  No
analytic zero-free or global covering theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry

/-- Labels for the four explicit involutive maps. -/
@[rep_depth thermo]
inductive V4
| id
| inv
| conj
| cpt
deriving DecidableEq, Repr

/-- The corresponding pointwise action on `ℂ`. -/
@[rep_depth thermo]
def v4Action (g : V4) (z : ℂ) : ℂ :=
  match g with
  | V4.id => z
  | V4.inv => z⁻¹
  | V4.conj => conj z
  | V4.cpt => (conj z)⁻¹

/-- A set is closed under all four explicit maps. -/
@[rep_depth thermo]
def IsV4Symmetric (S : Set ℂ) : Prop :=
  ∀ (g : V4) (z : ℂ), z ∈ S → v4Action g z ∈ S

@[simp] theorem v4Action_id_apply (z : ℂ) :
    v4Action V4.id z = z := rfl

@[simp] theorem v4Action_inv_apply (z : ℂ) :
    v4Action V4.inv z = z⁻¹ := rfl

@[simp] theorem v4Action_conj_apply (z : ℂ) :
    v4Action V4.conj z = conj z := rfl

@[simp] theorem v4Action_cpt_apply (z : ℂ) :
    v4Action V4.cpt z = (conj z)⁻¹ := rfl

@[simp] theorem v4Action_involutive
    (g : V4) (z : ℂ) :
    v4Action g (v4Action g z) = z := by
  cases g <;> simp [v4Action, conj_inv]

@[simp] theorem v4Action_comm
    (g h : V4) (z : ℂ) :
    v4Action g (v4Action h z) = v4Action h (v4Action g z) := by
  cases g <;> cases h <;> simp [v4Action, conj_inv]

/-- The `V₄` action preserves the unit circle. -/
theorem v4Action_preserves_unitCircle
    (g : V4) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖v4Action g z‖ = 1 := by
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz
    norm_num at hz
  cases g
  · simpa [v4Action] using hz
  · simp [v4Action, hz, hz0]
  · simpa [v4Action] using congrArg id (Complex.norm_conj z) ▸ hz
  · simp [v4Action, Complex.norm_conj, hz, hz0]

end InfoGeometry.Thermodynamics.AsanoKleinFourSymmetry
