/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Creation-sheet annihilator of the scalar vacuum

Creation acts by exterior multiplication on an arbitrary vector space. The
scalar vacuum has zero creation-sheet annihilator. This does not refute Cartan
purity: the full neutral Chevalley action includes covector contraction, and
`InfoGeometry.Clifford.scalarVacuum_isPureSpinor` proves full vacuum purity.
The previous contradictory rank-five pairing interface is not needed here.
-/
namespace InfoGeometry.Canonical.PureSpinor

variable {R W : Type*} [Field R] [AddCommGroup W] [Module R W]

/-- Creation by an exterior generator. -/
def creationAction (w : W) (ψ : ExteriorAlgebra R W) : ExteriorAlgebra R W :=
  ExteriorAlgebra.ι R w * ψ

/-- Only creation vectors are tested here, not the full neutral space. -/
def sheetAnnihilator (ψ : ExteriorAlgebra R W) : Submodule R W :=
  LinearMap.ker (show W →ₗ[R] ExteriorAlgebra R W from
    { toFun := fun w => ExteriorAlgebra.ι R w * ψ
      map_add' := fun _ _ => by simp [add_mul]
      map_smul' := fun c w => by
        simp only [map_smul, RingHom.id_apply, smul_mul_assoc] })

@[simp] theorem mem_sheetAnnihilator (ψ : ExteriorAlgebra R W) (w : W) :
    w ∈ sheetAnnihilator ψ ↔ creationAction w ψ = 0 := Iff.rfl

/-- Creation is faithful when evaluated on the scalar vacuum. -/
theorem creationAction_vacuum_eq_zero_iff (w : W) :
    creationAction w (1 : ExteriorAlgebra R W) = 0 ↔ w = 0 := by
  simp [creationAction]

theorem vacuum_annihilator_eq_bot :
    sheetAnnihilator (1 : ExteriorAlgebra R W) = ⊥ := by
  ext w
  exact creationAction_vacuum_eq_zero_iff (R := R) w

/-- A positive-rank creation sheet is not its scalar vacuum's annihilator. -/
theorem vacuum_annihilator_rank_lt (hW : 0 < Module.finrank R W) :
    Module.finrank R (sheetAnnihilator (1 : ExteriorAlgebra R W)) <
      Module.finrank R W := by
  rw [vacuum_annihilator_eq_bot]
  simpa using hW

/-- Failure of full creation-sheet rank is not failure of full Cartan purity. -/
theorem vacuum_creation_rank_ne (hW : 0 < Module.finrank R W) :
    Module.finrank R (sheetAnnihilator (1 : ExteriorAlgebra R W)) ≠
      Module.finrank R W :=
  ne_of_lt (vacuum_annihilator_rank_lt hW)

end InfoGeometry.Canonical.PureSpinor
