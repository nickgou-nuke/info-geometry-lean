/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Canonical.SouriauKKSForm
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Algebraic source/target linearization at a cotangent unit

For a real Lie algebra `g` and `α : g*`, the map
`poissonSharp α X = -⁅X, α⁆` has evaluation `α ⁅X, Y⁆`.
It is the curried algebraic KKS form already owned by `SouriauKKS`.

On the existing phase-space carrier `g × g*`, the source model is projection
onto the second coordinate and the target model subtracts `poissonSharp α`
from that coordinate. Both are native linear maps. Their difference,
midpoint, and reconstruction identities are proved at the linear-map level.

These are algebraic linearization models with an explicit sign convention.
No theorem here identifies them with `fderiv` or `mfderiv` of smooth
cotangent-groupoid source and target maps. Such an identification requires
a Lie-group and cotangent-bundle construction together with its derivative proof.
-/

noncomputable section

namespace InfoGeometry.Geometry.CotangentUnitLinearization

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {g : Type*} [LieRing g] [LieAlgebra ℝ g]

/-- The infinitesimal Lie-Poisson map in the convention
`poissonSharp α X Y = α ⁅X, Y⁆`. -/
def poissonSharp (α : Module.Dual ℝ g) : g →ₗ[ℝ] Module.Dual ℝ g where
  toFun X := -⁅X, α⁆
  map_add' X Y := by simp only [add_lie, neg_add]
  map_smul' r X := by simp only [smul_lie, smul_neg, RingHom.id_apply]

@[simp] theorem poissonSharp_apply (α : Module.Dual ℝ g) (X : g) :
    poissonSharp α X = -⁅X, α⁆ := rfl

@[simp] theorem poissonSharp_apply_apply (α : Module.Dual ℝ g) (X Y : g) :
    poissonSharp α X Y = α ⁅X, Y⁆ := by
  simp [poissonSharp]

/-- The map is the existing algebraic KKS form with its first argument bundled. -/
theorem poissonSharp_eq_kksForm (α : Module.Dual ℝ g) (X Y : g) :
    poissonSharp α X Y = SouriauKKS.kksForm α X Y :=
  poissonSharp_apply_apply α X Y

theorem poissonSharp_skew (α : Module.Dual ℝ g) (X Y : g) :
    poissonSharp α X Y = -poissonSharp α Y X := by
  simpa only [poissonSharp_eq_kksForm] using SouriauKKS.kksForm_skew α X Y

@[simp] theorem poissonSharp_self (α : Module.Dual ℝ g) (X : g) :
    poissonSharp α X X = 0 := by
  simp

/-- Kernel membership is exactly annihilation of every bracket against `X`. -/
theorem mem_ker_poissonSharp_iff (α : Module.Dual ℝ g) (X : g) :
    X ∈ LinearMap.ker (poissonSharp α) ↔ ∀ Y : g, α ⁅X, Y⁆ = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h Y
    have hY := congrArg (fun β : Module.Dual ℝ g => β Y) h
    simpa only [poissonSharp_apply_apply, LinearMap.zero_apply] using hY
  · intro h
    apply LinearMap.ext
    intro Y
    simpa only [poissonSharp_apply_apply, LinearMap.zero_apply] using h Y

/-- The kernel is the infinitesimal coadjoint stabilizer of `α`. -/
theorem mem_ker_poissonSharp_iff_coadjoint (α : Module.Dual ℝ g) (X : g) :
    X ∈ LinearMap.ker (poissonSharp α) ↔ ⁅X, α⁆ = 0 := by
  rw [LinearMap.mem_ker, poissonSharp_apply, neg_eq_zero]

/-- Algebraic source linearization: projection onto the dual coordinate. -/
def unitSource : PhaseSpaceCarrier g →ₗ[ℝ] Module.Dual ℝ g :=
  LinearMap.snd ℝ g (Module.Dual ℝ g)

/-- Algebraic target linearization with the stated Lie-Poisson sign convention. -/
def unitTarget (α : Module.Dual ℝ g) : PhaseSpaceCarrier g →ₗ[ℝ] Module.Dual ℝ g :=
  unitSource - (poissonSharp α).comp (LinearMap.fst ℝ g (Module.Dual ℝ g))

@[simp] theorem unitSource_apply (v : PhaseSpaceCarrier g) :
    unitSource v = v.2 := rfl

@[simp] theorem unitTarget_apply (α : Module.Dual ℝ g) (v : PhaseSpaceCarrier g) :
    unitTarget α v = v.2 - poissonSharp α v.1 := rfl

/-- The difference cancels the dual-coordinate variation, as an equality of linear maps. -/
theorem unitSource_sub_unitTarget (α : Module.Dual ℝ g) :
    unitSource - unitTarget α =
      (poissonSharp α).comp (LinearMap.fst ℝ g (Module.Dual ℝ g)) := by
  unfold unitTarget
  abel

theorem unitSource_sub_unitTarget_apply (α : Module.Dual ℝ g) (v : PhaseSpaceCarrier g) :
    unitSource v - unitTarget α v = poissonSharp α v.1 := by
  simp only [unitSource_apply, unitTarget_apply]
  abel

/-- The midpoint is source projection minus half the coadjoint drift. -/
theorem unit_midpoint (α : Module.Dual ℝ g) :
    (1 / 2 : ℝ) • (unitSource + unitTarget α) =
      unitSource - (1 / 2 : ℝ) •
        ((poissonSharp α).comp (LinearMap.fst ℝ g (Module.Dual ℝ g))) := by
  unfold unitTarget
  module

/-- Source reconstruction from the symmetric midpoint and antisymmetric difference. -/
theorem unitSource_reconstruction (α : Module.Dual ℝ g) :
    unitSource =
      (1 / 2 : ℝ) • (unitSource + unitTarget α) +
        (1 / 2 : ℝ) • (unitSource - unitTarget α) := by
  module

/-- Target reconstruction from the same midpoint and difference. -/
theorem unitTarget_reconstruction (α : Module.Dual ℝ g) :
    unitTarget α =
      (1 / 2 : ℝ) • (unitSource + unitTarget α) -
        (1 / 2 : ℝ) • (unitSource - unitTarget α) := by
  module

/-- Source and target models agree precisely on the infinitesimal coadjoint stabilizer. -/
theorem unitSource_eq_unitTarget_iff (α : Module.Dual ℝ g) (v : PhaseSpaceCarrier g) :
    unitSource v = unitTarget α v ↔ ⁅v.1, α⁆ = 0 := by
  calc
    (unitSource v = unitTarget α v) ↔ unitSource v - unitTarget α v = 0 :=
      sub_eq_zero.symm
    _ ↔ poissonSharp α v.1 = 0 := by rw [unitSource_sub_unitTarget_apply]
    _ ↔ ⁅v.1, α⁆ = 0 := by simp only [poissonSharp_apply, neg_eq_zero]

end InfoGeometry.Geometry.CotangentUnitLinearization
