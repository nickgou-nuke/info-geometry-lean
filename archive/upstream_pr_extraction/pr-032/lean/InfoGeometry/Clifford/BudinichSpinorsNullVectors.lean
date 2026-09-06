import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Budinich Spinors and Null Vectors: first formal kernel

This module formalizes the first constructive layer of Marco Budinich's
spinor/null-vector interface.

The general part defines the annihilator of a spinor under a real linear
Clifford action, its nullity, and the totally-null condition.  The explicit
part proves, in the concrete two-component split model, that a null action
cuts the spinor carrier into two one-dimensional halves: its kernel and its
image.
-/

namespace InfoGeometry
namespace Clifford
namespace BudinichSpinorsNullVectors

variable {V S : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup S] [Module ℝ S]

/-- A real quadratic readout vanishes on a null vector. -/
def IsNullVector (Q : V → ℝ) (v : V) : Prop :=
  Q v = 0

/-- Evaluation of a real linear Clifford action at a fixed spinor. -/
def spinorEvaluationMap (act : V →ₗ[ℝ] S →ₗ[ℝ] S) (ψ : S) : V →ₗ[ℝ] S where
  toFun v := act v ψ
  map_add' v w := by
    simp
  map_smul' a v := by
    simp

/-- The vectors annihilating a spinor. -/
def spinorAnnihilator (act : V →ₗ[ℝ] S →ₗ[ℝ] S) (ψ : S) : Submodule ℝ V :=
  LinearMap.ker (spinorEvaluationMap act ψ)

/-- The dimension of the annihilator of a spinor. -/
noncomputable def spinorNullity [FiniteDimensional ℝ V]
    (act : V →ₗ[ℝ] S →ₗ[ℝ] S) (ψ : S) : ℕ :=
  Module.finrank ℝ (spinorAnnihilator act ψ)

/-- A subspace is totally null for a bilinear readout when all pairings vanish. -/
def IsTotallyNull (B : V → V → ℝ) (W : Submodule ℝ V) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, B x y = 0

/-- A real Clifford action satisfies the anticommutator relation for `B`. -/
def SatisfiesRealCliffordRelation
    (B : V → V → ℝ) (act : V →ₗ[ℝ] S →ₗ[ℝ] S) : Prop :=
  ∀ v w ψ, act v (act w ψ) + act w (act v ψ) = (2 * B v w) • ψ

/--
If a nonzero spinor is annihilated by two vectors and the Clifford relation
holds, then the two vectors are mutually null.
-/
theorem annihilator_pairing_eq_zero_of_realClifford
    {B : V → V → ℝ} {act : V →ₗ[ℝ] S →ₗ[ℝ] S}
    (hrel : SatisfiesRealCliffordRelation B act) {ψ : S} (hψ : ψ ≠ 0)
    {x y : V} (hx : x ∈ spinorAnnihilator act ψ) (hy : y ∈ spinorAnnihilator act ψ) :
    B x y = 0 := by
  have hx0 : act x ψ = 0 := hx
  have hy0 : act y ψ = 0 := hy
  have hrelxy := hrel x y ψ
  have hzero : (2 * B x y) • ψ = 0 := by
    simpa [hx0, hy0] using hrelxy.symm
  rcases smul_eq_zero.mp hzero with hcoef | hspin
  · nlinarith
  · exact (hψ hspin).elim

/-- The annihilator of a nonzero spinor is totally null. -/
theorem annihilator_totallyNull_of_realClifford
    {B : V → V → ℝ} {act : V →ₗ[ℝ] S →ₗ[ℝ] S}
    (hrel : SatisfiesRealCliffordRelation B act) {ψ : S} (hψ : ψ ≠ 0) :
    IsTotallyNull B (spinorAnnihilator act ψ) := by
  intro x hx y hy
  exact annihilator_pairing_eq_zero_of_realClifford hrel hψ hx hy

/-- A spinor is pure at maximal nullity `m`. -/
def IsPureSpinorOfNullity [FiniteDimensional ℝ V]
    (m : ℕ) (act : V →ₗ[ℝ] S →ₗ[ℝ] S) (ψ : S) : Prop :=
  ψ ≠ 0 ∧ spinorNullity act ψ = m

/-! ## Explicit two-component split-null action -/

/-- Two-component real spinor carrier. -/
abbrev Spinor2 : Type :=
  Fin 2 → ℝ

/-- First coordinate basis spinor. -/
def spinor2e0 : Spinor2 :=
  fun i => if i = 0 then 1 else 0

/-- Second coordinate basis spinor. -/
def spinor2e1 : Spinor2 :=
  fun i => if i = 1 then 1 else 0

theorem spinor2e0_ne_zero : spinor2e0 ≠ 0 := by
  intro h
  have h0 := congr_fun h 0
  norm_num [spinor2e0] at h0

theorem spinor2e1_ne_zero : spinor2e1 ≠ 0 := by
  intro h
  have h1 := congr_fun h 1
  norm_num [spinor2e1] at h1

/-- The upper nilpotent null action `ψ ↦ (ψ₁, 0)`. -/
def nullPlusAction : Spinor2 →ₗ[ℝ] Spinor2 where
  toFun ψ := fun i => if i = 0 then ψ 1 else 0
  map_add' ψ φ := by
    ext i
    fin_cases i <;> simp
  map_smul' a ψ := by
    ext i
    fin_cases i <;> simp

@[simp] theorem nullPlusAction_apply_zero (ψ : Spinor2) :
    nullPlusAction ψ 0 = ψ 1 := by
  simp [nullPlusAction]

@[simp] theorem nullPlusAction_apply_one (ψ : Spinor2) :
    nullPlusAction ψ 1 = 0 := by
  simp [nullPlusAction]

/-- The lower nilpotent null action `ψ ↦ (0, ψ₀)`. -/
def nullMinusAction : Spinor2 →ₗ[ℝ] Spinor2 where
  toFun ψ := fun i => if i = 1 then ψ 0 else 0
  map_add' ψ φ := by
    ext i
    fin_cases i <;> simp
  map_smul' a ψ := by
    ext i
    fin_cases i <;> simp

@[simp] theorem nullMinusAction_apply_zero (ψ : Spinor2) :
    nullMinusAction ψ 0 = 0 := by
  simp [nullMinusAction]

@[simp] theorem nullMinusAction_apply_one (ψ : Spinor2) :
    nullMinusAction ψ 1 = ψ 0 := by
  simp [nullMinusAction]

theorem nullPlusAction_square :
    nullPlusAction.comp nullPlusAction = 0 := by
  ext ψ i
  fin_cases i <;> simp

theorem nullMinusAction_square :
    nullMinusAction.comp nullMinusAction = 0 := by
  ext ψ i
  fin_cases i <;> simp

theorem nullPlusAction_ker_eq_span :
    LinearMap.ker nullPlusAction = ℝ ∙ spinor2e0 := by
  ext ψ
  constructor
  · intro hψ
    rw [Submodule.mem_span_singleton]
    refine ⟨ψ 0, ?_⟩
    ext i
    fin_cases i
    · simp [spinor2e0]
    · have hcoord := congr_fun hψ 0
      simp at hcoord
      simp [spinor2e0, hcoord]
  · intro hψ
    rw [Submodule.mem_span_singleton] at hψ
    rcases hψ with ⟨a, rfl⟩
    ext i
    fin_cases i <;> simp [spinor2e0]

theorem nullPlusAction_range_eq_span :
    LinearMap.range nullPlusAction = ℝ ∙ spinor2e0 := by
  ext ψ
  constructor
  · rintro ⟨φ, rfl⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨φ 1, ?_⟩
    ext i
    fin_cases i <;> simp [spinor2e0]
  · intro hψ
    rw [Submodule.mem_span_singleton] at hψ
    rcases hψ with ⟨a, rfl⟩
    refine ⟨fun i => if i = 1 then a else 0, ?_⟩
    ext i
    fin_cases i <;> simp [spinor2e0]

theorem nullMinusAction_ker_eq_span :
    LinearMap.ker nullMinusAction = ℝ ∙ spinor2e1 := by
  ext ψ
  constructor
  · intro hψ
    rw [Submodule.mem_span_singleton]
    refine ⟨ψ 1, ?_⟩
    ext i
    fin_cases i
    · have hcoord := congr_fun hψ 1
      simp at hcoord
      simp [spinor2e1, hcoord]
    · simp [spinor2e1]
  · intro hψ
    rw [Submodule.mem_span_singleton] at hψ
    rcases hψ with ⟨a, rfl⟩
    ext i
    fin_cases i <;> simp [spinor2e1]

theorem nullMinusAction_range_eq_span :
    LinearMap.range nullMinusAction = ℝ ∙ spinor2e1 := by
  ext ψ
  constructor
  · rintro ⟨φ, rfl⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨φ 0, ?_⟩
    ext i
    fin_cases i <;> simp [spinor2e1]
  · intro hψ
    rw [Submodule.mem_span_singleton] at hψ
    rcases hψ with ⟨a, rfl⟩
    refine ⟨fun i => if i = 0 then a else 0, ?_⟩
    ext i
    fin_cases i <;> simp [spinor2e1]

theorem nullPlusAction_finrank_ker :
    Module.finrank ℝ (LinearMap.ker nullPlusAction) = 1 := by
  rw [nullPlusAction_ker_eq_span]
  exact finrank_span_singleton spinor2e0_ne_zero

theorem nullPlusAction_finrank_range :
    Module.finrank ℝ (LinearMap.range nullPlusAction) = 1 := by
  rw [nullPlusAction_range_eq_span]
  exact finrank_span_singleton spinor2e0_ne_zero

theorem nullMinusAction_finrank_ker :
    Module.finrank ℝ (LinearMap.ker nullMinusAction) = 1 := by
  rw [nullMinusAction_ker_eq_span]
  exact finrank_span_singleton spinor2e1_ne_zero

theorem nullMinusAction_finrank_range :
    Module.finrank ℝ (LinearMap.range nullMinusAction) = 1 := by
  rw [nullMinusAction_range_eq_span]
  exact finrank_span_singleton spinor2e1_ne_zero

theorem spinor2_finrank :
    Module.finrank ℝ Spinor2 = 2 := by
  simp

/--
Concrete Budinich bisection in the split `2 × 2` null model: the null action
has one-dimensional kernel and one-dimensional image inside a two-dimensional
spinor carrier.
-/
theorem nullPlusAction_bisects_spinor2 :
    Module.finrank ℝ (LinearMap.ker nullPlusAction) = 1
      ∧ Module.finrank ℝ (LinearMap.range nullPlusAction) = 1
      ∧ 2 * Module.finrank ℝ (LinearMap.ker nullPlusAction) =
          Module.finrank ℝ Spinor2
      ∧ 2 * Module.finrank ℝ (LinearMap.range nullPlusAction) =
          Module.finrank ℝ Spinor2 := by
  constructor
  · exact nullPlusAction_finrank_ker
  constructor
  · exact nullPlusAction_finrank_range
  constructor
  · rw [nullPlusAction_finrank_ker, spinor2_finrank]
  · rw [nullPlusAction_finrank_range, spinor2_finrank]

/--
The lower null action gives the same bisection: one-dimensional kernel and
one-dimensional image inside the same two-dimensional carrier.
-/
theorem nullMinusAction_bisects_spinor2 :
    Module.finrank ℝ (LinearMap.ker nullMinusAction) = 1
      ∧ Module.finrank ℝ (LinearMap.range nullMinusAction) = 1
      ∧ 2 * Module.finrank ℝ (LinearMap.ker nullMinusAction) =
          Module.finrank ℝ Spinor2
      ∧ 2 * Module.finrank ℝ (LinearMap.range nullMinusAction) =
          Module.finrank ℝ Spinor2 := by
  constructor
  · exact nullMinusAction_finrank_ker
  constructor
  · exact nullMinusAction_finrank_range
  constructor
  · rw [nullMinusAction_finrank_ker, spinor2_finrank]
  · rw [nullMinusAction_finrank_range, spinor2_finrank]

/--
A spinor annihilated by the upper null action is exactly a scalar multiple of
the basis spinor spanning its associated totally null plane.
-/
theorem nullPlusAction_spinor_eq_span_singleton
    (ψ : Spinor2) (hψ : nullPlusAction ψ = 0) :
    ∃ a : ℝ, ψ = a • spinor2e0 := by
  have hker : ψ ∈ LinearMap.ker nullPlusAction := by
    simpa [LinearMap.mem_ker] using hψ
  rw [nullPlusAction_ker_eq_span] at hker
  rw [Submodule.mem_span_singleton] at hker
  rcases hker with ⟨a, ha⟩
  exact ⟨a, ha.symm⟩

/--
A spinor annihilated by the lower null action is exactly a scalar multiple of
the basis spinor spanning its associated totally null plane.
-/
theorem nullMinusAction_spinor_eq_span_singleton
    (ψ : Spinor2) (hψ : nullMinusAction ψ = 0) :
    ∃ a : ℝ, ψ = a • spinor2e1 := by
  have hker : ψ ∈ LinearMap.ker nullMinusAction := by
    simpa [LinearMap.mem_ker] using hψ
  rw [nullMinusAction_ker_eq_span] at hker
  rw [Submodule.mem_span_singleton] at hker
  rcases hker with ⟨a, ha⟩
  exact ⟨a, ha.symm⟩

end BudinichSpinorsNullVectors
end Clifford
end InfoGeometry
