/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.AlgCat.Limits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# Algebraic Colimit Transport of Compatible Staged Functionals

This module formalizes purely algebraic compatibility and transport for normalized
linear functionals across sequential `AlgHom` towers and Mathlib's `ℕ ⥤ AlgCat ℂ`
categorical colimit:
1. `categoricalStageState_rep_equality` & `categoricalStageState_kms_descent`:
   Pulls back a colimit linear functional `Omega : (colimit F) →ₗ[ℂ] ℂ` along
   `colimit.ι F n` and transports any supplied stage-`n` equality `a * bthermal = bshift * a`
   under `categoricalStageState Omega n` to the colimit algebra.
2. `iota_seq` & `staged_state_m_step_compatibility`: Multi-step compatibility
   `ω_{n+m} ∘ ι_{n, m} = ω_n` for `StagedKMSFamily`.
3. `colimit_state_rep_equality` & `colimit_kms_thermal_condition`:
   Given a `ColimitKMSState` compatibility witness (`Omega ∘ psi n = omega n`) and a
   supplied stage-`n` equality `omega n (a * b_thermal) = omega n (b_shift * a)`,
   deduces `Omega (psi n a * psi n b_thermal) = Omega (psi n b_shift * psi n a)`.

No C*-norm completion or analytic KMS strip condition is constructed here.
-/

noncomputable section

namespace InfoGeometry.Modular.Colimit

open CategoryTheory CategoryTheory.Limits

/-!  The following interface uses Mathlib's actual categorical colimit.  The
    generic staged API above remains useful for algebraic calculations, while
    this section records the descent statement against a genuine cocone. -/

section Categorical

variable {F : ℕ ⥤ AlgCat ℂ} [HasColimit F]

/-- The state induced on a stage by a linear functional on the categorical
colimit. -/
def categoricalStageState (Omega : (colimit F : AlgCat ℂ) →ₗ[ℂ] ℂ) (n : ℕ) :
    (F.obj n) →ₗ[ℂ] ℂ :=
  Omega.comp (colimit.ι F n).hom.toLinearMap

theorem categoricalStageState_rep_equality
    (Omega : (colimit F : AlgCat ℂ) →ₗ[ℂ] ℂ)
    (n m : ℕ) (x : F.obj n) (y : F.obj m)
    (h : (colimit.ι F n) x = (colimit.ι F m) y) :
    categoricalStageState Omega n x = categoricalStageState Omega m y := by
  change Omega ((colimit.ι F n) x) = Omega ((colimit.ι F m) y)
  rw [h]

theorem categoricalStageState_kms_descent
    (Omega : (colimit F : AlgCat ℂ) →ₗ[ℂ] ℂ)
    (n : ℕ) (a bthermal bshift : F.obj n)
    (hKMS : categoricalStageState Omega n (a * bthermal) =
      categoricalStageState Omega n (bshift * a)) :
      Omega ((colimit.ι F n) a * (colimit.ι F n) bthermal) =
      Omega ((colimit.ι F n) bshift * (colimit.ι F n) a) := by
  have hmul₁ := congrArg Omega ((colimit.ι F n).hom.map_mul a bthermal)
  have hmul₂ := congrArg Omega ((colimit.ι F n).hom.map_mul bshift a)
  change Omega ((colimit.ι F n).hom.toRingHom a *
      (colimit.ι F n).hom.toRingHom bthermal) =
    Omega ((colimit.ι F n).hom.toRingHom bshift *
      (colimit.ι F n).hom.toRingHom a)
  rw [← hmul₁, ← hmul₂]
  simpa [categoricalStageState] using hKMS

end Categorical

variable {A : ℕ → Type*} [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
variable (iota : ∀ n, A n →ₐ[ℂ] A (n + 1))

/-- Multi-step forward inclusion map: ι_{n, m} : A_n → A_{n+m}. -/
def iota_seq (n : ℕ) : ∀ m, A n →ₐ[ℂ] A (n + m)
| 0 => AlgHom.id ℂ (A n)
| m + 1 => (iota (n + m)).comp (iota_seq n m)

variable {A_inf : Type*} [Ring A_inf] [Algebra ℂ A_inf]

/-- Cocycle commutativity of colimit morphisms: ψ_{n+m} ∘ ι_{n, m} = ψ_n. -/
theorem psi_comp_iota_seq
    (psi : ∀ n, A n →ₐ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (n m : ℕ) :
    (psi (n + m)).comp (iota_seq iota n m) = psi n := by
  induction' m with m ih
  · rfl
  · dsimp [iota_seq]
    rw [← AlgHom.comp_assoc]
    have hcomm : (psi (n + (m + 1))).comp (iota (n + m)) = psi (n + m) :=
      psi_comm (n + m)
    rw [hcomm]
    exact ih

/-- A family of staged KMS states compatible across algebra inclusions. -/
structure StagedKMSFamily (omega : ∀ n, A n →ₗ[ℂ] ℂ) : Prop where
  normalized : ∀ n, omega n 1 = 1
  compatible : ∀ n, (omega (n + 1)).comp (iota n).toLinearMap = omega n

/-- Multi-step compatibility: ω_{n+m} ∘ ι_{n, m} = ω_n. -/
theorem staged_state_m_step_compatibility
    {omega : ∀ n, A n →ₗ[ℂ] ℂ} (h_kms : StagedKMSFamily iota omega) (n m : ℕ) :
    (omega (n + m)).comp (iota_seq iota n m).toLinearMap = omega n := by
  induction' m with m ih
  · rfl
  · dsimp [iota_seq]
    rw [← LinearMap.comp_assoc]
    have h_one_step : (omega (n + (m + 1))).comp (iota (n + m)).toLinearMap = omega (n + m) :=
      h_kms.compatible (n + m)
    rw [h_one_step]
    exact ih

/-- Structure of a KMS state on the colimit algebra A_inf descending to the staged family. -/
structure ColimitKMSState
    (psi : ∀ n, A n →ₐ[ℂ] A_inf)
    (Omega : A_inf →ₗ[ℂ] ℂ)
    (omega : ∀ n, A n →ₗ[ℂ] ℂ) : Prop where
  normalized : Omega 1 = 1
  descent : ∀ n, Omega.comp (psi n).toLinearMap = omega n

/-- 
  MASTER THEOREM 1 (Colimit State Equivalence of Local Representatives):
  If two local elements x ∈ A_n and y ∈ A_m map to the same element in the colimit A_inf,
  their staged expectation values are identically equal: ω_n(x) = ω_m(y).
-/
theorem colimit_state_rep_equality
    (psi : ∀ n, A n →ₐ[ℂ] A_inf)
    {Omega : A_inf →ₗ[ℂ] ℂ} {omega : ∀ n, A n →ₗ[ℂ] ℂ}
    (h_colimit : ColimitKMSState psi Omega omega)
    (n m : ℕ) (x : A n) (y : A m)
    (h_colimit_eq : psi n x = psi m y) :
    omega n x = omega m y := by
  have h_n : Omega (psi n x) = omega n x := by
    have h := h_colimit.descent n
    exact congr_arg (fun (f : A n →ₗ[ℂ] ℂ) => f x) h
  have h_m : Omega (psi m y) = omega m y := by
    have h := h_colimit.descent m
    exact congr_arg (fun (f : A m →ₗ[ℂ] ℂ) => f y) h
  rw [← h_n, ← h_m, h_colimit_eq]

/--
Colimit Transport of a Supplied Stage-n Bilinear State Equality:
Given `ColimitKMSState psi Omega omega` and a supplied hypothesis
`h_kms_stage : omega n (a * b_thermal) = omega n (b_shift * a)` at stage `n`,
transports the equality along `psi n` to
  `Omega (psi n a * psi n b_thermal) = Omega (psi n b_shift * psi n a)`.
-/
theorem colimit_kms_thermal_condition
    (psi : ∀ n, A n →ₐ[ℂ] A_inf)
    {Omega : A_inf →ₗ[ℂ] ℂ} {omega : ∀ n, A n →ₗ[ℂ] ℂ}
    (h_colimit : ColimitKMSState psi Omega omega)
    (n : ℕ) (a b_thermal b_shift : A n)
    (h_kms_stage : omega n (a * b_thermal) = omega n (b_shift * a)) :
    Omega (psi n a * psi n b_thermal) = Omega (psi n b_shift * psi n a) := by
  have h_mul_1 : psi n a * psi n b_thermal = psi n (a * b_thermal) := (map_mul (psi n) a b_thermal).symm
  have h_mul_2 : psi n b_shift * psi n a = psi n (b_shift * a) := (map_mul (psi n) b_shift a).symm
  rw [h_mul_1, h_mul_2]
  have h_desc := h_colimit.descent n
  have h1 : Omega (psi n (a * b_thermal)) = omega n (a * b_thermal) :=
    congr_arg (fun (f : A n →ₗ[ℂ] ℂ) => f (a * b_thermal)) h_desc
  have h2 : Omega (psi n (b_shift * a)) = omega n (b_shift * a) :=
    congr_arg (fun (f : A n →ₗ[ℂ] ℂ) => f (b_shift * a)) h_desc
  rw [h1, h2, h_kms_stage]

end InfoGeometry.Modular.Colimit

end noncomputable section
