/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import InfoGeometry.GrandUnification.Commutant

/-!
# Modular Conjugation Reflection Laws over the Shared Commutant

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Formalizes conjugation by an involutive modular reflection operator
    `J_Δ : Module.End R M` (`J_Δ * J_Δ = 1`) relative to
    `InfoGeometry.GrandUnification.Commutant`.
- BUCKET 2 (Explicit Endomorphism Carrier):
  * `modularReflect J_Δ x = J_Δ * x * J_Δ` acts on `Module.End R M`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `modularReflect_involutive`: `modularReflect J_Δ (modularReflect J_Δ x) = x`
    when `J_Δ * J_Δ = 1`.
  * `modularReflect_mul`: `modularReflect J_Δ (x * y) = modularReflect J_Δ x * modularReflect J_Δ y`
    when `J_Δ * J_Δ = 1`.
  * `ego_commutes_with_modularReflect`: any `a ∈ M_alg` commutes with `modularReflect J_Δ x`
    whenever `modularReflect J_Δ x ∈ Commutant M_alg`.
-/

namespace InfoGeometry.GrandUnification

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Conjugation of an endomorphism `x` by the modular reflection operator `J_Δ`:
    `J_Δ * x * J_Δ`. -/
def modularReflect (J_Δ x : Module.End R M) : Module.End R M :=
  J_Δ * x * J_Δ

/-- Double modular reflection recovers the original operator when `J_Δ * J_Δ = 1`. -/
theorem modularReflect_involutive (J_Δ x : Module.End R M) (hJ : J_Δ * J_Δ = 1) :
    modularReflect J_Δ (modularReflect J_Δ x) = x := by
  unfold modularReflect
  calc
    J_Δ * (J_Δ * x * J_Δ) * J_Δ
      = (J_Δ * J_Δ) * x * (J_Δ * J_Δ) := by noncomm_ring
    _ = 1 * x * 1 := by rw [hJ]
    _ = x := by noncomm_ring

/-- Modular reflection is multiplicative on endomorphisms when `J_Δ * J_Δ = 1`. -/
theorem modularReflect_mul (J_Δ x y : Module.End R M) (hJ : J_Δ * J_Δ = 1) :
    modularReflect J_Δ (x * y) = modularReflect J_Δ x * modularReflect J_Δ y := by
  unfold modularReflect
  calc
    J_Δ * (x * y) * J_Δ
      = J_Δ * x * 1 * y * J_Δ := by noncomm_ring
    _ = J_Δ * x * (J_Δ * J_Δ) * y * J_Δ := by rw [← hJ]
    _ = (J_Δ * x * J_Δ) * (J_Δ * y * J_Δ) := by noncomm_ring

/-- Every observable `a ∈ M_alg` commutes with a modular-reflected operator
    `modularReflect J_Δ x` lying in `Commutant M_alg`. -/
theorem ego_commutes_with_modularReflect (J_Δ x a : Module.End R M)
    (M_alg : Set (Module.End R M)) (ha : a ∈ M_alg)
    (hrefl : modularReflect J_Δ x ∈ InfoGeometry.GrandUnification.Commutant M_alg) :
    a * modularReflect J_Δ x = modularReflect J_Δ x * a := by
  have hcomm := hrefl a ha
  exact Eq.trans hcomm (Eq.refl (modularReflect J_Δ x * a))

end InfoGeometry.GrandUnification
