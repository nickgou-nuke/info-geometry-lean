/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Set.Basic
import InfoGeometry.GrandUnification.MachianCosmology
import InfoGeometry.GrandUnification.Commutant

/-!
# Tomita–Takesaki Modular Conjugation and Bicommutant Inclusion

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Formalizes the bicommutant inclusion `A ⊆ Commutant (Commutant A)` and the
    commutation of observables in `M_alg` with elements of `Commutant M_alg`.
- BUCKET 2 (Explicit Endomorphism Carrier):
  * `ModularConjugation R M` carries the modular reflection operator `J_Δ : Module.End R M`
    and the local observable set `M_alg : Set (Module.End R M)`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `subset_bicommutant`: `A ⊆ Commutant (Commutant A)`.
  * `ego_commutes_with_anima`: every `x ∈ M_alg` commutes with every `y ∈ Commutant M_alg`.
  * `modular_conjugation_involutive`: `J_Δ * (J_Δ * x * J_Δ) * J_Δ = x` when `J_Δ * J_Δ = 1`.
-/

namespace InfoGeometry.GrandUnification.TomitaTakesakiRealization

open InfoGeometry.GrandUnification.MachianCosmology
open LinearMap

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The bicommutant `Commutant (Commutant A)` contains the original subset `A`. -/
lemma subset_bicommutant (A : Set (Module.End R M)) :
    A ⊆ Commutant (Commutant A) := by
  intro x hx y hy
  have h := hy x hx
  exact h.symm

/-- Carrier data for Tomita–Takesaki modular conjugation on `Module.End R M`. -/
class ModularConjugation (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] where
  /-- The modular conjugation operator `J_Δ`. -/
  J_Δ : Module.End R M
  /-- The local algebra of observables `M_alg`. -/
  M_alg : Set (Module.End R M)

/-- Canonical identity/empty model witnessing `Inhabited (ModularConjugation R M)`. -/
@[instance_reducible]
def trivialModularConjugation (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    ModularConjugation R M where
  J_Δ := 1
  M_alg := ∅

instance instInhabitedModularConjugation (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    Inhabited (ModularConjugation R M) :=
  ⟨trivialModularConjugation R M⟩

/-- Any observable `x ∈ M_alg` commutes with any observable `y ∈ Commutant M_alg`. -/
theorem ego_commutes_with_anima [ModularConjugation R M] :
    ∀ (x y : Module.End R M), x ∈ ModularConjugation.M_alg (R := R) (M := M) →
    y ∈ Commutant (ModularConjugation.M_alg (R := R) (M := M)) →
    x * y = y * x := by
  intro x y hx hy
  have hcomm := hy x hx
  exact Eq.trans hcomm (Eq.refl (y * x))

/-- Conjugating twice by an involutive modular operator `J_Δ` (`J_Δ * J_Δ = 1`)
    recovers the original endomorphism `x`. -/
theorem modular_conjugation_involutive [ModularConjugation R M]
    (hJ : (ModularConjugation.J_Δ (R := R) (M := M)) * ModularConjugation.J_Δ = 1)
    (x : Module.End R M) :
    (ModularConjugation.J_Δ (R := R) (M := M)) *
      (ModularConjugation.J_Δ * x * ModularConjugation.J_Δ) *
      ModularConjugation.J_Δ = x := by
  calc
    (ModularConjugation.J_Δ (R := R) (M := M)) *
        (ModularConjugation.J_Δ * x * ModularConjugation.J_Δ) *
        ModularConjugation.J_Δ
      = (ModularConjugation.J_Δ * ModularConjugation.J_Δ) * x *
          (ModularConjugation.J_Δ * ModularConjugation.J_Δ) := by noncomm_ring
    _ = 1 * x * 1 := by rw [hJ]
    _ = x := by noncomm_ring

end InfoGeometry.GrandUnification.TomitaTakesakiRealization
