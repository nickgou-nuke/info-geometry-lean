-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Basic

/-!
# Simple Modular Conjugation

A minimal definition of the `ModularConjugation` class used by the
`SpacetimeGlide` module. It avoids importing the full `TomitaTakesakiRealization`
file, which currently depends on `MachianCosmology` and does not compile.
-/

namespace InfoGeometry.GrandUnification

class ModularConjugation (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  /-- The modular conjugation operator `J_Δ` (Krein symmetry). -/
  J_Δ : Module.End R M
  /-- Involution property `J_Δ * J_Δ = 1`. -/
  involution : J_Δ * J_Δ = 1
  /-- Local algebra of observables. -/
  M_alg : Set (Module.End R M)
  /-- Modular reflection theorem: `y ∈ Commutant M_alg ↔ ∃ x ∈ M_alg, y = J_Δ * x * J_Δ`. -/
  modular_reflection : ∀ y, y ∈ InfoGeometry.GrandUnification.Commutant M_alg ↔ ∃ x ∈ M_alg, y = J_Δ * x * J_Δ

end InfoGeometry.GrandUnification
