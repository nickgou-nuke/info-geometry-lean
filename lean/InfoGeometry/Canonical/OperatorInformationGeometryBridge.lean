import InfoGeometry.Dynamics.ModularThermalState
import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
import InfoGeometry.Meta.Architecture

/-!
# Native operator-information geometry interfaces

This file exposes the laws connecting modular flow, noncommutative relative
entropy, conditional expectation, and invariant sectors directly on their
owning functions.  It contains no carrier records and no reflexive readback
theorems.
-/

namespace InfoGeometry.Canonical.OperatorInformationGeometryBridge

open scoped ComplexOrder

/-- A one-parameter action on an operator algebra. -/
abbrev OperatorFlow (Alg : Type*) :=
  ℝ → Alg → Alg

/-- Group law for a one-parameter operator flow. -/
def IsOperatorFlow {Alg : Type*} (σ : OperatorFlow Alg) : Prop :=
  (∀ A, σ 0 A = A) ∧
    ∀ s t A, σ (s + t) A = σ s (σ t A)

/-- A conditional-expectation candidate is idempotent when applying it twice
does not change the result. -/
def IsIdempotentExpectation {Alg : Type*} (E : Alg → Alg) : Prop :=
  ∀ A, E (E A) = E A

/-- Compatibility of a conditional expectation with modular time. -/
def IsModularEquivariant
    {Alg : Type*}
    (σ : OperatorFlow Alg)
    (E : Alg → Alg) : Prop :=
  ∀ t A, E (σ t A) = σ t (E A)

/-- The invariant sector of an expectation map. -/
def ExpectationFixedPoint
    {Alg : Type*}
    (E : Alg → Alg)
    (A : Alg) : Prop :=
  E A = A

/-- Every value in the range of an idempotent expectation is fixed. -/
theorem expectation_fixedPoint_of_mem_range
    {Alg : Type*}
    {E : Alg → Alg}
    (hE : IsIdempotentExpectation E)
    (A : Alg) :
    ExpectationFixedPoint E (E A) :=
  hE A

/-- A modular-equivariant expectation carries a fixed observable to a fixed
observable along the modular flow. -/
theorem expectationFixedPoint_modularFlow
    {Alg : Type*}
    {σ : OperatorFlow Alg}
    {E : Alg → Alg}
    (hEquivariant : IsModularEquivariant σ E)
    {A : Alg}
    (hA : ExpectationFixedPoint E A)
    (t : ℝ) :
    ExpectationFixedPoint E (σ t A) := by
  rw [ExpectationFixedPoint, hEquivariant, hA]

/-- Modular evolution preserves the range of a modular-equivariant
expectation. -/
theorem modularFlow_mem_range_of_mem_range
    {Alg : Type*}
    {σ : OperatorFlow Alg}
    {E : Alg → Alg}
    (hEquivariant : IsModularEquivariant σ E)
    {A : Alg}
    (hA : A ∈ Set.range E)
    (t : ℝ) :
    σ t A ∈ Set.range E := by
  obtain ⟨B, rfl⟩ := hA
  exact ⟨σ t B, hEquivariant t B⟩

section NoncommutativeRelativeEntropy

variable {A : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Native noncommutative relative log-density operator. -/
noncomputable abbrev relativeLogDensity (ρ σ : A) : A :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.relativeLogDensity ρ σ

/-- Native Umegaki operator kernel, before any scalar readout. -/
noncomputable abbrev umegakiKernel (ρ σ : A) : A :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiKernel ρ σ

/-- Umegaki readout through a genuine Mathlib positive functional. -/
noncomputable abbrev umegakiRelativeEntropy
    (τ : A →ₚ[ℂ] ℂ)
    (ρ σ : A) : ℂ :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy
    τ ρ σ

@[simp]
theorem relativeLogDensity_self (ρ : A) :
    relativeLogDensity ρ ρ = 0 :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.relativeLogDensity_self ρ

@[simp]
theorem umegakiKernel_self (ρ : A) :
    umegakiKernel ρ ρ = 0 :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiKernel_self ρ

@[simp]
theorem umegakiRelativeEntropy_self
    (τ : A →ₚ[ℂ] ℂ)
    (ρ : A) :
    umegakiRelativeEntropy τ ρ ρ = 0 :=
  InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiRelativeEntropy_self
    τ ρ

end NoncommutativeRelativeEntropy

end InfoGeometry.Canonical.OperatorInformationGeometryBridge
