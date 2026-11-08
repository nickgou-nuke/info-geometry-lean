import InfoGeometry.Canonical.BoundaryBraidRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge

/-!
# The boundary--Fibonacci intertwiner Hom-space

This owner records the exact finite linear system for a map from the native
eight-dimensional boundary carrier to the native Fibonacci horizon carrier.
It deliberately proves neither existence nor nonexistence of a nonzero
intertwiner: those are consequences of the kernel computed from the two
generator defects below, not assumed structure fields.
-/

namespace InfoGeometry.Twistor.BoundaryFibonacciHorizonIntertwiner

noncomputable section

open InfoGeometry.Canonical.BoundaryBraidRepresentation
open InfoGeometry.Physics.Algebra.FibonacciHorizonBraidBridge
open InfoGeometry.Physics.B3PresentedGroup

local notation "IntertwinerCarrier" =>
  BoundaryBraidState →ₗ[ℂ] horizonZeroMode

local notation "BoundaryGenerator" =>
  BoundaryBraidState →ₗ[ℂ] BoundaryBraidState

def boundaryGenerator (g : BoundaryBraidGroup) : BoundaryGenerator :=
  (boundaryBraidLinearRepresentation g : BoundaryGenerator)

def intertwinerDefect0 (Φ : IntertwinerCarrier) : IntertwinerCarrier :=
  Φ.comp (boundaryGenerator (PresentedGroup.of B3Gen.sig0)) -
    horizonRestrictedR.comp Φ

def intertwinerDefect1 (Φ : IntertwinerCarrier) : IntertwinerCarrier :=
  Φ.comp (boundaryGenerator (PresentedGroup.of B3Gen.sig1)) -
    horizonRestrictedB.comp Φ

/-- The simultaneous two-generator defect map. -/
def boundaryFibonacciIntertwinerOperator :
    IntertwinerCarrier →ₗ[ℂ] IntertwinerCarrier × IntertwinerCarrier where
  toFun Φ := (intertwinerDefect0 Φ, intertwinerDefect1 Φ)
  map_add' Φ Ψ := by
    apply Prod.ext <;> ext v <;>
      simp [intertwinerDefect0, intertwinerDefect1] <;> abel
  map_smul' c Φ := by
    apply Prod.ext <;> ext v <;>
      simp [intertwinerDefect0, intertwinerDefect1] <;> ring

/-- The exact space of maps intertwining both braid generators. -/
def boundaryFibonacciIntertwinerSpace : Submodule ℂ IntertwinerCarrier :=
  LinearMap.ker boundaryFibonacciIntertwinerOperator

theorem mem_boundaryFibonacciIntertwinerSpace_iff (Φ : IntertwinerCarrier) :
    Φ ∈ boundaryFibonacciIntertwinerSpace ↔
      intertwinerDefect0 Φ = 0 ∧ intertwinerDefect1 Φ = 0 := by
  change boundaryFibonacciIntertwinerOperator Φ = 0 ↔ _
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h0, h1⟩
    exact Prod.ext h0 h1

theorem mem_boundaryFibonacciIntertwinerSpace_iff_generator_equations
    (Φ : IntertwinerCarrier) :
    Φ ∈ boundaryFibonacciIntertwinerSpace ↔
      Φ.comp (boundaryGenerator (PresentedGroup.of B3Gen.sig0)) =
          horizonRestrictedR.comp Φ ∧
      Φ.comp (boundaryGenerator (PresentedGroup.of B3Gen.sig1)) =
          horizonRestrictedB.comp Φ := by
  rw [mem_boundaryFibonacciIntertwinerSpace_iff]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨sub_eq_zero.mpr h0, sub_eq_zero.mpr h1⟩

/-! ## Kernel consequences

The following results deliberately expose the exact hypothesis needed for a
zero-space conclusion.  The simultaneous defect map is the canonical owner;
injectivity of one component is supplied only by a concrete representation
proof, never smuggled into the definition of the Hom-space.
-/

theorem boundaryFibonacciIntertwinerSpace_eq_bot_of_injective_defect0
    (hInjective : Function.Injective intertwinerDefect0) :
    boundaryFibonacciIntertwinerSpace = ⊥ := by
  apply le_antisymm
  · intro Φ hΦ
    have hKernel : boundaryFibonacciIntertwinerOperator Φ = 0 := hΦ
    have hDefect : intertwinerDefect0 Φ = 0 :=
      congrArg Prod.fst hKernel
    have hZero : Φ = 0 := by
      apply hInjective
      calc
        intertwinerDefect0 Φ = 0 := hDefect
        _ = intertwinerDefect0 0 := by
          simp [intertwinerDefect0]
          abel
    simpa [hZero]
  · exact bot_le

theorem boundaryFibonacciIntertwinerSpace_finrank_zero_of_injective_defect0
    (hInjective : Function.Injective intertwinerDefect0) :
    Module.finrank ℂ boundaryFibonacciIntertwinerSpace = 0 := by
  rw [boundaryFibonacciIntertwinerSpace_eq_bot_of_injective_defect0 hInjective]
  simp

end

end InfoGeometry.Twistor.BoundaryFibonacciHorizonIntertwiner
