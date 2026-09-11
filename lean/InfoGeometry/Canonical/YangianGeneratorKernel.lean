import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

variable {K : Type*} [CommRing K]
variable {A : Type*} [AddCommGroup A] [Module K A]

/-- 
Defines what it means for an object Ω to be invariant under a linear generator Y.
This establishes the purely linear kernel condition.
-/
def IsGeneratorInvariant (Y : A →ₗ[K] A) (Ω : A) : Prop :=
  Y Ω = 0

/-- The kernel of a generator is closed under addition. -/
theorem invariant_add {Y : A →ₗ[K] A} {Ω Ψ : A}
    (hΩ : IsGeneratorInvariant Y Ω)
    (hΨ : IsGeneratorInvariant Y Ψ) :
    IsGeneratorInvariant Y (Ω + Ψ) := by
  dsimp [IsGeneratorInvariant] at *
  rw [LinearMap.map_add, hΩ, hΨ, add_zero]

/-- The kernel of a generator is closed under scalar multiplication. -/
theorem invariant_smul {Y : A →ₗ[K] A} {Ω : A} (c : K)
    (hΩ : IsGeneratorInvariant Y Ω) :
    IsGeneratorInvariant Y (c • Ω) := by
  dsimp [IsGeneratorInvariant] at *
  rw [LinearMap.map_smul, hΩ, smul_zero]

/-- The linear kernel is closed under the two basic module operations. -/
theorem master_yangian_generator_kernel_synthesis
    (Y : A →ₗ[K] A) {Ω Ψ : A} (c : K)
    (hΩ : IsGeneratorInvariant Y Ω)
    (hΨ : IsGeneratorInvariant Y Ψ) :
    IsGeneratorInvariant Y (Ω + Ψ) ∧
      IsGeneratorInvariant Y (c • Ω) :=
  ⟨invariant_add hΩ hΨ, invariant_smul c hΩ⟩

end InfoGeometry.Canonical
