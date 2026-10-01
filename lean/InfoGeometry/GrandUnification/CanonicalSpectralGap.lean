import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace InfoGeometry.GrandUnification.CanonicalSpectralGap
open LinearMap
open Module

/-!
# Canonical Mathematical Extraction: Spectral Gaps and Kernels
-/

section ArchetypePoset

inductive MathArchetype
  | endomorphism
  | kernelSubspace
  | trivialKernel
  | spectralGap
  | automorphism
  deriving DecidableEq, Repr

def rank : MathArchetype → Nat
  | .endomorphism => 1
  | .kernelSubspace => 2
  | .trivialKernel => 3
  | .spectralGap => 4
  | .automorphism => 5

def causallyPrecedes (a b : MathArchetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : MathArchetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : MathArchetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := Nat.le_trans

theorem causal_antisymm {a b : MathArchetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

end ArchetypePoset

section SpectralTheory

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
variable [FiniteDimensional R M]

/-- The "Defect Block" mathematically maps to the Kernel of the Endomorphism. -/
def kernelSubspace (K : Module.End R M) : Subspace R M := LinearMap.ker K

/-- The algebraic dimension of the kernel subspace. -/
noncomputable def kernelDimension (K : Module.End R M) : ℕ := Module.finrank R (LinearMap.ker K)

/-- 
The condition of "Confinement" mathematically translates to the 
triviality of the kernel (i.e., its dimension is zero).
-/
def TrivialKernelProp (K : Module.End R M) : Prop := kernelDimension K = 0

/-- 
If the kernel dimension is 0, the linear map is injective.
-/
theorem injective_of_trivial_kernel (K : Module.End R M) (h : TrivialKernelProp K) : 
    Function.Injective K := by
  dsimp [TrivialKernelProp, kernelDimension] at h
  rw [Submodule.finrank_eq_zero] at h
  exact LinearMap.ker_eq_bot.mp h

end SpectralTheory

end InfoGeometry.GrandUnification.CanonicalSpectralGap
