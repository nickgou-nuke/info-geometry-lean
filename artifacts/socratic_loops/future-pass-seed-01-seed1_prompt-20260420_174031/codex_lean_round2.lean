import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Real.Basic

/-!
# Logos-Pyre Hypothesis Surface

A conservative formal scaffold for the idea that an informational system
has a zero-production memory part and a positive-production dissipative part.
-/

structure EntropyProduction (I V : Type*) where
  sigma : I → V → ℝ
  nonneg : ∀ i v, 0 ≤ sigma i v

namespace EntropyProduction

variable {I V : Type*}

def memoryKernel (σ : EntropyProduction I V) (i : I) : Set V :=
  {v | σ.sigma i v = 0}

def dissipativeCone (σ : EntropyProduction I V) (i : I) : Set V :=
  {v | 0 < σ.sigma i v}

theorem logos_pyre_partition
    (σ : EntropyProduction I V) (i : I) (v : V) :
    v ∈ σ.memoryKernel i ∨ v ∈ σ.dissipativeCone i := by
  unfold memoryKernel dissipativeCone
  rcases eq_or_lt_of_le (σ.nonneg i v) with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

theorem not_memory_iff_dissipative
    (σ : EntropyProduction I V) (i : I) (v : V) :
    v ∉ σ.memoryKernel i ↔ v ∈ σ.dissipativeCone i := by
  unfold memoryKernel dissipativeCone
  constructor
  · intro h
    rcases eq_or_lt_of_le (σ.nonneg i v) with hz | hp
    · exact False.elim (h hz.symm)
    · exact hp
  · intro hp hz
    exact (not_lt_of_ge (le_of_eq hz)) hp

end EntropyProduction

structure LogosPyreSystem (R I V : Type*)
    [Semiring R] [AddCommMonoid V] [Module R V] where
  production : EntropyProduction I V
  memory : I → Submodule R V
  memory_eq_kernel :
    ∀ i, (memory i : Set V) = production.memoryKernel i

namespace LogosPyreSystem

variable {R I V : Type*}
variable [Semiring R] [AddCommMonoid V] [Module R V]

theorem memory_zero
    (S : LogosPyreSystem R I V) (i : I) :
    (0 : V) ∈ S.production.memoryKernel i := by
  rw [← S.memory_eq_kernel i]
  exact (S.memory i).zero_mem

theorem memory_closed_add
    (S : LogosPyreSystem R I V) (i : I)
    {v w : V}
    (hv : v ∈ S.production.memoryKernel i)
    (hw : w ∈ S.production.memoryKernel i) :
    v + w ∈ S.production.memoryKernel i := by
  rw [← S.memory_eq_kernel i] at hv hw ⊢
  exact (S.memory i).add_mem hv hw

theorem memory_closed_smul
    (S : LogosPyreSystem R I V) (i : I)
    (a : R) {v : V}
    (hv : v ∈ S.production.memoryKernel i) :
    a • v ∈ S.production.memoryKernel i := by
  rw [← S.memory_eq_kernel i] at hv ⊢
  exact (S.memory i).smul_mem a hv

end LogosPyreSystem