import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Dirac Berry-Keating Fredholm Bridge

This module contains finite linear-algebra statements and a conditional
zero-set readout. It does not construct a Fredholm operator or prove RH.

1. **Finite Stage Dirac Operator $D_n$**:
   Sum of two supplied operator families. No adjoint or Cuntz relations are
   imposed on the family named `S_star`.

2. **Zero-Mode Predicate**:
   Defines non-trivial kernel objects $\operatorname{HasZeroMode}(D) := \exists v \neq 0, D(v) = 0$.

3. **Kernel Protection Survival Theorem (Твърдост на Ядрото)**:
   Proves natively that if a non-zero state $v \in \ker(D_n) \setminus \{0\}$ exists at finite stage $n$, and the transition map $\psi_n$ is injective ($\ker(\psi_n) = \bot$) and commutes with the boundary operator ($D_{\text{boundary}} \circ \psi_n = \psi_n \circ D_n$), then $\psi_n(v)$ is a non-zero zero-mode of $D_{\text{boundary}}$, proving $\operatorname{HasZeroMode}(D_{\text{boundary}})$.

4. **RH Spectral Duality Predicate**:
   Assumes an equivalence between zeros of a supplied function and zero-modes:
   $$\zeta(s) = 0 \iff \operatorname{HasZeroMode}(D_s(s)).$$

5. **Conditional kernel vanishing**:
   Under that assumed equivalence, a nonzero function value implies trivial
   kernel. No cokernel or Fredholm index is computed.
-/

namespace InfoGeometry.Canonical.DiracBerryKeatingFredholmBridge

open scoped BigOperators

/-- 1. Finite Stage Dirac Operator $D_n$ mapped to Majorana sums. -/
def StageDiracOperator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (n : ℕ) (S S_star : ℕ → (V →ₗ[ℂ] V)) : V →ₗ[ℂ] V :=
  ∑ i ∈ Finset.range n, (S i + S_star i)

/-- Existence of a nonzero kernel vector; this does not determine an index. -/
def HasZeroMode {V : Type*} [AddCommGroup V] [Module ℂ V] (D : V →ₗ[ℂ] V) : Prop :=
  ∃ v : V, v ≠ 0 ∧ D v = 0

/-- The zero-mode predicate is exactly nontriviality of the native kernel. -/
theorem hasZeroMode_iff_ker_ne_bot {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) : HasZeroMode D ↔ LinearMap.ker D ≠ ⊥ := by
  constructor
  · rintro ⟨v, hv, hD⟩ hk
    have hm : v ∈ LinearMap.ker D := hD
    rw [hk, Submodule.mem_bot] at hm
    exact hv hm
  · intro hk
    by_contra hn
    apply hk
    apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    by_contra hne
    exact hn ⟨v, hne, hv⟩

/-- Absence of zero modes means injectivity, not index zero. -/
theorem not_hasZeroMode_iff_injective {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) : ¬ HasZeroMode D ↔ Function.Injective D := by
  rw [hasZeroMode_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]

/--
**Main Theorem 1: Kernel Protection Survival Theorem (Твърдост на Ядрото)**
If a state $v$ is a zero-mode at finite stage $n$, and the transition map $\psi_n$ is injective,
the topological defect survives strictly in the boundary colimit.
-/
theorem kernel_protection_survival
    {V V_colimit : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V_colimit] [Module ℂ V_colimit]
    (D_n : V →ₗ[ℂ] V) (D_boundary : V_colimit →ₗ[ℂ] V_colimit)
    (ψ_n : V →ₗ[ℂ] V_colimit)
    (h_injective : LinearMap.ker ψ_n = ⊥)
    (h_commute : D_boundary.comp ψ_n = ψ_n.comp D_n)
    (v : V) (h_v_not_zero : v ≠ 0) (h_v_in_ker : D_n v = 0) :
    HasZeroMode D_boundary := by
  use ψ_n v
  constructor
  · intro h_eq_zero
    have h_mem_ker : v ∈ LinearMap.ker ψ_n := LinearMap.mem_ker.mpr h_eq_zero
    rw [h_injective, Submodule.mem_bot] at h_mem_ker
    exact h_v_not_zero h_mem_ker
  · calc
      D_boundary (ψ_n v) = (D_boundary.comp ψ_n) v := rfl
      _ = (ψ_n.comp D_n) v := by rw [h_commute]
      _ = ψ_n (D_n v) := rfl
      _ = ψ_n 0 := by rw [h_v_in_ker]
      _ = 0 := LinearMap.map_zero ψ_n

/-- 4. RH Spectral Duality (Спектрално Тъждество за РХ): Zeta Zeros $\iff$ Zero-Modes of the Boundary Dirac Operator. -/
def RHSpectralDuality {V_colimit : Type*} [AddCommGroup V_colimit] [Module ℂ V_colimit]
    (riemannZeta : ℂ → ℂ) (D_s : ℂ → (V_colimit →ₗ[ℂ] V_colimit)) : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 ↔ HasZeroMode (D_s s)

/--
Conditional absence of zero modes. The historical declaration name mentions
an index, but its conclusion is only kernel vanishing under `h_duality`.
-/
theorem zero_free_region_trivial_index
    {V_colimit : Type*} [AddCommGroup V_colimit] [Module ℂ V_colimit]
    (riemannZeta : ℂ → ℂ) (D_s : ℂ → (V_colimit →ₗ[ℂ] V_colimit))
    (h_duality : RHSpectralDuality riemannZeta D_s) (s : ℂ) (h_zeta_neq_zero : riemannZeta s ≠ 0) :
    ¬ HasZeroMode (D_s s) := by
  intro h_has_zero
  have h_zeta_zero : riemannZeta s = 0 := (h_duality s).mpr h_has_zero
  exact h_zeta_neq_zero h_zeta_zero

end InfoGeometry.Canonical.DiracBerryKeatingFredholmBridge
