import Mathlib.Tactic
import InfoGeometry.Canonical.ColimitRigidityProofChainBridge
import InfoGeometry.Canonical.CategoricalRiemannRigidity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Finite linear-map kernel readouts

This module provides a finite linear-map/kernel API:

1. A finite-stage operator and its square.

2. Injectivity preserves a nonzero vector in one successor stage.

3. A compatible linear map sends a finite-stage kernel vector to the
   downstream kernel.

No direct colimit, self-adjointness, or Fredholm-index construction is defined
by this file.
-/

namespace InfoGeometry.Canonical.FilteredColimitDiracIndexBridge

open InfoGeometry.Canonical.ColimitRigidityProofChainBridge
open InfoGeometry.Canonical.CategoricalRiemannRigidity

/-- Finite-stage Dirac operator data structure on a real vector space. -/
abbrev FiniteDiracData (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  V →ₗ[ℝ] V

namespace FiniteDiracData

abbrev diracOp
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : FiniteDiracData V) : V →ₗ[ℝ] V :=
  data

end FiniteDiracData

namespace FiniteDiracData

/-- The finite-stage square is derived from the canonical Dirac operator. -/
abbrev diracSquare
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : FiniteDiracData V) : V →ₗ[ℝ] V :=
  data.diracOp.comp data.diracOp

@[simp] theorem diracSquare_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : FiniteDiracData V) :
    data.diracSquare = data.diracOp.comp data.diracOp :=
  rfl

end FiniteDiracData

/-- Applying the stored Dirac square is the same as applying the Dirac operator twice. -/
@[simp] theorem diracSquare_apply
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : FiniteDiracData V) (v : V) :
    data.diracSquare v = data.diracOp (data.diracOp v) := by
  rw [data.diracSquare_eq]
  rfl

/-- Kernel subspace of a finite-stage Dirac operator. -/
def diracKernel {V : Type*} [AddCommGroup V] [Module ℝ V] (data : FiniteDiracData V) : Submodule ℝ V :=
  LinearMap.ker data.diracOp

/--
**Finite kernel membership.**
Membership in the stored kernel is equivalent to vanishing of the operator.
-/
theorem mem_diracKernel_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : FiniteDiracData V) (v : V) :
    v ∈ diracKernel data ↔ data.diracOp v = 0 :=
  LinearMap.mem_ker

/--
**Successor-stage injectivity.**
An injective successor map sends a nonzero vector to a nonzero vector; the
kernel premise is retained as finite stage data.
$$v \in \ker(D_n) \land v \neq 0 \implies \phi_n(v) \neq 0.$$
-/
theorem dirac_kernel_stage_injectivity_survival
    {V : ℕ → Type*} [∀ n, AddCommGroup (V n)] [∀ n, Module ℝ (V n)]
    (f : ∀ n, V n →ₗ[ℝ] V (n + 1)) (h_inj : ∀ n, Function.Injective (f n))
    {n : ℕ} (data : FiniteDiracData (V n)) (v : V n)
    (h_ker : v ∈ diracKernel data) (h_ne : v ≠ 0) :
    f n v ≠ 0 :=
  tower_stage_injectivity_survival f h_inj v h_ne

/--
**Compatible finite kernel preservation.**
A commuting linear map sends a kernel vector to the target kernel.
-/
theorem colimit_kernel_step_preservation
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (DV : FiniteDiracData V) (DW : FiniteDiracData W)
    (f : V →ₗ[ℝ] W) (h_comm : DW.diracOp.comp f = f.comp DV.diracOp)
    (v : V) (hv : v ∈ diracKernel DV) :
    f v ∈ diracKernel DW := by
  rw [mem_diracKernel_iff] at hv ⊢
  have h : (DW.diracOp.comp f) v = (f.comp DV.diracOp) v := by rw [h_comm]
  simp only [LinearMap.comp_apply] at h ⊢
  rw [hv, map_zero] at h
  exact h

end InfoGeometry.Canonical.FilteredColimitDiracIndexBridge
