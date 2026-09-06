import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Routing.BirkhoffVonNeumann

set_option linter.unusedSectionVars false

/-!
# Bogoliubov–Sinkhorn Routing Bridge

This file establishes the typed bridge between:

- **Sinkhorn/bistochastic coupling** (global token-to-expert occupation balancing)
- **Arnold–Majorana expert dynamics** (expert-local paired-mode transformations)

## Architecture

The bridge is layered:

1. **Generic balanced mixture**: given arbitrary coefficients `P : Tok → ExpertIdx n → ℝ`
   and expert outputs, form `h_out(i) = ∑_e P(i,e) • expertOutput(e,i)`.
   Submodule preservation follows from linearity alone — no stochasticity needed.

2. **Arnold–Majorana specialization**: connect the generic mixture to the existing
   `ArnoldMajoranaNetwork` expert family.

3. **Sinkhorn coefficient bridge**: connect bistochastic `switchMatrix` coefficients
   (from `SinkhornFoundation`) to the generic mixture.

4. **Birkhoff permutation readback**: under bistochastic assumptions, decompose the
   balanced mixture as a convex combination of permutation-routed outputs.

## Critical epistemic boundary

This file does **not** claim:

- That the Sinkhorn-balanced Arnold mixture preserves any Clifford structure.
- That a convex combination of Bogoliubov transformations is itself Bogoliubov.
- That `Cl(5,5)` is preserved by the effective operator.

The only invariant proved is **state-level submodule preservation**:
if every expert maps a submodule `U` to itself, then any linear mixture of
expert outputs on inputs from `U` stays in `U`.

This is the correct mathematical distinction between:
- (A) state-level invariant: each transformed state lies in `U` → mixture remains in `U`
- (B) operator-level group property: each `B_e ∈ G` does NOT imply `∑ pₑ Bₑ ∈ G`
-/

open scoped BigOperators

namespace InfoGeometry.LLM.BogoliubovSinkhornRouting

open InfoGeometry.Canonical.MoE

/-! ## Section 1: Generic Balanced Expert Mixture -/

section GenericMixture

variable {Tok V : Type*} [Fintype Tok]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : Nat}

/--
Generic balanced expert mixture:
`h_out(i) = ∑_e P(i,e) • expertOutput(e,i)`

This is parametric in the coupling `P` and makes no assumptions about
stochasticity, nonnegativity, or normalization.
-/
noncomputable def balancedExpertMixture
    (P : Tok → ExpertIdx n → ℝ)
    (expertOutput : ExpertIdx n → Tok → V)
    (i : Tok) : V :=
  ∑ e, P i e • expertOutput e i

/-- The mixture depends only on the expert outputs at the queried token. -/
theorem balancedExpertMixture_congr
    (P : Tok → ExpertIdx n → ℝ)
    (expertOutput expertOutput' : ExpertIdx n → Tok → V)
    (i : Tok)
    (h : ∀ e, expertOutput e i = expertOutput' e i) :
    balancedExpertMixture P expertOutput i =
      balancedExpertMixture P expertOutput' i := by
  simp only [balancedExpertMixture]
  apply Finset.sum_congr rfl
  intro e he
  rw [h e]

/-- The mixture distributes over pointwise addition of expert outputs. -/
theorem balancedExpertMixture_add
    (P : Tok → ExpertIdx n → ℝ)
    (expertOutput expertOutput' : ExpertIdx n → Tok → V)
    (i : Tok) :
    balancedExpertMixture P (fun e j => expertOutput e j + expertOutput' e j) i =
      balancedExpertMixture P expertOutput i +
        balancedExpertMixture P expertOutput' i := by
  simp only [balancedExpertMixture, smul_add, Finset.sum_add_distrib]

/-- The mixture is homogeneous under a common scalar on expert outputs. -/
theorem balancedExpertMixture_smul
    (P : Tok → ExpertIdx n → ℝ)
    (r : ℝ)
    (expertOutput : ExpertIdx n → Tok → V)
    (i : Tok) :
    balancedExpertMixture P (fun e j => r • expertOutput e j) i =
      r • balancedExpertMixture P expertOutput i := by
  simp only [balancedExpertMixture, smul_smul, Finset.smul_sum]
  congr 1
  funext e
  rw [mul_comm]

/--
**Submodule preservation for balanced expert mixtures.**

If every expert output lies in a submodule `U`, then the balanced mixture
lies in `U` — regardless of the coupling coefficients `P`.

This is mathematically stronger than requiring `P` to be stochastic or
nonneg: submodule closure under finite linear combinations is unconditional.
-/
theorem balancedExpertMixture_mem_submodule
    (P : Tok → ExpertIdx n → ℝ)
    (U : Submodule ℝ V)
    (expertOutput : ExpertIdx n → Tok → V)
    (hU : ∀ e i, expertOutput e i ∈ U)
    (i : Tok) :
    balancedExpertMixture P expertOutput i ∈ U := by
  apply Submodule.sum_mem
  intro e _
  apply Submodule.smul_mem
  exact hU e i

/--
If expert outputs depend on token input: `expertOutput e i = f_e (x i)`,
and every `f_e` maps `U` into `U`, and `x i ∈ U`, then the mixture is in `U`.
-/
theorem balancedExpertMixture_mem_submodule_of_input
    (P : Tok → ExpertIdx n → ℝ)
    (U : Submodule ℝ V)
    (f : ExpertIdx n → V → V)
    (x : Tok → V)
    (hf : ∀ e v, v ∈ U → f e v ∈ U)
    (hx : ∀ i, x i ∈ U)
    (i : Tok) :
    balancedExpertMixture P (fun e i => f e (x i)) i ∈ U := by
  apply balancedExpertMixture_mem_submodule
  intro e j
  exact hf e (x j) (hx j)

end GenericMixture

/-! ## Section 2: Arnold–Majorana Specialization -/

section ArnoldMajoranaSpecialization

open InfoGeometry.Canonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable {n : Nat} [Nonempty (Fin n)]

/--
Arnold–Majorana balanced expert mixture with arbitrary coupling `P`.

This replaces the `normalizedWeights` in `arnoldNetworkOutput` with
a generic coupling matrix `P`, producing:

`h_out(i) = ∑_e P(i,e) • expert_e(x_i)`
-/
noncomputable def balancedArnoldMixture
    {Tok : Type*} [Fintype Tok]
    (P : Tok → ExpertIdx n → ℝ)
    (net : ArnoldMajoranaNetwork n E)
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok) : ArnoldMajoranaCarrier E :=
  balancedExpertMixture P (fun e i => (net.moe.experts e).apply (x i)) i

/--
The Arnold–Majorana balanced mixture preserves any submodule `U` that
is preserved by every expert in the network, for any coupling `P`.

All token inputs must lie in `U`.
-/
theorem balancedArnoldMixture_mem_submodule
    {Tok : Type*} [Fintype Tok]
    (P : Tok → ExpertIdx n → ℝ)
    (net : ArnoldMajoranaNetwork n E)
    (U : Submodule ℝ (ArnoldMajoranaCarrier E))
    (x : Tok → ArnoldMajoranaCarrier E)
    (hU : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      v ∈ U → (net.moe.experts e).apply v ∈ U)
    (hx : ∀ i, x i ∈ U)
    (i : Tok) :
    balancedArnoldMixture P net x i ∈ U := by
  apply balancedExpertMixture_mem_submodule_of_input
  · exact hU
  · exact hx

/--
The existing `arnoldNetworkOutput` is the balanced Arnold mixture with
`normalizedWeights` as the coupling.
-/
theorem arnoldNetworkOutput_eq_balancedArnoldMixture
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (β : ℝ)
    (net : ArnoldMajoranaNetwork n E)
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok) :
    arnoldNetworkOutput n net β x i =
      balancedArnoldMixture (normalizedWeights n β x) net x i := by
  simp [arnoldNetworkOutput, balancedArnoldMixture, balancedExpertMixture]

end ArnoldMajoranaSpecialization

/-! ## Section 3: Sinkhorn Coefficient Bridge -/

section SinkhornBridge

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (n : Nat) [Nonempty (Fin n)]

/--
The Sinkhorn-balanced Arnold mixture uses the `switchMatrix` (= normalized weights)
as the coupling for the balanced expert mixture.
-/
noncomputable def sinkhornBalancedMixture
    (β : ℝ)
    (layer : MoELayer n V)
    (x : Fin n → V)
    (i : Fin n) : V :=
  balancedExpertMixture (switchMatrix n β x) (fun e i => (layer.experts e).apply (x i)) i

/--
The Sinkhorn-balanced mixture equals the standard normalized mixture.
-/
theorem sinkhornBalancedMixture_eq_normalizedMixture
    (β : ℝ)
    (layer : MoELayer n V)
    (x : Fin n → V)
    (i : Fin n) :
    sinkhornBalancedMixture n β layer x i = normalizedMixture layer β x i := by
  simp [sinkhornBalancedMixture, balancedExpertMixture, normalizedMixture, switchMatrix]

/--
Submodule preservation for Sinkhorn-balanced mixtures: inherited directly
from the generic theorem.
-/
theorem sinkhornBalancedMixture_mem_submodule
    (β : ℝ)
    (U : Submodule ℝ V)
    (layer : MoELayer n V)
    (x : Fin n → V)
    (hU : ∀ e : ExpertIdx n, ∀ v : V, v ∈ U → (layer.experts e).apply v ∈ U)
    (hx : ∀ i, x i ∈ U)
    (i : Fin n) :
    sinkhornBalancedMixture n β layer x i ∈ U := by
  rw [sinkhornBalancedMixture]
  exact balancedExpertMixture_mem_submodule_of_input _ U _ x hU hx i

end SinkhornBridge

/-! ## Section 4: Birkhoff Permutation Readback -/

section BirkhoffReadback

variable (n : Nat) [Nonempty (Fin n)]

/--
Permutation-routed expert output: expert `σ(i)` processes token `i`.
-/
noncomputable def permutationRoutedOutput
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (σ : Equiv.Perm (Fin n))
    (expertOutput : ExpertIdx n → Fin n → V)
    (i : Fin n) : V :=
  expertOutput (σ i) i

/--
Under bistochastic assumptions, the balanced expert mixture can be read as a
convex combination of permutation-routed expert outputs, via the
Birkhoff–von Neumann decomposition.

Specifically, if `P` is doubly stochastic, then:
`∑_e P(i,e) • f(e,i) = ∑_σ λ_σ • f(σ(i), i)`

for some convex weights `λ_σ ≥ 0`, `∑ λ_σ = 1`.
-/
theorem balancedExpertMixture_eq_convex_permutation_mixture
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : BirkhoffRouting.IsDoublyStochastic P)
    (expertOutput : ExpertIdx n → Fin n → V) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∀ i : Fin n, balancedExpertMixture P expertOutput i =
        ∑ σ, w σ • permutationRoutedOutput n σ expertOutput i := by
  have hPM : P ∈ doublyStochastic ℝ (Fin n) := by
    simpa [BirkhoffRouting.IsDoublyStochastic, mem_doublyStochastic_iff_sum] using hP
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hPM
  refine ⟨w, hw_nonneg, hw_sum, ?_⟩
  intro i
  simp only [balancedExpertMixture, permutationRoutedOutput]
  have hPie : ∀ e, P i e = ∑ σ, if σ i = e then w σ else 0 := by
    intro e
    have h := congr_fun (congr_fun hw_eq.symm i) e
    simp [Matrix.sum_apply, Matrix.smul_apply] at h
    exact h
  simp_rw [hPie]
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  congr 1; ext σ
  simp

/--
Under the bistochastic switch hypothesis, the Sinkhorn-balanced MoE mixture
decomposes as a convex combination of permutation-routed expert outputs.
-/
theorem sinkhornBalanced_permutation_decomposition
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : ℝ)
    (layer : MoELayer n V)
    (x : Fin n → V)
    (hcol : IsBistochasticSwitch n β x) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      ∑ σ, w σ = 1 ∧
      ∀ i : Fin n, sinkhornBalancedMixture n β layer x i =
        ∑ σ, w σ • (layer.experts (σ i)).apply (x i) := by
  have hDS : BirkhoffRouting.IsDoublyStochastic (switchMatrix n β x) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i e; exact normalizedWeights_nonneg (n := n) β x i e
    · intro i; exact switchMatrix_row_sum_one (n := n) β x i
    · exact hcol
  obtain ⟨w, hw_nonneg, hw_sum, hw_perm⟩ :=
    balancedExpertMixture_eq_convex_permutation_mixture n
      (switchMatrix n β x) hDS (fun e i => (layer.experts e).apply (x i))
  refine ⟨w, hw_nonneg, hw_sum, ?_⟩
  intro i
  rw [sinkhornBalancedMixture, hw_perm i]
  rfl

end BirkhoffReadback

/-! ## Epistemic Boundary Documentation

### PROVED IN LEAN:
- `balancedExpertMixture_mem_submodule`: generic submodule preservation for
  arbitrary coupling, no stochasticity needed
- `balancedExpertMixture_mem_submodule_of_input`: same with expert-applied inputs
- `balancedArnoldMixture_mem_submodule`: Arnold–Majorana specialization
- `arnoldNetworkOutput_eq_balancedArnoldMixture`: existing output = balanced mixture
  with normalizedWeights
- `sinkhornBalancedMixture_eq_normalizedMixture`: Sinkhorn mixture = normalized mixture
- `sinkhornBalancedMixture_mem_submodule`: submodule preservation for Sinkhorn mixture
- `balancedExpertMixture_eq_convex_permutation_mixture`: Birkhoff readback for a
  doubly stochastic coupling
- `sinkhornBalanced_permutation_decomposition`: Birkhoff decomposition of the
  Sinkhorn-balanced mixture

### NOT CLAIMED:
- Convex combination of Bogoliubov transformations is Bogoliubov
- Effective operator preserves Cl(5,5)
- Sinkhorn coupling is a quantum algorithm
- Q₅₅(h_out) = Q₅₅(h_in) under convex mixing

### OPEN:
- Bogoliubov-specific invariant audit (which invariants survive convex mixing?)
- Weakest Cl(5,5)-compatible convexly stable invariant
- Context-to-cost bridge formalization
-/

end InfoGeometry.LLM.BogoliubovSinkhornRouting
