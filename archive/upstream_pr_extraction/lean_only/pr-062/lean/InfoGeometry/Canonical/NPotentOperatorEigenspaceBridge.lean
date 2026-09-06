import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic
import InfoGeometry.Topology.ConformalSpin
import InfoGeometry.Canonical.AffineConformalHullNPotencyBridge

/-!
# N-Potent Operator Spectral Decomposition and Fibonacci Boundary Eigenspace

This module formalizes the operator-level theorems for $n$-potent endomorphisms
$T^n = T$ on complex vector spaces, proving the spectral containment
$\operatorname{Spec}_{\neq 0}(T) \subseteq \mu_{n-1}$ and establishing the
topological Fibonacci boundary eigenspace $H_{\mathrm{Fib}} = \ker(T - \theta_\tau I)$.

## Key Theorems:
- `eigenvalue_pow_eq_of_isNPotent`: $T^n = T \wedge T v = \lambda v \implies \lambda^n = \lambda$.
- `nonzero_eigenvalue_pow_sub_one_eq_one`: Nonzero eigenvalues satisfy $\lambda^{n-1} = 1$.
- `sixPotent_nonzero_eigenvalue_pow_five`: For 6-potent operators, nonzero eigenvalues satisfy $\lambda^5 = 1$.
- `mem_fibonacciEigenspace_iff`: $v \in H_{\mathrm{Fib}} \iff T v = \theta_\tau \cdot v$.
- `fibonacciEigenspace_invariant`: $T(H_{\mathrm{Fib}}) \subseteq H_{\mathrm{Fib}}$.
- `fibonacciEigenspace_is_eigenvector`: Elements in $H_{\mathrm{Fib}}$ realize $\theta_\tau$ as an eigenvalue.
-/

noncomputable section

namespace InfoGeometry.Canonical.NPotentOperatorEigenspaceBridge

open Complex
open InfoGeometry.Topology.CFT
open InfoGeometry.Canonical.AffineConformalHullNPotencyBridge

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An endomorphism $T$ is $n$-potent if $T^n = T$. -/
def IsNPotent (n : ℕ) (T : Module.End ℂ V) : Prop :=
  T ^ n = T

/-! ### The general zero-mode projector -/

/-- The canonical polynomial projector onto the zero eigenspace of an
`n`-potent endomorphism.  The tripotent projector `1 - T ^ 2` is the
special case `n = 3`; the Fibonacci `6`-potent case uses `1 - T ^ 5`. -/
def nPotentZeroProjector (n : ℕ) (T : Module.End ℂ V) : Module.End ℂ V :=
  1 - T ^ (n - 1)

theorem nPotent_power_pred_idempotent (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    T ^ (n - 1) * T ^ (n - 1) = T ^ (n - 1) := by
  rw [← pow_add]
  have hsplit : (n - 1) + (n - 1) = n + (n - 2) := by omega
  rw [hsplit, pow_add, hT]
  rw [← pow_succ']
  congr 1
  omega

theorem nPotentZeroProjector_sq (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    nPotentZeroProjector n T * nPotentZeroProjector n T =
      nPotentZeroProjector n T := by
  have hU := nPotent_power_pred_idempotent n hn T hT
  dsimp [nPotentZeroProjector]
  calc
    (1 - T ^ (n - 1)) * (1 - T ^ (n - 1)) =
        1 - T ^ (n - 1) - T ^ (n - 1) +
          T ^ (n - 1) * T ^ (n - 1) := by noncomm_ring
    _ = 1 - T ^ (n - 1) - T ^ (n - 1) + T ^ (n - 1) := by rw [hU]
    _ = 1 - T ^ (n - 1) := by abel

theorem nPotent_mul_zeroProjector (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    T * nPotentZeroProjector n T = 0 := by
  dsimp [nPotentZeroProjector]
  have h_pow : T * T ^ (n - 1) = T ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  calc
    T * (1 - T ^ (n - 1)) = T - T * T ^ (n - 1) := by noncomm_ring
    _ = T - T ^ n := by rw [h_pow]
    _ = 0 := by rw [hT, sub_self]

theorem nPotent_zeroProjector_mul (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    nPotentZeroProjector n T * T = 0 := by
  dsimp [nPotentZeroProjector]
  have h_pow : T ^ (n - 1) * T = T ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    (1 - T ^ (n - 1)) * T = T - T ^ (n - 1) * T := by noncomm_ring
    _ = T - T ^ n := by rw [h_pow]
    _ = 0 := by rw [hT, sub_self]

/-! The zero-mode projector is not merely one-sided annihilating: it is a
commuting complementary projector for every `n`-potent operator. -/

theorem nPotent_zeroProjector_commutes (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    nPotentZeroProjector n T * T = T * nPotentZeroProjector n T := by
  rw [nPotent_zeroProjector_mul n hn T hT, nPotent_mul_zeroProjector n hn T hT]

theorem nPotent_zeroProjector_mul_power_pred (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    nPotentZeroProjector n T * (T ^ (n - 1)) = 0 := by
  dsimp [nPotentZeroProjector]
  have hU := nPotent_power_pred_idempotent n hn T hT
  calc
    (1 - T ^ (n - 1)) * T ^ (n - 1) =
        T ^ (n - 1) - T ^ (n - 1) * T ^ (n - 1) := by noncomm_ring
    _ = 0 := by rw [hU, sub_self]

theorem nPotent_power_pred_mul_zeroProjector (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    (T ^ (n - 1)) * nPotentZeroProjector n T = 0 := by
  dsimp [nPotentZeroProjector]
  have hU := nPotent_power_pred_idempotent n hn T hT
  calc
    T ^ (n - 1) * (1 - T ^ (n - 1)) =
        T ^ (n - 1) - T ^ (n - 1) * T ^ (n - 1) := by noncomm_ring
    _ = 0 := by rw [hU, sub_self]

theorem nPotent_zeroProjector_add_power_pred_eq_one (n : ℕ)
    (T : Module.End ℂ V) :
    nPotentZeroProjector n T + T ^ (n - 1) = 1 := by
  dsimp [nPotentZeroProjector]
  ext x
  simp

theorem nPotent_power_pred_add_zeroProjector_eq_one (n : ℕ)
    (T : Module.End ℂ V) :
    T ^ (n - 1) + nPotentZeroProjector n T = 1 := by
  rw [add_comm, nPotent_zeroProjector_add_power_pred_eq_one]

theorem nPotentZeroProjector_range_eq_ker (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    LinearMap.range (nPotentZeroProjector n T) = LinearMap.ker T := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change T (nPotentZeroProjector n T x) = 0
    have h := congrArg (fun A : Module.End ℂ V => A x)
      (nPotent_mul_zeroProjector n hn T hT)
    exact h
  · intro x hx
    have hx0 : T x = 0 := LinearMap.mem_ker.mp hx
    have hpred : n - 1 = (n - 2) + 1 := by omega
    refine ⟨x, ?_⟩
    dsimp [nPotentZeroProjector]
    change x - (T ^ (n - 1)) x = x
    rw [hpred, pow_succ]
    simp [hx0]

/-! The complementary idempotent sector has an equally intrinsic
    description: it is the fixed-point submodule of `T^(n-1)`. -/

theorem nPotent_power_pred_range_eq_fixed_submodule (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    LinearMap.range (T ^ (n - 1)) =
      LinearMap.ker (1 - T ^ (n - 1)) := by
  have hU := nPotent_power_pred_idempotent n hn T hT
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    change ((1 - T ^ (n - 1)) * T ^ (n - 1)) x = 0
    simp [sub_mul, hU]
  · intro x hx
    apply LinearMap.mem_range.mpr
    refine ⟨x, ?_⟩
    have hx0 := LinearMap.mem_ker.mp hx
    change (T ^ (n - 1)) x = x
    have : x - (T ^ (n - 1)) x = 0 := by
      simpa only [sub_eq_add_neg] using hx0
    exact sub_eq_zero.mp this |>.symm

theorem mem_nPotent_power_pred_range_iff (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) (x : V) :
    x ∈ LinearMap.range (T ^ (n - 1)) ↔ (T ^ (n - 1)) x = x := by
  constructor
  · intro hx
    have hxker : x ∈ LinearMap.ker (1 - T ^ (n - 1)) := by
      rw [← nPotent_power_pred_range_eq_fixed_submodule n hn T hT]
      exact hx
    have h := LinearMap.mem_ker.mp hxker
    change x - (T ^ (n - 1)) x = 0 at h
    exact sub_eq_zero.mp h |>.symm
  · intro hx
    rw [nPotent_power_pred_range_eq_fixed_submodule n hn T hT]
    apply LinearMap.mem_ker.mpr
    change x - (T ^ (n - 1)) x = 0
    exact sub_eq_zero.mpr hx.symm

/-! The projector gives a canonical algebraic split at every `n`-potent
stage.  This is a pointwise decomposition; no topology or diagonalisation
assumption is involved. -/

theorem nPotent_zeroMode_remainder_decomposition (n : ℕ)
    (T : Module.End ℂ V) (x : V) :
    x = nPotentZeroProjector n T x + (T ^ (n - 1)) x := by
  dsimp [nPotentZeroProjector]
  change x = (x - (T ^ (n - 1)) x) + (T ^ (n - 1)) x
  abel

theorem nPotent_zeroProjector_apply_of_mem_ker (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (x : V)
    (hx : x ∈ LinearMap.ker T) :
    nPotentZeroProjector n T x = x := by
  have hx0 : T x = 0 := LinearMap.mem_ker.mp hx
  have hpred : n - 1 = (n - 2) + 1 := by omega
  dsimp [nPotentZeroProjector]
  change x - (T ^ (n - 1)) x = x
  rw [hpred, pow_succ, Module.End.mul_apply, hx0, map_zero]
  simp

theorem nPotent_remainder_apply_of_mem_ker (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (x : V)
    (hx : x ∈ LinearMap.ker T) :
    (T ^ (n - 1)) x = 0 := by
  have hx0 : T x = 0 := LinearMap.mem_ker.mp hx
  have hpred : n - 1 = (n - 2) + 1 := by omega
  rw [hpred, pow_succ, Module.End.mul_apply, hx0, map_zero]

/-! The two canonical ranges form an algebraic direct decomposition.  These
results are stated here (rather than inferred from a spectral theorem) so
that downstream zero/nonzero-sector arguments can use only the `n`-potency
law. -/

theorem nPotent_zeroMode_range_disjoint_power_pred_range (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) :
    Disjoint (LinearMap.range (nPotentZeroProjector n T))
      (LinearMap.range (T ^ (n - 1))) := by
  refine Submodule.disjoint_def.mpr ?_
  intro x hx0 hx1
  rcases hx0 with ⟨y, rfl⟩
  have hker : nPotentZeroProjector n T y ∈ LinearMap.ker T := by
    apply LinearMap.mem_ker.mpr
    exact congrArg (fun F : Module.End ℂ V => F y)
      (nPotent_mul_zeroProjector n hn T hT)
  have hpow_zero := nPotent_remainder_apply_of_mem_ker n hn T
    (nPotentZeroProjector n T y) hker
  have hpow_fixed : (T ^ (n - 1)) (nPotentZeroProjector n T y) =
      nPotentZeroProjector n T y := by
    exact mem_nPotent_power_pred_range_iff n hn T hT _ |>.mp hx1
  rw [hpow_zero] at hpow_fixed
  exact hpow_fixed.symm

theorem nPotent_zeroMode_range_sup_power_pred_range_eq_top (n : ℕ)
    (T : Module.End ℂ V) :
    LinearMap.range (nPotentZeroProjector n T) ⊔
        LinearMap.range (T ^ (n - 1)) = ⊤ := by
  apply le_antisymm le_top
  intro x _
  have hdecomp := nPotent_zeroMode_remainder_decomposition n T x
  rw [hdecomp]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

/-- The `6`-potent/Fibonacci zero-mode projector is `1 - T^5`. -/
def sixPotentZeroProjector (T : Module.End ℂ V) : Module.End ℂ V :=
  nPotentZeroProjector 6 T

@[simp] theorem sixPotentZeroProjector_apply (T : Module.End ℂ V) :
    sixPotentZeroProjector T = 1 - T ^ 5 := by
  rfl

theorem sixPotentZeroProjector_range_eq_ker (T : Module.End ℂ V)
    (hT : IsNPotent 6 T) :
    LinearMap.range (sixPotentZeroProjector T) = LinearMap.ker T := by
  exact nPotentZeroProjector_range_eq_ker 6 (by norm_num) T hT

theorem sixPotentZeroProjector_sq (T : Module.End ℂ V)
    (hT : IsNPotent 6 T) :
    sixPotentZeroProjector T * sixPotentZeroProjector T =
      sixPotentZeroProjector T := by
  simpa [sixPotentZeroProjector] using
    nPotentZeroProjector_sq 6 (by norm_num) T hT

theorem sixPotent_mul_zeroProjector (T : Module.End ℂ V)
    (hT : IsNPotent 6 T) :
    T * sixPotentZeroProjector T = 0 := by
  simpa [sixPotentZeroProjector] using
    nPotent_mul_zeroProjector 6 (by norm_num) T hT

theorem sixPotent_zeroProjector_mul (T : Module.End ℂ V)
    (hT : IsNPotent 6 T) :
    sixPotentZeroProjector T * T = 0 := by
  simpa [sixPotentZeroProjector] using
    nPotent_zeroProjector_mul 6 (by norm_num) T hT

/-- Key Spectral Lemma: If $T$ is $n$-potent and $v$ is an eigenvector with eigenvalue `eigVal`,
    then $\lambda^n = \lambda$. -/
theorem eigenvalue_pow_eq_of_isNPotent (n : ℕ) (T : Module.End ℂ V)
    (hT : IsNPotent n T) (eigVal : ℂ) (v : V) (hv : v ≠ 0)
    (h_eig : T v = eigVal • v) :
    eigVal ^ n = eigVal := by
  have h_iter : ∀ m : ℕ, (T ^ m) v = (eigVal ^ m) • v := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero, one_smul]
      rfl
    | succ k ih =>
      show (T ^ k * T) v = (eigVal ^ (k + 1)) • v
      change (T ^ k) (T v) = (eigVal ^ (k + 1)) • v
      rw [h_eig, map_smul, ih, smul_smul, pow_succ, mul_comm eigVal (eigVal ^ k)]
  have h_apply : (T ^ n) v = T v := by
    have : T ^ n = T := hT
    rw [this]
  rw [h_iter n, h_eig] at h_apply
  have h_sub : (eigVal ^ n - eigVal) • v = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact h_apply
  have h_scalar : eigVal ^ n - eigVal = 0 := by
    by_contra h_ne
    have : v = 0 := by
      have : (eigVal ^ n - eigVal)⁻¹ • ((eigVal ^ n - eigVal) • v) = (eigVal ^ n - eigVal)⁻¹ • (0 : V) := by
        rw [h_sub]
      rwa [inv_smul_smul₀ h_ne, smul_zero] at this
    exact hv this
  exact sub_eq_zero.mp h_scalar

/-- Nonzero eigenvalue of an $n$-potent operator is an $(n-1)$-th root of unity ($n \ge 2$). -/
theorem nonzero_eigenvalue_pow_sub_one_eq_one (n : ℕ) (hn : 2 ≤ n)
    (T : Module.End ℂ V) (hT : IsNPotent n T) (eigVal : ℂ) (heig_ne : eigVal ≠ 0)
    (v : V) (hv : v ≠ 0) (h_eig : T v = eigVal • v) :
    eigVal ^ (n - 1) = 1 := by
  have h_pow := eigenvalue_pow_eq_of_isNPotent n T hT eigVal v hv h_eig
  have h_inHull : inHull n eigVal := h_pow
  have h_cases := (inHull_iff_zero_or_rootOfUnity n hn eigVal).mp h_inHull
  cases h_cases with
  | inl h_zero => exact False.elim (heig_ne h_zero)
  | inr h_root => exact h_root

/-- 6-Potent Hull: any nonzero eigenvalue satisfies $\lambda^5 = 1$. -/
theorem sixPotent_nonzero_eigenvalue_pow_five (T : Module.End ℂ V)
    (hT : IsNPotent 6 T) (eigVal : ℂ) (heig_ne : eigVal ≠ 0)
    (v : V) (hv : v ≠ 0) (h_eig : T v = eigVal • v) :
    eigVal ^ 5 = 1 := by
  have h := nonzero_eigenvalue_pow_sub_one_eq_one 6 (by norm_num) T hT eigVal heig_ne v hv h_eig
  exact h

/-- The Fibonacci boundary eigenspace for an endomorphism $T$: $H_{\mathrm{Fib}} = \ker(T - \theta_\tau I)$. -/
def fibonacciEigenspace (T : Module.End ℂ V) : Submodule ℂ V :=
  LinearMap.ker (T - fibonacciTopologicalTwist • (LinearMap.id : Module.End ℂ V))

/-- An element $v$ is in the Fibonacci eigenspace iff $T v = \theta_\tau \cdot v$. -/
theorem mem_fibonacciEigenspace_iff (T : Module.End ℂ V) (v : V) :
    v ∈ fibonacciEigenspace T ↔ T v = fibonacciTopologicalTwist • v := by
  dsimp [fibonacciEigenspace]
  rw [LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

/-- The Fibonacci boundary eigenspace is $T$-invariant. -/
theorem fibonacciEigenspace_invariant (T : Module.End ℂ V) (v : V)
    (hv : v ∈ fibonacciEigenspace T) :
    T v ∈ fibonacciEigenspace T := by
  rw [mem_fibonacciEigenspace_iff] at hv ⊢
  rw [hv, LinearMap.map_smul, hv, smul_smul, mul_comm]

/-- Non-zero vectors in the Fibonacci eigenspace are bona fide eigenvectors. -/
theorem fibonacciEigenspace_is_eigenvector (T : Module.End ℂ V)
    (v : V) (hv_mem : v ∈ fibonacciEigenspace T) (_hv_ne : v ≠ 0) :
    ∃ eigVal : ℂ, eigVal = fibonacciTopologicalTwist ∧ T v = eigVal • v := by
  refine ⟨fibonacciTopologicalTwist, rfl, (mem_fibonacciEigenspace_iff T v).mp hv_mem⟩

end InfoGeometry.Canonical.NPotentOperatorEigenspaceBridge
