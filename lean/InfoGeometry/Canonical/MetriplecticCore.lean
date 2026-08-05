import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.MetriplecticCore

Finite metriplectic core:

* skew Poisson bracket lane,
* symmetric metric bracket lane,
* unified Leibniz bracket,
* first/second-law style structural readbacks.
-/

namespace InfoGeometry.Canonical.MetriplecticCore

/-- Ring commutator lane (Poisson-style finite algebraic seed). -/
def commutator {A : Type*} [Ring A] (x y : A) : A :=
  x * y - y * x

/-- Ring anticommutator lane (metric-style finite algebraic seed). -/
def anticommutator {A : Type*} [Ring A] (x y : A) : A :=
  x * y + y * x

theorem commutator_skew {A : Type*} [Ring A] (x y : A) :
    commutator x y = -commutator y x := by
  unfold commutator
  simp [sub_eq_add_neg]

theorem anticommutator_symm {A : Type*} [Ring A] (x y : A) :
    anticommutator x y = anticommutator y x := by
  unfold anticommutator
  simp [add_comm]

structure MetriplecticSystem (A : Type*) [Ring A] where
  poisson : A → A → A
  poisson_skew : ∀ x y, poisson x y = -poisson y x
  metric : A → A → A
  metric_symm : ∀ x y, metric x y = metric y x
  Hamiltonian : A
  Entropy : A
  hamiltonian_conserved : ∀ x, metric x Hamiltonian = 0
  entropy_casimir : ∀ x, poisson x Entropy = 0

namespace MetriplecticSystem

variable {A : Type*} [Ring A] (M : MetriplecticSystem A)

/-- Unified metriplectic Leibniz bracket. -/
def leibniz (x y : A) : A :=
  M.poisson x y + M.metric x y

/-- Hamiltonian is in the kernel of the metric bracket (left form). -/
theorem metric_H_zero (x : A) :
    M.metric x M.Hamiltonian = 0 :=
  M.hamiltonian_conserved x

/-- Hamiltonian is also in the kernel of the metric bracket (right form). -/
theorem metric_H_zero_right (x : A) :
    M.metric M.Hamiltonian x = 0 := by
  rw [M.metric_symm, M.hamiltonian_conserved]

/-- Entropy is a Casimir of the Poisson bracket (left form). -/
theorem poisson_entropy_zero (x : A) :
    M.poisson x M.Entropy = 0 :=
  M.entropy_casimir x

/-- Entropy is a Casimir of the Poisson bracket (right form). -/
theorem poisson_entropy_zero_right (x : A) :
    M.poisson M.Entropy x = 0 := by
  have h := M.poisson_skew x M.Entropy
  rw [M.entropy_casimir x] at h
  have : -M.poisson M.Entropy x = (0 : A) := h.symm
  exact neg_eq_zero.mp this

/-- First-law style readback: zero metric leakage of Hamiltonian. -/
theorem leibniz_H_H_eq_zero
    (h_poisson_diag : M.poisson M.Hamiltonian M.Hamiltonian = 0) :
    M.leibniz M.Hamiltonian M.Hamiltonian = 0 := by
  unfold leibniz
  rw [h_poisson_diag, M.metric_H_zero]
  simp

/--
Second-law style decomposition:
`[S,H]_L = {S,H} + ((S,H))`, where the Poisson part can be eliminated
when `S` is a right-Casimir witness.
-/
theorem leibniz_entropy_H_decompose :
    M.leibniz M.Entropy M.Hamiltonian
      = M.poisson M.Entropy M.Hamiltonian + M.metric M.Entropy M.Hamiltonian := by
  rfl

/-- Casimir specialization: if `poisson Entropy Hamiltonian = 0`, only metric remains. -/
theorem leibniz_entropy_H_eq_metric
    (h_casimir_right : M.poisson M.Entropy M.Hamiltonian = 0) :
    M.leibniz M.Entropy M.Hamiltonian = M.metric M.Entropy M.Hamiltonian := by
  unfold leibniz
  rw [h_casimir_right, zero_add]

/-- Right-Casimir specialization pointwise in the second argument. -/
theorem leibniz_entropy_eq_metric_right
    (h_casimir_right : ∀ x, M.poisson M.Entropy x = 0) :
    ∀ x, M.leibniz M.Entropy x = M.metric M.Entropy x := by
  intro x
  unfold leibniz
  rw [h_casimir_right x, zero_add]

/-- Packaged finite metriplectic core summary: bracket antisymmetry,
kernel identities, and the two first/second-law style readbacks. -/
theorem metriplectic_summary
    (h_poisson_diag : M.poisson M.Hamiltonian M.Hamiltonian = 0) :
    (∀ x, M.metric x M.Hamiltonian = 0) ∧
    (∀ x, M.metric M.Hamiltonian x = 0) ∧
    (∀ x, M.poisson x M.Entropy = 0) ∧
    (∀ x, M.poisson M.Entropy x = 0) ∧
    M.leibniz M.Hamiltonian M.Hamiltonian = 0 ∧
    (∀ x, M.leibniz M.Entropy x = M.metric M.Entropy x) := by
  constructor
  · intro x
    exact M.metric_H_zero x
  · constructor
    · intro x
      exact M.metric_H_zero_right x
    · constructor
      · intro x
        exact M.poisson_entropy_zero x
      · constructor
        · intro x
          exact M.poisson_entropy_zero_right x
        · constructor
          · exact M.leibniz_H_H_eq_zero h_poisson_diag
          · intro x
            exact M.leibniz_entropy_eq_metric_right M.poisson_entropy_zero_right x

end MetriplecticSystem

/--
Canonical finite metriplectic package from commutator/anticommutator lanes,
parameterized by explicit Hamiltonian-kernel and entropy-Casimir witnesses.
-/
def commutatorAnticommutatorSystem
    {A : Type*} [Ring A]
    (H S : A)
    (hHmetric : ∀ x : A, anticommutator x H = 0)
    (hScasimir : ∀ x : A, commutator x S = 0) :
    MetriplecticSystem A where
  poisson := commutator
  poisson_skew := commutator_skew
  metric := anticommutator
  metric_symm := anticommutator_symm
  Hamiltonian := H
  Entropy := S
  hamiltonian_conserved := hHmetric
  entropy_casimir := hScasimir

end InfoGeometry.Canonical.MetriplecticCore
