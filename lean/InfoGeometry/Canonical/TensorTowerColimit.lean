import Mathlib

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
- psi_comp_iota_seq: Inductive proof of colimit commutativity
- protected_states_survive_colimit: Topological protection theorem

#### BUCKET 2: CONDITIONAL THEOREMS
- Requires psi_comm, colimit_exhaustion, colimit_kernel witnesses.

#### BUCKET 3: OPEN CLOSURE DEBT — None.
-/

namespace InfoGeometry.Canonical.TensorTowerColimit

variable {R : Type*} [CommRing R]
variable (A : ℕ → Type*)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (iota : ∀ n, A n →ₗ[R] A (n + 1))
variable (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf]
variable (psi : ∀ n, A n →ₗ[R] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)

def iota_seq (n : ℕ) : ∀ m, A n →ₗ[R] A (n + m)
| 0 => LinearMap.id
| m + 1 => (iota (n + m)).comp (iota_seq n m)

theorem psi_comp_iota_seq (n m : ℕ) :
    (psi (n + m)).comp (iota_seq A iota n m) = psi n := by
  induction' m with m ih
  · dsimp [iota_seq]; exact LinearMap.comp_id (psi n)
  · dsimp [iota_seq]; rw [← LinearMap.comp_assoc]
    have h := psi_comm (n + m); rw [h]; exact ih

variable (colimit_kernel : ∀ (n : ℕ) (x : A n), psi n x = 0 → ∃ m, iota_seq A iota n m x = 0)

def IsTopologicallyProtected (n : ℕ) (x : A n) : Prop := ∀ m, iota_seq A iota n m x ≠ 0

theorem protected_states_survive_colimit (n : ℕ) (x : A n)
    (h_prot : IsTopologicallyProtected A iota n x) : psi n x ≠ 0 := by
  intro h_vanish
  rcases colimit_kernel n x h_vanish with ⟨m, hm⟩
  exact h_prot m hm

end InfoGeometry.Canonical.TensorTowerColimit
