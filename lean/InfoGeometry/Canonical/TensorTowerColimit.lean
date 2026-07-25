import Mathlib.Tactic

/-
#### BUCKET 1: CLOSED FINITE/STAGED THEOREMS
- psi_comp_iota_seq: finite chain/cone compatibility by induction, using
  `psi_comm`
- protected_states_survive_colimit: conditional nonvanishing transport from an
  explicit kernel-lifting hypothesis and a finite-stage protection predicate

#### BUCKET 2: CONDITIONAL — requires the stated cone/kernel witnesses
#### BUCKET 3: No theorem in this file asserts a universal-property, topological,
or analytic colimit result.
-/

section TensorTowerColimit

variable {R : Type*} [CommRing R]
variable (A : ℕ → Type*)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (iota : ∀ n, A n →ₗ[R] A (n + 1))
variable (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf]
variable (psi : ∀ n, A n →ₗ[R] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)

include psi_comm

def iota_seq (n : ℕ) : ∀ m, A n →ₗ[R] A (n + m)
| 0 => LinearMap.id
| m + 1 => (iota (n + m)).comp (iota_seq n m)

theorem psi_comp_iota_seq (n m : ℕ) :
    (psi (n + m)).comp (iota_seq A iota n m) = psi n := by
  induction' m with m ih
  · dsimp [iota_seq]
  · dsimp [iota_seq]
    rw [← LinearMap.comp_assoc]
    have hcomm : (psi (n + (m + 1))).comp (iota (n + m)) = psi (n + m) := by
      simpa [Nat.add_assoc] using psi_comm (n + m)
    rw [hcomm]
    exact ih

/-- **Theorem: Generic Colimit Trace Commutativity**
    For any linear evaluation functional `psi_trace : A_inf →ₗ[R] R` on the colimit space,
    evaluating `psi_trace` on the $m$-step colimit image $\psi(n+m)(\text{iota\_seq } n m x)$
    is identically equal to evaluating it at stage $n$: $\psi_{\text{trace}}(\psi n x)$. -/
theorem colimit_trace_comm (psi_trace : A_inf →ₗ[R] R) (n m : ℕ) (x : A n) :
    psi_trace (psi (n + m) (iota_seq A iota n m x)) = psi_trace (psi n x) := by
  have h_comp := psi_comp_iota_seq A iota A_inf psi psi_comm n m
  have h_eval := congr_arg (fun (f : A n →ₗ[R] A_inf) => psi_trace (f x)) h_comp
  exact h_eval

variable (colimit_kernel : ∀ (n : ℕ) (x : A n), psi n x = 0 → ∃ m, iota_seq A iota n m x = 0)

include colimit_kernel

omit psi_comm in
/-- Legacy name for the algebraic predicate that every finite-stage iterate
remains nonzero. No topology is present in this definition. -/
def IsTopologicallyProtected (n : ℕ) (x : A n) : Prop :=
  ∀ m, iota_seq A iota n m x ≠ 0

omit psi_comm in
/-- Under the explicit kernel-lifting hypothesis, stagewise nonvanishing
implies nonvanishing of the target map. This is conditional algebraic transport,
not a universal-property or analytic colimit theorem. -/
theorem protected_states_survive_colimit (n : ℕ) (x : A n)
    (h_prot : IsTopologicallyProtected A iota n x) : psi n x ≠ 0 := by
  intro h_vanish
  have h_ex := colimit_kernel n x h_vanish
  rcases h_ex with ⟨m, hm⟩
  exact h_prot m hm

end TensorTowerColimit
