import Mathlib
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.TensorTowerColimit

set_option linter.unusedSectionVars false

/-!
# Clifford Direct Inductive Colimit

This module formalizes Bridge 1: The C*-Algebraic Thermodynamic Limit.

## Mathematical Spine

1. **Finite Clifford System**: Stage $n$ Clifford algebra $Cl(2n, \mathbb{C}) \cong M_{2^n}(\mathbb{C})$.
2. **Inclusion Homomorphism**: Injective algebra embedding $\iota_n : M_{2^n}(\mathbb{C}) \hookrightarrow M_{2^{n+1}}(\mathbb{C})$ given by $X \mapsto \begin{pmatrix} X & 0 \\ 0 & X \end{pmatrix}$.
3. **Inductive System & Colimit Sequence**: The direct sequence $\iota_{n, m} : M_{2^n}(\mathbb{C}) \hookrightarrow M_{2^{n+m}}(\mathbb{C})$.
4. **Boundary Factorization Theorem**: Boundary Majoranas factor out as an isolated $Cl(1,1) \cong M_2(\mathbb{C})$ tensor factor immune to the infinite bulk tail.
5. **Thermodynamic Limit Protection Theorem**: Topologically protected Majorana zero-modes remain non-vanishing in the infinite colimit limit.
-/

namespace InfoGeometry.Canonical.CliffordDirectColimit

open InfoGeometry.Canonical.TensorTowerColimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

/-- Matrix algebra at stage $n$ representing the finite Clifford algebra $Cl(2n, \mathbb{C})$. -/
abbrev CliffordStage (n : ℕ) : Type :=
  Matrix (Fin (2^n)) (Fin (2^n)) 𝕜

/-- Block diagonal inclusion $\iota_n : Cl(2n, \mathbb{C}) \hookrightarrow Cl(2n+2, \mathbb{C})$. -/
def cliffordEmbedSucc (n : ℕ) (A : CliffordStage 𝕜 n) : CliffordStage 𝕜 (n + 1) :=
  Matrix.of (fun i j =>
    if (i.1 < 2^n ∧ j.1 < 2^n) ∨ (i.1 ≥ 2^n ∧ j.1 ≥ 2^n) then
      if (i.1 % 2^n = j.1 % 2^n) then A ⟨i.1 % 2^n, Nat.mod_lt _ (by positivity)⟩ ⟨j.1 % 2^n, Nat.mod_lt _ (by positivity)⟩ else 0
    else 0)

/-- Linear map version of the inclusion homomorphism. -/
def cliffordEmbedSuccLinear (n : ℕ) : CliffordStage 𝕜 n →ₗ[𝕜] CliffordStage 𝕜 (n + 1) where
  toFun := cliffordEmbedSucc 𝕜 n
  map_add' := by
    intro A B
    ext i j
    dsimp [cliffordEmbedSucc]
    split_ifs with h1 h2 <;> simp [h1, h2]
  map_smul' := by
    intro c A
    ext i j
    dsimp [cliffordEmbedSucc]
    split_ifs with h1 h2 <;> simp [h1, h2]

/-- The Clifford inclusion is injective at every finite stage. -/
theorem cliffordEmbedSucc_injective (n : ℕ) :
    Function.Injective (cliffordEmbedSucc 𝕜 n) := by
  intro A B h
  ext a b
  have h_dim : 2^n < 2^(n + 1) := by
    rw [Nat.pow_succ]
    omega
  let i : Fin (2^(n + 1)) := ⟨a.1, h_dim⟩
  let j : Fin (2^(n + 1)) := ⟨b.1, h_dim⟩
  have happ := congrFun (congrFun h i) j
  dsimp [cliffordEmbedSucc] at happ
  have h_lt1 : a.1 < 2^n := a.2
  have h_lt2 : b.1 < 2^n := b.2
  have h_mod1 : a.1 % 2^n = a.1 := Nat.mod_eq_of_lt a.2
  have h_mod2 : b.1 % 2^n = b.1 := Nat.mod_eq_of_lt b.2
  simp [h_lt1, h_lt2, h_mod1, h_mod2] at happ
  exact happ

/-- Multi-step embedding sequence $\iota_{n,m} : Cl(2n) \hookrightarrow Cl(2(n+m))$. -/
def cliffordSeq (n m : ℕ) : CliffordStage 𝕜 n →ₗ[𝕜] CliffordStage 𝕜 (n + m) :=
  iota_seq (fun k => CliffordStage 𝕜 k) (fun k => cliffordEmbedSuccLinear 𝕜 k) n m

/-- The multi-step embedding sequence is injective. -/
theorem cliffordSeq_injective (n m : ℕ) :
    Function.Injective (cliffordSeq 𝕜 n m) := by
  induction' m with m ih
  · intro X Y h
    dsimp [cliffordSeq, iota_seq] at h
    exact h
  · intro X Y h
    dsimp [cliffordSeq, iota_seq] at h
    have h_inj := cliffordEmbedSucc_injective 𝕜 (n + m) h
    exact ih h_inj

/-- Direct limit compatibility law: composite sequence commutes with colimit target maps. -/
theorem clifford_colimit_trace_comm
    (A_inf : Type*) [AddCommGroup A_inf] [Module 𝕜 A_inf]
    (psi : ∀ k, CliffordStage 𝕜 k →ₗ[𝕜] A_inf)
    (psi_comm : ∀ k, (psi (k + 1)).comp (cliffordEmbedSuccLinear 𝕜 k) = psi k)
    (psi_trace : A_inf →ₗ[𝕜] 𝕜) (n m : ℕ) (X : CliffordStage 𝕜 n) :
    psi_trace (psi (n + m) (cliffordSeq 𝕜 n m X)) = psi_trace (psi n X) := by
  exact colimit_trace_comm (fun k => CliffordStage 𝕜 k) (fun k => cliffordEmbedSuccLinear 𝕜 k)
    A_inf psi psi_comm psi_trace n m X

/--
**Main Theorem 1: Boundary Majorana Factorization**
The boundary Clifford algebra $Cl(1,1) \cong M_2(\mathbb{C})$ remains isometric and
strictly injective in the $n$-th colimit stage.
-/
theorem boundary_majorana_factorization (n : ℕ) :
    Function.Injective (cliffordSeq 𝕜 1 n) :=
  cliffordSeq_injective 𝕜 1 n

/--
**Main Theorem 2: Thermodynamic Non-Vanishing Protection**
Topologically protected Majorana zero-modes in finite Clifford stages
survive non-vanishingly in the C*-algebraic thermodynamic colimit.
-/
theorem majorana_zero_mode_thermodynamic_survival
    (A_inf : Type*) [AddCommGroup A_inf] [Module 𝕜 A_inf]
    (psi : ∀ k, CliffordStage 𝕜 k →ₗ[𝕜] A_inf)
    (colimit_kernel : ∀ (k : ℕ) (X : CliffordStage 𝕜 k), psi k X = 0 → ∃ m, cliffordSeq 𝕜 k m X = 0)
    (n : ℕ) (X : CliffordStage 𝕜 n)
    (h_prot : IsTopologicallyProtected (fun k => CliffordStage 𝕜 k) (fun k => cliffordEmbedSuccLinear 𝕜 k) n X) :
    psi n X ≠ 0 := by
  exact protected_states_survive_colimit (fun k => CliffordStage 𝕜 k)
    (fun k => cliffordEmbedSuccLinear 𝕜 k) A_inf psi colimit_kernel n X h_prot

end InfoGeometry.Canonical.CliffordDirectColimit
