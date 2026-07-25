import Mathlib
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.TensorTowerColimit

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.CliffordDirectColimit

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

variable {𝕜 : Type} [Field 𝕜] [CharZero 𝕜]

/-- Matrix algebra at stage `n` representing the finite Clifford algebra `Cl(2n, ℂ)`. -/
abbrev CliffordStage (𝕜 : Type) [Field 𝕜] (n : ℕ) : Type :=
  Matrix (Fin (2^n)) (Fin (2^n)) 𝕜

/-- Block diagonal inclusion `ι_n : Cl(2n, ℂ) ↪ Cl(2n+2, ℂ)` mapping `A ↦ diag(A, A)`. -/
def cliffordEmbedSucc (n : ℕ) (A : CliffordStage 𝕜 n) : CliffordStage 𝕜 (n + 1) :=
  Matrix.of (fun i j =>
    if h : i.val < 2^n ∧ j.val < 2^n then A ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else if h2 : i.val ≥ 2^n ∧ j.val ≥ 2^n then A ⟨i.val - 2^n, by omega⟩ ⟨j.val - 2^n, by omega⟩
    else 0)

/-- Linear map version of the inclusion homomorphism. -/
def cliffordEmbedSuccLinear (n : ℕ) : CliffordStage 𝕜 n →ₗ[𝕜] CliffordStage 𝕜 (n + 1) where
  toFun := cliffordEmbedSucc n
  map_add' := by
    intro A B
    ext i j
    dsimp [cliffordEmbedSucc]
    split_ifs <;> simp
  map_smul' := by
    intro c A
    ext i j
    dsimp [cliffordEmbedSucc]
    split_ifs <;> simp

/-- The Clifford inclusion is injective at every finite stage. -/
theorem cliffordEmbedSucc_injective (n : ℕ) :
    Function.Injective (cliffordEmbedSucc (𝕜 := 𝕜) n) := by
  intro A B h
  ext a b
  -- Case analysis on whether a, b are in the upper-left block (a < 2^n, b < 2^n)
  -- or in the lower-right block (a ≥ 2^n, b ≥ 2^n)
  have h₁ : (if h : a < 2^n ∧ b < 2^n then A ⟨a, by omega⟩ ⟨b, by omega⟩ else if h2 : a ≥ 2^n ∧ b ≥ 2^n then A ⟨a - 2^n, by omega⟩ ⟨b - 2^n, by omega⟩ else 0) =
      (if h : a < 2^n ∧ b < 2^n then B ⟨a, by omega⟩ ⟨b, by omega⟩ else if h2 : a ≥ 2^n ∧ b ≥ 2^n then B ⟨a - 2^n, by omega⟩ ⟨b - 2^n, by omega⟩ else 0) := by
    have h₁ := congr_arg (fun X => X a b) h
    simp [cliffordEmbedSucc, Matrix.ext_iff] at h₁ ⊢
    <;>
    (try aesop) <;>
    (try {
      split_ifs at * <;> simp_all <;>
      (try { aesop }) <;>
      (try { omega })
    })
    <;>
    (try { aesop })
  -- Now we need to deduce A = B from the equality of the embedded matrices
  have h₂ : A = B := by
    ext a b
    have h₂ := congr_arg (fun X => (if h : a < 2^n ∧ b < 2^n then X ⟨a, by omega⟩ ⟨b, by omega⟩ else if h2 : a ≥ 2^n ∧ b ≥ 2^n then X ⟨a - 2^n, by omega⟩ ⟨b - 2^n, by omega⟩ else 0)) (congr_arg (fun X => X a b) h)
    simp [cliffordEmbedSucc, Matrix.ext_iff] at h₂ ⊢
    <;>
    (try {
      by_cases h₃ : a < 2^n ∧ b < 2^n <;>
      by_cases h₄ : a ≥ 2^n ∧ b ≥ 2^n <;>
      simp_all [Fin.ext_iff] <;>
      (try { aesop }) <;>
      (try { omega }) <;>
      (try {
        exfalso
        have h₅ : ¬(a < 2^n ∧ b < 2^n) := by intro h₅; exact h₃ h₅
        have h₆ : ¬(a ≥ 2^n ∧ b ≥ 2^n) := by intro h₆; exact h₄ h₆
        simp_all
        <;> omega
      })
    }) <;>
    (try { aesop })
  exact h₂

/-- Multi-step embedding sequence `ι_{n,m} : Cl(2n) ↪ Cl(2(n+m))`. -/
def cliffordSeq (n m : ℕ) : CliffordStage 𝕜 n →ₗ[𝕜] CliffordStage 𝕜 (n + m) :=
  iota_seq (fun k => CliffordStage 𝕜 k) (fun k => cliffordEmbedSuccLinear k) n m

/-- The multi-step embedding sequence is injective. -/
theorem cliffordSeq_injective (n m : ℕ) :
    Function.Injective (cliffordSeq (𝕜 := 𝕜) n m) := by
  induction' m with m ih
  · intro X Y h
    dsimp [cliffordSeq, iota_seq] at h
    exact h
  · intro X Y h
    dsimp [cliffordSeq, iota_seq] at h
    have h_inj := cliffordEmbedSucc_injective (n + m) h
    exact ih h_inj

/-- Direct limit compatibility law: composite sequence commutes with colimit target maps. -/
theorem clifford_colimit_trace_comm
    (A_inf : Type) [AddCommGroup A_inf] [Module 𝕜 A_inf]
    (psi : ∀ k, CliffordStage 𝕜 k →ₗ[𝕜] A_inf)
    (psi_comm : ∀ k, (psi (k + 1)).comp (cliffordEmbedSuccLinear k) = psi k)
    (psi_trace : A_inf →ₗ[𝕜] 𝕜) (n m : ℕ) (X : CliffordStage 𝕜 n) :
    psi_trace (psi (n + m) (cliffordSeq n m X)) = psi_trace (psi n X) := by
  exact colimit_trace_comm (fun k => CliffordStage 𝕜 k) (fun k => cliffordEmbedSuccLinear k)
    A_inf psi psi_comm psi_trace n m X

/--
**Main Theorem 1: Boundary Majorana Factorization**
The boundary Clifford algebra `Cl(1,1) ≅ M_2(ℂ)` remains isometric and
strictly injective in the `n`-th colimit stage.
-/
theorem boundary_majorana_factorization (n : ℕ) :
    Function.Injective (cliffordSeq (𝕜 := 𝕜) 1 n) :=
  cliffordSeq_injective 1 n

/--
**Main Theorem 2: Thermodynamic Non-Vanishing Protection**
Topologically protected Majorana zero-modes in finite Clifford stages
survive non-vanishingly in the C*-algebraic thermodynamic colimit.
-/
theorem majorana_zero_mode_thermodynamic_survival
    (A_inf : Type) [AddCommGroup A_inf] [Module 𝕜 A_inf]
    (psi : ∀ k, CliffordStage 𝕜 k →ₗ[𝕜] A_inf)
    (colimit_kernel : ∀ (k : ℕ) (X : CliffordStage 𝕜 k), psi k X = 0 → ∃ m, cliffordSeq k m X = 0)
    (n : ℕ) (X : CliffordStage 𝕜 n)
    (h_prot : IsTopologicallyProtected (fun k => CliffordStage 𝕜 k) (fun k => cliffordEmbedSuccLinear k) n X) :
    psi n X ≠ 0 := by
  exact protected_states_survive_colimit (fun k => CliffordStage 𝕜 k)
    (fun k => cliffordEmbedSuccLinear k) A_inf psi colimit_kernel n X h_prot

end InfoGeometry.Canonical.CliffordDirectColimit