/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Inductive Tower `ClTower A n`
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => a
    | 0, 1 => b
    | 1, 0 => c
    | 1, 1 => d

private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

@[simp] lemma mat2_00 {A : Type*} (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 {A : Type*} (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 {A : Type*} (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 {A : Type*} (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

variable {A : Type*} [Ring A]

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

end Matrix2Simp

universe u

@[reducible] def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

@[reducible] instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 =>
      let _ : Ring (ClTower A n) := instRingClTower n
      inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

private theorem cltower_noncomm_witness {A : Type u} [Ring A] [Nontrivial A] (n : ℕ) :
    ∃ X Y : Matrix (Fin 2) (Fin 2) (ClTower A n), X * Y ≠ Y * X := by
  let _ : Ring (ClTower A n) := instRingClTower n
  have : Nontrivial (ClTower A n) := by
    induction n with
    | zero => infer_instance
    | succ n ih =>
        let _ : Ring (ClTower A n) := instRingClTower n
        exact ⟨⟨Matrix.of fun _ _ => 0, Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0, by
          intro h
          have h00 := congr_fun (congr_fun h 0) 0
          simp at h00⟩⟩
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

variable {A : Type u} [Ring A]

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace]
      rw [towerTrace_zero n, add_zero]

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

/-!
## Archetype $\mathcal{C}\mathcal{L}_1$ & $\mathcal{C}\mathcal{L}_2$: Directed Bott Colimit `Setoid`, Quotient $\mathcal{C}\ell_\infty(A)$ & $\mathrm{Str}_\infty$
-/

section ArchetypeCL1_CL2_ColimitSetoidAndQuotient

/-- Canonical Bott corner embedding $\iota_{\mathrm{Bott}} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+1}(A)$. -/
def bottEmbed {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

theorem bottEmbed_add {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X + Y) = bottEmbed X + bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

theorem bottEmbed_mul {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X * Y) = bottEmbed X * bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

/-- Iterated multi-step Bott embedding $\iota_{\mathrm{Bott}}^{(k)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+k}(A)$. -/
def bottEmbedIter : ∀ {n : ℕ} (k : ℕ), ClTower A n → ClTower A (n + k)
  | _, 0,     X => X
  | _, k + 1, X => bottEmbed (bottEmbedIter k X)

theorem colimit_superTrace_invariant {n : ℕ} (X : ClTower A n) :
    superTrace (bottEmbed X) = superTrace X := by
  dsimp [superTrace, bottEmbed, chiralityOp, towerTrace]
  simp [towerTrace_zero n]

theorem colimit_superTrace_iter_invariant {n : ℕ} (k : ℕ) (X : ClTower A n) :
    superTrace (bottEmbedIter k X) = superTrace X := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]
    rw [colimit_superTrace_invariant, ih]

lemma bottEmbed_congr_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (bottEmbed X) (bottEmbed Y) := by
  subst h_dim; cases eq_of_heq h_heq; exact HEq.rfl

lemma bottEmbedIter_congr_heq {m₁ m₂ : ℕ} (d : ℕ) {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (bottEmbedIter d X) (bottEmbedIter d Y) := by
  induction' d with d ih
  · exact h_heq
  · exact bottEmbed_congr_heq (by simp [h_dim]) ih

lemma bottEmbedIter_add_heq {n : ℕ} (k d : ℕ) (X : ClTower A n) :
    HEq (bottEmbedIter (k + d) X) (bottEmbedIter d (bottEmbedIter k X)) := by
  induction' d with d ih
  · exact HEq.rfl
  · exact bottEmbed_congr_heq (by simp [Nat.add_assoc]) ih

lemma bottEmbedIter_comm_heq {n : ℕ} (a b : ℕ) (X : ClTower A n) :
    HEq (bottEmbedIter (a + b) X) (bottEmbedIter (b + a) X) := by
  have h : a + b = b + a := Nat.add_comm a b
  rw [h]

/-- Directed colimit equivalence relation on $\Sigma\, n : \mathbb{N},\, \mathcal{C}\ell_n(A)$. -/
def ClInfRel (u v : Σ n : ℕ, ClTower A n) : Prop :=
  ∃ (k₁ k₂ : ℕ), u.1 + k₁ = v.1 + k₂ ∧
    HEq (bottEmbedIter k₁ u.2) (bottEmbedIter k₂ v.2)

theorem clInfRel_trans {u v w : Σ n : ℕ, ClTower A n}
    (huv : ClInfRel u v) (hvw : ClInfRel v w) : ClInfRel u w := by
  rcases huv with ⟨k₁, k₂, h12, heq12⟩
  rcases hvw with ⟨l₁, l₂, h23, heq23⟩
  refine ⟨k₁ + l₁, l₂ + k₂, by omega, ?_⟩
  exact (bottEmbedIter_add_heq k₁ l₁ u.2).trans <|
    (bottEmbedIter_congr_heq l₁ h12 heq12).trans <|
    (bottEmbedIter_add_heq k₂ l₁ v.2).symm.trans <|
    (bottEmbedIter_comm_heq k₂ l₁ v.2).trans <|
    (bottEmbedIter_add_heq l₁ k₂ v.2).trans <|
    (bottEmbedIter_congr_heq k₂ h23 heq23).trans <|
    (bottEmbedIter_add_heq l₂ k₂ w.2).symm

/-- Certified `Setoid` instance for the inductive colimit $\mathcal{C}\ell(\infty, \infty)$. -/
instance clInfSetoid (A : Type u) [Ring A] : Setoid (Σ n : ℕ, ClTower A n) where
  r := ClInfRel
  iseqv := {
    refl  := fun _ => ⟨0, 0, rfl, HEq.rfl⟩
    symm  := fun ⟨k₁, k₂, h, heq⟩ => ⟨k₂, k₁, h.symm, heq.symm⟩
    trans := clInfRel_trans
  }

/-- The universal colimit quotient type $\mathcal{C}\ell_\infty(A) = \mathrm{Quotient}(\mathrm{clInfSetoid}\;A)$. -/
abbrev ClInf (A : Type u) [Ring A] := Quotient (clInfSetoid A)

/-- Canonical colimit cocone injection $\pi_\infty(n, X) \in \mathcal{C}\ell_\infty(A)$. -/
def toClInf (n : ℕ) (X : ClTower A n) : ClInf A :=
  Quotient.mk (clInfSetoid A) ⟨n, X⟩

lemma superTrace_eq_of_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    superTrace X = superTrace Y := by
  subst h_dim; cases eq_of_heq h_heq; rfl

theorem clInf_superTrace_well_defined
    (u v : Σ n : ℕ, ClTower A n) (h_rel : ClInfRel u v) :
    superTrace u.2 = superTrace v.2 := by
  rcases h_rel with ⟨k₁, k₂, h_dim, h_heq⟩
  calc superTrace u.2
    _ = superTrace (bottEmbedIter k₁ u.2) := (colimit_superTrace_iter_invariant k₁ u.2).symm
    _ = superTrace (bottEmbedIter k₂ v.2) := superTrace_eq_of_heq h_dim h_heq
    _ = superTrace v.2                    := colimit_superTrace_iter_invariant k₂ v.2

/-- The quotient-lifted Atiyah–Singer supertrace $\mathrm{Str}_\infty : \mathcal{C}\ell_\infty(A) \to A$. -/
def clInfSuperTrace : ClInf A → A :=
  Quotient.lift (fun u => superTrace u.2) clInf_superTrace_well_defined

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => bottEmbed (cantorProj n)

/-- **Universal Quotient Colimit Stabilization Theorem ($\mathcal{C}\mathcal{L}_1$ & $\mathcal{C}\mathcal{L}_2$)**:
1. $\pi_\infty(n + 1, \iota_{\mathrm{Bott}}(X)) = \pi_\infty(n, X)$,
2. All Cantor vacuum projections $\Pi_{\mathcal{C}_n}$ map to the same universal vacuum $\pi_\infty(0, 1_A)$,
3. $\mathrm{Str}_\infty(\pi_\infty(n, \Pi_{\mathcal{C}_n})) = 1_A$ for all $n \in \mathbb{N}$. -/
theorem clInf_vacuum_stabilization_and_supertrace (n : ℕ) (X : ClTower A n) :
    toClInf (n + 1) (bottEmbed X) = toClInf n X ∧
    toClInf n (cantorProj n) = toClInf 0 (1 : A) ∧
    clInfSuperTrace (toClInf n (cantorProj (A := A) n)) = (1 : A) := by
  have h_step : ∀ (m : ℕ) (Y : ClTower A m), toClInf (m + 1) (bottEmbed Y) = toClInf m Y := by
    intro m Y
    apply Quotient.sound
    exact ⟨0, 1, rfl, HEq.rfl⟩
  have h_vac : ∀ (m : ℕ), toClInf m (cantorProj (A := A) m) = toClInf 0 (1 : A) := by
    intro m; induction' m with m ih
    · rfl
    · dsimp [cantorProj]; rw [h_step m (cantorProj m), ih]
  refine ⟨h_step n X, h_vac n, ?_⟩
  rw [h_vac n]
  dsimp [clInfSuperTrace, toClInf, superTrace, chiralityOp, towerTrace]
  exact mul_one 1

end ArchetypeCL1_CL2_ColimitSetoidAndQuotient

/-!
## Archetype $\mathcal{C}\mathcal{L}_3$: Noncommutative Mass Gap Operator $\Delta_n(m_0)$ & Colimit Stability
-/

section ArchetypeCL3_NoncommutativeMassGapOperator

/-- Unital diagonal embedding $\iota_{\mathrm{diag}}^{(n)} : A \to \mathcal{C}\ell_n(A)$ of a mass operator $m_0 \in A$. -/
def towerScalar : ∀ (n : ℕ), A → ClTower A n
  | 0,     a => a
  | n + 1, a => mat2 (towerScalar n a) 0 0 (towerScalar n a)

lemma towerScalar_mul (n : ℕ) (a b : A) :
    towerScalar n (a * b) = towerScalar n a * towerScalar n b := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, ih]

lemma towerScalar_comm_cantorProj (n : ℕ) (m₀ : A) :
    towerScalar n m₀ * cantorProj n = cantorProj n * towerScalar n m₀ := by
  induction' n with m ih
  · dsimp [towerScalar, cantorProj]; rw [mul_one, one_mul]
  · apply ext_fin2 <;> simp [towerScalar, cantorProj, bottEmbed, ih]

lemma towerScalar_bottEmbed (n : ℕ) (m₀ : A) (X : ClTower A n) :
    towerScalar (n + 1) m₀ * bottEmbed X = bottEmbed (towerScalar n m₀ * X) := by
  apply ext_fin2 <;> simp [towerScalar, bottEmbed]

lemma cantorProj_idem : ∀ (n : ℕ), cantorProj n * cantorProj n = (cantorProj n : ClTower A n)
  | 0     => mul_one 1
  | n + 1 => by dsimp [cantorProj]; rw [← bottEmbed_mul, cantorProj_idem n]

/-- Noncommutative mass gap operator $\Delta_n(m_0) = \iota_{\mathrm{diag}}^{(n)}(m_0)(1 - \Pi_{\mathcal{C}_n}) \in \mathcal{C}\ell_n(A)$. -/
def massGapOp (m₀ : A) (n : ℕ) : ClTower A n :=
  towerScalar n m₀ * (1 - cantorProj n)

/-- **Two-Sided Vacuum Annihilation, Excited Coercivity & Colimit Stability ($\mathcal{C}\mathcal{L}_3$)**:
For any mass operator $m_0 \in A$ and scale $n \in \mathbb{N}$:
1. $\Delta_n(m_0) \Pi_{\mathcal{C}_n} = 0$ and $\Pi_{\mathcal{C}_n} \Delta_n(m_0) = 0$,
2. If $\Pi_{\mathcal{C}_n} \Psi = 0$, then $\Delta_n(m_0) \Psi = \iota_{\mathrm{diag}}^{(n)}(m_0) \Psi$,
3. If $\Pi_{\mathcal{C}_n} \Psi = 0$, then $\Delta_{n+1}(m_0)\,\iota_{\mathrm{Bott}}(\Psi) = \iota_{\mathrm{Bott}}(\Delta_n(m_0)\Psi)$. -/
theorem massGap_vacuum_annihilation_coercivity_and_colimit_stability
    (m₀ : A) (n : ℕ) (Ψ : ClTower A n) (h_orth : cantorProj n * Ψ = 0) :
    massGapOp m₀ n * cantorProj n = 0 ∧
    cantorProj n * massGapOp m₀ n = 0 ∧
    massGapOp m₀ n * Ψ = towerScalar n m₀ * Ψ ∧
    massGapOp m₀ (n + 1) * bottEmbed Ψ = bottEmbed (massGapOp m₀ n * Ψ) := by
  have hP := cantorProj_idem (A := A) n
  have h_coercive : ∀ {k : ℕ} (Φ : ClTower A k),
      cantorProj k * Φ = 0 → massGapOp m₀ k * Φ = towerScalar k m₀ * Φ := by
    intro k Φ hΦ
    dsimp [massGapOp]
    calc towerScalar k m₀ * (1 - cantorProj k) * Φ
      _ = towerScalar k m₀ * Φ - towerScalar k m₀ * (cantorProj k * Φ) := by noncomm_ring
      _ = towerScalar k m₀ * Φ := by rw [hΦ, mul_zero, sub_zero]
  have h_orth_next : cantorProj (n + 1) * bottEmbed Ψ = 0 := by
    dsimp [cantorProj]
    rw [← bottEmbed_mul, h_orth]
    apply ext_fin2 <;> rfl
  refine ⟨?_, ?_, h_coercive Ψ h_orth, ?_⟩
  · dsimp [massGapOp]
    calc towerScalar n m₀ * (1 - cantorProj n) * cantorProj n
      _ = towerScalar n m₀ * (cantorProj n - cantorProj n * cantorProj n) := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, mul_zero]
  · dsimp [massGapOp]
    calc cantorProj n * (towerScalar n m₀ * (1 - cantorProj n))
      _ = (cantorProj n * towerScalar n m₀) * (1 - cantorProj n) := by noncomm_ring
      _ = (towerScalar n m₀ * cantorProj n) * (1 - cantorProj n) := by
          rw [← towerScalar_comm_cantorProj n m₀]
      _ = towerScalar n m₀ * (cantorProj n - cantorProj n * cantorProj n) := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, mul_zero]
  · rw [h_coercive (bottEmbed Ψ) h_orth_next, h_coercive Ψ h_orth, towerScalar_bottEmbed]

end ArchetypeCL3_NoncommutativeMassGapOperator

/-!
## Archetype $\mathcal{C}\mathcal{L}_4$: Metriplectic Double-Commutator Lindblad Dissipator & Quadratic Mass-Gap Damping
-/

section ArchetypeCL4_MetriplecticLindbladMassGapDamping

/-- The Metriplectic Double-Commutator Lindblad Dissipator $\mathcal{D}_{\mathrm{Lind}}(H, \rho) = -\⁅H, \⁅H, \rho⁆⁆$. -/
def lindbladDissipator {R : Type*} [Ring R] (H ρ : R) : R :=
  -⁅H, ⁅H, ρ⁆⁆

/-- Off-diagonal vacuum-to-excited transition coherence $\Psi_{\mathrm{coh}}(X) = (1 - \Pi_{\mathcal{C}_n}) X \Pi_{\mathcal{C}_n}$. -/
def coherenceMode (n : ℕ) (X : ClTower A n) : ClTower A n :=
  (1 - cantorProj n) * X * cantorProj n

/-- **Metriplectic Lindblad GKSL Normal Form, Quadratic Mass-Gap Damping & Colimit Stability ($\mathcal{C}\mathcal{L}_4$)**:
1. *GKSL Normal Form*: $-\⁅H, \⁅H, \rho⁆⁆ = 2 \bullet (H \rho H) - (H^2 \rho + \rho H^2)$,
2. *Decoherence-Free Vacuum*: $\mathcal{D}_{\mathrm{Lind}}(\Delta_n(m_0), \Pi_{\mathcal{C}_n}) = 0$,
3. *Quadratic Mass-Gap Damping*: On any transition coherence $\Psi_{\mathrm{coh}}(X) = (1 - \Pi_{\mathcal{C}_n}) X \Pi_{\mathcal{C}_n}$,
   $\mathcal{D}_{\mathrm{Lind}}(\Delta_n(m_0), \Psi_{\mathrm{coh}}(X)) = -\iota_{\mathrm{diag}}^{(n)}(m_0^2)\,\Psi_{\mathrm{coh}}(X)$,
4. *Colimit Stability of Lindblad Damping*:
   $\mathcal{D}_{\mathrm{Lind}}(\Delta_{n+1}(m_0), \iota_{\mathrm{Bott}}(\Psi_{\mathrm{coh}}(X))) =
    \iota_{\mathrm{Bott}}(\mathcal{D}_{\mathrm{Lind}}(\Delta_n(m_0), \Psi_{\mathrm{coh}}(X)))$. -/
theorem lindblad_mass_gap_damping_and_colimit_stability
    (m₀ : A) (n : ℕ) (H ρ X : ClTower A n) :
    let Δ_n   := massGapOp m₀ n
    let Δ_n1  := massGapOp m₀ (n + 1)
    let Ψ_coh := coherenceMode n X
    lindbladDissipator H ρ = 2 • (H * ρ * H) - (H * H * ρ + ρ * (H * H)) ∧
    lindbladDissipator Δ_n (cantorProj n) = 0 ∧
    lindbladDissipator Δ_n Ψ_coh = -(towerScalar n (m₀ * m₀) * Ψ_coh) ∧
    lindbladDissipator Δ_n1 (bottEmbed Ψ_coh) =
      bottEmbed (lindbladDissipator Δ_n Ψ_coh) := by
  intro Δ_n Δ_n1 Ψ_coh
  have hP := cantorProj_idem (A := A) n
  have h_orth : cantorProj n * Ψ_coh = 0 := by
    dsimp [Ψ_coh, coherenceMode]
    calc cantorProj n * ((1 - cantorProj n) * X * cantorProj n)
      _ = (cantorProj n - cantorProj n * cantorProj n) * X * cantorProj n := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, zero_mul, zero_mul]
  rcases massGap_vacuum_annihilation_coercivity_and_colimit_stability m₀ n Ψ_coh h_orth with
    ⟨h_ann_R, h_ann_L, h_coer, _⟩
  have h_right_zero : ∀ (Y : ClTower A n), Y * cantorProj n * Δ_n = 0 := by
    intro Y
    calc Y * cantorProj n * Δ_n = Y * (cantorProj n * Δ_n) := by noncomm_ring
      _ = 0 := by rw [h_ann_L, mul_zero]
  have h_comm1 : ⁅Δ_n, Ψ_coh⁆ = towerScalar n m₀ * Ψ_coh := by
    rw [Ring.lie_def, h_coer]
    have hR : Ψ_coh * Δ_n = 0 := h_right_zero ((1 - cantorProj n) * X)
    rw [hR, sub_zero]
  have h_comm2 : ⁅Δ_n, towerScalar n m₀ * Ψ_coh⁆ = towerScalar n (m₀ * m₀) * Ψ_coh := by
    rw [Ring.lie_def]
    have h_orth2 : cantorProj n * (towerScalar n m₀ * Ψ_coh) = 0 := by
      calc cantorProj n * (towerScalar n m₀ * Ψ_coh)
        _ = (cantorProj n * towerScalar n m₀) * Ψ_coh := by noncomm_ring
        _ = (towerScalar n m₀ * cantorProj n) * Ψ_coh := by
            rw [← towerScalar_comm_cantorProj n m₀]
        _ = towerScalar n m₀ * (cantorProj n * Ψ_coh) := by noncomm_ring
        _ = 0 := by rw [h_orth, mul_zero]
    have hL2 := (massGap_vacuum_annihilation_coercivity_and_colimit_stability
      m₀ n (towerScalar n m₀ * Ψ_coh) h_orth2).2.2.1
    have hR2 : (towerScalar n m₀ * Ψ_coh) * Δ_n = 0 := by
      dsimp [Ψ_coh, coherenceMode]
      calc (towerScalar n m₀ * ((1 - cantorProj n) * X * cantorProj n)) * Δ_n
        _ = (towerScalar n m₀ * ((1 - cantorProj n) * X)) * (cantorProj n * Δ_n) := by
            noncomm_ring
        _ = 0 := by rw [h_ann_L, mul_zero]
    rw [hL2, hR2, sub_zero, ← mul_assoc, ← towerScalar_mul]
  have h_damping : lindbladDissipator Δ_n Ψ_coh = -(towerScalar n (m₀ * m₀) * Ψ_coh) := by
    dsimp [lindbladDissipator]
    rw [h_comm1, h_comm2]
  refine ⟨?_, ?_, h_damping, ?_⟩
  · dsimp [lindbladDissipator]
    simp only [Ring.lie_def, two_smul]
    noncomm_ring
  · dsimp [lindbladDissipator]
    have h_vac_comm : ⁅Δ_n, cantorProj n⁆ = (0 : ClTower A n) := by
      rw [Ring.lie_def, h_ann_R, h_ann_L, sub_self]
    rw [h_vac_comm, Ring.lie_def, mul_zero, zero_mul, sub_self, neg_zero]
  · rw [h_damping]
    have h_neg_emb : bottEmbed (-(towerScalar n (m₀ * m₀) * Ψ_coh)) =
        -(towerScalar (n + 1) (m₀ * m₀) * bottEmbed Ψ_coh) := by
      rw [towerScalar_bottEmbed]
      apply ext_fin2 <;> simp [bottEmbed]
    rw [h_neg_emb]
    have h_orth_b : cantorProj (n + 1) * bottEmbed Ψ_coh = 0 := by
      dsimp [cantorProj]; rw [← bottEmbed_mul, h_orth]; apply ext_fin2 <;> simp [bottEmbed]
    have h_R_b : bottEmbed Ψ_coh * cantorProj (n + 1) = bottEmbed Ψ_coh := by
      dsimp [cantorProj]; rw [← bottEmbed_mul]
      have h_id : Ψ_coh * cantorProj n = Ψ_coh := by
        dsimp [Ψ_coh, coherenceMode]
        calc (1 - cantorProj n) * X * cantorProj n * cantorProj n
          _ = (1 - cantorProj n) * X * (cantorProj n * cantorProj n) := by noncomm_ring
          _ = Ψ_coh := by rw [hP]; rfl
      rw [h_id]
    rcases massGap_vacuum_annihilation_coercivity_and_colimit_stability
      m₀ (n + 1) (bottEmbed Ψ_coh) h_orth_b with ⟨_, h_ann_L1, h_coer1, _⟩
    have h_c1 : ⁅Δ_n1, bottEmbed Ψ_coh⁆ = towerScalar (n + 1) m₀ * bottEmbed Ψ_coh := by
      rw [Ring.lie_def, h_coer1]
      have hR1 : bottEmbed Ψ_coh * Δ_n1 = 0 := by
        calc bottEmbed Ψ_coh * Δ_n1 = (bottEmbed Ψ_coh * cantorProj (n + 1)) * Δ_n1 := by
              rw [h_R_b]
          _ = bottEmbed Ψ_coh * (cantorProj (n + 1) * Δ_n1) := by noncomm_ring
          _ = 0 := by rw [h_ann_L1, mul_zero]
      rw [hR1, sub_zero]
    have h_c2 : ⁅Δ_n1, towerScalar (n + 1) m₀ * bottEmbed Ψ_coh⁆ =
        towerScalar (n + 1) (m₀ * m₀) * bottEmbed Ψ_coh := by
      rw [towerScalar_bottEmbed, Ring.lie_def]
      have h_orth2 : cantorProj n * (towerScalar n m₀ * Ψ_coh) = 0 := by
        calc cantorProj n * (towerScalar n m₀ * Ψ_coh)
          _ = (cantorProj n * towerScalar n m₀) * Ψ_coh := by noncomm_ring
          _ = (towerScalar n m₀ * cantorProj n) * Ψ_coh := by
              rw [← towerScalar_comm_cantorProj n m₀]
          _ = towerScalar n m₀ * (cantorProj n * Ψ_coh) := by noncomm_ring
          _ = 0 := by rw [h_orth, mul_zero]
      have hL2 := (massGap_vacuum_annihilation_coercivity_and_colimit_stability
        m₀ n (towerScalar n m₀ * Ψ_coh) h_orth2).2.2.2
      have hL2_eval := (massGap_vacuum_annihilation_coercivity_and_colimit_stability
        m₀ n (towerScalar n m₀ * Ψ_coh) h_orth2).2.2.1
      have hR2 : bottEmbed (towerScalar n m₀ * Ψ_coh) * Δ_n1 = 0 := by
        have h_id2 : bottEmbed (towerScalar n m₀ * Ψ_coh) * cantorProj (n + 1) =
            bottEmbed (towerScalar n m₀ * Ψ_coh) := by
          rw [← towerScalar_bottEmbed, mul_assoc, h_R_b]
        calc bottEmbed (towerScalar n m₀ * Ψ_coh) * Δ_n1
          _ = (bottEmbed (towerScalar n m₀ * Ψ_coh) * cantorProj (n + 1)) * Δ_n1 := by
              rw [h_id2]
          _ = bottEmbed (towerScalar n m₀ * Ψ_coh) * (cantorProj (n + 1) * Δ_n1) := by
              noncomm_ring
          _ = 0 := by rw [h_ann_L1, mul_zero]
      rw [hL2, hL2_eval, hR2, sub_zero, ← mul_assoc, ← towerScalar_mul, towerScalar_bottEmbed]
    dsimp [lindbladDissipator]
    rw [h_c1, h_c2]

end ArchetypeCL4_MetriplecticLindbladMassGapDamping

end InfoGeometry.Algebra.NoncommutativeCliffordColimitMassGapSynthesis
