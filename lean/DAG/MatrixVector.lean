import DAG.TwoComplex
import DAG.GraphHodge
import DAG.LaplacianRank
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix-Vector Operations — Genuine proofs, 0 sorries

Built on `LaplacianRank.dotProduct` and its positivity lemmas.
All theorems are fully proved using the Euclidean dot product technique:
  ‖x‖² = Σ x_i² = 0 ↔ x = 0 over ℚ.
-/

open Matrix

namespace DAG.MatrixVector

/-! ## Boundary operators as Matrices -/

/-- Boundary operator ∂₁ as Matrix (edges × vertices). -/
def boundary1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin tc.edges.size) (Fin tc.base.toGraph.nodes.size) ℚ :=
  λ i j =>
    let (u, v) := tc.edges[i.val]
    if j.val = u then (-1 : ℚ) else if j.val = v then 1 else 0

/-- Boundary operator ∂₂ as Matrix (faces × edges). -/
def boundary2 {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin (tc.faces.size + tc.digons.size)) (Fin tc.edges.size) ℚ :=
  λ i j =>
    if h : i.val < tc.faces.size then
      let (e1, e2, e3) := tc.faces[i.val]
      if j.val = e1 then 1 else if j.val = e2 then 1 else if j.val = e3 then (-1) else 0
    else
      let (eU, eV) := tc.digons[i.val - tc.faces.size]
      if j.val = eU then 1 else if j.val = eV then 1 else 0

/-- Hodge Laplacian Δ₁ = ∂₁∂₁ᵀ + ∂₂ᵀ∂₂. -/
def laplacian1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin tc.edges.size) (Fin tc.edges.size) ℚ :=
  let ∂₁ := boundary1 tc
  let ∂₂ := boundary2 tc
  ∂₁ * ∂₁ᵀ + ∂₂ᵀ * ∂₂

/-! ## Quadratic form helper — uses `LaplacianRank.dotProduct` -/

open DAG.LaplacianRank

/-- Quadratic form: q_A(x) = ⟨x, A·x⟩. -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ :=
  dotProduct x (A.mulVec x)

/-- vᵀ(AᵀA)v = ‖A·v‖² ≥ 0. -/
lemma quadForm_transpose_mul_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ) :
    0 ≤ quadForm (Aᵀ * A) x := by
  dsimp [quadForm]
  rw [Matrix.mulVec_mulVec]
  rw [dotProduct_transpose_mulVec_eq (A := Aᵀ) (m := n) (n := m) x (A.mulVec x)]
  simp
  exact dotProduct_self_nonneg (A.mulVec x)

/-- vᵀ(AᵀA)v = 0 → A·v = 0. Follows from ‖A·v‖² = 0. -/
lemma quadForm_zero_implies_matVecMul_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ)
    (h : quadForm (Aᵀ * A) x = 0) : A.mulVec x = 0 := by
  dsimp [quadForm] at h
  rw [Matrix.mulVec_mulVec] at h
  rw [dotProduct_transpose_mulVec_eq (A := Aᵀ) (m := n) (n := m) x (A.mulVec x)] at h
  simp at h
  exact (dotProduct_self_eq_zero_iff (A.mulVec x)).mp h

/-! ## Laplacian positive semidefiniteness -/

/-- Δ₁ = ∂₁∂₁ᵀ + ∂₂ᵀ∂₂ is PSD: ψᵀΔ₁ψ = ‖∂₁ᵀψ‖² + ‖∂₂ψ‖² ≥ 0. -/
lemma laplacian_quadForm_nonneg {α} [BEq α] [Hashable α]
    (tc : TwoComplex α) (ψ : Fin tc.edges.size → ℚ) :
    0 ≤ quadForm (laplacian1 tc) ψ := by
  let ∂₁ := boundary1 tc
  let ∂₂ := boundary2 tc
  have h_expand : quadForm (laplacian1 tc) ψ =
      dotProduct (∂₁ᵀ.mulVec ψ) (∂₁ᵀ.mulVec ψ) + dotProduct (∂₂.mulVec ψ) (∂₂.mulVec ψ) := by
    dsimp [laplacian1, quadForm]
    simp [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.mulVec_mulVec,
      dotProduct_transpose_mulVec_eq ∂₁ ψ (∂₁ᵀ.mulVec ψ),
      dotProduct_transpose_mulVec_eq (A := ∂₂ᵀ) (m := tc.edges.size) (n := tc.faces.size + tc.digons.size) ψ (∂₂.mulVec ψ)]
  rw [h_expand]
  nlinarith [dotProduct_self_nonneg (∂₁ᵀ.mulVec ψ), dotProduct_self_nonneg (∂₂.mulVec ψ)]

/-- Δ₁·ψ = 0 ⇒ ∂₁ᵀ·ψ = 0 ∧ ∂₂·ψ = 0.
    Sum of nonnegative terms = 0 ⇒ each term = 0. -/
lemma laplacian_zero_implies_boundary_zero {α} [BEq α] [Hashable α]
    (tc : TwoComplex α) (ψ : Fin tc.edges.size → ℚ)
    (h : (laplacian1 tc).mulVec ψ = 0) :
    (boundary1 tc)ᵀ.mulVec ψ = 0 ∧ (boundary2 tc).mulVec ψ = 0 := by
  let ∂₁ := boundary1 tc
  let ∂₂ := boundary2 tc
  have h_quad : quadForm (laplacian1 tc) ψ = 0 := by
    dsimp [quadForm]; rw [h]; simp [dotProduct]
  have h_expand : quadForm (laplacian1 tc) ψ =
      dotProduct (∂₁ᵀ.mulVec ψ) (∂₁ᵀ.mulVec ψ) + dotProduct (∂₂.mulVec ψ) (∂₂.mulVec ψ) := by
    dsimp [laplacian1, quadForm]
    simp [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.mulVec_mulVec,
      dotProduct_transpose_mulVec_eq ∂₁ ψ (∂₁ᵀ.mulVec ψ),
      dotProduct_transpose_mulVec_eq (A := ∂₂ᵀ) (m := tc.edges.size) (n := tc.faces.size + tc.digons.size) ψ (∂₂.mulVec ψ)]
  rw [h_expand] at h_quad
  have h_nonneg1 : 0 ≤ dotProduct (∂₁ᵀ.mulVec ψ) (∂₁ᵀ.mulVec ψ) :=
    dotProduct_self_nonneg _
  have h_nonneg2 : 0 ≤ dotProduct (∂₂.mulVec ψ) (∂₂.mulVec ψ) :=
    dotProduct_self_nonneg _
  have h_zero1 : dotProduct (∂₁ᵀ.mulVec ψ) (∂₁ᵀ.mulVec ψ) = 0 := by nlinarith
  have h_zero2 : dotProduct (∂₂.mulVec ψ) (∂₂.mulVec ψ) = 0 := by nlinarith
  exact ⟨(dotProduct_self_eq_zero_iff _).mp h_zero1, (dotProduct_self_eq_zero_iff _).mp h_zero2⟩

/-! ## Eckmann's Discrete Hodge Theorem — fully proved, 0 sorries -/

/--
**Eckmann's Discrete Hodge Theorem.**

Given boundary matrices ∂₁, ∂₂ of a TwoComplex with ∂₂∂₁ = 0,
if rank(∂₁) + rank(∂₂) = n₁ (equivalently betti1 = 0), then the
Hodge Laplacian Δ₁ = ∂₁∂₁ᵀ + ∂₂ᵀ∂₂ has trivial kernel:
  Δ₁·ψ = 0 → ψ = 0.

Proof:
1. Δ₁·ψ = 0 → ∂₁ᵀ·ψ = 0 and ∂₂·ψ = 0 (PSD argument, lemma above)
2. Thus (∂₁∂₁ᵀ + ∂₂ᵀ∂₂)·ψ = 0 (by direct computation)
3. Full rank → trivial kernel (LaplacianRank.ker_trivial_when_full_rank)
-/
theorem eckmann_discrete_hodge
    {α : Type} [BEq α] [Hashable α]
    (tc : TwoComplex α)
    (h_boundary_sq : boundary2 tc * boundary1 tc = 0)
    (h_full : Matrix.rank (boundary1 tc) + Matrix.rank (boundary2 tc) = Fintype.card (Fin tc.edges.size))
    (ψ : Fin tc.edges.size → ℚ)
    (h_harmonic : (laplacian1 tc).mulVec ψ = 0) :
    ψ = 0 := by
  let ∂₁ := boundary1 tc
  let ∂₂ := boundary2 tc
  rcases laplacian_zero_implies_boundary_zero tc ψ h_harmonic with ⟨hAᵀ, hB⟩
  -- (∂₁∂₁ᵀ + ∂₂ᵀ∂₂)·ψ = ∂₁·(∂₁ᵀ·ψ) + ∂₂ᵀ·(∂₂·ψ) = 0 + 0 = 0
  have h_laplacian_mul : (∂₁ * ∂₁ᵀ + ∂₂ᵀ * ∂₂).mulVec ψ = 0 := by
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAᵀ, hB]
    simp [mulVec]
  exact LaplacianRank.ker_trivial_when_full_rank
    ∂₁ ∂₂ h_boundary_sq h_full ψ h_laplacian_mul

end DAG.MatrixVector
