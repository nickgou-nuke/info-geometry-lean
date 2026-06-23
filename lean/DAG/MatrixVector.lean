import DAG.TwoComplex
import DAG.GraphHodge
import DAG.LaplacianRank
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix-Vector Operations — Genuine proofs, 0 sorries

Built on `LaplacianRank.innerProduct` and its positivity lemmas.
All theorems are fully proved using the Euclidean dot product technique:
  ‖x‖² = Σ x_i² = 0 ↔ x = 0 over ℚ.
-/

open Matrix

namespace DAG.MatrixVector

/-! ## Boundary operators as Matrices -/

/-- Boundary operator d1 as Matrix (edges × vertices). -/
def boundary1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin tc.edges.size) (Fin tc.base.toGraph.nodes.size) ℚ :=
  λ i j =>
    let (u, v) := tc.edges[i.val]
    if j.val = u then (-1 : ℚ) else if j.val = v then 1 else 0

/-- Boundary operator d2 as Matrix (faces × edges). -/
def boundary2 {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin (tc.faces.size + tc.digons.size)) (Fin tc.edges.size) ℚ :=
  λ i j =>
    if h : i.val < tc.faces.size then
      let (e1, e2, e3) := tc.faces[i.val]
      if j.val = e1 then 1 else if j.val = e2 then 1 else if j.val = e3 then (-1) else 0
    else
      let (eU, eV) := tc.digons[i.val - tc.faces.size]
      if j.val = eU then 1 else if j.val = eV then 1 else 0

/-- Hodge Laplacian Δ₁ = d1*d1ᵀ + d2ᵀ*d2. -/
def laplacian1 {α} [BEq α] [Hashable α] (tc : TwoComplex α) :
    Matrix (Fin tc.edges.size) (Fin tc.edges.size) ℚ :=
  let d1 := boundary1 tc
  let d2 := boundary2 tc
  d1 * d1ᵀ + d2ᵀ * d2

/-! ## Quadratic form helper — uses `LaplacianRank.innerProduct` -/

open DAG.LaplacianRank

/-- Quadratic form: q_A(x) = ⟨x, A·x⟩. -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ :=
  innerProduct x (A.mulVec x)

/-- vᵀ(AᵀA)v = ‖A·v‖² ≥ 0. -/
lemma quadForm_transpose_mul_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ) :
    0 ≤ quadForm (Aᵀ * A) x := by
  dsimp [quadForm]
  rw [← Matrix.mulVec_mulVec]
  rw [innerProduct_transpose_mulVec_eq (A := Aᵀ) x (A.mulVec x)]
  simp
  exact innerProduct_self_nonneg (A.mulVec x)

/-- vᵀ(AᵀA)v = 0 → A·v = 0. Follows from ‖A·v‖² = 0. -/
lemma quadForm_zero_implies_matVecMul_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ)
    (h : quadForm (Aᵀ * A) x = 0) : A.mulVec x = 0 := by
  dsimp [quadForm] at h
  rw [← Matrix.mulVec_mulVec] at h
  rw [innerProduct_transpose_mulVec_eq (A := Aᵀ) x (A.mulVec x)] at h
  simp at h
  exact (innerProduct_self_eq_zero_iff (A.mulVec x)).mp h

/-! ## Laplacian positive semidefiniteness -/

/-- Δ₁ = d1*d1ᵀ + d2ᵀ*d2 is PSD: ψᵀΔ₁ψ = ‖d1ᵀψ‖² + ‖d2ψ‖² ≥ 0. -/
lemma laplacian_quadForm_nonneg {α} [BEq α] [Hashable α]
    (tc : TwoComplex α) (ψ : Fin tc.edges.size → ℚ) :
    0 ≤ quadForm (laplacian1 tc) ψ := by
  let d1 := boundary1 tc
  let d2 := boundary2 tc
  have h_expand : quadForm (laplacian1 tc) ψ =
      innerProduct (d1ᵀ.mulVec ψ) (d1ᵀ.mulVec ψ) + innerProduct (d2.mulVec ψ) (d2.mulVec ψ) := by
    dsimp [laplacian1, quadForm, d1, d2]
    simp [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, innerProduct_transpose_mulVec_eq]
  rw [h_expand]
  nlinarith [innerProduct_self_nonneg (d1ᵀ.mulVec ψ), innerProduct_self_nonneg (d2.mulVec ψ)]

/-- Δ₁·ψ = 0 ⇒ d1ᵀ·ψ = 0 ∧ d2·ψ = 0.
    Sum of nonnegative terms = 0 ⇒ each term = 0. -/
lemma laplacian_zero_implies_boundary_zero {α} [BEq α] [Hashable α]
    (tc : TwoComplex α) (ψ : Fin tc.edges.size → ℚ)
    (h : (laplacian1 tc).mulVec ψ = 0) :
    (boundary1 tc)ᵀ.mulVec ψ = 0 ∧ (boundary2 tc).mulVec ψ = 0 := by
  let d1 := boundary1 tc
  let d2 := boundary2 tc
  have h_quad : quadForm (laplacian1 tc) ψ = 0 := by
    dsimp [quadForm]; rw [h]; simp [innerProduct]
  have h_expand : quadForm (laplacian1 tc) ψ =
      innerProduct (d1ᵀ.mulVec ψ) (d1ᵀ.mulVec ψ) + innerProduct (d2.mulVec ψ) (d2.mulVec ψ) := by
    dsimp [laplacian1, quadForm, d1, d2]
    simp [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, innerProduct_transpose_mulVec_eq]
  rw [h_expand] at h_quad
  have h_nonneg1 : 0 ≤ innerProduct (d1ᵀ.mulVec ψ) (d1ᵀ.mulVec ψ) :=
    innerProduct_self_nonneg _
  have h_nonneg2 : 0 ≤ innerProduct (d2.mulVec ψ) (d2.mulVec ψ) :=
    innerProduct_self_nonneg _
  have h_zero1 : innerProduct (d1ᵀ.mulVec ψ) (d1ᵀ.mulVec ψ) = 0 := by nlinarith
  have h_zero2 : innerProduct (d2.mulVec ψ) (d2.mulVec ψ) = 0 := by nlinarith
  exact ⟨(innerProduct_self_eq_zero_iff _).mp h_zero1, (innerProduct_self_eq_zero_iff _).mp h_zero2⟩

/-! ## Eckmann's Discrete Hodge Theorem — fully proved, 0 sorries -/

/--
**Eckmann's Discrete Hodge Theorem.**

Given boundary matrices d1, d2 of a TwoComplex with d2*d1 = 0,
if rank(d1) + rank(d2) = n₁ (equivalently betti1 = 0), then the
Hodge Laplacian Δ₁ = d1*d1ᵀ + d2ᵀ*d2 has trivial kernel:
  Δ₁·ψ = 0 → ψ = 0.

Proof:
1. Δ₁·ψ = 0 → d1ᵀ·ψ = 0 and d2·ψ = 0 (PSD argument, lemma above)
2. Thus (d1*d1ᵀ + d2ᵀ*d2)·ψ = 0 (by direct computation)
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
  let d1 := boundary1 tc
  let d2 := boundary2 tc
  rcases laplacian_zero_implies_boundary_zero tc ψ h_harmonic with ⟨hA_tr, hB⟩
  -- (d1*d1ᵀ + d2ᵀ*d2)·ψ = d1·(d1ᵀ·ψ) + d2ᵀ·(d2·ψ) = 0 + 0 = 0
  have h_laplacian_mul : (d1 * d1ᵀ + d2ᵀ * d2).mulVec ψ = 0 := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA_tr, hB]
    simp [mulVec]
  exact LaplacianRank.ker_trivial_when_full_rank
    d1 d2 h_boundary_sq h_full ψ h_laplacian_mul

end DAG.MatrixVector
