/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Conformal.MannheimWeylKazanasCosmology
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.BilinearForm

set_option autoImplicit false

/-!
# Conformal Cartan Tractor Calculus (Algebraic Fiber Core, Features `A1–A7`)

Formalizes the BUCKET 1 algebraic `(d + 2)`-dimensional conformal Cartan / Thomas tractor fiber
calculus over `ℝ`:

- **A1 — Tractor Bundle Fiber & Metric `h_{IJ}`**:
  `(d + 2)`-dimensional index type `TractorIdx d := Unit ⊕ Fin d ⊕ Unit`, equivalence
  `tractorIdxEquiv d : TractorIdx d ≃ Fin (d + 2)`, concrete `d = 4` (`Fin 6`) matrix/vector
  specialization, sign-parameterized block metric `tractorMetricMatrix ε g` (`ε ^ 2 = 1`), and
  bilinear form `tractorMetricBilin ε g := (tractorMetricMatrix ε g).toBilin'`, with symmetry,
  determinant `-g.det`, explicit block inverse, quadratic expansion, hyperbolic `(1, -1)`
  orthogonal pair witnessing signature `(p + 1, q + 1)` extension, and compatibility with
  `MannheimWeylKazanasCosmology.conformalRescale`.
- **A2 — Normal Cartan Tractor Connection & Schouten Tensor (`d ≥ 3`)**:
  Schouten tensor `schoutenTensor`, trace `R / (2 * (d - 1))`, Einstein equivalence,
  Einstein-`Λ` scalar relation, normal connection matrix `normalConnectionMatrix` with general
  `g`-compatible spin connection `ω`, `h`-skew-symmetry (`h * Γ + Γᵀ * h = 0`), and exact `(1, 1)`
  block commutator cancellation of Schouten terms.
- **A3 & A4 — Scale Tractor `I^A` & Unipotent Gauge Fixing `exp(g₁)`**:
  Scale tractor `scaleTractor`, unitary specialization `unitaryScaleTractor` (and literal `T07`
  vector `unitaryScaleTractorT07`), nilpotent shift generator `nilpotentGaugeGen` (`N^3 = 0`,
  `h`-skew-symmetric), truncated exponential `expG1` (`det = 1`, abelian group law,
  `h`-orthogonality), and `σ ≠ 0` unitary gauge fixing via `weightDiag σ *ᵥ (expG1 ... *ᵥ I)`.
- **A5 — Algebraic Eastwood–Gover Equivalence (`∇^T I = 0 ↔` Einstein)**:
  1-jet covariant derivative `tractorCovDeriv`, unitary-gauge equivalence with Einstein Schouten /
  Ricci equations (`d ≥ 3`), algebraic contracted Bianchi lemma (`d ≥ 2`), and general nonvanishing
  scale (`σ ≠ 0`, `μ = g⁻¹ dσ`) equivalence with the trace-free almost-Einstein equation and
  rescaled Schouten tensor.
- **A6 — Tractor Norm Constancy & Cosmological Casimir**:
  Exact differential constancy identity `∂_a (h(I, I)) = 2 * h(I, ∇_a^T I)`, unitary norm
  evaluation, dS / Minkowski / AdS causal trichotomy, and `σ = 0` horizon norm `nᵀ g⁻¹ n`.
- **A7 — Gravitational Meissner Effect (Cotton & Bach Expulsion)**:
  Curvature operator `tractorCurvatureMatrix`, `h`-skew-symmetry, `Ω *ᵥ I = 0` characterization,
  unitary-gauge Cotton expulsion, algebraic Bach tensor expulsion `bachTensor = 0`, and concrete
  `d = 4` instantiation reusing `MannheimWeylKazanasCosmology.weylTensor4_trace_zero`.

## Sign Reconciliation & Scope Boundary

The source transcript uses `h(-1)` anti-diagonal corners alongside Gover's `-1/d (Δσ + P σ)` bottom
slot and `-κ²` vs `+2Λ / ((d - 1)(d - 2))` norm signs. Parameterizing by `ε : ℝ` with `ε ^ 2 = 1`
reconciles standard Bailey–Eastwood–Gover (`ε = +1`) and the transcript (`ε = -1`) cleanly while
also providing a standalone lemma for the literal `T07:428` contraction.

Global smooth manifold PDE prolongation (`A5` global PDE), Gover–Leitner zero-locus smoothness
(`A8`), the 4-way Master equivalence with BV / `EP₂` shear (`A9`), and GHP path-integral narratives
(`A10`) belong to BUCKET 2 / BUCKET 3 and are out of scope for this fiber-algebra module.
-/

noncomputable section

namespace InfoGeometry.Conformal.CartanTractorCalculus

open Matrix BigOperators
open InfoGeometry.Conformal.MannheimWeylKazanasCosmology

/-! ## Non-Commutativity Witnesses on Concrete Matrix Carriers (OpenGauss T16) -/

/-- Explicit `6 × 6` real matrix non-commutativity witness for the `d = 4` tractor carrier. -/
theorem tractor_mat6_noncomm_witness :
    ∃ A B : Matrix (Fin 6) (Fin 6) ℝ, A * B ≠ B * A := by
  let A : Matrix (Fin 6) (Fin 6) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 6) (Fin 6) ℝ := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 0 0) h
  simp only [A, B, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_six] at h00
  norm_num at h00

/-- Explicit `4 × 4` real matrix non-commutativity witness for concrete `d = 4` base carriers. -/
theorem tractor_mat4_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
  simp only [A, B, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four] at h00
  norm_num at h00

/-! ## Tractor Index & Carrier Equivalence (`d + 2` Dimensions) -/

/-- `(d + 2)`-dimensional tractor fiber index type: top (`Unit`), middle (`Fin d`), bottom (`Unit`). -/
abbrev TractorIdx (d : ℕ) : Type := Unit ⊕ Fin d ⊕ Unit

/-- Tractor fiber vector type `(σ, μ, ρ)` over `ℝ`. -/
abbrev TractorVec (d : ℕ) : Type := TractorIdx d → ℝ

/-- Tractor fiber endomorphism / bilinear-form matrix type over `ℝ`. -/
abbrev TractorMat (d : ℕ) : Type := Matrix (TractorIdx d) (TractorIdx d) ℝ

/-- Canonical equivalence between `TractorIdx d` and `Fin (d + 2)`. -/
def tractorIdxEquiv (d : ℕ) : TractorIdx d ≃ Fin (d + 2) where
  toFun
    | Sum.inl () => ⟨0, by omega⟩
    | Sum.inr (Sum.inl i) => ⟨i.1 + 1, by omega⟩
    | Sum.inr (Sum.inr ()) => ⟨d + 1, by omega⟩
  invFun k :=
    if hk0 : k.1 = 0 then Sum.inl ()
    else if hkd : k.1 = d + 1 then Sum.inr (Sum.inr ())
    else Sum.inr (Sum.inl ⟨k.1 - 1, by omega⟩)
  left_inv x := by
    rcases x with ⟨⟩ | (i | ⟨⟩)
    · simp
    · have hid : i.1 ≠ d := i.isLt.ne
      simp [hid]
    · simp
  right_inv k := by
    ext; dsimp
    split_ifs with h1 h2
    · simp [h1]
    · simp [h2]
    · simp; omega

/-- Construct a tractor vector from top scale `σ`, middle tangent vector `μ`, and bottom slot `ρ`. -/
def tractorVec {d : ℕ} (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) : TractorVec d
  | Sum.inl _ => σ
  | Sum.inr (Sum.inl a) => μ a
  | Sum.inr (Sum.inr _) => ρ

/-- Top scale slot of a tractor vector. -/
def tractorTop {d : ℕ} (v : TractorVec d) : ℝ := v (Sum.inl ())

/-- Middle tangent slot of a tractor vector. -/
def tractorMid {d : ℕ} (v : TractorVec d) : Fin d → ℝ := fun a => v (Sum.inr (Sum.inl a))

/-- Bottom slot of a tractor vector. -/
def tractorBot {d : ℕ} (v : TractorVec d) : ℝ := v (Sum.inr (Sum.inr ()))

@[simp]
theorem tractorVec_inl {d : ℕ} (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) (u : Unit) :
    tractorVec σ μ ρ (Sum.inl u) = σ := rfl

@[simp]
theorem tractorVec_mid {d : ℕ} (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) (a : Fin d) :
    tractorVec σ μ ρ (Sum.inr (Sum.inl a)) = μ a := rfl

@[simp]
theorem tractorVec_inr {d : ℕ} (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) (u : Unit) :
    tractorVec σ μ ρ (Sum.inr (Sum.inr u)) = ρ := rfl

@[simp]
theorem tractorTop_tractorVec {d : ℕ} (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) :
    tractorTop (tractorVec σ μ ρ) = σ := rfl

@[simp]
theorem tractorMid_tractorVec {d : ℕ} (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) :
    tractorMid (tractorVec σ μ ρ) = μ := rfl

@[simp]
theorem tractorBot_tractorVec {d : ℕ} (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) :
    tractorBot (tractorVec σ μ ρ) = ρ := rfl

theorem tractorVec_eta {d : ℕ} (v : TractorVec d) :
    tractorVec (tractorTop v) (tractorMid v) (tractorBot v) = v := by
  funext i
  rcases i with ⟨⟩ | (a | ⟨⟩) <;> rfl

theorem tractorVec_eq_iff {d : ℕ} (σ₁ σ₂ ρ₁ ρ₂ : ℝ) (μ₁ μ₂ : Fin d → ℝ) :
    tractorVec σ₁ μ₁ ρ₁ = tractorVec σ₂ μ₂ ρ₂ ↔ σ₁ = σ₂ ∧ μ₁ = μ₂ ∧ ρ₁ = ρ₂ := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact congrFun h (Sum.inl ())
    · funext a; exact congrFun h (Sum.inr (Sum.inl a))
    · exact congrFun h (Sum.inr (Sum.inr ()))
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- Concrete `d = 4` specialization of a tractor matrix to `Matrix (Fin 6) (Fin 6) ℝ`. -/
def tractorMatToFin6 (M : TractorMat 4) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.reindex (tractorIdxEquiv 4) (tractorIdxEquiv 4) M

/-- Concrete `d = 4` specialization of a tractor vector to `Fin 6 → ℝ`. -/
def tractorVecToFin6 (v : TractorVec 4) : Fin 6 → ℝ :=
  fun i => v ((tractorIdxEquiv 4).symm i)

theorem tractorMatToFin6_mul (A B : TractorMat 4) :
    tractorMatToFin6 (A * B) = tractorMatToFin6 A * tractorMatToFin6 B := by
  ext i j
  simp only [tractorMatToFin6, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← (tractorIdxEquiv 4).symm.sum_comp]

theorem tractorMatToFin6_mulVec (M : TractorMat 4) (v : TractorVec 4) :
    tractorMatToFin6 M *ᵥ tractorVecToFin6 v = tractorVecToFin6 (M *ᵥ v) := by
  ext i
  simp only [tractorMatToFin6, tractorVecToFin6, Matrix.reindex_apply, Matrix.mulVec,
    dotProduct, Matrix.submatrix_apply]
  rw [← (tractorIdxEquiv 4).symm.sum_comp]

/-- Assemble a `3 × 3` block tractor matrix on `Unit ⊕ Fin d ⊕ Unit`. -/
def tractorBlockMat {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) :
    TractorMat d :=
  Matrix.of fun i j =>
    match i, j with
    | Sum.inl _, Sum.inl _ => m00
    | Sum.inl _, Sum.inr (Sum.inl b) => m01 b
    | Sum.inl _, Sum.inr (Sum.inr _) => m02
    | Sum.inr (Sum.inl a), Sum.inl _ => m10 a
    | Sum.inr (Sum.inl a), Sum.inr (Sum.inl b) => m11 a b
    | Sum.inr (Sum.inl a), Sum.inr (Sum.inr _) => m12 a
    | Sum.inr (Sum.inr _), Sum.inl _ => m20
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inl b) => m21 b
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => m22

@[simp]
theorem tractorBlockMat_inl_inl {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) (u₁ u₂ : Unit) :
    tractorBlockMat m00 m01 m02 m10 m11 m12 m20 m21 m22 (Sum.inl u₁) (Sum.inl u₂) = m00 := rfl

@[simp]
theorem tractorBlockMat_inl_mid {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) (u : Unit) (b : Fin d) :
    tractorBlockMat m00 m01 m02 m10 m11 m12 m20 m21 m22 (Sum.inl u) (Sum.inr (Sum.inl b)) =
      m01 b := rfl

@[simp]
theorem tractorBlockMat_inl_inr {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) (u₁ u₂ : Unit) :
    tractorBlockMat m00 m01 m02 m10 m11 m12 m20 m21 m22 (Sum.inl u₁) (Sum.inr (Sum.inr u₂)) =
      m02 := rfl

@[simp]
theorem tractorBlockMat_mid_inl {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) (a : Fin d) (u : Unit) :
    tractorBlockMat m00 m01 m02 m10 m11 m12 m20 m21 m22 (Sum.inr (Sum.inl a)) (Sum.inl u) =
      m10 a := rfl

@[simp]
theorem tractorBlockMat_mid_mid {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) (a b : Fin d) :
    tractorBlockMat m00 m01 m02 m10 m11 m12 m20 m21 m22
        (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) = m11 a b := rfl

@[simp]
theorem tractorBlockMat_mid_inr {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) (a : Fin d) (u : Unit) :
    tractorBlockMat m00 m01 m02 m10 m11 m12 m20 m21 m22
        (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr u)) = m12 a := rfl

@[simp]
theorem tractorBlockMat_inr_inl {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) (u₁ u₂ : Unit) :
    tractorBlockMat m00 m01 m02 m10 m11 m12 m20 m21 m22
        (Sum.inr (Sum.inr u₁)) (Sum.inl u₂) = m20 := rfl

@[simp]
theorem tractorBlockMat_inr_mid {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) (u : Unit) (b : Fin d) :
    tractorBlockMat m00 m01 m02 m10 m11 m12 m20 m21 m22
        (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inl b)) = m21 b := rfl

@[simp]
theorem tractorBlockMat_inr_inr {d : ℕ}
    (m00 : ℝ) (m01 : Fin d → ℝ) (m02 : ℝ)
    (m10 : Fin d → ℝ) (m11 : Matrix (Fin d) (Fin d) ℝ) (m12 : Fin d → ℝ)
    (m20 : ℝ) (m21 : Fin d → ℝ) (m22 : ℝ) (u₁ u₂ : Unit) :
    tractorBlockMat m00 m01 m02 m10 m11 m12 m20 m21 m22
        (Sum.inr (Sum.inr u₁)) (Sum.inr (Sum.inr u₂)) = m22 := rfl

private theorem sum_tractorIdx {d : ℕ} (f : TractorIdx d → ℝ) :
    (∑ i : TractorIdx d, f i) =
      f (Sum.inl ()) + (∑ a : Fin d, f (Sum.inr (Sum.inl a))) + f (Sum.inr (Sum.inr ())) := by
  simp only [Fintype.sum_sum_type, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
  ring

private theorem dotProduct_mulVec_left {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (u v : n → ℝ) :
    dotProduct (M *ᵥ u) v = dotProduct u (Mᵀ *ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

private theorem tractorMat_mulVec_tractorVec {d : ℕ} (M : TractorMat d)
    (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) :
    M *ᵥ tractorVec σ μ ρ =
      tractorVec
        (M (Sum.inl ()) (Sum.inl ()) * σ +
          (∑ b : Fin d, M (Sum.inl ()) (Sum.inr (Sum.inl b)) * μ b) +
          M (Sum.inl ()) (Sum.inr (Sum.inr ())) * ρ)
        (fun a =>
          M (Sum.inr (Sum.inl a)) (Sum.inl ()) * σ +
          (∑ b : Fin d, M (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) * μ b) +
          M (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr ())) * ρ)
        (M (Sum.inr (Sum.inr ())) (Sum.inl ()) * σ +
          (∑ b : Fin d, M (Sum.inr (Sum.inr ())) (Sum.inr (Sum.inl b)) * μ b) +
          M (Sum.inr (Sum.inr ())) (Sum.inr (Sum.inr ())) * ρ) := by
  funext i
  rw [Matrix.mulVec, dotProduct, sum_tractorIdx]
  rcases i with ⟨⟩ | (a | ⟨⟩) <;> simp [tractorVec]

/-! ## Feature `A1`: Tractor Bundle Metric `h_{IJ}` & Conformal Rescaling -/

section FeatureA1_TractorMetric

/-- Signature-`(p + 1, q + 1)` tractor metric block matrix
`h(ε, g) = [[0, 0, ε], [0, g, 0], [ε, 0, 0]]`, where `ε = -1` matches the transcript and
`ε = +1` matches standard Bailey–Eastwood–Gover conventions. -/
def tractorMetricMatrix {d : ℕ} (ε : ℝ) (g : Matrix (Fin d) (Fin d) ℝ) : TractorMat d :=
  tractorBlockMat 0 0 ε 0 g 0 ε 0 0

/-- Genuine Mathlib bilinear form `tractorMetricBilin ε g : LinearMap.BilinForm ℝ (TractorVec d)`. -/
def tractorMetricBilin {d : ℕ} (ε : ℝ) (g : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.BilinForm ℝ (TractorVec d) :=
  (tractorMetricMatrix ε g).toBilin'

/-- `tractorMetricMatrix ε g` is symmetric iff `g` is symmetric. -/
theorem tractorMetricMatrix_transpose_iff {d : ℕ} (ε : ℝ) (g : Matrix (Fin d) (Fin d) ℝ) :
    (tractorMetricMatrix ε g)ᵀ = tractorMetricMatrix ε g ↔ gᵀ = g := by
  constructor
  · intro h
    ext a b
    have hab := congrArg (fun M : TractorMat d => M (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b))) h
    simpa [tractorMetricMatrix] using hab
  · intro hg
    ext i j
    rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
      simp [tractorMetricMatrix]
    simpa [Matrix.transpose_apply] using congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M a b) hg

theorem tractorMetricMatrix_transpose {d : ℕ} (ε : ℝ) (g : Matrix (Fin d) (Fin d) ℝ)
    (hg : gᵀ = g) : (tractorMetricMatrix ε g)ᵀ = tractorMetricMatrix ε g :=
  (tractorMetricMatrix_transpose_iff ε g).mpr hg

/-- Determinant of the `(d + 2)`-dimensional tractor metric: `det(h(ε, g)) = -det(g)` whenever
`ε ^ 2 = 1`. -/
theorem tractorMetricMatrix_det {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1) (g : Matrix (Fin d) (Fin d) ℝ) :
    (tractorMetricMatrix ε g).det = -g.det := by
  let τ : Equiv.Perm (TractorIdx d) := Equiv.swap (Sum.inl () : TractorIdx d) (Sum.inr (Sum.inr ()))
  have hne : (Sum.inl () : TractorIdx d) ≠ Sum.inr (Sum.inr ()) := by simp
  have hsign : (Equiv.Perm.sign τ : ℝ) = -1 := by
    rw [Equiv.Perm.sign_swap hne]
    norm_num
  have hperm : ((tractorMetricMatrix ε g).submatrix τ id).det =
      (Equiv.Perm.sign τ : ℝ) * (tractorMetricMatrix ε g).det := by
    calc
      ((tractorMetricMatrix ε g).submatrix τ id).det
          = (((tractorMetricMatrix ε g).submatrix τ id)ᵀ).det := (Matrix.det_transpose _).symm
      _ = ((tractorMetricMatrix ε g)ᵀ.submatrix id τ).det := by rw [Matrix.transpose_submatrix]
      _ = (Equiv.Perm.sign τ : ℝ) * (tractorMetricMatrix ε g)ᵀ.det :=
            Matrix.det_permute' τ (tractorMetricMatrix ε g)ᵀ
      _ = (Equiv.Perm.sign τ : ℝ) * (tractorMetricMatrix ε g).det := by
            rw [Matrix.det_transpose]
  have hdiag : (tractorMetricMatrix ε g).submatrix τ id =
      Matrix.fromBlocks
        (Matrix.of fun _ _ : Unit => ε)
        (0 : Matrix Unit (Fin d ⊕ Unit) ℝ)
        (0 : Matrix (Fin d ⊕ Unit) Unit ℝ)
        (Matrix.fromBlocks g (0 : Matrix (Fin d) Unit ℝ) (0 : Matrix Unit (Fin d) ℝ)
          (Matrix.of fun _ _ : Unit => ε)) := by
    ext i j
    rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
      simp [τ, tractorMetricMatrix, Equiv.swap_apply_def]
  have hdet_diag : ((tractorMetricMatrix ε g).submatrix τ id).det = g.det := by
    rw [hdiag, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
    have hunit : (Matrix.of fun _ _ : Unit => ε).det = ε := by
      simp [Matrix.det_unique]
    rw [hunit]
    calc
      ε * (g.det * ε) = ε ^ 2 * g.det := by ring
      _ = 1 * g.det := by rw [hε]
      _ = g.det := one_mul _
  rw [hsign, hdet_diag] at hperm
  linarith

theorem tractorMetricMatrix_det_ne_zero_iff {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g : Matrix (Fin d) (Fin d) ℝ) :
    (tractorMetricMatrix ε g).det ≠ 0 ↔ g.det ≠ 0 := by
  rw [tractorMetricMatrix_det ε hε g, neg_ne_zero]

/-- Explicit block inverse of `tractorMetricMatrix ε g` when `g * gInv = 1`, `gInv * g = 1`,
and `ε ^ 2 = 1`. -/
theorem tractorMetricMatrix_mul_inv {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g gInv : Matrix (Fin d) (Fin d) ℝ) (hgg : g * gInv = 1) (hinv : gInv * g = 1) :
    tractorMetricMatrix ε g * tractorMetricMatrix ε gInv = 1 ∧
    tractorMetricMatrix ε gInv * tractorMetricMatrix ε g = 1 := by
  constructor
  · ext i j
    rw [Matrix.mul_apply, sum_tractorIdx]
    rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
      simp [tractorMetricMatrix, Matrix.one_apply]
    · calc
        ε * ε = ε ^ 2 := by ring
        _ = 1 := hε
    · simpa [Matrix.mul_apply, Matrix.one_apply] using
        congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M a b) hgg
    · calc
        ε * ε = ε ^ 2 := by ring
        _ = 1 := hε
  · ext i j
    rw [Matrix.mul_apply, sum_tractorIdx]
    rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
      simp [tractorMetricMatrix, Matrix.one_apply]
    · calc
        ε * ε = ε ^ 2 := by ring
        _ = 1 := hε
    · simpa [Matrix.mul_apply, Matrix.one_apply] using
        congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M a b) hinv
    · calc
        ε * ε = ε ^ 2 := by ring
        _ = 1 := hε

/-- Exact bilinear expansion `tractorMetricBilin ε g u v = ε (σ₁ ρ₂ + ρ₁ σ₂) + μ₁ ⬝ᵥ (g *ᵥ μ₂)`. -/
theorem tractorMetricBilin_apply {d : ℕ} (ε : ℝ) (g : Matrix (Fin d) (Fin d) ℝ)
    (σ₁ ρ₁ σ₂ ρ₂ : ℝ) (μ₁ μ₂ : Fin d → ℝ) :
    tractorMetricBilin ε g (tractorVec σ₁ μ₁ ρ₁) (tractorVec σ₂ μ₂ ρ₂) =
      ε * (σ₁ * ρ₂ + ρ₁ * σ₂) + dotProduct μ₁ (g *ᵥ μ₂) := by
  simp only [tractorMetricBilin, Matrix.toBilin'_apply']
  rw [tractorMat_mulVec_tractorVec, dotProduct, sum_tractorIdx]
  simp only [tractorMetricMatrix, tractorBlockMat_inl_inl, tractorBlockMat_inl_mid,
    tractorBlockMat_inl_inr, tractorBlockMat_mid_inl, tractorBlockMat_mid_mid,
    tractorBlockMat_mid_inr, tractorBlockMat_inr_inl, tractorBlockMat_inr_mid,
    tractorBlockMat_inr_inr, tractorVec_inl, tractorVec_mid, tractorVec_inr,
    Pi.zero_apply, zero_mul, add_zero, zero_add, Finset.sum_const_zero]
  have hdot : dotProduct μ₁ (g *ᵥ μ₂) = ∑ a : Fin d, μ₁ a * ∑ x : Fin d, g a x * μ₂ x := rfl
  rw [hdot]
  ring

/-- Exact quadratic norm expansion `h(u, u) = 2 ε σ ρ + μ ⬝ᵥ (g *ᵥ μ)`. -/
theorem tractorMetricBilin_self {d : ℕ} (ε : ℝ) (g : Matrix (Fin d) (Fin d) ℝ)
    (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) :
    tractorMetricBilin ε g (tractorVec σ μ ρ) (tractorVec σ μ ρ) =
      2 * ε * σ * ρ + dotProduct μ (g *ᵥ μ) := by
  rw [tractorMetricBilin_apply]
  ring

/-- Positive-norm hyperbolic basis vector `e₊ = (1, 0, ε / 2)`. -/
def tractorHyperbolicPlus {d : ℕ} (ε : ℝ) : TractorVec d := tractorVec 1 0 (ε / 2)

/-- Negative-norm hyperbolic basis vector `e₋ = (1, 0, -ε / 2)`. -/
def tractorHyperbolicMinus {d : ℕ} (ε : ℝ) : TractorVec d := tractorVec 1 0 (-(ε / 2))

/-- The pair `(e₊, e₋)` provides an orthogonal `(+, -)` hyperbolic plane orthogonal to the middle
`Fin d` fiber, witnessing the signature `(p + 1, q + 1)` extension of `g`. -/
theorem tractorHyperbolic_signature_extension {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g : Matrix (Fin d) (Fin d) ℝ) (μ : Fin d → ℝ) :
    tractorMetricBilin ε g (tractorHyperbolicPlus ε) (tractorHyperbolicPlus ε) = 1 ∧
    tractorMetricBilin ε g (tractorHyperbolicMinus ε) (tractorHyperbolicMinus ε) = -1 ∧
    tractorMetricBilin ε g (tractorHyperbolicPlus ε) (tractorHyperbolicMinus ε) = 0 ∧
    tractorMetricBilin ε g (tractorHyperbolicPlus ε) (tractorVec 0 μ 0) = 0 ∧
    tractorMetricBilin ε g (tractorHyperbolicMinus ε) (tractorVec 0 μ 0) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold tractorHyperbolicPlus
    rw [tractorMetricBilin_self]
    simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have h1 : 2 * ε * 1 * (ε / 2) = 1 := by linarith [hε]
    exact h1
  · unfold tractorHyperbolicMinus
    rw [tractorMetricBilin_self]
    simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have h2 : 2 * ε * 1 * -(ε / 2) = -1 := by linarith [hε]
    exact h2
  · unfold tractorHyperbolicPlus tractorHyperbolicMinus
    rw [tractorMetricBilin_apply]
    simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have h3 : ε * (1 * -(ε / 2) + ε / 2 * 1) = 0 := by ring
    exact h3
  · unfold tractorHyperbolicPlus
    rw [tractorMetricBilin_apply]
    simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have h4 : ε * (1 * 0 + ε / 2 * 0) = 0 := by ring
    exact h4
  · unfold tractorHyperbolicMinus
    rw [tractorMetricBilin_apply]
    simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have h5 : ε * (1 * 0 + -(ε / 2) * 0) = 0 := by ring
    exact h5

private lemma scalar_exp_bilin_compat (ε c s₁ r₁ s₂ r₂ m : ℝ) :
    ε * (c * s₁ * (c * r₂) + c * r₁ * (c * s₂)) + c * c * m =
      c * c * (ε * (s₁ * r₂ + r₁ * s₂) + m) := by ring

/-- Compatibility with `MannheimWeylKazanasCosmology.conformalRescale`: rescaling `g ↦ e^{2β} g`
agrees with `conformalRescale β (tractorMetricBilin ε g)` on `(e^β σ, μ, e^β ρ)` and preserves
the tractor light cone. -/
theorem tractorMetricBilin_conformalRescale_compat {d : ℕ} (β ε : ℝ)
    (g : Matrix (Fin d) (Fin d) ℝ) (σ₁ ρ₁ σ₂ ρ₂ : ℝ) (μ₁ μ₂ : Fin d → ℝ) :
    tractorMetricBilin ε (Real.exp (2 * β) • g)
        (tractorVec (Real.exp β * σ₁) μ₁ (Real.exp β * ρ₁))
        (tractorVec (Real.exp β * σ₂) μ₂ (Real.exp β * ρ₂)) =
      conformalRescale β (tractorMetricBilin ε g)
        (tractorVec σ₁ μ₁ ρ₁) (tractorVec σ₂ μ₂ ρ₂) ∧
    (conformalRescale β (tractorMetricBilin ε g)
        (tractorVec σ₁ μ₁ ρ₁) (tractorVec σ₁ μ₁ ρ₁) = 0 ↔
      tractorMetricBilin ε g (tractorVec σ₁ μ₁ ρ₁) (tractorVec σ₁ μ₁ ρ₁) = 0) := by
  constructor
  · rw [tractorMetricBilin_apply]
    simp only [conformalRescale, LinearMap.smul_apply, smul_eq_mul, tractorMetricBilin_apply]
    have hexp : Real.exp (2 * β) = Real.exp β * Real.exp β := by
      rw [← Real.exp_add, two_mul]
    have hdot : dotProduct μ₁ ((Real.exp (2 * β) • g) *ᵥ μ₂) =
        Real.exp (2 * β) * dotProduct μ₁ (g *ᵥ μ₂) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [mul_assoc, mul_left_comm (μ₁ a)]
    rw [hdot, hexp]
    exact scalar_exp_bilin_compat ε (Real.exp β) σ₁ ρ₁ σ₂ ρ₂ (dotProduct μ₁ (g *ᵥ μ₂))
  · exact conformalRescale_null_cone_iff β (tractorMetricBilin ε g) (tractorVec σ₁ μ₁ ρ₁)

end FeatureA1_TractorMetric

/-! ## Feature `A2`: Schouten Tensor & Normal Cartan Tractor Connection (`d ≥ 3`) -/

section FeatureA2_SchoutenAndConnection

/-- Ricci scalar `R = tr(g⁻¹ Ric)`. -/
def scalarCurvature {d : ℕ} (gInv Ric : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (gInv * Ric).trace

/-- Conformal Schouten tensor `P_{ab} = (1 / (d - 2)) (R_{ab} - R / (2 (d - 1)) g_{ab})`. -/
def schoutenTensor (d : ℕ) (gInv Ric g : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 / ((d : ℝ) - 2)) • (Ric - (scalarCurvature gInv Ric / (2 * ((d : ℝ) - 1))) • g)

/-- `schoutenTensor` is symmetric whenever `Ric` and `g` are symmetric. -/
theorem schoutenTensor_transpose (d : ℕ) (gInv Ric g : Matrix (Fin d) (Fin d) ℝ)
    (hRic : Ricᵀ = Ric) (hg : gᵀ = g) :
    (schoutenTensor d gInv Ric g)ᵀ = schoutenTensor d gInv Ric g := by
  simp only [schoutenTensor, Matrix.transpose_smul, Matrix.transpose_sub, hRic, hg]

/-- Trace of the Schouten tensor in dimension `d ≥ 3`: `tr(g⁻¹ P) = R / (2 (d - 1))`. -/
theorem schoutenTensor_trace (d : ℕ) (hd : 3 ≤ d) (gInv Ric g : Matrix (Fin d) (Fin d) ℝ)
    (hinv : gInv * g = 1) :
    (gInv * schoutenTensor d gInv Ric g).trace = scalarCurvature gInv Ric / (2 * ((d : ℝ) - 1)) := by
  have hd2 : (d : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have htr1 : (1 : Matrix (Fin d) (Fin d) ℝ).trace = (d : ℝ) := by
    simp [Matrix.trace]
  unfold schoutenTensor scalarCurvature
  rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, hinv]
  simp only [Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul, htr1]
  field_simp [hd2, hd1]
  ring

/-- Einstein equivalence (`d ≥ 3`): `Ric = (R / d) • g ↔ P = (R / (2 d (d - 1))) • g`. -/
theorem schoutenTensor_einstein_iff (d : ℕ) (hd : 3 ≤ d) (gInv Ric g : Matrix (Fin d) (Fin d) ℝ) :
    Ric = (scalarCurvature gInv Ric / (d : ℝ)) • g ↔
      schoutenTensor d gInv Ric g =
        (scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1))) • g := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd2 : (d : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  constructor
  · intro hRic
    ext a b
    have hab := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M a b) hRic
    simp only [schoutenTensor, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at hab ⊢
    rw [hab]
    field_simp [hd0, hd1, hd2]
    ring
  · intro hP
    ext a b
    have hab := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M a b) hP
    simp only [schoutenTensor, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at hab
    have hcoeff :
        (1 / ((d : ℝ) - 2)) *
            (Ric a b - scalarCurvature gInv Ric / (2 * ((d : ℝ) - 1)) * g a b) =
          scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1)) * g a b := hab
    have hmul := congrArg (fun x => ((d : ℝ) - 2) * x) hcoeff
    have hmul' : Ric a b - scalarCurvature gInv Ric / (2 * ((d : ℝ) - 1)) * g a b =
        ((d : ℝ) - 2) * (scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1)) * g a b) := by
      calc
        Ric a b - scalarCurvature gInv Ric / (2 * ((d : ℝ) - 1)) * g a b
            = ((d : ℝ) - 2) * ((1 / ((d : ℝ) - 2)) *
                (Ric a b - scalarCurvature gInv Ric / (2 * ((d : ℝ) - 1)) * g a b)) := by
              field_simp [hd2]
        _ = ((d : ℝ) - 2) *
              (scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1)) * g a b) := hmul
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc
      Ric a b =
          ((d : ℝ) - 2) * (scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1)) * g a b) +
            scalarCurvature gInv Ric / (2 * ((d : ℝ) - 1)) * g a b := by linarith [hmul']
      _ = scalarCurvature gInv Ric / (d : ℝ) * g a b := by
          field_simp [hd0, hd1]
          ring

/-- Einstein equation with cosmological constant `Λ` (`Ric - (R / 2) • g + Λ • g = 0`) determines
`R = 2 d Λ / (d - 2)` and `R / (d (d - 1)) = 2 Λ / ((d - 1)(d - 2))` for `d ≥ 3`. -/
theorem einsteinLambda_scalarCurv (d : ℕ) (hd : 3 ≤ d)
    (gInv Ric g : Matrix (Fin d) (Fin d) ℝ) (Λ : ℝ)
    (hinv : gInv * g = 1)
    (hEin : Ric - (scalarCurvature gInv Ric / 2) • g + Λ • g = 0) :
    scalarCurvature gInv Ric = 2 * (d : ℝ) * Λ / ((d : ℝ) - 2) ∧
    scalarCurvature gInv Ric / ((d : ℝ) * ((d : ℝ) - 1)) =
      2 * Λ / (((d : ℝ) - 1) * ((d : ℝ) - 2)) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd2 : (d : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have htr := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => (gInv * M).trace) hEin
  have htr1 : (1 : Matrix (Fin d) (Fin d) ℝ).trace = (d : ℝ) := by simp [Matrix.trace]
  rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hinv, Matrix.mul_zero] at htr
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_zero,
    smul_eq_mul, htr1] at htr
  change scalarCurvature gInv Ric - scalarCurvature gInv Ric / 2 * (d : ℝ) + Λ * (d : ℝ) = 0 at htr
  have hR : scalarCurvature gInv Ric = 2 * (d : ℝ) * Λ / ((d : ℝ) - 2) := by
    field_simp [hd2]
    linarith
  refine ⟨hR, ?_⟩
  rw [hR]
  field_simp [hd0, hd1, hd2]

/-- Normal Cartan tractor connection matrix `Γ_a(ε)` in direction `a : Fin d`, with general
Levi-Civita spin connection matrix `ω` and Schouten tensor `P`:
`[[0, -row_a(g), 0], [col_a(g⁻¹ P), ω, ε e_a], [0, -ε row_a(P), 0]]`. -/
def normalConnectionMatrix {d : ℕ} (ε : ℝ) (g gInv P ω : Matrix (Fin d) (Fin d) ℝ)
    (a : Fin d) : TractorMat d :=
  tractorBlockMat
    0 (fun b => -g a b) 0
    (fun c => (gInv * P) c a) ω (fun c => if c = a then ε else 0)
    0 (fun b => -(ε * P a b)) 0

/-- Metric compatibility of the normal Cartan tractor connection: `h * Γ_a + Γ_aᵀ * h = 0` whenever
`ε ^ 2 = 1`, `gᵀ = g`, `g * gInv = 1`, `Pᵀ = P`, and `g * ω + ωᵀ * g = 0`. -/
theorem normalConnectionMatrix_metric_compatible {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g gInv P ω : Matrix (Fin d) (Fin d) ℝ)
    (hg : gᵀ = g) (hgg : g * gInv = 1) (hP : Pᵀ = P) (hω : g * ω + ωᵀ * g = 0)
    (a : Fin d) :
    tractorMetricMatrix ε g * normalConnectionMatrix ε g gInv P ω a +
      (normalConnectionMatrix ε g gInv P ω a)ᵀ * tractorMetricMatrix ε g = 0 := by
  have hgP : g * (gInv * P) = P := by rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, sum_tractorIdx, sum_tractorIdx]
  rcases i with _ | (c | _) <;> rcases j with _ | (b | _)
  · simp [tractorMetricMatrix, normalConnectionMatrix]
  · simp [tractorMetricMatrix, normalConnectionMatrix]
    have hcol : (∑ x : Fin d, (gInv * P) x a * g x b) = P a b := by
      have h1 : (∑ x : Fin d, (gInv * P) x a * g x b) = ∑ x : Fin d, g b x * (gInv * P) x a := by
        refine Finset.sum_congr rfl ?_
        intro x _
        have hgx : g x b = g b x := by rw [← Matrix.transpose_apply g b x, hg]
        rw [hgx, mul_comm]
      rw [h1]
      exact (congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M b a) hgP).trans
        (by rw [← Matrix.transpose_apply P a b, hP])
    rw [hcol]
    calc
      -(ε * (ε * P a b)) + P a b = (1 - ε ^ 2) * P a b := by ring
      _ = (1 - 1) * P a b := by rw [hε]
      _ = 0 := by ring
  · simp [tractorMetricMatrix, normalConnectionMatrix]
  · simp [tractorMetricMatrix, normalConnectionMatrix]
    have hcol : (∑ x : Fin d, g c x * (gInv * P) x a) = P c a :=
      congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M c a) hgP
    rw [hcol]
    have hPac : P a c = P c a := by rw [← Matrix.transpose_apply P c a, hP]
    rw [hPac]
    calc
      P c a + -(ε * P c a * ε) = (1 - ε ^ 2) * P c a := by ring
      _ = (1 - 1) * P c a := by rw [hε]
      _ = 0 := by ring
  · simp [tractorMetricMatrix, normalConnectionMatrix]
    have hωcb := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M c b) hω
    simpa [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply] using hωcb
  · simp [tractorMetricMatrix, normalConnectionMatrix]
    have hgac : g a c = g c a := by rw [← Matrix.transpose_apply g c a, hg]
    rw [hgac]
    ring
  · simp [tractorMetricMatrix, normalConnectionMatrix]
  · simp [tractorMetricMatrix, normalConnectionMatrix]
  · simp [tractorMetricMatrix, normalConnectionMatrix]

private lemma scalar_mul_neg_eps_sq (ε p : ℝ) (hε : ε ^ 2 = 1) :
    ε * -(ε * p) = -p := by
  calc
    ε * -(ε * p) = -(ε ^ 2 * p) := by ring
    _ = -(1 * p) := by rw [hε]
    _ = -p := by ring

private lemma scalar_comm_mid_rearrange (gpca gae gpcb gbe pa pb : ℝ) :
    gpca * -gbe + -pa - (gpcb * -gae + -pb) = pb - pa + gpcb * gae - gpca * gbe := by
  ring

/-- Exact `(1, 1)`-block commutator cancellation identity of the normal tractor connection
(`ω = 0`): `[Γ_a, Γ_b]^c_e = δ_b^c P_{ae} - δ_a^c P_{be} + P_b^c g_{ae} - P_a^c g_{be}`,
canceling the Schouten terms in the Riemann tensor to leave the Weyl curvature. -/
theorem normalConnection_commutator_mid {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g gInv P : Matrix (Fin d) (Fin d) ℝ) (a b c e : Fin d) :
    (normalConnectionMatrix ε g gInv P 0 a * normalConnectionMatrix ε g gInv P 0 b -
      normalConnectionMatrix ε g gInv P 0 b * normalConnectionMatrix ε g gInv P 0 a)
      (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl e)) =
      (if c = b then P a e else 0) - (if c = a then P b e else 0) +
        (gInv * P) c b * g a e - (gInv * P) c a * g b e := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_tractorIdx, sum_tractorIdx]
  simp only [normalConnectionMatrix, tractorBlockMat_mid_inl, tractorBlockMat_mid_mid,
    tractorBlockMat_mid_inr, tractorBlockMat_inl_mid, tractorBlockMat_inr_mid,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  have h1 : (if c = a then ε else 0) * -(ε * P b e) = -(if c = a then P b e else 0) := by
    split_ifs
    · exact scalar_mul_neg_eps_sq ε (P b e) hε
    · simp
  have h2 : (if c = b then ε else 0) * -(ε * P a e) = -(if c = b then P a e else 0) := by
    split_ifs
    · exact scalar_mul_neg_eps_sq ε (P a e) hε
    · simp
  rw [h1, h2]
  exact scalar_comm_mid_rearrange ((gInv * P) c a) (g a e) ((gInv * P) c b) (g b e)
    (if c = a then P b e else 0) (if c = b then P a e else 0)

end FeatureA2_SchoutenAndConnection

/-! ## Features `A3` & `A4`: Scale Tractor `I^A` & Unipotent Gauge Fixing `exp(g₁)` -/

section FeaturesA3A4_ScaleAndUnipotentGauge

/-- General algebraic scale tractor `I^A = (σ, μ^a, ρ)^T`. -/
def scaleTractor {d : ℕ} (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) : TractorVec d :=
  tractorVec σ μ ρ

/-- Thomas scale tractor with differential slot `μ = g⁻¹ dσ` and bottom slot
`ρ = -(ε / d) * (Δσ + P σ)`. -/
def thomasScaleTractor (d : ℕ) (gInv : Matrix (Fin d) (Fin d) ℝ) (σ : ℝ)
    (dσ : Fin d → ℝ) (lapPlusPσ ε : ℝ) : TractorVec d :=
  tractorVec σ (gInv *ᵥ dσ) (-(ε / (d : ℝ)) * lapPlusPσ)

/-- Unitary-gauge scale tractor `(1, 0, -(ε R / (2 d (d - 1))))^T`. -/
def unitaryScaleTractor (d : ℕ) (ε R : ℝ) : TractorVec d :=
  tractorVec 1 0 (-(ε * R / (2 * (d : ℝ) * ((d : ℝ) - 1))))

/-- Literal transcript `T07:428` unitary scale tractor `(1, 0, -R / (2 d (d - 1)))^T`. -/
def unitaryScaleTractorT07 (d : ℕ) (R : ℝ) : TractorVec d :=
  unitaryScaleTractor d 1 R

/-- Nilpotent unipotent gauge generator `N(ε, g⁻¹, υ) ∈ g₁`:
`[[0, 0, 0], [-g⁻¹ υ, 0, 0], [0, ε υᵀ, 0]]`. -/
def nilpotentGaugeGen {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ) (υ : Fin d → ℝ) :
    TractorMat d :=
  tractorBlockMat 0 0 0 (fun a => -(gInv *ᵥ υ) a) 0 0 0 (fun b => ε * υ b) 0

/-- `N(ε, g⁻¹, υ)` is `h(ε)`-skew-symmetric (`h * N + Nᵀ * h = 0`) when `ε ^ 2 = 1`, `gᵀ = g`,
and `g * gInv = 1`. -/
theorem nilpotentGaugeGen_metric_skew {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g gInv : Matrix (Fin d) (Fin d) ℝ) (hg : gᵀ = g) (hgg : g * gInv = 1)
    (υ : Fin d → ℝ) :
    tractorMetricMatrix ε g * nilpotentGaugeGen ε gInv υ +
      (nilpotentGaugeGen ε gInv υ)ᵀ * tractorMetricMatrix ε g = 0 := by
  have hgυ : g *ᵥ (gInv *ᵥ υ) = υ := by
    rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, sum_tractorIdx, sum_tractorIdx]
  rcases i with _ | (a | _) <;> rcases j with _ | (b | _)
  · simp [tractorMetricMatrix, nilpotentGaugeGen]
  · simp [tractorMetricMatrix, nilpotentGaugeGen]
    have hcol : (∑ x : Fin d, (gInv *ᵥ υ) x * g x b) = (g *ᵥ (gInv *ᵥ υ)) b := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl ?_
      intro x _
      have hgx : g x b = g b x := by rw [← Matrix.transpose_apply g b x, hg]
      rw [hgx, mul_comm]
    rw [hcol, hgυ]
    calc
      ε * (ε * υ b) + -υ b = (ε ^ 2 - 1) * υ b := by ring
      _ = (1 - 1) * υ b := by rw [hε]
      _ = 0 := by ring
  · simp [tractorMetricMatrix, nilpotentGaugeGen]
  · simp [tractorMetricMatrix, nilpotentGaugeGen]
    have hrow : (∑ x : Fin d, g a x * (gInv *ᵥ υ) x) = (g *ᵥ (gInv *ᵥ υ)) a := rfl
    rw [hrow, hgυ]
    calc
      -υ a + ε * υ a * ε = (ε ^ 2 - 1) * υ a := by ring
      _ = (1 - 1) * υ a := by rw [hε]
      _ = 0 := by ring
  · simp [tractorMetricMatrix, nilpotentGaugeGen]
  · simp [tractorMetricMatrix, nilpotentGaugeGen]
  · simp [tractorMetricMatrix, nilpotentGaugeGen]
  · simp [tractorMetricMatrix, nilpotentGaugeGen]
  · simp [tractorMetricMatrix, nilpotentGaugeGen]

/-- Product of two `g₁` nilpotent generators has only a `(2, 0)` block `-ε ⟨υ₁, g⁻¹ υ₂⟩`. -/
theorem nilpotentGaugeGen_mul {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ)
    (υ₁ υ₂ : Fin d → ℝ) :
    nilpotentGaugeGen ε gInv υ₁ * nilpotentGaugeGen ε gInv υ₂ =
      tractorBlockMat 0 0 0 0 0 0 (-(ε * dotProduct υ₁ (gInv *ᵥ υ₂))) 0 0 := by
  ext i j
  rw [Matrix.mul_apply, sum_tractorIdx]
  rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
    simp [nilpotentGaugeGen, dotProduct, Finset.mul_sum]
  ring

theorem nilpotentGaugeGen_comm {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ)
    (hgInv : gInvᵀ = gInv) (υ₁ υ₂ : Fin d → ℝ) :
    nilpotentGaugeGen ε gInv υ₁ * nilpotentGaugeGen ε gInv υ₂ =
      nilpotentGaugeGen ε gInv υ₂ * nilpotentGaugeGen ε gInv υ₁ := by
  rw [nilpotentGaugeGen_mul, nilpotentGaugeGen_mul]
  have hdot : dotProduct υ₁ (gInv *ᵥ υ₂) = dotProduct υ₂ (gInv *ᵥ υ₁) := by
    calc
      dotProduct υ₁ (gInv *ᵥ υ₂) = dotProduct (gInv *ᵥ υ₂) υ₁ := dotProduct_comm _ _
      _ = dotProduct υ₂ (gInvᵀ *ᵥ υ₁) := dotProduct_mulVec_left gInv υ₂ υ₁
      _ = dotProduct υ₂ (gInv *ᵥ υ₁) := by rw [hgInv]
  rw [hdot]

theorem nilpotentGaugeGen_mul_three {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ)
    (υ₁ υ₂ υ₃ : Fin d → ℝ) :
    nilpotentGaugeGen ε gInv υ₁ * nilpotentGaugeGen ε gInv υ₂ * nilpotentGaugeGen ε gInv υ₃ = 0 := by
  rw [nilpotentGaugeGen_mul]
  ext i j
  rw [Matrix.mul_apply, sum_tractorIdx]
  rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
    simp [nilpotentGaugeGen]

/-- Exact nilpotency `N(υ) ^ 3 = 0`. -/
theorem nilpotentGaugeGen_pow_three {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ)
    (υ : Fin d → ℝ) :
    (nilpotentGaugeGen ε gInv υ) ^ 3 = 0 := by
  rw [pow_three, ← mul_assoc]
  exact nilpotentGaugeGen_mul_three ε gInv υ υ υ

/-- Truncated exponential unipotent gauge transformation `expG1 ε gInv υ = 1 + N + (1/2) N²`. -/
def expG1 {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ) (υ : Fin d → ℝ) : TractorMat d :=
  1 + nilpotentGaugeGen ε gInv υ +
    (1 / 2 : ℝ) • (nilpotentGaugeGen ε gInv υ * nilpotentGaugeGen ε gInv υ)

theorem expG1_eq_blocks {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ) (υ : Fin d → ℝ) :
    expG1 ε gInv υ =
      tractorBlockMat
        1 0 0
        (fun a => -(gInv *ᵥ υ) a) 1 0
        (-((ε / 2) * dotProduct υ (gInv *ᵥ υ))) (fun b => ε * υ b) 1 := by
  unfold expG1
  rw [nilpotentGaugeGen_mul]
  ext i j
  rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
    simp [nilpotentGaugeGen, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem expG1_zero {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ) :
    expG1 ε gInv 0 = 1 := by
  rw [expG1_eq_blocks]
  ext i j
  rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
    simp [Matrix.one_apply]

/-- Abelian group law on `exp(g₁)`: `expG1 υ₁ * expG1 υ₂ = expG1 (υ₁ + υ₂)` when `gInvᵀ = gInv`. -/
theorem expG1_mul {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ) (hgInv : gInvᵀ = gInv)
    (υ₁ υ₂ : Fin d → ℝ) :
    expG1 ε gInv υ₁ * expG1 ε gInv υ₂ = expG1 ε gInv (υ₁ + υ₂) := by
  have hsym : dotProduct υ₁ (gInv *ᵥ υ₂) = dotProduct υ₂ (gInv *ᵥ υ₁) := by
    calc
      dotProduct υ₁ (gInv *ᵥ υ₂) = dotProduct (gInv *ᵥ υ₂) υ₁ := dotProduct_comm _ _
      _ = dotProduct υ₂ (gInvᵀ *ᵥ υ₁) := dotProduct_mulVec_left gInv υ₂ υ₁
      _ = dotProduct υ₂ (gInv *ᵥ υ₁) := by rw [hgInv]
  rw [expG1_eq_blocks, expG1_eq_blocks, expG1_eq_blocks]
  ext i j
  rw [Matrix.mul_apply, sum_tractorIdx]
  rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
    simp [Matrix.one_apply, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  · ring
  · have hsum : (∑ x : Fin d, ε * υ₁ x * (gInv *ᵥ υ₂) x) = ε * dotProduct υ₁ (gInv *ᵥ υ₂) := by
      simp only [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _; ring
    rw [hsum, hsym]
    ring
  · ring

theorem expG1_mul_neg {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ) (hgInv : gInvᵀ = gInv)
    (υ : Fin d → ℝ) :
    expG1 ε gInv υ * expG1 ε gInv (-υ) = 1 ∧
    expG1 ε gInv (-υ) * expG1 ε gInv υ = 1 := by
  constructor <;>
  · rw [expG1_mul ε gInv hgInv]
    simp [expG1_zero]

/-- Determinant of any unipotent `exp(g₁)` element is `1`. -/
theorem expG1_det {d : ℕ} (ε : ℝ) (gInv : Matrix (Fin d) (Fin d) ℝ) (υ : Fin d → ℝ) :
    (expG1 ε gInv υ).det = 1 := by
  have hblk : expG1 ε gInv υ =
      Matrix.fromBlocks
        (1 : Matrix Unit Unit ℝ)
        (0 : Matrix Unit (Fin d ⊕ Unit) ℝ)
        (Matrix.of fun r _ =>
          match r with
          | Sum.inl a => -(gInv *ᵥ υ) a
          | Sum.inr _ => -((ε / 2) * dotProduct υ (gInv *ᵥ υ)))
        (Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) ℝ)
          (0 : Matrix (Fin d) Unit ℝ)
          (Matrix.of fun _ b => ε * υ b)
          (1 : Matrix Unit Unit ℝ)) := by
    rw [expG1_eq_blocks]
    ext i j
    rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
      simp [Matrix.one_apply]
  rw [hblk, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂]
  simp

/-- `expG1 ε gInv υ` preserves the tractor metric `h(ε, g)`:
`(expG1 ε gInv υ)ᵀ * h(ε, g) * expG1 ε gInv υ = h(ε, g)`. -/
theorem expG1_orthogonal {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g gInv : Matrix (Fin d) (Fin d) ℝ)
    (hg : gᵀ = g) (hgg : g * gInv = 1) (υ : Fin d → ℝ) :
    (expG1 ε gInv υ)ᵀ * tractorMetricMatrix ε g * expG1 ε gInv υ = tractorMetricMatrix ε g := by
  have hgυ : g *ᵥ (gInv *ᵥ υ) = υ := by
    rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  have hL : (expG1 ε gInv υ)ᵀ * tractorMetricMatrix ε g =
      tractorBlockMat
        (-((1 / 2 : ℝ) * dotProduct υ (gInv *ᵥ υ))) (fun b => -υ b) ε
        υ g 0
        ε 0 0 := by
    rw [expG1_eq_blocks]
    ext i j
    rw [Matrix.mul_apply, sum_tractorIdx]
    rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
      simp [tractorMetricMatrix, Matrix.transpose_apply, Matrix.one_apply]
    · calc
        ε / 2 * dotProduct υ (gInv *ᵥ υ) * ε = (ε ^ 2 / 2) * dotProduct υ (gInv *ᵥ υ) := by ring
        _ = 2⁻¹ * dotProduct υ (gInv *ᵥ υ) := by rw [hε]; ring
    · have hcol : (∑ x : Fin d, (gInv *ᵥ υ) x * g x b) = (g *ᵥ (gInv *ᵥ υ)) b := by
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl ?_
        intro x _
        have hgx : g x b = g b x := by rw [← Matrix.transpose_apply g b x, hg]
        rw [hgx, mul_comm]
      rw [hcol, hgυ]
    · calc
        ε * υ a * ε = ε ^ 2 * υ a := by ring
        _ = 1 * υ a := by rw [hε]
        _ = υ a := one_mul _
  rw [hL, expG1_eq_blocks]
  ext i j
  rw [Matrix.mul_apply, sum_tractorIdx]
  rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
    simp [tractorMetricMatrix, Matrix.one_apply]
  · have hsum : (∑ a : Fin d, υ a * (gInv *ᵥ υ) a) = dotProduct υ (gInv *ᵥ υ) := rfl
    rw [hsum]
    calc
      -(2⁻¹ * dotProduct υ (gInv *ᵥ υ)) + dotProduct υ (gInv *ᵥ υ) -
          ε * (ε / 2 * dotProduct υ (gInv *ᵥ υ))
          = ((1 / 2 : ℝ) - (ε ^ 2 / 2)) * dotProduct υ (gInv *ᵥ υ) := by ring
      _ = ((1 / 2 : ℝ) - (1 / 2 : ℝ)) * dotProduct υ (gInv *ᵥ υ) := by rw [hε]
      _ = 0 := by ring
  · calc
      -υ b + ε * (ε * υ b) = (ε ^ 2 - 1) * υ b := by ring
      _ = (1 - 1) * υ b := by rw [hε]
      _ = 0 := by ring
  · have hrow : (∑ x : Fin d, g a x * (gInv *ᵥ υ) x) = (g *ᵥ (gInv *ᵥ υ)) a := rfl
    rw [hrow, hgυ]
    ring

/-- Bilinear-form invariance under `exp(g₁)`: `h(U u, U v) = h(u, v)`. -/
theorem expG1_preserves_bilin {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g gInv : Matrix (Fin d) (Fin d) ℝ) (hg : gᵀ = g) (hgg : g * gInv = 1)
    (υ : Fin d → ℝ) (u v : TractorVec d) :
    tractorMetricBilin ε g (expG1 ε gInv υ *ᵥ u) (expG1 ε gInv υ *ᵥ v) =
      tractorMetricBilin ε g u v := by
  simp only [tractorMetricBilin, Matrix.toBilin'_apply']
  calc
    dotProduct (expG1 ε gInv υ *ᵥ u) (tractorMetricMatrix ε g *ᵥ (expG1 ε gInv υ *ᵥ v))
        = dotProduct u ((expG1 ε gInv υ)ᵀ *ᵥ (tractorMetricMatrix ε g *ᵥ (expG1 ε gInv υ *ᵥ v))) :=
          dotProduct_mulVec_left (expG1 ε gInv υ) u _
    _ = dotProduct u (((expG1 ε gInv υ)ᵀ * tractorMetricMatrix ε g * expG1 ε gInv υ) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = dotProduct u (tractorMetricMatrix ε g *ᵥ v) := by
          rw [expG1_orthogonal ε hε g gInv hg hgg υ]

/-- Conformal weight diagonal rescaling `D(σ) = diag(σ⁻¹, I_d, σ)`. -/
def weightDiag {d : ℕ} (σ : ℝ) : TractorMat d :=
  tractorBlockMat σ⁻¹ 0 0 0 1 0 0 0 σ

/-- `D(σ)` preserves the tractor metric `h(ε, g)` for `σ ≠ 0`. -/
theorem weightDiag_orthogonal {d : ℕ} (ε σ : ℝ) (hσ : σ ≠ 0)
    (g : Matrix (Fin d) (Fin d) ℝ) :
    (weightDiag σ)ᵀ * tractorMetricMatrix ε g * weightDiag σ = tractorMetricMatrix ε g := by
  ext i j
  rw [Matrix.mul_apply, sum_tractorIdx]
  rcases i with _ | (a | _) <;> rcases j with _ | (b | _) <;>
    simp [weightDiag, tractorMetricMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply]
  · field_simp [hσ]
  · field_simp [hσ]

/-- **Unitary Gauge Fixing (`A4`)**: when `σ ≠ 0`, applying the unipotent shift `expG1 ε gInv (σ⁻¹ • (g *ᵥ μ))`
followed by weight rescaling `D(σ)` annihilates the middle slot (`μ ↦ 0`), normalizes the top
slot (`σ ↦ 1`), and transforms the bottom slot to `σ * ρ + (ε / 2) * μ ⬝ᵥ (g *ᵥ μ)`. -/
theorem unitaryGaugeFixing {d : ℕ} (ε σ ρ : ℝ) (hσ : σ ≠ 0)
    (g gInv : Matrix (Fin d) (Fin d) ℝ) (hinv : gInv * g = 1) (μ : Fin d → ℝ) :
    weightDiag σ *ᵥ (expG1 ε gInv (σ⁻¹ • (g *ᵥ μ)) *ᵥ tractorVec σ μ ρ) =
      tractorVec 1 0 (σ * ρ + (ε / 2) * dotProduct μ (g *ᵥ μ)) := by
  have hgυ : gInv *ᵥ (σ⁻¹ • (g *ᵥ μ)) = σ⁻¹ • μ := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [expG1_eq_blocks, tractorMat_mulVec_tractorVec]
  simp only [tractorBlockMat_inl_inl, tractorBlockMat_inl_mid, tractorBlockMat_inl_inr,
    tractorBlockMat_mid_inl, tractorBlockMat_mid_mid, tractorBlockMat_mid_inr,
    tractorBlockMat_inr_inl, tractorBlockMat_inr_mid, tractorBlockMat_inr_inr,
    Matrix.one_apply, Pi.zero_apply, zero_mul, one_mul, Finset.sum_const_zero, add_zero]
  have hmid : (fun a => -(gInv *ᵥ (σ⁻¹ • (g *ᵥ μ))) a * σ +
      (∑ b : Fin d, (if a = b then (1 : ℝ) else 0) * μ b)) = 0 := by
    funext a
    have hgi : (gInv *ᵥ (σ⁻¹ • (g *ᵥ μ))) a = σ⁻¹ * μ a := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hgυ a
    rw [hgi]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Pi.zero_apply]
    field_simp [hσ]
    ring
  have hbot : -((ε / 2) * dotProduct (σ⁻¹ • (g *ᵥ μ)) (gInv *ᵥ (σ⁻¹ • (g *ᵥ μ)))) * σ +
      (∑ b : Fin d, ε * (σ⁻¹ • (g *ᵥ μ)) b * μ b) + ρ =
      ρ + (ε / 2) * σ⁻¹ * dotProduct μ (g *ᵥ μ) := by
    rw [hgυ]
    have hdot1 : dotProduct (σ⁻¹ • (g *ᵥ μ)) (σ⁻¹ • μ) = σ⁻¹ ^ 2 * dotProduct μ (g *ᵥ μ) := by
      rw [dotProduct_comm (σ⁻¹ • (g *ᵥ μ)) (σ⁻¹ • μ)]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro b _; ring
    have hdot2 : (∑ b : Fin d, ε * (σ⁻¹ • (g *ᵥ μ)) b * μ b) = ε * σ⁻¹ * dotProduct μ (g *ᵥ μ) := by
      rw [dotProduct_comm μ (g *ᵥ μ)]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro b _; ring
    rw [hdot1, hdot2]
    field_simp [hσ]
    ring
  rw [hmid, hbot]
  unfold weightDiag
  rw [tractorMat_mulVec_tractorVec]
  simp only [tractorBlockMat_inl_inl, tractorBlockMat_inl_mid, tractorBlockMat_inl_inr,
    tractorBlockMat_mid_inl, tractorBlockMat_mid_mid, tractorBlockMat_mid_inr,
    tractorBlockMat_inr_inl, tractorBlockMat_inr_mid, tractorBlockMat_inr_inr,
    Matrix.one_apply, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rw [tractorVec_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · field_simp [hσ]
  · funext a; simp
  · field_simp [hσ]

/-- Unitary gauge transformation on the Thomas scale tractor `(σ, g⁻¹ dσ, -(ε / d)(Δσ + P σ))`
evaluated at `σ = 1, dσ = 0, Δσ = 0, P = R / (2 (d - 1))` recovers `unitaryScaleTractor`. -/
theorem unitaryGaugeFixing_at_unitary {d : ℕ} (hd : 3 ≤ d) (ε R : ℝ)
    (g gInv : Matrix (Fin d) (Fin d) ℝ) (hinv : gInv * g = 1) :
    weightDiag 1 *ᵥ
        (expG1 ε gInv ((1 : ℝ)⁻¹ • (g *ᵥ (gInv *ᵥ 0))) *ᵥ
          thomasScaleTractor d gInv 1 0 (R / (2 * ((d : ℝ) - 1))) ε) =
      unitaryScaleTractor d ε R := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  unfold thomasScaleTractor unitaryScaleTractor
  rw [Matrix.mulVec_zero, unitaryGaugeFixing ε 1 _ one_ne_zero g gInv hinv 0]
  simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
    one_mul]
  rw [tractorVec_eq_iff]
  refine ⟨rfl, rfl, ?_⟩
  field_simp [hd0, hd1]

end FeaturesA3A4_ScaleAndUnipotentGauge

/-! ## Feature `A5`: Algebraic Eastwood–Gover Equivalence (`∇^T I = 0 ↔` Einstein) -/

section FeatureA5_EastwoodGoverAlgebraic

/-- 1-jet algebraic covariant derivative `∇_a^T(ε) I = ∂_a I + Γ_a(ε) *ᵥ I` on fiber data
`(I = (σ, μ, ρ), dσ, dμ, dρ)`. -/
def tractorCovDeriv {d : ℕ} (ε : ℝ) (g gInv P : Matrix (Fin d) (Fin d) ℝ)
    (I : TractorVec d) (dσ : Fin d → ℝ) (dμ : Fin d → Fin d → ℝ) (dρ : Fin d → ℝ)
    (a : Fin d) : TractorVec d :=
  tractorVec (dσ a) (dμ a) (dρ a) + normalConnectionMatrix ε g gInv P 0 a *ᵥ I

theorem tractorCovDeriv_apply {d : ℕ} (ε : ℝ) (g gInv P : Matrix (Fin d) (Fin d) ℝ)
    (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) (dσ : Fin d → ℝ) (dμ : Fin d → Fin d → ℝ)
    (dρ : Fin d → ℝ) (a : Fin d) :
    tractorCovDeriv ε g gInv P (tractorVec σ μ ρ) dσ dμ dρ a =
      tractorVec
        (dσ a - dotProduct (g a) μ)
        (fun c => dμ a c + (gInv * P) c a * σ + (if c = a then ε * ρ else 0))
        (dρ a - ε * dotProduct (P a) μ) := by
  unfold tractorCovDeriv
  rw [tractorMat_mulVec_tractorVec]
  funext i
  rcases i with _ | (c | _)
  · simp [normalConnectionMatrix, dotProduct, sub_eq_add_neg]
  · simp [normalConnectionMatrix]
    ring
  · simp [normalConnectionMatrix, dotProduct, sub_eq_add_neg, Finset.mul_sum, mul_assoc]

/-- **Eastwood–Gover Unitary-Gauge Fiber Equivalence**: in the unitary gauge
(`σ = 1, μ = 0, dσ = 0, dμ = 0`), `∇^T I = 0` holds iff `P = (-ε * ρ) • g` and `dρ = 0`. -/
theorem parallel_unitary_iff_schouten {d : ℕ} (ε ρ : ℝ)
    (g gInv P : Matrix (Fin d) (Fin d) ℝ) (dρ : Fin d → ℝ)
    (hgg : g * gInv = 1) (hinv : gInv * g = 1) :
    (∀ a, tractorCovDeriv ε g gInv P (tractorVec 1 0 ρ) 0 0 dρ a = 0) ↔
      P = (-(ε * ρ)) • g ∧ dρ = 0 := by
  constructor
  · intro h
    have hP : P = (-(ε * ρ)) • g := by
      have hgP : gInv * P = (-(ε * ρ)) • 1 := by
        ext c a
        have ha := congrFun (h a) (Sum.inr (Sum.inl c))
        rw [tractorCovDeriv_apply] at ha
        simp only [tractorVec_mid, Pi.zero_apply, zero_add, mul_one, Matrix.smul_apply,
          Matrix.one_apply, smul_eq_mul] at ha ⊢
        split_ifs at ha with hca
        · subst hca; simp; linarith
        · simp [hca]; linarith
      calc
        P = (g * gInv) * P := by rw [hgg, Matrix.one_mul]
        _ = g * (gInv * P) := Matrix.mul_assoc g gInv P
        _ = g * ((-(ε * ρ)) • 1) := by rw [hgP]
        _ = (-(ε * ρ)) • g := by rw [Matrix.mul_smul, Matrix.mul_one]
    have hdρ : dρ = 0 := by
      funext a
      have ha := congrFun (h a) (Sum.inr (Sum.inr ()))
      rw [tractorCovDeriv_apply] at ha
      simpa [dotProduct] using ha
    exact ⟨hP, hdρ⟩
  · rintro ⟨hP, hdρ⟩ a
    rw [tractorCovDeriv_apply, hP, hdρ]
    funext i
    rcases i with _ | (c | _)
    · simp [dotProduct]
    · simp only [tractorVec_mid, Pi.zero_apply, zero_add, mul_one, Matrix.mul_smul, hinv,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> ring
    · simp [dotProduct]

/-- **Eastwood–Gover Unitary-Gauge Einstein Equivalence (`d ≥ 3`)**: for `P = schoutenTensor`,
`∇^T I = 0` in the unitary gauge is equivalent to `Ric = (R / d) • g`, `ρ = -ε R / (2 d (d - 1))`,
and `dρ = 0`. -/
theorem parallel_unitary_iff_einstein (d : ℕ) (hd : 3 ≤ d) (ε ρ : ℝ) (hε : ε ^ 2 = 1)
    (g gInv Ric : Matrix (Fin d) (Fin d) ℝ) (dρ : Fin d → ℝ)
    (hgg : g * gInv = 1) (hinv : gInv * g = 1) :
    (∀ a, tractorCovDeriv ε g gInv (schoutenTensor d gInv Ric g) (tractorVec 1 0 ρ) 0 0 dρ a = 0) ↔
      Ric = (scalarCurvature gInv Ric / (d : ℝ)) • g ∧
      ρ = -(ε * scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1))) ∧
      dρ = 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [parallel_unitary_iff_schouten ε ρ g gInv (schoutenTensor d gInv Ric g) dρ hgg hinv]
  constructor
  · rintro ⟨hP, hdρ⟩
    have htr := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => (gInv * M).trace) hP
    rw [schoutenTensor_trace d hd gInv Ric g hinv, Matrix.mul_smul, hinv, Matrix.trace_smul] at htr
    have htr1 : (1 : Matrix (Fin d) (Fin d) ℝ).trace = (d : ℝ) := by simp [Matrix.trace]
    rw [htr1, smul_eq_mul] at htr
    have hρ_eq : -(ε * ρ) = scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1)) := by
      field_simp [hd0] at htr ⊢
      linarith
    have hρ : ρ = -(ε * scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1))) := by
      calc
        ρ = ε ^ 2 * ρ := by rw [hε, one_mul]
        _ = -(ε * -(ε * ρ)) := by ring
        _ = -(ε * (scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1)))) := by rw [hρ_eq]
        _ = -(ε * scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1))) := by ring
    have hP' : schoutenTensor d gInv Ric g =
        (scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1))) • g := by
      rw [hP, hρ_eq]
    exact ⟨(schoutenTensor_einstein_iff d hd gInv Ric g).mpr hP', hρ, hdρ⟩
  · rintro ⟨hRic, hρ, hdρ⟩
    have hP := (schoutenTensor_einstein_iff d hd gInv Ric g).mp hRic
    have hcoeff : -(ε * ρ) = scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1)) := by
      rw [hρ]
      calc
        -(ε * -(ε * scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1))))
            = ε ^ 2 * (scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1))) := by ring
        _ = scalarCurvature gInv Ric / (2 * (d : ℝ) * ((d : ℝ) - 1)) := by rw [hε, one_mul]
    rw [hcoeff]
    exact ⟨hP, hdρ⟩

/-- **Algebraic Contracted Bianchi Lemma (`d ≥ 2`)**: if the 1-jet of the Schouten tensor satisfies
`∇_c P_{ab} = (dλ)_c g_{ab}` together with the contracted Bianchi symmetry
`∑_{c,a} g^{ca} ∇_c P_{ab} = ∑_{c,a} g^{ca} ∇_b P_{ca}`, then `dλ = 0` (so `ρ` is constant). -/
theorem algebraic_bianchi_constancy (d : ℕ) (hd : 2 ≤ d)
    (gInv g : Matrix (Fin d) (Fin d) ℝ)
    (nablaP : Fin d → Matrix (Fin d) (Fin d) ℝ) (dlam : Fin d → ℝ)
    (hg : gᵀ = g) (hinv : gInv * g = 1)
    (hjet : ∀ c a b, nablaP c a b = dlam c * g a b)
    (hBianchi : ∀ b, (∑ c : Fin d, ∑ a : Fin d, gInv c a * nablaP c a b) =
      ∑ c : Fin d, ∑ a : Fin d, gInv c a * nablaP b c a) :
    dlam = 0 := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have htr : (∑ c : Fin d, ∑ a : Fin d, gInv c a * g c a) = (d : ℝ) := by
    have htr1 : (gInv * g).trace = (d : ℝ) := by
      rw [hinv]
      simp [Matrix.trace]
    rw [← htr1]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro c _
    refine Finset.sum_congr rfl ?_
    intro a _
    have hgca : g c a = g a c := by rw [← Matrix.transpose_apply g a c, hg]
    rw [hgca]
  funext b
  have hb := hBianchi b
  simp only [hjet] at hb
  have hlhs : (∑ c : Fin d, ∑ a : Fin d, gInv c a * (dlam c * g a b)) = dlam b := by
    have hswap : ∀ c : Fin d, (∑ a : Fin d, gInv c a * (dlam c * g a b)) =
        dlam c * (gInv * g) c b := by
      intro c
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      ring
    simp_rw [hswap, hinv, Matrix.one_apply]
    simp
  have hrhs : (∑ c : Fin d, ∑ a : Fin d, gInv c a * (dlam b * g c a)) = (d : ℝ) * dlam b := by
    have hpull : (∑ c : Fin d, ∑ a : Fin d, gInv c a * (dlam b * g c a)) =
        dlam b * (∑ c : Fin d, ∑ a : Fin d, gInv c a * g c a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro c _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      ring
    rw [hpull, htr, mul_comm]
  rw [hlhs, hrhs] at hb
  have hzero : ((d : ℝ) - 1) * dlam b = 0 := by linarith
  exact (mul_eq_zero.mp hzero).resolve_left hd1

/-- Trace-free part `tf(M) := M - (tr(g⁻¹ M) / d) • g` of a `(0, 2)` tensor `M`. -/
def traceFreePart (d : ℕ) (gInv g M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  M - ((gInv * M).trace / (d : ℝ)) • g

/-- **Almost-Einstein Equivalence on General Scale (`1 ≤ d`)**: vanishing of the middle slot of
`∇^T I` with `dμ a c = (g⁻¹ H)_{ca}` is equivalent to the trace-free almost-Einstein equation
`tf(H + σ P) = 0` together with `ρ = -(ε / d) (tr(g⁻¹ H) + σ tr(g⁻¹ P))`. -/
theorem parallel_general_mid_iff_almostEinstein (d : ℕ) (hd : 1 ≤ d) (ε σ ρ : ℝ)
    (hε : ε ^ 2 = 1) (g gInv P H : Matrix (Fin d) (Fin d) ℝ)
    (μ : Fin d → ℝ) (dσ dρ : Fin d → ℝ)
    (hgg : g * gInv = 1) (hinv : gInv * g = 1) :
    (∀ a c, (tractorCovDeriv ε g gInv P (tractorVec σ μ ρ) dσ
        (fun a c => (gInv * H) c a) dρ a) (Sum.inr (Sum.inl c)) = 0) ↔
      traceFreePart d gInv g (H + σ • P) = 0 ∧
        ρ = -(ε / (d : ℝ)) * ((gInv * H).trace + σ * (gInv * P).trace) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have htr1 : (1 : Matrix (Fin d) (Fin d) ℝ).trace = (d : ℝ) := by simp [Matrix.trace]
  have hiff_mat :
      (∀ a c, (tractorCovDeriv ε g gInv P (tractorVec σ μ ρ) dσ
          (fun a c => (gInv * H) c a) dρ a) (Sum.inr (Sum.inl c)) = 0) ↔
        H + σ • P + (ε * ρ) • g = 0 := by
    constructor
    · intro h
      have hgi : gInv * (H + σ • P) = -(ε * ρ) • 1 := by
        ext c a
        have hca := h a c
        rw [tractorCovDeriv_apply] at hca
        simp only [tractorVec_mid, Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply,
          Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hca ⊢
        split_ifs at hca with hEq
        · subst hEq; simp; linarith
        · simp [hEq]; linarith
      have hg_mul := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => g * M) hgi
      rw [← Matrix.mul_assoc, hgg, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at hg_mul
      rw [hg_mul]
      ext c a
      simp [smul_eq_mul]
    · intro h a c
      rw [tractorCovDeriv_apply]
      have hgi := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => (gInv * M) c a) h
      rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hinv,
        Matrix.mul_zero, Matrix.zero_apply] at hgi
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hgi
      simp only [tractorVec_mid]
      split_ifs with hEq
      · subst hEq; simp at hgi; linarith
      · simp [hEq] at hgi; linarith
  rw [hiff_mat]
  constructor
  · intro h
    have htr := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => (gInv * M).trace) h
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hinv,
      Matrix.mul_zero] at htr
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_zero, smul_eq_mul, htr1] at htr
    have hρ : ρ = -(ε / (d : ℝ)) * ((gInv * H).trace + σ * (gInv * P).trace) := by
      calc
        ρ = ε ^ 2 * ρ := by rw [hε, one_mul]
        _ = (ε / (d : ℝ)) * (ε * ρ * (d : ℝ)) := by field_simp [hd0]
        _ = (ε / (d : ℝ)) * (-((gInv * H).trace + σ * (gInv * P).trace)) := by
            congr 1; linarith
        _ = -(ε / (d : ℝ)) * ((gInv * H).trace + σ * (gInv * P).trace) := by ring
    have htf : traceFreePart d gInv g (H + σ • P) = 0 := by
      unfold traceFreePart
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
      ext c a
      have hca := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M c a) h
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hca
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply,
        smul_eq_mul]
      have hερ : ε * ρ = -(((gInv * H).trace + σ * (gInv * P).trace) / (d : ℝ)) := by
        field_simp [hd0]
        linarith
      rw [hερ] at hca
      linarith
    exact ⟨htf, hρ⟩
  · rintro ⟨htf, hρ⟩
    have hερ : ε * ρ = -(((gInv * H).trace + σ * (gInv * P).trace) / (d : ℝ)) := by
      rw [hρ]
      calc
        ε * (-(ε / (d : ℝ)) * ((gInv * H).trace + σ * (gInv * P).trace))
            = -(ε ^ 2 * ((gInv * H).trace + σ * (gInv * P).trace) / (d : ℝ)) := by ring
        _ = -(((gInv * H).trace + σ * (gInv * P).trace) / (d : ℝ)) := by rw [hε, one_mul]
    ext c a
    have hca := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M c a) htf
    unfold traceFreePart at hca
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul] at hca
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply,
      smul_eq_mul] at hca ⊢
    rw [hερ]
    linarith

/-- Rescaled Schouten tensor equivalence for nonvanishing scale `σ ≠ 0`:
`H + σ P + (ε ρ) g = 0` iff the conformally rescaled Schouten tensor
`P + σ⁻¹ H - (1/2) σ⁻² |dσ|² g` equals `-(ε σ ρ + (1/2) |dσ|²) (σ⁻² g)`. -/
theorem rescaledSchouten_einstein_iff {d : ℕ} (ε σ ρ gradSq : ℝ) (hσ : σ ≠ 0)
    (g P H : Matrix (Fin d) (Fin d) ℝ) :
    H + σ • P + (ε * ρ) • g = 0 ↔
      P + σ⁻¹ • H - ((1 / 2 : ℝ) * σ⁻¹ ^ 2 * gradSq) • g =
        (-(ε * σ * ρ + (1 / 2 : ℝ) * gradSq)) • ((σ⁻¹ ^ 2) • g) := by
  constructor
  · intro h
    ext a b
    have hab := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M a b) h
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
      smul_eq_mul] at hab ⊢
    have hH : H a b = -(σ * P a b + ε * ρ * g a b) := by linarith
    rw [hH]
    field_simp [hσ]
    ring
  · intro h
    ext a b
    have hab := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M a b) h
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
      smul_eq_mul] at hab ⊢
    calc
      H a b + σ * P a b + ε * ρ * g a b
          = σ * ((P a b + σ⁻¹ * H a b - (1 / 2 : ℝ) * σ⁻¹ ^ 2 * gradSq * g a b) -
              (-(ε * σ * ρ + (1 / 2 : ℝ) * gradSq) * (σ⁻¹ ^ 2 * g a b))) := by
            field_simp [hσ]; ring
      _ = 0 := by rw [hab, sub_self, mul_zero]

end FeatureA5_EastwoodGoverAlgebraic

/-! ## Feature `A6`: Tractor Norm Constancy & Cosmological Casimir -/

section FeatureA6_NormConstancyAndCasimir

/-- **Exact Differential Norm Constancy Identity (`A6`)**:
`∂_a(h(I, I)) = 2 ε (dσ_a ρ + σ dρ_a) + 2 μ ⬝ᵥ (g *ᵥ dμ_a) = 2 h(I, ∇_a^T I)`. -/
theorem tractorNorm_deriv_eq_two_bilin {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g gInv P : Matrix (Fin d) (Fin d) ℝ)
    (hg : gᵀ = g) (hgg : g * gInv = 1) (hP : Pᵀ = P)
    (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ)
    (dσ : Fin d → ℝ) (dμ : Fin d → Fin d → ℝ) (dρ : Fin d → ℝ) (a : Fin d) :
    2 * ε * (dσ a * ρ + σ * dρ a) + 2 * dotProduct μ (g *ᵥ dμ a) =
      2 * tractorMetricBilin ε g (tractorVec σ μ ρ)
        (tractorCovDeriv ε g gInv P (tractorVec σ μ ρ) dσ dμ dρ a) := by
  have hgP : g * (gInv * P) = P := by rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]
  rw [tractorCovDeriv_apply, tractorMetricBilin_apply]
  have h1 : dotProduct (g a) μ = dotProduct μ (fun c => g c a) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl ?_
    intro c _
    have hgca : g a c = g c a := by rw [← Matrix.transpose_apply g c a, hg]
    rw [hgca, mul_comm]
  have h2 : dotProduct (P a) μ = dotProduct μ (fun c => (g * (gInv * P)) c a) := by
    rw [hgP]
    simp only [dotProduct]
    refine Finset.sum_congr rfl ?_
    intro c _
    have hPca : P a c = P c a := by rw [← Matrix.transpose_apply P c a, hP]
    rw [hPca, mul_comm]
  have hmul : dotProduct μ (g *ᵥ (fun c => dμ a c + (gInv * P) c a * σ +
      (if c = a then ε * ρ else 0))) =
      dotProduct μ (g *ᵥ dμ a) +
        σ * dotProduct μ (fun c => (g * (gInv * P)) c a) +
        ε * ρ * dotProduct μ (fun c => g c a) := by
    simp only [dotProduct, Matrix.mulVec]
    have hrow : ∀ x : Fin d,
        ∑ c : Fin d, g x c * (dμ a c + (gInv * P) c a * σ + (if c = a then ε * ρ else 0)) =
          (∑ c : Fin d, g x c * dμ a c) +
            σ * (g * (gInv * P)) x a + ε * ρ * g x a := by
      intro x
      simp only [mul_add, Finset.sum_add_distrib]
      have hterm1 : (∑ c : Fin d, g x c * ((gInv * P) c a * σ)) =
          σ * (g * (gInv * P)) x a := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro c _
        ring
      have hterm2 : (∑ c : Fin d, g x c * (if c = a then ε * ρ else 0)) = ε * ρ * g x a := by
        rw [Finset.sum_eq_single a]
        · simp; ring
        · intro c _ hc; simp [hc]
        · intro ha; exact (ha (Finset.mem_univ a)).elim
      rw [hterm1, hterm2]
    have hsum_P : (∑ x : Fin d, μ x * (σ * (g * (gInv * P)) x a)) =
        σ * dotProduct μ (fun c => (g * (gInv * P)) c a) := by
      simp only [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _; ring
    have hsum_g : (∑ x : Fin d, μ x * (ε * ρ * g x a)) =
        ε * ρ * dotProduct μ (fun c => g c a) := by
      simp only [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _; ring
    simp_rw [hrow]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hsum_P, hsum_g]
    rfl
  rw [hmul, ← h1, ← h2]
  have hε_sq : ε * (σ * -(ε * dotProduct (P a) μ)) = -(σ * dotProduct (P a) μ) := by
    calc
      ε * (σ * -(ε * dotProduct (P a) μ)) = -(ε ^ 2 * (σ * dotProduct (P a) μ)) := by ring
      _ = -(1 * (σ * dotProduct (P a) μ)) := by rw [hε]
      _ = -(σ * dotProduct (P a) μ) := by ring
  calc
    2 * ε * (dσ a * ρ + σ * dρ a) + 2 * dotProduct μ (g *ᵥ dμ a)
        = 2 * (ε * (σ * dρ a + ρ * dσ a) + dotProduct μ (g *ᵥ dμ a)) := by ring
    _ = 2 * (ε * (σ * (dρ a - ε * dotProduct (P a) μ) + ρ * (dσ a - dotProduct (g a) μ)) +
          (dotProduct μ (g *ᵥ dμ a) + σ * dotProduct (P a) μ + ε * ρ * dotProduct (g a) μ)) := by
        have hexp : ε * (σ * (dρ a - ε * dotProduct (P a) μ) + ρ * (dσ a - dotProduct (g a) μ)) =
            ε * (σ * dρ a + ρ * dσ a) + ε * (σ * -(ε * dotProduct (P a) μ)) -
              ε * ρ * dotProduct (g a) μ := by ring
        rw [hexp, hε_sq]
        ring

/-- Parallel scale tractor implies vanishing differential of the tractor norm: `∇_a^T I = 0 → ∂_a(h(I,I)) = 0`. -/
theorem tractorNorm_const_of_parallel {d : ℕ} (ε : ℝ) (hε : ε ^ 2 = 1)
    (g gInv P : Matrix (Fin d) (Fin d) ℝ)
    (hg : gᵀ = g) (hgg : g * gInv = 1) (hP : Pᵀ = P)
    (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ)
    (dσ : Fin d → ℝ) (dμ : Fin d → Fin d → ℝ) (dρ : Fin d → ℝ) (a : Fin d)
    (hpar : tractorCovDeriv ε g gInv P (tractorVec σ μ ρ) dσ dμ dρ a = 0) :
    2 * ε * (dσ a * ρ + σ * dρ a) + 2 * dotProduct μ (g *ᵥ dμ a) = 0 := by
  rw [tractorNorm_deriv_eq_two_bilin ε hε g gInv P hg hgg hP σ μ ρ dσ dμ dρ a, hpar]
  simp

private lemma scalar_unitary_norm_aux (d ε R : ℝ) (hε : ε ^ 2 = 1)
    (hd0 : d ≠ 0) (hd1 : d - 1 ≠ 0) :
    2 * ε * 1 * -(ε * R / (2 * d * (d - 1))) = -(R / (d * (d - 1))) := by
  calc
    2 * ε * 1 * -(ε * R / (2 * d * (d - 1)))
        = -(ε ^ 2 * (2 * R / (2 * d * (d - 1)))) := by ring
    _ = -(1 * (2 * R / (2 * d * (d - 1)))) := by rw [hε]
    _ = -(R / (d * (d - 1))) := by field_simp [hd0, hd1]

private lemma scalar_T07_norm_aux (d R : ℝ) (hd0 : d ≠ 0) (hd1 : d - 1 ≠ 0) :
    2 * (-1 : ℝ) * 1 * -(1 * R / (2 * d * (d - 1))) = R / (d * (d - 1)) := by
  field_simp [hd0, hd1]

/-- Consistent unitary tractor norm `h(ε)(I(ε), I(ε)) = -R / (d (d - 1))`. -/
theorem unitaryScaleTractor_norm (d : ℕ) (ε R : ℝ) (hε : ε ^ 2 = 1)
    (hd0 : (d : ℝ) ≠ 0) (hd1 : (d : ℝ) - 1 ≠ 0) (g : Matrix (Fin d) (Fin d) ℝ) :
    tractorMetricBilin ε g (unitaryScaleTractor d ε R) (unitaryScaleTractor d ε R) =
      -(R / ((d : ℝ) * ((d : ℝ) - 1))) := by
  unfold unitaryScaleTractor
  rw [tractorMetricBilin_self]
  simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  exact scalar_unitary_norm_aux (d : ℝ) ε R hε hd0 hd1

/-- Literal `T07:428-431` contraction: pairing `h(-1)` with `unitaryScaleTractorT07 d R` gives
`+R / (d (d - 1))`. -/
theorem transcript_T07_unitary_norm (d : ℕ) (R : ℝ)
    (hd0 : (d : ℝ) ≠ 0) (hd1 : (d : ℝ) - 1 ≠ 0) (g : Matrix (Fin d) (Fin d) ℝ) :
    tractorMetricBilin (-1) g (unitaryScaleTractorT07 d R) (unitaryScaleTractorT07 d R) =
      R / ((d : ℝ) * ((d : ℝ) - 1)) := by
  unfold unitaryScaleTractorT07 unitaryScaleTractor
  rw [tractorMetricBilin_self]
  simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  exact scalar_T07_norm_aux (d : ℝ) R hd0 hd1

/-- Literal `T07:433-434` cosmological substitution `R = 2 d Λ / (d - 2)` for `d ≥ 3`. -/
theorem transcript_T07_unitary_norm_lambda (d : ℕ) (hd : 3 ≤ d) (R Λ : ℝ)
    (hR : R = 2 * (d : ℝ) * Λ / ((d : ℝ) - 2)) (g : Matrix (Fin d) (Fin d) ℝ) :
    tractorMetricBilin (-1) g (unitaryScaleTractorT07 d R) (unitaryScaleTractorT07 d R) =
      2 * Λ / (((d : ℝ) - 1) * ((d : ℝ) - 2)) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd2 : (d : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [transcript_T07_unitary_norm d R hd0 hd1 g, hR]
  field_simp [hd0, hd1, hd2]

/-- Cosmological Casimir trichotomy (`d ≥ 3`): dS (`Λ > 0`), Minkowski (`Λ = 0`), AdS (`Λ < 0`). -/
theorem casimir_cosmological_trichotomy (d : ℕ) (hd : 3 ≤ d) (Λ : ℝ) :
    let norm := 2 * Λ / (((d : ℝ) - 1) * ((d : ℝ) - 2))
    (0 < Λ ↔ 0 < norm) ∧ (Λ = 0 ↔ norm = 0) ∧ (Λ < 0 ↔ norm < 0) := by
  have hden : 0 < ((d : ℝ) - 1) * ((d : ℝ) - 2) := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  intro norm
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h; exact div_pos (by linarith) hden
    · intro h; have := mul_pos h hden; rw [div_mul_cancel₀ _ hden.ne'] at this; linarith
  · constructor
    · intro h; simp [norm, h]
    · intro h
      have h0 : 2 * Λ = 0 := by
        have := congrArg (fun x => x * (((d : ℝ) - 1) * ((d : ℝ) - 2))) h
        simpa [norm, hden.ne'] using this
      linarith
  · constructor
    · intro h; exact div_neg_of_neg_of_pos (by linarith) hden
    · intro h
      have h0 : 2 * Λ < 0 := by
        have := mul_neg_of_neg_of_pos h hden
        rw [div_mul_cancel₀ _ hden.ne'] at this
        exact this
      linarith

/-- At the conformal infinity / horizon zero-locus `σ = 0` (`I = (0, g⁻¹ n, ρ)`), the tractor norm
reduces to `n ⬝ᵥ (g⁻¹ n)` independently of `ε` and `ρ`. -/
theorem horizon_sigma_zero_norm {d : ℕ} (ε ρ : ℝ) (g gInv : Matrix (Fin d) (Fin d) ℝ)
    (hgg : g * gInv = 1) (n : Fin d → ℝ) :
    tractorMetricBilin ε g (tractorVec 0 (gInv *ᵥ n) ρ) (tractorVec 0 (gInv *ᵥ n) ρ) =
      dotProduct n (gInv *ᵥ n) := by
  rw [tractorMetricBilin_self]
  have hgn : g *ᵥ (gInv *ᵥ n) = n := by
    rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  rw [hgn, dotProduct_comm (gInv *ᵥ n) n]
  ring

end FeatureA6_NormConstancyAndCasimir

/-! ## Feature `A7`: Gravitational Meissner Effect (Cotton & Bach Expulsion) -/

section FeatureA7_GravitationalMeissner

/-- Tractor curvature block matrix `Ω_{ab}(ε, α)` with Cotton vector `A` and Weyl operator `C`:
`[[0, 0, 0], [α A, C, 0], [0, -ε α (g A)ᵀ, 0]]`. -/
def tractorCurvatureMatrix {d : ℕ} (ε α : ℝ) (g : Matrix (Fin d) (Fin d) ℝ)
    (A : Fin d → ℝ) (C : Matrix (Fin d) (Fin d) ℝ) : TractorMat d :=
  tractorBlockMat 0 0 0 (fun c => α * A c) C 0 0 (fun b => -(ε * α * (g *ᵥ A) b)) 0

/-- `tractorCurvatureMatrix` is `h(ε)`-skew-symmetric when `ε ^ 2 = 1` and `(g * C)ᵀ = -(g * C)`. -/
theorem tractorCurvatureMatrix_metric_skew {d : ℕ} (ε α : ℝ) (hε : ε ^ 2 = 1)
    (g : Matrix (Fin d) (Fin d) ℝ) (A : Fin d → ℝ)
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : (g * C)ᵀ = -(g * C)) :
    (tractorMetricMatrix ε g * tractorCurvatureMatrix ε α g A C)ᵀ =
      -(tractorMetricMatrix ε g * tractorCurvatureMatrix ε α g A C) := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply,
    sum_tractorIdx, sum_tractorIdx]
  rcases i with _ | (c | _) <;> rcases j with _ | (b | _)
  · simp [tractorMetricMatrix, tractorCurvatureMatrix]
  · simp [tractorMetricMatrix, tractorCurvatureMatrix]
    have hrow : (∑ x : Fin d, g b x * (α * A x)) = α * (g *ᵥ A) b := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _; ring
    rw [hrow]
    calc
      α * (g *ᵥ A) b = ε ^ 2 * (α * (g *ᵥ A) b) := by rw [hε, one_mul]
      _ = ε * (ε * α * (g *ᵥ A) b) := by ring
  · simp [tractorMetricMatrix, tractorCurvatureMatrix]
  · simp [tractorMetricMatrix, tractorCurvatureMatrix]
    have hrow : (∑ x : Fin d, g c x * (α * A x)) = α * (g *ᵥ A) c := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _; ring
    rw [hrow]
    calc
      ε * (ε * α * (g *ᵥ A) c) = ε ^ 2 * (α * (g *ᵥ A) c) := by ring
      _ = 1 * (α * (g *ᵥ A) c) := by rw [hε]
      _ = α * (g *ᵥ A) c := one_mul _
  · simp [tractorMetricMatrix, tractorCurvatureMatrix]
    have hCcb := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M c b) hC
    simpa [Matrix.transpose_apply, Matrix.neg_apply, Matrix.mul_apply] using hCcb
  · simp [tractorMetricMatrix, tractorCurvatureMatrix]
  · simp [tractorMetricMatrix, tractorCurvatureMatrix]
  · simp [tractorMetricMatrix, tractorCurvatureMatrix]
  · simp [tractorMetricMatrix, tractorCurvatureMatrix]

/-- Characterization of `Ω *ᵥ I = 0`. -/
theorem tractorCurvatureMatrix_mulVec_eq_zero_iff {d : ℕ} (ε α : ℝ)
    (g : Matrix (Fin d) (Fin d) ℝ) (A : Fin d → ℝ) (C : Matrix (Fin d) (Fin d) ℝ)
    (σ : ℝ) (μ : Fin d → ℝ) (ρ : ℝ) :
    tractorCurvatureMatrix ε α g A C *ᵥ tractorVec σ μ ρ = 0 ↔
      (α * σ) • A + C *ᵥ μ = 0 ∧ ε * α * dotProduct (g *ᵥ A) μ = 0 := by
  rw [tractorMat_mulVec_tractorVec]
  simp only [tractorCurvatureMatrix, tractorBlockMat_inl_inl, tractorBlockMat_inl_mid,
    tractorBlockMat_inl_inr, tractorBlockMat_mid_inl, tractorBlockMat_mid_mid,
    tractorBlockMat_mid_inr, tractorBlockMat_inr_inl, tractorBlockMat_inr_mid,
    tractorBlockMat_inr_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  have hmid : (fun a => α * A a * σ + ∑ b : Fin d, C a b * μ b) = (α * σ) • A + C *ᵥ μ := by
    funext c
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    ring
  have hbot : (∑ b : Fin d, -(ε * α * (g *ᵥ A) b) * μ b) = -(ε * α * dotProduct (g *ᵥ A) μ) := by
    simp only [dotProduct, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro b _; ring
  rw [hmid, hbot]
  have hzero : (0 : TractorVec d) = tractorVec 0 0 0 := by
    funext i; rcases i with _ | (c | _) <;> rfl
  rw [hzero, tractorVec_eq_iff]
  constructor
  · rintro ⟨_, hm, hb⟩
    exact ⟨hm, by linarith⟩
  · rintro ⟨hm, hb⟩
    exact ⟨rfl, hm, by linarith⟩

/-- By `g`-skew-symmetry of `C`, the middle equation `(α σ) A + C μ = 0` automatically implies
`g(A, μ) = 0` whenever `α ≠ 0` and `σ ≠ 0`. -/
theorem meissner_skew_bottom_vanishes {d : ℕ} (α σ : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0)
    (g : Matrix (Fin d) (Fin d) ℝ) (A μ : Fin d → ℝ) (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : (g * C)ᵀ = -(g * C)) (hmid : (α * σ) • A + C *ᵥ μ = 0) :
    dotProduct (g *ᵥ A) μ = 0 := by
  have hskew : dotProduct μ ((g * C) *ᵥ μ) = 0 := by
    have h1 : dotProduct μ ((g * C) *ᵥ μ) = -dotProduct μ ((g * C) *ᵥ μ) := by
      calc
        dotProduct μ ((g * C) *ᵥ μ) = dotProduct ((g * C) *ᵥ μ) μ := dotProduct_comm _ _
        _ = dotProduct μ ((g * C)ᵀ *ᵥ μ) := dotProduct_mulVec_left (g * C) μ μ
        _ = dotProduct μ ((-(g * C)) *ᵥ μ) := by rw [hC]
        _ = -dotProduct μ ((g * C) *ᵥ μ) := by rw [Matrix.neg_mulVec, dotProduct_neg]
    linarith
  have hcon := congrArg (fun v => dotProduct (gᵀ *ᵥ μ) v) hmid
  have hcon' : (α * σ) * dotProduct (g *ᵥ A) μ + dotProduct μ ((g * C) *ᵥ μ) = 0 := by
    calc
      (α * σ) * dotProduct (g *ᵥ A) μ + dotProduct μ ((g * C) *ᵥ μ)
          = (α * σ) * dotProduct (g *ᵥ A) μ + dotProduct (g *ᵥ (C *ᵥ μ)) μ := by
            rw [Matrix.mulVec_mulVec, dotProduct_comm ((g * C) *ᵥ μ) μ]
      _ = (α * σ) * dotProduct (g *ᵥ A) μ + dotProduct (C *ᵥ μ) (gᵀ *ᵥ μ) := by
            rw [dotProduct_mulVec_left g (C *ᵥ μ) μ]
      _ = (α * σ) * dotProduct (gᵀ *ᵥ μ) A + dotProduct (gᵀ *ᵥ μ) (C *ᵥ μ) := by
            rw [dotProduct_mulVec_left g A μ, dotProduct_comm A (gᵀ *ᵥ μ),
              dotProduct_comm (C *ᵥ μ) (gᵀ *ᵥ μ)]
      _ = dotProduct (gᵀ *ᵥ μ) ((α * σ) • A + C *ᵥ μ) := by
            rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      _ = dotProduct (gᵀ *ᵥ μ) 0 := hcon
      _ = 0 := dotProduct_zero _
  rw [hskew, add_zero] at hcon'
  have hασ : α * σ ≠ 0 := mul_ne_zero hα hσ
  exact (mul_eq_zero.mp hcon').resolve_left hασ

/-- **Unitary-Gauge Cotton Expulsion (`A7`)**: when `α ≠ 0`, `σ ≠ 0`, and `μ = 0`,
`Ω *ᵥ I = 0` forces `A = 0`. -/
theorem meissner_unitary_cotton_zero {d : ℕ} (ε α σ ρ : ℝ) (hα : α ≠ 0) (hσ : σ ≠ 0)
    (g : Matrix (Fin d) (Fin d) ℝ) (A : Fin d → ℝ) (C : Matrix (Fin d) (Fin d) ℝ)
    (hΩ : tractorCurvatureMatrix ε α g A C *ᵥ tractorVec σ 0 ρ = 0) :
    A = 0 := by
  rw [tractorCurvatureMatrix_mulVec_eq_zero_iff] at hΩ
  have hmid := hΩ.1
  rw [Matrix.mulVec_zero, add_zero] at hmid
  have hασ : α * σ ≠ 0 := mul_ne_zero hα hσ
  funext c
  have hc := congrFun hmid c
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
  exact (mul_eq_zero.mp hc).resolve_left hασ

/-- Algebraic Bach tensor `B_{ab} = (div A)_{ab} + ∑_{c,e} P^{ce} W_{caeb}`. -/
def bachTensor {d : ℕ} (divA P_up : Matrix (Fin d) (Fin d) ℝ)
    (W_down : Fin d → Fin d → Fin d → Fin d → ℝ) (a b : Fin d) : ℝ :=
  divA a b + ∑ c : Fin d, ∑ e : Fin d, P_up c e * W_down c a e b

/-- **Algebraic Bach Expulsion (`A7`)**: under Cotton divergence vanishing `divA = 0`,
Einstein Schouten condition `P^{ce} = λ g^{ce}`, and Weyl Ricci-trace-freeness
`∑_{c,e} g^{ce} W_{caeb} = 0`, the Bach tensor vanishes identically. -/
theorem bachTensor_expulsion {d : ℕ} (divA P_up gInv : Matrix (Fin d) (Fin d) ℝ)
    (lam : ℝ) (W_down : Fin d → Fin d → Fin d → Fin d → ℝ)
    (hdiv : divA = 0) (hEin : P_up = lam • gInv)
    (hW : ∀ a b, ∑ c : Fin d, ∑ e : Fin d, gInv c e * W_down c a e b = 0)
    (a b : Fin d) :
    bachTensor divA P_up W_down a b = 0 := by
  unfold bachTensor
  rw [hdiv, hEin]
  simp only [Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul, zero_add]
  have hpull : (∑ c : Fin d, ∑ e : Fin d, lam * gInv c e * W_down c a e b) =
      lam * (∑ c : Fin d, ∑ e : Fin d, gInv c e * W_down c a e b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro c _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro e _
    rw [mul_assoc]
  rw [hpull, hW a b, mul_zero]

/-- **Concrete `d = 4` Bach Expulsion (`A7` × `MannheimWeylKazanasCosmology`)**:
instantiates `bachTensor_expulsion` directly on the signature-general 4D Weyl tensor
`weylTensor4` via `weylTensor4_trace_zero` for any diagonal signature `sig : Fin 4 → ℝ` with
`sig i * sig i = 1` and pair-symmetric algebraic Riemann tensor `Riem`. -/
theorem bachTensor4_weyl_expulsion
    (sig : Fin 4 → ℝ) (hsig : ∀ i : Fin 4, sig i * sig i = 1)
    (Riem : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h_pair : ∀ i j k l, Riem k l i j = Riem i j k l)
    (lam : ℝ) (divA : Matrix (Fin 4) (Fin 4) ℝ) (hdiv : divA = 0)
    (a b : Fin 4) :
    bachTensor divA (lam • diagMetric4 sig) (weylTensor4 sig Riem) a b = 0 := by
  refine bachTensor_expulsion divA (lam • diagMetric4 sig) (diagMetric4 sig) lam
    (weylTensor4 sig Riem) hdiv rfl ?_ a b
  intro p q
  have hsum : ∀ c : Fin 4,
      (∑ e : Fin 4, diagMetric4 sig c e * weylTensor4 sig Riem c p e q) =
        sig c * weylTensor4 sig Riem c p c q := by
    intro c
    rw [Finset.sum_eq_single c]
    · simp [diagMetric4]
    · intro e _ he
      simp [diagMetric4, Matrix.diagonal_apply_ne _ he.symm]
    · intro hc
      exact (hc (Finset.mem_univ c)).elim
  simp_rw [hsum]
  exact weylTensor4_trace_zero sig hsig Riem h_pair p q

end FeatureA7_GravitationalMeissner

end InfoGeometry.Conformal.CartanTractorCalculus
