/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.ConeSheetBraiding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Stages D₁₆ → D₁₈ (Archetypes S₁ → S₁₅): Non-Commutative Cellular Sheaf Operator Identities

This file formalizes a 15-stage ranked causal DAG (`S₁ → S₁₅`) of non-commutative
cellular-sheaf-inspired operator identities over an arbitrary associative star-ring `B`
(`[Ring B]` and `[StarRing B]`), together with their exact specialization to the
Peirce Tetraktys operators `(Φ, J, V, Σ)`, curved cochain identities (`d₁ * d₀ = F`),
algebraic Bianchi identities, and all-scale iterated defect sheet filtering. The listed
causal edges strictly increase a rank; `CellularSheafStage` also has the total order induced
by that rank, which is not claimed to be the transitive closure of the edge relation. The
ring elements and finite edge-indexed sums below are operator encodings: this module does not
construct vertex/stalk modules, incidence maps, or a graded cellular cochain complex.

* **Stage `D₁₆` (`S₁ → S₇`)**:
  - `S₁` & `S₂`: Peirce-graded degree-0 sheaf coboundary
    `sheafCoboundary0 P R_u R_v = R_u * P - R_v * (1 - P)` and the alignment condition
    `R_u * (P * X) = R_v * ((1 - P) * X) → sheafCoboundary0 P R_u R_v * X = 0`.
  - `S₃`: Degree-0 operator sheaf Laplacian `sheafLaplacian0 P R_u R_v = (δ_F)⋆ * δ_F`,
    its self-adjointness, and its `2 × 2` Peirce block decomposition
    `sheafBlock11 + sheafBlock10 + sheafBlock01 + sheafBlock00`.
  - `S₄`: Operator Dirichlet quadratic form `sheafDirichletForm P R_u R_v X = X⋆ * L_F * X`,
    its Hermitian square factorization `(δ_F * X)⋆ * (δ_F * X)`, and aligned-element
    annihilation of `L_F * X`, `X⋆ * L_F * X`, and `sheafDiffusionOp P R_u R_v X`.
  - `S₅`: Left-isometric operator covariance `δ_{U F} = U * δ_F` and strict gauge
    invariance `L_{U F} = L_F` under `star U * U = 1`.
  - `S₆`: Higher-order cochain pair with zero composite `d₁ * d₀ = 0`, adjoint annihilation
    `star d₀ * star d₁ = 0`, self-adjoint Hodge operator
    `sheafHodgeLaplacian d₀ d₁ = d₀ * star d₀ + star d₁ * d₁`, orthogonal up/down
    annihilation, and clean square splitting `Δ₁² = Δ_down² + Δ_up²`.
  - `S₇`: Exact specialization to the Peirce Tetraktys: for `R_u = coneMinus P C`
    and `R_v = conePlus P A` with `P * P = P` and `star P = P`,
    `sheafCoboundary0 P (coneMinus P C) (conePlus P A) = -genJ P A C`,
    `sheafCoboundary0 P (coneMinus P C) (-conePlus P A) = genPhi P A C`, and
    `sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A)`.
* **Stage `D₁₇` (`S₈ → S₁₁`)**:
  - `S₈`: Split-complex coboundary intertwining `δ_F * invS P = δ_F^+`, Laplacian conjugation
    `invS P * L_F * invS P = L_F^+`, and exact isolation of diagonal blocks (`L_F + L_F^+`)
    versus off-diagonal blocks (`L_F - L_F^+`).
  - `S₉`: operator `sheafEdgeLaplacian1 P R_u R_v = δ_F * (δ_F)⋆`,
    its cross-term-free reduction `R_u * P * star R_u + R_v * (1 - P) * star R_v`,
    sign-independence under `R_v ↦ -R_v`, universal supersymmetric vertex–edge intertwining
    `δ_F * L_F = L_F^(1) * δ_F`, and conjugation covariance `L_{U F}^(1) = U * L_F^(1) * star U`.
  - `S₁₀`: Horizon vertex–edge self-duality (`sheafEdgeLaplacian1 = sheafLaplacian0 = genV`),
    exact normality `comm (star δ_F) δ_F = 0`, and chiral cross-coboundary pairing
    `(δ_F^+)⋆ * δ_F = (δ_F)⋆ * δ_F^+ = genSig P A (star A)`.
  - `S₁₁`: Unconditional Peirce–Hodge cochain complex `d₀ = d₁ = conePlus P A` satisfying
    `d₁ * d₀ = 0`, with `Δ_down = qgtPlus`, `Δ_up = qgtMinus`, `Δ₁ = genV`, and
    `Δ_down - Δ_up = genSig`.
* **Stage `D₁₈` (`S₁₂ → S₁₅`)**:
  - `S₁₂`: Curved 2-step cochain complexes with curvature `sheafCurvature2 d₀ d₁ = d₁ * d₀`
    and Hodge–Weitzenböck curvature defect `Δ₁² = Δ_down² + Δ_up² + sheafWeitzenboeckDefect d₀ d₁`.
  - `S₁₃`: Non-commutative algebraic Bianchi identity `d₂ * F₁₀ = F₂₁ * d₀` and its adjoint
    identity `star d₀ * star F₂₁ = star F₁₀ * star d₂` for 3-tier complexes `(d₀, d₁, d₂)`.
  - `S₁₄`: Two-sided Peirce ideal absorption of the iterated defect tower (`mandelbrotTower`
    and `idempotencyDefect^[n]`) and swapped-cone global-section vanishing.
  - `S₁₅`: All-depth (`n : ℕ`) fractal sheet Hodge filtering and half-harmonic annihilation
    (`Δ_up * X_n = 0`, `Δ_down * Y_n = 0`, `Δ₁ * X_n = Q_+ * X_n`, `Δ₁ * Y_n = Q_- * Y_n`).
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

/-! ### 1. The 15-Stage Cellular Sheaf Causal DAG (`S₁ → S₁₅`) -/

/-- The 15 cellular sheaf archetype stages `S₁` through `S₁₅` spanning Stages `D₁₆`–`D₁₈`. -/
inductive CellularSheafStage : Type
  | S1 | S2 | S3 | S4 | S5 | S6 | S7
  | S8 | S9 | S10 | S11
  | S12 | S13 | S14 | S15
  deriving DecidableEq, Repr

namespace CellularSheafStage

/-- Topological rank (1 through 15) of each cellular sheaf archetype stage. -/
def rank : CellularSheafStage → ℕ
  | S1 => 1
  | S2 => 2
  | S3 => 3
  | S4 => 4
  | S5 => 5
  | S6 => 6
  | S7 => 7
  | S8 => 8
  | S9 => 9
  | S10 => 10
  | S11 => 11
  | S12 => 12
  | S13 => 13
  | S14 => 14
  | S15 => 15

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder CellularSheafStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed edges of the 15-stage cellular sheaf causal DAG (`S₁ → S₁₅`). -/
def causalEdge : CellularSheafStage → CellularSheafStage → Prop
  | S1, S2 => True
  | S1, S3 => True
  | S2, S4 => True
  | S3, S4 => True
  | S3, S5 => True
  | S4, S6 => True
  | S5, S6 => True
  | S5, S7 => True
  | S6, S7 => True
  | S3, S8 => True
  | S7, S8 => True
  | S6, S9 => True
  | S8, S9 => True
  | S7, S10 => True
  | S8, S10 => True
  | S9, S10 => True
  | S6, S11 => True
  | S10, S11 => True
  | S6, S12 => True
  | S11, S12 => True
  | S12, S13 => True
  | S11, S14 => True
  | S13, S14 => True
  | S12, S15 => True
  | S14, S15 => True
  | _, _ => False

/-- Every directed edge strictly increases the stage rank. -/
theorem causalEdge_strict_rank_mono {s t : CellularSheafStage} (h : causalEdge s t) :
    rank s < rank t := by
  cases s <;> cases t <;> simp_all [causalEdge, rank]

/-- The ranked causal edge relation is irreflexive (acyclic). -/
theorem causalEdge_irrefl (s : CellularSheafStage) : ¬ causalEdge s s := by
  intro h
  exact Nat.lt_irrefl (rank s) (causalEdge_strict_rank_mono h)

end CellularSheafStage

/-! ### 2. Stage D₁₆ (`S₁ → S₇`): Core Cellular Sheaf Operator Definitions & Lemmas -/

variable {B : Type*} [Ring B]

/-- **Archetypes S₁ & S₂ (`sheafCoboundary0`)**:
Given an idempotent `P` splitting the operator carrier into source corner `P` and target corner `1 - P`,
and arbitrary restriction operators `R_u, R_v : B`, the degree-0 sheaf coboundary
operator is `δ_F = R_u * P - R_v * (1 - P)`. -/
def sheafCoboundary0 (P R_u R_v : B) : B :=
  R_u * P - R_v * (1 - P)

/-- Symmetric degree-0 sheaf coboundary `δ_F^+ = R_u * P + R_v * (1 - P)`. -/
def sheafCoboundary0Sym (P R_u R_v : B) : B :=
  sheafCoboundary0 P R_u (-R_v)

/-- **Archetype S₁₂ (`sheafCurvature2`)**:
2-cell cochain curvature operator `F = d₁ * d₀` measuring the failure of a 2-step
cochain complex to be flat. -/
def sheafCurvature2 (d₀ d₁ : B) : B := d₁ * d₀

/-- Recursive Mandelbrot defect tower `mandelbrotTower n X = idempotencyDefect^[n + 1] X`. -/
def mandelbrotTower : ℕ → B → B
  | 0, X => idempotencyDefect X
  | n + 1, X => idempotencyDefect (mandelbrotTower n X)

/-- `mandelbrotTower n X` coincides with the `(n + 1)`-fold iterate `idempotencyDefect^[n + 1] X`. -/
theorem mandelbrotTower_eq_idempotencyDefect_iterate (n : ℕ) (X : B) :
    mandelbrotTower n X = idempotencyDefect^[n + 1] X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mandelbrotTower, ih, Function.iterate_succ_apply']

/-- **Lemma S₂.1 (`sheafCoboundary0_eq_zero_of_aligned`)**:
Any element `X : B` whose stalk projections satisfy `R_u * (P * X) = R_v * ((1 - P) * X)`
lies in the kernel of `sheafCoboundary0 P R_u R_v * ·`. -/
theorem sheafCoboundary0_eq_zero_of_aligned {P R_u R_v X : B}
    (hAlign : R_u * (P * X) = R_v * ((1 - P) * X)) :
    sheafCoboundary0 P R_u R_v * X = 0 := by
  unfold sheafCoboundary0
  rw [sub_mul, mul_assoc, mul_assoc, hAlign, sub_self]

/-- **Lemma S₅.0 (`sheafCoboundary0_gauge_covariant`)**:
Left-multiplying both restriction operators by `U : B` transforms `sheafCoboundary0`
covariantly on the left: `δ_{U F} = U * δ_F`. -/
theorem sheafCoboundary0_gauge_covariant (P R_u R_v U : B) :
    sheafCoboundary0 P (U * R_u) (U * R_v) = U * sheafCoboundary0 P R_u R_v := by
  unfold sheafCoboundary0
  noncomm_ring

variable [StarRing B]

/-- **Archetype S₃ (`sheafLaplacian0`)**:
Degree-0 operator sheaf Laplacian `L_F = (δ_F)⋆ * δ_F`. -/
def sheafLaplacian0 (P R_u R_v : B) : B :=
  star (sheafCoboundary0 P R_u R_v) * sheafCoboundary0 P R_u R_v

/-- Symmetric degree-0 sheaf Laplacian `L_F^+ = (δ_F^+)⋆ * δ_F^+`. -/
def sheafLaplacian0Sym (P R_u R_v : B) : B :=
  sheafLaplacian0 P R_u (-R_v)

/-- `(1, 1)` diagonal Peirce block `P * R_u⋆ * R_u * P` of `sheafLaplacian0`. -/
def sheafBlock11 (P R_u : B) : B := P * star R_u * R_u * P

/-- `(0, 0)` diagonal Peirce block `(1 - P) * R_v⋆ * R_v * (1 - P)` of `sheafLaplacian0`. -/
def sheafBlock00 (P R_v : B) : B := (1 - P) * star R_v * R_v * (1 - P)

/-- `(1, 0)` off-diagonal Peirce block `-(P * R_u⋆ * R_v * (1 - P))` of `sheafLaplacian0`. -/
def sheafBlock10 (P R_u R_v : B) : B := -(P * star R_u * R_v * (1 - P))

/-- `(0, 1)` off-diagonal Peirce block `-((1 - P) * R_v⋆ * R_u * P)` of `sheafLaplacian0`. -/
def sheafBlock01 (P R_u R_v : B) : B := -((1 - P) * star R_v * R_u * P)

/-- **Archetype S₄ (`sheafDirichletForm`, `sheafDiffusionOp`)**:
Operator-valued Dirichlet quadratic form `X⋆ * L_F * X` and negative-Laplacian
diffusion operator `-(L_F * X)`. -/
def sheafDirichletForm (P R_u R_v X : B) : B :=
  star X * sheafLaplacian0 P R_u R_v * X

def sheafDiffusionOp (P R_u R_v X : B) : B :=
  -(sheafLaplacian0 P R_u R_v * X)

/-- **Archetype S₆ (`sheafHodgeDown`, `sheafHodgeUp`, `sheafHodgeLaplacian`)**:
Lower coboundary Laplacian `d₀ * d₀⋆`, upper coboundary Laplacian `d₁⋆ * d₁`,
and total degree-1 sheaf Hodge Laplacian `Δ₁ = d₀ * d₀⋆ + d₁⋆ * d₁`. -/
def sheafHodgeDown (d₀ : B) : B := d₀ * star d₀
def sheafHodgeUp (d₁ : B) : B := star d₁ * d₁
def sheafHodgeLaplacian (d₀ d₁ : B) : B := sheafHodgeDown d₀ + sheafHodgeUp d₁

/-- **Archetype S₉ (`sheafEdgeLaplacian1`)**:
Operator `L_F^(1) = δ_F * (δ_F)⋆`. -/
def sheafEdgeLaplacian1 (P R_u R_v : B) : B :=
  sheafHodgeDown (sheafCoboundary0 P R_u R_v)

/-- **Archetype S₁₂ (`sheafWeitzenboeckDefect`)**:
Hodge–Weitzenböck curvature defect `d₁⋆ * F * d₀⋆ + d₀ * F⋆ * d₁` of a curved 2-step
cochain pair `(d₀, d₁)` with `F = d₁ * d₀`. -/
def sheafWeitzenboeckDefect (d₀ d₁ : B) : B :=
  star d₁ * sheafCurvature2 d₀ d₁ * star d₀ + d₀ * star (sheafCurvature2 d₀ d₁) * d₁

/-- `sheafLaplacian0 P R_u R_v` is unconditionally self-adjoint in any `StarRing`. -/
theorem star_sheafLaplacian0 (P R_u R_v : B) :
    star (sheafLaplacian0 P R_u R_v) = sheafLaplacian0 P R_u R_v := by
  unfold sheafLaplacian0
  rw [star_mul, star_star]

/-- For a self-adjoint element `P` (`star P = P`), `sheafLaplacian0 P R_u R_v`
decomposes into the sum of its four Peirce blocks. -/
theorem sheafLaplacian0_block_decomp {P R_u R_v : B} (hPsym : star P = P) :
    sheafLaplacian0 P R_u R_v =
      sheafBlock11 P R_u + sheafBlock10 P R_u R_v +
      sheafBlock01 P R_u R_v + sheafBlock00 P R_v := by
  unfold sheafLaplacian0 sheafCoboundary0 sheafBlock11 sheafBlock10 sheafBlock01 sheafBlock00
  rw [star_sub, star_mul, star_mul, star_sub, star_one, hPsym]
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-- **Lemma S₃.1 (`sheafLaplacian0_block_decomp_and_self_adjoint`)**:
Combined self-adjointness and `2 × 2` Peirce block decomposition of `sheafLaplacian0`. -/
theorem sheafLaplacian0_block_decomp_and_self_adjoint {P R_u R_v : B} (hPsym : star P = P) :
    star (sheafLaplacian0 P R_u R_v) = sheafLaplacian0 P R_u R_v ∧
    sheafLaplacian0 P R_u R_v =
      sheafBlock11 P R_u + sheafBlock10 P R_u R_v +
      sheafBlock01 P R_u R_v + sheafBlock00 P R_v :=
  ⟨star_sheafLaplacian0 P R_u R_v, sheafLaplacian0_block_decomp hPsym⟩

/-- `sheafDirichletForm P R_u R_v X` factors as `star (δ_F * X) * (δ_F * X)`. -/
theorem sheafDirichletForm_eq_star_coboundary_mul (P R_u R_v X : B) :
    sheafDirichletForm P R_u R_v X =
      star (sheafCoboundary0 P R_u R_v * X) * (sheafCoboundary0 P R_u R_v * X) := by
  unfold sheafDirichletForm sheafLaplacian0
  rw [star_mul]
  noncomm_ring

/-- **Lemma S₄.1 (`sheafDirichlet_and_diffusion_equilibrium`)**:
1. `sheafDirichletForm` factors as the star-square of `sheafCoboundary0 P R_u R_v * X`.
2. Every aligned element (`R_u * (P * X) = R_v * ((1 - P) * X)`, the global-section analogue)
   is annihilated by
   `sheafLaplacian0`, `sheafDirichletForm`, and `sheafDiffusionOp`. -/
theorem sheafDirichlet_and_diffusion_equilibrium {P R_u R_v X : B} :
    sheafDirichletForm P R_u R_v X =
      star (sheafCoboundary0 P R_u R_v * X) * (sheafCoboundary0 P R_u R_v * X) ∧
    (R_u * (P * X) = R_v * ((1 - P) * X) →
      sheafLaplacian0 P R_u R_v * X = 0 ∧
      sheafDirichletForm P R_u R_v X = 0 ∧
      sheafDiffusionOp P R_u R_v X = 0) := by
  have hDir := sheafDirichletForm_eq_star_coboundary_mul P R_u R_v X
  refine ⟨hDir, fun hAlign => ?_⟩
  have hCob0 : sheafCoboundary0 P R_u R_v * X = 0 :=
    sheafCoboundary0_eq_zero_of_aligned hAlign
  have hLap0 : sheafLaplacian0 P R_u R_v * X = 0 := by
    unfold sheafLaplacian0
    rw [mul_assoc, hCob0, mul_zero]
  refine ⟨hLap0, ?_, ?_⟩
  · rw [hDir, hCob0, star_zero, zero_mul]
  · unfold sheafDiffusionOp
    rw [hLap0, neg_zero]

/-- **Lemma S₅.1 (`sheafLaplacian0_gauge_invariance`)**:
Under a left-isometric operator `U` (`star U * U = 1`):
1. `sheafCoboundary0` transforms covariantly (`δ_{U F} = U * δ_F`);
2. `sheafLaplacian0` is strictly invariant (`L_{U F} = L_F`);
3. `sheafDirichletForm` is strictly invariant (`E_{U F}(X) = E_F(X)`). -/
theorem sheafLaplacian0_gauge_invariance {P R_u R_v U X : B} (hU : star U * U = 1) :
    sheafCoboundary0 P (U * R_u) (U * R_v) = U * sheafCoboundary0 P R_u R_v ∧
    sheafLaplacian0 P (U * R_u) (U * R_v) = sheafLaplacian0 P R_u R_v ∧
    sheafDirichletForm P (U * R_u) (U * R_v) X = sheafDirichletForm P R_u R_v X := by
  have hCob := sheafCoboundary0_gauge_covariant P R_u R_v U
  have hLap : sheafLaplacian0 P (U * R_u) (U * R_v) = sheafLaplacian0 P R_u R_v := by
    unfold sheafLaplacian0
    rw [hCob, star_mul, mul_assoc, ← mul_assoc (star U) U, hU, one_mul]
  refine ⟨hCob, hLap, ?_⟩
  unfold sheafDirichletForm
  rw [hLap]

/-- **Lemma S₆.1 (`sheafHodgeLaplacian_properties`)**:
For composable coboundary operators `d₀, d₁ : B` satisfying `d₁ * d₀ = 0`:
1. `star d₀ * star d₁ = 0`;
2. `sheafHodgeLaplacian d₀ d₁` is self-adjoint;
3. `sheafHodgeUp d₁ * sheafHodgeDown d₀ = 0` and `sheafHodgeDown d₀ * sheafHodgeUp d₁ = 0`;
4. `(sheafHodgeLaplacian d₀ d₁)² = (sheafHodgeDown d₀)² + (sheafHodgeUp d₁)²`. -/
theorem sheafHodgeLaplacian_properties {d₀ d₁ : B} (hd : d₁ * d₀ = 0) :
    star d₀ * star d₁ = 0 ∧
    star (sheafHodgeLaplacian d₀ d₁) = sheafHodgeLaplacian d₀ d₁ ∧
    sheafHodgeUp d₁ * sheafHodgeDown d₀ = 0 ∧
    sheafHodgeDown d₀ * sheafHodgeUp d₁ = 0 ∧
    sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
      sheafHodgeDown d₀ * sheafHodgeDown d₀ + sheafHodgeUp d₁ * sheafHodgeUp d₁ := by
  have hStarD : star d₀ * star d₁ = 0 := by
    rw [← star_mul, hd, star_zero]
  have hUpDown : sheafHodgeUp d₁ * sheafHodgeDown d₀ = 0 := by
    unfold sheafHodgeUp sheafHodgeDown
    rw [mul_assoc, ← mul_assoc d₁ d₀, hd, zero_mul, mul_zero]
  have hDownUp : sheafHodgeDown d₀ * sheafHodgeUp d₁ = 0 := by
    unfold sheafHodgeUp sheafHodgeDown
    rw [mul_assoc, ← mul_assoc (star d₀) (star d₁), hStarD, zero_mul, mul_zero]
  refine ⟨hStarD, ?_, hUpDown, hDownUp, ?_⟩
  · unfold sheafHodgeLaplacian sheafHodgeDown sheafHodgeUp
    rw [star_add, star_mul, star_mul, star_star, star_star]
  · unfold sheafHodgeLaplacian
    rw [add_mul, mul_add, mul_add, hUpDown, hDownUp, add_zero, zero_add]

/-- **Lemma S₇.1 (`sheaf_to_tetraktys_bridge`)**:
When the vertex-to-edge restriction operators are chosen as the Peirce corners
`R_u = coneMinus P C = (1 - P) C P` and `R_v = conePlus P A = P A (1 - P)` for a
self-adjoint idempotent `P` (`P * P = P`, `star P = P`):
1. `sheafCoboundary0 P (coneMinus P C) (conePlus P A) = -genJ P A C`;
2. `sheafCoboundary0 P (coneMinus P C) (-conePlus P A) = genPhi P A C`;
3. For `C = star A`, `sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A)`. -/
theorem sheaf_to_tetraktys_bridge {P : B} (hP : P * P = P) (hPsym : star P = P) (A C : B) :
    sheafCoboundary0 P (coneMinus P C) (conePlus P A) = -genJ P A C ∧
    sheafCoboundary0 P (coneMinus P C) (-conePlus P A) = genPhi P A C ∧
    sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A) := by
  have hCobJ : ∀ C' : B, sheafCoboundary0 P (coneMinus P C') (conePlus P A) = -genJ P A C' :=
    fun C' => by
      unfold sheafCoboundary0
      peirce_nf hP
  have hCobPhi : sheafCoboundary0 P (coneMinus P C) (-conePlus P A) = genPhi P A C := by
    unfold sheafCoboundary0
    peirce_nf hP
  refine ⟨hCobJ C, hCobPhi, ?_⟩
  have hCobStar :
      sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) =
        -genJ P A (star A) := hCobJ (star A)
  unfold sheafLaplacian0
  rw [hCobStar, star_neg, star_genJ hPsym]
  peirce_nf hP

/-- **Stage D₁₆ (`stage_D16_cellular_sheaf_operator_master_synthesis`)**:
Unifies the seven sheaf-inspired operator archetypes (`S₁ → S₇`) over
`[Ring B] [StarRing B]`. -/
theorem stage_D16_cellular_sheaf_operator_master_synthesis
    {P R_u R_v U X d₀ d₁ A C : B}
    (hP : P * P = P) (hPsym : star P = P)
    (hU : star U * U = 1) (hd : d₁ * d₀ = 0) :
    star (sheafLaplacian0 P R_u R_v) = sheafLaplacian0 P R_u R_v ∧
    sheafLaplacian0 P R_u R_v =
      sheafBlock11 P R_u + sheafBlock10 P R_u R_v +
      sheafBlock01 P R_u R_v + sheafBlock00 P R_v ∧
    sheafDirichletForm P R_u R_v X =
      star (sheafCoboundary0 P R_u R_v * X) * (sheafCoboundary0 P R_u R_v * X) ∧
    (R_u * (P * X) = R_v * ((1 - P) * X) →
      sheafLaplacian0 P R_u R_v * X = 0 ∧
      sheafDirichletForm P R_u R_v X = 0 ∧
      sheafDiffusionOp P R_u R_v X = 0) ∧
    sheafCoboundary0 P (U * R_u) (U * R_v) = U * sheafCoboundary0 P R_u R_v ∧
    sheafLaplacian0 P (U * R_u) (U * R_v) = sheafLaplacian0 P R_u R_v ∧
    sheafDirichletForm P (U * R_u) (U * R_v) X = sheafDirichletForm P R_u R_v X ∧
    star (sheafHodgeLaplacian d₀ d₁) = sheafHodgeLaplacian d₀ d₁ ∧
    sheafHodgeUp d₁ * sheafHodgeDown d₀ = 0 ∧
    sheafHodgeDown d₀ * sheafHodgeUp d₁ = 0 ∧
    sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
      sheafHodgeDown d₀ * sheafHodgeDown d₀ + sheafHodgeUp d₁ * sheafHodgeUp d₁ ∧
    sheafCoboundary0 P (coneMinus P C) (conePlus P A) = -genJ P A C ∧
    sheafCoboundary0 P (coneMinus P C) (-conePlus P A) = genPhi P A C ∧
    sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A) := by
  rcases sheafLaplacian0_block_decomp_and_self_adjoint (R_u := R_u) (R_v := R_v) hPsym with
    ⟨hSym, hBlk⟩
  rcases sheafDirichlet_and_diffusion_equilibrium (P := P) (R_u := R_u) (R_v := R_v) (X := X) with
    ⟨hDir, hEq⟩
  rcases sheafLaplacian0_gauge_invariance (P := P) (R_u := R_u) (R_v := R_v) (X := X) hU with
    ⟨hGCob, hGLap, hGDir⟩
  rcases sheafHodgeLaplacian_properties hd with ⟨_, hHSym, hHUpDown, hHDownUp, hHSq⟩
  rcases sheaf_to_tetraktys_bridge hP hPsym A C with ⟨hBrJ, hBrPhi, hBrV⟩
  exact ⟨hSym, hBlk, hDir, hEq, hGCob, hGLap, hGDir, hHSym, hHUpDown, hHDownUp, hHSq,
    hBrJ, hBrPhi, hBrV⟩

/-! ### 3. Stage D₁₇ (`S₈ → S₁₁`): Split-Complex Block Separation, Edge-Stalk Laplacian & Horizon Normality -/

/-- **Lemma S₈.1 (`sheafLaplacian0_split_complex_block_separation`)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `R_u, R_v : B`:
1. Right-multiplication by `invS P` intertwines the skew and symmetric sheaf coboundaries:
   `sheafCoboundary0 P R_u R_v * invS P = sheafCoboundary0Sym P R_u R_v`.
2. Conjugation by `invS P` maps `sheafLaplacian0` to `sheafLaplacian0Sym`:
   `invS P * sheafLaplacian0 P R_u R_v * invS P = sheafLaplacian0Sym P R_u R_v`.
3. Adding `L_F + L_F^+` isolates twice the diagonal stalk self-comparison blocks (`Block₁₁ + Block₀₀`).
4. Subtracting `L_F - L_F^+` isolates twice the off-diagonal transport blocks (`Block₁₀ + Block₀₁`). -/
theorem sheafLaplacian0_split_complex_block_separation
    {P : B} (hP : P * P = P) (hPsym : star P = P) (R_u R_v : B) :
    sheafCoboundary0 P R_u R_v * invS P = sheafCoboundary0Sym P R_u R_v ∧
    invS P * sheafLaplacian0 P R_u R_v * invS P = sheafLaplacian0Sym P R_u R_v ∧
    sheafLaplacian0 P R_u R_v + sheafLaplacian0Sym P R_u R_v =
      (2 : ℤ) • (sheafBlock11 P R_u + sheafBlock00 P R_v) ∧
    sheafLaplacian0 P R_u R_v - sheafLaplacian0Sym P R_u R_v =
      (2 : ℤ) • (sheafBlock10 P R_u R_v + sheafBlock01 P R_u R_v) := by
  have hCob : sheafCoboundary0 P R_u R_v * invS P = sheafCoboundary0Sym P R_u R_v := by
    unfold sheafCoboundary0Sym sheafCoboundary0
    peirce_nf hP
  refine ⟨hCob, ?_, ?_, ?_⟩
  · change invS P * (star (sheafCoboundary0 P R_u R_v) * sheafCoboundary0 P R_u R_v) * invS P =
      star (sheafCoboundary0Sym P R_u R_v) * sheafCoboundary0Sym P R_u R_v
    rw [← hCob, star_mul, star_invS hPsym]
    noncomm_ring
  · unfold sheafLaplacian0Sym
    rw [sheafLaplacian0_block_decomp hPsym, sheafLaplacian0_block_decomp hPsym]
    unfold sheafBlock11 sheafBlock00 sheafBlock10 sheafBlock01
    rw [star_neg]
    simp only [neg_mul, mul_neg, neg_neg, two_zsmul]
    abel
  · unfold sheafLaplacian0Sym
    rw [sheafLaplacian0_block_decomp hPsym, sheafLaplacian0_block_decomp hPsym]
    unfold sheafBlock11 sheafBlock00 sheafBlock10 sheafBlock01
    rw [star_neg]
    simp only [neg_mul, mul_neg, neg_neg, two_zsmul]
    abel

/-- **Lemma S₉.1 (`sheafEdgeLaplacian1_structure_and_intertwining`)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `R_u, R_v, U : B`:
1. **Cross-Term Vanishing in the Edge Stalk:**
   `sheafEdgeLaplacian1 P R_u R_v = R_u * P * star R_u + R_v * (1 - P) * star R_v`.
2. **Exact Sign-Independence Under `R_v ↦ -R_v`:**
   `sheafEdgeLaplacian1 P R_u (-R_v) = sheafEdgeLaplacian1 P R_u R_v`.
3. **Universal Vertex–Edge Supersymmetric Intertwining:**
   `sheafCoboundary0 P R_u R_v * sheafLaplacian0 P R_u R_v = sheafEdgeLaplacian1 P R_u R_v * sheafCoboundary0 P R_u R_v`
   and `sheafLaplacian0 P R_u R_v * star (sheafCoboundary0 P R_u R_v) = star (sheafCoboundary0 P R_u R_v) * sheafEdgeLaplacian1 P R_u R_v`.
4. **Edge-Stalk Gauge Covariance (`L_{U F}^(1) = U * L_F^(1) * star U`):**
   `sheafEdgeLaplacian1 P (U * R_u) (U * R_v) = U * sheafEdgeLaplacian1 P R_u R_v * star U`. -/
theorem sheafEdgeLaplacian1_structure_and_intertwining
    {P : B} (hP : P * P = P) (hPsym : star P = P) (R_u R_v U : B) :
    sheafEdgeLaplacian1 P R_u R_v = R_u * P * star R_u + R_v * (1 - P) * star R_v ∧
    sheafEdgeLaplacian1 P R_u (-R_v) = sheafEdgeLaplacian1 P R_u R_v ∧
    sheafCoboundary0 P R_u R_v * sheafLaplacian0 P R_u R_v =
      sheafEdgeLaplacian1 P R_u R_v * sheafCoboundary0 P R_u R_v ∧
    sheafLaplacian0 P R_u R_v * star (sheafCoboundary0 P R_u R_v) =
      star (sheafCoboundary0 P R_u R_v) * sheafEdgeLaplacian1 P R_u R_v ∧
    sheafEdgeLaplacian1 P (U * R_u) (U * R_v) =
      U * sheafEdgeLaplacian1 P R_u R_v * star U := by
  have hFormula : ∀ Rv : B,
      sheafEdgeLaplacian1 P R_u Rv = R_u * P * star R_u + Rv * (1 - P) * star Rv :=
    fun Rv => by
      unfold sheafEdgeLaplacian1 sheafHodgeDown sheafCoboundary0
      rw [star_sub, star_mul, star_mul, star_sub, star_one, hPsym]
      peirce_nf hP
  refine ⟨hFormula R_v, ?_, ?_, ?_, ?_⟩
  · rw [hFormula (-R_v), hFormula R_v, star_neg]
    simp only [neg_mul, mul_neg, neg_neg]
  · unfold sheafLaplacian0 sheafEdgeLaplacian1 sheafHodgeDown
    rw [mul_assoc]
  · unfold sheafLaplacian0 sheafEdgeLaplacian1 sheafHodgeDown
    rw [mul_assoc]
  · unfold sheafEdgeLaplacian1 sheafHodgeDown
    rw [sheafCoboundary0_gauge_covariant, star_mul]
    noncomm_ring

/-- **Lemma S₁₀.1 (`sheaf_horizon_normality_and_chiral_cross_coboundary`)**:
At the Peirce horizon `R_u = coneMinus P (star A)` and `R_v = conePlus P A` (`P * P = P`, `star P = P`):
1. The 1-cell edge Laplacian `sheafEdgeLaplacian1` equals `genV P A (star A)` and coincides with
   the 0-cell vertex Laplacian `sheafLaplacian0`, so `comm (star δ_F) δ_F = 0` (exact normality).
2. The symmetric and skew sheaf coboundaries pair to generate the chiral curvature `genSig P A (star A)`:
   `star (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) * sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) = genSig P A (star A)`
   and `star (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)) * sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A) = genSig P A (star A)`. -/
theorem sheaf_horizon_normality_and_chiral_cross_coboundary
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) :
    sheafEdgeLaplacian1 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A) ∧
    comm (star (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)))
         (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)) = 0 ∧
    star (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) *
      sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) = genSig P A (star A) ∧
    star (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)) *
      sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A) = genSig P A (star A) := by
  rcases sheaf_to_tetraktys_bridge hP hPsym A (star A) with ⟨hCobJ, hCobPhi, hLapV⟩
  have hEdgeV : sheafEdgeLaplacian1 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A) := by
    unfold sheafEdgeLaplacian1 sheafHodgeDown
    rw [hCobJ, star_neg, star_genJ hPsym, neg_neg]
    peirce_nf hP
  refine ⟨hEdgeV, ?_, ?_, ?_⟩
  · unfold comm
    change sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) -
           sheafEdgeLaplacian1 P (coneMinus P (star A)) (conePlus P A) = 0
    rw [hLapV, hEdgeV, sub_self]
  · unfold sheafCoboundary0Sym
    rw [hCobPhi, hCobJ, star_genPhi hPsym]
    peirce_nf hP
  · unfold sheafCoboundary0Sym
    rw [hCobPhi, hCobJ, star_neg, star_genJ hPsym, neg_neg]
    peirce_nf hP

/-- **Lemma S₁₁.1 (`sheafHodge_concrete_horizon_instantiation`)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `A : B`, setting
`d₀ = conePlus P A` and `d₁ = conePlus P A`:
1. Satisfies the cochain complex boundary law `d₁ * d₀ = 0` unconditionally.
2. Evaluates `sheafHodgeDown (conePlus P A) = qgtPlus P A (star A)`.
3. Evaluates `sheafHodgeUp (conePlus P A) = qgtMinus P A (star A)`.
4. Evaluates `sheafHodgeLaplacian (conePlus P A) (conePlus P A) = genV P A (star A)` and
   `sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A) = genSig P A (star A)`. -/
theorem sheafHodge_concrete_horizon_instantiation
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) :
    conePlus P A * conePlus P A = 0 ∧
    sheafHodgeDown (conePlus P A) = qgtPlus P A (star A) ∧
    sheafHodgeUp (conePlus P A) = qgtMinus P A (star A) ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) = genV P A (star A) ∧
    sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A) = genSig P A (star A) := by
  have hDown : sheafHodgeDown (conePlus P A) = qgtPlus P A (star A) := by
    unfold sheafHodgeDown qgtPlus
    rw [star_conePlus hPsym]
  have hUp : sheafHodgeUp (conePlus P A) = qgtMinus P A (star A) := by
    unfold sheafHodgeUp qgtMinus
    rw [star_conePlus hPsym]
  refine ⟨by peirce_nf hP, hDown, hUp, ?_, ?_⟩
  · unfold sheafHodgeLaplacian genV anticomm qgtPlus qgtMinus at *
    rw [hDown, hUp]
  · unfold genSig comm qgtPlus qgtMinus at *
    rw [hDown, hUp]

/-- **Stage D₁₇ (`stage_D17_extended_cellular_sheaf_hodge_and_tetraktys_synthesis`)**:
Unifies Archetypes `S₈ → S₁₁` over `[Ring B] [StarRing B]`. -/
theorem stage_D17_extended_cellular_sheaf_hodge_and_tetraktys_synthesis
    {P R_u R_v U A : B} (hP : P * P = P) (hPsym : star P = P) :
    sheafCoboundary0 P R_u R_v * invS P = sheafCoboundary0Sym P R_u R_v ∧
    invS P * sheafLaplacian0 P R_u R_v * invS P = sheafLaplacian0Sym P R_u R_v ∧
    sheafLaplacian0 P R_u R_v + sheafLaplacian0Sym P R_u R_v =
      (2 : ℤ) • (sheafBlock11 P R_u + sheafBlock00 P R_v) ∧
    sheafLaplacian0 P R_u R_v - sheafLaplacian0Sym P R_u R_v =
      (2 : ℤ) • (sheafBlock10 P R_u R_v + sheafBlock01 P R_u R_v) ∧
    sheafEdgeLaplacian1 P R_u R_v = R_u * P * star R_u + R_v * (1 - P) * star R_v ∧
    sheafEdgeLaplacian1 P R_u (-R_v) = sheafEdgeLaplacian1 P R_u R_v ∧
    sheafCoboundary0 P R_u R_v * sheafLaplacian0 P R_u R_v =
      sheafEdgeLaplacian1 P R_u R_v * sheafCoboundary0 P R_u R_v ∧
    sheafEdgeLaplacian1 P (U * R_u) (U * R_v) =
      U * sheafEdgeLaplacian1 P R_u R_v * star U ∧
    comm (star (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)))
         (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)) = 0 ∧
    star (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) *
      sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) = genSig P A (star A) ∧
    conePlus P A * conePlus P A = 0 ∧
    sheafHodgeDown (conePlus P A) = qgtPlus P A (star A) ∧
    sheafHodgeUp (conePlus P A) = qgtMinus P A (star A) ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) = genV P A (star A) ∧
    sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A) = genSig P A (star A) := by
  rcases sheafLaplacian0_split_complex_block_separation hP hPsym R_u R_v with
    ⟨hSC1, hSC2, hSC3, hSC4⟩
  rcases sheafEdgeLaplacian1_structure_and_intertwining hP hPsym R_u R_v U with
    ⟨hEd1, hEd2, hEd3, _, hEd5⟩
  rcases sheaf_horizon_normality_and_chiral_cross_coboundary hP hPsym A with
    ⟨_, hNorm, hSig1, _⟩
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym A with
    ⟨hC1, hC2, hC3, hC4, hC5⟩
  exact ⟨hSC1, hSC2, hSC3, hSC4, hEd1, hEd2, hEd3, hEd5, hNorm, hSig1, hC1, hC2, hC3, hC4, hC5⟩

/-! ### 4. Stage D₁₈ (`S₁₂ → S₁₅`): Curved Sheaf Weitzenböck Defect, Bianchi Identity & Fractal Sheet Hodge Filtering -/

/-- **Lemma S₁₂.1 (`curved_sheaf_weitzenboeck_identity`)**:
For any operators `d₀, d₁ : B` (without assuming `d₁ * d₀ = 0`):
1. `sheafHodgeUp d₁ * sheafHodgeDown d₀ = star d₁ * sheafCurvature2 d₀ d₁ * star d₀`.
2. `sheafHodgeDown d₀ * sheafHodgeUp d₁ = d₀ * star (sheafCurvature2 d₀ d₁) * d₁`.
3. The square of the Sheaf Hodge Laplacian `Δ₁ = d₀ d₀⋆ + d₁⋆ d₁` decomposes into the
   unmixed squares `Δ_down² + Δ_up²` plus the exact Weitzenböck curvature defect:
   `Δ₁ * Δ₁ = Δ_down * Δ_down + Δ_up * Δ_up + sheafWeitzenboeckDefect d₀ d₁`. -/
theorem curved_sheaf_weitzenboeck_identity (d₀ d₁ : B) :
    sheafHodgeUp d₁ * sheafHodgeDown d₀ = star d₁ * sheafCurvature2 d₀ d₁ * star d₀ ∧
    sheafHodgeDown d₀ * sheafHodgeUp d₁ = d₀ * star (sheafCurvature2 d₀ d₁) * d₁ ∧
    sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
      sheafHodgeDown d₀ * sheafHodgeDown d₀ +
      sheafHodgeUp d₁ * sheafHodgeUp d₁ +
      sheafWeitzenboeckDefect d₀ d₁ := by
  have hUpDown : sheafHodgeUp d₁ * sheafHodgeDown d₀ =
      star d₁ * sheafCurvature2 d₀ d₁ * star d₀ := by
    unfold sheafHodgeUp sheafHodgeDown sheafCurvature2
    simp only [mul_assoc]
  have hDownUp : sheafHodgeDown d₀ * sheafHodgeUp d₁ =
      d₀ * star (sheafCurvature2 d₀ d₁) * d₁ := by
    unfold sheafHodgeDown sheafHodgeUp sheafCurvature2
    rw [star_mul]
    simp only [mul_assoc]
  refine ⟨hUpDown, hDownUp, ?_⟩
  unfold sheafHodgeLaplacian sheafWeitzenboeckDefect
  rw [add_mul, mul_add, mul_add, hUpDown, hDownUp]
  abel

/-- **Lemma S₁₃.1 (`curved_sheaf_bianchi_identity`)**:
For any three consecutive coboundary operators `d₀, d₁, d₂ : B`:
1. `d₂ * sheafCurvature2 d₀ d₁ = sheafCurvature2 d₁ d₂ * d₀`.
2. Their adjoint curvatures satisfy `star d₀ * star (sheafCurvature2 d₁ d₂) = star (sheafCurvature2 d₀ d₁) * star d₂`. -/
theorem curved_sheaf_bianchi_identity (d₀ d₁ d₂ : B) :
    d₂ * sheafCurvature2 d₀ d₁ = sheafCurvature2 d₁ d₂ * d₀ ∧
    star d₀ * star (sheafCurvature2 d₁ d₂) = star (sheafCurvature2 d₀ d₁) * star d₂ := by
  constructor
  · unfold sheafCurvature2
    rw [mul_assoc]
  · unfold sheafCurvature2
    rw [star_mul, star_mul, mul_assoc]

omit [StarRing B] in
/-- **Lemma S₁₄.0 (`sheafCoboundary0_swapped_cones_eq_zero`)**:
Swapping the horizon restriction cones (`R_u = conePlus P A`, `R_v = coneMinus P C`)
yields an identically vanishing degree-0 coboundary `sheafCoboundary0 P (conePlus P A) (coneMinus P C) = 0`. -/
theorem sheafCoboundary0_swapped_cones_eq_zero {P : B} (hP : P * P = P) (A C : B) :
    sheafCoboundary0 P (conePlus P A) (coneMinus P C) = 0 := by
  unfold sheafCoboundary0
  peirce_nf hP

omit [StarRing B] in
/-- **Lemma S₁₄.1 (`mandelbrotTower_peirce_absorption`)**:
For any idempotent `P` (`P * P = P`), any `A, C : B`, and any vertical Mandelbrot depth `n : ℕ`:
1. The upper fractal sheet `X_n = mandelbrotTower n (qgtPlus P A C)` lies in `P B P`:
   `P * X_n = X_n` and `X_n * P = X_n`.
2. The lower fractal sheet `Y_n = mandelbrotTower n (qgtMinus P A C)` lies in `(1 - P) B (1 - P)`:
   `(1 - P) * Y_n = Y_n` and `Y_n * (1 - P) = Y_n`. -/
theorem mandelbrotTower_peirce_absorption {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    P * mandelbrotTower n (qgtPlus P A C) = mandelbrotTower n (qgtPlus P A C) ∧
    mandelbrotTower n (qgtPlus P A C) * P = mandelbrotTower n (qgtPlus P A C) ∧
    (1 - P) * mandelbrotTower n (qgtMinus P A C) = mandelbrotTower n (qgtMinus P A C) ∧
    mandelbrotTower n (qgtMinus P A C) * (1 - P) = mandelbrotTower n (qgtMinus P A C) := by
  rw [mandelbrotTower_eq_idempotencyDefect_iterate, mandelbrotTower_eq_idempotencyDefect_iterate]
  exact ⟨qgtPlus_defect_iterates_left hP A C (n + 1),
         qgtPlus_defect_iterates_right hP A C (n + 1),
         qgtMinus_defect_iterates_left hP A C (n + 1),
         qgtMinus_defect_iterates_right hP A C (n + 1)⟩

/-- **Lemma S₁₅.0 (`defect_iterate_sheet_hodge_filtering`)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`), any `A : B`, and any iterate
depth `n : ℕ` (including `n = 0`), let `X_n = idempotencyDefect^[n] (qgtPlus P A (star A))` and
`Y_n = idempotencyDefect^[n] (qgtMinus P A (star A))`. Under the horizon Hodge complex `d₀ = d₁ = conePlus P A`:
1. `conePlus P A * X_n = 0` and `coneMinus P (star A) * Y_n = 0`.
2. `sheafHodgeUp (conePlus P A) * X_n = 0` and `sheafHodgeDown (conePlus P A) * Y_n = 0`.
3. `sheafHodgeLaplacian (conePlus P A) (conePlus P A) * X_n = qgtPlus P A (star A) * X_n` and
   `sheafHodgeLaplacian (conePlus P A) (conePlus P A) * Y_n = qgtMinus P A (star A) * Y_n`. -/
theorem defect_iterate_sheet_hodge_filtering
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) (n : ℕ) :
    conePlus P A * idempotencyDefect^[n] (qgtPlus P A (star A)) = 0 ∧
    coneMinus P (star A) * idempotencyDefect^[n] (qgtMinus P A (star A)) = 0 ∧
    sheafHodgeUp (conePlus P A) * idempotencyDefect^[n] (qgtPlus P A (star A)) = 0 ∧
    sheafHodgeDown (conePlus P A) * idempotencyDefect^[n] (qgtMinus P A (star A)) = 0 ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
      idempotencyDefect^[n] (qgtPlus P A (star A)) =
      qgtPlus P A (star A) * idempotencyDefect^[n] (qgtPlus P A (star A)) ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
      idempotencyDefect^[n] (qgtMinus P A (star A)) =
      qgtMinus P A (star A) * idempotencyDefect^[n] (qgtMinus P A (star A)) := by
  rcases qgt_defect_iterates_cone_relations hP A (star A) n with
    ⟨hConeX, _, _, hConeY, _, _⟩
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym A with
    ⟨_, hDown, hUp, _, _⟩
  have hUpX : sheafHodgeUp (conePlus P A) * idempotencyDefect^[n] (qgtPlus P A (star A)) = 0 := by
    rw [hUp]
    unfold qgtMinus
    rw [mul_assoc, hConeX, mul_zero]
  have hDownY : sheafHodgeDown (conePlus P A) * idempotencyDefect^[n] (qgtMinus P A (star A)) = 0 := by
    rw [hDown]
    unfold qgtPlus
    rw [mul_assoc, hConeY, mul_zero]
  refine ⟨hConeX, hConeY, hUpX, hDownY, ?_, ?_⟩
  · unfold sheafHodgeLaplacian
    rw [add_mul, hUpX, add_zero, hDown]
  · unfold sheafHodgeLaplacian
    rw [add_mul, hDownY, zero_add, hUp]

/-- **Lemma S₁₅.1 (`fractal_sheet_hodge_filtering`)**:
Specialization of `defect_iterate_sheet_hodge_filtering` to `mandelbrotTower n`. -/
theorem fractal_sheet_hodge_filtering
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) (n : ℕ) :
    conePlus P A * mandelbrotTower n (qgtPlus P A (star A)) = 0 ∧
    coneMinus P (star A) * mandelbrotTower n (qgtMinus P A (star A)) = 0 ∧
    sheafHodgeUp (conePlus P A) * mandelbrotTower n (qgtPlus P A (star A)) = 0 ∧
    sheafHodgeDown (conePlus P A) * mandelbrotTower n (qgtMinus P A (star A)) = 0 ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
      mandelbrotTower n (qgtPlus P A (star A)) =
      qgtPlus P A (star A) * mandelbrotTower n (qgtPlus P A (star A)) ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
      mandelbrotTower n (qgtMinus P A (star A)) =
      qgtMinus P A (star A) * mandelbrotTower n (qgtMinus P A (star A)) := by
  rw [mandelbrotTower_eq_idempotencyDefect_iterate, mandelbrotTower_eq_idempotencyDefect_iterate]
  exact defect_iterate_sheet_hodge_filtering hP hPsym A (n + 1)

/-- **Stage D₁₈ (`stage_D18_curved_sheaf_bianchi_and_fractal_hodge_cohomology`)**:
Unifies Archetypes `S₁₂ → S₁₅`: curved sheaf Hodge–Weitzenböck decomposition,
3-tier non-commutative Bianchi identities, and all-scale fractal Hodge sheet filtering. -/
theorem stage_D18_curved_sheaf_bianchi_and_fractal_hodge_cohomology
    {P d₀ d₁ d₂ A : B} (hP : P * P = P) (hPsym : star P = P) (n : ℕ) :
    sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
      sheafHodgeDown d₀ * sheafHodgeDown d₀ +
      sheafHodgeUp d₁ * sheafHodgeUp d₁ +
      sheafWeitzenboeckDefect d₀ d₁ ∧
    d₂ * sheafCurvature2 d₀ d₁ = sheafCurvature2 d₁ d₂ * d₀ ∧
    star d₀ * star (sheafCurvature2 d₁ d₂) = star (sheafCurvature2 d₀ d₁) * star d₂ ∧
    sheafHodgeUp (conePlus P A) * mandelbrotTower n (qgtPlus P A (star A)) = 0 ∧
    sheafHodgeDown (conePlus P A) * mandelbrotTower n (qgtMinus P A (star A)) = 0 ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
      mandelbrotTower n (qgtPlus P A (star A)) =
      qgtPlus P A (star A) * mandelbrotTower n (qgtPlus P A (star A)) ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
      mandelbrotTower n (qgtMinus P A (star A)) =
      qgtMinus P A (star A) * mandelbrotTower n (qgtMinus P A (star A)) := by
  rcases curved_sheaf_weitzenboeck_identity d₀ d₁ with ⟨_, _, hWeitz⟩
  rcases curved_sheaf_bianchi_identity d₀ d₁ d₂ with ⟨hBianchi1, hBianchi2⟩
  rcases fractal_sheet_hodge_filtering hP hPsym A n with ⟨_, _, hUpX, hDownY, hLapX, hLapY⟩
  exact ⟨hWeitz, hBianchi1, hBianchi2, hUpX, hDownY, hLapX, hLapY⟩

/-! ### Supplemental Operator Results (`S₁₆ → S₁₈`): Finite Edge-Indexed Sums and Conditional Energy Bounds

These declarations extend the preceding ranked DAG with additional operator identities; the
three supplemental labels are not nodes of `CellularSheafStage` or edges of `causalEdge`. -/

/-- **Operator family S₁₆ (`multiEdgeSheafLaplacian`, `multiEdgeDirichletForm`)**:
Finite sum `∑ e ∈ E, sheafLaplacian0 (P e) (R_u e) (R_v e)` and its associated operator
quadratic form over an index set `E : Finset ι`. This is an edge-indexed operator encoding;
no graph incidence or stalk data is defined here. -/
def multiEdgeSheafLaplacian {ι : Type*} (E : Finset ι) (P R_u R_v : ι → B) : B :=
  ∑ e ∈ E, sheafLaplacian0 (P e) (R_u e) (R_v e)

def multiEdgeDirichletForm {ι : Type*} (E : Finset ι) (P R_u R_v : ι → B) (X : B) : B :=
  star X * multiEdgeSheafLaplacian E P R_u R_v * X

/-- **Archetype S₁₈ (`sheafCurvatureEnergy`, `sheafHodgeSqForm`)**:
Operator-valued 2-cell curvature energy `X⋆ * F⋆ * F * X` (`F = d₁ * d₀`) and squared
Hodge Laplacian quadratic form `X⋆ * (Δ₁ * Δ₁) * X`. -/
def sheafCurvatureEnergy (d₀ d₁ X : B) : B :=
  star X * (star (sheafCurvature2 d₀ d₁) * sheafCurvature2 d₀ d₁) * X

def sheafHodgeSqForm (d₀ d₁ X : B) : B :=
  star X * (sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁) * X

/-- **Lemma S₁₆.1 (`multiEdgeSheafLaplacian_properties`)**:
For any finite index set `E : Finset ι` and edge-indexed operator data `(P, R_u, R_v)`:
1. `multiEdgeSheafLaplacian E P R_u R_v` is unconditionally self-adjoint.
2. `multiEdgeDirichletForm E P R_u R_v X` decomposes as the sum of edge-wise Hermitian squares
   `∑ e ∈ E, star (sheafCoboundary0 (P e) (R_u e) (R_v e) * X) * (sheafCoboundary0 (P e) (R_u e) (R_v e) * X)`.
3. Under edge-wise left-isometric gauge transformations `U : ι → B` (`∀ e ∈ E, star (U e) * U e = 1`),
   `multiEdgeSheafLaplacian` is strictly gauge-invariant.
4. Any element aligned across all indices (`∀ e ∈ E, R_u e * (P e * X) = R_v e * ((1 - P e) * X)`)
   lies in the kernel of `multiEdgeSheafLaplacian` and has zero `multiEdgeDirichletForm`. -/
theorem multiEdgeSheafLaplacian_properties
    {ι : Type*} (E : Finset ι) (P R_u R_v U : ι → B) (X : B)
    (hU : ∀ e ∈ E, star (U e) * U e = 1) :
    star (multiEdgeSheafLaplacian E P R_u R_v) = multiEdgeSheafLaplacian E P R_u R_v ∧
    multiEdgeDirichletForm E P R_u R_v X =
      ∑ e ∈ E,
        star (sheafCoboundary0 (P e) (R_u e) (R_v e) * X) *
          (sheafCoboundary0 (P e) (R_u e) (R_v e) * X) ∧
    multiEdgeSheafLaplacian E P (fun e => U e * R_u e) (fun e => U e * R_v e) =
      multiEdgeSheafLaplacian E P R_u R_v ∧
    ((∀ e ∈ E, R_u e * (P e * X) = R_v e * ((1 - P e) * X)) →
      multiEdgeSheafLaplacian E P R_u R_v * X = 0 ∧
      multiEdgeDirichletForm E P R_u R_v X = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold multiEdgeSheafLaplacian
    rw [star_sum]
    refine Finset.sum_congr rfl (fun e _ => star_sheafLaplacian0 (P e) (R_u e) (R_v e))
  · unfold multiEdgeDirichletForm multiEdgeSheafLaplacian
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    exact sheafDirichletForm_eq_star_coboundary_mul (P e) (R_u e) (R_v e) X
  · unfold multiEdgeSheafLaplacian
    refine Finset.sum_congr rfl (fun e he => ?_)
    exact (sheafLaplacian0_gauge_invariance (X := X) (hU e he)).2.1
  · intro hAlign
    have hLap0 : multiEdgeSheafLaplacian E P R_u R_v * X = 0 := by
      unfold multiEdgeSheafLaplacian
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero (fun e he => ?_)
      exact ((sheafDirichlet_and_diffusion_equilibrium
        (P := P e) (R_u := R_u e) (R_v := R_v e) (X := X)).2 (hAlign e he)).1
    refine ⟨hLap0, ?_⟩
    unfold multiEdgeDirichletForm
    rw [mul_assoc, hLap0, mul_zero]

/-- **Lemma S₁₇.1 (`sheafDirichlet_positive_state_and_faithful_kernel`)**:
Given an additive functional `τ : B →+ R₀` into a linearly ordered commutative ring `R₀`
satisfying star-positivity `∀ Y : B, 0 ≤ τ (star Y * Y)`:
1. Both the single-edge and multi-edge Dirichlet energies are non-negative:
   `0 ≤ τ (sheafDirichletForm P R_u R_v X)` and `0 ≤ τ (multiEdgeDirichletForm E P R_u R_v X)`.
2. If `τ` is faithful (`∀ Y : B, τ (star Y * Y) = 0 → Y = 0`), then the scalar Dirichlet
   energy vanishes iff the coboundary annihilates `X` (`sheafCoboundary0 P R_u R_v * X = 0`). -/
theorem sheafDirichlet_positive_state_and_faithful_kernel
    {R₀ : Type*} [CommRing R₀] [LinearOrder R₀] [IsStrictOrderedRing R₀]
    (τ : B →+ R₀) (hPos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (hFaithful : ∀ Y : B, τ (star Y * Y) = 0 → Y = 0)
    {ι : Type*} (E : Finset ι) (P_edge R_u_edge R_v_edge : ι → B)
    (P R_u R_v X : B) :
    0 ≤ τ (sheafDirichletForm P R_u R_v X) ∧
    0 ≤ τ (multiEdgeDirichletForm E P_edge R_u_edge R_v_edge X) ∧
    (τ (sheafDirichletForm P R_u R_v X) = 0 ↔ sheafCoboundary0 P R_u R_v * X = 0) := by
  have hSingle : 0 ≤ τ (sheafDirichletForm P R_u R_v X) := by
    rw [sheafDirichletForm_eq_star_coboundary_mul]
    exact hPos (sheafCoboundary0 P R_u R_v * X)
  have hMulti : 0 ≤ τ (multiEdgeDirichletForm E P_edge R_u_edge R_v_edge X) := by
    have hDecomp :
        multiEdgeDirichletForm E P_edge R_u_edge R_v_edge X =
          ∑ e ∈ E,
            star (sheafCoboundary0 (P_edge e) (R_u_edge e) (R_v_edge e) * X) *
              (sheafCoboundary0 (P_edge e) (R_u_edge e) (R_v_edge e) * X) := by
      unfold multiEdgeDirichletForm multiEdgeSheafLaplacian
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun e _ =>
        sheafDirichletForm_eq_star_coboundary_mul (P_edge e) (R_u_edge e) (R_v_edge e) X)
    rw [hDecomp, map_sum]
    exact Finset.sum_nonneg (fun e _ => hPos _)
  refine ⟨hSingle, hMulti, ?_⟩
  constructor
  · intro hZero
    rw [sheafDirichletForm_eq_star_coboundary_mul] at hZero
    exact hFaithful (sheafCoboundary0 P R_u R_v * X) hZero
  · intro hCob0
    rw [sheafDirichletForm_eq_star_coboundary_mul, hCob0, star_zero, zero_mul, map_zero]

/-- **Lemma S₁₈.1 (Curved sheaf energy and conditional coercivity consequence)**:
For any cochain operators `d₀, d₁ : B` and state `X : B`:
1. The curvature energy factors as a Hermitian square:
   `sheafCurvatureEnergy d₀ d₁ X = star (d₁ * (d₀ * X)) * (d₁ * (d₀ * X))`.
2. The squared Hodge Laplacian form factors as a Hermitian square:
   `sheafHodgeSqForm d₀ d₁ X = star (sheafHodgeLaplacian d₀ d₁ * X) * (sheafHodgeLaplacian d₀ d₁ * X)`.
3. Under a faithful positive functional `τ : B →+ R₀`, assuming `X ≠ 0` and the pointwise
   bound `m_sq * τ (star X * X) ≤ τ (sheafHodgeSqForm d₀ d₁ X)` for `0 < m_sq`, the energy is
   strictly positive and the Hodge image is nonzero. This conditional statement does not
   establish a uniform spectral bound or a Yang–Mills mass gap. -/
theorem curved_sheaf_energy_and_conditional_coercivity
    {R₀ : Type*} [CommRing R₀] [LinearOrder R₀] [IsStrictOrderedRing R₀]
    (τ : B →+ R₀) (hPos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (hFaithful : ∀ Y : B, τ (star Y * Y) = 0 → Y = 0)
    (d₀ d₁ X : B) (m_sq : R₀) :
    sheafCurvatureEnergy d₀ d₁ X = star (d₁ * (d₀ * X)) * (d₁ * (d₀ * X)) ∧
    sheafHodgeSqForm d₀ d₁ X =
      star (sheafHodgeLaplacian d₀ d₁ * X) * (sheafHodgeLaplacian d₀ d₁ * X) ∧
    0 ≤ τ (sheafCurvatureEnergy d₀ d₁ X) ∧
    0 ≤ τ (sheafHodgeSqForm d₀ d₁ X) ∧
    (0 < m_sq → X ≠ 0 → m_sq * τ (star X * X) ≤ τ (sheafHodgeSqForm d₀ d₁ X) →
      0 < τ (sheafHodgeSqForm d₀ d₁ X) ∧ sheafHodgeLaplacian d₀ d₁ * X ≠ 0) := by
  have hCurvSq : sheafCurvatureEnergy d₀ d₁ X = star (d₁ * (d₀ * X)) * (d₁ * (d₀ * X)) := by
    simp only [sheafCurvatureEnergy, sheafCurvature2, star_mul, mul_assoc]
  have hStarLap : star (sheafHodgeLaplacian d₀ d₁) = sheafHodgeLaplacian d₀ d₁ := by
    unfold sheafHodgeLaplacian sheafHodgeDown sheafHodgeUp
    rw [star_add, star_mul, star_mul, star_star, star_star]
  have hHodgeSq :
      sheafHodgeSqForm d₀ d₁ X =
        star (sheafHodgeLaplacian d₀ d₁ * X) * (sheafHodgeLaplacian d₀ d₁ * X) := by
    unfold sheafHodgeSqForm
    rw [star_mul, hStarLap]
    noncomm_ring
  have hCurvPos : 0 ≤ τ (sheafCurvatureEnergy d₀ d₁ X) := by
    rw [hCurvSq]
    exact hPos (d₁ * (d₀ * X))
  have hHodgePos : 0 ≤ τ (sheafHodgeSqForm d₀ d₁ X) := by
    rw [hHodgeSq]
    exact hPos (sheafHodgeLaplacian d₀ d₁ * X)
  refine ⟨hCurvSq, hHodgeSq, hCurvPos, hHodgePos, ?_⟩
  intro hm hXne hCoercive
  have hTauXPos : 0 < τ (star X * X) := by
    refine lt_of_le_of_ne (hPos X) ?_
    intro hZero
    exact hXne (hFaithful X hZero.symm)
  have hStrictPos : 0 < τ (sheafHodgeSqForm d₀ d₁ X) :=
    lt_of_lt_of_le (mul_pos hm hTauXPos) hCoercive
  refine ⟨hStrictPos, ?_⟩
  intro hLapZero
  have hFormZero : τ (sheafHodgeSqForm d₀ d₁ X) = 0 := by
    rw [hHodgeSq, hLapZero, star_zero, zero_mul, map_zero]
  exact ne_of_gt hStrictPos hFormZero

end InfoGeometry.OperatorAlgebra.PeirceSpine
