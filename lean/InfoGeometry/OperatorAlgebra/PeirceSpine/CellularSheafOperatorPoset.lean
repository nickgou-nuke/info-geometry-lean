/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading

/-!
# Stage D₁₆ (Archetypes S₁ → S₇): Sheaf-Inspired Operator Algebra

This file formalizes a seven-stage causal DAG of sheaf-inspired operator
identities over an arbitrary associative ring `B` (`[Ring B]` and
`[StarRing B]`) and proves its exact specialization to the Peirce `Cl₁,₁`
tetraktys `(Φ, J, V, Σ)`. The stages are indexed by a separate total order;
the DAG edges are not asserted to be covers or to generate that order. The
single-ring encoding does not define cell/stalk modules or restriction maps.

* `S₁` & `S₂`: Peirce-graded degree-0 sheaf coboundary
  `sheafCoboundary0 P R_u R_v = R_u * P - R_v * (1 - P)` and global-section
  alignment `R_u * (P * X) = R_v * ((1 - P) * X) → sheafCoboundary0 P R_u R_v * X = 0`.
* `S₃`: Operator sheaf Laplacian `sheafLaplacian0 P R_u R_v = (δ_F)⋆ * δ_F`,
  its self-adjointness, and its `2 × 2` Peirce block decomposition
  `sheafBlock11 + sheafBlock10 + sheafBlock01 + sheafBlock00`.
* `S₄`: Operator Dirichlet quadratic form `sheafDirichletForm P R_u R_v X = X⋆ * L_F * X`,
  its Hermitian square factorization `(δ_F * X)⋆ * (δ_F * X)`, and global-section
  annihilation of `L_F * X`, `X⋆ * L_F * X`, and `sheafDiffusionOp P R_u R_v X`.
* `S₅`: Left-isometric operator covariance `δ_{U F} = U * δ_F` and strict gauge
  invariance `L_{U F} = L_F` under `star U * U = 1`.
* `S₆`: Higher-order operator pair with zero composite `d₁ * d₀ = 0`, adjoint annihilation
  `star d₀ * star d₁ = 0`, self-adjoint Hodge operator
  `sheafHodgeLaplacian d₀ d₁ = d₀ * star d₀ + star d₁ * d₁`, orthogonal up/down
  annihilation, and clean square splitting `Δ₁² = Δ_down² + Δ_up²`.
* `S₇`: Exact specialization to the Peirce `Cl₁,₁` tetraktys: for `R_u = N_-(C)`
  and `R_v = N_+(A)` with `P * P = P` and `star P = P`,
  `sheafCoboundary0 P (coneMinus P C) (conePlus P A) = -genJ P A C`,
  `sheafCoboundary0 P (coneMinus P C) (-conePlus P A) = genPhi P A C`, and
  `sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A)`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ### 1. The 7-Stage Sheaf-Inspired Causal DAG (`S₁ → S₇`) -/

/-- The 7 cellular sheaf archetype stages `S₁` through `S₇` forming Master Stage `D₁₆`. -/
inductive CellularSheafStage : Type
  | S1 | S2 | S3 | S4 | S5 | S6 | S7
  deriving DecidableEq, Repr

namespace CellularSheafStage

/-- Topological rank (1 through 7) of each cellular sheaf archetype stage. -/
def rank : CellularSheafStage → ℕ
  | S1 => 1
  | S2 => 2
  | S3 => 3
  | S4 => 4
  | S5 => 5
  | S6 => 6
  | S7 => 7

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder CellularSheafStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed edges of the 7-stage causal DAG. -/
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
  | _, _ => False

/-- Every directed edge strictly increases the stage rank. -/
theorem causalEdge_strict_rank_mono {s t : CellularSheafStage} (h : causalEdge s t) :
    rank s < rank t := by
  cases s <;> cases t <;> first | contradiction | decide

/-- The 7-stage causal DAG is irreflexive (acyclic). -/
theorem causalEdge_irrefl (s : CellularSheafStage) : ¬ causalEdge s s := by
  intro h
  exact Nat.lt_irrefl (rank s) (causalEdge_strict_rank_mono h)

end CellularSheafStage

/-! ### 2. Non-Commutative Cellular Sheaf Operator Definitions -/

variable {B : Type*} [Ring B]

/-- **Archetypes S₁ & S₂ (`sheafCoboundary0`)**:
Given an idempotent `P` splitting the operator carrier into source corner `P` and target corner `1 - P`,
and arbitrary restriction operators `R_u, R_v : B`, the degree-0 sheaf coboundary
operator is `δ_F = R_u * P - R_v * (1 - P)`. -/
def sheafCoboundary0 (P R_u R_v : B) : B :=
  R_u * P - R_v * (1 - P)

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

/-! ### 3. Lemmas for Archetypes S₃ → S₇ -/

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
2. Every aligned global section (`R_u * (P * X) = R_v * ((1 - P) * X)`) is annihilated by
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

/-! ### 4. Stage D₁₆: Synthesis of the Sheaf-Inspired Operator Identities -/

/-- **Stage D₁₆ (`stage_D16_cellular_sheaf_operator_master_synthesis`)**:
Unifies the stated seven sheaf-inspired operator archetypes (`S₁ → S₇`) over
`[Ring B] [StarRing B]`:
1. **Block Decomposition & Self-Adjointness (`S₃`):** `L_F⋆ = L_F` and
   `L_F = sheafBlock11 + sheafBlock10 + sheafBlock01 + sheafBlock00`.
2. **Global Section Equilibrium (`S₂ & S₄`):**
   `R_u * (P * X) = R_v * ((1 - P) * X) → L_F * X = 0 ∧ X⋆ * L_F * X = 0 ∧ sheafDiffusionOp P R_u R_v X = 0`.
3. **Left-Isometric Operator Covariance (`S₅`):** `star U * U = 1 → L_{U F} = L_F` and `E_{U F}(X) = E_F(X)`.
4. **Higher Operator Hodge Identities (`S₆`):** `d₁ * d₀ = 0 → Δ₁⋆ = Δ₁`, `Δ_up * Δ_down = 0`,
   and `Δ₁² = Δ_down² + Δ_up²`.
5. **Peirce–Tetraktys Unification (`S₇`):** For `R_u = coneMinus P (star A)` and `R_v = conePlus P A`,
   `δ_F = -genJ P A (star A)` and `L_F = genV P A (star A)`. -/
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

end InfoGeometry.OperatorAlgebra.PeirceSpine
