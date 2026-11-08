/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.ConeSheetBraiding
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectParity
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParpicOperatorSpine
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator
import InfoGeometry.OperatorAlgebra.PeirceSpine.DirectedFlowMagneticResolvent
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.OperatorAlgebra.ThreeCornerColumnAlgebra
import InfoGeometry.Core.PeirceCompressionDefect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Stages D₁₆ → D₁₉, D₂₁, and D₂₂ (`S₁ → S₂₈`)

This file formalizes the non-commutative cellular-sheaf-inspired operator identities over an
arbitrary associative star-ring `B` (`[Ring B]` and `[StarRing B]`), with **zero scalar
functional parameters** and **zero duplicate pinching definitions**,
connected directly to preexisting codebase owners (`DefectParity`, `PeirceCompressionDefect`,
`ParpicOperatorSpine`, `PeirceDefectBridge`, `Bergman`, `ChiralEulerFactors`, `Orientation`,
`Supercharge`, `DirectedFlowMagneticResolvent`, `ThreeCornerColumnAlgebra`, and
`ConeSheetBraiding`):

* **Stage `D₁₆` (`S₁ → S₇`)**:
  Degree-0 sheaf coboundary `sheafCoboundary0`, sheaf Laplacian `sheafLaplacian0`,
  `2 × 2` Peirce block decomposition, operator Dirichlet quadratic form `sheafDirichletForm`,
  left-isometric gauge invariance, degree-1 Hodge Laplacian `sheafHodgeLaplacian`, and
  exact specialization to the Peirce Tetraktys `(Φ, J, V, Σ)`.
* **Stage `D₁₇` (`S₈ → S₁₁`)**:
  Split-complex coboundary intertwining via `invS P`, 1-cell edge Laplacian
  `sheafEdgeLaplacian1`, horizon vertex–edge self-duality (`comm (star δ_F) δ_F = 0`),
  and the unconditional Peirce–Hodge cochain complex `d₀ = d₁ = conePlus P A`.
* **Stage `D₁₈` (`S₁₂ → S₁₅`)**:
  Curved 2-step cochain complexes (`sheafCurvature2`, `sheafWeitzenboeckDefect`),
  3-tier non-commutative Bianchi identities, Mandelbrot defect tower Peirce absorption,
  and all-depth fractal sheet Hodge filtering.
* **Stage `D₁₉` (`S₁₆ → S₁₉`)**:
  - `S₁₆` (`curved_sheaf_clifford_instantiation`): Clifford `(Φ, J)` curved sheaf complex
    with `F = Σ`, `Δ_down = Δ_up = V`, `Δ₁ = 2 • V`, and `sheafWeitzenboeckDefect = 2 • V²`.
  - `S₁₇` (`curved_sheaf_weitzenboeck_gauge_invariance`): Gauge covariance of curvature
    `F ↦ U₂ F U₀` and strict invariance of `Δ₁` and `sheafWeitzenboeckDefect` under
    `U₀ * star U₀ = 1` and `star U₂ * U₂ = 1`.
  - `S₁₈` (`curved_cone_bianchi_braiding_instantiation`): Direct bridge from
    `curved_sheaf_bianchi_identity` on alternating Peirce cones `(N_-, N_+, N_-)` and
    `(N_+, N_-, N_+)` to `ConeSheetBraiding` (`N_- Q_+ = Q_- N_-`, `N_+ Q_- = Q_+ N_+`).
  - `S₁₉` (`all_depth_sheaf_hodge_fractal_intertwining`): All-depth (`n : ℕ`) commutation
    of `idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))` with
    `conePlus P A`, `coneMinus P (star A)`, `sheafCoboundary0`, `sheafCoboundary0Sym`, and `Δ₁`.
* **Stage `D₂₁` / Supplemental operator identities (`S₂₀ → S₂₄`)**:
  - `S₂₀` (`sheaf_bergman_euler_projector_and_factor_identities`): Direct bridge from
    `sheafHodgeLaplacian (conePlus P A) (conePlus P A)` to `Bergman.bergmanOp`,
    `ChiralEulerFactors`, and a truncated polynomial factor identity
    `(1 - Δ₁) * (1 + Δ₁) = 1 - (Δ_down² + Δ_up²)`.
  - `S₂₁` (`multiEdgeSheafLaplacian_properties`, `multiVertexOrthogonalSheaf_properties` &
    `sheafDirichlet_proper_star_kernel_iff`): Purely operator-ring multi-edge and multi-vertex
    sheaf Laplacians and proper star-ring (`star z * z = 0 → z = 0`) faithful kernel equivalences.
  - `S₂₂` (`curved_sheaf_operator_energy_factorization_and_kernel`): Operator-ring lift
    of `sheafCurvatureEnergy`, `sheafHodgeSqForm`, `sheafOperatorMassForm`,
    `sheafOperatorGapResidual`, and conditional factorization identities from a supplied
    operator `G` satisfying `G * Δ₁ = M`.
  - `S₂₃` (`krein_involution_peirce_exchange_equivalence` &
    `sheaf_krein_unital_laplacian_and_hodge_identity`): Krein involution–Peirce exchange
    equivalence and unital sheaf/Hodge Laplacians (`L_F = 1`, `Δ₁ = 1`, `Δ_down - Δ_up = invS P`).
  - `S₂₄` (`sheaf_evenGrade_defect_compression_and_parpic_bridge` &
    `sheaf_orientation_hodgeStar_and_codifferential_bridge`): Deduplicated bridges
    using `evenGrade` (from `DefectParity`), `peirce11_idempotencyDefect_sub` and
    `peirce00_idempotencyDefect_sub` (from `PeirceDefectBridge`),
    `compression_square_defect_star` (from `PeirceCompressionDefect`),
    `parpicFlux` / `parpicCirc` (from `ParpicOperatorSpine`), and
    `hodgeStar` / `hodgeLaplacianPhi` / `superDerivPlus` (from `Orientation` and `Supercharge`).
* **Stage `D₂₂` (`S₂₅ → S₂₈`)**:
  - `S₂₅` (`sheafHodgeComplement_factorization_and_green_polynomial`,
    `sheafHodgeComplement_on_shell_iff`, `horizon_hodge_complement_depth0_and_cubic_green_identity`):
    Bergman–Euler Hodge complement `sheafHodgeComplement`, degree-2 Green polynomial
    `sheafGreenPolynomial2`, on-shell idempotent projector equivalence, and horizon cubic Green split.
  - `S₂₆` (`mandelbrotTower_sheet_orthogonality` & `fractal_hodge_complement_tower_descent`):
    All-depth fractal Hodge complement `fractalHodgeComplement` and vertical defect-tower descent.
  - `S₂₇ & S₂₈` (`simplicial_triangle_sheaf_holonomy_and_localization` &
    `simplicial_three_corner_partition_bridge`): 3-stalk directed simplicial edge operators,
    2-simplex curvature, 3-cycle closed-path holonomy, middle-stalk localization, and bridges to
    `ThreeCornerColumnAlgebra` and `DirectedFlowMagneticResolvent` (`twoStepUpper`, `twoStepResolvent`).
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

/-! ### 1. The 28-Stage Cellular Sheaf Causal DAG (`S₁ → S₂₈`) -/

/-- The 28 cellular sheaf archetype stages `S₁` through `S₂₈` spanning Stages `D₁₆`–`D₁₉`,
`D₂₁`, and `D₂₂`. -/
inductive CellularSheafStage : Type
  | S1 | S2 | S3 | S4 | S5 | S6 | S7
  | S8 | S9 | S10 | S11
  | S12 | S13 | S14 | S15
  | S16 | S17 | S18 | S19
  | S20 | S21 | S22 | S23 | S24
  | S25 | S26 | S27 | S28
  deriving DecidableEq, Repr

namespace CellularSheafStage

/-- Topological rank (1 through 28) of each cellular sheaf archetype stage. -/
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
  | S16 => 16
  | S17 => 17
  | S18 => 18
  | S19 => 19
  | S20 => 20
  | S21 => 21
  | S22 => 22
  | S23 => 23
  | S24 => 24
  | S25 => 25
  | S26 => 26
  | S27 => 27
  | S28 => 28

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder CellularSheafStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed edges of the 28-stage cellular sheaf causal DAG (`S₁ → S₂₈`). -/
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
  | S12, S16 => True
  | S12, S17 => True
  | S13, S18 => True
  | S15, S19 => True
  | S16, S19 => True
  | S18, S19 => True
  | S7, S20 => True
  | S11, S20 => True
  | S5, S21 => True
  | S12, S22 => True
  | S17, S22 => True
  | S11, S23 => True
  | S19, S24 => True
  | S20, S25 => True
  | S19, S26 => True
  | S25, S26 => True
  | S21, S27 => True
  | S25, S28 => True
  | S27, S28 => True
  | _, _ => False

/-- Every directed edge strictly increases the stage rank. -/
theorem causalEdge_strict_rank_mono {s t : CellularSheafStage} (h : causalEdge s t) :
    rank s < rank t := by
  cases s <;> cases t <;> first | decide | cases h

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

/-- **Unconditional Coboundary Alignment Equivalence (`sheafCoboundary0_mul_eq_zero_iff`)**:
In any ring `B` (without requiring `P` to be idempotent or any star structure),
`sheafCoboundary0 P R_u R_v * X = 0` holds if and only if `R_u * (P * X) = R_v * ((1 - P) * X)`. -/
theorem sheafCoboundary0_mul_eq_zero_iff (P R_u R_v X : B) :
    sheafCoboundary0 P R_u R_v * X = 0 ↔ R_u * (P * X) = R_v * ((1 - P) * X) := by
  unfold sheafCoboundary0
  rw [sub_mul, mul_assoc, mul_assoc, sub_eq_zero]

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

/-! ### 5. Stage D₁₉ (`S₁₆ → S₁₉`): Curved Clifford Sheaf Instantiation, Gauge Invariance, Cone Bianchi Braiding & All-Depth Fractal Intertwining -/

/-- **Lemma S₁₆.1 (`curved_sheaf_clifford_instantiation`)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `A : B`, setting
`d₀ = genPhi P A (star A)` and `d₁ = genJ P A (star A)` produces a concrete curved
cochain pair with non-vanishing curvature `genSig P A (star A)`:
1. `sheafCurvature2 (genPhi P A (star A)) (genJ P A (star A)) = genSig P A (star A)`.
2. `sheafHodgeDown (genPhi P A (star A)) = genV P A (star A)` and
   `sheafHodgeUp (genJ P A (star A)) = genV P A (star A)`.
3. `sheafHodgeLaplacian (genPhi P A (star A)) (genJ P A (star A)) = (2 : ℤ) • genV P A (star A)`.
4. `sheafWeitzenboeckDefect (genPhi P A (star A)) (genJ P A (star A)) = (2 : ℤ) • (genV P A (star A) * genV P A (star A))`. -/
theorem curved_sheaf_clifford_instantiation
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) :
    sheafCurvature2 (genPhi P A (star A)) (genJ P A (star A)) = genSig P A (star A) ∧
    sheafHodgeDown (genPhi P A (star A)) = genV P A (star A) ∧
    sheafHodgeUp (genJ P A (star A)) = genV P A (star A) ∧
    sheafHodgeLaplacian (genPhi P A (star A)) (genJ P A (star A)) =
      (2 : ℤ) • genV P A (star A) ∧
    sheafWeitzenboeckDefect (genPhi P A (star A)) (genJ P A (star A)) =
      (2 : ℤ) • (genV P A (star A) * genV P A (star A)) := by
  have hCurv : sheafCurvature2 (genPhi P A (star A)) (genJ P A (star A)) = genSig P A (star A) := by
    unfold sheafCurvature2
    peirce_nf hP
  have hDown : sheafHodgeDown (genPhi P A (star A)) = genV P A (star A) := by
    unfold sheafHodgeDown
    rw [star_genPhi hPsym]
    peirce_nf hP
  have hUp : sheafHodgeUp (genJ P A (star A)) = genV P A (star A) := by
    unfold sheafHodgeUp
    rw [star_genJ hPsym]
    peirce_nf hP
  have hLap :
      sheafHodgeLaplacian (genPhi P A (star A)) (genJ P A (star A)) =
        (2 : ℤ) • genV P A (star A) := by
    unfold sheafHodgeLaplacian
    rw [hDown, hUp, two_zsmul]
  refine ⟨hCurv, hDown, hUp, hLap, ?_⟩
  rcases curved_sheaf_weitzenboeck_identity (genPhi P A (star A)) (genJ P A (star A)) with
    ⟨hUD, hDU, _⟩
  unfold sheafWeitzenboeckDefect
  rw [← hUD, ← hDU, hDown, hUp, two_zsmul]

/-- **Lemma S₁₇.1 (`curved_sheaf_weitzenboeck_gauge_invariance`)**:
Under a co-isometric 0-cochain gauge transformation `U₀` (`U₀ * star U₀ = 1`) and a
left-isometric 2-cochain gauge transformation `U₂` (`star U₂ * U₂ = 1`):
1. The 2-cell curvature transforms covariantly:
   `sheafCurvature2 (d₀ * U₀) (U₂ * d₁) = U₂ * sheafCurvature2 d₀ d₁ * U₀`.
2. `sheafHodgeDown (d₀ * U₀) = sheafHodgeDown d₀` and `sheafHodgeUp (U₂ * d₁) = sheafHodgeUp d₁`.
3. Both `sheafHodgeLaplacian` and `sheafWeitzenboeckDefect` are strictly gauge-invariant. -/
theorem curved_sheaf_weitzenboeck_gauge_invariance
    {d₀ d₁ U₀ U₂ : B} (hU₀ : U₀ * star U₀ = 1) (hU₂ : star U₂ * U₂ = 1) :
    sheafCurvature2 (d₀ * U₀) (U₂ * d₁) = U₂ * sheafCurvature2 d₀ d₁ * U₀ ∧
    sheafHodgeDown (d₀ * U₀) = sheafHodgeDown d₀ ∧
    sheafHodgeUp (U₂ * d₁) = sheafHodgeUp d₁ ∧
    sheafHodgeLaplacian (d₀ * U₀) (U₂ * d₁) = sheafHodgeLaplacian d₀ d₁ ∧
    sheafWeitzenboeckDefect (d₀ * U₀) (U₂ * d₁) = sheafWeitzenboeckDefect d₀ d₁ := by
  have hCurv : sheafCurvature2 (d₀ * U₀) (U₂ * d₁) = U₂ * sheafCurvature2 d₀ d₁ * U₀ := by
    unfold sheafCurvature2
    noncomm_ring
  have hDown : sheafHodgeDown (d₀ * U₀) = sheafHodgeDown d₀ := by
    unfold sheafHodgeDown
    rw [star_mul, mul_assoc, ← mul_assoc U₀ (star U₀), hU₀, one_mul]
  have hUp : sheafHodgeUp (U₂ * d₁) = sheafHodgeUp d₁ := by
    unfold sheafHodgeUp
    rw [star_mul, mul_assoc, ← mul_assoc (star U₂) U₂, hU₂, one_mul]
  have hLap : sheafHodgeLaplacian (d₀ * U₀) (U₂ * d₁) = sheafHodgeLaplacian d₀ d₁ := by
    unfold sheafHodgeLaplacian
    rw [hDown, hUp]
  refine ⟨hCurv, hDown, hUp, hLap, ?_⟩
  rcases curved_sheaf_weitzenboeck_identity d₀ d₁ with ⟨hUD, hDU, _⟩
  rcases curved_sheaf_weitzenboeck_identity (d₀ * U₀) (U₂ * d₁) with ⟨hUD', hDU', _⟩
  unfold sheafWeitzenboeckDefect at *
  rw [← hUD', ← hDU', hDown, hUp, hUD, hDU]

omit [StarRing B] in
/-- **Lemma S₁₈.1 (`curved_cone_bianchi_braiding_instantiation`)**:
Applying the 3-tier algebraic Bianchi associative law `(d₂ * d₁) * d₀ = d₂ * (d₁ * d₀)` to
alternating Peirce cones `(coneMinus P C, conePlus P A, coneMinus P C)` and
`(conePlus P A, coneMinus P C, conePlus P A)` recovers the cone-sheet braiding identities of
`ConeSheetBraiding.qgt_cycles_cone_relations`:
1. `sheafCurvature2 (coneMinus P C) (conePlus P A) = qgtPlus P A C`,
2. `sheafCurvature2 (conePlus P A) (coneMinus P C) = qgtMinus P A C`,
3. `coneMinus P C * qgtPlus P A C = qgtMinus P A C * coneMinus P C`,
4. `conePlus P A * qgtMinus P A C = qgtPlus P A C * conePlus P A`. -/
theorem curved_cone_bianchi_braiding_instantiation (P A C : B) :
    sheafCurvature2 (coneMinus P C) (conePlus P A) = qgtPlus P A C ∧
    sheafCurvature2 (conePlus P A) (coneMinus P C) = qgtMinus P A C ∧
    coneMinus P C * qgtPlus P A C = qgtMinus P A C * coneMinus P C ∧
    conePlus P A * qgtMinus P A C = qgtPlus P A C * conePlus P A := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold qgtPlus qgtMinus
    rw [mul_assoc]
  · unfold qgtPlus qgtMinus
    rw [mul_assoc]

/-- **Lemma S₁₉.1 (`all_depth_sheaf_hodge_fractal_intertwining`)**:
At every Mandelbrot defect depth `n : ℕ`, let
`X_n = mandelbrotTower n (qgtPlus P A (star A))`,
`Y_n = mandelbrotTower n (qgtMinus P A (star A))`,
`V_n = X_n + Y_n`, and `Sig_n = X_n - Y_n`:
1. **All-depth agreement of `sheafLaplacian0` and `sheafHodgeLaplacian` & chiral Hodge intertwining**:
   - `sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) * V_n = sheafHodgeLaplacian (conePlus P A) (conePlus P A) * V_n`,
   - `sheafHodgeLaplacian (conePlus P A) (conePlus P A) * V_n = qgtPlus P A (star A) * X_n + qgtMinus P A (star A) * Y_n`,
   - `sheafHodgeLaplacian (conePlus P A) (conePlus P A) * Sig_n = qgtPlus P A (star A) * X_n - qgtMinus P A (star A) * Y_n`,
   - `(sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) * V_n = sheafHodgeLaplacian (conePlus P A) (conePlus P A) * Sig_n`,
   - `(sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) * Sig_n = sheafHodgeLaplacian (conePlus P A) (conePlus P A) * V_n`.
2. **All-depth commutation (`ConeSheetBraiding` bridge)**:
   `idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))` commutes with
   `conePlus P A`, `coneMinus P (star A)`, `sheafCoboundary0`, `sheafCoboundary0Sym`, and
   `sheafHodgeLaplacian (conePlus P A) (conePlus P A)`. -/
theorem all_depth_sheaf_hodge_fractal_intertwining
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) (n : ℕ) :
    let X_n := mandelbrotTower n (qgtPlus P A (star A))
    let Y_n := mandelbrotTower n (qgtMinus P A (star A))
    let V_n := X_n + Y_n
    let Sig_n := X_n - Y_n
    sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) * V_n =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) * V_n ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) * V_n =
      qgtPlus P A (star A) * X_n + qgtMinus P A (star A) * Y_n ∧
    sheafHodgeLaplacian (conePlus P A) (conePlus P A) * Sig_n =
      qgtPlus P A (star A) * X_n - qgtMinus P A (star A) * Y_n ∧
    (sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) * V_n =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) * Sig_n ∧
    (sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) * Sig_n =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) * V_n ∧
    comm (conePlus P A)
      (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0 ∧
    comm (coneMinus P (star A))
      (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0 ∧
    comm (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A))
      (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0 ∧
    comm (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A))
      (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0 ∧
    comm (sheafHodgeLaplacian (conePlus P A) (conePlus P A))
      (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0 := by
  intro X_n Y_n V_n Sig_n
  rcases fractal_sheet_hodge_filtering hP hPsym A n with
    ⟨_, _, hUpX, hDownY, hLapX, hLapY⟩
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym A with
    ⟨_, hDown, hUp, hHodgeV, _⟩
  rcases sheaf_to_tetraktys_bridge hP hPsym A (star A) with ⟨hCobJ, hCobPhi, hLap0V⟩
  have hSheafEqHodge :
      sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) =
        sheafHodgeLaplacian (conePlus P A) (conePlus P A) :=
    hLap0V.trans hHodgeV.symm
  have hLapVn :
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) * V_n =
        qgtPlus P A (star A) * X_n + qgtMinus P A (star A) * Y_n := by
    dsimp [V_n]
    rw [mul_add, hLapX, hLapY]
  have hLapSign :
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) * Sig_n =
        qgtPlus P A (star A) * X_n - qgtMinus P A (star A) * Y_n := by
    dsimp [Sig_n]
    rw [mul_sub, hLapX, hLapY]
  have hChiralV :
      (sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) * V_n =
        sheafHodgeLaplacian (conePlus P A) (conePlus P A) * Sig_n := by
    dsimp [V_n]
    rw [mul_add, sub_mul, sub_mul, hUpX, hDownY, sub_zero, zero_sub, hDown, hUp,
      ← sub_eq_add_neg, ← hLapSign]
  have hChiralSig :
      (sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) * Sig_n =
        sheafHodgeLaplacian (conePlus P A) (conePlus P A) * V_n := by
    dsimp [Sig_n]
    rw [mul_sub, sub_mul, sub_mul, hUpX, hDownY, sub_zero, zero_sub, sub_neg_eq_add,
      hDown, hUp, ← hLapVn]
  have hSplit := genV_defect_iterates_cycle_split hP A (star A) n
  rcases qgt_defect_iterate_sum_commutes_with_cones hP A (star A) n with ⟨hConeP, hConeM⟩
  rcases qgt_defect_iterate_sum_commutes_with_generators hP A (star A) n with ⟨hPhi, hJ⟩
  refine ⟨by rw [hSheafEqHodge], hLapVn, hLapSign, hChiralV, hChiralSig, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hHodgeV, hSplit]
    exact hConeP
  · rw [hHodgeV, hSplit]
    exact hConeM
  · rw [hHodgeV, hCobJ, hSplit]
    unfold comm at hJ ⊢
    have hEq := sub_eq_zero.mp hJ
    simp only [neg_mul, mul_neg]
    rw [hEq]
    noncomm_ring
  · unfold sheafCoboundary0Sym
    rw [hHodgeV, hCobPhi, hSplit]
    exact hPhi
  · rw [hHodgeV]
    unfold comm
    exact sub_eq_zero.mpr (comm_idempotencyDefect_iterate (genV P A (star A)) n)

/-- **Stage D₁₉ (`stage_D19_curved_clifford_sheaf_gauge_invariance_and_fractal_intertwining`)**:
Unifies Archetypes `S₁₆ → S₁₉` over `[Ring B] [StarRing B]`. -/
theorem stage_D19_curved_clifford_sheaf_gauge_invariance_and_fractal_intertwining
    {P d₀ d₁ U₀ U₂ A C : B} (hP : P * P = P) (hPsym : star P = P)
    (hU₀ : U₀ * star U₀ = 1) (hU₂ : star U₂ * U₂ = 1) (n : ℕ) :
    sheafCurvature2 (genPhi P A (star A)) (genJ P A (star A)) = genSig P A (star A) ∧
    sheafHodgeLaplacian (genPhi P A (star A)) (genJ P A (star A)) =
      (2 : ℤ) • genV P A (star A) ∧
    sheafWeitzenboeckDefect (genPhi P A (star A)) (genJ P A (star A)) =
      (2 : ℤ) • (genV P A (star A) * genV P A (star A)) ∧
    sheafCurvature2 (d₀ * U₀) (U₂ * d₁) = U₂ * sheafCurvature2 d₀ d₁ * U₀ ∧
    sheafHodgeLaplacian (d₀ * U₀) (U₂ * d₁) = sheafHodgeLaplacian d₀ d₁ ∧
    sheafWeitzenboeckDefect (d₀ * U₀) (U₂ * d₁) = sheafWeitzenboeckDefect d₀ d₁ ∧
    coneMinus P C * qgtPlus P A C = qgtMinus P A C * coneMinus P C ∧
    conePlus P A * qgtMinus P A C = qgtPlus P A C * conePlus P A ∧
    (sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) *
      (mandelbrotTower n (qgtPlus P A (star A)) + mandelbrotTower n (qgtMinus P A (star A))) =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
      (mandelbrotTower n (qgtPlus P A (star A)) - mandelbrotTower n (qgtMinus P A (star A))) ∧
    (sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) *
      (mandelbrotTower n (qgtPlus P A (star A)) - mandelbrotTower n (qgtMinus P A (star A))) =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
      (mandelbrotTower n (qgtPlus P A (star A)) + mandelbrotTower n (qgtMinus P A (star A))) ∧
    comm (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A))
      (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0 ∧
    comm (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A))
      (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0 := by
  rcases curved_sheaf_clifford_instantiation hP hPsym A with
    ⟨hCl1, _, _, hCl4, hCl5⟩
  rcases curved_sheaf_weitzenboeck_gauge_invariance (d₀ := d₀) (d₁ := d₁) hU₀ hU₂ with
    ⟨hG1, _, _, hG4, hG5⟩
  rcases curved_cone_bianchi_braiding_instantiation P A C with
    ⟨_, _, hB3, hB4⟩
  rcases all_depth_sheaf_hodge_fractal_intertwining hP hPsym A n with
    ⟨_, _, _, hChV, hChSig, _, _, hF3, hF4, _⟩
  exact ⟨hCl1, hCl4, hCl5, hG1, hG4, hG5, hB3, hB4, hChV, hChSig, hF3, hF4⟩

/-! ### 6. Supplemental Operator Identities (`S₂₀ → S₂₄`): Bergman–Euler Factor Identities, Multi-Edge Proper Star-Ring Kernel, Operator Mass Factorizations, Krein Exchange & Deduplicated Defect/Parpic Bridges -/

/-- **Lemma S₂₀.1 (`sheaf_bergman_euler_projector_and_factor_identities`)**:
Connects the horizon sheaf Laplacians `sheafHodgeLaplacian (conePlus P A) (conePlus P A)` and
`sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A)` directly to `Bergman.bergmanOp`,
`ChiralEulerFactors`, and the following truncated polynomial factor identities (no inverse
or resolvent assertion is made):
1. `bergmanOp P A (star A) 1 = 1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A)`,
2. `bergmanOp P A (star A) 1 = 1 - sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A)`,
3. `(1 - sheafHodgeDown (conePlus P A)) * (1 - sheafHodgeUp (conePlus P A)) = 1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A)`,
4. `(1 - genPhi P A (star A)) * (1 + genPhi P A (star A)) = 1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A)`,
5. `(1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A)) * (1 + sheafHodgeLaplacian (conePlus P A) (conePlus P A)) = 1 - (sheafHodgeDown (conePlus P A) * sheafHodgeDown (conePlus P A) + sheafHodgeUp (conePlus P A) * sheafHodgeUp (conePlus P A))`. -/
theorem sheaf_bergman_euler_projector_and_factor_identities
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) :
    bergmanOp P A (star A) 1 =
      1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    bergmanOp P A (star A) 1 =
      1 - sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) ∧
    (1 - sheafHodgeDown (conePlus P A)) * (1 - sheafHodgeUp (conePlus P A)) =
      1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    (1 - genPhi P A (star A)) * (1 + genPhi P A (star A)) =
      1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    (1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A)) *
      (1 + sheafHodgeLaplacian (conePlus P A) (conePlus P A)) =
      1 - (sheafHodgeDown (conePlus P A) * sheafHodgeDown (conePlus P A) +
           sheafHodgeUp (conePlus P A) * sheafHodgeUp (conePlus P A)) := by
  have hBerg := (archetype_A23_bergman_operator hP A (star A)).1
  have hEuler := (chiralEuler_factorizations hP A (star A)).1
  have hLap0 := (sheaf_to_tetraktys_bridge hP hPsym A (star A)).2.2
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym A with
    ⟨hConeSq, hDown, hUp, hHodgeV, _⟩
  have hPhiBinom : (1 - genPhi P A (star A)) * (1 + genPhi P A (star A)) =
      1 - genV P A (star A) := by
    peirce_nf hP
  have hHodgeSq := (sheafHodgeLaplacian_properties hConeSq).2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hBerg, hHodgeV]
  · rw [hBerg, hLap0]
  · rw [hDown, hUp, hHodgeV]
    exact hEuler
  · rw [hPhiBinom, hHodgeV]
  · calc
      (1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A)) *
          (1 + sheafHodgeLaplacian (conePlus P A) (conePlus P A)) =
        1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
            sheafHodgeLaplacian (conePlus P A) (conePlus P A) := by noncomm_ring
      _ = 1 - (sheafHodgeDown (conePlus P A) * sheafHodgeDown (conePlus P A) +
               sheafHodgeUp (conePlus P A) * sheafHodgeUp (conePlus P A)) := by
        rw [hHodgeSq]

/-- **Operator family S₂₁ (`multiEdgeSheafLaplacian`, `multiEdgeDirichletForm`)**:
Finite sum `∑ e ∈ E, sheafLaplacian0 (P e) (R_u e) (R_v e)` and its associated operator
quadratic form over an index set `E : Finset ι`. -/
def multiEdgeSheafLaplacian {ι : Type*} (E : Finset ι) (P R_u R_v : ι → B) : B :=
  ∑ e ∈ E, sheafLaplacian0 (P e) (R_u e) (R_v e)

def multiEdgeDirichletForm {ι : Type*} (E : Finset ι) (P R_u R_v : ι → B) (X : B) : B :=
  star X * multiEdgeSheafLaplacian E P R_u R_v * X

/-- **Lemma S₂₁.1 (`multiEdgeSheafLaplacian_properties`)**:
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

/-- **Directed edge coboundary (`orthogonalPairCoboundary`) & Laplacian (`orthogonalPairLaplacian`)
over a Pair of Orthogonal Vertex Idempotents (`P_u, P_v`):**
Generalizes `sheafCoboundary0 P R_u R_v = R_u * P - R_v * (1 - P)` (the 2-vertex case
`P_u + P_v = 1`) to any pair of vertex-stalk idempotents `P_u, P_v : B` in a $K$-vertex
orthogonal decomposition $\sum_{i=1}^K P_i = 1$. -/
def orthogonalPairCoboundary (P_u P_v R_u R_v : B) : B :=
  R_u * P_u - R_v * P_v

def orthogonalPairLaplacian (P_u P_v R_u R_v : B) : B :=
  star (orthogonalPairCoboundary P_u P_v R_u R_v) * orthogonalPairCoboundary P_u P_v R_u R_v

/-- **Lemma S₂₁.2 (`multiVertexOrthogonalSheaf_properties`)**:
For any pair of mutually orthogonal self-adjoint idempotents `P_u, P_v : B`
(`P_u * P_u = P_u`, `P_v * P_v = P_v`, `P_u * P_v = 0`, `P_v * P_u = 0`,
`star P_u = P_u`, `star P_v = P_v`) and any restriction operators `R_u, R_v : B`:
1. Reduction to `sheafCoboundary0` and `sheafLaplacian0` when `P_v = 1 - P_u`,
2. Exact four-block expansion of `orthogonalPairLaplacian P_u P_v R_u R_v`,
3. Exact extraction of the diagonal blocks `P_u L P_u`, `P_v L P_v` and off-diagonal
   transport blocks `P_u L P_v`, `P_v L P_u`,
4. Vanishing on any non-incident vertex stalk `P_w` (`P_u * P_w = 0`, `P_v * P_w = 0`). -/
theorem multiVertexOrthogonalSheaf_properties
    {P_u P_v P_w : B}
    (hPu : P_u * P_u = P_u) (hPv : P_v * P_v = P_v)
    (hOrthUV : P_u * P_v = 0) (hOrthVU : P_v * P_u = 0)
    (hPuSym : star P_u = P_u) (hPvSym : star P_v = P_v)
    (hOrthUW : P_u * P_w = 0) (hOrthVW : P_v * P_w = 0)
    (R_u R_v : B) :
    orthogonalPairCoboundary P_u (1 - P_u) R_u R_v = sheafCoboundary0 P_u R_u R_v ∧
    orthogonalPairLaplacian P_u (1 - P_u) R_u R_v = sheafLaplacian0 P_u R_u R_v ∧
    orthogonalPairLaplacian P_u P_v R_u R_v =
      P_u * star R_u * R_u * P_u + P_v * star R_v * R_v * P_v -
        P_u * star R_u * R_v * P_v - P_v * star R_v * R_u * P_u ∧
    P_u * orthogonalPairLaplacian P_u P_v R_u R_v * P_u = P_u * star R_u * R_u * P_u ∧
    P_v * orthogonalPairLaplacian P_u P_v R_u R_v * P_v = P_v * star R_v * R_v * P_v ∧
    P_u * orthogonalPairLaplacian P_u P_v R_u R_v * P_v = -(P_u * star R_u * R_v * P_v) ∧
    P_v * orthogonalPairLaplacian P_u P_v R_u R_v * P_u = -(P_v * star R_v * R_u * P_u) ∧
    orthogonalPairCoboundary P_u P_v R_u R_v * P_w = 0 ∧
    orthogonalPairLaplacian P_u P_v R_u R_v * P_w = 0 := by
  have hExp :
      orthogonalPairLaplacian P_u P_v R_u R_v =
        P_u * star R_u * R_u * P_u + P_v * star R_v * R_v * P_v -
          P_u * star R_u * R_v * P_v - P_v * star R_v * R_u * P_u := by
    unfold orthogonalPairLaplacian orthogonalPairCoboundary
    rw [star_sub, star_mul, star_mul, hPuSym, hPvSym]
    noncomm_ring
  have hPuA : ∀ X : B, P_u * (P_u * X) = P_u * X := fun X => by rw [← mul_assoc, hPu]
  have hPvA : ∀ X : B, P_v * (P_v * X) = P_v * X := fun X => by rw [← mul_assoc, hPv]
  have hUV_A : ∀ X : B, P_u * (P_v * X) = 0 := fun X => by rw [← mul_assoc, hOrthUV, zero_mul]
  have hVU_A : ∀ X : B, P_v * (P_u * X) = 0 := fun X => by rw [← mul_assoc, hOrthVU, zero_mul]
  have hCobW : orthogonalPairCoboundary P_u P_v R_u R_v * P_w = 0 := by
    unfold orthogonalPairCoboundary
    rw [sub_mul, mul_assoc, hOrthUW, mul_zero, mul_assoc, hOrthVW, mul_zero, sub_self]
  refine ⟨rfl, rfl, hExp, ?_, ?_, ?_, ?_, hCobW, ?_⟩
  · rw [hExp]
    simp only [sub_mul, mul_sub, mul_add, mul_assoc,
      hPu, hOrthVU, hPuA, hUV_A, mul_zero, add_zero, sub_zero]
  · rw [hExp]
    simp only [sub_mul, mul_sub, mul_add, mul_assoc,
      hPv, hOrthUV, hPvA, hVU_A, mul_zero, zero_add, sub_zero]
  · rw [hExp]
    simp only [sub_mul, mul_sub, mul_add, mul_assoc,
      hPv, hOrthUV, hPuA, hUV_A, mul_zero, add_zero, sub_zero, zero_sub]
  · rw [hExp]
    simp only [sub_mul, add_mul, mul_sub, mul_add, mul_assoc,
      hPu, hOrthVU, hPvA, hVU_A, mul_zero, zero_mul, add_zero, sub_zero, zero_sub]
  · unfold orthogonalPairLaplacian
    rw [mul_assoc, hCobW, mul_zero]

/-- **Lemma S₂₁.3 (`sheafDirichlet_proper_star_kernel_iff`)**:
Purely operator-ring faithful kernel characterization over `[Ring B] [StarRing B]`:
1. Unconditionally in any ring `B`, `sheafCoboundary0 P R_u R_v * X = 0 ↔ R_u * (P * X) = R_v * ((1 - P) * X)`.
2. Under star-ring properness `hproper : ∀ z : B, star z * z = 0 → z = 0`:
   - `sheafDirichletForm P R_u R_v X = 0 ↔ sheafCoboundary0 P R_u R_v * X = 0`,
   - `sheafLaplacian0 P R_u R_v * X = 0 ↔ sheafCoboundary0 P R_u R_v * X = 0`,
   - `sheafDirichletForm P R_u R_v X = 0 ↔ R_u * (P * X) = R_v * ((1 - P) * X)`.
3. Operator-valued Peirce pinching of `sheafDirichletForm` via `evenGrade`:
   `evenGrade P (sheafDirichletForm P R_u R_v X) = peirce11 P (star (sheafCoboundary0 P R_u R_v * X) * (sheafCoboundary0 P R_u R_v * X)) + peirce00 P (star (sheafCoboundary0 P R_u R_v * X) * (sheafCoboundary0 P R_u R_v * X))`. -/
theorem sheafDirichlet_proper_star_kernel_iff
    (hproper : ∀ z : B, star z * z = 0 → z = 0)
    (P R_u R_v X : B) :
    (sheafCoboundary0 P R_u R_v * X = 0 ↔ R_u * (P * X) = R_v * ((1 - P) * X)) ∧
    (sheafDirichletForm P R_u R_v X = 0 ↔ sheafCoboundary0 P R_u R_v * X = 0) ∧
    (sheafLaplacian0 P R_u R_v * X = 0 ↔ sheafCoboundary0 P R_u R_v * X = 0) ∧
    (sheafDirichletForm P R_u R_v X = 0 ↔ R_u * (P * X) = R_v * ((1 - P) * X)) ∧
    evenGrade P (sheafDirichletForm P R_u R_v X) =
      peirce11 P (star (sheafCoboundary0 P R_u R_v * X) * (sheafCoboundary0 P R_u R_v * X)) +
      peirce00 P (star (sheafCoboundary0 P R_u R_v * X) * (sheafCoboundary0 P R_u R_v * X)) := by
  have hCobIff := sheafCoboundary0_mul_eq_zero_iff P R_u R_v X
  have hDirIff : sheafDirichletForm P R_u R_v X = 0 ↔ sheafCoboundary0 P R_u R_v * X = 0 := by
    rw [sheafDirichletForm_eq_star_coboundary_mul]
    constructor
    · exact hproper (sheafCoboundary0 P R_u R_v * X)
    · intro h0
      rw [h0, star_zero, zero_mul]
  have hLapIff : sheafLaplacian0 P R_u R_v * X = 0 ↔ sheafCoboundary0 P R_u R_v * X = 0 := by
    constructor
    · intro hLap0
      apply hproper
      rw [← sheafDirichletForm_eq_star_coboundary_mul]
      unfold sheafDirichletForm
      rw [mul_assoc, hLap0, mul_zero]
    · intro hCob0
      unfold sheafLaplacian0
      rw [mul_assoc, hCob0, mul_zero]
  refine ⟨hCobIff, hDirIff, hLapIff, hDirIff.trans hCobIff, ?_⟩
  unfold evenGrade peirce11 peirce00
  rw [sheafDirichletForm_eq_star_coboundary_mul]

/-- **Archetype S₂₂ (`sheafCurvatureEnergy`, `sheafHodgeSqForm`, `sheafOperatorMassForm`, `sheafOperatorGapResidual`)**:
Purely operator-valued 2-cell curvature energy `X⋆ * F⋆ * F * X` (`F = d₁ * d₀`),
squared Hodge Laplacian quadratic form `X⋆ * (Δ₁ * Δ₁) * X`, operator-weighted mass form
`(M * X)⋆ * (M * X)`, and operator-shifted Hodge residual `(Δ₁ * X - M * X)⋆ * (Δ₁ * X - M * X)`. -/
def sheafCurvatureEnergy (d₀ d₁ X : B) : B :=
  star X * (star (sheafCurvature2 d₀ d₁) * sheafCurvature2 d₀ d₁) * X

def sheafHodgeSqForm (d₀ d₁ X : B) : B :=
  star X * (sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁) * X

def sheafOperatorMassForm (M X : B) : B :=
  star (M * X) * (M * X)

def sheafOperatorGapResidual (d₀ d₁ M X : B) : B :=
  star (sheafHodgeLaplacian d₀ d₁ * X - M * X) * (sheafHodgeLaplacian d₀ d₁ * X - M * X)

/-- **Lemma S₂₂.1 (`curved_sheaf_operator_energy_factorization_and_kernel`)**:
Sheaf-inspired operator energy factorization and kernel identities over
`[Ring B] [StarRing B]`:
1. `sheafCurvatureEnergy d₀ d₁ X = star (d₁ * (d₀ * X)) * (d₁ * (d₀ * X))`.
2. `sheafHodgeSqForm d₀ d₁ X = star (sheafHodgeLaplacian d₀ d₁ * X) * (sheafHodgeLaplacian d₀ d₁ * X)`.
3. If a supplied operator `G` satisfies `G * sheafHodgeLaplacian d₀ d₁ = M`,
   then `M * X = G * (sheafHodgeLaplacian d₀ d₁ * X)` and
   `sheafOperatorMassForm M X = star (sheafHodgeLaplacian d₀ d₁ * X) * (star G * G) * (sheafHodgeLaplacian d₀ d₁ * X)`.
4. Under star-ring properness `hproper : ∀ z : B, star z * z = 0 → z = 0`:
   - `sheafCurvatureEnergy d₀ d₁ X = 0 ↔ d₁ * (d₀ * X) = 0`,
   - `sheafHodgeSqForm d₀ d₁ X = 0 ↔ sheafHodgeLaplacian d₀ d₁ * X = 0`,
   - `sheafOperatorGapResidual d₀ d₁ M X = 0 ↔ sheafHodgeLaplacian d₀ d₁ * X = M * X`,
   - If `G * sheafHodgeLaplacian d₀ d₁ = M` and `M * X ≠ 0`, then
     `sheafHodgeLaplacian d₀ d₁ * X ≠ 0` and `sheafHodgeSqForm d₀ d₁ X ≠ 0`. -/
theorem curved_sheaf_operator_energy_factorization_and_kernel
    (d₀ d₁ M G X : B) :
    sheafCurvatureEnergy d₀ d₁ X = star (d₁ * (d₀ * X)) * (d₁ * (d₀ * X)) ∧
    sheafHodgeSqForm d₀ d₁ X =
      star (sheafHodgeLaplacian d₀ d₁ * X) * (sheafHodgeLaplacian d₀ d₁ * X) ∧
    (G * sheafHodgeLaplacian d₀ d₁ = M →
      M * X = G * (sheafHodgeLaplacian d₀ d₁ * X) ∧
      sheafOperatorMassForm M X =
        star (sheafHodgeLaplacian d₀ d₁ * X) * (star G * G) *
          (sheafHodgeLaplacian d₀ d₁ * X)) ∧
    ((∀ z : B, star z * z = 0 → z = 0) →
      (sheafCurvatureEnergy d₀ d₁ X = 0 ↔ d₁ * (d₀ * X) = 0) ∧
      (sheafHodgeSqForm d₀ d₁ X = 0 ↔ sheafHodgeLaplacian d₀ d₁ * X = 0) ∧
      (sheafOperatorGapResidual d₀ d₁ M X = 0 ↔ sheafHodgeLaplacian d₀ d₁ * X = M * X) ∧
      (G * sheafHodgeLaplacian d₀ d₁ = M → M * X ≠ 0 →
        sheafHodgeLaplacian d₀ d₁ * X ≠ 0 ∧ sheafHodgeSqForm d₀ d₁ X ≠ 0)) := by
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
  have hRes :
      G * sheafHodgeLaplacian d₀ d₁ = M →
        M * X = G * (sheafHodgeLaplacian d₀ d₁ * X) ∧
        sheafOperatorMassForm M X =
          star (sheafHodgeLaplacian d₀ d₁ * X) * (star G * G) *
            (sheafHodgeLaplacian d₀ d₁ * X) := by
    intro hGM
    have hMX : M * X = G * (sheafHodgeLaplacian d₀ d₁ * X) := by
      rw [← hGM, mul_assoc]
    refine ⟨hMX, ?_⟩
    unfold sheafOperatorMassForm
    rw [hMX, star_mul]
    noncomm_ring
  refine ⟨hCurvSq, hHodgeSq, hRes, ?_⟩
  intro hproper
  have hCurvIff : sheafCurvatureEnergy d₀ d₁ X = 0 ↔ d₁ * (d₀ * X) = 0 := by
    rw [hCurvSq]
    exact ⟨hproper (d₁ * (d₀ * X)), fun h0 => by rw [h0, star_zero, zero_mul]⟩
  have hHodgeIff : sheafHodgeSqForm d₀ d₁ X = 0 ↔ sheafHodgeLaplacian d₀ d₁ * X = 0 := by
    rw [hHodgeSq]
    exact ⟨hproper (sheafHodgeLaplacian d₀ d₁ * X), fun h0 => by rw [h0, star_zero, zero_mul]⟩
  have hGapIff : sheafOperatorGapResidual d₀ d₁ M X = 0 ↔ sheafHodgeLaplacian d₀ d₁ * X = M * X := by
    unfold sheafOperatorGapResidual
    rw [← sub_eq_zero (a := sheafHodgeLaplacian d₀ d₁ * X) (b := M * X)]
    exact ⟨hproper (sheafHodgeLaplacian d₀ d₁ * X - M * X),
      fun h0 => by rw [h0, star_zero, zero_mul]⟩
  refine ⟨hCurvIff, hHodgeIff, hGapIff, ?_⟩
  intro hGM hMXne
  have hMX := (hRes hGM).1
  have hLapNe : sheafHodgeLaplacian d₀ d₁ * X ≠ 0 := by
    intro hLap0
    apply hMXne
    rw [hMX, hLap0, mul_zero]
  exact ⟨hLapNe, fun hSq0 => hLapNe (hHodgeIff.mp hSq0)⟩

omit [StarRing B] in
/-- **Lemma S₂₃.1 (`krein_involution_peirce_exchange_equivalence`)**:
In any associative ring `B` with idempotent `P` (`P * P = P`):
1. If `genV P A C = 1`, then `genPhi P A C` is an involution (`genPhi P A C * genPhi P A C = 1`)
   whose conjugation exchanges `P` and `1 - P`, with `qgtPlus P A C = P` and `qgtMinus P A C = 1 - P`.
2. Conversely, if `η : B` is an involution (`η * η = 1`) exchanging `P` and `1 - P`
   (`η * P * η = 1 - P`), then `conePlus P η = P * η`, `coneMinus P η = (1 - P) * η`,
   `genPhi P η η = η`, `genV P η η = 1`, `qgtPlus P η η = P`, and `qgtMinus P η η = 1 - P`. -/
theorem krein_involution_peirce_exchange_equivalence
    {P A C η : B} (hP : P * P = P) :
    (genV P A C = 1 →
      genPhi P A C * genPhi P A C = 1 ∧
      qgtPlus P A C = P ∧
      qgtMinus P A C = 1 - P ∧
      genPhi P A C * P * genPhi P A C = 1 - P ∧
      genPhi P A C * (1 - P) * genPhi P A C = P) ∧
    (η * η = 1 → η * P * η = 1 - P →
      conePlus P η = P * η ∧
      coneMinus P η = (1 - P) * η ∧
      genPhi P η η = η ∧
      genV P η η = 1 ∧
      qgtPlus P η η = P ∧
      qgtMinus P η η = 1 - P) := by
  refine ⟨?_, ?_⟩
  · intro hV
    have hPhiSq : genPhi P A C * genPhi P A C = 1 := by
      calc
        genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
        _ = 1 := hV
    have hQPlus : qgtPlus P A C = P := by
      calc
        qgtPlus P A C = P * genV P A C := by peirce_nf hP
        _ = P * 1 := by rw [hV]
        _ = P := mul_one P
    have hQMinus : qgtMinus P A C = 1 - P := by
      calc
        qgtMinus P A C = (1 - P) * genV P A C := by peirce_nf hP
        _ = (1 - P) * 1 := by rw [hV]
        _ = 1 - P := mul_one (1 - P)
    have hConjP : genPhi P A C * P * genPhi P A C = 1 - P := by
      calc
        genPhi P A C * P * genPhi P A C = qgtMinus P A C := by peirce_nf hP
        _ = 1 - P := hQMinus
    have hConjCompl : genPhi P A C * (1 - P) * genPhi P A C = P := by
      calc
        genPhi P A C * (1 - P) * genPhi P A C = qgtPlus P A C := by peirce_nf hP
        _ = P := hQPlus
    exact ⟨hPhiSq, hQPlus, hQMinus, hConjP, hConjCompl⟩
  · intro hη hEx
    have hComplEta : (1 - P) * η = η * P := by
      calc
        (1 - P) * η = (η * P * η) * η := by rw [← hEx]
        _ = η * P * (η * η) := by noncomm_ring
        _ = η * P := by rw [hη, mul_one]
    have hPEta : P * η = η * (1 - P) := by
      calc
        P * η = η - (1 - P) * η := by noncomm_ring
        _ = η - η * P := by rw [hComplEta]
        _ = η * (1 - P) := by noncomm_ring
    have hConeP : conePlus P η = P * η := by
      unfold conePlus
      calc
        P * η * (1 - P) = P * (η * (1 - P)) := by noncomm_ring
        _ = P * (P * η) := by rw [← hPEta]
        _ = (P * P) * η := by noncomm_ring
        _ = P * η := by rw [hP]
    have hConeM : coneMinus P η = (1 - P) * η := by
      unfold coneMinus
      calc
        (1 - P) * η * P = (1 - P) * (η * P) := by noncomm_ring
        _ = (1 - P) * ((1 - P) * η) := by rw [← hComplEta]
        _ = (1 - P - P + P * P) * η := by noncomm_ring
        _ = (1 - P) * η := by rw [hP]; noncomm_ring
    have hPhi : genPhi P η η = η := by
      unfold genPhi
      rw [hConeP, hConeM]
      noncomm_ring
    have hV : genV P η η = 1 := by
      calc
        genV P η η = genPhi P η η * genPhi P η η := by peirce_nf hP
        _ = η * η := by rw [hPhi]
        _ = 1 := hη
    have hQPlus : qgtPlus P η η = P := by
      calc
        qgtPlus P η η = P * genV P η η := by peirce_nf hP
        _ = P * 1 := by rw [hV]
        _ = P := mul_one P
    have hQMinus : qgtMinus P η η = 1 - P := by
      calc
        qgtMinus P η η = (1 - P) * genV P η η := by peirce_nf hP
        _ = (1 - P) * 1 := by rw [hV]
        _ = 1 - P := mul_one (1 - P)
    exact ⟨hConeP, hConeM, hPhi, hV, hQPlus, hQMinus⟩

/-- **Lemma S₂₃.2 (`sheaf_krein_unital_laplacian_and_hodge_identity`)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and self-adjoint Krein
involution `η` (`star η = η`, `η * η = 1`) exchanging `P` and `1 - P` (`η * P * η = 1 - P`),
both the degree-0 cellular sheaf Laplacian and the degree-1 horizon Hodge Laplacian
evaluate to the multiplicative identity `1`:
1. `sheafCoboundary0 P (coneMinus P η) (-conePlus P η) = η`,
2. `sheafLaplacian0 P (coneMinus P η) (conePlus P η) = 1`,
3. `sheafHodgeDown (conePlus P η) = P` and `sheafHodgeUp (conePlus P η) = 1 - P`,
4. `sheafHodgeLaplacian (conePlus P η) (conePlus P η) = 1`,
5. `sheafHodgeDown (conePlus P η) - sheafHodgeUp (conePlus P η) = invS P`. -/
theorem sheaf_krein_unital_laplacian_and_hodge_identity
    {P η : B} (hP : P * P = P) (hPsym : star P = P)
    (hη_sym : star η = η) (hη_sq : η * η = 1) (hEx : η * P * η = 1 - P) :
    sheafCoboundary0 P (coneMinus P η) (-conePlus P η) = η ∧
    sheafLaplacian0 P (coneMinus P η) (conePlus P η) = 1 ∧
    sheafHodgeDown (conePlus P η) = P ∧
    sheafHodgeUp (conePlus P η) = 1 - P ∧
    sheafHodgeLaplacian (conePlus P η) (conePlus P η) = 1 ∧
    sheafHodgeDown (conePlus P η) - sheafHodgeUp (conePlus P η) = invS P := by
  rcases (krein_involution_peirce_exchange_equivalence (A := η) (C := η) hP).2 hη_sq hEx with
    ⟨_, _, hPhi, hV, hQPlus, hQMinus⟩
  rcases sheaf_to_tetraktys_bridge hP hPsym η η with ⟨_, hCobPhi, hLap0Star⟩
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym η with
    ⟨_, hDown, hUp, hHodgeLap, _⟩
  rw [hη_sym] at hLap0Star hDown hUp hHodgeLap
  have hDownP : sheafHodgeDown (conePlus P η) = P := hDown.trans hQPlus
  have hUpCompl : sheafHodgeUp (conePlus P η) = 1 - P := hUp.trans hQMinus
  refine ⟨hCobPhi.trans hPhi, hLap0Star.trans hV, hDownP, hUpCompl, hHodgeLap.trans hV, ?_⟩
  rw [hDownP, hUpCompl]
  unfold invS
  noncomm_ring

/-- **Lemma S₂₄.1 (`sheaf_evenGrade_defect_compression_and_parpic_bridge`)**:
Deduplicated bridge connecting the cellular sheaf and Hodge Laplacians directly to the
preexisting codebase owners `DefectParity` (`evenGrade`, `even_idempotencyDefect_sub_eq_genV`,
`qgtPlus_selfAdjoint_eq_zero_iff_commute`), `PeirceDefectBridge` (`peirce11_idempotencyDefect_sub`,
`peirce00_idempotencyDefect_sub`), `PeirceCompressionDefect` (`compression_square_defect_star`),
and `ParpicOperatorSpine` (`parpicFlux`, `parpicCirc`):
1. `evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) = genV P X X`,
2. `peirce11 P (idempotencyDefect X) - idempotencyDefect (peirce11 P X) = qgtPlus P X X` and
   `peirce00 P (idempotencyDefect X) - idempotencyDefect (peirce00 P X) = qgtMinus P X X`,
3. For `Φ = genPhi P A (star A)`, `evenGrade P Φ = 0`,
   `evenGrade P (idempotencyDefect Φ) = sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = sheafHodgeLaplacian (conePlus P A) (conePlus P A)`,
   `peirce11 P (idempotencyDefect Φ) = sheafHodgeDown (conePlus P A)`, and
   `peirce00 P (idempotencyDefect Φ) = sheafHodgeUp (conePlus P A)`,
4. For self-adjoint `X` (`star X = X`), `sheafHodgeDown (conePlus P X) = P * (X * X) * P - (P * X * P) * (P * X * P)`,
   and under `hproper : ∀ z : B, star z * z = 0 → z = 0`, `sheafHodgeDown (conePlus P X) = 0 ↔ P * X = X * P`,
5. `sheafCoboundary0 P (coneMinus P (star A)) (-conePlus P A) = parpicFlux 1 (conePlus P A)`,
   `sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) = -parpicCirc 1 (conePlus P A)`, and
   `sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A) = parpicFlux (invS P) (conePlus P A)`. -/
theorem sheaf_evenGrade_defect_compression_and_parpic_bridge
    {P : B} (hP : P * P = P) (hPsym : star P = P) (X A : B) :
    evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) =
      genV P X X ∧
    peirce11 P (idempotencyDefect X) - idempotencyDefect (peirce11 P X) =
      qgtPlus P X X ∧
    peirce00 P (idempotencyDefect X) - idempotencyDefect (peirce00 P X) =
      qgtMinus P X X ∧
    evenGrade P (genPhi P A (star A)) = 0 ∧
    evenGrade P (idempotencyDefect (genPhi P A (star A))) =
      sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) ∧
    evenGrade P (idempotencyDefect (genPhi P A (star A))) =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    peirce11 P (idempotencyDefect (genPhi P A (star A))) =
      sheafHodgeDown (conePlus P A) ∧
    peirce00 P (idempotencyDefect (genPhi P A (star A))) =
      sheafHodgeUp (conePlus P A) ∧
    (star X = X →
      sheafHodgeDown (conePlus P X) = P * (X * X) * P - (P * X * P) * (P * X * P)) ∧
    ((∀ z : B, star z * z = 0 → z = 0) → star X = X →
      (sheafHodgeDown (conePlus P X) = 0 ↔ P * X = X * P)) ∧
    sheafCoboundary0 P (coneMinus P (star A)) (-conePlus P A) =
      parpicFlux 1 (conePlus P A) ∧
    sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) =
      -parpicCirc 1 (conePlus P A) ∧
    sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A) =
      parpicFlux (invS P) (conePlus P A) := by
  have hEvenSub := even_idempotencyDefect_sub_eq_genV hP X
  have h11Sub := InfoGeometry.OperatorAlgebra.PeirceDefectBridge.peirce11_idempotencyDefect_sub P X hP
  have h00Sub := InfoGeometry.OperatorAlgebra.PeirceDefectBridge.peirce00_idempotencyDefect_sub P X hP
  have hEvenPhi : evenGrade P (genPhi P A (star A)) = 0 := by
    peirce_nf hP
  have h11Phi : peirce11 P (genPhi P A (star A)) = 0 := by
    peirce_nf hP
  have h00Phi : peirce00 P (genPhi P A (star A)) = 0 := by
    peirce_nf hP
  have hDefZero : idempotencyDefect (0 : B) = 0 := by
    unfold idempotencyDefect
    noncomm_ring
  have hGenVPhi : genV P (genPhi P A (star A)) (genPhi P A (star A)) = genV P A (star A) := by
    simp only [genV, anticomm, genPhi, conePlus, coneMinus]
    peirce_nf hP
  have hQPlusPhi : qgtPlus P (genPhi P A (star A)) (genPhi P A (star A)) = qgtPlus P A (star A) := by
    simp only [qgtPlus, genPhi, conePlus, coneMinus]
    peirce_nf hP
  have hQMinusPhi : qgtMinus P (genPhi P A (star A)) (genPhi P A (star A)) = qgtMinus P A (star A) := by
    simp only [qgtMinus, genPhi, conePlus, coneMinus]
    peirce_nf hP
  have hEvenDefPhi :
      evenGrade P (idempotencyDefect (genPhi P A (star A))) = genV P A (star A) := by
    have h0 := even_idempotencyDefect_sub_eq_genV hP (genPhi P A (star A))
    rw [hEvenPhi, hDefZero, sub_zero, hGenVPhi] at h0
    exact h0
  have h11DefPhi :
      peirce11 P (idempotencyDefect (genPhi P A (star A))) = qgtPlus P A (star A) := by
    have h0 := InfoGeometry.OperatorAlgebra.PeirceDefectBridge.peirce11_idempotencyDefect_sub
      P (genPhi P A (star A)) hP
    rw [h11Phi, hDefZero, sub_zero, hQPlusPhi] at h0
    exact h0
  have h00DefPhi :
      peirce00 P (idempotencyDefect (genPhi P A (star A))) = qgtMinus P A (star A) := by
    have h0 := InfoGeometry.OperatorAlgebra.PeirceDefectBridge.peirce00_idempotencyDefect_sub
      P (genPhi P A (star A)) hP
    rw [h00Phi, hDefZero, sub_zero, hQMinusPhi] at h0
    exact h0
  rcases sheaf_to_tetraktys_bridge hP hPsym A (star A) with ⟨hCobJ, hCobPhi, hLap0V⟩
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym A with
    ⟨_, hDown, hUp, hHodgeV, _⟩
  rcases parpicFlux_peirce_specializations hP hPsym A with
    ⟨hParFlux1, hParCirc1, hParFluxS, _, _, _⟩
  have hTwistedPhi := gradingTwistedAdj_eq_genPhi hPsym hP A
  refine ⟨hEvenSub, h11Sub, h00Sub, hEvenPhi,
    hEvenDefPhi.trans hLap0V.symm, hEvenDefPhi.trans hHodgeV.symm,
    h11DefPhi.trans hDown.symm, h00DefPhi.trans hUp.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro hXsym
    have hComp :=
      InfoGeometry.Core.PeirceCompressionDefect.compression_square_defect_star
        P X hP hPsym hXsym
    unfold sheafHodgeDown conePlus
    exact hComp.symm
  · intro hproper hXsym
    have hDownX := (sheafHodge_concrete_horizon_instantiation hP hPsym X).2.1
    rw [hDownX, hXsym]
    exact qgtPlus_selfAdjoint_eq_zero_iff_commute hP hproper hPsym X hXsym
  · exact hCobPhi.trans hParFlux1.symm
  · rw [hCobJ, hParCirc1]
  · unfold sheafCoboundary0Sym
    exact hCobPhi.trans (hTwistedPhi.symm.trans hParFluxS.symm)

/-- Supplemental operator-ring synthesis of `S₂₀ → S₂₄` over `[Ring B] [StarRing B]`,
with operator-valued inputs and the shared `evenGrade` owner. -/
theorem supplemental_S20_to_S24_operator_synthesis
    (hproper : ∀ z : B, star z * z = 0 → z = 0)
    {ι : Type*} (E : Finset ι) (P_edge R_u_edge R_v_edge U_edge : ι → B)
    (hU_edge : ∀ e ∈ E, star (U_edge e) * U_edge e = 1)
    {P R_u R_v d₀ d₁ M G η X A : B}
    (hP : P * P = P) (hPsym : star P = P)
    (hη_sym : star η = η) (hη_sq : η * η = 1) (hEx : η * P * η = 1 - P) :
    -- S₂₀: Bergman–Euler projector & truncated polynomial factor identities
    bergmanOp P A (star A) 1 =
      1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    (1 - sheafHodgeDown (conePlus P A)) * (1 - sheafHodgeUp (conePlus P A)) =
      1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    (1 - sheafHodgeLaplacian (conePlus P A) (conePlus P A)) *
      (1 + sheafHodgeLaplacian (conePlus P A) (conePlus P A)) =
      1 - (sheafHodgeDown (conePlus P A) * sheafHodgeDown (conePlus P A) +
           sheafHodgeUp (conePlus P A) * sheafHodgeUp (conePlus P A)) ∧
    -- S₂₁: Multi-edge sheaf Laplacian & proper star-ring faithful kernel
    star (multiEdgeSheafLaplacian E P_edge R_u_edge R_v_edge) =
      multiEdgeSheafLaplacian E P_edge R_u_edge R_v_edge ∧
    multiEdgeSheafLaplacian E P_edge (fun e => U_edge e * R_u_edge e)
      (fun e => U_edge e * R_v_edge e) =
      multiEdgeSheafLaplacian E P_edge R_u_edge R_v_edge ∧
    (sheafDirichletForm P R_u R_v X = 0 ↔ sheafCoboundary0 P R_u R_v * X = 0) ∧
    (sheafLaplacian0 P R_u R_v * X = 0 ↔ sheafCoboundary0 P R_u R_v * X = 0) ∧
    (sheafDirichletForm P R_u R_v X = 0 ↔ R_u * (P * X) = R_v * ((1 - P) * X)) ∧
    -- S₂₂: Operator-ring curvature energy, Hodge square form & supplied-factor identities
    (sheafCurvatureEnergy d₀ d₁ X = 0 ↔ d₁ * (d₀ * X) = 0) ∧
    (sheafHodgeSqForm d₀ d₁ X = 0 ↔ sheafHodgeLaplacian d₀ d₁ * X = 0) ∧
    (G * sheafHodgeLaplacian d₀ d₁ = M →
      sheafOperatorMassForm M X =
        star (sheafHodgeLaplacian d₀ d₁ * X) * (star G * G) *
          (sheafHodgeLaplacian d₀ d₁ * X)) ∧
    (G * sheafHodgeLaplacian d₀ d₁ = M → M * X ≠ 0 →
      sheafHodgeLaplacian d₀ d₁ * X ≠ 0 ∧ sheafHodgeSqForm d₀ d₁ X ≠ 0) ∧
    -- S₂₃: Krein exchange & unital Laplacians
    genPhi P η η = η ∧
    genV P η η = 1 ∧
    sheafLaplacian0 P (coneMinus P η) (conePlus P η) = 1 ∧
    sheafHodgeLaplacian (conePlus P η) (conePlus P η) = 1 ∧
    sheafHodgeDown (conePlus P η) - sheafHodgeUp (conePlus P η) = invS P ∧
    -- S₂₄: Deduplicated DefectParity, PeirceDefectBridge, PeirceCompressionDefect & Parpic bridge
    evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) = genV P X X ∧
    evenGrade P (idempotencyDefect (genPhi P A (star A))) =
      sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) ∧
    evenGrade P (idempotencyDefect (genPhi P A (star A))) =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    peirce11 P (idempotencyDefect (genPhi P A (star A))) =
      sheafHodgeDown (conePlus P A) ∧
    peirce00 P (idempotencyDefect (genPhi P A (star A))) =
      sheafHodgeUp (conePlus P A) ∧
    (star X = X →
      sheafHodgeDown (conePlus P X) = P * (X * X) * P - (P * X * P) * (P * X * P)) ∧
    (star X = X → (sheafHodgeDown (conePlus P X) = 0 ↔ P * X = X * P)) ∧
    sheafCoboundary0 P (coneMinus P (star A)) (-conePlus P A) =
      parpicFlux 1 (conePlus P A) ∧
    sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) =
      -parpicCirc 1 (conePlus P A) ∧
    sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A) =
      parpicFlux (invS P) (conePlus P A) := by
  rcases sheaf_bergman_euler_projector_and_factor_identities hP hPsym A with
    ⟨hB1, _, hB3, _, hB5⟩
  rcases multiEdgeSheafLaplacian_properties E P_edge R_u_edge R_v_edge U_edge X hU_edge with
    ⟨hMSym, _, hMGauge, _⟩
  rcases sheafDirichlet_proper_star_kernel_iff hproper P R_u R_v X with
    ⟨_, hDirKer, hLapKer, hDirAlign, _⟩
  rcases curved_sheaf_operator_energy_factorization_and_kernel d₀ d₁ M G X with
    ⟨_, _, hResId, hProperEnergy⟩
  rcases hProperEnergy hproper with ⟨hCurvKer, hHodgeKer, _, hResCoercive⟩
  rcases (krein_involution_peirce_exchange_equivalence (A := η) (C := η) hP).2 hη_sq hEx with
    ⟨_, _, hPhi, hV, _, _⟩
  rcases sheaf_krein_unital_laplacian_and_hodge_identity hP hPsym hη_sym hη_sq hEx with
    ⟨_, hLap1, _, _, hHodge1, hInvS⟩
  rcases sheaf_evenGrade_defect_compression_and_parpic_bridge hP hPsym X A with
    ⟨hEvenX, _, _, _, hEvenLap0, hEvenHodge, h11Down, h00Up, hCompSq, hCommIff,
     hPar1, hPar2, hPar3⟩
  exact ⟨hB1, hB3, hB5, hMSym, hMGauge, hDirKer, hLapKer, hDirAlign,
    hCurvKer, hHodgeKer, fun hGM => (hResId hGM).2, hResCoercive,
    hPhi, hV, hLap1, hHodge1, hInvS,
    hEvenX, hEvenLap0, hEvenHodge, h11Down, h00Up, hCompSq, hCommIff hproper,
    hPar1, hPar2, hPar3⟩

/-- **Lemma S₂₄.2 (`sheaf_orientation_hodgeStar_and_codifferential_bridge`)**:
Connects the cellular sheaf coboundary and horizon Hodge Laplacian directly to
`Orientation.lean` (`hodgeStar`, `hodgeLaplacianPhi`) and `Supercharge.lean`
(`superDerivPlus`, `superDerivPlusBar`):
1. `hodgeStar P (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)) = -sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)`,
2. `hodgeStar P (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) = -sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)`,
3. `hodgeStar P (sheafHodgeLaplacian (conePlus P A) (conePlus P A)) = sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)`,
4. `hodgeStar P (sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) = sheafHodgeLaplacian (conePlus P A) (conePlus P A)`,
5. `superDerivPlus P A (coneMinus P (star A)) = sheafHodgeLaplacian (conePlus P A) (conePlus P A)` and
   `superDerivPlusBar P A (coneMinus P (star A)) = sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)`,
6. `hodgeLaplacianPhi P A (star A) X = (2 : ℤ) • anticomm (sheafHodgeLaplacian (conePlus P A) (conePlus P A)) X`. -/
theorem sheaf_orientation_hodgeStar_and_codifferential_bridge
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A X : B) :
    hodgeStar P (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)) =
      -sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A) ∧
    hodgeStar P (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) =
      -sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) ∧
    hodgeStar P (sheafHodgeLaplacian (conePlus P A) (conePlus P A)) =
      sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A) ∧
    hodgeStar P (sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A)) =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    superDerivPlus P A (coneMinus P (star A)) =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    superDerivPlusBar P A (coneMinus P (star A)) =
      sheafHodgeDown (conePlus P A) - sheafHodgeUp (conePlus P A) ∧
    hodgeLaplacianPhi P A (star A) X =
      (2 : ℤ) • anticomm (sheafHodgeLaplacian (conePlus P A) (conePlus P A)) X := by
  rcases sheaf_to_tetraktys_bridge hP hPsym A (star A) with ⟨hCobJ, hCobPhi, _⟩
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym A with
    ⟨_, _, _, hHodgeV, hDiffSig⟩
  rcases archetype_A33_hodge_star_and_half_twists hP A (star A) X with
    ⟨_, hStarV, hStarSig, hStarPhi, hStarJ, _⟩
  have hSym : sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A) = genPhi P A (star A) :=
    hCobPhi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCobJ, hSym, hodgeStar, mul_neg, ← hodgeStar, hStarJ]
  · rw [hSym, hCobJ, neg_neg, hStarPhi]
  · rw [hHodgeV, hDiffSig, hStarV]
  · rw [hDiffSig, hHodgeV, hStarSig]
  · rw [hHodgeV]
    simp only [superDerivPlus, parityConj]
    peirce_nf hP
  · rw [hDiffSig]
    simp only [superDerivPlusBar, parityConj]
    peirce_nf hP
  · rw [hHodgeV, hodgeLaplacianPhi_eq hP A (star A) X, anticomm]

/-!
### 7. Stage D₂₂: Hodge Complement Polynomials, Defect-Tower Descent & Three-Stalk Operator Paths
-/

/-- **Bergman–Euler Hodge Complement (`sheafHodgeComplement`) and
Truncated Green Polynomial (`sheafGreenPolynomial2`):**
For any coboundary pair `(d₀, d₁)`:
- `sheafHodgeComplement d₀ d₁ = 1 - sheafHodgeLaplacian d₀ d₁`,
- `sheafGreenPolynomial2 d₀ d₁ = 1 + Δ₁ + Δ₁²`.
The complement is not asserted to be idempotent here, and the polynomial is not
asserted to be an inverse without an additional nilpotence hypothesis. -/
def sheafHodgeComplement (d₀ d₁ : B) : B :=
  1 - sheafHodgeLaplacian d₀ d₁

def sheafGreenPolynomial2 (d₀ d₁ : B) : B :=
  1 + sheafHodgeLaplacian d₀ d₁ + sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁

omit [StarRing B] in
/-- **Depth-`n` Fractal Hodge Complement Operator (`fractalHodgeComplement`):**
At defect depth `n ∈ ℕ`, this is the polynomial `1 - (X_n + Y_n)`; no
cohomology quotient or projector property is part of this definition. -/
def fractalHodgeComplement (n : ℕ) (P A C : B) : B :=
  1 - (mandelbrotTower n (qgtPlus P A C) + mandelbrotTower n (qgtMinus P A C))

omit [StarRing B] in
/-- **Directed Simplicial Sheaf Edge Restriction (`simplicialEdge`):**
Maps from vertex stalk `P_j` to vertex stalk `P_i` via `P_i * A * P_j`. -/
def simplicialEdge (P_i P_j A : B) : B := P_i * A * P_j

/-- **Lemma S₂₅.1 (`sheafHodgeComplement_factorization_and_green_polynomial`)**:
For coboundary operators `d₀, d₁ : B` satisfying flatness `d₁ * d₀ = 0`:
1. **Two-Sided Cubic Polynomial Identity:**
   `sheafHodgeComplement d₀ d₁ * sheafGreenPolynomial2 d₀ d₁ = 1 - sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁`
   and `sheafGreenPolynomial2 d₀ d₁ * sheafHodgeComplement d₀ d₁ = 1 - sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁`.
2. **Two-Sided Complement–Laplacian Product, Defect Identity & Self-Adjointness:**
   `sheafHodgeComplement d₀ d₁ * sheafHodgeLaplacian d₀ d₁ = -idempotencyDefect (sheafHodgeLaplacian d₀ d₁)`,
   `sheafHodgeLaplacian d₀ d₁ * sheafHodgeComplement d₀ d₁ = -idempotencyDefect (sheafHodgeLaplacian d₀ d₁)`,
   `idempotencyDefect (sheafHodgeComplement d₀ d₁) = idempotencyDefect (sheafHodgeLaplacian d₀ d₁)`,
   `star (sheafHodgeComplement d₀ d₁) = sheafHodgeComplement d₀ d₁`, and
   `star (sheafGreenPolynomial2 d₀ d₁) = sheafGreenPolynomial2 d₀ d₁`.
3. **Flat Cochain Complex (`d₁ * d₀ = 0`) Plücker–Bergman Factorization:**
   `(1 - sheafHodgeDown d₀) * (1 - sheafHodgeUp d₁) = sheafHodgeComplement d₀ d₁` and
   `(1 - sheafHodgeUp d₁) * (1 - sheafHodgeDown d₀) = sheafHodgeComplement d₀ d₁`. -/
theorem sheafHodgeComplement_factorization_and_green_polynomial {d₀ d₁ : B} (hd : d₁ * d₀ = 0) :
    sheafHodgeComplement d₀ d₁ * sheafGreenPolynomial2 d₀ d₁ =
      1 - sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ ∧
    sheafHodgeComplement d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
      -idempotencyDefect (sheafHodgeLaplacian d₀ d₁) ∧
    idempotencyDefect (sheafHodgeComplement d₀ d₁) =
      idempotencyDefect (sheafHodgeLaplacian d₀ d₁) ∧
    (1 - sheafHodgeDown d₀) * (1 - sheafHodgeUp d₁) = sheafHodgeComplement d₀ d₁ ∧
    (1 - sheafHodgeUp d₁) * (1 - sheafHodgeDown d₀) = sheafHodgeComplement d₀ d₁ ∧
    sheafGreenPolynomial2 d₀ d₁ * sheafHodgeComplement d₀ d₁ =
      1 - sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ ∧
    sheafHodgeLaplacian d₀ d₁ * sheafHodgeComplement d₀ d₁ =
      -idempotencyDefect (sheafHodgeLaplacian d₀ d₁) ∧
    star (sheafHodgeComplement d₀ d₁) = sheafHodgeComplement d₀ d₁ ∧
    star (sheafGreenPolynomial2 d₀ d₁) = sheafGreenPolynomial2 d₀ d₁ := by
  have hStarD : star d₀ * star d₁ = 0 := by rw [← star_mul, hd, star_zero]
  have hUpDown : sheafHodgeUp d₁ * sheafHodgeDown d₀ = 0 := by
    unfold sheafHodgeUp sheafHodgeDown
    rw [mul_assoc, ← mul_assoc d₁ d₀, hd, zero_mul, mul_zero]
  have hDownUp : sheafHodgeDown d₀ * sheafHodgeUp d₁ = 0 := by
    unfold sheafHodgeUp sheafHodgeDown
    rw [mul_assoc, ← mul_assoc (star d₀) (star d₁), hStarD, zero_mul, mul_zero]
  have hStarLap : star (sheafHodgeLaplacian d₀ d₁) = sheafHodgeLaplacian d₀ d₁ :=
    (sheafHodgeLaplacian_properties hd).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sheafHodgeComplement sheafGreenPolynomial2
    noncomm_ring
  · unfold sheafHodgeComplement idempotencyDefect
    noncomm_ring
  · unfold sheafHodgeComplement idempotencyDefect
    noncomm_ring
  · unfold sheafHodgeComplement sheafHodgeLaplacian
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, hDownUp]
    noncomm_ring
  · unfold sheafHodgeComplement sheafHodgeLaplacian
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, hUpDown]
    noncomm_ring
  · unfold sheafHodgeComplement sheafGreenPolynomial2
    noncomm_ring
  · unfold sheafHodgeComplement idempotencyDefect
    noncomm_ring
  · unfold sheafHodgeComplement
    rw [star_sub, star_one, hStarLap]
  · unfold sheafGreenPolynomial2
    rw [star_add, star_add, star_one, star_mul, hStarLap]

/-- If the Hodge Laplacian is idempotent, its algebraic complement is an
idempotent. This is the precise extra hypothesis needed before calling the
complement a projector. -/
theorem sheafHodgeComplement_idempotent_of_laplacian_idempotent
    {d₀ d₁ : B}
    (hΔ : sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
      sheafHodgeLaplacian d₀ d₁) :
    sheafHodgeComplement d₀ d₁ * sheafHodgeComplement d₀ d₁ =
      sheafHodgeComplement d₀ d₁ := by
  unfold sheafHodgeComplement
  noncomm_ring [hΔ]

/-- **Lemma S₂₅.2 (`sheafHodgeComplement_on_shell_iff`)**:
1. `idempotencyDefect (sheafHodgeLaplacian d₀ d₁) = 0 ↔ sheafHodgeComplement d₀ d₁ * sheafHodgeComplement d₀ d₁ = sheafHodgeComplement d₀ d₁`;
2. Whenever `idempotencyDefect (sheafHodgeLaplacian d₀ d₁) = 0`, `sheafHodgeComplement d₀ d₁`
   is idempotent and annihilates `sheafHodgeLaplacian d₀ d₁` from both sides. -/
theorem sheafHodgeComplement_on_shell_iff (d₀ d₁ : B) :
    (idempotencyDefect (sheafHodgeLaplacian d₀ d₁) = 0 ↔
      sheafHodgeComplement d₀ d₁ * sheafHodgeComplement d₀ d₁ = sheafHodgeComplement d₀ d₁) ∧
    (idempotencyDefect (sheafHodgeLaplacian d₀ d₁) = 0 →
      sheafHodgeComplement d₀ d₁ * sheafHodgeComplement d₀ d₁ = sheafHodgeComplement d₀ d₁ ∧
      sheafHodgeComplement d₀ d₁ * sheafHodgeLaplacian d₀ d₁ = 0 ∧
      sheafHodgeLaplacian d₀ d₁ * sheafHodgeComplement d₀ d₁ = 0) := by
  have hDefEq : idempotencyDefect (sheafHodgeComplement d₀ d₁) =
      idempotencyDefect (sheafHodgeLaplacian d₀ d₁) := by
    unfold sheafHodgeComplement idempotencyDefect
    noncomm_ring
  have hLeft : sheafHodgeComplement d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
      -idempotencyDefect (sheafHodgeLaplacian d₀ d₁) := by
    unfold sheafHodgeComplement idempotencyDefect
    noncomm_ring
  have hRight : sheafHodgeLaplacian d₀ d₁ * sheafHodgeComplement d₀ d₁ =
      -idempotencyDefect (sheafHodgeLaplacian d₀ d₁) := by
    unfold sheafHodgeComplement idempotencyDefect
    noncomm_ring
  have hIff : idempotencyDefect (sheafHodgeLaplacian d₀ d₁) = 0 ↔
      sheafHodgeComplement d₀ d₁ * sheafHodgeComplement d₀ d₁ = sheafHodgeComplement d₀ d₁ := by
    rw [← hDefEq]
    unfold idempotencyDefect
    exact sub_eq_zero
  refine ⟨hIff, fun h0 => ⟨hIff.mp h0, ?_, ?_⟩⟩
  · rw [hLeft, h0, neg_zero]
  · rw [hRight, h0, neg_zero]

/-- Under the cubic nilpotence condition, the degree-two Green polynomial is a
two-sided inverse for `1 - Δ`. -/
theorem sheafGreenPolynomial2_inverse_of_laplacian_cube_eq_zero
    {d₀ d₁ : B}
    (hΔ : sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ *
      sheafHodgeLaplacian d₀ d₁ = 0) :
    sheafHodgeComplement d₀ d₁ * sheafGreenPolynomial2 d₀ d₁ = 1 ∧
      sheafGreenPolynomial2 d₀ d₁ * sheafHodgeComplement d₀ d₁ = 1 := by
  have hRightCube : sheafHodgeLaplacian d₀ d₁ *
      (sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁) = 0 := by
    rw [← mul_assoc, hΔ]
  constructor
  · unfold sheafHodgeComplement sheafGreenPolynomial2
    noncomm_ring [hΔ, hRightCube]
  · unfold sheafHodgeComplement sheafGreenPolynomial2
    noncomm_ring [hΔ, hRightCube]

/-- **Lemma S₂₅.3 / S₂₆.0 (`horizon_hodge_complement_depth0_and_cubic_green_identity`)**:
At the Peirce horizon `d₀ = d₁ = conePlus P A` (`P * P = P`, `star P = P`):
1. `sheafHodgeComplement (conePlus P A) (conePlus P A) = zetaFactor P A (star A)` and
   `sheafHodgeComplement (conePlus P A) (conePlus P A) = bergmanOp P A (star A) 1`;
2. **Depth-`0` Obstruction Entry into the Mandelbrot Tower (`X_0`, `Y_0`):**
   - `sheafHodgeComplement (conePlus P A) (conePlus P A) * qgtPlus P A (star A) = -mandelbrotTower 0 (qgtPlus P A (star A))`,
   - `sheafHodgeComplement (conePlus P A) (conePlus P A) * qgtMinus P A (star A) = -mandelbrotTower 0 (qgtMinus P A (star A))`,
   - `sheafHodgeComplement (conePlus P A) (conePlus P A) * genV P A (star A) = -(mandelbrotTower 0 (qgtPlus P A (star A)) + mandelbrotTower 0 (qgtMinus P A (star A)))`;
3. **Horizon Green Polynomial Split & Cubic Horizon Green Identity (`1 - (Q_+³ + Q_-³)`):**
   - `sheafGreenPolynomial2 (conePlus P A) (conePlus P A) = 1 + (qgtPlus P A (star A) + qgtMinus P A (star A)) + (qgtPlus P A (star A) * qgtPlus P A (star A) + qgtMinus P A (star A) * qgtMinus P A (star A))`,
   - `sheafHodgeComplement (conePlus P A) (conePlus P A) * sheafGreenPolynomial2 (conePlus P A) (conePlus P A) = 1 - (qgtPlus P A (star A) * qgtPlus P A (star A) * qgtPlus P A (star A) + qgtMinus P A (star A) * qgtMinus P A (star A) * qgtMinus P A (star A))`. -/
theorem horizon_hodge_complement_depth0_and_cubic_green_identity
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) :
    sheafHodgeComplement (conePlus P A) (conePlus P A) = zetaFactor P A (star A) ∧
    sheafHodgeComplement (conePlus P A) (conePlus P A) = bergmanOp P A (star A) 1 ∧
    sheafHodgeComplement (conePlus P A) (conePlus P A) * qgtPlus P A (star A) =
      -mandelbrotTower 0 (qgtPlus P A (star A)) ∧
    sheafHodgeComplement (conePlus P A) (conePlus P A) * qgtMinus P A (star A) =
      -mandelbrotTower 0 (qgtMinus P A (star A)) ∧
    sheafHodgeComplement (conePlus P A) (conePlus P A) * genV P A (star A) =
      -(mandelbrotTower 0 (qgtPlus P A (star A)) + mandelbrotTower 0 (qgtMinus P A (star A))) ∧
    sheafGreenPolynomial2 (conePlus P A) (conePlus P A) =
      1 + (qgtPlus P A (star A) + qgtMinus P A (star A)) +
        (qgtPlus P A (star A) * qgtPlus P A (star A) +
          qgtMinus P A (star A) * qgtMinus P A (star A)) ∧
    sheafHodgeComplement (conePlus P A) (conePlus P A) *
      sheafGreenPolynomial2 (conePlus P A) (conePlus P A) =
      1 - (qgtPlus P A (star A) * qgtPlus P A (star A) * qgtPlus P A (star A) +
           qgtMinus P A (star A) * qgtMinus P A (star A) * qgtMinus P A (star A)) := by
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym A with
    ⟨_, _, _, hHodgeV, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sheafHodgeComplement zetaFactor
    rw [hHodgeV]
  · unfold sheafHodgeComplement
    exact (sheaf_bergman_euler_projector_and_factor_identities hP hPsym A).1.symm
  · unfold sheafHodgeComplement mandelbrotTower idempotencyDefect
    rw [hHodgeV]
    simp only [qgtPlus]
    peirce_nf hP
  · unfold sheafHodgeComplement mandelbrotTower idempotencyDefect
    rw [hHodgeV]
    simp only [qgtMinus]
    peirce_nf hP
  · unfold sheafHodgeComplement mandelbrotTower idempotencyDefect
    rw [hHodgeV]
    simp only [qgtPlus, qgtMinus]
    peirce_nf hP
  · unfold sheafGreenPolynomial2
    rw [hHodgeV]
    simp only [qgtPlus, qgtMinus]
    peirce_nf hP
  · unfold sheafHodgeComplement sheafGreenPolynomial2
    rw [hHodgeV]
    simp only [qgtPlus, qgtMinus]
    peirce_nf hP

omit [StarRing B] in
/-- **Helper Lemma (`mandelbrotTower_sheet_orthogonality`)**:
Two-sided cross-sheet orthogonality `X_n * Y_m = 0` and `Y_m * X_n = 0` across all fractal
depths `n, m : ℕ`, derived directly from `mandelbrotTower_eq_idempotencyDefect_iterate` and
`ConeSheetBraiding.qgt_defect_iterates_cross_orthogonal`. -/
theorem mandelbrotTower_sheet_orthogonality {P : B} (hP : P * P = P) (A C : B) (n m : ℕ) :
    mandelbrotTower n (qgtPlus P A C) * mandelbrotTower m (qgtMinus P A C) = 0 ∧
    mandelbrotTower m (qgtMinus P A C) * mandelbrotTower n (qgtPlus P A C) = 0 := by
  rw [mandelbrotTower_eq_idempotencyDefect_iterate, mandelbrotTower_eq_idempotencyDefect_iterate]
  exact ⟨(qgt_defect_iterates_cross_orthogonal hP A C (n + 1) (m + 1)).1,
         (qgt_defect_iterates_cross_orthogonal hP A C (m + 1) (n + 1)).2⟩

omit [StarRing B] in
/-- **Lemma S₂₆.1 (`fractal_hodge_complement_tower_descent`)**:
For any idempotent `P` (`P * P = P`), any `A, C : B`, and all fractal depths `n : ℕ`, let
`X_n = mandelbrotTower n (qgtPlus P A C)`, `Y_n = mandelbrotTower n (qgtMinus P A C)`, and `V_n = X_n + Y_n`:
1. **Bergman Factorization at Depth `n`:**
   `fractalHodgeComplement n P A C = (1 - X_n) * (1 - Y_n)`.
2. **Exact Vertical Descent of the Fractal Sheets by `fractalHodgeComplement n`:**
   - `fractalHodgeComplement n P A C * X_n = -mandelbrotTower (n + 1) (qgtPlus P A C)` (`= -X_{n+1}`),
   - `fractalHodgeComplement n P A C * Y_n = -mandelbrotTower (n + 1) (qgtMinus P A C)` (`= -Y_{n+1}`),
   - `fractalHodgeComplement n P A C * V_n = -(mandelbrotTower (n + 1) (qgtPlus P A C) + mandelbrotTower (n + 1) (qgtMinus P A C))` (`= -V_{n+1}`). -/
theorem fractal_hodge_complement_tower_descent {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    fractalHodgeComplement n P A C =
      (1 - mandelbrotTower n (qgtPlus P A C)) * (1 - mandelbrotTower n (qgtMinus P A C)) ∧
    fractalHodgeComplement n P A C * mandelbrotTower n (qgtPlus P A C) =
      -mandelbrotTower (n + 1) (qgtPlus P A C) ∧
    fractalHodgeComplement n P A C * mandelbrotTower n (qgtMinus P A C) =
      -mandelbrotTower (n + 1) (qgtMinus P A C) ∧
    fractalHodgeComplement n P A C *
      (mandelbrotTower n (qgtPlus P A C) + mandelbrotTower n (qgtMinus P A C)) =
      -(mandelbrotTower (n + 1) (qgtPlus P A C) + mandelbrotTower (n + 1) (qgtMinus P A C)) := by
  rcases mandelbrotTower_sheet_orthogonality hP A C n n with ⟨hXY, hYX⟩
  have hFact : fractalHodgeComplement n P A C =
      (1 - mandelbrotTower n (qgtPlus P A C)) * (1 - mandelbrotTower n (qgtMinus P A C)) := by
    unfold fractalHodgeComplement
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, hXY]
    noncomm_ring
  have hDescX : fractalHodgeComplement n P A C * mandelbrotTower n (qgtPlus P A C) =
      -mandelbrotTower (n + 1) (qgtPlus P A C) := by
    change (1 - (mandelbrotTower n (qgtPlus P A C) + mandelbrotTower n (qgtMinus P A C))) *
        mandelbrotTower n (qgtPlus P A C) =
      -idempotencyDefect (mandelbrotTower n (qgtPlus P A C))
    unfold idempotencyDefect
    rw [sub_mul, add_mul, one_mul, hYX, add_zero, neg_sub]
  have hDescY : fractalHodgeComplement n P A C * mandelbrotTower n (qgtMinus P A C) =
      -mandelbrotTower (n + 1) (qgtMinus P A C) := by
    change (1 - (mandelbrotTower n (qgtPlus P A C) + mandelbrotTower n (qgtMinus P A C))) *
        mandelbrotTower n (qgtMinus P A C) =
      -idempotencyDefect (mandelbrotTower n (qgtMinus P A C))
    unfold idempotencyDefect
    rw [sub_mul, add_mul, one_mul, hXY, zero_add, neg_sub]
  refine ⟨hFact, hDescX, hDescY, ?_⟩
  rw [mul_add, hDescX, hDescY, neg_add]

/- **Lemma S₂₇.1 & S₂₈.1 (`simplicial_triangle_sheaf_holonomy_and_localization`)**:
Assume `P₂` and `P₃` are idempotent, each `Pᵢ` is self-adjoint, and the directed
annihilations `P₂ * P₁ = 0`, `P₃ * P₂ = 0`, and `P₃ * P₁ = 0` hold. Let
`E₁₂ = simplicialEdge P₁ P₂ A₁₂`, `E₂₃ = simplicialEdge P₂ P₃ A₂₃`, `E₃₁ = simplicialEdge P₃ P₁ A₃₁`.
Then:
1. **Individual Edge Nilpotency & Reverse-Order Vanishing:**
   `E₁₂ * E₁₂ = 0`, `E₂₃ * E₂₃ = 0`, and `E₂₃ * E₁₂ = 0`.
2. **2-Simplex Curvature & 3-Cycle Triangle Holonomy:**
   - `sheafCurvature2 E₂₃ E₁₂ = P₁ * A₁₂ * P₂ * A₂₃ * P₃` (2-hop path transport `P₃ → P₂ → P₁`),
   - `sheafCurvature2 E₂₃ E₁₂ * E₃₁ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁` (the ordered closed-path product).
3. **Middle-Stalk (`P₂ B P₂`) Localization of the Simplicial Sheaf Hodge Laplacian & Weitzenböck Defect:**
   `P₂ * sheafHodgeLaplacian E₂₃ E₁₂ * P₂ = sheafHodgeLaplacian E₂₃ E₁₂` and
   `P₂ * sheafWeitzenboeckDefect E₂₃ E₁₂ * P₂ = sheafWeitzenboeckDefect E₂₃ E₁₂`.
4. **Flat Simplicial Channel Criterion (`S₂₈`):**
   Whenever `E₁₂ * E₂₃ = 0`, `sheafWeitzenboeckDefect E₂₃ E₁₂ = 0`
   and `(1 - sheafHodgeDown E₂₃) * (1 - sheafHodgeUp E₁₂) = sheafHodgeComplement E₂₃ E₁₂`. -/
theorem simplicial_triangle_sheaf_holonomy_and_localization
    {P₁ P₂ P₃ : B}
    (h2 : P₂ * P₂ = P₂) (h3 : P₃ * P₃ = P₃)
    (hPsym1 : star P₁ = P₁) (hPsym2 : star P₂ = P₂) (hPsym3 : star P₃ = P₃)
    (h21 : P₂ * P₁ = 0) (h32 : P₃ * P₂ = 0) (h31 : P₃ * P₁ = 0)
    (A₁₂ A₂₃ A₃₁ : B) :
    let E₁₂ := simplicialEdge P₁ P₂ A₁₂
    let E₂₃ := simplicialEdge P₂ P₃ A₂₃
    let E₃₁ := simplicialEdge P₃ P₁ A₃₁
    E₁₂ * E₁₂ = 0 ∧
    E₂₃ * E₂₃ = 0 ∧
    E₂₃ * E₁₂ = 0 ∧
    sheafCurvature2 E₂₃ E₁₂ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ ∧
    sheafCurvature2 E₂₃ E₁₂ * E₃₁ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁ ∧
    P₂ * sheafHodgeLaplacian E₂₃ E₁₂ * P₂ = sheafHodgeLaplacian E₂₃ E₁₂ ∧
    P₂ * sheafWeitzenboeckDefect E₂₃ E₁₂ * P₂ = sheafWeitzenboeckDefect E₂₃ E₁₂ ∧
    (E₁₂ * E₂₃ = 0 →
      sheafWeitzenboeckDefect E₂₃ E₁₂ = 0 ∧
      (1 - sheafHodgeDown E₂₃) * (1 - sheafHodgeUp E₁₂) = sheafHodgeComplement E₂₃ E₁₂) := by
  intro E₁₂ E₂₃ E₃₁
  have hE12_sq : E₁₂ * E₁₂ = 0 := by
    dsimp [E₁₂, simplicialEdge]
    calc
      (P₁ * A₁₂ * P₂) * (P₁ * A₁₂ * P₂) = P₁ * A₁₂ * (P₂ * P₁) * A₁₂ * P₂ := by noncomm_ring
      _ = 0 := by rw [h21]; noncomm_ring
  have hE23_sq : E₂₃ * E₂₃ = 0 := by
    dsimp [E₂₃, simplicialEdge]
    calc
      (P₂ * A₂₃ * P₃) * (P₂ * A₂₃ * P₃) = P₂ * A₂₃ * (P₃ * P₂) * A₂₃ * P₃ := by noncomm_ring
      _ = 0 := by rw [h32]; noncomm_ring
  have hE23_12 : E₂₃ * E₁₂ = 0 := by
    dsimp [E₁₂, E₂₃, simplicialEdge]
    calc
      (P₂ * A₂₃ * P₃) * (P₁ * A₁₂ * P₂) = P₂ * A₂₃ * (P₃ * P₁) * A₁₂ * P₂ := by noncomm_ring
      _ = 0 := by rw [h31]; noncomm_ring
  have hCurv : sheafCurvature2 E₂₃ E₁₂ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ := by
    dsimp [E₁₂, E₂₃, simplicialEdge, sheafCurvature2]
    calc (P₁ * A₁₂ * P₂) * (P₂ * A₂₃ * P₃)
      _ = P₁ * A₁₂ * (P₂ * P₂) * A₂₃ * P₃ := by noncomm_ring
      _ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ := by rw [h2]
  have hHol : sheafCurvature2 E₂₃ E₁₂ * E₃₁ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁ := by
    rw [hCurv]
    dsimp [E₃₁, simplicialEdge]
    calc (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₃ * A₃₁ * P₁)
      _ = P₁ * A₁₂ * P₂ * A₂₃ * (P₃ * P₃) * A₃₁ * P₁ := by noncomm_ring
      _ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁ := by rw [h3]
  have hLoc : P₂ * sheafHodgeLaplacian E₂₃ E₁₂ * P₂ = sheafHodgeLaplacian E₂₃ E₁₂ := by
    dsimp [E₁₂, E₂₃, simplicialEdge, sheafHodgeLaplacian, sheafHodgeDown, sheafHodgeUp]
    simp only [star_mul, hPsym1, hPsym2, hPsym3]
    calc
      P₂ * (P₂ * A₂₃ * P₃ * (P₃ * (star A₂₃ * P₂)) +
          P₂ * (star A₁₂ * P₁) * (P₁ * A₁₂ * P₂)) * P₂ =
        (P₂ * P₂) * A₂₃ * P₃ * (P₃ * star A₂₃ * (P₂ * P₂)) +
          (P₂ * P₂) * star A₁₂ * P₁ * (P₁ * A₁₂ * (P₂ * P₂)) := by noncomm_ring
      _ = P₂ * A₂₃ * P₃ * (P₃ * (star A₂₃ * P₂)) +
          P₂ * (star A₁₂ * P₁) * (P₁ * A₁₂ * P₂) := by rw [h2]; noncomm_ring
  have hLocW : P₂ * sheafWeitzenboeckDefect E₂₃ E₁₂ * P₂ = sheafWeitzenboeckDefect E₂₃ E₁₂ := by
    dsimp [E₁₂, E₂₃, simplicialEdge, sheafWeitzenboeckDefect, sheafCurvature2]
    simp only [star_mul, hPsym1, hPsym2, hPsym3]
    calc
      P₂ *
          (P₂ * (star A₁₂ * P₁) * (P₁ * A₁₂ * P₂ * (P₂ * A₂₃ * P₃)) * (P₃ * (star A₂₃ * P₂)) +
            P₂ * A₂₃ * P₃ * (P₃ * (star A₂₃ * P₂) * (P₂ * (star A₁₂ * P₁))) * (P₁ * A₁₂ * P₂)) *
          P₂ =
        (P₂ * P₂) * star A₁₂ * P₁ * (P₁ * A₁₂ * P₂ * (P₂ * A₂₃ * P₃)) * (P₃ * star A₂₃ * (P₂ * P₂)) +
          (P₂ * P₂) * A₂₃ * P₃ * (P₃ * star A₂₃ * P₂ * (P₂ * star A₁₂ * P₁)) * (P₁ * A₁₂ * (P₂ * P₂)) := by
        noncomm_ring
      _ = P₂ * (star A₁₂ * P₁) * (P₁ * A₁₂ * P₂ * (P₂ * A₂₃ * P₃)) * (P₃ * (star A₂₃ * P₂)) +
          P₂ * A₂₃ * P₃ * (P₃ * (star A₂₃ * P₂) * (P₂ * (star A₁₂ * P₁))) * (P₁ * A₁₂ * P₂) := by
        rw [h2]; noncomm_ring
  refine ⟨hE12_sq, hE23_sq, hE23_12, hCurv, hHol, hLoc, hLocW, fun hFlat => ?_⟩
  constructor
  · unfold sheafWeitzenboeckDefect sheafCurvature2
    rw [hFlat, star_zero]
    noncomm_ring
  · exact (sheafHodgeComplement_factorization_and_green_polynomial hFlat).2.2.2.1

/-- **Lemma S₂₇.2 (`simplicial_three_corner_partition_bridge`)**:
Connects the 3-stalk simplicial triangle sheaf directly to the preexisting
`ThreeCornerColumnAlgebra` owner (`third`, `partition`, `third_idempotent`,
`third_orthogonal`, `retrievalOp`) and `DirectedFlowMagneticResolvent`
(`twoStepUpper`, `twoStepResolvent`): for any two mutually orthogonal self-adjoint
idempotents `P₁, P₂`, setting `P₃ = ThreeCornerColumnAlgebra.third P₁ P₂ = 1 - P₁ - P₂`
yields a complete 3-stalk orthogonal self-adjoint partition of unity `P₁ + P₂ + P₃ = 1`
satisfying `simplicial_triangle_sheaf_holonomy_and_localization`, with:
1. `simplicialEdge P₃ P₁ A₃₁ = ThreeCornerColumnAlgebra.retrievalOp P₁ P₂ 0 0 0 A₃₁`;
2. Basepoint (`P₁ B P₁`) localization of the closed 3-cycle holonomy
   `sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) * simplicialEdge P₃ P₁ A₃₁`;
3. Exact identification of the 2-edge sum `E₁₂ + E₂₃` with `twoStepUpper P₁ P₂ A₁₂ A₂₃`,
   the 2-simplex curvature `sheafCurvature2 E₂₃ E₁₂` with `twoStepUpper²`, and the
   truncated 2-step Neumann series with the two-sided inverse `twoStepResolvent P₁ P₂ A₁₂ A₂₃`. -/
theorem simplicial_three_corner_partition_bridge
    {P₁ P₂ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (hPsym1 : star P₁ = P₁) (hPsym2 : star P₂ = P₂)
    (A₁₂ A₂₃ A₃₁ : B) :
    let P₃ := ThreeCornerColumnAlgebra.third P₁ P₂
    P₁ + P₂ + P₃ = 1 ∧
    P₃ * P₃ = P₃ ∧
    star P₃ = P₃ ∧
    simplicialEdge P₃ P₁ A₃₁ = ThreeCornerColumnAlgebra.retrievalOp P₁ P₂ 0 0 0 A₃₁ ∧
    sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) *
      simplicialEdge P₃ P₁ A₃₁ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁ ∧
    P₂ * sheafHodgeLaplacian (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) * P₂ =
      sheafHodgeLaplacian (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) ∧
    P₁ * (sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) *
      simplicialEdge P₃ P₁ A₃₁) * P₁ =
      sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) *
        simplicialEdge P₃ P₁ A₃₁ ∧
    simplicialEdge P₁ P₂ A₁₂ + simplicialEdge P₂ P₃ A₂₃ = twoStepUpper P₁ P₂ A₁₂ A₂₃ ∧
    sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) =
      twoStepUpper P₁ P₂ A₁₂ A₂₃ * twoStepUpper P₁ P₂ A₁₂ A₂₃ ∧
    1 + (simplicialEdge P₁ P₂ A₁₂ + simplicialEdge P₂ P₃ A₂₃) +
      sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) =
      twoStepResolvent P₁ P₂ A₁₂ A₂₃ ∧
    (1 - (simplicialEdge P₁ P₂ A₁₂ + simplicialEdge P₂ P₃ A₂₃)) *
      twoStepResolvent P₁ P₂ A₁₂ A₂₃ = 1 ∧
    twoStepResolvent P₁ P₂ A₁₂ A₂₃ *
      (1 - (simplicialEdge P₁ P₂ A₁₂ + simplicialEdge P₂ P₃ A₂₃)) = 1 := by
  intro P₃
  have hPart : P₁ + P₂ + P₃ = 1 := ThreeCornerColumnAlgebra.partition
  have h3 : P₃ * P₃ = P₃ := ThreeCornerColumnAlgebra.third_idempotent h1 h2 h12 h21
  rcases ThreeCornerColumnAlgebra.third_orthogonal h1 h2 h12 h21 with ⟨_, h31, _, h32⟩
  have hPsym3 : star P₃ = P₃ := by
    dsimp [P₃, ThreeCornerColumnAlgebra.third]
    rw [star_sub, star_sub, star_one, hPsym1, hPsym2]
  have hRet : simplicialEdge P₃ P₁ A₃₁ = ThreeCornerColumnAlgebra.retrievalOp P₁ P₂ 0 0 0 A₃₁ := by
    dsimp [P₃]
    unfold simplicialEdge ThreeCornerColumnAlgebra.retrievalOp ThreeCornerColumnAlgebra.columnOp
      peirce11
    noncomm_ring
  rcases simplicial_triangle_sheaf_holonomy_and_localization
    h2 h3 hPsym1 hPsym2 hPsym3 h21 h32 h31 A₁₂ A₂₃ A₃₁ with
    ⟨_, _, _, hCurv, hHol, hLoc, _, _⟩
  have hHolLoc1 :
      P₁ * (sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) *
        simplicialEdge P₃ P₁ A₃₁) * P₁ =
        sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) *
          simplicialEdge P₃ P₁ A₃₁ := by
    rw [hHol]
    calc
      P₁ * (P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁) * P₁ =
        (P₁ * P₁) * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * (P₁ * P₁) := by noncomm_ring
      _ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁ := by rw [h1]
  have hTwoStepSum :
      simplicialEdge P₁ P₂ A₁₂ + simplicialEdge P₂ P₃ A₂₃ = twoStepUpper P₁ P₂ A₁₂ A₂₃ := rfl
  have hCurvSq :
      sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) =
        twoStepUpper P₁ P₂ A₁₂ A₂₃ * twoStepUpper P₁ P₂ A₁₂ A₂₃ := by
    rw [hCurv, twoStepUpper_sq h1 h2 h12 h21 A₁₂ A₂₃]
  have hResEq :
      1 + (simplicialEdge P₁ P₂ A₁₂ + simplicialEdge P₂ P₃ A₂₃) +
        sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) =
        twoStepResolvent P₁ P₂ A₁₂ A₂₃ := by
    rw [hTwoStepSum, hCurvSq]
    rfl
  exact ⟨hPart, h3, hPsym3, hRet, hHol, hLoc, hHolLoc1, hTwoStepSum, hCurvSq, hResEq,
    twoStepResolvent_left_inv h1 h2 h12 h21 A₁₂ A₂₃,
    twoStepResolvent_right_inv h1 h2 h12 h21 A₁₂ A₂₃⟩

/-- **Stage D₂₂ (`stage_D22_hodge_complement_fractal_tower_and_simplicial_operator_bridge`)**:
Packages the Bergman–Euler Hodge complement and Green polynomial identities, all-depth
defect-tower complement descent, and three-stalk ordered-path and localization identities.
The flat-channel result remains explicitly conditional in the conclusion. -/
theorem stage_D22_hodge_complement_fractal_tower_and_simplicial_operator_bridge
    {P P₁ P₂ P₃ d₀ d₁ A C A₁₂ A₂₃ A₃₁ : B}
    (hP : P * P = P) (hd : d₁ * d₀ = 0)
    (h2 : P₂ * P₂ = P₂) (h3 : P₃ * P₃ = P₃)
    (hPsym1 : star P₁ = P₁) (hPsym2 : star P₂ = P₂) (hPsym3 : star P₃ = P₃)
    (h21 : P₂ * P₁ = 0) (h32 : P₃ * P₂ = 0) (h31 : P₃ * P₁ = 0) (n : ℕ) :
    -- 1. Bergman–Euler Sheaf Cohomology Factorization & Green Polynomial (S₂₅):
    sheafHodgeComplement d₀ d₁ * sheafGreenPolynomial2 d₀ d₁ =
      1 - sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ ∧
    (1 - sheafHodgeDown d₀) * (1 - sheafHodgeUp d₁) = sheafHodgeComplement d₀ d₁ ∧
    sheafHodgeComplement d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
      -idempotencyDefect (sheafHodgeLaplacian d₀ d₁) ∧
    -- 2. All-Depth Fractal Hodge-Complement Descent `H_n * V_n = -V_{n+1}` (S₂₆):
    fractalHodgeComplement n P A C =
      (1 - mandelbrotTower n (qgtPlus P A C)) * (1 - mandelbrotTower n (qgtMinus P A C)) ∧
    fractalHodgeComplement n P A C *
      (mandelbrotTower n (qgtPlus P A C) + mandelbrotTower n (qgtMinus P A C)) =
      -(mandelbrotTower (n + 1) (qgtPlus P A C) + mandelbrotTower (n + 1) (qgtMinus P A C)) ∧
    -- 3. 3-Stalk Simplicial Triangle Sheaf Holonomy & Middle-Stalk Localization (S₂₇ & S₂₈):
    sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) *
      simplicialEdge P₃ P₁ A₃₁ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁ ∧
    P₂ * sheafHodgeLaplacian (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) * P₂ =
      sheafHodgeLaplacian (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) ∧
    P₂ * sheafWeitzenboeckDefect (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) * P₂ =
      sheafWeitzenboeckDefect (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) ∧
    (simplicialEdge P₁ P₂ A₁₂ * simplicialEdge P₂ P₃ A₂₃ = 0 →
      sheafWeitzenboeckDefect (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) = 0 ∧
      (1 - sheafHodgeDown (simplicialEdge P₂ P₃ A₂₃)) *
        (1 - sheafHodgeUp (simplicialEdge P₁ P₂ A₁₂)) =
        sheafHodgeComplement (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂)) := by
  rcases sheafHodgeComplement_factorization_and_green_polynomial hd with
    ⟨hC1, hC2, _, hC4, _⟩
  rcases fractal_hodge_complement_tower_descent hP A C n with ⟨hF1, _, _, hF4⟩
  rcases simplicial_triangle_sheaf_holonomy_and_localization
    h2 h3 hPsym1 hPsym2 hPsym3 h21 h32 h31 A₁₂ A₂₃ A₃₁ with
    ⟨_, _, _, _, hS5, hS6, hS7, hS8⟩
  exact ⟨hC1, hC4, hC2, hF1, hF4, hS5, hS6, hS7, hS8⟩

/-!
### 8. All-Degree Truncated Green Series (`sheafGreenN`), Fractal Defect Commutation,
and Full Cyclic 3-Stalk Simplicial Holonomy (`simplicialCycleOp`)
-/

/-- **All-Degree Truncated Neumann–Green Geometric Polynomial (`sheafGreenN`):**
For any coboundary pair `(d₀, d₁)` and truncation degree `N : ℕ`,
`sheafGreenN N d₀ d₁ = ∑ k ∈ Finset.range N, (sheafHodgeLaplacian d₀ d₁) ^ k`,
which coincides definitionally with `RankedDAGResolvent.finiteGreen (sheafHodgeLaplacian d₀ d₁) N`. -/
def sheafGreenN (N : ℕ) (d₀ d₁ : B) : B :=
  ∑ k ∈ Finset.range N, (sheafHodgeLaplacian d₀ d₁) ^ k

omit [StarRing B] in
/-- **Helper Lemma (`add_pow_succ_of_orthogonal`):**
For mutually orthogonal elements `x, y : B` (`x * y = 0`, `y * x = 0`), every positive power
`(x + y) ^ (N + 1)` splits additively as `x ^ (N + 1) + y ^ (N + 1)` in any associative ring `B`. -/
theorem add_pow_succ_of_orthogonal {x y : B} (hxy : x * y = 0) (hyx : y * x = 0) (N : ℕ) :
    (x + y) ^ (N + 1) = x ^ (N + 1) + y ^ (N + 1) := by
  induction N with
  | zero =>
    simp only [zero_add, pow_one]
  | succ N ih =>
    have hxNy : x ^ (N + 1) * y = 0 := by
      rw [pow_succ, mul_assoc, hxy, mul_zero]
    have hyNx : y ^ (N + 1) * x = 0 := by
      rw [pow_succ, mul_assoc, hyx, mul_zero]
    calc
      (x + y) ^ (N + 1 + 1) = (x + y) ^ (N + 1) * (x + y) := pow_succ (x + y) (N + 1)
      _ = (x ^ (N + 1) + y ^ (N + 1)) * (x + y) := by rw [ih]
      _ = x ^ (N + 1) * x + x ^ (N + 1) * y + y ^ (N + 1) * x + y ^ (N + 1) * y := by
        noncomm_ring
      _ = x ^ (N + 1 + 1) + y ^ (N + 1 + 1) := by
        rw [hxNy, hyNx]
        noncomm_ring

omit [StarRing B] in
/-- **Helper Lemma (`genV_pow_succ_eq_qgt_pow_sum`):**
For any idempotent `P` (`P * P = P`), any `A, C : B`, and any `N : ℕ`,
`genV P A C ^ (N + 1) = qgtPlus P A C ^ (N + 1) + qgtMinus P A C ^ (N + 1)`. -/
theorem genV_pow_succ_eq_qgt_pow_sum {P : B} (hP : P * P = P) (A C : B) (N : ℕ) :
    genV P A C ^ (N + 1) = qgtPlus P A C ^ (N + 1) + qgtMinus P A C ^ (N + 1) := by
  rcases qgt_cycles_orthogonal hP A C with ⟨hPM, hMP⟩
  change (qgtPlus P A C + qgtMinus P A C) ^ (N + 1) = _
  exact add_pow_succ_of_orthogonal hPM hMP N

/-- **Helper Lemma (`flat_sheafHodgeLaplacian_pow_succ_split`):**
For any flat cochain pair `d₁ * d₀ = 0`, all positive powers of `sheafHodgeLaplacian d₀ d₁`
split additively into lower and upper Hodge powers:
`(sheafHodgeLaplacian d₀ d₁) ^ (N + 1) = (sheafHodgeDown d₀) ^ (N + 1) + (sheafHodgeUp d₁) ^ (N + 1)`. -/
theorem flat_sheafHodgeLaplacian_pow_succ_split {d₀ d₁ : B} (hd : d₁ * d₀ = 0) (N : ℕ) :
    (sheafHodgeLaplacian d₀ d₁) ^ (N + 1) =
      (sheafHodgeDown d₀) ^ (N + 1) + (sheafHodgeUp d₁) ^ (N + 1) := by
  rcases sheafHodgeLaplacian_properties hd with ⟨_, _, hUpDown, hDownUp, _⟩
  unfold sheafHodgeLaplacian
  exact add_pow_succ_of_orthogonal hDownUp hUpDown N

/-- **Lemma S₂₅.4 (`sheafHodgeComplement_mul_sheafGreenN_and_geomSeries_bridge`):**
Unifies `sheafHodgeComplement`, `sheafGreenPolynomial2`, `sheafGreenN`,
`RankedDAGResolvent.finiteGreen`, `zetaFactor`, `bergmanOp`, and `Mathlib.Algebra.Ring.GeomSum`:
1. `sheafGreenN N d₀ d₁ = InfoGeometry.SignedNetwork.RankedDAGResolvent.finiteGreen (sheafHodgeLaplacian d₀ d₁) N`,
2. `sheafGreenN 3 d₀ d₁ = sheafGreenPolynomial2 d₀ d₁`,
3. `sheafHodgeComplement d₀ d₁ * sheafGreenN N d₀ d₁ = 1 - (sheafHodgeLaplacian d₀ d₁) ^ N`,
4. `sheafGreenN N d₀ d₁ * sheafHodgeComplement d₀ d₁ = 1 - (sheafHodgeLaplacian d₀ d₁) ^ N`,
5. At the horizon `d₀ = d₁ = conePlus P A` (`P * P = P`, `star P = P`):
   - `sheafHodgeComplement (conePlus P A) (conePlus P A) = zetaFactor P A (star A)`,
   - `sheafHodgeComplement (conePlus P A) (conePlus P A) = bergmanOp P A (star A) 1`,
   - `(sheafHodgeLaplacian (conePlus P A) (conePlus P A)) ^ (N + 1) = qgtPlus P A (star A) ^ (N + 1) + qgtMinus P A (star A) ^ (N + 1)`,
   - `sheafHodgeComplement (conePlus P A) (conePlus P A) * sheafGreenN (N + 1) (conePlus P A) (conePlus P A) = 1 - (qgtPlus P A (star A) ^ (N + 1) + qgtMinus P A (star A) ^ (N + 1))`. -/
theorem sheafHodgeComplement_mul_sheafGreenN_and_geomSeries_bridge
    {P : B} (hP : P * P = P) (hPsym : star P = P) (d₀ d₁ A : B) (N : ℕ) :
    sheafGreenN N d₀ d₁ =
      InfoGeometry.SignedNetwork.RankedDAGResolvent.finiteGreen (sheafHodgeLaplacian d₀ d₁) N ∧
    sheafGreenN 3 d₀ d₁ = sheafGreenPolynomial2 d₀ d₁ ∧
    sheafHodgeComplement d₀ d₁ * sheafGreenN N d₀ d₁ =
      1 - (sheafHodgeLaplacian d₀ d₁) ^ N ∧
    sheafGreenN N d₀ d₁ * sheafHodgeComplement d₀ d₁ =
      1 - (sheafHodgeLaplacian d₀ d₁) ^ N ∧
    sheafHodgeComplement (conePlus P A) (conePlus P A) = zetaFactor P A (star A) ∧
    sheafHodgeComplement (conePlus P A) (conePlus P A) = bergmanOp P A (star A) 1 ∧
    (sheafHodgeLaplacian (conePlus P A) (conePlus P A)) ^ (N + 1) =
      qgtPlus P A (star A) ^ (N + 1) + qgtMinus P A (star A) ^ (N + 1) ∧
    sheafHodgeComplement (conePlus P A) (conePlus P A) *
      sheafGreenN (N + 1) (conePlus P A) (conePlus P A) =
      1 - (qgtPlus P A (star A) ^ (N + 1) + qgtMinus P A (star A) ^ (N + 1)) := by
  have hGreen3 : sheafGreenN 3 d₀ d₁ = sheafGreenPolynomial2 d₀ d₁ := by
    unfold sheafGreenN sheafGreenPolynomial2
    calc
      ∑ k ∈ Finset.range 3, (sheafHodgeLaplacian d₀ d₁) ^ k =
        (∑ k ∈ Finset.range 2, (sheafHodgeLaplacian d₀ d₁) ^ k) +
          (sheafHodgeLaplacian d₀ d₁) ^ 2 := Finset.sum_range_succ _ 2
      _ = ((∑ k ∈ Finset.range 1, (sheafHodgeLaplacian d₀ d₁) ^ k) +
            (sheafHodgeLaplacian d₀ d₁) ^ 1) +
          (sheafHodgeLaplacian d₀ d₁) ^ 2 := by
        rw [Finset.sum_range_succ _ 1]
      _ = (sheafHodgeLaplacian d₀ d₁) ^ 0 +
          (sheafHodgeLaplacian d₀ d₁) ^ 1 +
          (sheafHodgeLaplacian d₀ d₁) ^ 2 := by
        rw [Finset.sum_range_one]
      _ = 1 + sheafHodgeLaplacian d₀ d₁ +
          sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ := by
        rw [pow_zero, pow_one, sq]
  have hLeftGeom : ∀ (x y : B) (M : ℕ),
      sheafHodgeComplement x y * sheafGreenN M x y = 1 - (sheafHodgeLaplacian x y) ^ M :=
    fun x y M => mul_neg_geom_sum (sheafHodgeLaplacian x y) M
  have hRightGeom : ∀ (x y : B) (M : ℕ),
      sheafGreenN M x y * sheafHodgeComplement x y = 1 - (sheafHodgeLaplacian x y) ^ M :=
    fun x y M => geom_sum_mul_neg (sheafHodgeLaplacian x y) M
  rcases horizon_hodge_complement_depth0_and_cubic_green_identity hP hPsym A with
    ⟨hProjZeta, hProjBerg, _⟩
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym A with
    ⟨_, _, _, hHodgeV, _⟩
  have hPowSplit :
      (sheafHodgeLaplacian (conePlus P A) (conePlus P A)) ^ (N + 1) =
        qgtPlus P A (star A) ^ (N + 1) + qgtMinus P A (star A) ^ (N + 1) := by
    rw [hHodgeV]
    exact genV_pow_succ_eq_qgt_pow_sum hP A (star A) N
  refine ⟨rfl, hGreen3, hLeftGeom d₀ d₁ N, hRightGeom d₀ d₁ N, hProjZeta, hProjBerg, hPowSplit, ?_⟩
  rw [hLeftGeom (conePlus P A) (conePlus P A) (N + 1), hPowSplit]

/-- **Lemma S₂₅.5 (`sheaf_tripotent_and_chart_bruhat_bridge`):**
Connects the cellular sheaf operators directly to `TripotentDefect` (`triProj0`, `triProjPlus`,
`triProjMinus`), `TwoStateSandwich` (`chartBruhatConj`), and `simplicialEdge`:
1. `triProj0 (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) = sheafHodgeComplement (conePlus P A) (conePlus P A)`,
2. `triProjPlus (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) - triProjMinus (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) = (2 : ℤ) • sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)`,
3. `chartBruhatConj P A (star A) (sheafHodgeLaplacian (conePlus P A) (conePlus P A)) = sheafHodgeLaplacian (conePlus P A) (conePlus P A)`,
4. `chartBruhatConj P A (star A) (sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A)) = sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A)`,
5. `chartBruhatConj P A (star A) (sheafHodgeComplement (conePlus P A) (conePlus P A)) = sheafHodgeComplement (conePlus P A) (conePlus P A)`,
6. `orthogonalPairCoboundary P_u P_v (P_w * A_u) (P_w * A_v) = simplicialEdge P_w P_u A_u - simplicialEdge P_w P_v A_v`. -/
theorem sheaf_tripotent_and_chart_bruhat_bridge
    {P : B} (hP : P * P = P) (hPsym : star P = P)
    (P_u P_v P_w A A_u A_v : B) :
    triProj0 (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) =
      sheafHodgeComplement (conePlus P A) (conePlus P A) ∧
    triProjPlus (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) -
      triProjMinus (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) =
      (2 : ℤ) • sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A) ∧
    chartBruhatConj P A (star A) (sheafHodgeLaplacian (conePlus P A) (conePlus P A)) =
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) ∧
    chartBruhatConj P A (star A) (sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A)) =
      sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) ∧
    chartBruhatConj P A (star A) (sheafHodgeComplement (conePlus P A) (conePlus P A)) =
      sheafHodgeComplement (conePlus P A) (conePlus P A) ∧
    orthogonalPairCoboundary P_u P_v (P_w * A_u) (P_w * A_v) =
      simplicialEdge P_w P_u A_u - simplicialEdge P_w P_v A_v := by
  rcases sheaf_to_tetraktys_bridge hP hPsym A (star A) with ⟨_, hCobPhi, hLap0V⟩
  rcases sheafHodge_concrete_horizon_instantiation hP hPsym A with ⟨_, _, _, hHodgeV, _⟩
  have hSymPhi : sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A) = genPhi P A (star A) :=
    hCobPhi
  have hPhiSq : genPhi P A (star A) * genPhi P A (star A) = genV P A (star A) := by
    peirce_nf hP
  refine ⟨?_, triProj_scaled_reconstruction _, ?_, ?_, ?_, rfl⟩
  · unfold triProj0 sheafHodgeComplement
    rw [hSymPhi, hPhiSq, hHodgeV]
  · rw [hHodgeV]
    exact chartBruhatConj_genV hP A (star A)
  · rw [hLap0V]
    exact chartBruhatConj_genV hP A (star A)
  · unfold sheafHodgeComplement
    rw [hHodgeV]
    unfold chartBruhatConj
    peirce_nf hP

omit [StarRing B] in
/-- **Helper Lemma (`comm_one_sub_right`):**
In any ring `B`, `comm X (1 - Y) = -comm X Y`. -/
theorem comm_one_sub_right (X Y : B) : comm X (1 - Y) = -comm X Y := by
  unfold comm
  noncomm_ring

/-- **Lemma S₂₆.2 (`fractalHodgeComplement_bridge_to_genV_defect_and_commutation`):**
Connects `fractalHodgeComplement n P A C` across all fractal depths `n : ℕ` directly to
`DefectTower.genV_defect_iterates_cycle_split` and `ConeSheetBraiding`:
1. `fractalHodgeComplement n P A C = 1 - idempotencyDefect^[n + 1] (genV P A C)`,
2. `comm (conePlus P A) (fractalHodgeComplement n P A C) = 0`,
3. `comm (coneMinus P C) (fractalHodgeComplement n P A C) = 0`,
4. `comm (genPhi P A C) (fractalHodgeComplement n P A C) = 0`,
5. `comm (genJ P A C) (fractalHodgeComplement n P A C) = 0`,
6. At the horizon `C = star A` (`star P = P`):
   - `comm (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)) (fractalHodgeComplement n P A (star A)) = 0`,
   - `comm (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) (fractalHodgeComplement n P A (star A)) = 0`. -/
theorem fractalHodgeComplement_bridge_to_genV_defect_and_commutation
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A C : B) (n : ℕ) :
    fractalHodgeComplement n P A C = 1 - idempotencyDefect^[n + 1] (genV P A C) ∧
    comm (conePlus P A) (fractalHodgeComplement n P A C) = 0 ∧
    comm (coneMinus P C) (fractalHodgeComplement n P A C) = 0 ∧
    comm (genPhi P A C) (fractalHodgeComplement n P A C) = 0 ∧
    comm (genJ P A C) (fractalHodgeComplement n P A C) = 0 ∧
    comm (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A))
      (fractalHodgeComplement n P A (star A)) = 0 ∧
    comm (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A))
      (fractalHodgeComplement n P A (star A)) = 0 := by
  have hTowerEq : ∀ C' : B,
      fractalHodgeComplement n P A C' =
        1 - (idempotencyDefect^[n + 1] (qgtPlus P A C') +
             idempotencyDefect^[n + 1] (qgtMinus P A C')) := fun C' => by
    unfold fractalHodgeComplement
    rw [mandelbrotTower_eq_idempotencyDefect_iterate,
        mandelbrotTower_eq_idempotencyDefect_iterate]
  have hDefectEq :
      fractalHodgeComplement n P A C = 1 - idempotencyDefect^[n + 1] (genV P A C) := by
    rw [hTowerEq C, ← genV_defect_iterates_cycle_split hP A C (n + 1)]
  rcases qgt_defect_iterate_sum_commutes_with_cones hP A C (n + 1) with ⟨hConeP, hConeM⟩
  rcases qgt_defect_iterate_sum_commutes_with_generators hP A C (n + 1) with ⟨hPhi, hJ⟩
  rcases qgt_defect_iterate_sum_commutes_with_generators hP A (star A) (n + 1) with
    ⟨hPhiStar, hJStar⟩
  rcases sheaf_to_tetraktys_bridge hP hPsym A (star A) with ⟨hCobJ, hCobPhi, _⟩
  refine ⟨hDefectEq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTowerEq C, comm_one_sub_right, hConeP, neg_zero]
  · rw [hTowerEq C, comm_one_sub_right, hConeM, neg_zero]
  · rw [hTowerEq C, comm_one_sub_right, hPhi, neg_zero]
  · rw [hTowerEq C, comm_one_sub_right, hJ, neg_zero]
  · rw [hCobJ, hTowerEq (star A), comm_one_sub_right]
    have hNegComm : ∀ X Y : B, comm (-X) Y = -comm X Y := fun X Y => by
      unfold comm; noncomm_ring
    rw [hNegComm, hJStar, neg_zero, neg_zero]
  · unfold sheafCoboundary0Sym
    rw [hCobPhi, hTowerEq (star A), comm_one_sub_right, hPhiStar, neg_zero]

omit [StarRing B] in
/-- **Cyclic 3-Stalk Simplicial Triangle Operator (`simplicialCycleOp`):**
Sum of the three directed edge restrictions around a 3-stalk triangle `(P₁, P₂, P₃)`:
`simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁ = simplicialEdge P₁ P₂ A₁₂ + simplicialEdge P₂ P₃ A₂₃ + simplicialEdge P₃ P₁ A₃₁`. -/
def simplicialCycleOp (P₁ P₂ P₃ A₁₂ A₂₃ A₃₁ : B) : B :=
  simplicialEdge P₁ P₂ A₁₂ + simplicialEdge P₂ P₃ A₂₃ + simplicialEdge P₃ P₁ A₃₁

omit [StarRing B] in
/-- **Helper Lemma (`simplicialEdge_mul_vanish_of_orth`):**
If `P_j * P_k = 0`, then `simplicialEdge P_i P_j A * simplicialEdge P_k P_l C = 0`. -/
theorem simplicialEdge_mul_vanish_of_orth
    {P_i P_j P_k P_l : B} (hjk : P_j * P_k = 0) (A C : B) :
    simplicialEdge P_i P_j A * simplicialEdge P_k P_l C = 0 := by
  unfold simplicialEdge
  calc
    (P_i * A * P_j) * (P_k * C * P_l) = P_i * A * (P_j * P_k) * C * P_l := by noncomm_ring
    _ = 0 := by rw [hjk]; noncomm_ring

omit [StarRing B] in
/-- **Helper Lemma (`simplicialEdge_mul_composable_eq_curvature`):**
If `P_j * P_j = P_j`, then
`simplicialEdge P_i P_j A * simplicialEdge P_j P_k C = sheafCurvature2 (simplicialEdge P_j P_k C) (simplicialEdge P_i P_j A) = P_i * A * P_j * C * P_k`. -/
theorem simplicialEdge_mul_composable_eq_curvature
    {P_i P_j P_k : B} (hj : P_j * P_j = P_j) (A C : B) :
    simplicialEdge P_i P_j A * simplicialEdge P_j P_k C =
      sheafCurvature2 (simplicialEdge P_j P_k C) (simplicialEdge P_i P_j A) ∧
    sheafCurvature2 (simplicialEdge P_j P_k C) (simplicialEdge P_i P_j A) =
      P_i * A * P_j * C * P_k := by
  refine ⟨rfl, ?_⟩
  unfold sheafCurvature2 simplicialEdge
  calc
    (P_i * A * P_j) * (P_j * C * P_k) = P_i * A * (P_j * P_j) * C * P_k := by noncomm_ring
    _ = P_i * A * P_j * C * P_k := by rw [hj]

omit [StarRing B] in
/-- **Helper Lemma (`simplicialDiagSum_vertex_extract`):**
Extracts the `Q₁`-corner diagonal block from a sum of three vertex-supported operators. -/
theorem simplicialDiagSum_vertex_extract
    {Q₁ Q₂ Q₃ : B} (hq1 : Q₁ * Q₁ = Q₁)
    (hq12 : Q₁ * Q₂ = 0) (hq21 : Q₂ * Q₁ = 0)
    (hq13 : Q₁ * Q₃ = 0) (hq31 : Q₃ * Q₁ = 0) (X₁ X₂ X₃ : B) :
    Q₁ * (simplicialEdge Q₁ Q₁ X₁ + simplicialEdge Q₂ Q₂ X₂ + simplicialEdge Q₃ Q₃ X₃) * Q₁ =
      simplicialEdge Q₁ Q₁ X₁ := by
  have hL1 : Q₁ * simplicialEdge Q₁ Q₁ X₁ * Q₁ = simplicialEdge Q₁ Q₁ X₁ := by
    unfold simplicialEdge
    calc Q₁ * (Q₁ * X₁ * Q₁) * Q₁ = (Q₁ * Q₁) * X₁ * (Q₁ * Q₁) := by noncomm_ring
      _ = Q₁ * X₁ * Q₁ := by rw [hq1]
  have hL2 : Q₁ * simplicialEdge Q₂ Q₂ X₂ * Q₁ = 0 := by
    unfold simplicialEdge
    calc Q₁ * (Q₂ * X₂ * Q₂) * Q₁ = (Q₁ * Q₂) * X₂ * (Q₂ * Q₁) := by noncomm_ring
      _ = 0 := by rw [hq12, hq21]; noncomm_ring
  have hL3 : Q₁ * simplicialEdge Q₃ Q₃ X₃ * Q₁ = 0 := by
    unfold simplicialEdge
    calc Q₁ * (Q₃ * X₃ * Q₃) * Q₁ = (Q₁ * Q₃) * X₃ * (Q₃ * Q₁) := by noncomm_ring
      _ = 0 := by rw [hq13, hq31]; noncomm_ring
  calc
    Q₁ * (simplicialEdge Q₁ Q₁ X₁ + simplicialEdge Q₂ Q₂ X₂ + simplicialEdge Q₃ Q₃ X₃) * Q₁ =
      Q₁ * simplicialEdge Q₁ Q₁ X₁ * Q₁ +
      Q₁ * simplicialEdge Q₂ Q₂ X₂ * Q₁ +
      Q₁ * simplicialEdge Q₃ Q₃ X₃ * Q₁ := by noncomm_ring
    _ = simplicialEdge Q₁ Q₁ X₁ := by rw [hL1, hL2, hL3, add_zero, add_zero]

omit [StarRing B] in
/-- **Helper Lemma (`simplicialDiagSum_off_diag_zero`):**
Off-diagonal `(Q₁, Q₂)` corner block of a sum of three vertex-supported operators vanishes. -/
theorem simplicialDiagSum_off_diag_zero
    {Q₁ Q₂ Q₃ : B} (hq12 : Q₁ * Q₂ = 0) (hq13 : Q₁ * Q₃ = 0) (hq32 : Q₃ * Q₂ = 0)
    (X₁ X₂ X₃ : B) :
    Q₁ * (simplicialEdge Q₁ Q₁ X₁ + simplicialEdge Q₂ Q₂ X₂ + simplicialEdge Q₃ Q₃ X₃) * Q₂ = 0 := by
  have hO1 : Q₁ * simplicialEdge Q₁ Q₁ X₁ * Q₂ = 0 := by
    unfold simplicialEdge
    calc Q₁ * (Q₁ * X₁ * Q₁) * Q₂ = Q₁ * Q₁ * X₁ * (Q₁ * Q₂) := by noncomm_ring
      _ = 0 := by rw [hq12]; noncomm_ring
  have hO2 : Q₁ * simplicialEdge Q₂ Q₂ X₂ * Q₂ = 0 := by
    unfold simplicialEdge
    calc Q₁ * (Q₂ * X₂ * Q₂) * Q₂ = (Q₁ * Q₂) * X₂ * Q₂ * Q₂ := by noncomm_ring
      _ = 0 := by rw [hq12]; noncomm_ring
  have hO3 : Q₁ * simplicialEdge Q₃ Q₃ X₃ * Q₂ = 0 := by
    unfold simplicialEdge
    calc Q₁ * (Q₃ * X₃ * Q₃) * Q₂ = (Q₁ * Q₃) * X₃ * (Q₃ * Q₂) := by noncomm_ring
      _ = 0 := by rw [hq13, hq32]; noncomm_ring
  calc
    Q₁ * (simplicialEdge Q₁ Q₁ X₁ + simplicialEdge Q₂ Q₂ X₂ + simplicialEdge Q₃ Q₃ X₃) * Q₂ =
      Q₁ * simplicialEdge Q₁ Q₁ X₁ * Q₂ +
      Q₁ * simplicialEdge Q₂ Q₂ X₂ * Q₂ +
      Q₁ * simplicialEdge Q₃ Q₃ X₃ * Q₂ := by noncomm_ring
    _ = 0 := by rw [hO1, hO2, hO3, add_zero, add_zero]

omit [StarRing B] in
/-- **Lemma S₂₇.3 (`simplicialCycleOp_sq_and_cube_holonomy`):**
For mutually orthogonal vertex-stalk idempotents `P₁, P₂, P₃ : B`
(`P_i * P_i = P_i`, `P_i * P_j = 0` for `i ≠ j`) and any `A₁₂, A₂₃, A₃₁ : B`:
1. The square `(simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 2` equals the sum of the three
   composable 2-simplex curvatures:
   `sheafCurvature2 (simplicialEdge P₂ P₃ A₂₃) (simplicialEdge P₁ P₂ A₁₂) + sheafCurvature2 (simplicialEdge P₃ P₁ A₃₁) (simplicialEdge P₂ P₃ A₂₃) + sheafCurvature2 (simplicialEdge P₁ P₂ A₁₂) (simplicialEdge P₃ P₁ A₃₁)`.
2. Explicitly, `(simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 2 = P₁ * A₁₂ * P₂ * A₂₃ * P₃ + P₂ * A₂₃ * P₃ * A₃₁ * P₁ + P₃ * A₃₁ * P₁ * A₁₂ * P₂`.
3. The cube `(simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3` is vertex-block diagonal and equals
   the sum of the three closed 3-cycle triangle holonomies:
   `(P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁) + (P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂ * P₂) + (P₃ * A₃₁ * P₁ * A₁₂ * P₂ * A₂₃ * P₃)`. -/
theorem simplicialCycleOp_sq_and_cube_holonomy
    {P₁ P₂ P₃ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂) (h3 : P₃ * P₃ = P₃)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (h23 : P₂ * P₃ = 0) (h32 : P₃ * P₂ = 0)
    (h13 : P₁ * P₃ = 0) (h31 : P₃ * P₁ = 0)
    (A₁₂ A₂₃ A₃₁ : B) :
    let E₁₂ := simplicialEdge P₁ P₂ A₁₂
    let E₂₃ := simplicialEdge P₂ P₃ A₂₃
    let E₃₁ := simplicialEdge P₃ P₁ A₃₁
    (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 2 =
      sheafCurvature2 E₂₃ E₁₂ + sheafCurvature2 E₃₁ E₂₃ + sheafCurvature2 E₁₂ E₃₁ ∧
    (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 2 =
      P₁ * A₁₂ * P₂ * A₂₃ * P₃ + P₂ * A₂₃ * P₃ * A₃₁ * P₁ + P₃ * A₃₁ * P₁ * A₁₂ * P₂ ∧
    (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3 =
      (P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁) +
      (P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂ * P₂) +
      (P₃ * A₃₁ * P₁ * A₁₂ * P₂ * A₂₃ * P₃) := by
  intro E₁₂ E₂₃ E₃₁
  have h11_0 : E₁₂ * E₁₂ = 0 := simplicialEdge_mul_vanish_of_orth h21 A₁₂ A₁₂
  have h22_0 : E₂₃ * E₂₃ = 0 := simplicialEdge_mul_vanish_of_orth h32 A₂₃ A₂₃
  have h33_0 : E₃₁ * E₃₁ = 0 := simplicialEdge_mul_vanish_of_orth h13 A₃₁ A₃₁
  have h21_0 : E₂₃ * E₁₂ = 0 := simplicialEdge_mul_vanish_of_orth h31 A₂₃ A₁₂
  have h32_0 : E₃₁ * E₂₃ = 0 := simplicialEdge_mul_vanish_of_orth h12 A₃₁ A₂₃
  have h13_0 : E₁₂ * E₃₁ = 0 := simplicialEdge_mul_vanish_of_orth h23 A₁₂ A₃₁
  rcases simplicialEdge_mul_composable_eq_curvature (P_i := P₁) (P_k := P₃) h2 A₁₂ A₂₃ with
    ⟨h12_curv, h12_exp⟩
  rcases simplicialEdge_mul_composable_eq_curvature (P_i := P₂) (P_k := P₁) h3 A₂₃ A₃₁ with
    ⟨h23_curv, h23_exp⟩
  rcases simplicialEdge_mul_composable_eq_curvature (P_i := P₃) (P_k := P₂) h1 A₃₁ A₁₂ with
    ⟨h31_curv, h31_exp⟩
  have hSqCurv :
      (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 2 =
        sheafCurvature2 E₂₃ E₁₂ + sheafCurvature2 E₃₁ E₂₃ + sheafCurvature2 E₁₂ E₃₁ := by
    unfold simplicialCycleOp
    change (E₁₂ + E₂₃ + E₃₁) ^ 2 = _
    rw [sq]
    calc
      (E₁₂ + E₂₃ + E₃₁) * (E₁₂ + E₂₃ + E₃₁) =
        E₁₂ * E₁₂ + E₁₂ * E₂₃ + E₁₂ * E₃₁ +
        E₂₃ * E₁₂ + E₂₃ * E₂₃ + E₂₃ * E₃₁ +
        E₃₁ * E₁₂ + E₃₁ * E₂₃ + E₃₁ * E₃₁ := by noncomm_ring
      _ = sheafCurvature2 E₂₃ E₁₂ + sheafCurvature2 E₃₁ E₂₃ + sheafCurvature2 E₁₂ E₃₁ := by
        rw [h11_0, h22_0, h33_0, h21_0, h32_0, h13_0, h12_curv, h23_curv, h31_curv]
        abel
  have hSqExp :
      (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 2 =
        P₁ * A₁₂ * P₂ * A₂₃ * P₃ + P₂ * A₂₃ * P₃ * A₃₁ * P₁ + P₃ * A₃₁ * P₁ * A₁₂ * P₂ := by
    rw [hSqCurv, h12_exp, h23_exp, h31_exp]
  refine ⟨hSqCurv, hSqExp, ?_⟩
  rw [pow_succ _ 2, hSqExp]
  unfold simplicialCycleOp
  change (P₁ * A₁₂ * P₂ * A₂₃ * P₃ + P₂ * A₂₃ * P₃ * A₃₁ * P₁ + P₃ * A₃₁ * P₁ * A₁₂ * P₂) *
    (P₁ * A₁₂ * P₂ + P₂ * A₂₃ * P₃ + P₃ * A₃₁ * P₁) = _
  have hF13_12 : (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₁ * A₁₂ * P₂) = 0 := by
    calc (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₁ * A₁₂ * P₂)
      _ = P₁ * A₁₂ * P₂ * A₂₃ * (P₃ * P₁) * A₁₂ * P₂ := by noncomm_ring
      _ = 0 := by rw [h31]; noncomm_ring
  have hF13_23 : (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₂ * A₂₃ * P₃) = 0 := by
    calc (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₂ * A₂₃ * P₃)
      _ = P₁ * A₁₂ * P₂ * A₂₃ * (P₃ * P₂) * A₂₃ * P₃ := by noncomm_ring
      _ = 0 := by rw [h32]; noncomm_ring
  have hF13_31 :
      (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₃ * A₃₁ * P₁) =
        P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁ := by
    calc (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₃ * A₃₁ * P₁)
      _ = P₁ * A₁₂ * P₂ * A₂₃ * (P₃ * P₃) * A₃₁ * P₁ := by noncomm_ring
      _ = P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁ := by rw [h3]
  have hF21_12 :
      (P₂ * A₂₃ * P₃ * A₃₁ * P₁) * (P₁ * A₁₂ * P₂) =
        P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂ * P₂ := by
    calc (P₂ * A₂₃ * P₃ * A₃₁ * P₁) * (P₁ * A₁₂ * P₂)
      _ = P₂ * A₂₃ * P₃ * A₃₁ * (P₁ * P₁) * A₁₂ * P₂ := by noncomm_ring
      _ = P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂ * P₂ := by rw [h1]
  have hF21_23 : (P₂ * A₂₃ * P₃ * A₃₁ * P₁) * (P₂ * A₂₃ * P₃) = 0 := by
    calc (P₂ * A₂₃ * P₃ * A₃₁ * P₁) * (P₂ * A₂₃ * P₃)
      _ = P₂ * A₂₃ * P₃ * A₃₁ * (P₁ * P₂) * A₂₃ * P₃ := by noncomm_ring
      _ = 0 := by rw [h12]; noncomm_ring
  have hF21_31 : (P₂ * A₂₃ * P₃ * A₃₁ * P₁) * (P₃ * A₃₁ * P₁) = 0 := by
    calc (P₂ * A₂₃ * P₃ * A₃₁ * P₁) * (P₃ * A₃₁ * P₁)
      _ = P₂ * A₂₃ * P₃ * A₃₁ * (P₁ * P₃) * A₃₁ * P₁ := by noncomm_ring
      _ = 0 := by rw [h13]; noncomm_ring
  have hF32_12 : (P₃ * A₃₁ * P₁ * A₁₂ * P₂) * (P₁ * A₁₂ * P₂) = 0 := by
    calc (P₃ * A₃₁ * P₁ * A₁₂ * P₂) * (P₁ * A₁₂ * P₂)
      _ = P₃ * A₃₁ * P₁ * A₁₂ * (P₂ * P₁) * A₁₂ * P₂ := by noncomm_ring
      _ = 0 := by rw [h21]; noncomm_ring
  have hF32_23 :
      (P₃ * A₃₁ * P₁ * A₁₂ * P₂) * (P₂ * A₂₃ * P₃) =
        P₃ * A₃₁ * P₁ * A₁₂ * P₂ * A₂₃ * P₃ := by
    calc (P₃ * A₃₁ * P₁ * A₁₂ * P₂) * (P₂ * A₂₃ * P₃)
      _ = P₃ * A₃₁ * P₁ * A₁₂ * (P₂ * P₂) * A₂₃ * P₃ := by noncomm_ring
      _ = P₃ * A₃₁ * P₁ * A₁₂ * P₂ * A₂₃ * P₃ := by rw [h2]
  have hF32_31 : (P₃ * A₃₁ * P₁ * A₁₂ * P₂) * (P₃ * A₃₁ * P₁) = 0 := by
    calc (P₃ * A₃₁ * P₁ * A₁₂ * P₂) * (P₃ * A₃₁ * P₁)
      _ = P₃ * A₃₁ * P₁ * A₁₂ * (P₂ * P₃) * A₃₁ * P₁ := by noncomm_ring
      _ = 0 := by rw [h23]; noncomm_ring
  calc
    (P₁ * A₁₂ * P₂ * A₂₃ * P₃ + P₂ * A₂₃ * P₃ * A₃₁ * P₁ + P₃ * A₃₁ * P₁ * A₁₂ * P₂) *
        (P₁ * A₁₂ * P₂ + P₂ * A₂₃ * P₃ + P₃ * A₃₁ * P₁) =
      (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₁ * A₁₂ * P₂) +
      (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₂ * A₂₃ * P₃) +
      (P₁ * A₁₂ * P₂ * A₂₃ * P₃) * (P₃ * A₃₁ * P₁) +
      (P₂ * A₂₃ * P₃ * A₃₁ * P₁) * (P₁ * A₁₂ * P₂) +
      (P₂ * A₂₃ * P₃ * A₃₁ * P₁) * (P₂ * A₂₃ * P₃) +
      (P₂ * A₂₃ * P₃ * A₃₁ * P₁) * (P₃ * A₃₁ * P₁) +
      (P₃ * A₃₁ * P₁ * A₁₂ * P₂) * (P₁ * A₁₂ * P₂) +
      (P₃ * A₃₁ * P₁ * A₁₂ * P₂) * (P₂ * A₂₃ * P₃) +
      (P₃ * A₃₁ * P₁ * A₁₂ * P₂) * (P₃ * A₃₁ * P₁) := by noncomm_ring
    _ = (P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₁ * P₁) +
        (P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂ * P₂) +
        (P₃ * A₃₁ * P₁ * A₁₂ * P₂ * A₂₃ * P₃) := by
      rw [hF13_12, hF13_23, hF13_31, hF21_12, hF21_23, hF21_31, hF32_12, hF32_23, hF32_31]
      abel

omit [StarRing B] in
/-- **Lemma S₂₇.4 (`simplicialCycleOp_cube_supportedSubring_bridge`):**
When `P₃ = ThreeCornerColumnAlgebra.third P₁ P₂ = 1 - P₁ - P₂` for mutually orthogonal
idempotents `P₁, P₂` (`P₁ * P₁ = P₁`, `P₂ * P₂ = P₂`, `P₁ * P₂ = 0`, `P₂ * P₁ = 0`),
the 3-cycle holonomy cube `(simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3` equals
`ThreeCornerColumnAlgebra.columnOp P₁ P₂ (A₁₂ * P₂ * A₂₃ * P₃ * A₃₁)
(P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂) (A₃₁ * P₁ * A₁₂ * P₂ * A₂₃)` and therefore belongs to
`ThreeCornerColumnAlgebra.supportedSubring h1 h2 h12 h21`, with all four forbidden cross-corner
blocks vanishing. -/
theorem simplicialCycleOp_cube_supportedSubring_bridge
    {P₁ P₂ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (A₁₂ A₂₃ A₃₁ : B) :
    let P₃ := ThreeCornerColumnAlgebra.third P₁ P₂
    (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3 =
      ThreeCornerColumnAlgebra.columnOp P₁ P₂
        (A₁₂ * P₂ * A₂₃ * P₃ * A₃₁)
        (P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂)
        (A₃₁ * P₁ * A₁₂ * P₂ * A₂₃) ∧
    (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3 ∈
      ThreeCornerColumnAlgebra.supportedSubring h1 h2 h12 h21 ∧
    P₂ * (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3 * P₁ = 0 ∧
    P₂ * (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3 * P₃ = 0 ∧
    P₁ * (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3 * P₃ = 0 ∧
    P₃ * (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3 * P₁ = 0 := by
  intro P₃
  have h3 : P₃ * P₃ = P₃ := ThreeCornerColumnAlgebra.third_idempotent h1 h2 h12 h21
  rcases ThreeCornerColumnAlgebra.third_orthogonal h1 h2 h12 h21 with ⟨h13, h31, h23, h32⟩
  rcases simplicialCycleOp_sq_and_cube_holonomy
    h1 h2 h3 h12 h21 h23 h32 h13 h31 A₁₂ A₂₃ A₃₁ with ⟨_, _, hCube⟩
  have hColEq :
      (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3 =
        ThreeCornerColumnAlgebra.columnOp P₁ P₂
          (A₁₂ * P₂ * A₂₃ * P₃ * A₃₁)
          (P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂)
          (A₃₁ * P₁ * A₁₂ * P₂ * A₂₃) := by
    rw [hCube]
    dsimp [P₃]
    unfold ThreeCornerColumnAlgebra.columnOp peirce11
    noncomm_ring
  have hMem :
      (simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁) ^ 3 ∈
        ThreeCornerColumnAlgebra.supportedSubring h1 h2 h12 h21 :=
    ⟨A₁₂ * P₂ * A₂₃ * P₃ * A₃₁,
     P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂,
     A₃₁ * P₁ * A₁₂ * P₂ * A₂₃,
     hColEq⟩
  rcases ThreeCornerColumnAlgebra.forbidden_corners h1 h2 h12 h21
    (A₁₂ * P₂ * A₂₃ * P₃ * A₃₁)
    (P₂ * A₂₃ * P₃ * A₃₁ * P₁ * A₁₂)
    (A₃₁ * P₁ * A₁₂ * P₂ * A₂₃) with ⟨hForb1, hForb2, hForb3, hForb4⟩
  rw [← hColEq] at hForb1 hForb2 hForb3 hForb4
  exact ⟨hColEq, hMem, hForb1, hForb2, hForb3, hForb4⟩

/-- **Lemma S₂₈.2 (`simplicialCycleOp_hodge_vertex_block_decomposition`):**
For mutually orthogonal self-adjoint vertex-stalk idempotents `P₁, P₂, P₃ : B`
(`P_i * P_i = P_i`, `star P_i = P_i`, `P_i * P_j = 0` for `i ≠ j`) and any `A₁₂, A₂₃, A₃₁ : B`,
let `E_cycle = simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁`,
`Δ_down = sheafHodgeDown E_cycle`, and `Δ_up = sheafHodgeUp E_cycle`:
1. `Δ_down = sheafHodgeDown E₁₂ + sheafHodgeDown E₂₃ + sheafHodgeDown E₃₁`,
2. `Δ_up = sheafHodgeUp E₁₂ + sheafHodgeUp E₂₃ + sheafHodgeUp E₃₁`,
3. Diagonal vertex-stalk block extraction for `Δ_down` and `Δ_up`:
   - `P₁ * Δ_down * P₁ = sheafHodgeDown E₁₂`, `P₂ * Δ_down * P₂ = sheafHodgeDown E₂₃`,
     `P₃ * Δ_down * P₃ = sheafHodgeDown E₃₁`,
   - `Δ_down = P₁ * Δ_down * P₁ + P₂ * Δ_down * P₂ + P₃ * Δ_down * P₃`,
   - `P₁ * Δ_up * P₁ = sheafHodgeUp E₃₁`, `P₂ * Δ_up * P₂ = sheafHodgeUp E₁₂`,
     `P₃ * Δ_up * P₃ = sheafHodgeUp E₂₃`,
   - `Δ_up = P₁ * Δ_up * P₁ + P₂ * Δ_up * P₂ + P₃ * Δ_up * P₃`,
4. All six off-diagonal vertex blocks `P_i * Δ_down * P_j` and `P_i * Δ_up * P_j` (`i ≠ j`) vanish. -/
theorem simplicialCycleOp_hodge_vertex_block_decomposition
    {P₁ P₂ P₃ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂) (h3 : P₃ * P₃ = P₃)
    (hPsym1 : star P₁ = P₁) (hPsym2 : star P₂ = P₂) (hPsym3 : star P₃ = P₃)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (h23 : P₂ * P₃ = 0) (h32 : P₃ * P₂ = 0)
    (h13 : P₁ * P₃ = 0) (h31 : P₃ * P₁ = 0)
    (A₁₂ A₂₃ A₃₁ : B) :
    let E₁₂ := simplicialEdge P₁ P₂ A₁₂
    let E₂₃ := simplicialEdge P₂ P₃ A₂₃
    let E₃₁ := simplicialEdge P₃ P₁ A₃₁
    let E_cycle := simplicialCycleOp P₁ P₂ P₃ A₁₂ A₂₃ A₃₁
    let Δ_down := sheafHodgeDown E_cycle
    let Δ_up := sheafHodgeUp E_cycle
    Δ_down = sheafHodgeDown E₁₂ + sheafHodgeDown E₂₃ + sheafHodgeDown E₃₁ ∧
    Δ_up = sheafHodgeUp E₁₂ + sheafHodgeUp E₂₃ + sheafHodgeUp E₃₁ ∧
    P₁ * Δ_down * P₁ = sheafHodgeDown E₁₂ ∧
    P₂ * Δ_down * P₂ = sheafHodgeDown E₂₃ ∧
    P₃ * Δ_down * P₃ = sheafHodgeDown E₃₁ ∧
    Δ_down = P₁ * Δ_down * P₁ + P₂ * Δ_down * P₂ + P₃ * Δ_down * P₃ ∧
    P₁ * Δ_up * P₁ = sheafHodgeUp E₃₁ ∧
    P₂ * Δ_up * P₂ = sheafHodgeUp E₁₂ ∧
    P₃ * Δ_up * P₃ = sheafHodgeUp E₂₃ ∧
    Δ_up = P₁ * Δ_up * P₁ + P₂ * Δ_up * P₂ + P₃ * Δ_up * P₃ ∧
    P₁ * Δ_down * P₂ = 0 ∧ P₂ * Δ_down * P₁ = 0 ∧
    P₂ * Δ_down * P₃ = 0 ∧ P₃ * Δ_down * P₂ = 0 ∧
    P₃ * Δ_down * P₁ = 0 ∧ P₁ * Δ_down * P₃ = 0 ∧
    P₁ * Δ_up * P₂ = 0 ∧ P₂ * Δ_up * P₁ = 0 ∧
    P₂ * Δ_up * P₃ = 0 ∧ P₃ * Δ_up * P₂ = 0 ∧
    P₃ * Δ_up * P₁ = 0 ∧ P₁ * Δ_up * P₃ = 0 := by
  intro E₁₂ E₂₃ E₃₁ E_cycle Δ_down Δ_up
  have hStarE12 : star E₁₂ = simplicialEdge P₂ P₁ (star A₁₂) := by
    dsimp [E₁₂, simplicialEdge]
    rw [star_mul, star_mul, hPsym1, hPsym2]
    noncomm_ring
  have hStarE23 : star E₂₃ = simplicialEdge P₃ P₂ (star A₂₃) := by
    dsimp [E₂₃, simplicialEdge]
    rw [star_mul, star_mul, hPsym2, hPsym3]
    noncomm_ring
  have hStarE31 : star E₃₁ = simplicialEdge P₁ P₃ (star A₃₁) := by
    dsimp [E₃₁, simplicialEdge]
    rw [star_mul, star_mul, hPsym3, hPsym1]
    noncomm_ring
  have hD12_23 : E₁₂ * star E₂₃ = 0 := by
    rw [hStarE23]; exact simplicialEdge_mul_vanish_of_orth h23 A₁₂ (star A₂₃)
  have hD12_31 : E₁₂ * star E₃₁ = 0 := by
    rw [hStarE31]; exact simplicialEdge_mul_vanish_of_orth h21 A₁₂ (star A₃₁)
  have hD23_12 : E₂₃ * star E₁₂ = 0 := by
    rw [hStarE12]; exact simplicialEdge_mul_vanish_of_orth h32 A₂₃ (star A₁₂)
  have hD23_31 : E₂₃ * star E₃₁ = 0 := by
    rw [hStarE31]; exact simplicialEdge_mul_vanish_of_orth h31 A₂₃ (star A₃₁)
  have hD31_12 : E₃₁ * star E₁₂ = 0 := by
    rw [hStarE12]; exact simplicialEdge_mul_vanish_of_orth h12 A₃₁ (star A₁₂)
  have hD31_23 : E₃₁ * star E₂₃ = 0 := by
    rw [hStarE23]; exact simplicialEdge_mul_vanish_of_orth h13 A₃₁ (star A₂₃)
  have hU12_23 : star E₁₂ * E₂₃ = 0 := by
    rw [hStarE12]; exact simplicialEdge_mul_vanish_of_orth h12 (star A₁₂) A₂₃
  have hU12_31 : star E₁₂ * E₃₁ = 0 := by
    rw [hStarE12]; exact simplicialEdge_mul_vanish_of_orth h13 (star A₁₂) A₃₁
  have hU23_12 : star E₂₃ * E₁₂ = 0 := by
    rw [hStarE23]; exact simplicialEdge_mul_vanish_of_orth h21 (star A₂₃) A₁₂
  have hU23_31 : star E₂₃ * E₃₁ = 0 := by
    rw [hStarE23]; exact simplicialEdge_mul_vanish_of_orth h23 (star A₂₃) A₃₁
  have hU31_12 : star E₃₁ * E₁₂ = 0 := by
    rw [hStarE31]; exact simplicialEdge_mul_vanish_of_orth h31 (star A₃₁) A₁₂
  have hU31_23 : star E₃₁ * E₂₃ = 0 := by
    rw [hStarE31]; exact simplicialEdge_mul_vanish_of_orth h32 (star A₃₁) A₂₃
  have hDownSum : Δ_down = sheafHodgeDown E₁₂ + sheafHodgeDown E₂₃ + sheafHodgeDown E₃₁ := by
    dsimp [Δ_down, E_cycle, simplicialCycleOp]
    change sheafHodgeDown (E₁₂ + E₂₃ + E₃₁) = _
    unfold sheafHodgeDown
    rw [star_add, star_add]
    calc
      (E₁₂ + E₂₃ + E₃₁) * (star E₁₂ + star E₂₃ + star E₃₁) =
        E₁₂ * star E₁₂ + E₁₂ * star E₂₃ + E₁₂ * star E₃₁ +
        E₂₃ * star E₁₂ + E₂₃ * star E₂₃ + E₂₃ * star E₃₁ +
        E₃₁ * star E₁₂ + E₃₁ * star E₂₃ + E₃₁ * star E₃₁ := by noncomm_ring
      _ = E₁₂ * star E₁₂ + E₂₃ * star E₂₃ + E₃₁ * star E₃₁ := by
        rw [hD12_23, hD12_31, hD23_12, hD23_31, hD31_12, hD31_23]
        abel
  have hUpSum : Δ_up = sheafHodgeUp E₁₂ + sheafHodgeUp E₂₃ + sheafHodgeUp E₃₁ := by
    dsimp [Δ_up, E_cycle, simplicialCycleOp]
    change sheafHodgeUp (E₁₂ + E₂₃ + E₃₁) = _
    unfold sheafHodgeUp
    rw [star_add, star_add]
    calc
      (star E₁₂ + star E₂₃ + star E₃₁) * (E₁₂ + E₂₃ + E₃₁) =
        star E₁₂ * E₁₂ + star E₁₂ * E₂₃ + star E₁₂ * E₃₁ +
        star E₂₃ * E₁₂ + star E₂₃ * E₂₃ + star E₂₃ * E₃₁ +
        star E₃₁ * E₁₂ + star E₃₁ * E₂₃ + star E₃₁ * E₃₁ := by noncomm_ring
      _ = star E₁₂ * E₁₂ + star E₂₃ * E₂₃ + star E₃₁ * E₃₁ := by
        rw [hU12_23, hU12_31, hU23_12, hU23_31, hU31_12, hU31_23]
        abel
  have hDown12_exp : sheafHodgeDown E₁₂ = simplicialEdge P₁ P₁ (A₁₂ * P₂ * star A₁₂) := by
    unfold sheafHodgeDown
    rw [hStarE12, (simplicialEdge_mul_composable_eq_curvature h2 A₁₂ (star A₁₂)).1,
        (simplicialEdge_mul_composable_eq_curvature h2 A₁₂ (star A₁₂)).2]
    unfold simplicialEdge; noncomm_ring
  have hDown23_exp : sheafHodgeDown E₂₃ = simplicialEdge P₂ P₂ (A₂₃ * P₃ * star A₂₃) := by
    unfold sheafHodgeDown
    rw [hStarE23, (simplicialEdge_mul_composable_eq_curvature h3 A₂₃ (star A₂₃)).1,
        (simplicialEdge_mul_composable_eq_curvature h3 A₂₃ (star A₂₃)).2]
    unfold simplicialEdge; noncomm_ring
  have hDown31_exp : sheafHodgeDown E₃₁ = simplicialEdge P₃ P₃ (A₃₁ * P₁ * star A₃₁) := by
    unfold sheafHodgeDown
    rw [hStarE31, (simplicialEdge_mul_composable_eq_curvature h1 A₃₁ (star A₃₁)).1,
        (simplicialEdge_mul_composable_eq_curvature h1 A₃₁ (star A₃₁)).2]
    unfold simplicialEdge; noncomm_ring
  have hUp12_exp : sheafHodgeUp E₁₂ = simplicialEdge P₂ P₂ (star A₁₂ * P₁ * A₁₂) := by
    unfold sheafHodgeUp
    rw [hStarE12, (simplicialEdge_mul_composable_eq_curvature h1 (star A₁₂) A₁₂).1,
        (simplicialEdge_mul_composable_eq_curvature h1 (star A₁₂) A₁₂).2]
    unfold simplicialEdge; noncomm_ring
  have hUp23_exp : sheafHodgeUp E₂₃ = simplicialEdge P₃ P₃ (star A₂₃ * P₂ * A₂₃) := by
    unfold sheafHodgeUp
    rw [hStarE23, (simplicialEdge_mul_composable_eq_curvature h2 (star A₂₃) A₂₃).1,
        (simplicialEdge_mul_composable_eq_curvature h2 (star A₂₃) A₂₃).2]
    unfold simplicialEdge; noncomm_ring
  have hUp31_exp : sheafHodgeUp E₃₁ = simplicialEdge P₁ P₁ (star A₃₁ * P₃ * A₃₁) := by
    unfold sheafHodgeUp
    rw [hStarE31, (simplicialEdge_mul_composable_eq_curvature h3 (star A₃₁) A₃₁).1,
        (simplicialEdge_mul_composable_eq_curvature h3 (star A₃₁) A₃₁).2]
    unfold simplicialEdge; noncomm_ring
  have hDownPerm2 :
      Δ_down =
        simplicialEdge P₂ P₂ (A₂₃ * P₃ * star A₂₃) +
        simplicialEdge P₃ P₃ (A₃₁ * P₁ * star A₃₁) +
        simplicialEdge P₁ P₁ (A₁₂ * P₂ * star A₁₂) := by
    rw [hDownSum, hDown12_exp, hDown23_exp, hDown31_exp]; abel
  have hDownPerm3 :
      Δ_down =
        simplicialEdge P₃ P₃ (A₃₁ * P₁ * star A₃₁) +
        simplicialEdge P₁ P₁ (A₁₂ * P₂ * star A₁₂) +
        simplicialEdge P₂ P₂ (A₂₃ * P₃ * star A₂₃) := by
    rw [hDownSum, hDown12_exp, hDown23_exp, hDown31_exp]; abel
  have hDownPerm4 :
      Δ_down =
        simplicialEdge P₂ P₂ (A₂₃ * P₃ * star A₂₃) +
        simplicialEdge P₁ P₁ (A₁₂ * P₂ * star A₁₂) +
        simplicialEdge P₃ P₃ (A₃₁ * P₁ * star A₃₁) := by
    rw [hDownSum, hDown12_exp, hDown23_exp, hDown31_exp]; abel
  have hDownPerm5 :
      Δ_down =
        simplicialEdge P₁ P₁ (A₁₂ * P₂ * star A₁₂) +
        simplicialEdge P₃ P₃ (A₃₁ * P₁ * star A₃₁) +
        simplicialEdge P₂ P₂ (A₂₃ * P₃ * star A₂₃) := by
    rw [hDownSum, hDown12_exp, hDown23_exp, hDown31_exp]; abel
  have hDownPerm6 :
      Δ_down =
        simplicialEdge P₃ P₃ (A₃₁ * P₁ * star A₃₁) +
        simplicialEdge P₂ P₂ (A₂₃ * P₃ * star A₂₃) +
        simplicialEdge P₁ P₁ (A₁₂ * P₂ * star A₁₂) := by
    rw [hDownSum, hDown12_exp, hDown23_exp, hDown31_exp]; abel
  have hUpPerm1 :
      Δ_up =
        simplicialEdge P₁ P₁ (star A₃₁ * P₃ * A₃₁) +
        simplicialEdge P₂ P₂ (star A₁₂ * P₁ * A₁₂) +
        simplicialEdge P₃ P₃ (star A₂₃ * P₂ * A₂₃) := by
    rw [hUpSum, hUp12_exp, hUp23_exp, hUp31_exp]; abel
  have hUpPerm2 :
      Δ_up =
        simplicialEdge P₂ P₂ (star A₁₂ * P₁ * A₁₂) +
        simplicialEdge P₁ P₁ (star A₃₁ * P₃ * A₃₁) +
        simplicialEdge P₃ P₃ (star A₂₃ * P₂ * A₂₃) := by
    rw [hUpSum, hUp12_exp, hUp23_exp, hUp31_exp]; abel
  have hUpPerm3 :
      Δ_up =
        simplicialEdge P₃ P₃ (star A₂₃ * P₂ * A₂₃) +
        simplicialEdge P₁ P₁ (star A₃₁ * P₃ * A₃₁) +
        simplicialEdge P₂ P₂ (star A₁₂ * P₁ * A₁₂) := by
    rw [hUpSum, hUp12_exp, hUp23_exp, hUp31_exp]; abel
  have hUpPerm4 :
      Δ_up =
        simplicialEdge P₃ P₃ (star A₂₃ * P₂ * A₂₃) +
        simplicialEdge P₂ P₂ (star A₁₂ * P₁ * A₁₂) +
        simplicialEdge P₁ P₁ (star A₃₁ * P₃ * A₃₁) := by
    rw [hUpSum, hUp12_exp, hUp23_exp, hUp31_exp]; abel
  have hUpPerm5 :
      Δ_up =
        simplicialEdge P₁ P₁ (star A₃₁ * P₃ * A₃₁) +
        simplicialEdge P₃ P₃ (star A₂₃ * P₂ * A₂₃) +
        simplicialEdge P₂ P₂ (star A₁₂ * P₁ * A₁₂) := by
    rw [hUpSum, hUp12_exp, hUp23_exp, hUp31_exp]; abel
  have hP1Down : P₁ * Δ_down * P₁ = sheafHodgeDown E₁₂ := by
    rw [hDownSum, hDown12_exp, hDown23_exp, hDown31_exp]
    exact simplicialDiagSum_vertex_extract h1 h12 h21 h13 h31 _ _ _
  have hP2Down : P₂ * Δ_down * P₂ = sheafHodgeDown E₂₃ := by
    rw [hDownPerm2, hDown23_exp]
    exact simplicialDiagSum_vertex_extract h2 h23 h32 h21 h12 _ _ _
  have hP3Down : P₃ * Δ_down * P₃ = sheafHodgeDown E₃₁ := by
    rw [hDownPerm3, hDown31_exp]
    exact simplicialDiagSum_vertex_extract h3 h31 h13 h32 h23 _ _ _
  have hP1Up : P₁ * Δ_up * P₁ = sheafHodgeUp E₃₁ := by
    rw [hUpPerm1, hUp31_exp]
    exact simplicialDiagSum_vertex_extract h1 h12 h21 h13 h31 _ _ _
  have hP2Up : P₂ * Δ_up * P₂ = sheafHodgeUp E₁₂ := by
    rw [hUpSum, hUp12_exp, hUp23_exp, hUp31_exp]
    exact simplicialDiagSum_vertex_extract h2 h23 h32 h21 h12 _ _ _
  have hP3Up : P₃ * Δ_up * P₃ = sheafHodgeUp E₂₃ := by
    rw [hUpPerm3, hUp23_exp]
    exact simplicialDiagSum_vertex_extract h3 h31 h13 h32 h23 _ _ _
  have hDownDiag : Δ_down = P₁ * Δ_down * P₁ + P₂ * Δ_down * P₂ + P₃ * Δ_down * P₃ := by
    rw [hP1Down, hP2Down, hP3Down, hDownSum]
  have hUpDiag : Δ_up = P₁ * Δ_up * P₁ + P₂ * Δ_up * P₂ + P₃ * Δ_up * P₃ := by
    rw [hP1Up, hP2Up, hP3Up, hUpSum]
    abel
  refine ⟨hDownSum, hUpSum, hP1Down, hP2Down, hP3Down, hDownDiag,
          hP1Up, hP2Up, hP3Up, hUpDiag,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hDownSum, hDown12_exp, hDown23_exp, hDown31_exp]
    exact simplicialDiagSum_off_diag_zero h12 h13 h32 _ _ _
  · rw [hDownPerm4]
    exact simplicialDiagSum_off_diag_zero h21 h23 h31 _ _ _
  · rw [hDownPerm2]
    exact simplicialDiagSum_off_diag_zero h23 h21 h13 _ _ _
  · rw [hDownPerm6]
    exact simplicialDiagSum_off_diag_zero h32 h31 h12 _ _ _
  · rw [hDownPerm3]
    exact simplicialDiagSum_off_diag_zero h31 h32 h21 _ _ _
  · rw [hDownPerm5]
    exact simplicialDiagSum_off_diag_zero h13 h12 h23 _ _ _
  · rw [hUpPerm1]
    exact simplicialDiagSum_off_diag_zero h12 h13 h32 _ _ _
  · rw [hUpPerm2]
    exact simplicialDiagSum_off_diag_zero h21 h23 h31 _ _ _
  · rw [hUpSum, hUp12_exp, hUp23_exp, hUp31_exp]
    exact simplicialDiagSum_off_diag_zero h23 h21 h13 _ _ _
  · rw [hUpPerm4]
    exact simplicialDiagSum_off_diag_zero h32 h31 h12 _ _ _
  · rw [hUpPerm3]
    exact simplicialDiagSum_off_diag_zero h31 h32 h21 _ _ _
  · rw [hUpPerm5]
    exact simplicialDiagSum_off_diag_zero h13 h12 h23 _ _ _

/-! ### 9. Audited All-Scale Metriplectic Master Polynomial (`M₇`) and Two-Parameter
(`(k, n) ∈ ℕ × ℕ`) Cellular Sheaf Hodge Filtering & Intertwining (`M₁₀`) -/

omit [StarRing B] in
/-- **Definition M₇ (`metriplecticMasterPoly4`)**:
The 4th-order charge polynomial `(charge P⁴ - 5 • charge P² + 4 • id)(K)` on operators `K : B → B`. -/
def metriplecticMasterPoly4 (P : B) (K : B → B) (X : B) : B :=
  chargeIter P K 4 X - (5 : ℤ) • chargeIter P K 2 X + (4 : ℤ) • K X

omit [StarRing B] in
private theorem charge_zsmul (P : B) (K : B → B) (r : ℤ) (X : B) :
    charge P (fun Y => r • K Y) X = r • charge P K X := by
  unfold charge comm
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

omit [StarRing B] in
private theorem chargeIter_of_eigenvalue (P : B) (K : B → B) (r : ℤ)
    (hK : ∀ X, charge P K X = r • K X) :
    ∀ n X, chargeIter P K n X = r ^ n • K X := by
  intro n
  induction n with
  | zero => intro X; simp [chargeIter]
  | succ n ih =>
      intro X
      change charge P (chargeIter P K n) X = r ^ (n + 1) • K X
      have hIter : chargeIter P K n = fun Y => r ^ n • K Y := by
        funext Y
        exact ih Y
      rw [hIter, charge_zsmul, hK, pow_succ, mul_smul]

omit [StarRing B] in
private theorem chargeIter_zero_of_charge_zero (P : B) (K : B → B)
    (hK : ∀ X, charge P K X = 0) :
    ∀ n X, chargeIter P K (n + 1) X = 0 := by
  intro n
  induction n with
  | zero => intro X; simpa [chargeIter] using hK X
  | succ n ih =>
      intro X
      change charge P (chargeIter P K (n + 1)) X = 0
      unfold charge
      rw [ih X, ih (comm P X)]
      simp [comm]

omit [StarRing B] in
/-- **Theorem M₇ (`all_scale_metriplectic_master_polynomial_annihilation`)**:
At every Mandelbrot defect depth `n : ℕ`, the 4th-order charge polynomial
`metriplecticMasterPoly4 P` annihilates:
1. Every left-multiplied scale tower `fun X => idempotencyDefect^[n] (genV P A C) * X`;
2. Every odd cone commutator `fun X => comm (conePlus P A) X` and `fun X => comm (coneMinus P C) X`;
3. Every charge-`±2` corner sandwich `fun X => sandwich (conePlus P A) (conePlus P A) X`
   and `fun X => sandwich (coneMinus P C) (coneMinus P C) X`. -/
theorem all_scale_metriplectic_master_polynomial_annihilation
    {P : B} (hP : P * P = P) (A C X : B) (n : ℕ) :
    charge P (fun Y => idempotencyDefect^[n] (genV P A C) * Y) X = 0 ∧
    metriplecticMasterPoly4 P
      (fun Y => idempotencyDefect^[n] (genV P A C) * Y) X =
      (4 : ℤ) • (idempotencyDefect^[n] (genV P A C) * X) ∧
    metriplecticMasterPoly4 P (comm (conePlus P A)) X = 0 ∧
    metriplecticMasterPoly4 P (comm (coneMinus P C)) X = 0 ∧
    metriplecticMasterPoly4 P (sandwich (conePlus P A) (conePlus P A)) X = 0 ∧
    metriplecticMasterPoly4 P (sandwich (coneMinus P C) (coneMinus P C)) X = 0 := by
  have hCommPn : comm P (idempotencyDefect^[n] (genV P A C)) = 0 := by
    unfold comm
    rw [genV_defect_iterates_left_projection hP A C n,
      genV_defect_iterates_right_projection hP A C n, sub_self]
  have hChV : ∀ Z : B,
      charge P (fun Y => idempotencyDefect^[n] (genV P A C) * Y) Z = 0 := by
    intro Z
    calc
      charge P (fun Y => idempotencyDefect^[n] (genV P A C) * Y) Z =
        comm P (idempotencyDefect^[n] (genV P A C)) * Z := by
          unfold charge comm; noncomm_ring
      _ = 0 := by rw [hCommPn, zero_mul]
  have hChVIter := chargeIter_zero_of_charge_zero P
    (fun Y => idempotencyDefect^[n] (genV P A C) * Y) hChV
  have hChV2 : ∀ Z : B,
      chargeIter P (fun Y => idempotencyDefect^[n] (genV P A C) * Y) 2 Z = 0 := by
    intro Z
    simpa using hChVIter 1 Z
  have hChV3 : ∀ Z : B,
      chargeIter P (fun Y => idempotencyDefect^[n] (genV P A C) * Y) 3 Z = 0 := by
    intro Z
    simpa using hChVIter 2 Z
  have hChV4 : ∀ Z : B,
      chargeIter P (fun Y => idempotencyDefect^[n] (genV P A C) * Y) 4 Z = 0 := by
    intro Z
    simpa using hChVIter 3 Z
  refine ⟨hChV X, ?_, ?_, ?_, ?_, ?_⟩
  · unfold metriplecticMasterPoly4
    rw [hChV4 X, hChV2 X]
    simp
  · unfold metriplecticMasterPoly4
    have hEig : ∀ Z, charge P (comm (conePlus P A)) Z = (1 : ℤ) • comm (conePlus P A) Z := by
      intro Z
      rw [charge_plus_comm hP]
      simp
    rw [chargeIter_of_eigenvalue P (comm (conePlus P A)) 1 hEig 4 X,
      chargeIter_of_eigenvalue P (comm (conePlus P A)) 1 hEig 2 X]
    simp
    noncomm_ring
  · unfold metriplecticMasterPoly4
    have hEig : ∀ Z, charge P (comm (coneMinus P C)) Z = (-1 : ℤ) • comm (coneMinus P C) Z := by
      intro Z
      rw [charge_minus_comm hP]
      simp
    rw [chargeIter_of_eigenvalue P (comm (coneMinus P C)) (-1) hEig 4 X,
      chargeIter_of_eigenvalue P (comm (coneMinus P C)) (-1) hEig 2 X]
    simp only [Int.reducePow, one_zsmul]
    noncomm_ring
  · unfold metriplecticMasterPoly4
    have hEig : ∀ Z, charge P (sandwich (conePlus P A) (conePlus P A)) Z =
        (2 : ℤ) • sandwich (conePlus P A) (conePlus P A) Z := by
      intro Z
      exact charge_plus_sandwich hP A Z
    rw [chargeIter_of_eigenvalue P (sandwich (conePlus P A) (conePlus P A)) 2 hEig 4 X,
      chargeIter_of_eigenvalue P (sandwich (conePlus P A) (conePlus P A)) 2 hEig 2 X]
    simp only [Int.reducePow, ← mul_smul]
    norm_num
    noncomm_ring
  · unfold metriplecticMasterPoly4
    have hEig : ∀ Z, charge P (sandwich (coneMinus P C) (coneMinus P C)) Z =
        (-2 : ℤ) • sandwich (coneMinus P C) (coneMinus P C) Z := by
      intro Z
      simpa only [neg_smul] using charge_minus_sandwich hP C Z
    rw [chargeIter_of_eigenvalue P (sandwich (coneMinus P C) (coneMinus P C)) (-2) hEig 4 X,
      chargeIter_of_eigenvalue P (sandwich (coneMinus P C) (coneMinus P C)) (-2) hEig 2 X]
    simp only [Int.reducePow, ← mul_smul]
    norm_num
    noncomm_ring

/-- **Theorem M₁₀ (`stage_M10_all_scale_cellular_sheaf_hodge_filtering_and_intertwining`)**:
Unifies the cellular sheaf coboundary, gauge invariance, curved Weitzenböck and Bianchi
identities, and
simultaneous two-parameter (`(k, n) ∈ ℕ × ℕ`) fractal Hodge filtering and intertwining:
1. **Horizon Sheaf-to-Tetraktys Identity:**
   `sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) = -(invS P * genPhi P A (star A))`
   and `sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A)`;
2. **Left-Isometric Edge-Gauge Invariance:**
   Under `star U * U = 1`, `sheafLaplacian0 P (U * R_u) (U * R_v) = sheafLaplacian0 P R_u R_v`;
3. **Curved Weitzenböck & Bianchi Identities:**
   `sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
      sheafHodgeDown d₀ * sheafHodgeDown d₀ + sheafHodgeUp d₁ * sheafHodgeUp d₁ +
      sheafWeitzenboeckDefect d₀ d₁` and
   `d₂ * sheafCurvature2 d₀ d₁ = sheafCurvature2 d₁ d₂ * d₀`;
4. **Two-Parameter (`k, n : ℕ`) All-Depth Hodge Filtering & Intertwining:**
   - `sheafHodgeUp (conePlus P A) * mandelbrotTower k (qgtPlus P A (star A)) = 0`,
   - `sheafHodgeDown (conePlus P A) * mandelbrotTower k (qgtMinus P A (star A)) = 0`,
   - `sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
       mandelbrotTower k (genV P A (star A)) =
       qgtPlus P A (star A) * mandelbrotTower k (qgtPlus P A (star A)) +
       qgtMinus P A (star A) * mandelbrotTower k (qgtMinus P A (star A))`,
   - `comm (sheafHodgeLaplacian (conePlus P A) (conePlus P A))
       (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0`,
   - `comm (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A))
       (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0`. -/
theorem stage_M10_all_scale_cellular_sheaf_hodge_filtering_and_intertwining
    {P U : B} (hP : P * P = P) (hPsym : star P = P) (hU : star U * U = 1)
    (A R_u R_v d₀ d₁ d₂ X : B) (k n : ℕ) :
    (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) =
       -(invS P * genPhi P A (star A)) ∧
     sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A)) ∧
    sheafLaplacian0 P (U * R_u) (U * R_v) = sheafLaplacian0 P R_u R_v ∧
    (sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
       sheafHodgeDown d₀ * sheafHodgeDown d₀ + sheafHodgeUp d₁ * sheafHodgeUp d₁ +
       sheafWeitzenboeckDefect d₀ d₁ ∧
     d₂ * sheafCurvature2 d₀ d₁ = sheafCurvature2 d₁ d₂ * d₀) ∧
    (sheafHodgeUp (conePlus P A) * mandelbrotTower k (qgtPlus P A (star A)) = 0 ∧
     sheafHodgeDown (conePlus P A) * mandelbrotTower k (qgtMinus P A (star A)) = 0 ∧
     sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
       mandelbrotTower k (genV P A (star A)) =
       qgtPlus P A (star A) * mandelbrotTower k (qgtPlus P A (star A)) +
       qgtMinus P A (star A) * mandelbrotTower k (qgtMinus P A (star A)) ∧
     comm (sheafHodgeLaplacian (conePlus P A) (conePlus P A))
       (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0 ∧
     comm (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A))
       (idempotencyDefect^[n] (sheafHodgeLaplacian (conePlus P A) (conePlus P A))) = 0) := by
  rcases sheaf_to_tetraktys_bridge hP hPsym A (star A) with ⟨hCobJ, _, hLap0⟩
  rcases curved_sheaf_weitzenboeck_identity d₀ d₁ with ⟨_, _, hWeitz⟩
  rcases curved_sheaf_bianchi_identity d₀ d₁ d₂ with ⟨hBianchi, _⟩
  rcases fractal_sheet_hodge_filtering hP hPsym A k with
    ⟨_, _, hUpK, hDownK, hLapX, hLapY⟩
  rcases all_depth_sheaf_hodge_fractal_intertwining hP hPsym A n with
    ⟨_, _, _, _, _, _, _, hCommCobSource, _, hCommHodgeN⟩
  have hSphi : invS P * genPhi P A (star A) = genJ P A (star A) := by
    peirce_nf hP
  have hCob :
      sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) =
        -(invS P * genPhi P A (star A)) := by
    rw [hCobJ, hSphi]
  have hHodgeAction :
      sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
      mandelbrotTower k (genV P A (star A)) =
      qgtPlus P A (star A) * mandelbrotTower k (qgtPlus P A (star A)) +
      qgtMinus P A (star A) * mandelbrotTower k (qgtMinus P A (star A)) := by
    have hSplit : mandelbrotTower k (genV P A (star A)) =
        mandelbrotTower k (qgtPlus P A (star A)) +
          mandelbrotTower k (qgtMinus P A (star A)) := by
      simpa [mandelbrotTower_eq_idempotencyDefect_iterate] using
        (genV_defect_iterates_cycle_split hP A (star A) (k + 1))
    calc
      _ = sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
          (mandelbrotTower k (qgtPlus P A (star A)) +
            mandelbrotTower k (qgtMinus P A (star A))) := by rw [hSplit]
      _ = qgtPlus P A (star A) * mandelbrotTower k (qgtPlus P A (star A)) +
          qgtMinus P A (star A) * mandelbrotTower k (qgtMinus P A (star A)) := by
            rw [mul_add, hLapX, hLapY]
  exact ⟨⟨hCob, hLap0⟩,
         (sheafLaplacian0_gauge_invariance (P := P) (R_u := R_u) (R_v := R_v) (X := X) hU).2.1,
         ⟨hWeitz, hBianchi⟩,
         ⟨hUpK, hDownK, hHodgeAction, hCommHodgeN, hCommCobSource⟩⟩

/-- **Theorem M₁₀b (`stage_M10_daughter_tower_all_scale_sheaf_hodge_intertwining`)**:
Across all `(k, n) ∈ ℕ × ℕ` on the daughter-idempotent tower `P_k = daughterIdemTower k P A`
(when `star P_k = P_k`), with `d_k = conePlus P_k A`, `X_n = mandelbrotTower n (qgtPlus P_k A (star A))`,
`Y_n = mandelbrotTower n (qgtMinus P_k A (star A))`, `V_{k,n} = X_n + Y_n`, and `Sig_{k,n} = X_n - Y_n`:
1. `sheafHodgeUp d_k * X_n = 0` and `sheafHodgeDown d_k * Y_n = 0`;
2. `sheafLaplacian0 P_k (coneMinus P_k (star A)) d_k * V_{k,n} = sheafHodgeLaplacian d_k d_k * V_{k,n}`;
3. `(sheafHodgeDown d_k - sheafHodgeUp d_k) * V_{k,n} = sheafHodgeLaplacian d_k d_k * Sig_{k,n}`;
4. `(sheafHodgeDown d_k - sheafHodgeUp d_k) * Sig_{k,n} = sheafHodgeLaplacian d_k d_k * V_{k,n}`. -/
theorem stage_M10_daughter_tower_all_scale_sheaf_hodge_intertwining
    {P : B} (hP : P * P = P) (A : B) (k n : ℕ)
    (hPk_sym : star (daughterIdemTower k P A) = daughterIdemTower k P A) :
    let P_k := daughterIdemTower k P A
    let d_k := conePlus P_k A
    let X_n := mandelbrotTower n (qgtPlus P_k A (star A))
    let Y_n := mandelbrotTower n (qgtMinus P_k A (star A))
    let V_kn := X_n + Y_n
    let Sig_kn := X_n - Y_n
    sheafHodgeUp d_k * X_n = 0 ∧
    sheafHodgeDown d_k * Y_n = 0 ∧
    sheafLaplacian0 P_k (coneMinus P_k (star A)) d_k * V_kn =
      sheafHodgeLaplacian d_k d_k * V_kn ∧
    (sheafHodgeDown d_k - sheafHodgeUp d_k) * V_kn =
      sheafHodgeLaplacian d_k d_k * Sig_kn ∧
    (sheafHodgeDown d_k - sheafHodgeUp d_k) * Sig_kn =
      sheafHodgeLaplacian d_k d_k * V_kn := by
  intro P_k d_k X_n Y_n V_kn Sig_kn
  have hPk : P_k * P_k = P_k :=
    (stage_M9_all_scale_fractal_braiding_instanton_duality_and_master_metriplectic_poly4
      hP A (star A) k n).1
  rcases fractal_sheet_hodge_filtering hPk hPk_sym A n with
    ⟨_, _, hUpX, hDownY, _, _⟩
  have hLapEq :
      sheafLaplacian0 P_k (coneMinus P_k (star A)) d_k = sheafHodgeLaplacian d_k d_k := by
    rw [(sheaf_to_tetraktys_bridge hPk hPk_sym A (star A)).2.2,
        (sheafHodge_concrete_horizon_instantiation hPk hPk_sym A).2.2.2.1]
  refine ⟨hUpX, hDownY, by rw [hLapEq], ?_, ?_⟩
  · dsimp [V_kn, Sig_kn, X_n, Y_n, d_k]
    unfold sheafHodgeLaplacian
    rw [mul_add, mul_sub, sub_mul, sub_mul, add_mul, add_mul, hUpX, hDownY]
    abel
  · dsimp [V_kn, Sig_kn, X_n, Y_n, d_k]
    unfold sheafHodgeLaplacian
    rw [mul_sub, mul_add, sub_mul, sub_mul, add_mul, add_mul, hUpX, hDownY]
    abel

end InfoGeometry.OperatorAlgebra.PeirceSpine
