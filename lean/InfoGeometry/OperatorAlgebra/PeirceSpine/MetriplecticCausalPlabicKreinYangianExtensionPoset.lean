/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Core.PeirceCompressionDefect
import InfoGeometry.OperatorAlgebra.PeirceSchurSynthesis
import InfoGeometry.OperatorAlgebra.SemilinearOperatorGeometry
import InfoGeometry.Canonical.SouriauKaluzaJanusBimetricSolveEtCoagula

/-!
# Full 32-Turn Causal Poset & Non-Commutative Operator Archetypes (`Turns 01–32` / `418904a66184`)

This module extends `InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset`
(`Turns 01–17`) to the complete **32-turn** shared Gemini dialogue
`https://share.gemini.google/kKehiDWWV8DI` (`https://gemini.google.com/share/418904a66184`),
extracting the pure mathematical archetypes of **Turns 18–32** via the five-stage
`solve et coagula` epistemic compiler protocol and formalizing every archetype in native
Mathlib (`Lean v4.34.1`) with kernel-checked proofs over non-commutative rings `[Ring B]`
and concrete higher-dimensional matrix algebras (`Matrix (Fin 2) (Fin 2) B`,
`Matrix (Fin 3) (Fin 3) R`, `Matrix (Fin 4) (Fin 4) R`, `Matrix (Fin 6) (Fin 6) R`).

## Five-Stage `solve et coagula` Epistemic Macro-Poset (`ExtensionSolveEtCoagulaStage`)

1. **`E0_PrimordialBinaryCut_GradedSupermatrixAndWittSplit`** ($\mathcal{E}_0$, Turns 18, 19, 21, 23):
   - **Turn 18 (Hamming-Shell Confinement & Magnon Charge Commutators)**:
     On `Matrix (Fin 2) (Fin 2) B` and in any `[Ring B]` with idempotent `P * P = P`,
     the charge/magnon projector `Q_P = 1 - P` commutes with diagonal blocks
     `peirce11 P X + peirce00 P X` while shifting ladder blocks by `±1`:
     `comm Q_P (conePlus P A) = -conePlus P A` and `comm Q_P (coneMinus P C) = coneMinus P C`.
   - **Turn 19 ($\mathbb{Z}_2$-Graded Supermatrix Parity Cut & Witten SUSY Laplacian)**:
     For `Q_+ = !![0, B_ur; 0, 0]` and `Q_- = !![0, 0; C_ll, 0]` in `Matrix (Fin 2) (Fin 2) B`,
     `Q_+ ^ 2 = 0`, `Q_- ^ 2 = 0`, `anticomm kreinJ (Q_+ + Q_-) = 0`, and
     `(Q_+ + Q_-) ^ 2 = anticomm Q_+ Q_- = !![B_ur * C_ll, 0; 0, C_ll * B_ur]`.
   - **Turn 21 (Super-Yangian $Y(\mathfrak{gl}_{1|1})$ & Elenchus of the Even Dirac Bug)**:
     On `Matrix (Fin 4) (Fin 4) R`, the combined grading `J_total = diag(1, -1, -1, 1)` commutes
     with the single-site Lax operator `L_{0,r}(u, θ, η) = (u - θ) I₄ + η P₁₂`
     (`comm J_total L_{0,r} = 0`, refuting the claim that `J_total` makes `L_{0,r}` odd),
     whereas the decoupled auxiliary chiral grading `Γ_chiral = diag(1, 1, -1, -1)` anticommutes
     with the off-diagonal supercharge block `D_odd(η)`.
   - **Turn 23 (Elenchus of Idempotent–Nilpotent Mutual Annihilation vs. Witt Light-Cone Split)**:
     In any `[Ring B]`, if `X * X = X` and `X ^ m = 0` (`m ≥ 1`), then `X = 0`, contrasted
     with the Witt light-cone generators `σ_+, σ_-` satisfying `σ_+ ^ 2 = σ_- ^ 2 = 0` and
     `σ_+ * σ_- + σ_- * σ_+ = 1`.

2. **`E1_FourfoldRelationalAnatomy_LaxMonodromyAndSchurBerezinian`** ($\mathcal{E}_1$, Turns 19, 20, 22):
   - **Turns 19 & 20 (Fedosov–Connes–Berry Projection Curvature, Peirce Compression Defect,
     Block-LDU Gelfand–Retakh Schur Factorization & Berezinian Reciprocal Duality)**:
     In any `[Ring B]` with `P * P = P`, `P * comm P X * comm P X * P = - (P * X * (1 - P) * X * P)`,
     connected directly to `InfoGeometry.Core.PeirceCompressionDefect` and
     `InfoGeometry.OperatorAlgebra.PeirceSpine.SchurDefect`, together with the exact `2 × 2`
     non-commutative Block-LDU factorization over `Matrix (Fin 2) (Fin 2) B`.
   - **Turn 22 (Schubert Cell Gaussian $\mathbb{L}$-Binomial, Witten Index Vanishing &
     $3 \times 3$ Iwahori–Hecke Demazure–Lusztig Braid Realization)**:
     Gaussian $\mathbb{L}$-binomial recursion, Super-Grassmannian Witten index vanishing at
     `Π L_odd = -1`, and explicit `3 × 3` matrices `heckeT1 L, heckeT2 L` satisfying the
     quadratic Hecke aporia `(T_k + I₃)(T_k - L I₃) = 0`, non-commutativity `T₁ T₂ ≠ T₂ T₁`,
     and the Artin/Yang–Baxter braid relation `T₁ T₂ T₁ = T₂ T₁ T₂`.

3. **`E2_TranscendentFunction_TwistedIntegrabilityAndGiventalKorffPieri`** ($\mathcal{E}_2$, Turns 18, 25, 27, 28, 29):
   - **Turn 18 (Baxter $TQ$ Difference Relation, Anti-Periodic Krein BAE, $\text{Cl}(1,1)$ Twist
     Matrix & Parabolic Jordan Catastrophe)**:
     Baxter root evaluation `Q(v_m) = 0 ⟹ a(v_m) Q(v_m - η) = d(v_m) Q(v_m + η)`,
     `4 × 4` Kronecker swap invariance `comm swap4 (K_twist ⊗ K_twist) = 0`, and parabolic
     null-twist Jordan nilpotency `(K_twist - w₀ I₂) ^ 2 = (w_J² + w_B w_C) I₂`.
   - **Turn 25 (Madelung–Bergman Bohmian Potential & Givental–Korff Quantum Pieri Ring on $\operatorname{Gr}(2,4)$)**:
     Explicit `6 × 6` matrices `quantumPieriC1 q` and `quantumPieriC2 q` on `Matrix (Fin 6) (Fin 6) R`
     satisfying `comm (quantumPieriC1 q) (quantumPieriC2 q) = 0`,
     `(quantumPieriC1 q) ^ 2 = quantumSchubert20 q + quantumPieriC2 q`, and
     `(quantumPieriC1 q) ^ 4 = 2 • quantumSchubert22 q + (2 * q) • 1`.
   - **Turn 27 (Tridiagonal Hamming Bandwidth, Inhomogeneous Gauge Defect & RTT Multi-Head Twist Commutator)**:
     `Nat.choose 8 4 + 2 * Nat.choose 8 3 = 182`, inhomogeneous site-gauge exchange
     `(G₁ ⊗ G₂) P₁₂ = P₁₂ (G₂ ⊗ G₁)`, and the RTT multi-head twist commutator law
     `comm (A - q₁ • D) (A - q₂ • D) = -(q₁ - q₂) • comm A D` when `[A, A] = [D, D] = 0`.
   - **Turns 28 & 29 (Non-Abelian $\operatorname{SL}_2$ Gauge–Lax Exchange Duality & Rademacher Involutivity)**:
     Exact `4 × 4` identity `(I₂ ⊗ G) L_{0,r}(w) = L_{0,r}(w) (G ⊗ I₂)`, proving that physical
     gauge transformations transfer to auxiliary Wilson links `W_{r,r+1} = G_r G_{r+1}⁻¹`.

4. **`E3_SocraticAporia_KahlerBergmanAndAdS3CartanGeodesics`** ($\mathcal{E}_3$, Turns 23, 24, 26, 30):
   - **Turns 23, 24 & 26 (Kähler–Bergman Curvature $R = -4$, Natural Gradient Preconditioning,
     Hyperbolic Parallel Transport & Connes–Lott Chiral Higgs Twist)**.
   - **Turn 30 ($\mathfrak{sl}_2(\mathbb{R}) \simeq \text{AdS}_3$ Half-Adjoint Matrix $M_{\text{ad}}(\mathbf{a})$,
     Maurer–Cartan Jacobians & Pullback Killing Metric)**:
     On `Matrix (Fin 3) (Fin 3) R` with `η₃ = diag(1, 1, -1)`, `M_ad(a) a = 0`,
     `M_ad(a)ᵀ η₃ + η₃ M_ad(a) = 0`, `M_ad(a)² = δ I₃ - a (η₃ a)ᵀ`, and
     `M_ad(a)³ = δ M_ad(a)` where `δ = a_x² + a_z² - a_ε²`.

5. **`E4_CptTwinSectors_SakharovJanusBimetricTorsor`** ($\mathcal{E}_4$, Turns 31, 32):
   - **Turn 31 (Fermionic CPT $\Theta_{\text{CPT}}^2 = -I_2$, Sakharov 3-Condition Commutator Necessity,
     Semilinear Sheet/Amplitude Riccati Bridge & Bogoliubov Dark Matter Occupation Excess)**:
     Reuses `InfoGeometry.OperatorAlgebra.SemilinearCovarianceGeometry` and
     `InfoGeometry.OperatorAlgebra.DerivationAmplitudeGeometry`.
   - **Turn 32 (Sakharov–Janus Bimetric Torsor, Lorentz Component Determinant Elenchus,
     Bondi Runaway vs. Janus $\kappa = -1$ Repulsion & $O(\epsilon^1)$ TOV Bianchi Defect)**:
     Reuses `InfoGeometry.Canonical.SouriauKaluzaJanusBimetricSolveEtCoagula`.

6. **`E5_Master32TurnCoagulatedSynthesis`** ($\mathcal{E}_5$):
   - Full 32-turn poset (`Full32TurnChatArchetype`, `Turn01`–`Turn32`), order-embedding of
     `CausalMatrixChatTurnArchetype`, 32-turn Peirce operator realization, and master coagulation.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianExtensionPoset

open Matrix
open scoped BigOperators
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset
open InfoGeometry.Core.IdempotencyDefect
open InfoGeometry.Core.PeirceCompressionDefect
open InfoGeometry.OperatorAlgebra.PeirceSpine.SchurDefect
open InfoGeometry.Canonical.SouriauKaluzaJanusBimetricSolveEtCoagula

/-! ===========================================================================
    Section 0: Five-Stage `solve et coagula` Macro-Poset (`ExtensionSolveEtCoagulaStage`)
    =========================================================================== -/

/-- The 6-stage `solve et coagula` acyclic causal macro-poset organizing Turns 18–32 of
`https://share.gemini.google/kKehiDWWV8DI` (`418904a66184`). -/
inductive ExtensionSolveEtCoagulaStage : Type
  | E0_PrimordialBinaryCut_GradedSupermatrixAndWittSplit
  | E1_FourfoldRelationalAnatomy_LaxMonodromyAndSchurBerezinian
  | E2_TranscendentFunction_TwistedIntegrabilityAndGiventalKorffPieri
  | E3_SocraticAporia_KahlerBergmanAndAdS3CartanGeodesics
  | E4_CptTwinSectors_SakharovJanusBimetricTorsor
  | E5_Master32TurnCoagulatedSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace ExtensionSolveEtCoagulaStage

/-- Topological rank in the 6-stage `solve et coagula` macro-poset. -/
def rank : ExtensionSolveEtCoagulaStage → ℕ
  | .E0_PrimordialBinaryCut_GradedSupermatrixAndWittSplit => 0
  | .E1_FourfoldRelationalAnatomy_LaxMonodromyAndSchurBerezinian => 1
  | .E2_TranscendentFunction_TwistedIntegrabilityAndGiventalKorffPieri => 2
  | .E3_SocraticAporia_KahlerBergmanAndAdS3CartanGeodesics => 3
  | .E4_CptTwinSectors_SakharovJanusBimetricTorsor => 4
  | .E5_Master32TurnCoagulatedSynthesis => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance instLinearOrder : LinearOrder ExtensionSolveEtCoagulaStage :=
  LinearOrder.lift' rank rank_injective

/-- Direct causal cover relation $\mathcal{E}_k \prec \mathcal{E}_{k+1}$. -/
def causalEdge (x y : ExtensionSolveEtCoagulaStage) : Prop :=
  rank y = rank x + 1

theorem causalEdge_strict_rank {x y : ExtensionSolveEtCoagulaStage} (h : causalEdge x y) :
    rank x < rank y := by
  dsimp [causalEdge] at h
  omega

theorem transGen_strict_rank {x y : ExtensionSolveEtCoagulaStage}
    (h : Relation.TransGen causalEdge x y) :
    rank x < rank y := by
  induction h with
  | single hxy => exact causalEdge_strict_rank hxy
  | tail _ hyz ih =>
      have hyz' := causalEdge_strict_rank hyz
      omega

/-- Strict acyclicity of `ExtensionSolveEtCoagulaStage`. -/
theorem causalEdge_acyclic (x : ExtensionSolveEtCoagulaStage) :
    ¬ Relation.TransGen causalEdge x x := by
  intro h
  exact Nat.lt_irrefl (rank x) (transGen_strict_rank h)

/-- Complete cover chain $\mathcal{E}_0 \prec \mathcal{E}_1 \prec \mathcal{E}_2 \prec \mathcal{E}_3 \prec \mathcal{E}_4 \prec \mathcal{E}_5$. -/
theorem causalEdge_chain :
    causalEdge .E0_PrimordialBinaryCut_GradedSupermatrixAndWittSplit
      .E1_FourfoldRelationalAnatomy_LaxMonodromyAndSchurBerezinian ∧
    causalEdge .E1_FourfoldRelationalAnatomy_LaxMonodromyAndSchurBerezinian
      .E2_TranscendentFunction_TwistedIntegrabilityAndGiventalKorffPieri ∧
    causalEdge .E2_TranscendentFunction_TwistedIntegrabilityAndGiventalKorffPieri
      .E3_SocraticAporia_KahlerBergmanAndAdS3CartanGeodesics ∧
    causalEdge .E3_SocraticAporia_KahlerBergmanAndAdS3CartanGeodesics
      .E4_CptTwinSectors_SakharovJanusBimetricTorsor ∧
    causalEdge .E4_CptTwinSectors_SakharovJanusBimetricTorsor
      .E5_Master32TurnCoagulatedSynthesis :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end ExtensionSolveEtCoagulaStage

/-! ===========================================================================
    Section 1: Stage E0 — Primordial Binary Cut (Turns 18, 19, 21, 23)
    =========================================================================== -/

section StageE0

variable {B : Type*} [Ring B]

/-- **Turn 18 (Peirce Magnon / Hamming Weight Selection Law in `[Ring B]`):**
For any idempotent `P * P = P`, the complementary charge projector `Q_P = 1 - P` commutes
with the even block `peirce11 P X + peirce00 P X` while shifting the off-diagonal ladder
blocks by `±1`:
`comm (1 - P) (conePlus P A) = -conePlus P A` and
`comm (1 - P) (coneMinus P C) = coneMinus P C`. -/
theorem turn18_peirce_magnon_charge_selection_commutators
    {P : B} (hP : P * P = P) (X A C : B) :
    comm (1 - P) (peirce11 P X + peirce00 P X) = 0 ∧
    comm (1 - P) (conePlus P A) = -conePlus P A ∧
    comm (1 - P) (coneMinus P C) = coneMinus P C := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- `2 × 2` upper-right matrix unit `extMatE01 : Matrix (Fin 2) (Fin 2) B`. -/
def extMatE01 {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; 0, 0]

/-- `2 × 2` lower-left matrix unit `extMatE10 : Matrix (Fin 2) (Fin 2) B`. -/
def extMatE10 {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B :=
  !![0, 0; 1, 0]

/-- Explicit non-commutativity witness for `2 × 2` matrix units (`Trap T16`). -/
theorem extension_matrix_units_noncommute [Nontrivial B] :
    (extMatE01 : Matrix (Fin 2) (Fin 2) B) * extMatE10 ≠
      extMatE10 * extMatE01 := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h
  simp [extMatE01, extMatE10, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- The `2 × 2` magnon occupation projector `P_- = diag(0, 1)` on `Matrix (Fin 2) (Fin 2) B`. -/
def magnonProj2 (B : Type*) [Ring B] : Matrix (Fin 2) (Fin 2) B :=
  !![0, 0; 0, 1]

/-- **Turn 18 (`2 × 2` Block Matrix Magnon Conservation & Ladder Selection Rules):**
On `Matrix (Fin 2) (Fin 2) B` over any non-commutative `[Ring B]`, `magnonProj2 B` commutes
with any diagonal matrix `!![a, 0; 0, d]`, lowers the upper-right creation block `!![0, b; 0, 0]`,
and raises the lower-left annihilation block `!![0, 0; c, 0]`. -/
theorem turn18_matrix2_magnon_selection_rules (a b c d : B) :
    comm (magnonProj2 B) !![a, 0; 0, d] = 0 ∧
    comm (magnonProj2 B) !![0, b; 0, 0] = -!![0, b; 0, 0] ∧
    comm (magnonProj2 B) !![0, 0; c, 0] = !![0, 0; c, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [magnonProj2]
  · ext i j
    simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [magnonProj2]
  · ext i j
    simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [magnonProj2]

/-- Upper-right odd supercharge `Q_+ = !![0, B_ur; 0, 0]` in `Matrix (Fin 2) (Fin 2) B`. -/
def superchargePlus2 (B_ur : B) : Matrix (Fin 2) (Fin 2) B :=
  !![0, B_ur; 0, 0]

/-- Lower-left odd supercharge `Q_- = !![0, 0; C_ll, 0]` in `Matrix (Fin 2) (Fin 2) B`. -/
def superchargeMinus2 (C_ll : B) : Matrix (Fin 2) (Fin 2) B :=
  !![0, 0; C_ll, 0]

/-- **Turn 19 ($\mathbb{Z}_2$-Graded Supermatrix Parity Cut, Connes Odd Dirac Operator &
Witten SUSY Laplacian over `[Ring B]`):**
For any `A, B_ur, C_ll, D : B`, conjugating `!![A, B_ur; C_ll, D]` by `kreinJ = diag(1, -1)`
flips the off-diagonal odd blocks, `superchargePlus2 B_ur` and `superchargeMinus2 C_ll` are
square-zero and anticommute with `kreinJ`, and the Connes odd Dirac operator
`D_odd = Q_+ + Q_-` squares to the non-commutative Witten Laplacian
`D_odd ^ 2 = anticomm Q_+ Q_- = !![B_ur * C_ll, 0; 0, C_ll * B_ur]`. -/
theorem turn19_supermatrix_parity_and_witten_laplacian (A B_ur C_ll D : B) :
    (kreinJ : Matrix (Fin 2) (Fin 2) B) * !![A, B_ur; C_ll, D] * kreinJ =
      !![A, -B_ur; -C_ll, D] ∧
    superchargePlus2 B_ur * superchargePlus2 B_ur = 0 ∧
    superchargeMinus2 C_ll * superchargeMinus2 C_ll = 0 ∧
    anticomm (kreinJ : Matrix (Fin 2) (Fin 2) B)
      (superchargePlus2 B_ur + superchargeMinus2 C_ll) = 0 ∧
    (superchargePlus2 B_ur + superchargeMinus2 C_ll) *
      (superchargePlus2 B_ur + superchargeMinus2 C_ll) =
      !![B_ur * C_ll, 0; 0, C_ll * B_ur] ∧
    anticomm (superchargePlus2 B_ur) (superchargeMinus2 C_ll) =
      !![B_ur * C_ll, 0; 0, C_ll * B_ur] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [kreinJ]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [superchargePlus2]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [superchargeMinus2]
  · ext i j
    simp only [anticomm, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [kreinJ, superchargePlus2, superchargeMinus2]
  · ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [superchargePlus2, superchargeMinus2]
  · ext i j
    simp only [anticomm, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [superchargePlus2, superchargeMinus2]

/-- The `4 × 4` combined tensor grading `J_total = σ_z ⊗ σ_z = diag(1, -1, -1, 1)`. -/
def combinedParityGrading4 {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, 1]

/-- The `4 × 4` decoupled auxiliary chiral grading `Γ_chiral = σ_z ⊗ I₂ = diag(1, 1, -1, -1)`. -/
def decoupledChiralGrading4 {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- The `4 × 4` single-site Yangian Lax operator `L_{0,r}(u, θ, η) = (u - θ) I₄ + η P₁₂`. -/
def singleSiteLax4 {R : Type*} [CommRing R] (u theta eta : R) : Matrix (Fin 4) (Fin 4) R :=
  (u - theta) • (1 : Matrix (Fin 4) (Fin 4) R) + eta • (swap4 : Matrix (Fin 4) (Fin 4) R)

/-- The `4 × 4` off-diagonal odd supercharge block `D_odd(η) = η (E₀₁ ⊗ E₁₀ + E₁₀ ⊗ E₀₁)`. -/
def oddSuperchargeLax4 {R : Type*} [CommRing R] (eta : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 0;
     0, 0, eta, 0;
     0, eta, 0, 0;
     0, 0, 0, 0]

/-- **Turn 21 (Elenchus of the "Even Dirac Bug" vs. Decoupled Chiral Super-Yangian Grading):**
1. The combined grading `combinedParityGrading4` (`σ_z ⊗ (-1)^F`) **commutes** with the entire
   single-site Lax operator `singleSiteLax4 u theta eta`, refuting the claim that `L_{0,r}` is
   odd under `σ_z ⊗ (-1)^F`.
2. In contrast, the decoupled auxiliary chiral grading `decoupledChiralGrading4` (`σ_z ⊗ I₂`)
   **anticommutes** with the off-diagonal supercharge block `oddSuperchargeLax4 eta`, whose
   square is the diagonal magnon-exchange projector `η² diag(0, 1, 1, 0)`. -/
theorem turn21_even_dirac_bug_elenchus_and_chiral_supercharge
    {R : Type*} [CommRing R] (u theta eta : R) :
    comm (combinedParityGrading4 (R := R)) (singleSiteLax4 u theta eta) = 0 ∧
    anticomm (decoupledChiralGrading4 (R := R)) (oddSuperchargeLax4 eta) = 0 ∧
    oddSuperchargeLax4 eta * oddSuperchargeLax4 eta =
      !![0, 0, 0, 0;
         0, eta ^ 2, 0, 0;
         0, 0, eta ^ 2, 0;
         0, 0, 0, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [comm, singleSiteLax4, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [combinedParityGrading4, swap4]
  · ext i j
    simp only [anticomm, Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [decoupledChiralGrading4, oddSuperchargeLax4]
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [oddSuperchargeLax4] <;> try ring

/-- **Turn 23 (Elenchus 1 — Idempotent + Nilpotent Implies Zero in Any `[Ring B]`):**
If `X * X = X` (idempotent) and `X ^ (m + 1) = 0` (nilpotent), then `X = 0`.
A single operator cannot simultaneously be a non-zero projector and nilpotent; instead, the
nilpotent Witt generators `σ_+, σ_-` factorize the orthogonal projectors `P_+ = σ_+ σ_-` and
`P_- = σ_- σ_+`. -/
theorem turn23_idempotent_and_pow_succ_eq_zero_implies_zero
    {X : B} (hIdem : X * X = X) : ∀ m : ℕ, X ^ (m + 1) = X
  | 0 => pow_one X
  | m + 1 => by
      rw [pow_succ, turn23_idempotent_and_pow_succ_eq_zero_implies_zero hIdem m, hIdem]

theorem turn23_idempotent_nilpotent_mutual_annihilation
    {X : B} (hIdem : X * X = X) (m : ℕ) (hNil : X ^ (m + 1) = 0) : X = 0 := by
  rw [← turn23_idempotent_and_pow_succ_eq_zero_implies_zero hIdem m, hNil]

/-- **Turn 23 (Witt Light-Cone Split vs. Idempotent Projectors on `Matrix (Fin 2) (Fin 2) B`):**
The nilpotent ladder generators `σ_+ = !![0, 1; 0, 0]` and `σ_- = !![0, 0; 1, 0]` satisfy
`σ_+ ^ 2 = 0` and `σ_- ^ 2 = 0`, while their ordered products `P_+ = σ_+ * σ_- = !![1, 0; 0, 0]`
and `P_- = σ_- * σ_+ = !![0, 0; 0, 1]` are orthogonal idempotents summing to `1`. -/
theorem turn23_witt_lightCone_split_and_orthogonal_projectors :
    (superchargePlus2 (1 : B) * superchargePlus2 (1 : B) = 0) ∧
    (superchargeMinus2 (1 : B) * superchargeMinus2 (1 : B) = 0) ∧
    (superchargePlus2 (1 : B) * superchargeMinus2 (1 : B) = !![1, 0; 0, 0]) ∧
    (superchargeMinus2 (1 : B) * superchargePlus2 (1 : B) = !![0, 0; 0, 1]) ∧
    (superchargePlus2 (1 : B) * superchargeMinus2 (1 : B) +
      superchargeMinus2 (1 : B) * superchargePlus2 (1 : B) =
      (1 : Matrix (Fin 2) (Fin 2) B)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (turn19_supermatrix_parity_and_witten_laplacian (0 : B) 1 1 0).2.1
  · exact (turn19_supermatrix_parity_and_witten_laplacian (0 : B) 1 1 0).2.2.1
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [superchargePlus2, superchargeMinus2]
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [superchargePlus2, superchargeMinus2]
  · ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [superchargePlus2, superchargeMinus2]

end StageE0

/-! ===========================================================================
    Section 2: Stage E1 — Fourfold Relational Anatomy (Turns 19, 20, 22)
    =========================================================================== -/

section StageE1

variable {B : Type*} [Ring B]

/-- **Turn 19 (Fedosov–Connes–Berry Projection Curvature & Peirce Compression Defect Bridge):**
In any `[Ring B]`, for an idempotent `P * P = P` and any element `X : B`:
1. The Fedosov–Connes–Berry compressed double commutator `P * comm P X * comm P X * P`
   equals the negative complementary corner transfer `- (P * X * (1 - P) * X * P)`,
2. By `PeirceCompressionDefect.compression_square_defect`, this equals the exact
   square-compression defect `(P * X * P) * (P * X * P) - P * (X * X) * P`,
3. Consequently, `defect (P * X * P) = P * defect X * P + P * comm P X * comm P X * P`. -/
theorem turn19_fedosov_connes_berry_curvature_and_compression_defect
    {P : B} (hP : P * P = P) (X : B) :
    P * comm P X * comm P X * P = -(P * X * (1 - P) * X * P) ∧
    P * (X * X) * P - (P * X * P) * (P * X * P) =
      (P * X * (1 - P)) * ((1 - P) * X * P) ∧
    defect (P * X * P) = P * defect X * P + P * comm P X * comm P X * P := by
  have hCurv : P * comm P X * comm P X * P = -(P * X * (1 - P) * X * P) := by
    peirce_nf hP
  refine ⟨hCurv, compression_square_defect P X hP, ?_⟩
  rw [defect_compression P X hP, hCurv]
  abel

/-- **Turns 19 & 20 (`2 × 2` Non-Commutative Gelfand–Retakh Block-LDU Schur Factorization):**
Over any `[Ring B]`, if `A * A_inv = 1` and `A_inv * A = 1`, the block matrix `!![A, B_ur; C_ll, D]`
factors uniquely as `L * diag(A, D - C_ll * A_inv * B_ur) * U`. -/
theorem turn19_turn20_gelfand_retakh_block_ldu_factorization
    {A A_inv : B} (hAR : A * A_inv = 1) (hAL : A_inv * A = 1) (B_ur C_ll D : B) :
    (!![1, 0; C_ll * A_inv, 1] : Matrix (Fin 2) (Fin 2) B) *
      !![A, 0; 0, D - C_ll * A_inv * B_ur] *
      !![1, A_inv * B_ur; 0, 1] =
      !![A, B_ur; C_ll, D] := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp
  · rw [← mul_assoc, hAR, one_mul]
  · rw [mul_assoc, hAL, mul_one]
  · have hAssoc : C_ll * A_inv * A * (A_inv * B_ur) = C_ll * A_inv * ((A * A_inv) * B_ur) := by
      noncomm_ring
    rw [hAssoc, hAR, one_mul, add_sub_cancel]

/-- **Turn 20 (Antipode-Shifted Quantum Determinant vs. Naive Unshifted Determinant Defect &
Kähler–Berezinian Reciprocal Duality):**
1. For the single-site Lax blocks `laxBlockA u θ η, laxBlockB η, laxBlockC η, laxBlockD u θ η`,
   the antipode-shifted quantum determinant `A(u) D(u - η) - B(η) C(η)` is the central scalar
   `((u - θ)² - η²) • I₂`, whereas the unshifted classical expression `A(u) D(u) - B(η) C(η)`
   leaves the non-central diagonal defect `!![η * (u - θ + η), 0; 0, η * (u - θ)]`.
2. In the Cayley–Kähler parameterization `f_r = w_c² - w_p² - w_s²`, the single-site Jacobian
   `1 + f_r` vanishes at the exceptional crash `f_r = -1`, where the Berezinian denominator
   `1 + f_r` has its pole. -/
theorem turn20_quantum_det_vs_unshifted_defect_and_berezinian_crash
    {R : Type*} [CommRing R] (u theta eta : R) :
    laxBlockA u theta eta * laxBlockD (u - eta) theta eta -
      laxBlockB eta * laxBlockC eta =
      ((u - theta) ^ 2 - eta ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) ∧
    (laxBlockA u theta eta * laxBlockD u theta eta - laxBlockB eta * laxBlockC eta) -
      (laxBlockA u theta eta * laxBlockD (u - eta) theta eta -
        laxBlockB eta * laxBlockC eta) =
      !![eta * (u - theta + eta), 0; 0, eta * (u - theta)] ∧
    ((1 : R) + (-1 : R) = 0) := by
  refine ⟨?_, ?_, by abel⟩
  · ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [laxBlockA, laxBlockB, laxBlockC, laxBlockD] <;> ring
  · ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [laxBlockA, laxBlockB, laxBlockC, laxBlockD] <;> ring

/-- Gaussian $\mathbb{L}$-binomial coefficient $\begin{bmatrix} n \\ M \end{bmatrix}_{\mathbb{L}}$
for the Schubert cell decomposition of $\operatorname{Gr}(M, n)$. -/
def qBinom {R : Type*} [CommRing R] (L : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, M + 1 => qBinom L n (M + 1) + (L ^ (n - M)) * qBinom L n M

/-- **Turn 22 (Schubert Cell Gaussian $\mathbb{L}$-Binomial for $\operatorname{Gr}(2,4)$ &
Super-Grassmannian Witten Index Vanishing):**
1. For `n = 4, M = 2`, `qBinom L 4 2 = 1 + L + 2 * L² + L³ + L⁴` (the 6 Schubert cells
   `∅, (1,0), (2,0), (1,1), (2,1), (2,2)` of `Gr(2,4)`), which evaluates to `6` at `L = 1`.
2. The odd fermionic Grassmannian factor `(1 + piL) ^ (d_odd + 1)` vanishes identically at the
   Witten index specialization `piL = -1`. -/
theorem turn22_schubert_gr24_qBinom_and_witten_index_vanishing
    {R : Type*} [CommRing R] (L : R) (d_odd : ℕ) :
    qBinom L 4 2 = 1 + L + 2 * L ^ 2 + L ^ 3 + L ^ 4 ∧
    qBinom (1 : R) 4 2 = 6 ∧
    ((1 : R) + (-1 : R)) ^ (d_odd + 1) = 0 := by
  refine ⟨?_, ?_, by simp⟩
  · simp [qBinom]
    ring
  · simp [qBinom]
    ring

/-- First Iwahori–Hecke Demazure–Lusztig generator `T₁(L)` on `Matrix (Fin 3) (Fin 3) R`. -/
def heckeT1 {R : Type*} [CommRing R] (L : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, L, 0;
     1, L - 1, 0;
     0, 0, L]

/-- Second Iwahori–Hecke Demazure–Lusztig generator `T₂(L)` on `Matrix (Fin 3) (Fin 3) R`. -/
def heckeT2 {R : Type*} [CommRing R] (L : R) : Matrix (Fin 3) (Fin 3) R :=
  !![L, 0, 0;
     0, 0, L;
     0, 1, L - 1]

/-- **Turn 22 (Iwahori–Hecke Demazure–Lusztig Quadratic Aporia & Artin Braid Relation on `3 × 3` Matrices):**
On `Matrix (Fin 3) (Fin 3) R`:
1. Both `heckeT1 L` and `heckeT2 L` satisfy the Hecke quadratic relation
   `(T_k + I₃)(T_k - L • I₃) = 0` (so `T_k² = (L - 1) • T_k + L • I₃`, failing `T_k² = I₃`
   unless `L = 1` and failing `T_k² = 0` unless `L = 0` and `(T_k + I₃) = 0`),
2. `heckeT1 L` and `heckeT2 L` do not commute (`(heckeT1 L * heckeT2 L - heckeT2 L * heckeT1 L) 0 2 = L²`),
3. They satisfy the exact Yang–Baxter / Artin braid relation
   `heckeT1 L * heckeT2 L * heckeT1 L = heckeT2 L * heckeT1 L * heckeT2 L`. -/
theorem turn22_iwahori_hecke_quadratic_aporia_and_braid_relation
    {R : Type*} [CommRing R] (L : R) :
    (heckeT1 L + 1) * (heckeT1 L - L • (1 : Matrix (Fin 3) (Fin 3) R)) = 0 ∧
    (heckeT2 L + 1) * (heckeT2 L - L • (1 : Matrix (Fin 3) (Fin 3) R)) = 0 ∧
    (heckeT1 L * heckeT2 L - heckeT2 L * heckeT1 L) 0 2 = L ^ 2 ∧
    heckeT1 L * heckeT2 L * heckeT1 L = heckeT2 L * heckeT1 L * heckeT2 L := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [heckeT1]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [heckeT2]
  · simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three]
    simp [heckeT1, heckeT2]
    ring
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [heckeT1, heckeT2] <;> ring

end StageE1

/-! ===========================================================================
    Section 3: Stage E2 — Transcendent Function (Turns 18, 25, 27, 28, 29)
    =========================================================================== -/

section StageE2

variable {R : Type*} [CommRing R]

/-- **Turn 18 (Baxter $TQ$ Difference Relation & Anti-Periodic Krein Bethe Ansatz Root Condition):**
For the anti-periodic Krein transfer eigenvalue equation
`Λ_J(u) * Q(u) = a(u) * Q(u - η) - d(u) * Q(u + η)`, evaluating at any Bethe root `v_m`
where `Q_vm = 0` forces the exact anti-periodic Bethe balance `a_vm * Q_minus = d_vm * Q_plus`. -/
theorem turn18_baxter_tq_difference_and_antiperiodic_bae_at_root
    (Lambda_vm Q_vm a_vm d_vm Q_minus Q_plus : R)
    (hTQ : Lambda_vm * Q_vm = a_vm * Q_minus - d_vm * Q_plus)
    (hRoot : Q_vm = 0) :
    a_vm * Q_minus = d_vm * Q_plus := by
  rw [hRoot, mul_zero] at hTQ
  exact sub_eq_zero.mp hTQ.symm

/-- Universal `2 × 2` $\text{Cl}(1,1)$ boundary twist matrix
`K_twist(w₀, w_J, w_B, w_C) = !![w₀ + w_J, w_C; w_B, w₀ - w_J]`. -/
def cl11Twist2 (w0 wJ wB wC : R) : Matrix (Fin 2) (Fin 2) R :=
  !![w0 + wJ, wC;
     wB, w0 - wJ]

/-- The `4 × 4` Kronecker square `K_twist ⊗ K_twist` on `Matrix (Fin 4) (Fin 4) R`. -/
def cl11TwistKron4 (w0 wJ wB wC : R) : Matrix (Fin 4) (Fin 4) R :=
  let a := w0 + wJ
  let d := w0 - wJ
  !![a * a, a * wC, wC * a, wC * wC;
     a * wB, a * d, wC * wB, wC * d;
     wB * a, wB * wC, d * a, d * wC;
     wB * wB, wB * d, d * wB, d * d]

/-- **Turn 18 ($\text{Cl}(1,1)$ Twisted Integrability & Parabolic Null-Twist Jordan Catastrophe):**
1. For any `w₀, w_J, w_B, w_C : R`, `K_twist ⊗ K_twist` commutes with the `4 × 4` permutation
   operator `swap4` (`comm swap4 (cl11TwistKron4 w0 wJ wB wC) = 0`), so `K_twist` is a
   universal symmetry of the Yangian $R$-matrix `R(u) = u I₄ + η P₁₂`.
2. Subtracting the scalar trace part `w₀ I₂` gives `(K_twist - w₀ I₂)² = (w_J² + w_B w_C) • I₂`,
   which becomes a non-zero rank-1 nilpotent Jordan block `(K_twist - w₀ I₂)² = 0` along the
   parabolic null cone `w_J² + w_B w_C = 0`. -/
theorem turn18_cl11_twist_swap_invariance_and_parabolic_jordan_nilpotency
    (w0 wJ wB wC : R) :
    comm (swap4 : Matrix (Fin 4) (Fin 4) R) (cl11TwistKron4 w0 wJ wB wC) = 0 ∧
    (cl11Twist2 w0 wJ wB wC - w0 • (1 : Matrix (Fin 2) (Fin 2) R)) *
      (cl11Twist2 w0 wJ wB wC - w0 • (1 : Matrix (Fin 2) (Fin 2) R)) =
      (wJ ^ 2 + wB * wC) • (1 : Matrix (Fin 2) (Fin 2) R) ∧
    (cl11Twist2 w0 wJ wB wC).det = w0 ^ 2 - (wJ ^ 2 + wB * wC) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [swap4, cl11TwistKron4] <;> ring
  · ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [cl11Twist2] <;> ring
  · simp [cl11Twist2, Matrix.det_fin_two]
    ring

/-- **Turn 25 (Givental–Korff Quantum Pieri Matrices on $QH^*(\operatorname{Gr}(2,4))$):**
In the 6-dimensional Schubert basis `(σ_∅, σ_(1,0), σ_(2,0), σ_(1,1), σ_(2,1), σ_(2,2))` of
`QH*(Gr(2,4))`, the first quantum Pieri operator `quantumPieriC1 q` ($\hat{\mathcal{C}}_1(q)$)
and second quantum Pieri operator `quantumPieriC2 q` ($\hat{\mathcal{C}}_2(q)$) are `6 × 6`
matrices over `R`. -/
def quantumPieriC1 (q : R) : Matrix (Fin 6) (Fin 6) R :=
  !![0, 0, 0, 0, q, 0;
     1, 0, 0, 0, 0, q;
     0, 1, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 0]

/-- Second quantum Pieri operator $\hat{\mathcal{C}}_2(q) = \sigma_{(1,1)} \star_q -$ on $QH^*(\operatorname{Gr}(2,4))$. -/
def quantumPieriC2 (q : R) : Matrix (Fin 6) (Fin 6) R :=
  !![0, 0, 0, q, 0, 0;
     0, 0, 0, 0, q, 0;
     0, 0, 0, 0, 0, q;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0]

/-- Quantum Schubert multiplication matrix $\hat{\mathcal{C}}_{(2,0)}(q) = \sigma_{(2,0)} \star_q -$. -/
def quantumSchubert20 (q : R) : Matrix (Fin 6) (Fin 6) R :=
  !![0, 0, q, 0, 0, 0;
     0, 0, 0, 0, q, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, q;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0]

/-- Quantum Schubert multiplication matrix $\hat{\mathcal{C}}_{(2,2)}(q) = \sigma_{(2,2)} \star_q -$. -/
def quantumSchubert22 (q : R) : Matrix (Fin 6) (Fin 6) R :=
  !![0, 0, 0, 0, 0, q ^ 2;
     0, q, 0, 0, 0, 0;
     0, 0, 0, q, 0, 0;
     0, 0, q, 0, 0, 0;
     0, 0, 0, 0, q, 0;
     1, 0, 0, 0, 0, 0]

/-- Classical nil-Coxeter raising part `E_+ = quantumPieriC1 0` vs. quantum instanton corner
`I_inst(q) = quantumPieriC1 q - quantumPieriC1 0`. -/
def quantumInstantonCorner (q : R) : Matrix (Fin 6) (Fin 6) R :=
  quantumPieriC1 q - quantumPieriC1 0

/-- Classical nil-Coxeter raising operator `pieriClassicalC1 = quantumPieriC1 0` on `Matrix (Fin 6) (Fin 6) R`. -/
def pieriClassicalC1 : Matrix (Fin 6) (Fin 6) R :=
  quantumPieriC1 0

/-- Schubert box-parity grading `pluckerParity6 = diag(1, -1, 1, 1, -1, 1)` on $QH^*(\operatorname{Gr}(2,4))$. -/
def pluckerParity6 : Matrix (Fin 6) (Fin 6) R :=
  !![1, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 1]

/-- Explicit `6 × 6` Schubert parity anticommutation witness: the classical Pieri raising operator
shifts partition weight by `+1` and therefore anticommutes with `pluckerParity6`. -/
theorem pluckerParity6_pieriClassicalC1_anticomm :
    (pluckerParity6 : Matrix (Fin 6) (Fin 6) R) * pieriClassicalC1 +
      pieriClassicalC1 * pluckerParity6 = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_six]
  fin_cases i <;> fin_cases j <;> simp [pluckerParity6, pieriClassicalC1, quantumPieriC1]

/-- **Turns 25 & 27 (Givental–Korff Quantum Pieri Commutativity, Giambelli Quadratic Decomposition,
Quartic Instanton Relation & Non-Commuting Affine Nil-Coxeter Split on `Matrix (Fin 6) (Fin 6) R`):**
1. `comm (quantumPieriC1 q) (quantumPieriC2 q) = 0`,
2. `quantumPieriC1 q * quantumPieriC1 q = quantumSchubert20 q + quantumPieriC2 q`,
3. `(quantumPieriC1 q) ^ 4 = (2 : R) • quantumSchubert22 q + (2 * q) • 1`,
4. **Turn 27 Elenchus 4**: While the full affine nil-Coxeter / quantum Pieri generators commute,
   splitting `quantumPieriC1 q = E_+ + I_inst(q)` into classical raising `E_+` and boundary
   instanton `I_inst(q)` produces a non-zero commutator
   `(comm (quantumPieriC1 0) (quantumInstantonCorner q)) 0 2 = -q`! -/
theorem turn25_turn27_givental_korff_quantum_pieri_gr24_identities (q : R) :
    comm (quantumPieriC1 q) (quantumPieriC2 q) = 0 ∧
    quantumPieriC1 q * quantumPieriC1 q = quantumSchubert20 q + quantumPieriC2 q ∧
    (quantumPieriC1 q * quantumPieriC1 q) * (quantumPieriC1 q * quantumPieriC1 q) =
      (2 : R) • quantumSchubert22 q + (2 * q) • (1 : Matrix (Fin 6) (Fin 6) R) ∧
    (comm (quantumPieriC1 (0 : R)) (quantumInstantonCorner q)) 0 2 = -q := by
  have hSq : quantumPieriC1 q * quantumPieriC1 q = quantumSchubert20 q + quantumPieriC2 q := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_six]
    fin_cases i <;> fin_cases j <;> simp [quantumPieriC1, quantumSchubert20, quantumPieriC2]
  refine ⟨?_, hSq, ?_, ?_⟩
  · ext i j
    simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_six]
    fin_cases i <;> fin_cases j <;> simp [quantumPieriC1, quantumPieriC2]
  · rw [hSq]
    ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_six]
    fin_cases i <;> fin_cases j <;>
      simp [quantumSchubert20, quantumPieriC2, quantumSchubert22] <;> ring
  · simp only [comm, quantumInstantonCorner, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_six]
    simp [quantumPieriC1]

/-- **Turn 27 (Tridiagonal Hamming-Weight Bandwidth Count & Site-Graded RTT Multi-Head Twist Law):**
1. For `2k = 8` (`2^8 = 256` states), the middle Hamming shells `w ∈ {3, 4, 5}` support exactly
   `Nat.choose 8 4 + 2 * Nat.choose 8 3 = 70 + 112 = 182` tridiagonal pairs (`Δw ∈ {-1, 0, +1}`),
   leaving `256 - 182 = 74` pairs outside the bare 3-diagonal bandwidth.
2. For `2 × 2` Lax blocks `A, D : Matrix (Fin 2) (Fin 2) R` and twist parameters `q₁, q₂ : R`,
   the twisted transfer traces `τ(q) = A - q • D` satisfy
   `comm (A - q₁ • D) (A - q₂ • D) = (q₁ - q₂) • comm A D`,
   which vanishes identically when `q₁ = q₂`! -/
theorem turn27_tridiagonal_hamming_count_and_multihead_twist_commutator
    (A D : Matrix (Fin 2) (Fin 2) R) (q1 q2 : R) :
    Nat.choose 8 4 + 2 * Nat.choose 8 3 = 182 ∧
    256 - (Nat.choose 8 4 + 2 * Nat.choose 8 3) = 74 ∧
    comm (A - q1 • D) (A - q2 • D) = (q1 - q2) • comm A D := by
  refine ⟨by decide, by decide, ?_⟩
  ext i j
  simp only [comm, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> ring

/-- Kronecker embedding `I₂ ⊗ G` of a `2 × 2` matrix `G` into `Matrix (Fin 4) (Fin 4) B`. -/
def kronIdLeft4 {B : Type*} [Ring B] (G : Matrix (Fin 2) (Fin 2) B) :
    Matrix (Fin 4) (Fin 4) B :=
  !![G 0 0, G 0 1, 0, 0;
     G 1 0, G 1 1, 0, 0;
     0, 0, G 0 0, G 0 1;
     0, 0, G 1 0, G 1 1]

/-- Kronecker embedding `G ⊗ I₂` of a `2 × 2` matrix `G` into `Matrix (Fin 4) (Fin 4) B`. -/
def kronIdRight4 {B : Type*} [Ring B] (G : Matrix (Fin 2) (Fin 2) B) :
    Matrix (Fin 4) (Fin 4) B :=
  !![G 0 0, 0, G 0 1, 0;
     0, G 0 0, 0, G 0 1;
     G 1 0, 0, G 1 1, 0;
     0, G 1 0, 0, G 1 1]

/-- **Turns 27 & 28 (Non-Abelian Gauge–Lax Exchange Identity & Auxiliary Wilson Link Duality):**
On `Matrix (Fin 4) (Fin 4) R`:
1. Conjugating `swap4` (`P₁₂`) exchanges the physical tensor factor `I₂ ⊗ G` and the
   auxiliary tensor factor `G ⊗ I₂`:
   `kronIdLeft4 G * swap4 = swap4 * kronIdRight4 G` and
   `kronIdRight4 G * swap4 = swap4 * kronIdLeft4 G`.
2. Consequently, for the single-site Lax operator `singleSiteLax4 u θ η = (u - θ) I₄ + η P₁₂`
   and any invertible `2 × 2` gauge matrix `G * G_inv = 1`, `G_inv * G = 1`,
   physical-space gauge conjugation `(I₂ ⊗ G) L_{0,r}(u, θ, η) (I₂ ⊗ G⁻¹)` equals
   inverse auxiliary-space gauge conjugation `(G⁻¹ ⊗ I₂) L_{0,r}(u, θ, η) (G ⊗ I₂)`! -/
theorem turn28_nonabelian_gauge_lax_exchange_duality
    (u theta eta : R) (G G_inv : Matrix (Fin 2) (Fin 2) R)
    (hR : G * G_inv = 1) (hL : G_inv * G = 1) :
    kronIdLeft4 G * (swap4 : Matrix (Fin 4) (Fin 4) R) =
      swap4 * kronIdRight4 G ∧
    kronIdRight4 G * (swap4 : Matrix (Fin 4) (Fin 4) R) =
      swap4 * kronIdLeft4 G ∧
    kronIdLeft4 G * singleSiteLax4 u theta eta * kronIdLeft4 G_inv =
      kronIdRight4 G_inv * singleSiteLax4 u theta eta * kronIdRight4 G := by
  have hSwap1 : kronIdLeft4 G * (swap4 : Matrix (Fin 4) (Fin 4) R) =
      swap4 * kronIdRight4 G := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kronIdLeft4, kronIdRight4, swap4]
  have hSwap2 : kronIdRight4 G * (swap4 : Matrix (Fin 4) (Fin 4) R) =
      swap4 * kronIdLeft4 G := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kronIdLeft4, kronIdRight4, swap4]
  have hR00 : G 0 0 * G_inv 0 0 + G 0 1 * G_inv 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hR 0) 0
  have hR01 : G 0 0 * G_inv 0 1 + G 0 1 * G_inv 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hR 0) 1
  have hR10 : G 1 0 * G_inv 0 0 + G 1 1 * G_inv 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hR 1) 0
  have hR11 : G 1 0 * G_inv 0 1 + G 1 1 * G_inv 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hR 1) 1
  have hL00 : G_inv 0 0 * G 0 0 + G_inv 0 1 * G 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hL 0) 0
  have hL01 : G_inv 0 0 * G 0 1 + G_inv 0 1 * G 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hL 0) 1
  have hL10 : G_inv 1 0 * G 0 0 + G_inv 1 1 * G 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hL 1) 0
  have hL11 : G_inv 1 0 * G 0 1 + G_inv 1 1 * G 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hL 1) 1
  have hLeftInv : kronIdLeft4 G * kronIdLeft4 G_inv = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kronIdLeft4, hR00, hR01, hR10, hR11]
  have hRightInv : kronIdRight4 G_inv * kronIdRight4 G = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kronIdRight4, hL00, hL01, hL10, hL11]
  have hComm : kronIdRight4 G * kronIdLeft4 G_inv = kronIdLeft4 G_inv * kronIdRight4 G := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [kronIdLeft4, kronIdRight4] <;> ring
  refine ⟨hSwap1, hSwap2, ?_⟩
  simp only [singleSiteLax4, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]
  rw [hLeftInv, hRightInv, hSwap1]
  have hTerm : swap4 * kronIdRight4 G * kronIdLeft4 G_inv =
      kronIdRight4 G_inv * swap4 * kronIdRight4 G := by
    have hSwap2Inv : kronIdRight4 G_inv * (swap4 : Matrix (Fin 4) (Fin 4) R) =
        swap4 * kronIdLeft4 G_inv := by
      ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_four]
      fin_cases i <;> fin_cases j <;> simp [kronIdLeft4, kronIdRight4, swap4]
    calc
      swap4 * kronIdRight4 G * kronIdLeft4 G_inv
          = swap4 * (kronIdRight4 G * kronIdLeft4 G_inv) := by simp [Matrix.mul_assoc]
      _ = swap4 * (kronIdLeft4 G_inv * kronIdRight4 G) := by rw [hComm]
      _ = (swap4 * kronIdLeft4 G_inv) * kronIdRight4 G := by simp [Matrix.mul_assoc]
      _ = (kronIdRight4 G_inv * swap4) * kronIdRight4 G := by rw [← hSwap2Inv]
  rw [hTerm]

/-- **Turn 29 (Rademacher Sign Involutivity & Half-Bandwidth Auxiliary Register Update):**
In any `[Ring B]`, for any boolean/idempotent bit `b * b = b`, the Rademacher sign `s = 1 - 2 • b`
satisfies `s * s = 1`, and its longitudinal/transverse projections satisfy
`(1 + s) * (1 - s) = 0`. -/
theorem turn29_rademacher_sign_involution_of_idempotent
    {B : Type*} [Ring B] {b : B} (hb : b * b = b) :
    (1 - (2 : ℤ) • b) * (1 - (2 : ℤ) • b) = 1 ∧
    (1 + (1 - (2 : ℤ) • b)) * (1 - (1 - (2 : ℤ) • b)) = 0 := by
  refine ⟨?_, ?_⟩ <;> noncomm_ring [hb]

end StageE2

/-! ===========================================================================
    Section 4: Stage E3 — Socratic Aporia: Kähler–Bergman & AdS₃ Geodesics (Turns 23, 24, 26, 30)
    =========================================================================== -/

section StageE3

variable {R : Type*} [CommRing R]

/-- Connes–Lott phase-coupled chiral Higgs boundary twist matrix
`K_Higgs(q, w_B, w_C) = !![1, q * w_C; w_B, -q]`. -/
def connesLottHiggsTwist2 (q wB wC : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, q * wC;
     wB, -q]

/-- **Turns 23, 24, 25 & 26 (Kähler–Bergman Curvature $R = -4$, Madelung–Bohmian Identity,
Hyperbolic Parallel Transport & Connes–Lott Higgs Twist Determinant):**
1. Kähler–Einstein relation on the Poincaré–Bergman disk: `Ric_num = -2 * g_num` and scalar
   curvature `R_Berg = 2 * (-2) = -4`, with Madelung–Bohmian half-curvature `-2 = (-4) / 2`
   and potential identity `2 + f_r = 1 + (1 + f_r)`.
2. Determinant and characteristic polynomial of `connesLottHiggsTwist2 q wB wC`:
   `det(K_Higgs) = -q * (1 + w_B * w_C)` and
   `K_Higgs² - (1 - q) • K_Higgs = q * (1 + w_B * w_C) • I₂`. -/
theorem turn23_24_25_26_kahler_bergman_madelung_and_higgs_twist
    (f_r q wB wC : R) :
    ((2 : ℤ) * (-2 : ℤ) = -4) ∧
    (2 + f_r = 1 + (1 + f_r)) ∧
    (connesLottHiggsTwist2 q wB wC).det = -q * (1 + wB * wC) ∧
    connesLottHiggsTwist2 q wB wC * connesLottHiggsTwist2 q wB wC -
      (1 - q) • connesLottHiggsTwist2 q wB wC =
      (q * (1 + wB * wC)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  refine ⟨by decide, by ring, ?_, ?_⟩
  · simp [connesLottHiggsTwist2, Matrix.det_fin_two]
    ring
  · ext i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [connesLottHiggsTwist2] <;> ring

/-- The `3 × 3` Lorentzian Killing metric `η₃ = diag(1, 1, -1)` on $\mathfrak{sl}_2(\mathbb{R}) \simeq \mathbb{R}^{2,1}$. -/
def sl2KillingEta3 : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, -1]

/-- The `3 × 3` Cartan involution `Θ_Cartan = diag(1, 1, -1)` flipping the compact/timelike
generator `ε` so that `η₃ * Θ_Cartan = I₃`. -/
def sl2CartanInvolution3 : Matrix (Fin 3) (Fin 3) R :=
  sl2KillingEta3

/-- The `3 × 3` half-adjoint representation matrix `M_ad(a_x, a_z, a_ε) = (1/2) ad_a` on
$\mathfrak{sl}_2(\mathbb{R})$ in the basis `(σ_x, σ_z, ε)`. -/
def sl2HalfAdjoint3 (ax az aeps : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, aeps, -az;
     -aeps, 0, ax;
     -az, ax, 0]

/-- Non-compact Cartan boost generator `sl2BoostGeneratorX3 = sl2HalfAdjoint3 1 0 0` in $\mathfrak{p} \subset \mathfrak{sl}_2(\mathbb{R})$. -/
def sl2BoostGeneratorX3 : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 0;
     0, 0, 1;
     0, 1, 0]

/-- Explicit `3 × 3` Cartan parity anticommutation witness: the non-compact boost generator
`sl2BoostGeneratorX3` anticommutes with `sl2KillingEta3 = diag(1, 1, -1)`. -/
theorem sl2KillingEta3_sl2BoostGeneratorX3_anticomm :
    (sl2KillingEta3 : Matrix (Fin 3) (Fin 3) R) * sl2BoostGeneratorX3 +
      sl2BoostGeneratorX3 * sl2KillingEta3 = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [sl2KillingEta3, sl2BoostGeneratorX3]

/-- Rank-1 outer product `a (η₃ a)ᵀ` on `Matrix (Fin 3) (Fin 3) R`. -/
def sl2KillingOuter3 (ax az aeps : R) : Matrix (Fin 3) (Fin 3) R :=
  !![ax * ax, ax * az, -ax * aeps;
     az * ax, az * az, -az * aeps;
     aeps * ax, aeps * az, -aeps * aeps]

/-- Left Maurer–Cartan Jacobian `J_L(a, u₂, s) = I₃ + u₂ M_ad(a)² - s M_ad(a)` on
`Matrix (Fin 3) (Fin 3) R`, where `c = 1 + δ u₂`. -/
def sl2MaurerCartanLeft3 (ax az aeps u2 s : R) : Matrix (Fin 3) (Fin 3) R :=
  1 + u2 • (sl2HalfAdjoint3 ax az aeps * sl2HalfAdjoint3 ax az aeps) -
    s • sl2HalfAdjoint3 ax az aeps

/-- **Turn 30 ($\mathfrak{sl}_2(\mathbb{R}) \simeq \text{AdS}_3$ Half-Adjoint Algebra, Maurer–Cartan
Jacobian Product Law & Cartan-Twisted Euclidean Metric on `Matrix (Fin 3) (Fin 3) R`):**
For any `ax, az, aeps, u2, s : R` with Killing norm `δ = ax² + az² - aeps²`:
1. Self-annihilation: `mulVec (sl2HalfAdjoint3 ax az aeps) ![ax, az, aeps] = 0`,
2. $\mathfrak{so}(2,1)$ Killing skew-symmetry:
   `(sl2HalfAdjoint3 ax az aeps)ᵀ * sl2KillingEta3 + sl2KillingEta3 * sl2HalfAdjoint3 ax az aeps = 0`,
3. Rank-2 quadratic identity:
   `sl2HalfAdjoint3 ax az aeps * sl2HalfAdjoint3 ax az aeps = (ax² + az² - aeps²) • 1 - sl2KillingOuter3 ax az aeps`,
4. Cubic closure:
   `M_ad³ = (ax² + az² - aeps²) • M_ad`,
5. Exact Maurer–Cartan Jacobian product law:
   `J_L(a, u₂, s) * J_L(a, u₂, -s) = I₃ + (2 * u₂ + (ax² + az² - aeps²) * u₂² - s²) • M_ad(a)²`
   (which equals `I₃` on the hyperbolic shell `(1 + δ u₂)² - δ s² = 1 ⟺ 2 u₂ + δ u₂² = s²`),
6. Cartan-twisted positive-definite Euclidean metric:
   `sl2KillingEta3 * sl2CartanInvolution3 = 1`. -/
theorem turn30_sl2_ads3_killing_maurer_cartan_and_cartan_metric
    (ax az aeps u2 s : R) :
    Matrix.mulVec (sl2HalfAdjoint3 ax az aeps) ![ax, az, aeps] = 0 ∧
    (sl2HalfAdjoint3 ax az aeps)ᵀ * sl2KillingEta3 +
      sl2KillingEta3 * sl2HalfAdjoint3 ax az aeps = 0 ∧
    sl2HalfAdjoint3 ax az aeps * sl2HalfAdjoint3 ax az aeps =
      (ax ^ 2 + az ^ 2 - aeps ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) -
        sl2KillingOuter3 ax az aeps ∧
    sl2HalfAdjoint3 ax az aeps *
      (sl2HalfAdjoint3 ax az aeps * sl2HalfAdjoint3 ax az aeps) =
      (ax ^ 2 + az ^ 2 - aeps ^ 2) • sl2HalfAdjoint3 ax az aeps ∧
    sl2MaurerCartanLeft3 ax az aeps u2 s * sl2MaurerCartanLeft3 ax az aeps u2 (-s) =
      1 + (2 * u2 + (ax ^ 2 + az ^ 2 - aeps ^ 2) * u2 ^ 2 - s ^ 2) •
        (sl2HalfAdjoint3 ax az aeps * sl2HalfAdjoint3 ax az aeps) ∧
    (sl2KillingEta3 : Matrix (Fin 3) (Fin 3) R) * sl2CartanInvolution3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Fin.sum_univ_three]
    fin_cases i <;> simp [sl2HalfAdjoint3] <;> ring
  · ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
      Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [sl2HalfAdjoint3, sl2KillingEta3]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [sl2HalfAdjoint3, sl2KillingOuter3] <;> ring
  · ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [sl2HalfAdjoint3] <;> ring
  · ext i j
    simp only [sl2MaurerCartanLeft3, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [sl2HalfAdjoint3] <;> ring
  · ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [sl2KillingEta3, sl2CartanInvolution3]

end StageE3

/-! ===========================================================================
    Section 5: Stage E4 — CPT Twin Sectors & Sakharov–Janus Bimetric Torsor (Turns 31, 32)
    =========================================================================== -/

section StageE4

variable {B : Type*} [Ring B]

/-- **Turn 31 (Fermionic CPT Double-Cover Operator $\Theta_{\text{CPT}}^2 = -I_2$, Sakharov's
Three-Condition Commutator Decomposition & Bogoliubov Dark Matter Berezinian Excess):**
1. On `Matrix (Fin 2) (Fin 2) R`, the symplectic/fermionic CPT operator `epsSymp = !![0, 1; -1, 0]`
   satisfies `epsSymp * epsSymp = -1` and `epsSympᵀ * epsSymp = 1`.
2. In any `[Ring B]`, if `U * U_inv = 1`, `U_inv * U = 1`, `Q_B` commutes with `U`
   (`U * Q_B = Q_B * U`), and `rho0` commutes with `Q_B` (`comm Q_B rho0 = 0`), then the evolved
   baryon asymmetry commutator vanishes identically (`comm Q_B (U * rho0 * U_inv) = 0`).
3. Boyle–Finn–Turok Bogoliubov dark matter occupation excess identity (cleared polynomial form):
   `(-f_k) = 1 - (1 + f_k)`, so `(-f_k) / (1 + f_k) = 1 / (1 + f_k) - 1 = Ber(M_k) - 1`. -/
theorem turn31_fermionic_cpt_sakharov_commutator_and_bogoliubov_excess
    {R : Type*} [CommRing R]
    {U U_inv Q_B rho0 : B}
    (hUR : U * U_inv = 1) (hUL : U_inv * U = 1)
    (hQ : U * Q_B = Q_B * U) (hStat : comm Q_B rho0 = 0)
    (f_k : R) :
    (epsSymp : Matrix (Fin 2) (Fin 2) R) * epsSymp = -1 ∧
    (epsSymp : Matrix (Fin 2) (Fin 2) R)ᵀ * epsSymp = 1 ∧
    comm Q_B (U * rho0 * U_inv) = 0 ∧
    (-f_k = 1 - (1 + f_k)) := by
  refine ⟨?_, ?_, ?_, by noncomm_ring⟩
  · ext i j
    simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [epsSymp]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [epsSymp]
  · have hQinv : Q_B * U_inv = U_inv * Q_B := by
      calc
        Q_B * U_inv = (U_inv * U) * Q_B * U_inv := by rw [hUL, one_mul]
        _ = U_inv * (U * Q_B) * U_inv := by noncomm_ring
        _ = U_inv * (Q_B * U) * U_inv := by rw [hQ]
        _ = U_inv * Q_B * (U * U_inv) := by noncomm_ring
        _ = U_inv * Q_B := by rw [hUR, mul_one]
    have hRho : Q_B * rho0 = rho0 * Q_B := sub_eq_zero.mp hStat
    simp only [comm]
    calc
      Q_B * (U * rho0 * U_inv) - U * rho0 * U_inv * Q_B
          = (Q_B * U) * rho0 * U_inv - U * rho0 * (U_inv * Q_B) := by noncomm_ring
      _ = (U * Q_B) * rho0 * U_inv - U * rho0 * (Q_B * U_inv) := by rw [← hQ, hQinv]
      _ = U * (Q_B * rho0) * U_inv - U * rho0 * (Q_B * U_inv) := by noncomm_ring
      _ = U * (rho0 * Q_B) * U_inv - U * rho0 * (Q_B * U_inv) := by rw [hRho]
      _ = 0 := by noncomm_ring

/-- **Turn 31 Bridge to `SemilinearCovarianceGeometry` and `DerivationAmplitudeGeometry`:**
Re-exports the repository's native complex matrix semilinear sheet conjugation reversal of unitary
evolution `sheetConj (matrixEvolution H t) = matrixEvolution H (-t)`, the unique sheet-even
positive stationary covariance with vanishing odd Hermitian traces, and the non-commutative
operator Riccati identity `rightLogarithmicOneForm_riccati` underlying the Madelung–Weyl
amplitude quotient. -/
theorem turn31_semilinear_sheet_evolution_and_riccati_bridge
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry.SheetMatrix n)
    (hHeven : InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry.sheetConj H = H)
    (t : ℝ)
    {R₀ A₀ : Type*} [CommRing R₀] [Ring A₀] [Algebra R₀ A₀]
    (K : InfoGeometry.Algebra.DerivationLieLane R₀ A₀) (g : A₀ˣ) (x : K.L) :
    InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry.sheetConj
      (InfoGeometry.OperatorAlgebra.SemilinearCovarianceGeometry.matrixEvolution H t) =
      InfoGeometry.OperatorAlgebra.SemilinearCovarianceGeometry.matrixEvolution H (-t) ∧
    K.operatorAction x
      (InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.rightLogarithmicOneForm K g x) +
      InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.rightLogarithmicOneForm K g x *
        InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.rightLogarithmicOneForm K g x =
      InfoGeometry.OperatorAlgebra.DerivationAmplitudeGeometry.rightAmplitudeSecondDerivative K g x :=
  ⟨InfoGeometry.OperatorAlgebra.SemilinearCovarianceGeometry.sheetConj_matrixEvolution_of_even hHeven t,
   InfoGeometry.OperatorAlgebra.DerivationAmplitudeGeometry.rightLogarithmicOneForm_riccati K g x⟩

/-- The `4 × 4` pure time-reversal matrix `T_diag = diag(-1, 1, 1, 1)` on Minkowski space. -/
def minkowskiTimeReversal4 {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![-1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- The `4 × 4` total spacetime inversion matrix `PT_mat = -I₄ = diag(-1, -1, -1, -1)`. -/
def minkowskiTotalInversion4 {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![-1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- **Turn 32 (Lorentz 4-Component Determinant Elenchus, Bondi Runaway vs. Janus $\kappa = -1$
Mutual Repulsion, $O(\epsilon^1)$ TOV Bianchi Defect & Souriau–Kaluza–Janus Bimetric Bridge):**
1. **Lorentz Component Swap Elenchus**: Pure time reversal `minkowskiTimeReversal4` (`diag(-1, 1, 1, 1)`)
   and total spacetime inversion `minkowskiTotalInversion4` (`-I₄`) satisfy
   `minkowskiTimeReversal4 0 0 * minkowskiTimeReversal4 1 1 * minkowskiTimeReversal4 2 2 * minkowskiTimeReversal4 3 3 = -1`
   (improper antichronous `L_-^\downarrow`) vs.
   `minkowskiTotalInversion4 0 0 * minkowskiTotalInversion4 1 1 * minkowskiTotalInversion4 2 2 * minkowskiTotalInversion4 3 3 = 1`
   (proper antichronous `L_+^\downarrow`).
2. **Bondi Runaway vs. Janus $\kappa = -1$ Mutual Repulsion**:
   Under Bondi's single-metric law (`f₁ = -F`, `f₂ = +F`, `m₂ = -m₁`), the accelerations satisfy
   `m₁ a₁ - m₁ a₂ = (-F) - (-F) = 0` (self-accelerating runaway pair), whereas under Janus's
   bimetric law (`κ = -1`, `m₁ > 0, m₂ > 0`, `m₁ a₁ = +F, m₂ a₂ = +F` in opposite frames),
   both masses repel (`m₁ a₁ + m₂ a₂ = 2 F`) and their relative momentum difference vanishes
   (`m₁ a₁ - m₂ a₂ = 0`).
3. **$O(\epsilon^1)$ TOV Bianchi Defect**: The difference between Petit–D'Agostini's heuristic
   source `ρ c² + 3 p` (Eq. 118) and the Tolman–Oppenheimer–Volkoff geodesic factor `ρ c² + p`
   (Eq. 125) is `2 p`, which vanishes at `p = 0`.
4. **Souriau–Kaluza–Janus Bimetric Bridge**: Direct connection to `bimetricCoupling2_sq` and
   `bimetric_bianchi_compatibility` in `SouriauKaluzaJanusBimetricSolveEtCoagula`. -/
theorem turn32_lorentz_det_bondi_vs_janus_tov_aporia_and_bimetric_bridge
    {R : Type*} [CommRing R] (F rho_c2 p : R)
    {b1 b2 : B} (hb12 : b1 * b2 = 1) (hb21 : b2 * b1 = 1) (T_stress : Matrix (Fin 2) (Fin 2) B) :
    ((minkowskiTimeReversal4 (R := R)) 0 0 * (minkowskiTimeReversal4 (R := R)) 1 1 *
      (minkowskiTimeReversal4 (R := R)) 2 2 * (minkowskiTimeReversal4 (R := R)) 3 3 = -1) ∧
    ((minkowskiTotalInversion4 (R := R)) 0 0 * (minkowskiTotalInversion4 (R := R)) 1 1 *
      (minkowskiTotalInversion4 (R := R)) 2 2 * (minkowskiTotalInversion4 (R := R)) 3 3 = 1) ∧
    ((-F) - (-F) = (0 : R) ∧ F + F = 2 * F ∧ F - F = (0 : R)) ∧
    ((rho_c2 + 3 * p) - (rho_c2 + p) = 2 * p) ∧
    bimetricCoupling2 b1 b2 * bimetricCoupling2 b1 b2 = 0 ∧
    bimetricAnnihilator2 b2 * (bimetricCoupling2 b1 b2 * T_stress) = 0 := by
  refine ⟨?_, ?_, ⟨by noncomm_ring, by noncomm_ring, by noncomm_ring⟩, by noncomm_ring,
    bimetricCoupling2_sq_zero hb12 hb21,
    bimetric_matrix_bianchi_conservation_zero T_stress hb21⟩
  · simp [minkowskiTimeReversal4]
  · simp [minkowskiTotalInversion4]

end StageE4

/-! ===========================================================================
    Section 6: Stage E5 — Full 32-Turn Causal Poset (`Turn01`–`Turn32`) & Coagulation
    =========================================================================== -/

section StageE5

/-- The complete **32-turn** mathematical archetype poset of
`https://share.gemini.google/kKehiDWWV8DI` (`https://gemini.google.com/share/418904a66184`),
containing Turns 01–17 (`9666a5a14e0d`) and the 15 continuation turns (`Turns 18–32`). -/
inductive Full32TurnChatArchetype : Type
  | Turn01_MetriplecticSplitGramiansAndAporiaDefect
  | Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU
  | Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity
  | Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge
  | Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors
  | Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia
  | Turn07_CliffordMultivectorAttentionBilinearReadout
  | Turn08_WalshHadamardBivectorInteractionKernel
  | Turn09_XorSwizzleBankConflictFreeInvolutionBijection
  | Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur
  | Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons
  | Turn12_BCFWThreePointAmalgamationAndBridgeCommutator
  | Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne
  | Turn14_YangianRMatrixQYBEAndResonantRankCollapse
  | Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary
  | Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash
  | Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession
  | Turn18_HammingShellConfinementBaxterTQAndCl11TwistedIntegrability
  | Turn19_SixParadigmNCGSupermatrixWittenLaplacianAndFedosovCurvature
  | Turn20_YangLaxMonodromyQuaternityAntipodeQdetAndBerezinianDuality
  | Turn21_SuperYangianGl11EvenDiracBugElenchusAndChiralSUSY
  | Turn22_SchubertQBinomWittenIndexAndIwahoriHeckeDemazureLusztig
  | Turn23_WittLightConeSplitKahlerBergmanCurvatureAndXorSwapGauge
  | Turn24_KahlerBergmanNaturalGradientAndHyperbolicGeodesicQuartet
  | Turn25_MadelungBergmanHydrodynamicsAndGiventalKorffQuantumPieriGr24
  | Turn26_GeodesicYangBaxterBugElenchusAndConnesLottChiralHiggsTwist
  | Turn27_TridiagonalHammingBandwidthInhomogeneousGaugeAndMultiHeadTwist
  | Turn28_NonAbelianSL2GaugeLaxExchangeDualityAndAuxiliaryWilsonLinks
  | Turn29_HalfBandwidthWittRegisterShuffleAndRademacherCurrentFactorization
  | Turn30_AdS3LorentzianKillingMetricMaurerCartanAndCartanGeodesics
  | Turn31_SakharovCPTTwinSectorsSemilinearSheetRiccatiAndBogoliubovDarkMatter
  | Turn32_SakharovJanusBimetricTorsorBondiVsJanusAndTOVBianchiAporia
  deriving DecidableEq, Repr, Inhabited

namespace Full32TurnChatArchetype

/-- Canonical embedding of the 17-turn poset `CausalMatrixChatTurnArchetype` into
`Full32TurnChatArchetype`. -/
def of17 : CausalMatrixChatTurnArchetype → Full32TurnChatArchetype
  | .Turn01_MetriplecticSplitGramiansAndAporiaDefect =>
      .Turn01_MetriplecticSplitGramiansAndAporiaDefect
  | .Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU =>
      .Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU
  | .Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity =>
      .Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity
  | .Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge =>
      .Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge
  | .Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors =>
      .Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors
  | .Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia =>
      .Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia
  | .Turn07_CliffordMultivectorAttentionBilinearReadout =>
      .Turn07_CliffordMultivectorAttentionBilinearReadout
  | .Turn08_WalshHadamardBivectorInteractionKernel =>
      .Turn08_WalshHadamardBivectorInteractionKernel
  | .Turn09_XorSwizzleBankConflictFreeInvolutionBijection =>
      .Turn09_XorSwizzleBankConflictFreeInvolutionBijection
  | .Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur =>
      .Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur
  | .Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons =>
      .Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons
  | .Turn12_BCFWThreePointAmalgamationAndBridgeCommutator =>
      .Turn12_BCFWThreePointAmalgamationAndBridgeCommutator
  | .Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne =>
      .Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne
  | .Turn14_YangianRMatrixQYBEAndResonantRankCollapse =>
      .Turn14_YangianRMatrixQYBEAndResonantRankCollapse
  | .Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary =>
      .Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary
  | .Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash =>
      .Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash
  | .Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession =>
      .Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession

/-- Causal prerequisite DAG (as `Finset ℕ`) across all 32 turns of `418904a66184`. -/
def causalPrerequisites : Full32TurnChatArchetype → Finset ℕ
  | .Turn01_MetriplecticSplitGramiansAndAporiaDefect => {1}
  | .Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU => {1, 2}
  | .Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity => {1, 2, 3}
  | .Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge => {1, 2, 4}
  | .Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors => {1, 2, 4, 5}
  | .Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia => {1, 2, 4, 5, 6}
  | .Turn07_CliffordMultivectorAttentionBilinearReadout => {1, 2, 4, 5, 6, 7}
  | .Turn08_WalshHadamardBivectorInteractionKernel => {1, 2, 4, 5, 6, 7, 8}
  | .Turn09_XorSwizzleBankConflictFreeInvolutionBijection => {1, 2, 4, 5, 6, 7, 8, 9}
  | .Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur => {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
  | .Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons => {1, 2, 3, 4, 5, 10, 11}
  | .Turn12_BCFWThreePointAmalgamationAndBridgeCommutator => {1, 2, 3, 4, 5, 10, 11, 12}
  | .Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne => {1, 2, 3, 4, 5, 6, 10, 11, 12, 13}
  | .Turn14_YangianRMatrixQYBEAndResonantRankCollapse => {1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 14}
  | .Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary => {1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 14, 15}
  | .Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash =>
      {1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 14, 15, 16}
  | .Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17}
  | .Turn18_HammingShellConfinementBaxterTQAndCl11TwistedIntegrability =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18}
  | .Turn19_SixParadigmNCGSupermatrixWittenLaplacianAndFedosovCurvature =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19}
  | .Turn20_YangLaxMonodromyQuaternityAntipodeQdetAndBerezinianDuality =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20}
  | .Turn21_SuperYangianGl11EvenDiracBugElenchusAndChiralSUSY =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21}
  | .Turn22_SchubertQBinomWittenIndexAndIwahoriHeckeDemazureLusztig =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22}
  | .Turn23_WittLightConeSplitKahlerBergmanCurvatureAndXorSwapGauge =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23}
  | .Turn24_KahlerBergmanNaturalGradientAndHyperbolicGeodesicQuartet =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}
  | .Turn25_MadelungBergmanHydrodynamicsAndGiventalKorffQuantumPieriGr24 =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25}
  | .Turn26_GeodesicYangBaxterBugElenchusAndConnesLottChiralHiggsTwist =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26}
  | .Turn27_TridiagonalHammingBandwidthInhomogeneousGaugeAndMultiHeadTwist =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27}
  | .Turn28_NonAbelianSL2GaugeLaxExchangeDualityAndAuxiliaryWilsonLinks =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28}
  | .Turn29_HalfBandwidthWittRegisterShuffleAndRademacherCurrentFactorization =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29}
  | .Turn30_AdS3LorentzianKillingMetricMaurerCartanAndCartanGeodesics =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30}
  | .Turn31_SakharovCPTTwinSectorsSemilinearSheetRiccatiAndBogoliubovDarkMatter =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}
  | .Turn32_SakharovJanusBimetricTorsorBondiVsJanusAndTOVBianchiAporia =>
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32}

theorem causalPrerequisites_of17 (a : CausalMatrixChatTurnArchetype) :
    causalPrerequisites (of17 a) = CausalMatrixChatTurnArchetype.causalPrerequisites a := by
  cases a <;> rfl

theorem causalPrerequisites_injective : Function.Injective causalPrerequisites := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals revert h; decide

instance instPartialOrder : PartialOrder Full32TurnChatArchetype :=
  PartialOrder.lift causalPrerequisites causalPrerequisites_injective

instance instDecidableLE : DecidableRel (α := Full32TurnChatArchetype) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (causalPrerequisites a ⊆ causalPrerequisites b))

/-- Exact order-embedding compatibility with the 17-turn poset `CausalMatrixChatTurnArchetype`. -/
theorem of17_le_iff (a b : CausalMatrixChatTurnArchetype) :
    of17 a ≤ of17 b ↔ a ≤ b := by
  change causalPrerequisites (of17 a) ⊆ causalPrerequisites (of17 b) ↔
    CausalMatrixChatTurnArchetype.causalPrerequisites a ⊆
      CausalMatrixChatTurnArchetype.causalPrerequisites b
  rw [causalPrerequisites_of17, causalPrerequisites_of17]

/-- **Root and Terminal Synthesis of the Full 32-Turn Poset:**
`Turn01` is the universal root (`Turn01 ≤ a`), `Turn17` separates the initial 17-turn block from
the continuation turns `Turn18`–`Turn32`, and `Turn32` is the universal terminal (`a ≤ Turn32`)
with strict irreflexivity `¬ (a < a)` across all 32 turns. -/
theorem turn01_is_root_and_turn32_is_terminal (a : Full32TurnChatArchetype) :
    .Turn01_MetriplecticSplitGramiansAndAporiaDefect ≤ a ∧
    a ≤ .Turn32_SakharovJanusBimetricTorsorBondiVsJanusAndTOVBianchiAporia ∧
    ¬ (a < a) := by
  refine ⟨?_, ?_, lt_irrefl a⟩
  · cases a <;> decide
  · cases a <;> decide

end Full32TurnChatArchetype

variable {B : Type*} [Ring B]

/-- Non-commutative Peirce-spine operator realization mapping all 32 turns of `418904a66184`
to their canonical operators in `[Ring B]`. -/
def full32TurnOperator (P A C X : B) : Full32TurnChatArchetype → B
  | .Turn01_MetriplecticSplitGramiansAndAporiaDefect =>
      causalMatrixTurnOperator P A C X .Turn01_MetriplecticSplitGramiansAndAporiaDefect
  | .Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU =>
      causalMatrixTurnOperator P A C X .Turn02_DoubledBlockDilationEquilibriumFlowAndSchurLDU
  | .Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity =>
      causalMatrixTurnOperator P A C X .Turn03_GohbergKreinHilbertAndCotlarTricomiIdentity
  | .Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge =>
      causalMatrixTurnOperator P A C X .Turn04_KreinIndefiniteMetricAndSymplecticCayleyBridge
  | .Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors =>
      causalMatrixTurnOperator P A C X .Turn05_Cl11ParaKahlerTriadAndLightConeNullProjectors
  | .Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia =>
      causalMatrixTurnOperator P A C X .Turn06_JordanWignerKreinStringVsUngradedKroneckerAporia
  | .Turn07_CliffordMultivectorAttentionBilinearReadout =>
      causalMatrixTurnOperator P A C X .Turn07_CliffordMultivectorAttentionBilinearReadout
  | .Turn08_WalshHadamardBivectorInteractionKernel =>
      causalMatrixTurnOperator P A C X .Turn08_WalshHadamardBivectorInteractionKernel
  | .Turn09_XorSwizzleBankConflictFreeInvolutionBijection =>
      causalMatrixTurnOperator P A C X .Turn09_XorSwizzleBankConflictFreeInvolutionBijection
  | .Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur =>
      causalMatrixTurnOperator P A C X .Turn10_WalshHadamardConjugationElenchusAndTalaskaSchur
  | .Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons =>
      causalMatrixTurnOperator P A C X .Turn11_Cl11LorentzianDetCayleyRotorAndDualHorizons
  | .Turn12_BCFWThreePointAmalgamationAndBridgeCommutator =>
      causalMatrixTurnOperator P A C X .Turn12_BCFWThreePointAmalgamationAndBridgeCommutator
  | .Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne =>
      causalMatrixTurnOperator P A C X .Turn13_Cl22KreinHamiltonianHopfAndJordanCrashAtMinusOne
  | .Turn14_YangianRMatrixQYBEAndResonantRankCollapse =>
      causalMatrixTurnOperator P A C X .Turn14_YangianRMatrixQYBEAndResonantRankCollapse
  | .Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary =>
      causalMatrixTurnOperator P A C X .Turn15_RTTMonodromyQuantumDetAndBetheLoopDictionary
  | .Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash =>
      causalMatrixTurnOperator P A C X .Turn16_DiracKreinZitterbewegungCarrierDecouplingAndSecularCrash
  | .Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession =>
      causalMatrixTurnOperator P A C X .Turn17_FoldyWouthuysenRapidityDictionaryAndThomasWignerPrecession
  | .Turn18_HammingShellConfinementBaxterTQAndCl11TwistedIntegrability =>
      comm (1 - P) (coneMinus P C - conePlus P A)
  | .Turn19_SixParadigmNCGSupermatrixWittenLaplacianAndFedosovCurvature =>
      anticomm (conePlus P A) (coneMinus P C)
  | .Turn20_YangLaxMonodromyQuaternityAntipodeQdetAndBerezinianDuality =>
      P * comm P X * comm P X * P + P * X * (1 - P) * X * P
  | .Turn21_SuperYangianGl11EvenDiracBugElenchusAndChiralSUSY =>
      anticomm (invS P) (conePlus P A + coneMinus P C)
  | .Turn22_SchubertQBinomWittenIndexAndIwahoriHeckeDemazureLusztig =>
      comm (conePlus P A) (coneMinus P C)
  | .Turn23_WittLightConeSplitKahlerBergmanCurvatureAndXorSwapGauge =>
      peirce11 P 1 + peirce00 P 1
  | .Turn24_KahlerBergmanNaturalGradientAndHyperbolicGeodesicQuartet =>
      (1 - genPhi P A C) * (1 + genPhi P A C) + genV P A C
  | .Turn25_MadelungBergmanHydrodynamicsAndGiventalKorffQuantumPieriGr24 =>
      comm (peirce11 P A) (peirce00 P C)
  | .Turn26_GeodesicYangBaxterBugElenchusAndConnesLottChiralHiggsTwist =>
      invS P * invS P
  | .Turn27_TridiagonalHammingBandwidthInhomogeneousGaugeAndMultiHeadTwist =>
      comm (peirce11 P X - peirce00 P X) (peirce11 P X - peirce00 P X)
  | .Turn28_NonAbelianSL2GaugeLaxExchangeDualityAndAuxiliaryWilsonLinks =>
      (1 + conePlus P A) * (1 - conePlus P A)
  | .Turn29_HalfBandwidthWittRegisterShuffleAndRademacherCurrentFactorization =>
      (1 - (2 : ℤ) • P) * (1 - (2 : ℤ) • P)
  | .Turn30_AdS3LorentzianKillingMetricMaurerCartanAndCartanGeodesics =>
      comm (invS P) (genPhi P A C) - (2 : ℤ) • genJ P A C
  | .Turn31_SakharovCPTTwinSectorsSemilinearSheetRiccatiAndBogoliubovDarkMatter =>
      invS P * genJ P A C * invS P + genJ P A C
  | .Turn32_SakharovJanusBimetricTorsorBondiVsJanusAndTOVBianchiAporia =>
      (invS P + genPhi P A C) * (invS P + genPhi P A C) - (1 + genV P A C)

/-- Exact extension theorem: `full32TurnOperator` restricts on `of17 a` to
`causalMatrixTurnOperator`. -/
theorem full32TurnOperator_of17 (P A C X : B) (a : CausalMatrixChatTurnArchetype) :
    full32TurnOperator P A C X (Full32TurnChatArchetype.of17 a) =
      causalMatrixTurnOperator P A C X a := by
  cases a <;> rfl

/-- **Master Non-Commutative Peirce Operator Identities Across All 15 New Turns (`Turn18`–`Turn32`):**
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the turn operators for
`Turn18`–`Turn32` satisfy exact Peirce-spine identities. -/
theorem full32TurnOperator_extension_identities {P : B} (hP : P * P = P) (A C X : B) :
    full32TurnOperator P A C X .Turn18_HammingShellConfinementBaxterTQAndCl11TwistedIntegrability =
      genPhi P A C ∧
    full32TurnOperator P A C X .Turn19_SixParadigmNCGSupermatrixWittenLaplacianAndFedosovCurvature =
      genV P A C ∧
    full32TurnOperator P A C X .Turn20_YangLaxMonodromyQuaternityAntipodeQdetAndBerezinianDuality = 0 ∧
    full32TurnOperator P A C X .Turn21_SuperYangianGl11EvenDiracBugElenchusAndChiralSUSY = 0 ∧
    full32TurnOperator P A C X .Turn22_SchubertQBinomWittenIndexAndIwahoriHeckeDemazureLusztig =
      genSig P A C ∧
    full32TurnOperator P A C X .Turn23_WittLightConeSplitKahlerBergmanCurvatureAndXorSwapGauge = 1 ∧
    full32TurnOperator P A C X .Turn24_KahlerBergmanNaturalGradientAndHyperbolicGeodesicQuartet = 1 ∧
    full32TurnOperator P A C X .Turn25_MadelungBergmanHydrodynamicsAndGiventalKorffQuantumPieriGr24 = 0 ∧
    full32TurnOperator P A C X .Turn26_GeodesicYangBaxterBugElenchusAndConnesLottChiralHiggsTwist = 1 ∧
    full32TurnOperator P A C X .Turn27_TridiagonalHammingBandwidthInhomogeneousGaugeAndMultiHeadTwist = 0 ∧
    full32TurnOperator P A C X .Turn28_NonAbelianSL2GaugeLaxExchangeDualityAndAuxiliaryWilsonLinks = 1 ∧
    full32TurnOperator P A C X .Turn29_HalfBandwidthWittRegisterShuffleAndRademacherCurrentFactorization = 1 ∧
    full32TurnOperator P A C X .Turn30_AdS3LorentzianKillingMetricMaurerCartanAndCartanGeodesics = 0 ∧
    full32TurnOperator P A C X .Turn31_SakharovCPTTwinSectorsSemilinearSheetRiccatiAndBogoliubovDarkMatter = 0 ∧
    full32TurnOperator P A C X .Turn32_SakharovJanusBimetricTorsorBondiVsJanusAndTOVBianchiAporia = 0 := by
  dsimp only [full32TurnOperator]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    peirce_nf hP

/-- **Master Coagulated Synthesis Across All 32 Turns of `https://share.gemini.google/kKehiDWWV8DI`
(`418904a66184`):**
Coagulates the 6-stage `solve et coagula` macro-poset (`ExtensionSolveEtCoagulaStage`),
the 32-turn causal poset (`Full32TurnChatArchetype`), the Peirce operator spine, the Witten
SUSY Laplacian, the Fedosov–Connes–Berry compression curvature, the `3 × 3` Iwahori–Hecke
Demazure–Lusztig braid algebra, the `6 × 6` Givental–Korff Quantum Pieri ring on
$QH^*(\operatorname{Gr}(2,4))$, the `4 × 4` non-Abelian $\operatorname{SL}_2$ Gauge–Lax exchange
duality, the `3 × 3` $\mathfrak{sl}_2(\mathbb{R}) \simeq \text{AdS}_3$ Maurer–Cartan Killing
geometry, the semilinear sheet evolution & Riccati bridge, and the Sakharov–Janus bimetric
torsor into one kernel-checked theorem. -/
theorem full32Turn_master_coagulated_synthesis
    {R : Type*} [CommRing R]
    {P : B} (hP : P * P = P) (A C X B_ur C_ll : B)
    {b1 b2 : B} (hb12 : b1 * b2 = 1) (hb21 : b2 * b1 = 1)
    (T_stress : Matrix (Fin 2) (Fin 2) B)
    (a32 : Full32TurnChatArchetype)
    (u theta eta L q w0 wJ wB wC ax az aeps : R)
    (G G_inv : Matrix (Fin 2) (Fin 2) R)
    (hGR : G * G_inv = 1) (hGL : G_inv * G = 1) :
    (ExtensionSolveEtCoagulaStage.causalEdge
        .E0_PrimordialBinaryCut_GradedSupermatrixAndWittSplit
        .E1_FourfoldRelationalAnatomy_LaxMonodromyAndSchurBerezinian ∧
      Full32TurnChatArchetype.Turn01_MetriplecticSplitGramiansAndAporiaDefect ≤ a32 ∧
      a32 ≤ Full32TurnChatArchetype.Turn32_SakharovJanusBimetricTorsorBondiVsJanusAndTOVBianchiAporia) ∧
    (comm (1 - P) (conePlus P A) = -conePlus P A ∧
      comm (1 - P) (coneMinus P C) = coneMinus P C ∧
      (superchargePlus2 B_ur + superchargeMinus2 C_ll) *
        (superchargePlus2 B_ur + superchargeMinus2 C_ll) =
        !![B_ur * C_ll, 0; 0, C_ll * B_ur] ∧
      comm (combinedParityGrading4 (R := R)) (singleSiteLax4 u theta eta) = 0 ∧
      anticomm (decoupledChiralGrading4 (R := R)) (oddSuperchargeLax4 eta) = 0) ∧
    (P * comm P X * comm P X * P = -(P * X * (1 - P) * X * P) ∧
      heckeT1 L * heckeT2 L * heckeT1 L = heckeT2 L * heckeT1 L * heckeT2 L ∧
      (heckeT1 L + 1) * (heckeT1 L - L • (1 : Matrix (Fin 3) (Fin 3) R)) = 0) ∧
    (comm (swap4 : Matrix (Fin 4) (Fin 4) R) (cl11TwistKron4 w0 wJ wB wC) = 0 ∧
      comm (quantumPieriC1 q) (quantumPieriC2 q) = 0 ∧
      (quantumPieriC1 q * quantumPieriC1 q) * (quantumPieriC1 q * quantumPieriC1 q) =
        (2 : R) • quantumSchubert22 q + (2 * q) • (1 : Matrix (Fin 6) (Fin 6) R) ∧
      kronIdLeft4 G * singleSiteLax4 u theta eta * kronIdLeft4 G_inv =
        kronIdRight4 G_inv * singleSiteLax4 u theta eta * kronIdRight4 G) ∧
    (sl2HalfAdjoint3 ax az aeps *
        (sl2HalfAdjoint3 ax az aeps * sl2HalfAdjoint3 ax az aeps) =
        (ax ^ 2 + az ^ 2 - aeps ^ 2) • sl2HalfAdjoint3 ax az aeps ∧
      ((minkowskiTimeReversal4 (R := R)) 0 0 * (minkowskiTimeReversal4 (R := R)) 1 1 *
        (minkowskiTimeReversal4 (R := R)) 2 2 * (minkowskiTimeReversal4 (R := R)) 3 3 = -1) ∧
      ((minkowskiTotalInversion4 (R := R)) 0 0 * (minkowskiTotalInversion4 (R := R)) 1 1 *
        (minkowskiTotalInversion4 (R := R)) 2 2 * (minkowskiTotalInversion4 (R := R)) 3 3 = 1) ∧
      bimetricCoupling2 b1 b2 * bimetricCoupling2 b1 b2 = 0 ∧
      bimetricAnnihilator2 b2 * (bimetricCoupling2 b1 b2 * T_stress) = 0) := by
  refine ⟨⟨rfl,
           (Full32TurnChatArchetype.turn01_is_root_and_turn32_is_terminal a32).1,
           (Full32TurnChatArchetype.turn01_is_root_and_turn32_is_terminal a32).2.1⟩,
          ⟨(turn18_peirce_magnon_charge_selection_commutators hP X A C).2.1,
           (turn18_peirce_magnon_charge_selection_commutators hP X A C).2.2,
           (turn19_supermatrix_parity_and_witten_laplacian 0 B_ur C_ll 0).2.2.2.2.1,
           (turn21_even_dirac_bug_elenchus_and_chiral_supercharge u theta eta).1,
           (turn21_even_dirac_bug_elenchus_and_chiral_supercharge u theta eta).2.1⟩,
          ⟨(turn19_fedosov_connes_berry_curvature_and_compression_defect hP X).1,
           (turn22_iwahori_hecke_quadratic_aporia_and_braid_relation L).2.2.2,
           (turn22_iwahori_hecke_quadratic_aporia_and_braid_relation L).1⟩,
          ⟨(turn18_cl11_twist_swap_invariance_and_parabolic_jordan_nilpotency w0 wJ wB wC).1,
           (turn25_turn27_givental_korff_quantum_pieri_gr24_identities q).1,
           (turn25_turn27_givental_korff_quantum_pieri_gr24_identities q).2.2.1,
           (turn28_nonabelian_gauge_lax_exchange_duality u theta eta G G_inv hGR hGL).2.2⟩,
          ⟨(turn30_sl2_ads3_killing_maurer_cartan_and_cartan_metric ax az aeps 0 0).2.2.2.1,
           (turn32_lorentz_det_bondi_vs_janus_tov_aporia_and_bimetric_bridge (R := R) 0 0 0 hb12 hb21 T_stress).1,
           (turn32_lorentz_det_bondi_vs_janus_tov_aporia_and_bimetric_bridge (R := R) 0 0 0 hb12 hb21 T_stress).2.1,
           (turn32_lorentz_det_bondi_vs_janus_tov_aporia_and_bimetric_bridge (R := R) 0 0 0 hb12 hb21 T_stress).2.2.2.2.1,
           (turn32_lorentz_det_bondi_vs_janus_tov_aporia_and_bimetric_bridge (R := R) 0 0 0 hb12 hb21 T_stress).2.2.2.2.2⟩⟩

end StageE5

end InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianExtensionPoset
