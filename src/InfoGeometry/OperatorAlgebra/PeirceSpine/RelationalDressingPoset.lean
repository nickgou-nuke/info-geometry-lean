/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge

/-!
# Stage D₂₆ (Archetypes F₁ → F₆): Non-Commutative Relational Dressing, Cocyclic Bundle Geometry,
# Quantum Reference Frame Switching, BRST Ghost Reduction & Gribov-Free Peirce Horizon Dressing

Pure non-commutative operator-algebraic formalization over `[Ring B] [StarRing B]`
reusing the canonical `InfoGeometry.OperatorAlgebra.PeirceSpine` primitives
(`comm`, `anticomm`, `conePlus`, `coneMinus`, `genV`, `conjPlus`, `conjPlusInv`,
`conjMinus`, `conjMinusInv`, `projChartPlus`):

* **Archetype `F₁` (`maurerCartanCocycle`, `maurer_cartan_cocycle_and_composition`)**:
  Non-Abelian Maurer–Cartan 1-cocycle chain rule
  `Λ_d(U Γ) = Γ⁻¹ Λ_d(U) Γ + Λ_d(Γ)` and transitive connection dressing
  `(A^U)^Γ = A^{U Γ}`, together with the exact carrier bridge to
  `NoncommutativeMaurerCartanAdjointBridge.maurerCartanForm`.
* **Archetype `F₂` (`dressedConn`, `dressedCurv`, `dressedState`, `relationalPairing`,
  `point_coincidence_gauge_invariance`)**:
  Exact gauge invariance of dressed connections `(A^Γ)^{U^Γ} = A^U`, dressed tensors
  `(F^Γ)^{U^Γ} = F^U`, dressed states `(Ψ^Γ)^{U^Γ} = Ψ^U`, and relational point-coincidence
  pairings `⟨Ψ₁^U, F^U Ψ₂^U⟩` under equivariant dressing transformations `U^Γ = Γ⁻¹ U`.
* **Archetype `F₃` (`quantum_reference_frame_switching_of_second_kind`)**:
  Quantum reference frame switching (transformations of the 2nd kind `U ↦ U Ξ`)
  `A^{U Ξ} = (A^U)^Ξ`, `F^{U Ξ} = (F^U)^Ξ`, `Ψ^{U Ξ} = (Ψ^U)^Ξ`, and strict invariance
  of the relational expectation pairing `⟨Ψ₁^U, F^U Ψ₂^U⟩` under unitary frame transitions
  (`Ξ * Ξ⁻¹ = 1`, `star Ξ⁻¹ = Ξ`).
* **Archetype `F₄` (`dressedGhost`, `brstGhostFull`, `brstGhostPartial`,
  `full_and_partial_brst_ghost_reduction`)**:
  Full BRST ghost trivialization `C_ghost^U = 0` vs. partial normal-subgroup ghost
  reduction `C_sub^{U₁} = C_res`.
* **Archetype `F₅` (`connectionShiftCocycle`, `anomaly_cancellation_and_second_kind_resurgence`)**:
  Gauge anomaly cancellation on dressed connections `(A^Γ)^{U^Γ} - A^U = 0` and resurgence
  in the physical 2nd-kind frame-transition sector `A^{U Ξ} - A^U = (A^U)^Ξ - A^U`.
* **Archetype `F₆` (`gribov_free_peirce_horizon_dressing`)**:
  Gribov-free unipotent Peirce horizon dressing `U = 1 + N_+(A)` (`U⁻¹ = 1 - N_+(A)`),
  exact identification with `conjPlusInv`/`conjPlus` and `projChartPlus`, Maurer–Cartan
  cocycle evaluation `Λ_{ad_P}(1 + N_+) = N_+`, dressed grading `P^{1 + N_+} = P + 2 N_+`,
  and exact invariance of the Peirce–Clifford horizon metric `V^{1 + N_+} = V`.

## Three-Bucket Audit Classification

- **BUCKET 1 (`KERNEL_PROVED`):**
  All 6 stages `F₁ → F₆` (`RelationalDressingStage`), Maurer–Cartan 1-cocycle chain rule,
  point-coincidence gauge invariance, 2nd-kind quantum reference frame switching, BRST ghost
  reduction, and Gribov-free unipotent Peirce horizon dressing in `[Ring B] [StarRing B]`.
- **BUCKET 2 (`EXPLICIT_HYPOTHESIS`):**
  Two-sided inverse and Leibniz derivation hypotheses (`U * U⁻¹ = 1`, `d(U Γ) = d(U) Γ + U d(Γ)`)
  and idempotency `hP : P * P = P` on `[Ring B]`.
- **BUCKET 3 (`OPEN_HORIZON`):**
  Non-perturbative Gribov copy topology on infinite-dimensional principal gauge bundles beyond
  unipotent Peirce horizon charts.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ### 1. The 6-Stage Causal Poset of Relational Dressing Archetypes (`F₁ → F₆`) -/

/-- Archetype stages `F₁` through `F₆` of Stage `D₂₆`. -/
inductive RelationalDressingStage : Type
  | F1 | F2 | F3 | F4 | F5 | F6
  deriving DecidableEq, Repr

namespace RelationalDressingStage

/-- Integer topological rank (1 through 6) of each relational dressing archetype. -/
def rank : RelationalDressingStage → ℕ
  | F1 => 1
  | F2 => 2
  | F3 => 3
  | F4 => 4
  | F5 => 5
  | F6 => 6

/-- The topological rank map on `RelationalDressingStage` is injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance relationalDressingStageLinearOrder : LinearOrder RelationalDressingStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal edges of the 6-stage relational dressing poset (`F₁ → F₆`). -/
def causalEdge : RelationalDressingStage → RelationalDressingStage → Prop
  | F1, F2 => True
  | F1, F3 => True
  | F2, F4 => True
  | F2, F5 => True
  | F3, F4 => True
  | F3, F5 => True
  | F4, F6 => True
  | F5, F6 => True
  | _, _ => False

/-- Every direct edge in the `F₁ → F₆` causal DAG strictly increases topological rank. -/
theorem causalEdge_strict_rank_mono {s t : RelationalDressingStage} (h : causalEdge s t) :
    rank s < rank t := by
  cases s <;> cases t <;> first | decide | cases h

/-- The `F₁ → F₆` causal DAG has no self-loops. -/
theorem causalEdge_irrefl (s : RelationalDressingStage) : ¬ causalEdge s s := by
  intro h
  exact Nat.lt_irrefl (rank s) (causalEdge_strict_rank_mono h)

end RelationalDressingStage

/-! ### 2. Core Cocycle, Relational Dressing & BRST Ghost Primitives -/

section RingPrimitives

variable {B : Type*} [Ring B]

/-- **Archetype `F₁` (`maurerCartanCocycle`)**:
Non-Abelian Maurer–Cartan 1-cocycle `U⁻¹ d(U)` for an operator map `d : B → B`. -/
def maurerCartanCocycle (d : B → B) (U U_inv : B) : B :=
  U_inv * d U

/-- **Archetype `F₂` (`dressedConn`)**:
Dressed gauge connection `U_inv * A * U + U_inv * d U`. -/
def dressedConn (d : B → B) (U U_inv A : B) : B :=
  U_inv * A * U + U_inv * d U

/-- **Archetype `F₂` (`dressedCurv`)**:
Dressed tensor/curvature operator `U_inv * F * U`. -/
def dressedCurv (U U_inv F : B) : B :=
  U_inv * F * U

/-- **Archetype `F₂` (`dressedState`)**:
Dressed state operator `U_inv * Ψ`. -/
def dressedState (U_inv Ψ : B) : B :=
  U_inv * Ψ

/-- **Archetype `F₄` (`dressedGhost`)**:
Dressed BRST ghost `U_inv * C_ghost * U + U_inv * δ_brst U`. -/
def dressedGhost (δ_brst : B → B) (U U_inv C_ghost : B) : B :=
  U_inv * C_ghost * U + U_inv * δ_brst U

/-- **Archetype `F₄` (`brstGhostFull`)**:
Full BRST Maurer–Cartan ghost `-(δ_brst U * U_inv)`. -/
def brstGhostFull (δ_brst : B → B) (U U_inv : B) : B :=
  -(δ_brst U * U_inv)

/-- **Archetype `F₄` (`brstGhostPartial`)**:
Partial normal-subgroup BRST ghost `-(δ_brst U₁ * U₁_inv) + U₁ * C_res * U₁_inv`. -/
def brstGhostPartial (δ_brst : B → B) (U₁ U₁_inv C_res : B) : B :=
  -(δ_brst U₁ * U₁_inv) + U₁ * C_res * U₁_inv

/-- **Archetype `F₅` (`connectionShiftCocycle`)**:
Finite gauge/frame shift 1-cocycle `dressedConn d Γ Γ_inv A - A`. -/
def connectionShiftCocycle (d : B → B) (Γ Γ_inv A : B) : B :=
  dressedConn d Γ Γ_inv A - A

end RingPrimitives

section StarPrimitives

variable {B : Type*} [Ring B] [StarRing B]

/-- **Archetype `F₂`/`F₃` (`relationalPairing`)**:
Relational point-coincidence pairing `star Ψ₁ * F * Ψ₂`. -/
def relationalPairing (Ψ₁ F Ψ₂ : B) : B :=
  star Ψ₁ * F * Ψ₂

end StarPrimitives

/-! ### 3. Individual Lemmas for Archetypes `F₁ → F₆` -/

section Theorems

variable {B : Type*} [Ring B] [StarRing B]

/-- **Theorem `F₁.0` (`maurerCartanCocycle_adCLM_eq_maurerCartanForm`)**:
Exact carrier identification between `maurerCartanCocycle` along the continuous inner
derivation `adCLM H` on a Banach algebra `A` and
`NoncommutativeMaurerCartanAdjointBridge.maurerCartanForm`. -/
theorem maurerCartanCocycle_adCLM_eq_maurerCartanForm
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (G Ginv H : A) :
    maurerCartanCocycle
      (InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge.adCLM H) G Ginv =
      InfoGeometry.OperatorAlgebra.NoncommutativeMaurerCartanAdjointBridge.maurerCartanForm
        G Ginv H :=
  rfl

/-- **Theorem `F₁.1` (`maurer_cartan_cocycle_and_composition`)**:
Let `d : B → B` satisfy the Leibniz rule `d (U * Γ) = d U * Γ + U * d Γ` and let `U_inv * U = 1`.
Then:
1. `maurerCartanCocycle d (U * Γ) (Γ_inv * U_inv) =`
   `Γ_inv * maurerCartanCocycle d U U_inv * Γ + maurerCartanCocycle d Γ Γ_inv`.
2. `dressedConn d Γ Γ_inv (dressedConn d U U_inv A) = dressedConn d (U * Γ) (Γ_inv * U_inv) A`. -/
theorem maurer_cartan_cocycle_and_composition
    {B : Type*} [Ring B]
    (d : B → B) {U U_inv Γ Γ_inv : B}
    (hLeib : d (U * Γ) = d U * Γ + U * d Γ)
    (hU : U_inv * U = 1) (A : B) :
    maurerCartanCocycle d (U * Γ) (Γ_inv * U_inv) =
      Γ_inv * maurerCartanCocycle d U U_inv * Γ + maurerCartanCocycle d Γ Γ_inv ∧
    dressedConn d Γ Γ_inv (dressedConn d U U_inv A) =
      dressedConn d (U * Γ) (Γ_inv * U_inv) A := by
  have hCocycle : maurerCartanCocycle d (U * Γ) (Γ_inv * U_inv) =
      Γ_inv * maurerCartanCocycle d U U_inv * Γ + maurerCartanCocycle d Γ Γ_inv := by
    unfold maurerCartanCocycle
    rw [hLeib, mul_add]
    congr 1
    · simp only [mul_assoc]
    · calc (Γ_inv * U_inv) * (U * d Γ)
        _ = Γ_inv * (U_inv * U) * d Γ := by simp only [mul_assoc]
        _ = Γ_inv * d Γ := by rw [hU, mul_one]
  refine ⟨hCocycle, ?_⟩
  unfold dressedConn
  change Γ_inv * (U_inv * A * U + maurerCartanCocycle d U U_inv) * Γ +
      maurerCartanCocycle d Γ Γ_inv =
    (Γ_inv * U_inv) * A * (U * Γ) + maurerCartanCocycle d (U * Γ) (Γ_inv * U_inv)
  rw [hCocycle, mul_add, add_mul, add_assoc]
  congr 1
  simp only [mul_assoc]

/-- **Theorem `F₂.1` (`point_coincidence_gauge_invariance`)**:
Under a gauge transformation `Γ` (`Γ_inv * Γ = 1`, `Γ * Γ_inv = 1`) where `U^Γ = Γ_inv * U`
and `(U^Γ)_inv = U_inv * Γ`:
1. `(A^Γ)^{U^Γ} = A^U`, `(F^Γ)^{U^Γ} = F^U`, and `(Ψ^Γ)^{U^Γ} = Ψ^U`.
2. Consequently, the dressed point-coincidence pairing
   `relationalPairing (Ψ₁^U) (F^U) (Ψ₂^U)` is strictly gauge-invariant. -/
theorem point_coincidence_gauge_invariance
    (d : B → B) {U U_inv Γ Γ_inv : B}
    (hLeib : d (Γ * (Γ_inv * U)) = d Γ * (Γ_inv * U) + Γ * d (Γ_inv * U))
    (hΓ1 : Γ_inv * Γ = 1) (hΓ2 : Γ * Γ_inv = 1) (A F Ψ₁ Ψ₂ : B) :
    dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) =
      dressedConn d U U_inv A ∧
    dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F) =
      dressedCurv U U_inv F ∧
    dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₁) =
      dressedState U_inv Ψ₁ ∧
    relationalPairing
      (dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₁))
      (dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F))
      (dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₂)) =
      relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂) := by
  have hComp :=
    (maurer_cartan_cocycle_and_composition d (U_inv := Γ_inv) (Γ_inv := U_inv * Γ) hLeib hΓ1 A).2
  have hProd1 : Γ * (Γ_inv * U) = U := by rw [← mul_assoc, hΓ2, one_mul]
  have hProd2 : (U_inv * Γ) * Γ_inv = U_inv := by rw [mul_assoc, hΓ2, mul_one]
  have hConn : dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) =
      dressedConn d U U_inv A := by rw [hComp, hProd1, hProd2]
  have hCurv : dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F) =
      dressedCurv U U_inv F := by
    unfold dressedCurv
    calc (U_inv * Γ) * (Γ_inv * F * Γ) * (Γ_inv * U)
      _ = U_inv * (Γ * Γ_inv) * F * (Γ * Γ_inv) * U := by simp only [mul_assoc]
      _ = U_inv * F * U := by rw [hΓ2, mul_one, mul_one]
  have hState : ∀ Ψ : B, dressedState (U_inv * Γ) (dressedState Γ_inv Ψ) = dressedState U_inv Ψ := by
    intro Ψ
    unfold dressedState
    rw [← mul_assoc, hProd2]
  refine ⟨hConn, hCurv, hState Ψ₁, ?_⟩
  rw [hState Ψ₁, hState Ψ₂, hCurv]

/-- **Theorem `F₃.1` (`quantum_reference_frame_switching_of_second_kind`)**:
Under a change of internal reference frame `U ↦ U * Ξ` (with inverse `Ξ_inv * U_inv`
where `U_inv * U = 1`):
1. `dressedConn d (U * Ξ) (Ξ_inv * U_inv) A = dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A)`.
2. `dressedCurv (U * Ξ) (Ξ_inv * U_inv) F = dressedCurv Ξ Ξ_inv (dressedCurv U U_inv F)`.
3. `dressedState (Ξ_inv * U_inv) Ψ₁ = dressedState Ξ_inv (dressedState U_inv Ψ₁)`.
4. **Unitary Quantum Reference Frame Equivalence (`star Ξ_inv = Ξ` and `Ξ * Ξ_inv = 1`)**:
   Switching between two unitary quantum reference frames preserves the relational measurement
   pairing identically:
   `relationalPairing (dressedState (Ξ_inv * U_inv) Ψ₁) (dressedCurv (U * Ξ) (Ξ_inv * U_inv) F) (dressedState (Ξ_inv * U_inv) Ψ₂) =`
   `relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂)`. -/
theorem quantum_reference_frame_switching_of_second_kind
    (d : B → B) {U U_inv Ξ Ξ_inv : B}
    (hLeib : d (U * Ξ) = d U * Ξ + U * d Ξ)
    (hU : U_inv * U = 1) (hΞ : Ξ * Ξ_inv = 1) (hΞunitary : star Ξ_inv = Ξ)
    (A F Ψ₁ Ψ₂ : B) :
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A =
      dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A) ∧
    dressedCurv (U * Ξ) (Ξ_inv * U_inv) F =
      dressedCurv Ξ Ξ_inv (dressedCurv U U_inv F) ∧
    dressedState (Ξ_inv * U_inv) Ψ₁ =
      dressedState Ξ_inv (dressedState U_inv Ψ₁) ∧
    relationalPairing
      (dressedState (Ξ_inv * U_inv) Ψ₁)
      (dressedCurv (U * Ξ) (Ξ_inv * U_inv) F)
      (dressedState (Ξ_inv * U_inv) Ψ₂) =
      relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂) := by
  have hConn := (maurer_cartan_cocycle_and_composition d (Γ_inv := Ξ_inv) hLeib hU A).2.symm
  have hCurv : dressedCurv (U * Ξ) (Ξ_inv * U_inv) F =
      dressedCurv Ξ Ξ_inv (dressedCurv U U_inv F) := by
    unfold dressedCurv; simp only [mul_assoc]
  have hState : ∀ Ψ : B, dressedState (Ξ_inv * U_inv) Ψ = dressedState Ξ_inv (dressedState U_inv Ψ) := by
    intro Ψ; unfold dressedState; rw [mul_assoc]
  refine ⟨hConn, hCurv, hState Ψ₁, ?_⟩
  rw [hState Ψ₁, hState Ψ₂, hCurv]
  unfold relationalPairing dressedState dressedCurv
  rw [star_mul, hΞunitary]
  calc (star (U_inv * Ψ₁) * Ξ) * (Ξ_inv * (U_inv * F * U) * Ξ) * (Ξ_inv * (U_inv * Ψ₂))
    _ = star (U_inv * Ψ₁) * (Ξ * Ξ_inv) * (U_inv * F * U) * (Ξ * Ξ_inv) * (U_inv * Ψ₂) := by
        simp only [mul_assoc]
    _ = star (U_inv * Ψ₁) * (U_inv * F * U) * (U_inv * Ψ₂) := by
        rw [hΞ, mul_one, mul_one]

/-- **Theorem `F₄.1` (`full_and_partial_brst_ghost_reduction`)**:
Let `δ_brst : B → B` be a BRST variation.
1. **Full Symmetry Reduction**:
   If `U` (`U_inv * U = 1`) reduces the full gauge group so that `C_ghost = brstGhostFull δ_brst U U_inv`,
   then the dressed ghost vanishes identically:
   `dressedGhost δ_brst U U_inv (brstGhostFull δ_brst U U_inv) = 0`.
2. **Partial Subgroup Reduction**:
   If `U₁` (`U₁_inv * U₁ = 1`) reduces a normal subgroup while leaving a residual ghost `C_res`
   so that `C_ghost = brstGhostPartial δ_brst U₁ U₁_inv C_res`, then dressing reduces the ghost
   algebra to the exact residual ghost `C_res`:
   `dressedGhost δ_brst U₁ U₁_inv (brstGhostPartial δ_brst U₁ U₁_inv C_res) = C_res`. -/
theorem full_and_partial_brst_ghost_reduction
    {B : Type*} [Ring B]
    (δ_brst : B → B) {U U_inv U₁ U₁_inv : B}
    (hU : U_inv * U = 1) (hU₁ : U₁_inv * U₁ = 1) (C_res : B) :
    dressedGhost δ_brst U U_inv (brstGhostFull δ_brst U U_inv) = 0 ∧
    dressedGhost δ_brst U₁ U₁_inv (brstGhostPartial δ_brst U₁ U₁_inv C_res) = C_res := by
  have hFull : dressedGhost δ_brst U U_inv (brstGhostFull δ_brst U U_inv) = 0 := by
    unfold dressedGhost brstGhostFull
    have hSimp : U_inv * -(δ_brst U * U_inv) * U = -(U_inv * δ_brst U) := by
      calc U_inv * -(δ_brst U * U_inv) * U
        _ = -(U_inv * δ_brst U * (U_inv * U)) := by simp only [mul_neg, neg_mul, mul_assoc]
        _ = -(U_inv * δ_brst U) := by rw [hU, mul_one]
    rw [hSimp, neg_add_cancel]
  refine ⟨hFull, ?_⟩
  unfold dressedGhost brstGhostPartial
  rw [mul_add, add_mul]
  have hSimp1 : U₁_inv * -(δ_brst U₁ * U₁_inv) * U₁ = -(U₁_inv * δ_brst U₁) := by
    calc U₁_inv * -(δ_brst U₁ * U₁_inv) * U₁
      _ = -(U₁_inv * δ_brst U₁ * (U₁_inv * U₁)) := by simp only [mul_neg, neg_mul, mul_assoc]
      _ = -(U₁_inv * δ_brst U₁) := by rw [hU₁, mul_one]
  have hSimp2 : U₁_inv * (U₁ * C_res * U₁_inv) * U₁ = C_res := by
    calc U₁_inv * (U₁ * C_res * U₁_inv) * U₁
      _ = (U₁_inv * U₁) * C_res * (U₁_inv * U₁) := by simp only [mul_assoc]
      _ = C_res := by rw [hU₁, one_mul, mul_one]
  rw [hSimp1, hSimp2]
  abel

/-- **Theorem `F₅.1` (`anomaly_cancellation_and_second_kind_resurgence`)**:
1. **Gauge Anomaly Cancellation**:
   Under any gauge transformation `Γ`, the difference between the `U^Γ`-dressed transformed
   connection `(A^Γ)^{U^Γ}` and the `U`-dressed connection `A^U` vanishes identically.
2. **Resurgence Under Frame Transformations of the 2nd Kind**:
   Under a physical frame shift `U ↦ U * Ξ` (`U_inv * U = 1`), the shift of the dressed connection
   `A^{U Ξ} - A^U` equals the exact `Ξ`-cocycle evaluated on the dressed connection `A^U`:
   `dressedConn d (U * Ξ) (Ξ_inv * U_inv) A - dressedConn d U U_inv A =`
   `connectionShiftCocycle d Ξ Ξ_inv (dressedConn d U U_inv A)`. -/
theorem anomaly_cancellation_and_second_kind_resurgence
    (d : B → B) {U U_inv Γ Γ_inv Ξ Ξ_inv : B}
    (hLeibΓ : d (Γ * (Γ_inv * U)) = d Γ * (Γ_inv * U) + Γ * d (Γ_inv * U))
    (hLeibΞ : d (U * Ξ) = d U * Ξ + U * d Ξ)
    (hU : U_inv * U = 1) (hΓ1 : Γ_inv * Γ = 1) (hΓ2 : Γ * Γ_inv = 1) (A : B) :
    dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) -
      dressedConn d U U_inv A = 0 ∧
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A - dressedConn d U U_inv A =
      connectionShiftCocycle d Ξ Ξ_inv (dressedConn d U U_inv A) := by
  have hInv := (point_coincidence_gauge_invariance d (U_inv := U_inv) hLeibΓ hΓ1 hΓ2 A 0 0 0).1
  have hComp := (maurer_cartan_cocycle_and_composition d (Γ_inv := Ξ_inv) hLeibΞ hU A).2.symm
  refine ⟨by rw [hInv, sub_self], ?_⟩
  unfold connectionShiftCocycle
  rw [hComp]

/-- **Theorem `F₆.1` (`gribov_free_peirce_horizon_dressing`)**:
For any idempotent `P` (`P * P = P`) and any `A, C, X : B`:
1. The unipotent horizon dressing field `U = 1 + conePlus P A` is globally invertible by
   polynomial nilpotency (`U_inv = 1 - conePlus P A`, with both `U_inv * U = 1` and `U * U_inv = 1`).
2. Tensor dressing by `U = 1 + conePlus P A` coincides with `conjPlusInv P A`, while dressing by
   `U_inv = 1 - conePlus P A` coincides with `conjPlus P A` and sends `P` to the projective
   chart `projChartPlus P A = P - conePlus P A`.
3. Under the Peirce grading derivation `d = comm P`,
   `maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A` and
   `dressedConn (comm P) (1 + conePlus P A) (1 - conePlus P A) P = P + (2 : ℤ) • conePlus P A`.
4. Dressing preserves the horizon metric `genV P A C` identically:
   `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C`. -/
theorem gribov_free_peirce_horizon_dressing
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X : B) :
    (1 - conePlus P A) * (1 + conePlus P A) = 1 ∧
    (1 + conePlus P A) * (1 - conePlus P A) = 1 ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) X = conjPlusInv P A X ∧
    dressedCurv (1 - conePlus P A) (1 + conePlus P A) X = conjPlus P A X ∧
    dressedCurv (1 - conePlus P A) (1 + conePlus P A) P = projChartPlus P A ∧
    maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A ∧
    dressedConn (comm P) (1 + conePlus P A) (1 - conePlus P A) P =
      P + (2 : ℤ) • conePlus P A ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C := by
  refine ⟨by peirce_nf hP, by peirce_nf hP, rfl, rfl,
    by unfold dressedCurv projChartPlus; peirce_nf hP,
    by unfold maurerCartanCocycle; peirce_nf hP,
    by unfold dressedConn; peirce_nf hP,
    by unfold dressedCurv; peirce_nf hP⟩

/-! ### 4. Master Theorem `D₂₆` (`F₁ → F₆`): Relational Dressing & Cocyclic Bundle Geometry -/

/-- **Master Theorem `D₂₆` (`stage_D26_relational_dressing_frame_switching_and_brst_master_synthesis`)**:
Complete synthesis of the 6-stage relational dressing poset (`F₁ → F₆`) over `[Ring B] [StarRing B]`:
1. **`F₁` (Non-Abelian 1-Cocycle Chain Rule)**:
   `maurerCartanCocycle d (U * Ξ) (Ξ_inv * U_inv) = Ξ_inv * maurerCartanCocycle d U U_inv * Ξ + maurerCartanCocycle d Ξ Ξ_inv`;
2. **`F₂` (Point-Coincidence Gauge Invariance of Dressed Fields & Relational Pairings)**:
   `(A^Γ)^{U^Γ} = A^U` and `⟨(Ψ₁^Γ)^{U^Γ}, (F^Γ)^{U^Γ} (Ψ₂^Γ)^{U^Γ}⟩ = ⟨Ψ₁^U, F^U Ψ₂^U⟩`;
3. **`F₃` (Quantum Reference Frame Switching of the 2nd Kind `U ↦ U Ξ` & Unitary Pairing Invariance)**:
   `A^{U Ξ} = (A^U)^Ξ` and `⟨Ψ₁^{U Ξ}, F^{U Ξ} Ψ₂^{U Ξ}⟩ = ⟨Ψ₁^U, F^U Ψ₂^U⟩` when `Ξ * Ξ_inv = 1` and `star Ξ_inv = Ξ`;
4. **`F₄` (Full BRST Ghost Trivialization vs. Partial Subgroup Ghost Reduction)**:
   `dressedGhost δ_brst U U_inv (brstGhostFull δ_brst U U_inv) = 0` and
   `dressedGhost δ_brst U₁ U₁_inv (brstGhostPartial δ_brst U₁ U₁_inv C_res) = C_res`;
5. **`F₅` (Anomaly Cancellation on Dressed Connections & 2nd-Kind Resurgence)**:
   `(A^Γ)^{U^Γ} - A^U = 0` and `A^{U Ξ} - A^U = connectionShiftCocycle d Ξ Ξ_inv (A^U)`;
6. **`F₆` (Gribov-Free Unipotent Peirce Horizon Dressing)**:
   `maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A`,
   `dressedConn (comm P) (1 + conePlus P A) (1 - conePlus P A) P = P + 2 • conePlus P A`, and
   `dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C`. -/
theorem stage_D26_relational_dressing_frame_switching_and_brst_master_synthesis
    (d δ_brst : B → B) {P U U_inv U₁ U₁_inv Γ Γ_inv Ξ Ξ_inv : B}
    (hP : P * P = P)
    (hLeibΓ : d (Γ * (Γ_inv * U)) = d Γ * (Γ_inv * U) + Γ * d (Γ_inv * U))
    (hLeibΞ : d (U * Ξ) = d U * Ξ + U * d Ξ)
    (hU : U_inv * U = 1) (hU₁ : U₁_inv * U₁ = 1)
    (hΓ1 : Γ_inv * Γ = 1) (hΓ2 : Γ * Γ_inv = 1)
    (hΞ : Ξ * Ξ_inv = 1) (hΞunitary : star Ξ_inv = Ξ)
    (A C F Ψ₁ Ψ₂ C_res : B) :
    -- 1. Non-Abelian 1-Cocycle Chain Rule (F₁):
    maurerCartanCocycle d (U * Ξ) (Ξ_inv * U_inv) =
      Ξ_inv * maurerCartanCocycle d U U_inv * Ξ + maurerCartanCocycle d Ξ Ξ_inv ∧
    -- 2. Point-Coincidence Gauge Invariance of Dressed Fields & Relational Pairings (F₂):
    dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) =
      dressedConn d U U_inv A ∧
    relationalPairing
      (dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₁))
      (dressedCurv (Γ_inv * U) (U_inv * Γ) (dressedCurv Γ Γ_inv F))
      (dressedState (U_inv * Γ) (dressedState Γ_inv Ψ₂)) =
      relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂) ∧
    -- 3. Quantum Reference Frame Switching (2nd Kind `U ↦ U Ξ`) & Unitary Pairing Invariance (F₃):
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A =
      dressedConn d Ξ Ξ_inv (dressedConn d U U_inv A) ∧
    relationalPairing
      (dressedState (Ξ_inv * U_inv) Ψ₁)
      (dressedCurv (U * Ξ) (Ξ_inv * U_inv) F)
      (dressedState (Ξ_inv * U_inv) Ψ₂) =
      relationalPairing (dressedState U_inv Ψ₁) (dressedCurv U U_inv F) (dressedState U_inv Ψ₂) ∧
    -- 4. Full BRST Ghost Vanishing vs. Partial Subgroup Ghost Reduction (F₄):
    dressedGhost δ_brst U U_inv (brstGhostFull δ_brst U U_inv) = 0 ∧
    dressedGhost δ_brst U₁ U₁_inv (brstGhostPartial δ_brst U₁ U₁_inv C_res) = C_res ∧
    -- 5. Anomaly Cancellation on Dressed Connections & 2nd-Kind Resurgence (F₅):
    dressedConn d (Γ_inv * U) (U_inv * Γ) (dressedConn d Γ Γ_inv A) -
      dressedConn d U U_inv A = 0 ∧
    dressedConn d (U * Ξ) (Ξ_inv * U_inv) A - dressedConn d U U_inv A =
      connectionShiftCocycle d Ξ Ξ_inv (dressedConn d U U_inv A) ∧
    -- 6. Gribov-Free Unipotent Peirce Horizon Dressing (F₆):
    maurerCartanCocycle (comm P) (1 + conePlus P A) (1 - conePlus P A) = conePlus P A ∧
    dressedConn (comm P) (1 + conePlus P A) (1 - conePlus P A) P =
      P + (2 : ℤ) • conePlus P A ∧
    dressedCurv (1 + conePlus P A) (1 - conePlus P A) (genV P A C) = genV P A C := by
  rcases maurer_cartan_cocycle_and_composition d (Γ_inv := Ξ_inv) hLeibΞ hU A with ⟨hC1, _⟩
  rcases point_coincidence_gauge_invariance d (U_inv := U_inv) hLeibΓ hΓ1 hΓ2 A F Ψ₁ Ψ₂ with
    ⟨hPC1, _, _, hPC4⟩
  rcases quantum_reference_frame_switching_of_second_kind d hLeibΞ hU hΞ hΞunitary A F Ψ₁ Ψ₂ with
    ⟨hQF1, _, _, hQF4⟩
  rcases full_and_partial_brst_ghost_reduction δ_brst hU hU₁ C_res with ⟨hB1, hB2⟩
  rcases anomaly_cancellation_and_second_kind_resurgence d (Ξ_inv := Ξ_inv) hLeibΓ hLeibΞ hU hΓ1 hΓ2 A with
    ⟨hAnom1, hAnom2⟩
  rcases gribov_free_peirce_horizon_dressing hP A C 0 with ⟨_, _, _, _, _, hP2, hP3, hP4⟩
  exact ⟨hC1, hPC1, hPC4, hQF1, hQF4, hB1, hB2, hAnom1, hAnom2, hP2, hP3, hP4⟩

end Theorems

end InfoGeometry.OperatorAlgebra.PeirceSpine
