/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.KreinPeirceTowerIntertwine
import InfoGeometry.Algebra.NoncommutativeKitaevMajoranaThermalHallSynthesis
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.Core.IdempotentDefectIteration

/-!
# Kitaev Honeycomb Spin Liquid via Peirce–Tetraktys–Aporia Epistemic Synthesis

5-stage noncommutative `solve et coagula` epistemic compilation of the Kitaev
honeycomb Majorana/vison/Dirac–Zorn system (`KM₁`–`KM₄`) in
`NoncommutativeKitaevMajoranaThermalHallSynthesis` and `KreinPeirceTowerIntertwine`
over an arbitrary associative ring `[Ring B]`:

1. **Stage 1 — Primordial Binary Cut (`sublatticeCut`)**:
   The bipartite sublattice idempotent `P_A = diag(1, 0) : NestedMat B` satisfies
   `P_A² = P_A`, complement `1 - P_A = diag(0, 1)`, grading involution
   `invS P_A = sublatticeGamma`, explicit characteristic-free non-commutativity
   `P_A * majC ≠ majC * P_A`, and exact Peirce `ℤ/2`-parity separation of
   `majC, majB1, majB2, majB3, kitaevGaugeD, kitaevSpin1..3`.
2. **Stage 2 — Fourfold Peirce Corner Anatomy**:
   Decomposes `kitaevHoneycombH Δ_H K₁ K₂ K₃` into its four Peirce blocks:
   `peirce11` (`fiberEmbed Δ_H`), `conePlus` (`vecOp K`), `coneMinus` (`vecOp K`),
   and `peirce00` (`-fiberEmbed Δ_H`).
3. **Stage 3 — Transcendent Function, Tetraktys `(Φ, J, V, Σ)`, & Chiral Readout**:
   Realizes off-diagonal Dirac hopping as `genPhi`, tangent commutator as `genJ`,
   square gap + Berry curvature as `genV`, and sublattice-graded mass as `genSig = Γ_sub V`,
   proving `H² = even² + V + {even, Φ}`, `sublatticeSuperTrace V = 0`, and
   `sublatticeSuperTrace Σ = 4 • (K₁² + K₂² - K₃²)`.
4. **Stage 4 — Socratic Aporia (`idempotencyDefect`) & Recursive Defect Tower**:
   Establishes Peirce boundary aporia `evenGrade P (idempotencyDefect H) - idempotencyDefect (evenGrade P H) = V`,
   arbitrary-depth recursive `DefectTower` cycle splitting `idempotencyDefect^[k] V`,
   non-Abelian `hexPlaquette` vison aporia conjugation covariance & central invariance,
   aporia-free fixed points for `majoranaPlusProj`/`majoranaMinusProj`/`fullDiracModeProj`,
   Newton–Peirce correction factorization, and `clTowerHom` + `ClTowerColimit` transport.
5. **Stage 5 — Bounded Acyclic Causal Poset (`SolveEtCoagulaStage`) & Master Coagulation**:
   Packages the strict hierarchical dependency order and unified theorem
   `kitaev_peirce_aporia_solve_et_coagula_synthesis`.

Scope: All declarations prove finite noncommutative matrix, Peirce-ring, finite
defect-iterate, and `RingCat`-colimit algebraic theorems over `[Ring B]`. They do not
establish physical continuum thermal Hall conductance, Kubo transport coefficients, or
experimental quantization plateaus.
-/

open Matrix
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
open InfoGeometry.Algebra.NoncommutativeInherentZornGaugeSynthesis
open InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis
open InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
open InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
open InfoGeometry.Algebra.NoncommutativeKitaevMajoranaThermalHallSynthesis

namespace InfoGeometry.Algebra.KitaevPeirceAporiaEpistemicSynthesis

/-! ## Stage 1: Primordial Binary Cut & Majorana / Spin Peirce Parity -/

section Stage1_PrimordialBinaryCut

variable {B : Type*} [Ring B]

/-- Sublattice `A` idempotent projection `P_A = diag(1, 0)` on `NestedMat B = M₂(M₂(B))`. -/
def sublatticeCut : NestedMat B :=
  mat2 (1 : Matrix (Fin 2) (Fin 2) B) 0 0 0

lemma sublatticeCut_idem : (sublatticeCut : NestedMat B) * sublatticeCut = sublatticeCut := by
  apply ext_fin2 <;> simp [sublatticeCut]

theorem sublatticeCut_complement_and_invS :
    (1 : NestedMat B) - sublatticeCut = mat2 0 0 0 (1 : Matrix (Fin 2) (Fin 2) B) ∧
    (sublatticeCut : NestedMat B) * (1 - sublatticeCut) = 0 ∧
    ((1 : NestedMat B) - sublatticeCut) * sublatticeCut = 0 ∧
    PeirceSpine.invS (sublatticeCut : NestedMat B) = sublatticeGamma := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [sublatticeCut]
  · calc
      (sublatticeCut : NestedMat B) * (1 - sublatticeCut)
          = sublatticeCut - sublatticeCut * sublatticeCut := by noncomm_ring
      _ = 0 := by rw [sublatticeCut_idem, sub_self]
  · calc
      ((1 : NestedMat B) - sublatticeCut) * sublatticeCut
          = sublatticeCut - sublatticeCut * sublatticeCut := by noncomm_ring
      _ = 0 := by rw [sublatticeCut_idem, sub_self]
  · apply ext_fin2 <;> simp [PeirceSpine.invS, sublatticeCut, sublatticeGamma]

/-- Characteristic-free non-commutativity witness in `NestedMat B`: the sublattice cut
fails to commute with the itinerant Majorana fermion `majC` over any nontrivial ring. -/
theorem sublatticeCut_majC_noncommuting [Nontrivial B] :
    (sublatticeCut : NestedMat B) * majC ≠ majC * sublatticeCut := by
  intro h
  have h0100 := congrArg (fun M : NestedMat B => M 0 1 0 0) h
  simp [sublatticeCut, majC, mat2] at h0100

set_option maxHeartbeats 0
/-- **Stage 1 (`KM₁` Peirce Grading Theorem)**: Under `P_A = sublatticeCut`, the itinerant
Majorana `majC`, first bond Majorana `majB1`, and spins `S₂, S₃` are purely odd, while
`majB2`, `majB3`, the gauge-fixing operator `kitaevGaugeD`, and `S₁` are purely even. -/
theorem kitaev_majorana_and_spin_peirce_parity :
    let P : NestedMat B := sublatticeCut
    evenGrade P majC = 0 ∧ oddGrade P majC = majC ∧
    evenGrade P majB1 = 0 ∧ oddGrade P majB1 = majB1 ∧
    oddGrade P majB2 = 0 ∧ evenGrade P majB2 = majB2 ∧
    oddGrade P majB3 = 0 ∧ evenGrade P majB3 = majB3 ∧
    oddGrade P kitaevGaugeD = 0 ∧ evenGrade P kitaevGaugeD = kitaevGaugeD ∧
    oddGrade P kitaevSpin1 = 0 ∧ evenGrade P kitaevSpin1 = kitaevSpin1 ∧
    evenGrade P kitaevSpin2 = 0 ∧ oddGrade P kitaevSpin2 = kitaevSpin2 ∧
    evenGrade P kitaevSpin3 = 0 ∧ oddGrade P kitaevSpin3 = kitaevSpin3 := by
  intro P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> apply ext_fin2 <;>
      simp [P, sublatticeCut, evenGrade, oddGrade,
        kitaevGaugeD, kitaevSpin1, kitaevSpin2, kitaevSpin3,
        majC, majB1, majB2, majB3, sigmaOp, omegaOp])
set_option maxHeartbeats 200000

end Stage1_PrimordialBinaryCut

/-! ## Stage 2: Fourfold Relational Peirce Corner Anatomy of `kitaevHoneycombH` -/

section Stage2_FourfoldPeirceAnatomy

variable {B : Type*} [Ring B]

/-- **Stage 2 (`KM₃` Fourfold Peirce Anatomy)**: The four Peirce corners `(peirce11, conePlus,
coneMinus, peirce00)` of `kitaevHoneycombH Δ_H K₁ K₂ K₃` under `sublatticeCut` isolate
the intra-sublattice Haldane masses `±fiberEmbed Δ_H` and inter-sublattice hopping `vecOp K`. -/
theorem kitaevHoneycombH_peirce_fourfold_anatomy (Δ_H K₁ K₂ K₃ : B) :
    let P : NestedMat B := sublatticeCut
    let H := kitaevHoneycombH Δ_H K₁ K₂ K₃
    PeirceSpine.peirce11 P H = mat2 (fiberEmbed Δ_H) 0 0 0 ∧
    PeirceSpine.conePlus P H = mat2 0 (vecOp K₁ K₂ K₃) 0 0 ∧
    PeirceSpine.coneMinus P H = mat2 0 0 (vecOp K₁ K₂ K₃) 0 ∧
    PeirceSpine.peirce00 P H = mat2 0 0 0 (-fiberEmbed Δ_H) ∧
    PeirceSpine.evenGrade P H = kitaevHoneycombH Δ_H 0 0 0 ∧
    PeirceSpine.oddGrade P H = kitaevHoneycombH 0 K₁ K₂ K₃ ∧
    PeirceSpine.peirce11 P H + PeirceSpine.conePlus P H +
      PeirceSpine.coneMinus P H + PeirceSpine.peirce00 P H = H := by
  intro P H
  have hcomp : (1 : NestedMat B) - P = mat2 0 0 0 (1 : Matrix (Fin 2) (Fin 2) B) :=
    (sublatticeCut_complement_and_invS (B := B)).1
  have hnegF : fiberEmbed (-Δ_H) = -fiberEmbed Δ_H := by
    apply ext_fin2 <;> simp [fiberEmbed]
  have hvec0 : vecOp (0 : B) 0 0 = 0 := by
    apply ext_fin2 <;> simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;>
      simp [P, H, PeirceSpine.peirce11, sublatticeCut, bareDiracZorn, diracZornOp, mat2]
  · apply ext_fin2 <;>
      simp [P, H, PeirceSpine.conePlus, sublatticeCut, bareDiracZorn,
        diracZornOp, mat2]
  · apply ext_fin2 <;>
      simp [P, H, PeirceSpine.coneMinus, sublatticeCut, bareDiracZorn,
        diracZornOp, mat2]
  · apply ext_fin2 <;>
      simp [P, H, PeirceSpine.peirce00, hcomp, hnegF, bareDiracZorn, diracZornOp, mat2]
  · apply ext_fin2 <;>
      simp [P, H, PeirceSpine.evenGrade, hvec0, sublatticeCut,
        bareDiracZorn, diracZornOp, mat2]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [P, H, PeirceSpine.oddGrade, sublatticeCut, kitaevHoneycombH, bareDiracZorn,
        diracZornOp, fiberEmbed, mat2]
  · calc
      PeirceSpine.peirce11 P H + PeirceSpine.conePlus P H +
          PeirceSpine.coneMinus P H + PeirceSpine.peirce00 P H
          = PeirceSpine.evenGrade P H + PeirceSpine.oddGrade P H := by
              simp only [PeirceSpine.peirce11, PeirceSpine.conePlus,
                PeirceSpine.coneMinus, PeirceSpine.peirce00,
                PeirceSpine.evenGrade, PeirceSpine.oddGrade]
              abel
      _ = H := (grade_projection_laws (sublatticeCut_idem (B := B)) H).2.2.2.2

end Stage2_FourfoldPeirceAnatomy

/-! ## Stage 3: Transcendent Tetraktys `(Φ, J, V, Σ)` & Chiral Supertrace Readout -/

section Stage3_TranscendentTetraktys

variable {B : Type*} [Ring B]

/-- **Stage 3 (`KM₃` Tetraktys & Chiral Readout)**: Compiles the Kitaev Dirac–Zorn
Hamiltonian `H` into the Peirce Tetraktys `(Φ, J, V, Σ)`, deriving the universal
unconditional square decomposition and distinguishing `sublatticeSuperTrace V = 0` from
the Zorn gap/norm channel `sublatticeSuperTrace Σ = 4 • (K₁² + K₂² - K₃²)`. -/
theorem kitaevHoneycombH_tetraktys_and_chiral_readout (Δ_H K₁ K₂ K₃ : B) :
    let P : NestedMat B := sublatticeCut
    let H := kitaevHoneycombH Δ_H K₁ K₂ K₃
    let V_block : Matrix (Fin 2) (Fin 2) B :=
      fiberEmbed (K₁ * K₁ + K₂ * K₂ - K₃ * K₃) + vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆)
    genPhi P H H = kitaevHoneycombH 0 K₁ K₂ K₃ ∧
    genJ P H H = PeirceSpine.comm P H ∧
    genJ P H H = mat2 0 (vecOp K₁ K₂ K₃) (-vecOp K₁ K₂ K₃) 0 ∧
    genV P H H = mat2 V_block 0 0 V_block ∧
    genSig P H H = sublatticeGamma * genV P H H ∧
    genSig P H H = mat2 V_block 0 0 (-V_block) ∧
    H * H = evenGrade P H * evenGrade P H + genV P H H +
      PeirceSpine.anticomm (evenGrade P H) (genPhi P H H) ∧
    sublatticeSuperTrace (genV P H H) = 0 ∧
    sublatticeSuperTrace (genSig P H H) = 4 • (K₁ * K₁ + K₂ * K₂ - K₃ * K₃) := by
  intro P H V_block
  have hP : P * P = P := sublatticeCut_idem
  have hPhi : genPhi P H H = kitaevHoneycombH 0 K₁ K₂ K₃ := by
    have h4 := kitaevHoneycombH_peirce_fourfold_anatomy Δ_H K₁ K₂ K₃
    dsimp [P, H] at h4 ⊢
    change conePlus P H + coneMinus P H = kitaevHoneycombH 0 K₁ K₂ K₃
    rw [h4.2.1, h4.2.2.1]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [kitaevHoneycombH, bareDiracZorn, diracZornOp, fiberEmbed, mat2]
  have hJ_comm : genJ P H H = PeirceSpine.comm P H := by
    change P * H * (1 - P) - (1 - P) * H * P = P * H - H * P
    noncomm_ring
  have hJ_mat : genJ P H H = mat2 0 (vecOp K₁ K₂ K₃) (-vecOp K₁ K₂ K₃) 0 := by
    have h4 := kitaevHoneycombH_peirce_fourfold_anatomy Δ_H K₁ K₂ K₃
    dsimp [P, H] at h4 ⊢
    rw [hJ_comm]
    calc
      PeirceSpine.comm P H = conePlus P H - coneMinus P H := by
        change P * H - H * P = P * H * (1 - P) - (1 - P) * H * P
        noncomm_ring
      _ = mat2 0 (vecOp K₁ K₂ K₃) (-vecOp K₁ K₂ K₃) 0 := by
        rw [h4.2.1, h4.2.2.1]
        apply ext_fin2 <;> apply ext_fin2 <;> simp [mat2]
  have h_vec_sq : vecOp K₁ K₂ K₃ * vecOp K₁ K₂ K₃ = V_block :=
    (zorn_vector_product_dot_plus_cross 0 0 0 0 0 0 K₁ K₂ K₃).2
  have hV_mat : genV P H H = mat2 V_block 0 0 V_block := by
    have h4 := kitaevHoneycombH_peirce_fourfold_anatomy Δ_H K₁ K₂ K₃
    dsimp [P, H] at h4 ⊢
    change anticomm (conePlus P H) (coneMinus P H) = mat2 V_block 0 0 V_block
    unfold anticomm
    rw [h4.2.1, h4.2.2.1]
    apply ext_fin2 <;> simp [h_vec_sq]
  have hSig_gamma : genSig P H H = sublatticeGamma * genV P H H := by
    have hinv := (sublatticeCut_complement_and_invS (B := B)).2.2.2
    have hA3 := (archetype_A3_nilpotent_cones_and_tetraktys_table hP H H).2.2.2.2.2.2.2.2.1
    change genSig P H H = sublatticeGamma * genV P H H
    rw [← hinv]
    exact hA3
  have hSig_mat : genSig P H H = mat2 V_block 0 0 (-V_block) := by
    rw [hSig_gamma, hV_mat]
    apply ext_fin2 <;> simp [sublatticeGamma]
  have hSq : H * H = evenGrade P H * evenGrade P H + genV P H H +
      PeirceSpine.anticomm (evenGrade P H) (genPhi P H H) := by
    have h_decomp : H = evenGrade P H + oddGrade P H :=
      (grade_projection_laws hP H).2.2.2.2.symm
    have h_odd_eq : oddGrade P H = genPhi P H H := rfl
    have h_odd_sq : oddGrade P H * oddGrade P H = genV P H H :=
      oddGrade_square_eq_genV P H hP
    calc
      H * H = (evenGrade P H + oddGrade P H) * (evenGrade P H + oddGrade P H) := by
          conv_lhs => rw [h_decomp]
      _ = evenGrade P H * evenGrade P H + oddGrade P H * oddGrade P H +
            (evenGrade P H * oddGrade P H + oddGrade P H * evenGrade P H) := by
          noncomm_ring
      _ = evenGrade P H * evenGrade P H + genV P H H +
            PeirceSpine.anticomm (evenGrade P H) (genPhi P H H) := by
          rw [h_odd_sq, ← h_odd_eq]
          rfl
  have hTrV : sublatticeSuperTrace (genV P H H) = 0 := by
    rw [hV_mat]
    simp [sublatticeSuperTrace]
  have hTrSig : sublatticeSuperTrace (genSig P H H) = 4 • (K₁ * K₁ + K₂ * K₂ - K₃ * K₃) := by
    rw [hSig_mat]
    dsimp [sublatticeSuperTrace, V_block]
    simp only [trace_fin2, mat2_00, mat2_11, Matrix.neg_apply, Matrix.add_apply, fiberEmbed,
      vecOp_00, vecOp_11]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    noncomm_ring
  exact ⟨hPhi, hJ_comm, hJ_mat, hV_mat, hSig_gamma, hSig_mat, hSq, hTrV, hTrSig⟩

end Stage3_TranscendentTetraktys

/-! ## Stage 4: Socratic Aporia (`idempotencyDefect`) & Recursive Defect Tower -/

section Stage4_SocraticAporiaTower

universe u

/-- **Stage 4A (`KM₃` Boundary Aporia & Defect-Tower Split)**: Pinching the idempotency
defect of `kitaevHoneycombH` differs from the pinched defect by `genV`, whose entire
recursive defect orbit `idempotencyDefect^[k]` splits additively over the orthogonal
Peirce cycles `qgtPlus` and `qgtMinus`. -/
theorem kitaevHoneycombH_aporia_and_defect_tower
    {B : Type*} [Ring B] (Δ_H K₁ K₂ K₃ : B) (k : ℕ) :
    let P : NestedMat B := sublatticeCut
    let H := kitaevHoneycombH Δ_H K₁ K₂ K₃
    evenGrade P (idempotencyDefect H) - idempotencyDefect (evenGrade P H) = genV P H H ∧
    PeirceSpine.peirce11 P (idempotencyDefect H) -
      idempotencyDefect (PeirceSpine.peirce11 P H) = qgtPlus P H H ∧
    idempotencyDefect^[k] (genV P H H) =
      idempotencyDefect^[k] (qgtPlus P H H) + idempotencyDefect^[k] (qgtMinus P H H) := by
  intro P H
  have hP : P * P = P := sublatticeCut_idem
  exact ⟨even_idempotencyDefect_sub P H hP,
    peirce11_idempotencyDefect_sub P H hP,
    genV_defect_iterates_cycle_split hP H H k⟩

/-- **Stage 4B (`KM₂` Non-Abelian Vison Aporia Covariance)**: Over ANY noncommutative ring `R`,
every finite iterate `idempotencyDefect^[k]` of the hexagonal plaquette operator `hexPlaquette`
transforms by basepoint conjugation `g₁ · (-) · g₁⁻¹` under arbitrary local vertex gauge
transformations `linkGauge gᵢ gⱼ Uᵢⱼ`, without any centrality assumption. -/
theorem hexagonal_vison_aporia_iterate_covariance
    {R : Type*} [Ring R]
    (g₁ g₂ g₃ g₄ g₅ g₆ : Rˣ) (U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁ : R) (k : ℕ) :
    let W_g := hexPlaquette
      (linkGauge g₁ g₂ U₁₂) (linkGauge g₂ g₃ U₂₃) (linkGauge g₃ g₄ U₃₄)
      (linkGauge g₄ g₅ U₄₅) (linkGauge g₅ g₆ U₅₆) (linkGauge g₆ g₁ U₆₁)
    let W_0 := hexPlaquette U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁
    idempotencyDefect^[k] W_g = (g₁ : R) * idempotencyDefect^[k] W_0 * (↑g₁⁻¹ : R) := by
  intro W_g W_0
  have h2 : (↑g₂⁻¹ : R) * (g₂ : R) = 1 := Units.inv_mul g₂
  have h3 : (↑g₃⁻¹ : R) * (g₃ : R) = 1 := Units.inv_mul g₃
  have h4 : (↑g₄⁻¹ : R) * (g₄ : R) = 1 := Units.inv_mul g₄
  have h5 : (↑g₅⁻¹ : R) * (g₅ : R) = 1 := Units.inv_mul g₅
  have h6 : (↑g₆⁻¹ : R) * (g₆ : R) = 1 := Units.inv_mul g₆
  have h_cov : W_g = (g₁ : R) * W_0 * (↑g₁⁻¹ : R) := by
    dsimp [W_g, W_0, hexPlaquette, linkGauge]
    calc (g₁ : R) * U₁₂ * (↑g₂⁻¹ : R) * ((g₂ : R) * U₂₃ * (↑g₃⁻¹ : R)) *
         ((g₃ : R) * U₃₄ * (↑g₄⁻¹ : R)) * ((g₄ : R) * U₄₅ * (↑g₅⁻¹ : R)) *
         ((g₅ : R) * U₅₆ * (↑g₆⁻¹ : R)) * ((g₆ : R) * U₆₁ * (↑g₁⁻¹ : R))
      _ = (g₁ : R) * U₁₂ * ((↑g₂⁻¹ : R) * (g₂ : R)) * U₂₃ * ((↑g₃⁻¹ : R) * (g₃ : R)) *
          U₃₄ * ((↑g₄⁻¹ : R) * (g₄ : R)) * U₄₅ * ((↑g₅⁻¹ : R) * (g₅ : R)) *
          U₅₆ * ((↑g₆⁻¹ : R) * (g₆ : R)) * U₆₁ * (↑g₁⁻¹ : R) := by noncomm_ring
      _ = (g₁ : R) * (U₁₂ * U₂₃ * U₃₄ * U₄₅ * U₅₆ * U₆₁) * (↑g₁⁻¹ : R) := by
          rw [h2, h3, h4, h5, h6]; noncomm_ring
  have h_inter : W_g * (g₁ : R) = (g₁ : R) * W_0 := by
    rw [h_cov, mul_assoc ((g₁ : R) * W_0), Units.inv_mul, mul_one]
  have h_iter := idempotencyDefect_iterates_intertwines h_inter k
  calc
    idempotencyDefect^[k] W_g
        = idempotencyDefect^[k] W_g * ((g₁ : R) * (↑g₁⁻¹ : R)) := by
            rw [Units.mul_inv, mul_one]
    _ = (idempotencyDefect^[k] W_g * (g₁ : R)) * (↑g₁⁻¹ : R) := by rw [mul_assoc]
    _ = ((g₁ : R) * idempotencyDefect^[k] W_0) * (↑g₁⁻¹ : R) := by rw [h_iter]
    _ = (g₁ : R) * idempotencyDefect^[k] W_0 * (↑g₁⁻¹ : R) := rfl

/-- When the basepoint gauge sign `g₁` is central (e.g., `ℤ₂` flux gauge sign), every
recursive aporia iterate `idempotencyDefect^[k] W_g` is strictly gauge-invariant. -/
theorem hexagonal_vison_aporia_iterate_central_invariance
    {R : Type*} [Ring R]
    (g₁ g₂ g₃ g₄ g₅ g₆ : Rˣ) (U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁ : R)
    (hg₁_cent : ∀ X : R, (g₁ : R) * X = X * (g₁ : R)) (k : ℕ) :
    idempotencyDefect^[k] (hexPlaquette
      (linkGauge g₁ g₂ U₁₂) (linkGauge g₂ g₃ U₂₃) (linkGauge g₃ g₄ U₃₄)
      (linkGauge g₄ g₅ U₄₅) (linkGauge g₅ g₆ U₅₆) (linkGauge g₆ g₁ U₆₁)) =
      idempotencyDefect^[k] (hexPlaquette U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁) := by
  have h := hexagonal_vison_aporia_iterate_covariance g₁ g₂ g₃ g₄ g₅ g₆ U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁ k
  rw [h, hg₁_cent _, mul_assoc, Units.mul_inv, mul_one]

/-- The Zorn–Clifford triad plaquette `hexPlaquette gamma1Op sigmaOp omegaOp ...` is
aporia-free (`idempotencyDefect = 0`). -/
theorem zorn_triad_hexPlaquette_aporia_zero {B : Type u} [Ring B] :
    idempotencyDefect (hexPlaquette (gamma1Op : Matrix (Fin 2) (Fin 2) B) sigmaOp omegaOp
      gamma1Op sigmaOp omegaOp) = 0 := by
  have h1 : hexPlaquette (gamma1Op : Matrix (Fin 2) (Fin 2) B) sigmaOp omegaOp
      gamma1Op sigmaOp omegaOp = 1 := (KreinPeirceTowerIntertwine.hexPlaquette_eq_kitaevPlaquette6).2
  rw [h1]
  simp [idempotencyDefect]

/-- **Stage 4C (`KM₄` Aporia-Free Chiral Fixed Points & `ClTowerColimit` Transport)**:
Every chiral Majorana mode projection `majoranaPlusProj n`, `majoranaMinusProj n`, and
`fullDiracModeProj n` has vanishing idempotency defect and is fixed by `newtonPeirceStep`;
arbitrary elements obey the cubic Newton–Peirce defect contraction law and transport
their full recursive `idempotencyDefect^[k]` orbits along `clTowerHom` and into the
native Mathlib `RingCat` colimit `ClTowerColimit B`. -/
theorem chiral_majorana_aporia_fixed_points_and_colimit_transport
    {B : Type u} [Ring B] {m n : ℕ} (h : m ≤ n) (X : ClTower B m) (k : ℕ) :
    idempotencyDefect (majoranaPlusProj (B := B) n) = 0 ∧
    idempotencyDefect (majoranaMinusProj (B := B) n) = 0 ∧
    idempotencyDefect (fullDiracModeProj (B := B) n) = 0 ∧
    newtonPeirceStep (majoranaPlusProj (B := B) n) = majoranaPlusProj (B := B) n ∧
    newtonPeirceStep (majoranaMinusProj (B := B) n) = majoranaMinusProj (B := B) n ∧
    idempotencyDefect (newtonPeirceStep X) =
      idempotencyDefect X * idempotencyDefect X * (4 * idempotencyDefect X - 3) ∧
    clTowerHom B h (idempotencyDefect^[k] X) = idempotencyDefect^[k] (clTowerHom B h X) ∧
    (CategoryTheory.Limits.colimit.ι (clTowerFunctor B) n).hom
        (idempotencyDefect^[k] (clTowerHom B h X)) =
      idempotencyDefect^[k] ((CategoryTheory.Limits.colimit.ι (clTowerFunctor B) m).hom X) := by
  rcases all_scales_chiral_projection_trace_split (B := B) n with
    ⟨_, hp2, hm2, _, _, hd2, _, _, _, _⟩
  refine ⟨idempotencyDefect_eq_zero_iff.mpr hp2,
    idempotencyDefect_eq_zero_iff.mpr hm2,
    idempotencyDefect_eq_zero_iff.mpr hd2,
    newtonPeirceStep_eq_self_of_idempotent hp2,
    newtonPeirceStep_eq_self_of_idempotent hm2,
    idempotencyDefect_newtonPeirceStep X,
    map_idempotencyDefect_iterates (clTowerHom B h) X k, ?_⟩
  rw [map_idempotencyDefect_iterates
      ((CategoryTheory.Limits.colimit.ι (clTowerFunctor B) n).hom)
      (clTowerHom B h X) k,
    clTowerColimit_ι_comp h X]

end Stage4_SocraticAporiaTower

/-! ## Stage 5: Bounded Acyclic Causal Poset & Master `Solve et Coagula` Synthesis -/

section Stage5_CausalPosetAndCoagulation

/-- Five epistemic stages of noncommutative `solve et coagula` compilation for
`KM₁`–`KM₄`. -/
inductive SolveEtCoagulaStage : Type
  | primordialCut
  | fourfoldAnatomy
  | transcendentTetraktys
  | socraticAporiaTower
  | masterCoagulation
  deriving DecidableEq, Repr

/-- Strictly monotone rank embedding `SolveEtCoagulaStage → ℕ`. -/
def solveEtCoagulaRank : SolveEtCoagulaStage → ℕ
  | .primordialCut => 0
  | .fourfoldAnatomy => 1
  | .transcendentTetraktys => 2
  | .socraticAporiaTower => 3
  | .masterCoagulation => 4

lemma solveEtCoagulaRank_injective : Function.Injective solveEtCoagulaRank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : PartialOrder SolveEtCoagulaStage :=
  PartialOrder.lift solveEtCoagulaRank solveEtCoagulaRank_injective

instance : DecidableLE SolveEtCoagulaStage := fun a b =>
  inferInstanceAs (Decidable (solveEtCoagulaRank a ≤ solveEtCoagulaRank b))

instance : DecidableLT SolveEtCoagulaStage := fun a b =>
  inferInstanceAs (Decidable (solveEtCoagulaRank a < solveEtCoagulaRank b))

/-- Strict causal chain & acyclicity across the 5 `SolveEtCoagulaStage` phases. -/
theorem solveEtCoagulaStage_causal_chain_and_acyclic :
    SolveEtCoagulaStage.primordialCut < SolveEtCoagulaStage.fourfoldAnatomy ∧
    SolveEtCoagulaStage.fourfoldAnatomy < SolveEtCoagulaStage.transcendentTetraktys ∧
    SolveEtCoagulaStage.transcendentTetraktys < SolveEtCoagulaStage.socraticAporiaTower ∧
    SolveEtCoagulaStage.socraticAporiaTower < SolveEtCoagulaStage.masterCoagulation ∧
    ∀ s₁ s₂ : SolveEtCoagulaStage, ¬ (s₁ < s₂ ∧ s₂ < s₁) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro s₁ s₂ h
  exact lt_asymm h.1 h.2

/-- **Master `Solve et Coagula` Epistemic Synthesis (`KM₁`–`KM₄` × Peirce–Tetraktys–Aporia)**:
Unites 4-Majorana three-spin fractionalization (`S₁ S₂ S₃ = -D`), Peirce parity grading
of `kitaevGaugeD`, fourfold Dirac–Zorn block decomposition of `kitaevHoneycombH`,
Tetraktys chiral trace readout (`Str(V) = 0` vs. `Str(Σ) = 4 • (K₁² + K₂² - K₃²)`),
Socratic aporia boundary jump & `DefectTower` orbit splitting, and aporia-free
chiral Majorana projection trace half-splitting on `ClTower B (n + 1)`. -/
theorem kitaev_peirce_aporia_solve_et_coagula_synthesis
    {B : Type u} [Ring B] (Δ_H K₁ K₂ K₃ : B) (n k : ℕ) :
    let P : NestedMat B := sublatticeCut
    let H := kitaevHoneycombH Δ_H K₁ K₂ K₃
    let M_plus := majoranaPlusProj (B := B) n
    let D_full := fullDiracModeProj (B := B) n
    (kitaevSpin1 : NestedMat B) * kitaevSpin2 * kitaevSpin3 = -kitaevGaugeD ∧
    oddGrade P (kitaevGaugeD : NestedMat B) = 0 ∧
    evenGrade P H + oddGrade P H = H ∧
    genPhi P H H = kitaevHoneycombH 0 K₁ K₂ K₃ ∧
    sublatticeSuperTrace (genV P H H) = 0 ∧
    sublatticeSuperTrace (genSig P H H) = 4 • (K₁ * K₁ + K₂ * K₂ - K₃ * K₃) ∧
    evenGrade P (idempotencyDefect H) - idempotencyDefect (evenGrade P H) = genV P H H ∧
    idempotencyDefect^[k] (genV P H H) =
      idempotencyDefect^[k] (qgtPlus P H H) + idempotencyDefect^[k] (qgtMinus P H H) ∧
    idempotencyDefect M_plus = 0 ∧
    2 • towerTrace M_plus = towerTrace D_full := by
  intro P H M_plus D_full
  have hkm1 := (kitaev_majorana_fractionalization_and_three_spin_identity (B := B)).2.2.2.2.2.2.2
  have hparity := (kitaev_majorana_and_spin_peirce_parity (B := B)).2.2.2.2.2.2.2.2.1
  have hdecomp := (grade_projection_laws (sublatticeCut_idem (B := B)) H).2.2.2.2
  have htet := kitaevHoneycombH_tetraktys_and_chiral_readout Δ_H K₁ K₂ K₃
  have hap := kitaevHoneycombH_aporia_and_defect_tower Δ_H K₁ K₂ K₃ k
  have hkm4 := all_scales_chiral_projection_trace_split (B := B) n
  exact ⟨hkm1, hparity, hdecomp, htet.1, htet.2.2.2.2.2.2.2.1,
    htet.2.2.2.2.2.2.2.2, hap.1, hap.2.2,
    idempotencyDefect_eq_zero_iff.mpr hkm4.2.1, hkm4.2.2.2.2.2.2.2.2.2⟩

end Stage5_CausalPosetAndCoagulation

end InfoGeometry.Algebra.KitaevPeirceAporiaEpistemicSynthesis
