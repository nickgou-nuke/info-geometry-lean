import Mathlib
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.TowerMatrix

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.CliffordDirectColimit

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

variable {𝕜 : Type} [Field 𝕜] [CharZero 𝕜]

/-- Matrix algebra at stage `n` representing the finite Clifford algebra `Cl(2n, ℂ)`. -/
abbrev CliffordStage (𝕜 : Type) [Field 𝕜] (n : ℕ) : Type :=
  Matrix (Fin (2^n)) (Fin (2^n)) 𝕜

/-- Algebra isomorphism between the standard Clifford stage and the Cl(1,1)^⊗n tower stage (for 𝕜 = ℝ). -/
noncomputable def cliffordStageEquivTower (n : ℕ) :
    CliffordStage ℝ n ≃ₐ[ℝ] MatStage n := by
  haveI : Fintype (Idx n) := inferInstance
  haveI : DecidableEq (Idx n) := inferInstance
  -- Use the reindexing equivalence from TowerMatrix
  have h : Matrix (Fin (2^n)) (Fin (2^n)) ℝ ≃ₐ[ℝ] Matrix (Idx n) (Idx n) ℝ :=
    Matrix.reindexAlgEquiv ℝ ℝ (Fintype.equivFinOfCardEq (by
      simp [Idx, Fintype.card_fin, Fintype.card_prod, pow_succ, Nat.mul_comm]))
  exact h

/-- The Clifford inclusion matches the Cl(1,1) tower embedding under the stage isomorphism. -/
theorem cliffordEmbed_matches_towerEmbed (n : ℕ) (A : CliffordStage ℝ n) :
    (cliffordStageEquivTower (n + 1)) (cliffordEmbedSucc n A) =
      matStageEmbed n ((cliffordStageEquivTower n) A) := by
  -- Both embeddings implement A ↦ diag(A, A) = A ⊗ I₂
  -- The equivalence reindexes Fin (2^n) to Idx n
  -- Under this reindexing, the block-diagonal structure is preserved
  ext i j
  simp [cliffordEmbedSucc, cliffordStageEquivTower, matStageEmbed, Matrix.reindexAlgEquiv_apply,
    Fin.sum_univ_succ, Idx, Fintype.card_fin, Fintype.card_prod, pow_succ]
  <;>
  (try { aesop }) <;>
  (try {
    rcases i with (i₁, i₂) <;> rcases j with (j₁, j₂) <;>
    simp_all [Matrix.mul_apply, Fin.sum_univ_succ, Idx, Fintype.card_fin, Fintype.card_prod, pow_succ]
    <;>
    (try { aesop }) <;>
    (try { ring_nf }) <;>
    (try { norm_num }) <;>
    (try { split_ifs <;> simp_all }) <;>
    (try { aesop })
  }) <;>
  (try {
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp_all [Matrix.mul_apply, Fin.sum_univ_succ, Idx, Fintype.card_fin, Fintype.card_prod, pow_succ]
    <;>
    (try { aesop }) <;>
    (try { ring_nf }) <;>
    (try { norm_num }) <;>
    (try { split_ifs <;> simp_all }) <;>
    (try { aesop })
  })

/-- The Clifford sequence matches the tensor tower sequence under the isomorphism. -/
theorem cliffordSeq_matches_towerSeq (n m : ℕ) (A : CliffordStage ℝ n) :
    (cliffordStageEquivTower (n + m)) (cliffordSeq n m A) =
      (bondMap (fun n => matStageEmbed n) n m) ((cliffordStageEquivTower n) A) := by
  have h : ∀ m : ℕ, (cliffordStageEquivTower (n + m)) (cliffordSeq n m A) =
      (bondMap (fun n => matStageEmbed n) n m) ((cliffordStageEquivTower n) A) := by
    intro m
    induction m with
    | zero =>
      simp [cliffordSeq, bondMap]
    | succ m ih =>
      rw [cliffordSeq, bondMap]
      simp_all [cliffordEmbed_matches_towerEmbed, Function.comp_apply]
      <;>
      simp_all [Matrix.reindexAlgEquiv_apply]
      <;>
      aesop
  exact h m

/-- Boundary Majorana mode at stage 1 corresponds to the first tensor factor in Cl(1,1)^⊗n. -/
noncomputable def boundaryMajoranaAtStage (n : ℕ) : MatStage n :=
  (cliffordStageEquivTower n) (cliffordSeq 1 n (!![(0 : ℝ), 1; 1, 0]))

/-- The boundary Majorana factors out as a tensor factor: Cl(1,1) ⊗ I_{2^{n-1}} in Cl(1,1)^⊗n. -/
theorem boundaryMajorana_tensorFactorization (n : ℕ) :
    boundaryMajoranaAtStage (n + 1) =
      boundaryMajoranaAtStage 1 ⊗ₖ (1 : MatStage n) := by
  have h₁ : boundaryMajoranaAtStage (n + 1) =
      (cliffordStageEquivTower (n + 1)) (cliffordSeq 1 (n + 1) (!![(0 : ℝ), 1; 1, 0])) := rfl
  have h₂ : boundaryMajoranaAtStage 1 =
      (cliffordStageEquivTower 1) (cliffordSeq 1 1 (!![(0 : ℝ), 1; 1, 0])) := rfl
  rw [h₁, h₂]
  -- Use the fact that cliffordSeq matches towerSeq and the tower embedding is A ⊗ I₂
  have h₃ : (cliffordStageEquivTower (1 + n)) (cliffordSeq 1 (1 + n) (!![(0 : ℝ), 1; 1, 0])) =
      (bondMap (fun n => matStageEmbed n) 1 n) ((cliffordStageEquivTower 1) (!![(0 : ℝ), 1; 1, 0])) := by
    have h₄ := cliffordSeq_matches_towerSeq 1 n (!![(0 : ℝ), 1; 1, 0])
    simpa [add_assoc] using h₄
  rw [h₃]
  -- The bondMap of matStageEmbed from 1 to 1+n is exactly the tensor product with I_{2^n}
  simp [bondMap, matStageEmbed]
  <;>
  simp_all [Matrix.one_mul, Matrix.mul_one]
  <;>
  aesop

end InfoGeometry.Canonical.CliffordDirectColimit