import Mathlib
import proofs.ZornCore
import proofs.StructureTensor

noncomputable section

open Matrix ZornCore

def projector (n : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (dotProduct n n)⁻¹ • vecMulVec n n

theorem normalized_outer_idempotent
    (n : Fin 2 → ℝ)
    (hn : dotProduct n n ≠ 0) :
    projector n * projector n = projector n := by
  ext i j
  dsimp [projector, vecMulVec, Matrix.mul_apply, smul_apply]
  have h_sum : ∑ k : Fin 2, n k * n k = dotProduct n n := rfl
  calc
    ∑ k : Fin 2, ((dotProduct n n)⁻¹ * (n i * n k)) * ((dotProduct n n)⁻¹ * (n k * n j))
      = ∑ k : Fin 2, ((dotProduct n n)⁻¹ * (dotProduct n n)⁻¹ * n i * n j) * (n k * n k) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ((dotProduct n n)⁻¹ * (dotProduct n n)⁻¹ * n i * n j) * (∑ k : Fin 2, n k * n k) := by
        rw [← Finset.mul_sum]
    _ = ((dotProduct n n)⁻¹ * (dotProduct n n)⁻¹ * n i * n j) * dotProduct n n := by
        rw [h_sum]
    _ = (dotProduct n n)⁻¹ * (n i * n j) := by
        calc
          ((dotProduct n n)⁻¹ * (dotProduct n n)⁻¹ * n i * n j) * dotProduct n n
            = (dotProduct n n)⁻¹ * ((dotProduct n n)⁻¹ * dotProduct n n) * (n i * n j) := by ring
          _ = (dotProduct n n)⁻¹ * 1 * (n i * n j) := by rw [inv_mul_cancel₀ hn]
          _ = (dotProduct n n)⁻¹ * (n i * n j) := by ring

theorem peirce_decomposition_symm_two
    (p : Matrix (Fin 2) (Fin 2) ℝ)
    (hp_symm : pᵀ = p)
    (hp_idem : p * p = p) :
    ∀ A : Matrix (Fin 2) (Fin 2) ℝ, Aᵀ = A →
      A =
        p * A * p +
        (1 - p) * A * (1 - p) +
        p * A * (1 - p) +
        (1 - p) * A * p := by
  intro A _
  have h1 : p + (1 - p) = 1 := by
    ext i j
    simp [Matrix.add_apply, Matrix.sub_apply]
  calc A = 1 * A * 1 := by simp
       _ = (p + (1 - p)) * A * (p + (1 - p)) := by rw [h1]
       _ = p * A * p + (1 - p) * A * (1 - p) + p * A * (1 - p) + (1 - p) * A * p := by
         ext i j
         simp [add_mul, sub_mul, mul_add, mul_sub]
         ring

theorem collinear_structureTensor_mem_peirceOne
    (n : Fin 2 → ℝ)
    (hn : dotProduct n n ≠ 0)
    (α : ℝ) :
    let p := projector n
    let J := α • vecMulVec n n
    p * J * p = J := by
  intros p J
  have hp_idem := normalized_outer_idempotent n hn
  have h_J : J = (α * dotProduct n n) • p := by
    ext i j
    change α * (n i * n j) = (α * dotProduct n n) * ((dotProduct n n)⁻¹ * (n i * n j))
    calc
      α * (n i * n j) = α * (1 * (n i * n j)) := by ring
      _ = α * ((dotProduct n n * (dotProduct n n)⁻¹) * (n i * n j)) := by rw [mul_inv_cancel₀ hn]
      _ = (α * dotProduct n n) * ((dotProduct n n)⁻¹ * (n i * n j)) := by ring
  calc
    p * J * p
      = p * ((α * dotProduct n n) • p) * p := by rw [h_J]
    _ = (α * dotProduct n n) • (p * p * p) := by
        simp [Matrix.mul_smul, Matrix.smul_mul, mul_assoc]
    _ = (α * dotProduct n n) • p := by
        rw [hp_idem, hp_idem]
    _ = J := h_J.symm

def zornLineEmbed
    (e : Vec3)
    (he : dot e e = 1) :
    Matrix (Fin 2) (Fin 2) ℝ → ZornCore.Zorn :=
  fun A => ⟨A 0 0, A 0 1 • e, A 1 0 • e, A 1 1⟩

def zornOne : Zorn := ⟨1, 0, 0, 1⟩

theorem zornLineEmbed_one (e : Vec3) (he : dot e e = 1) :
    zornLineEmbed e he 1 = zornOne := by
  apply ZornCore.Zorn.ext'
  · rfl
  · ext i; simp [zornLineEmbed, zornOne, Matrix.one_apply]
  · ext i; simp [zornLineEmbed, zornOne, Matrix.one_apply]
  · rfl

theorem zornLineEmbed_injective (e : Vec3) (he : dot e e = 1) :
    Function.Injective (zornLineEmbed e he) := by
  intro A B h
  have h00 : A 0 0 = B 0 0 := congr_arg ZornCore.Zorn.a h
  have h01_eq : A 0 1 • e = B 0 1 • e := congr_arg ZornCore.Zorn.u h
  have h10_eq : A 1 0 • e = B 1 0 • e := congr_arg ZornCore.Zorn.v h
  have h11 : A 1 1 = B 1 1 := congr_arg ZornCore.Zorn.b h
  have h01 : A 0 1 = B 0 1 := by
    have hd : ZornCore.dot (A 0 1 • e) e = ZornCore.dot (B 0 1 • e) e := by rw [h01_eq]
    dsimp [ZornCore.dot, smul_apply] at hd
    have hd2 : A 0 1 * ∑ i, e i * e i = B 0 1 * ∑ i, e i * e i := by
      calc A 0 1 * ∑ i, e i * e i = ∑ i, (A 0 1 * e i) * e i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
           _ = ZornCore.dot (A 0 1 • e) e := rfl
           _ = ZornCore.dot (B 0 1 • e) e := hd
           _ = ∑ i, (B 0 1 * e i) * e i := rfl
           _ = B 0 1 * ∑ i, e i * e i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    change A 0 1 * ZornCore.dot e e = B 0 1 * ZornCore.dot e e at hd2
    rw [he, mul_one, mul_one] at hd2
    exact hd2
  have h10 : A 1 0 = B 1 0 := by
    have hd : ZornCore.dot (A 1 0 • e) e = ZornCore.dot (B 1 0 • e) e := by rw [h10_eq]
    dsimp [ZornCore.dot, smul_apply] at hd
    have hd2 : A 1 0 * ∑ i, e i * e i = B 1 0 * ∑ i, e i * e i := by
      calc A 1 0 * ∑ i, e i * e i = ∑ i, (A 1 0 * e i) * e i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
           _ = ZornCore.dot (A 1 0 • e) e := rfl
           _ = ZornCore.dot (B 1 0 • e) e := hd
           _ = ∑ i, (B 1 0 * e i) * e i := rfl
           _ = B 1 0 * ∑ i, e i * e i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    change A 1 0 * ZornCore.dot e e = B 1 0 * ZornCore.dot e e at hd2
    rw [he, mul_one, mul_one] at hd2
    exact hd2
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem zornLineEmbed_norm_eq_det (e : Vec3) (he : dot e e = 1)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ZornCore.det (zornLineEmbed e he A) = Matrix.det A := by
  dsimp [ZornCore.det, zornLineEmbed]
  have h_dot : ZornCore.dot (A 0 1 • e) (A 1 0 • e) = A 0 1 * A 1 0 * ZornCore.dot e e := by
    dsimp [ZornCore.dot, smul_apply]
    calc
      ∑ i, (A 0 1 * e i) * (A 1 0 * e i)
        = ∑ i, (A 0 1 * A 1 0) * (e i * e i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = (A 0 1 * A 1 0) * ∑ i, e i * e i := by rw [← Finset.mul_sum]
  rw [h_dot, he, mul_one]
  rw [Matrix.det_fin_two]

theorem zornLineEmbed_null_iff (e : Vec3) (he : dot e e = 1)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ZornCore.det (zornLineEmbed e he A) = 0 ↔ Matrix.det A = 0 := by
  rw [zornLineEmbed_norm_eq_det e he A]

theorem cross_smul_smul (c d : ℝ) (u v : Vec3) : cross (c • u) (d • v) = (c * d) • cross u v := by
  ext i
  fin_cases i <;> simp [cross, smul_apply] <;> ring

theorem zornLineEmbed_mul
    (e : Vec3)
    (he : dot e e = 1)
    (hx : cross e e = 0)
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    zornLineEmbed e he (A * B) = zornLineEmbed e he A * zornLineEmbed e he B := by
  apply ZornCore.Zorn.ext'
  · dsimp [zornLineEmbed, Matrix.mul_apply]
    have h_dot : ZornCore.dot (A 0 1 • e) (B 1 0 • e) = A 0 1 * B 1 0 := by
      dsimp [ZornCore.dot, smul_apply]
      calc
        ∑ i, (A 0 1 * e i) * (B 1 0 * e i) = ∑ i, (A 0 1 * B 1 0) * (e i * e i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (A 0 1 * B 1 0) * ∑ i, e i * e i := by rw [← Finset.mul_sum]
        _ = (A 0 1 * B 1 0) * ZornCore.dot e e := rfl
        _ = A 0 1 * B 1 0 := by rw [he, mul_one]
    rw [h_dot]
    rw [Fin.sum_univ_two]
    try ring
  · dsimp [zornLineEmbed, Matrix.mul_apply, ZornCore.mul_u]
    have hc : cross (A 1 0 • e) (B 1 0 • e) = (A 1 0 * B 1 0) • cross e e := cross_smul_smul _ _ _ _
    rw [hc, hx, smul_zero, sub_zero]
    ext i
    rw [Fin.sum_univ_two]
    simp [smul_apply]
    ring
  · dsimp [zornLineEmbed, Matrix.mul_apply, ZornCore.mul_v]
    have hc : cross (A 0 1 • e) (B 0 1 • e) = (A 0 1 * B 0 1) • cross e e := cross_smul_smul _ _ _ _
    rw [hc, hx, smul_zero, add_zero]
    ext i
    rw [Fin.sum_univ_two]
    simp [smul_apply]
    ring
  · dsimp [zornLineEmbed, Matrix.mul_apply]
    have h_dot : ZornCore.dot (A 1 0 • e) (B 0 1 • e) = A 1 0 * B 0 1 := by
      dsimp [ZornCore.dot, smul_apply]
      calc
        ∑ i, (A 1 0 * e i) * (B 0 1 * e i) = ∑ i, (A 1 0 * B 0 1) * (e i * e i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (A 1 0 * B 0 1) * ∑ i, e i * e i := by rw [← Finset.mul_sum]
        _ = (A 1 0 * B 0 1) * ZornCore.dot e e := rfl
        _ = A 1 0 * B 0 1 := by rw [he, mul_one]
    rw [h_dot]
    rw [Fin.sum_univ_two]
    try ring

theorem zornLineEmbed_associator_vanishes
    (e : Vec3) (he : dot e e = 1) (hx : cross e e = 0)
    (A B C : Matrix (Fin 2) (Fin 2) ℝ) :
    (zornLineEmbed e he A * zornLineEmbed e he B) * zornLineEmbed e he C =
    zornLineEmbed e he A * (zornLineEmbed e he B * zornLineEmbed e he C) := by
  rw [← zornLineEmbed_mul e he hx A B, ← zornLineEmbed_mul e he hx B C]
  rw [← zornLineEmbed_mul e he hx (A * B) C, ← zornLineEmbed_mul e he hx A (B * C)]
  rw [Matrix.mul_assoc]

theorem zornLineEmbed_peirce_intertwines (e : Vec3) (he : dot e e = 1)
    (hx : cross e e = 0)
    (p A : Matrix (Fin 2) (Fin 2) ℝ) :
    zornLineEmbed e he (p * A * p) = 
      zornLineEmbed e he p * zornLineEmbed e he A * zornLineEmbed e he p := by
  rw [zornLineEmbed_mul e he hx (p * A) p]
  rw [zornLineEmbed_mul e he hx p A]

/-- 
Transport of the Peirce projection into the Zorn algebra:
ι_e(P A P) = ι_e(P) ι_e(A) ι_e(P) 
-/
theorem zornLineEmbed_peirce_transport
    (e : Vec3) (he : dot e e = 1) (hx : cross e e = 0)
    (P A : Matrix (Fin 2) (Fin 2) ℝ) :
    zornLineEmbed e he (P * A * P) = 
      zornLineEmbed e he P * zornLineEmbed e he A * zornLineEmbed e he P := by
  exact zornLineEmbed_peirce_intertwines e he hx P A

/-- 
Internal geometric characterization of the embedded split-quaternion section:
z ∈ range(ι_e) ↔ u_z ∈ ℝe ∧ v_z ∈ ℝe 
-/
theorem zornLineEmbed_image_char (e : Vec3) (he : dot e e = 1) (z : ZornCore.Zorn) :
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ, z = zornLineEmbed e he A) ↔
    (∃ (a b c d : ℝ), z = ⟨a, b • e, c • e, d⟩) := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A 0 0, A 0 1, A 1 0, A 1 1, rfl⟩
  · rintro ⟨a, b, c, d, rfl⟩
    use ![![a, b], ![c, d]]
    rfl

/-- 
Rank-one and null-cone classification:
A ≠ 0, det A = 0 ↔ A = x y^T
-/
theorem det_zero_iff_rank_one (A : Matrix (Fin 2) (Fin 2) ℝ) (h_nz : A ≠ 0) :
    Matrix.det A = 0 ↔ ∃ (x y : Fin 2 → ℝ), A = vecMulVec x y := by
  constructor
  · intro h
    rw [Matrix.det_fin_two] at h
    by_cases h00 : A 0 0 = 0
    · by_cases h01 : A 0 1 = 0
      · have h1 : A 0 0 = 0 ∧ A 0 1 = 0 := ⟨h00, h01⟩
        by_cases h10 : A 1 0 = 0
        · have h2 : A 1 1 ≠ 0 := by
            intro contra
            apply h_nz
            ext i j
            fin_cases i <;> fin_cases j
            · exact h00
            · exact h01
            · exact h10
            · exact contra
          use ![0, 1], ![0, A 1 1]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [vecMulVec, h00, h01, h10]
        · use ![0, 1], ![A 1 0, A 1 1]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [vecMulVec, h00, h01, h10]
      · rw [h00, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero] at h
        cases h with
        | inl h_contra => exact False.elim (h01 h_contra)
        | inr h10 =>
          have h11 : A 1 1 = A 1 1 / A 0 1 * A 0 1 := by exact (div_mul_cancel₀ (A 1 1) h01).symm
          use ![1, A 1 1 / A 0 1], ![0, A 0 1]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [vecMulVec, h00, h10]
          · exact h11
    · have h11 : A 1 1 = A 1 1 / A 0 0 * A 0 0 := by exact (div_mul_cancel₀ (A 1 1) h00).symm
      have h11_2 : A 1 1 = A 0 1 * A 1 0 / A 0 0 := by
        calc A 1 1 = (A 0 0 * A 1 1) / A 0 0 := by rw [mul_div_cancel_left₀ _ h00]
        _ = (A 0 1 * A 1 0) / A 0 0 := by rw [sub_eq_zero.mp h]
      use ![1, A 1 0 / A 0 0], ![A 0 0, A 0 1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vecMulVec, h00, h11_2]
      · ring
  · rintro ⟨x, y, rfl⟩
    simp [Matrix.det_fin_two, vecMulVec]
    ring
