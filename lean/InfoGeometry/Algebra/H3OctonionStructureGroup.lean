/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.JordanStructureGroup
import InfoGeometry.Algebra.H3Octonion

/-!
# Compact Albert Automorphism Group `F₄(-52) = Aut(H₃(𝕆))` and Structure Group `Str(H₃(𝕆))` / `Str₀(H₃(𝕆)) = E₆(-26)`

Directly on the compact 27-dimensional Albert Jordan algebra `H3Octonion ℝ`, this module proves:

1. `H3OctonionJordanAut` (`F₄(-52)`), `h3OctonionReducedStructureGroup` (`Str₀(H₃(𝕆)) = E₆(-26)`),
   and `StructureGroup ℝ (H3Octonion ℝ)` (`Str(H₃(𝕆))`).
2. `h3Octonion_traceBilin_U_selfAdjoint`, `h3Octonion_normCubic_adjointQuad`,
   `h3Octonion_U_adjointQuad_U`, `h3Octonion_U_U_adjointQuad`,
   `h3Octonion_adjointQuad_U`, and **Cubic Norm Homothety** `normCubic (U X Y) = normCubic X ^ 2 * normCubic Y`.
3. Positive-definite trace-adjoint `h3OctonionTraceAdjoint` and `h3OctonionNormTrilin`,
   yielding similitude-to-isotopy inclusion and the universal **Fundamental Formula**
   `U (U X Y) Z = U X (U Y (U X Z))`.
4. **Isotopy–Similitude Equivalence**: `g ∈ StructureGroup ℝ (H3Octonion ℝ)` iff `N(g x) = u * N(x)`
   with `u = N(g 1) ≠ 0`, multiplier homomorphism `StructureGroup ℝ (H3Octonion ℝ) →* ℝˣ`
   with kernel `≃* h3OctonionReducedStructureGroup`, `H3OctonionJordanAut ≃* {g ∈ Str₀ | g 1 = 1}`,
   and `H3OctonionJordanAut.preserves_traceBilin` (embedding `F₄(-52)` into the orthogonal group
   of positive-definite `traceBilin`).
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Octonion

section ScalarHelpers

private theorem sq_inv_mul_sq_eq_one {a : ℝ} (ha : a ≠ 0) : a⁻¹ ^ 2 * a ^ 2 = 1 := by
  calc a⁻¹ ^ 2 * a ^ 2 = (a⁻¹ * a) ^ 2 := by ring
    _ = 1 := by rw [inv_mul_cancel₀ ha, one_pow]

private theorem sq_inv_mul_eq_inv {a : ℝ} (ha : a ≠ 0) : a⁻¹ ^ 2 * a = a⁻¹ := by
  calc a⁻¹ ^ 2 * a = (a⁻¹ * a) * a⁻¹ := by ring
    _ = a⁻¹ := by rw [inv_mul_cancel₀ ha, one_mul]

private theorem real_cubic_ne_zero_near_zero_oct (a b c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, |r| ≤ 2 * δ →
      1 + r * a + r ^ 2 * b + r ^ 3 * c ≠ 0 := by
  refine ⟨min (1 / 2) (1 / (8 * (|a| + |b| + |c| + 1))), ?_, ?_⟩
  · positivity
  · intro r hr hzero
    have hδ1 : min (1 / 2) (1 / (8 * (|a| + |b| + |c| + 1))) ≤ 1 / 2 := min_le_left _ _
    have hδ2 : min (1 / 2) (1 / (8 * (|a| + |b| + |c| + 1))) ≤
        1 / (8 * (|a| + |b| + |c| + 1)) := min_le_right _ _
    have hr1 : |r| ≤ 1 := by linarith
    have hdenom : 0 < |a| + |b| + |c| + 1 := by positivity
    have hr2 : |r| * (|a| + |b| + |c| + 1) ≤ 1 / 4 := by
      have hmul : |r| ≤ 1 / (4 * (|a| + |b| + |c| + 1)) := by
        calc |r| ≤ 2 * min (1 / 2) (1 / (8 * (|a| + |b| + |c| + 1))) := hr
          _ ≤ 2 * (1 / (8 * (|a| + |b| + |c| + 1))) := by linarith
          _ = 1 / (4 * (|a| + |b| + |c| + 1)) := by field_simp; ring
      calc |r| * (|a| + |b| + |c| + 1)
          ≤ (1 / (4 * (|a| + |b| + |c| + 1))) * (|a| + |b| + |c| + 1) := by gcongr
        _ = 1 / 4 := by field_simp [hdenom.ne']
    have hr_sq : |r ^ 2| ≤ |r| := by
      rw [sq, abs_mul]
      nlinarith [abs_nonneg r]
    have hr_cu : |r ^ 3| ≤ |r| := by
      rw [pow_succ, abs_mul]
      nlinarith [abs_nonneg r, sq_abs r]
    have hbound : |r * a + r ^ 2 * b + r ^ 3 * c| ≤ 1 / 4 := by
      calc |r * a + r ^ 2 * b + r ^ 3 * c|
          ≤ |r * a + r ^ 2 * b| + |r ^ 3 * c| := abs_add_le _ _
        _ ≤ |r * a| + |r ^ 2 * b| + |r ^ 3 * c| := by linarith [abs_add_le (r * a) (r ^ 2 * b)]
        _ = |r| * |a| + |r ^ 2| * |b| + |r ^ 3| * |c| := by simp [abs_mul]
        _ ≤ |r| * |a| + |r| * |b| + |r| * |c| := by gcongr
        _ = |r| * (|a| + |b| + |c|) := by ring
        _ ≤ |r| * (|a| + |b| + |c| + 1) := by nlinarith [abs_nonneg r]
        _ ≤ 1 / 4 := hr2
    have hneg : -(1 / 4 : ℝ) ≤ r * a + r ^ 2 * b + r ^ 3 * c := (abs_le.mp hbound).1
    linarith

private theorem extract_real_deg3_leading_oct (δ : ℝ) (hδ : 0 < δ)
    (a₀ a₁ a₂ a₃ : ℝ)
    (h : ∀ r : ℝ, |r| ≤ 2 * δ → a₀ + r * a₁ + r ^ 2 * a₂ + r ^ 3 * a₃ = 0) :
    a₃ = 0 := by
  have h1 := h δ (by rw [abs_of_pos hδ]; linarith)
  have hm1 := h (-δ) (by rw [abs_neg, abs_of_pos hδ]; linarith)
  have h2 := h (2 * δ) (by rw [abs_of_pos (by linarith)])
  have hm2 := h (-2 * δ) (by rw [show (-2 : ℝ) * δ = -(2 * δ) by ring, abs_neg, abs_of_pos (by linarith)])
  have hcomb : 12 * δ ^ 3 * a₃ = 0 := by nlinarith [h1, hm1, h2, hm2]
  rcases mul_eq_zero.mp hcomb with h12 | ha3
  · exfalso
    have : 0 < 12 * δ ^ 3 := by positivity
    linarith
  · exact ha3

private theorem det3_cofactor_cancel_oct {c₀ c₁ c₂ x₁ x₂ x₃ u₁ u₂ u₃ : ℝ}
    (h1 : c₂ * u₁ + c₁ * x₁ + c₀ = 0)
    (h2 : c₂ * u₂ + c₁ * x₂ + c₀ = 0)
    (h3 : c₂ * u₃ + c₁ * x₃ + c₀ = 0) :
    ((x₂ * u₃ - u₂ * x₃) - (x₁ * u₃ - u₁ * x₃) + (x₁ * u₂ - u₁ * x₂)) * c₀ = 0 := by
  have hcomb :
      (x₂ * u₃ - u₂ * x₃) * (c₂ * u₁ + c₁ * x₁ + c₀) -
      (x₁ * u₃ - u₁ * x₃) * (c₂ * u₂ + c₁ * x₂ + c₀) +
      (x₁ * u₂ - u₁ * x₂) * (c₂ * u₃ + c₁ * x₃ + c₀) = 0 := by
    rw [h1, h2, h3]; ring
  calc ((x₂ * u₃ - u₂ * x₃) - (x₁ * u₃ - u₁ * x₃) + (x₁ * u₂ - u₁ * x₂)) * c₀
      = (x₂ * u₃ - u₂ * x₃) * (c₂ * u₁ + c₁ * x₁ + c₀) -
        (x₁ * u₃ - u₁ * x₃) * (c₂ * u₂ + c₁ * x₂ + c₀) +
        (x₁ * u₂ - u₁ * x₂) * (c₂ * u₃ + c₁ * x₃ + c₀) := by ring
    _ = 0 := hcomb

private theorem diag123_det_poly {r A B C u1a u1b u1c u2a u2b u2c z1 z2 z3 : ℝ}
    (hA : A = ((2 * u1c - u1b * 3 + 9 * z2 - 4 * z3) -
      (u1c - u1a * 3 + 9 * z1 - z3) + (u1b - u1a * 2 + 4 * z1 - z2)) / 2)
    (hB : B = ((2 * u2c + z2 * u1c - u2b * 3 - u1b * z3) -
      (u2c + z1 * u1c - u2a * 3 - u1a * z3) + (u2b + z1 * u1b - u2a * 2 - u1a * z2)) / 2)
    (hC : C = ((z2 * u2c - u2b * z3) - (z1 * u2c - u2a * z3) + (z1 * u2b - u2a * z2)) / 2) :
    ((2 + r * z2) * (9 + r * u1c + r ^ 2 * u2c) - (4 + r * u1b + r ^ 2 * u2b) * (3 + r * z3)) -
      ((1 + r * z1) * (9 + r * u1c + r ^ 2 * u2c) - (1 + r * u1a + r ^ 2 * u2a) * (3 + r * z3)) +
      ((1 + r * z1) * (4 + r * u1b + r ^ 2 * u2b) - (1 + r * u1a + r ^ 2 * u2a) * (2 + r * z2)) =
    2 * (1 + r * A + r ^ 2 * B + r ^ 3 * C) := by
  rw [hA, hB, hC]; ring

end ScalarHelpers

section JordanAutomorphismGroup

def H3OctonionJordanAutLaws (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) : Prop :=
  e 1 = 1 ∧ ∀ x y : H3Octonion ℝ, e (x * y) = e x * e y

/-- Native automorphism group `F₄(-52) = Aut(H₃(𝕆))` of the compact Albert algebra. -/
structure H3OctonionJordanAut where
  toLinearEquiv : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ
  map_one' : toLinearEquiv 1 = 1
  map_mul' : ∀ x y : H3Octonion ℝ, toLinearEquiv (x * y) = toLinearEquiv x * toLinearEquiv y

namespace H3OctonionJordanAut

@[ext] theorem ext {e₁ e₂ : H3OctonionJordanAut}
    (h : e₁.toLinearEquiv = e₂.toLinearEquiv) : e₁ = e₂ := by
  cases e₁; cases e₂; cases h; rfl

theorem toLinearEquiv_injective : Function.Injective H3OctonionJordanAut.toLinearEquiv :=
  fun _ _ h => ext h

instance : CoeFun H3OctonionJordanAut (fun _ => H3Octonion ℝ → H3Octonion ℝ) where
  coe e := e.toLinearEquiv

instance : Group H3OctonionJordanAut where
  one := ⟨LinearEquiv.refl ℝ (H3Octonion ℝ), rfl, fun _ _ => rfl⟩
  mul e₁ e₂ :=
    ⟨e₂.toLinearEquiv.trans e₁.toLinearEquiv,
      by simp [e₂.map_one', e₁.map_one'],
      fun x y => by simp [e₂.map_mul', e₁.map_mul']⟩
  inv e :=
    ⟨e.toLinearEquiv.symm,
      by
        apply e.toLinearEquiv.injective
        simp [e.map_one'],
      fun x y => by
        apply e.toLinearEquiv.injective
        simp [e.map_mul']⟩
  one_mul _ := ext (by rfl)
  mul_one _ := ext (by rfl)
  mul_assoc _ _ _ := ext (by rfl)
  inv_mul_cancel e := ext (LinearEquiv.ext fun x => e.toLinearEquiv.symm_apply_apply x)

@[simp] theorem mul_apply (e₁ e₂ : H3OctonionJordanAut) (x : H3Octonion ℝ) :
    (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp] theorem one_apply (x : H3Octonion ℝ) : (1 : H3OctonionJordanAut) x = x := rfl

@[simp] theorem inv_apply (e : H3OctonionJordanAut) (x : H3Octonion ℝ) :
    e⁻¹ x = e.toLinearEquiv.symm x := rfl

theorem map_one (e : H3OctonionJordanAut) : e 1 = 1 := e.map_one'

theorem map_mul (e : H3OctonionJordanAut) (x y : H3Octonion ℝ) : e (x * y) = e x * e y :=
  e.map_mul' x y

theorem mem_StructureGroup (e : H3OctonionJordanAut) :
    e.toLinearEquiv ∈ StructureGroup ℝ (H3Octonion ℝ) :=
  jordanAut_mem_StructureGroup e.toLinearEquiv e.map_mul'

theorem laws (e : H3OctonionJordanAut) : H3OctonionJordanAutLaws e.toLinearEquiv :=
  ⟨e.map_one', e.map_mul'⟩

end H3OctonionJordanAut

end JordanAutomorphismGroup

section QuadraticAndCubicIdentities

theorem jordanU_eq_h3Octonion_U (x y : H3Octonion ℝ) :
    jordanU (R := ℝ) x y = U x y :=
  jordanU_eq_U x y

theorem h3Octonion_traceBilin_U_selfAdjoint (x y z : H3Octonion ℝ) :
    traceBilin (U x y) z = traceBilin y (U x z) := by
  simp only [U, traceBilin_sub_left, traceBilin_smul_left,
    traceBilin_sub_right, traceBilin_smul_right]
  rw [traceBilin_symm x y, traceBilin_symm y x, crossProduct_symm (adjointQuad x) y,
    mccrimmon_identity_15]
  ring

theorem h3Octonion_normCubic_adjointQuad (x : H3Octonion ℝ) :
    normCubic (adjointQuad x) = normCubic x ^ 2 := by
  have h1 := mccrimmon_identity_13 (adjointQuad x)
  have h2 := mccrimmon_identity_13 x
  have hsq : normCubic x * (3 * normCubic x) = 3 * normCubic x ^ 2 := by ring
  rw [adjointQuad_adjointQuad, traceBilin_smul_left, traceBilin_symm, h2] at h1
  linarith [h1, hsq]

theorem h3Octonion_U_self_adjointQuad (x : H3Octonion ℝ) :
    U x (adjointQuad x) = normCubic x • x := by
  rw [U, traceBilin_symm, mccrimmon_identity_13, crossProduct_self, adjointQuad_adjointQuad]
  module

theorem h3Octonion_U_adjointQuad_self (x : H3Octonion ℝ) :
    U (adjointQuad x) x = normCubic x • adjointQuad x := by
  rw [U, mccrimmon_identity_13, adjointQuad_adjointQuad, crossProduct_smul_left, crossProduct_self]
  module

theorem h3Octonion_U_adjointQuad_U (x y : H3Octonion ℝ) :
    U (adjointQuad x) (U x y) = normCubic x ^ 2 • y := by
  conv_lhs => arg 2; rw [U]
  rw [U_sub_right, U_smul_right, h3Octonion_U_adjointQuad_self]
  have hm := mccrimmon_identity_17 (adjointQuad x) y
  rw [adjointQuad_adjointQuad, traceBilin_smul_left, h3Octonion_normCubic_adjointQuad] at hm
  rw [hm]
  module

theorem h3Octonion_U_U_adjointQuad (x y : H3Octonion ℝ) :
    U x (U (adjointQuad x) y) = normCubic x ^ 2 • y := by
  have h1 : U (adjointQuad x) y =
      traceBilin (adjointQuad x) y • adjointQuad x - normCubic x • crossProduct x y := by
    rw [U, adjointQuad_adjointQuad, crossProduct_smul_left]
  rw [h1, U_sub_right, U_smul_right, U_smul_right, h3Octonion_U_self_adjointQuad, mccrimmon_identity_17]
  module

private theorem adjointQuad_sub (a b : H3Octonion ℝ) :
    adjointQuad (a - b) = adjointQuad a - crossProduct a b + adjointQuad b := by
  rw [sub_eq_add_neg, show -b = (-1 : ℝ) • b by module, adjointQuad_add,
    crossProduct_smul_right, adjointQuad_smul]
  module

theorem h3Octonion_adjointQuad_U (x y : H3Octonion ℝ) :
    adjointQuad (U x y) = U (adjointQuad x) (adjointQuad y) := by
  rw [U, adjointQuad_sub, adjointQuad_smul, crossProduct_smul_left, mccrimmon_identity_19 x y]
  have hm := mccrimmon_identity_11 (adjointQuad x) y
  rw [adjointQuad_adjointQuad] at hm
  have hadjB : adjointQuad (crossProduct (adjointQuad x) y) =
      (normCubic x * traceBilin x y) • y +
        traceBilin (adjointQuad y) (adjointQuad x) • adjointQuad x -
        crossProduct (adjointQuad (adjointQuad x)) (adjointQuad y) := by
    rw [eq_sub_of_add_eq' hm, adjointQuad_adjointQuad, traceBilin_smul_left]
  rw [hadjB, U, traceBilin_symm (adjointQuad x) (adjointQuad y)]
  module

/-- **Cubic Norm Homothety** on compact `H₃(𝕆)`: `N(U X Y) = N(X)^2 * N(Y)`. -/
theorem h3Octonion_normCubic_U (x y : H3Octonion ℝ) :
    normCubic (U x y) = normCubic x ^ 2 * normCubic y := by
  have h1 := mccrimmon_identity_13 (U x y)
  have h2 := mccrimmon_identity_13 y
  rw [h3Octonion_adjointQuad_U, h3Octonion_traceBilin_U_selfAdjoint, h3Octonion_U_adjointQuad_U,
    traceBilin_smul_right, h2] at h1
  linarith

end QuadraticAndCubicIdentities

section TraceAdjointAndNormTrilin

private def h3OctonionDualBasisVec (k : Fin 27) : H3Octonion ℝ :=
  if k.val < 3 then basisVec k else (1 / 2 : ℝ) • basisVec k

private theorem traceBilin_diagCartan_embed12 (l1 l2 l3 : ℝ) (u : CompactOctonion ℝ) :
    traceBilin (diagCartan l1 l2 l3) (embedJ12 u) = 0 := by
  simp [traceBilin, diagCartan, embedJ12]

private theorem traceBilin_diagCartan_embed23 (l1 l2 l3 : ℝ) (u : CompactOctonion ℝ) :
    traceBilin (diagCartan l1 l2 l3) (embedJ23 u) = 0 := by
  simp [traceBilin, diagCartan, embedJ23]

private theorem traceBilin_diagCartan_embed31 (l1 l2 l3 : ℝ) (u : CompactOctonion ℝ) :
    traceBilin (diagCartan l1 l2 l3) (embedJ31 u) = 0 := by
  simp [traceBilin, diagCartan, embedJ31]

private theorem traceBilin_basisVec_dual (j k : Fin 27) :
    traceBilin (basisVec j) (h3OctonionDualBasisVec k) = if j = k then 1 else 0 := by
  dsimp [h3OctonionDualBasisVec]
  by_cases hj3 : j.val < 3 <;> by_cases hk3 : k.val < 3
  · rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 by omega) with hj0 | hj0 | hj0 <;>
      rcases (show k.val = 0 ∨ k.val = 1 ∨ k.val = 2 by omega) with hk0 | hk0 | hk0 <;>
      simp [basisVec, traceBilin, diagCartan, Fin.ext_iff, hj0, hk0]
  · simp only [hk3, ↓reduceIte, traceBilin_smul_right]
    have hne : j ≠ k := fun h => hk3 (h ▸ hj3)
    simp only [hne, ↓reduceIte]
    have h0 : traceBilin (basisVec j) (basisVec k) = 0 := by
      have hj0 : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
      have hk0 : k.val ≠ 0 ∧ k.val ≠ 1 ∧ k.val ≠ 2 := by omega
      have hsub : ∀ l1 l2 l3 : ℝ, traceBilin (diagCartan l1 l2 l3) (basisVec k) = 0 := fun l1 l2 l3 => by
        by_cases hk11 : k.val < 11
        · simp [basisVec, hk0.1, hk0.2.1, hk0.2.2, hk11, traceBilin_diagCartan_embed12]
        · by_cases hk19 : k.val < 19
          · simp [basisVec, hk0.1, hk0.2.1, hk0.2.2, hk11, hk19, traceBilin_diagCartan_embed23]
          · simp [basisVec, hk0.1, hk0.2.1, hk0.2.2, hk11, hk19, traceBilin_diagCartan_embed31]
      rcases hj0 with h0 | h1 | h2
      · rw [show basisVec j = diagCartan 1 0 0 by simp [basisVec, h0]]; exact hsub 1 0 0
      · rw [show basisVec j = diagCartan 0 1 0 by simp [basisVec, h1]]; exact hsub 0 1 0
      · rw [show basisVec j = diagCartan 0 0 1 by simp [basisVec, h2]]; exact hsub 0 0 1
    rw [h0, mul_zero]
  · have hne : j ≠ k := fun h => hj3 (h ▸ hk3)
    simp only [hk3, hne, ↓reduceIte]
    rw [traceBilin_symm]
    have hk0 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
    have hj0 : j.val ≠ 0 ∧ j.val ≠ 1 ∧ j.val ≠ 2 := by omega
    have hsub : ∀ l1 l2 l3 : ℝ, traceBilin (diagCartan l1 l2 l3) (basisVec j) = 0 := fun l1 l2 l3 => by
      by_cases hj11 : j.val < 11
      · simp [basisVec, hj0.1, hj0.2.1, hj0.2.2, hj11, traceBilin_diagCartan_embed12]
      · by_cases hj19 : j.val < 19
        · simp [basisVec, hj0.1, hj0.2.1, hj0.2.2, hj11, hj19, traceBilin_diagCartan_embed23]
        · simp [basisVec, hj0.1, hj0.2.1, hj0.2.2, hj11, hj19, traceBilin_diagCartan_embed31]
    rcases hk0 with h0 | h1 | h2
    · rw [show basisVec k = diagCartan 1 0 0 by simp [basisVec, h0]]; exact hsub 1 0 0
    · rw [show basisVec k = diagCartan 0 1 0 by simp [basisVec, h1]]; exact hsub 0 1 0
    · rw [show basisVec k = diagCartan 0 0 1 by simp [basisVec, h2]]; exact hsub 0 0 1
  · simp only [hk3, ↓reduceIte, traceBilin_smul_right]
    have hne012 : ∀ (m : Fin 27), ¬m.val < 3 → m.val ≠ 0 ∧ m.val ≠ 1 ∧ m.val ≠ 2 := fun m hm => by
      omega
    rcases hne012 j hj3 with ⟨hj0, hj1, hj2⟩
    rcases hne012 k hk3 with ⟨hk0, hk1, hk2⟩
    by_cases hj11 : j.val < 11 <;> by_cases hk11 : k.val < 11
    · have hb : basisVec j = embedJ12 (CompactOctonion.basisVec ⟨j.val - 3, by omega⟩) := by
        simp [basisVec, hj0, hj1, hj2, hj11]
      have hc : basisVec k = embedJ12 (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩) := by
        simp [basisVec, hk0, hk1, hk2, hk11]
      rw [hb, hc]
      have htb : traceBilin (embedJ12 (CompactOctonion.basisVec ⟨j.val - 3, by omega⟩))
          (embedJ12 (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩)) =
          CompactOctonion.bilin (CompactOctonion.basisVec ⟨j.val - 3, by omega⟩)
            (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩) := by
        simp [traceBilin, embedJ12, CompactOctonion.bilin]
      rw [htb, CompactOctonion.bilin_basis]
      have hij : (⟨j.val - 3, by omega⟩ : Fin 8) = ⟨k.val - 3, by omega⟩ ↔ j = k := by
        constructor
        · intro h; ext; have := congrArg Fin.val h; dsimp at this; omega
        · intro h; subst h; rfl
      by_cases hjk : j = k
      · simp only [hjk, ↓reduceIte]; norm_num
      · simp only [mt hij.mp hjk, hjk, ↓reduceIte]; norm_num
    · have hjne : j ≠ k := fun h => hk11 (h ▸ hj11)
      simp only [hjne, ↓reduceIte]
      by_cases hk19 : k.val < 19
      · have : traceBilin (basisVec j) (basisVec k) = 0 := by
          simp [basisVec, hj0, hj1, hj2, hj11, hk0, hk1, hk2, hk11, hk19, traceBilin,
            embedJ12, embedJ23]
        rw [this, mul_zero]
      · have : traceBilin (basisVec j) (basisVec k) = 0 := by
          simp [basisVec, hj0, hj1, hj2, hj11, hk0, hk1, hk2, hk11, hk19, traceBilin,
            embedJ12, embedJ31]
        rw [this, mul_zero]
    · have hjne : j ≠ k := fun h => hj11 (h ▸ hk11)
      simp only [hjne, ↓reduceIte]
      by_cases hj19 : j.val < 19
      · have : traceBilin (basisVec j) (basisVec k) = 0 := by
          simp [basisVec, hj0, hj1, hj2, hj11, hj19, hk0, hk1, hk2, hk11, traceBilin,
            embedJ12, embedJ23]
        rw [this, mul_zero]
      · have : traceBilin (basisVec j) (basisVec k) = 0 := by
          simp [basisVec, hj0, hj1, hj2, hj11, hj19, hk0, hk1, hk2, hk11, traceBilin,
            embedJ12, embedJ31]
        rw [this, mul_zero]
    · by_cases hj19 : j.val < 19 <;> by_cases hk19 : k.val < 19
      · have hb : basisVec j = embedJ23 (CompactOctonion.basisVec ⟨j.val - 11, by omega⟩) := by
          simp [basisVec, hj0, hj1, hj2, hj11, hj19]
        have hc : basisVec k = embedJ23 (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩) := by
          simp [basisVec, hk0, hk1, hk2, hk11, hk19]
        rw [hb, hc]
        have htb : traceBilin (embedJ23 (CompactOctonion.basisVec ⟨j.val - 11, by omega⟩))
            (embedJ23 (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩)) =
            CompactOctonion.bilin (CompactOctonion.basisVec ⟨j.val - 11, by omega⟩)
              (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩) := by
          simp [traceBilin, embedJ23, CompactOctonion.bilin]
        rw [htb, CompactOctonion.bilin_basis]
        have hij : (⟨j.val - 11, by omega⟩ : Fin 8) = ⟨k.val - 11, by omega⟩ ↔ j = k := by
          constructor
          · intro h; ext; have := congrArg Fin.val h; dsimp at this; omega
          · intro h; subst h; rfl
        by_cases hjk : j = k
        · simp only [hjk, ↓reduceIte]; norm_num
        · simp only [mt hij.mp hjk, hjk, ↓reduceIte]; norm_num
      · have hjne : j ≠ k := fun h => hk19 (h ▸ hj19)
        simp only [hjne, ↓reduceIte]
        have : traceBilin (basisVec j) (basisVec k) = 0 := by
          simp [basisVec, hj0, hj1, hj2, hj11, hj19, hk0, hk1, hk2, hk11, hk19, traceBilin,
            embedJ23, embedJ31]
        rw [this, mul_zero]
      · have hjne : j ≠ k := fun h => hj19 (h ▸ hk19)
        simp only [hjne, ↓reduceIte]
        have : traceBilin (basisVec j) (basisVec k) = 0 := by
          simp [basisVec, hj0, hj1, hj2, hj11, hj19, hk0, hk1, hk2, hk11, hk19, traceBilin,
            embedJ23, embedJ31]
        rw [this, mul_zero]
      · have hb : basisVec j = embedJ31 (CompactOctonion.basisVec ⟨j.val - 19, by omega⟩) := by
          simp [basisVec, hj0, hj1, hj2, hj11, hj19]
        have hc : basisVec k = embedJ31 (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩) := by
          simp [basisVec, hk0, hk1, hk2, hk11, hk19]
        rw [hb, hc]
        have htb : traceBilin (embedJ31 (CompactOctonion.basisVec ⟨j.val - 19, by omega⟩))
            (embedJ31 (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩)) =
            CompactOctonion.bilin (CompactOctonion.basisVec ⟨j.val - 19, by omega⟩)
              (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩) := by
          simp [traceBilin, embedJ31, CompactOctonion.bilin]
        rw [htb, CompactOctonion.bilin_basis]
        have hij : (⟨j.val - 19, by omega⟩ : Fin 8) = ⟨k.val - 19, by omega⟩ ↔ j = k := by
          constructor
          · intro h; ext; have := congrArg Fin.val h; dsimp at this; omega
          · intro h; subst h; rfl
        by_cases hjk : j = k
        · simp only [hjk, ↓reduceIte]; norm_num
        · simp only [mt hij.mp hjk, hjk, ↓reduceIte]; norm_num

/-- Trace-adjoint operator `T†` on `H3Octonion ℝ` with `traceBilin (T† x) y = traceBilin x (T y)`. -/
def h3OctonionTraceAdjoint (T : Module.End ℝ (H3Octonion ℝ)) : Module.End ℝ (H3Octonion ℝ) where
  toFun x := ∑ k : Fin 27, traceBilin x (T (basisVec k)) • h3OctonionDualBasisVec k
  map_add' x y := by
    simp only [traceBilin_add_left, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [traceBilin_smul_left, ← smul_smul, Finset.smul_sum, RingHom.id_apply]

theorem h3OctonionTraceAdjoint_pair (T : Module.End ℝ (H3Octonion ℝ)) (x y : H3Octonion ℝ) :
    traceBilin (h3OctonionTraceAdjoint T x) y = traceBilin x (T y) := by
  conv_lhs => rw [basisVec_decomposition y]
  conv_rhs => rw [basisVec_decomposition y]
  dsimp [h3OctonionTraceAdjoint]
  simp only [map_sum, map_smul]
  have hsum_l : ∀ (s : Finset (Fin 27)) (A : Fin 27 → H3Octonion ℝ) (v : H3Octonion ℝ),
      traceBilin (∑ k ∈ s, A k) v = ∑ k ∈ s, traceBilin (A k) v := by
    intro s A v
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha, traceBilin_add_left, ih]
  have hsum_r : ∀ (s : Finset (Fin 27)) (u : H3Octonion ℝ) (B : Fin 27 → H3Octonion ℝ),
      traceBilin u (∑ j ∈ s, B j) = ∑ j ∈ s, traceBilin u (B j) := by
    intro s u B
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha, traceBilin_add_right, ih]
  have hl : traceBilin (∑ k : Fin 27, traceBilin x (T (basisVec k)) • h3OctonionDualBasisVec k)
      (∑ j : Fin 27, coordFun y j • basisVec j) =
      ∑ j : Fin 27, coordFun y j * traceBilin x (T (basisVec j)) := by
    rw [hsum_r Finset.univ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [traceBilin_smul_right, hsum_l Finset.univ]
    congr 1
    rw [Finset.sum_eq_single j]
    · rw [traceBilin_smul_left, traceBilin_symm (h3OctonionDualBasisVec j),
        traceBilin_basisVec_dual]
      simp only [↓reduceIte, mul_one]
    · intro k _ hkj
      rw [traceBilin_smul_left, traceBilin_symm (h3OctonionDualBasisVec k),
        traceBilin_basisVec_dual]
      simp only [Ne.symm hkj, ↓reduceIte, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hr : traceBilin x (∑ j : Fin 27, coordFun y j • T (basisVec j)) =
      ∑ j : Fin 27, coordFun y j * traceBilin x (T (basisVec j)) := by
    rw [hsum_r Finset.univ]
    refine Finset.sum_congr rfl fun j _ => traceBilin_smul_right _ _ _
  rw [hl, hr]

def h3OctonionTraceInverseAdjoint (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) :
    Module.End ℝ (H3Octonion ℝ) :=
  h3OctonionTraceAdjoint e.symm.toLinearMap

def h3OctonionTraceAdjointEquiv (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) :
    H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ :=
  LinearEquiv.ofLinearMap
    (h3OctonionTraceAdjoint e.toLinearMap)
    (h3OctonionTraceInverseAdjoint e)
    (by
      apply LinearMap.ext; intro x
      apply eq_of_traceBilin_left_eq; intro y
      change traceBilin (h3OctonionTraceAdjoint e.toLinearMap
          (h3OctonionTraceInverseAdjoint e x)) y = traceBilin x y
      rw [h3OctonionTraceAdjoint_pair, h3OctonionTraceInverseAdjoint,
        h3OctonionTraceAdjoint_pair]
      simp)
    (by
      apply LinearMap.ext; intro x
      apply eq_of_traceBilin_left_eq; intro y
      change traceBilin (h3OctonionTraceInverseAdjoint e
          (h3OctonionTraceAdjoint e.toLinearMap x)) y = traceBilin x y
      rw [h3OctonionTraceInverseAdjoint, h3OctonionTraceAdjoint_pair,
        h3OctonionTraceAdjoint_pair]
      simp)

theorem h3OctonionTraceInverseAdjoint_traceBilin (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ)
    (x y : H3Octonion ℝ) :
    traceBilin (h3OctonionTraceInverseAdjoint e x) (e y) = traceBilin x y := by
  rw [h3OctonionTraceInverseAdjoint, h3OctonionTraceAdjoint_pair]
  simp

/-- Symmetric cubic norm trilinear form `(1/6) T(x × y, z)` on `H3Octonion ℝ`. -/
def h3OctonionNormTrilin :
    H3Octonion ℝ →ₗ[ℝ] H3Octonion ℝ →ₗ[ℝ] H3Octonion ℝ →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => (1 / 6 : ℝ) * traceBilin (crossProduct x y) z
          map_add' := fun z₁ z₂ => by simp [traceBilin_add_right, mul_add]
          map_smul' := fun r z => by simp [traceBilin_smul_right]; ring }
      map_add' := fun y₁ y₂ => by
        ext z; simp [crossProduct_add_right, traceBilin_add_left, mul_add]
      map_smul' := fun r y => by
        ext z; simp [crossProduct_smul_right, traceBilin_smul_left]; ring }
  map_add' x₁ x₂ := by
    ext y z; simp [crossProduct_add_left, traceBilin_add_left, mul_add]
  map_smul' r x := by
    ext y z; simp [crossProduct_smul_left, traceBilin_smul_left]; ring

theorem h3OctonionNormTrilin_eq_trace_crossProduct (x y z : H3Octonion ℝ) :
    h3OctonionNormTrilin x y z = (1 / 6 : ℝ) * traceBilin (crossProduct x y) z := rfl

theorem h3OctonionNormTrilin_symm_12 (x y z : H3Octonion ℝ) :
    h3OctonionNormTrilin x y z = h3OctonionNormTrilin y x z := by
  simp [h3OctonionNormTrilin_eq_trace_crossProduct, crossProduct_symm]

theorem h3OctonionNormTrilin_symm_23 (x y z : H3Octonion ℝ) :
    h3OctonionNormTrilin x y z = h3OctonionNormTrilin x z y := by
  simp only [h3OctonionNormTrilin_eq_trace_crossProduct]
  rw [crossProduct_symm x y, mccrimmon_identity_15, traceBilin_symm y,
    crossProduct_symm x z, mccrimmon_identity_15]

theorem h3OctonionNormTrilin_diag (x : H3Octonion ℝ) :
    h3OctonionNormTrilin x x x = normCubic x := by
  rw [h3OctonionNormTrilin_eq_trace_crossProduct, crossProduct_self, traceBilin_smul_left,
    mccrimmon_identity_13]
  ring

theorem h3OctonionNormTrilin_polarization (x y z : H3Octonion ℝ) :
    6 * h3OctonionNormTrilin x y z =
      normCubic (x + y + z) - normCubic (x + y) - normCubic (x + z) - normCubic (y + z) +
        normCubic x + normCubic y + normCubic z := by
  rw [← h3OctonionNormTrilin_diag (x + y + z), ← h3OctonionNormTrilin_diag (x + y),
    ← h3OctonionNormTrilin_diag (x + z), ← h3OctonionNormTrilin_diag (y + z),
    ← h3OctonionNormTrilin_diag x, ← h3OctonionNormTrilin_diag y, ← h3OctonionNormTrilin_diag z]
  simp only [map_add, LinearMap.add_apply]
  have h13 : ∀ a b c : H3Octonion ℝ, h3OctonionNormTrilin a b c = h3OctonionNormTrilin c b a :=
    fun a b c => by rw [h3OctonionNormTrilin_symm_12, h3OctonionNormTrilin_symm_23,
      h3OctonionNormTrilin_symm_12]
  have h213 : h3OctonionNormTrilin y x z = h3OctonionNormTrilin x y z :=
    h3OctonionNormTrilin_symm_12 y x z
  have h132 : h3OctonionNormTrilin x z y = h3OctonionNormTrilin x y z :=
    h3OctonionNormTrilin_symm_23 x z y
  have h312 : h3OctonionNormTrilin z x y = h3OctonionNormTrilin x y z := by
    rw [h3OctonionNormTrilin_symm_12 z x y, h3OctonionNormTrilin_symm_23 x z y]
  have h231 : h3OctonionNormTrilin y z x = h3OctonionNormTrilin x y z := by
    rw [h13 y z x, h3OctonionNormTrilin_symm_23 x z y]
  have h321 : h3OctonionNormTrilin z y x = h3OctonionNormTrilin x y z := h13 z y x
  rw [h3OctonionNormTrilin_symm_12 y x x, h3OctonionNormTrilin_symm_23 x x y,
    h3OctonionNormTrilin_symm_23 y y x, h3OctonionNormTrilin_symm_12 y x y,
    h3OctonionNormTrilin_symm_12 z x x, h3OctonionNormTrilin_symm_23 x x z,
    h3OctonionNormTrilin_symm_23 z z x, h3OctonionNormTrilin_symm_12 z x z,
    h3OctonionNormTrilin_symm_12 z y y, h3OctonionNormTrilin_symm_23 y y z,
    h3OctonionNormTrilin_symm_23 z z y, h3OctonionNormTrilin_symm_12 z y z,
    h213, h132, h312, h231, h321]
  ring

theorem h3OctonionNormTrilin_similitude (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) (x y z : H3Octonion ℝ) :
    h3OctonionNormTrilin (e x) (e y) (e z) = (u : ℝ) * h3OctonionNormTrilin x y z := by
  have h1 := h3OctonionNormTrilin_polarization (e x) (e y) (e z)
  have h2 := h3OctonionNormTrilin_polarization x y z
  simp only [← map_add, hN] at h1
  have hu : 6 * h3OctonionNormTrilin (e x) (e y) (e z) =
      6 * ((u : ℝ) * h3OctonionNormTrilin x y z) := by
    rw [h1, mul_left_comm 6 (u : ℝ), h2]; ring
  linarith [hu]

end TraceAdjointAndNormTrilin

section SimilitudeToIsotopyAndFundamentalFormula

theorem h3Octonion_adjointQuad_similitude_intertwines
    (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) (x : H3Octonion ℝ) :
    adjointQuad (e x) = (u : ℝ) • h3OctonionTraceInverseAdjoint e (adjointQuad x) := by
  apply eq_of_traceBilin_left_eq
  intro z
  let w := e.symm z
  have hw : e w = z := e.apply_symm_apply z
  rw [← hw]
  have hC := h3OctonionNormTrilin_similitude e u hN x x w
  calc traceBilin (adjointQuad (e x)) (e w)
      = 3 * h3OctonionNormTrilin (e x) (e x) (e w) := by
        rw [h3OctonionNormTrilin_eq_trace_crossProduct, crossProduct_self, traceBilin_smul_left]; ring
    _ = (u : ℝ) * (3 * h3OctonionNormTrilin x x w) := by rw [hC]; ring
    _ = traceBilin ((u : ℝ) • h3OctonionTraceInverseAdjoint e (adjointQuad x)) (e w) := by
        rw [h3OctonionNormTrilin_eq_trace_crossProduct, crossProduct_self, traceBilin_smul_left,
          traceBilin_smul_left, h3OctonionTraceInverseAdjoint_traceBilin]
        ring

theorem h3Octonion_crossProduct_similitude_intertwines
    (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) (x y : H3Octonion ℝ) :
    crossProduct (e x) (e y) =
      (u : ℝ) • h3OctonionTraceInverseAdjoint e (crossProduct x y) := by
  apply eq_of_traceBilin_left_eq
  intro z
  let w := e.symm z
  have hw : e w = z := e.apply_symm_apply z
  rw [← hw]
  have hC := h3OctonionNormTrilin_similitude e u hN x y w
  calc traceBilin (crossProduct (e x) (e y)) (e w)
      = 6 * h3OctonionNormTrilin (e x) (e y) (e w) := by
        rw [h3OctonionNormTrilin_eq_trace_crossProduct]; ring
    _ = (u : ℝ) * (6 * h3OctonionNormTrilin x y w) := by rw [hC]; ring
    _ = traceBilin ((u : ℝ) • h3OctonionTraceInverseAdjoint e (crossProduct x y)) (e w) := by
        rw [h3OctonionNormTrilin_eq_trace_crossProduct, traceBilin_smul_left,
          h3OctonionTraceInverseAdjoint_traceBilin]
        ring

theorem h3Octonion_traceInverseAdjoint_crossProduct_intertwines
    (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) (a b : H3Octonion ℝ) :
    (u : ℝ) • crossProduct (h3OctonionTraceInverseAdjoint e a)
        (h3OctonionTraceInverseAdjoint e b) = e (crossProduct a b) := by
  let eInvAdj := h3OctonionTraceInverseAdjoint e
  let F : H3Octonion ℝ → H3Octonion ℝ → H3Octonion ℝ := fun x y =>
    (u : ℝ) • crossProduct (eInvAdj x) (eInvAdj y) - e (crossProduct x y)
  apply sub_eq_zero.mp
  change F a b = 0
  have hu : (u : ℝ) ≠ 0 := Units.ne_zero u
  have hadj1 : adjointQuad (e (1 : H3Octonion ℝ)) = (u : ℝ) • eInvAdj 1 := by
    have h := h3Octonion_adjointQuad_similitude_intertwines e u hN 1
    simpa [adjointQuad_one] using h
  have hnorm1 : normCubic (e (1 : H3Octonion ℝ)) = (u : ℝ) := by
    simpa [normCubic_one] using hN 1
  have hcross1_inv (y : H3Octonion ℝ) :
      crossProduct 1 (((1 / 2 : ℝ) * linearTrace y) • (1 : H3Octonion ℝ) - y) = y := by
    rw [crossProduct_symm, crossProduct_one]
    have hlt : linearTrace (((1 / 2 : ℝ) * linearTrace y) • (1 : H3Octonion ℝ) - y) =
        (1 / 2 : ℝ) * linearTrace y := by
      rw [linearTrace_sub, linearTrace_smul, linearTrace_one]; ring
    rw [hlt]; module
  have hF1 : ∀ y : H3Octonion ℝ, F 1 y = 0 := by
    have hF1cross : ∀ z : H3Octonion ℝ, F 1 (crossProduct 1 z) = 0 := by
      intro z
      have hm := mccrimmon_identity_10 (e 1) (e z)
      rw [hadj1, hnorm1, crossProduct_smul_left,
        h3Octonion_crossProduct_similitude_intertwines e u hN 1 z,
        crossProduct_smul_right, traceBilin_smul_left,
        h3OctonionTraceInverseAdjoint_traceBilin] at hm
      have hmc := mccrimmon_identity_10 (1 : H3Octonion ℝ) z
      rw [adjointQuad_one, normCubic_one] at hmc
      have hec := congrArg (fun w : H3Octonion ℝ => (u : ℝ) • e w) hmc
      rw [map_add, map_smul, map_smul, smul_add] at hec
      have hm_eq : (u : ℝ) • ((u : ℝ) • crossProduct (eInvAdj 1)
            (eInvAdj (crossProduct 1 z))) =
          (u : ℝ) • e (crossProduct 1 (crossProduct 1 z)) := by
        calc (u : ℝ) • ((u : ℝ) • crossProduct (eInvAdj 1) (eInvAdj (crossProduct 1 z)))
            = (u : ℝ) • e z + ((u : ℝ) * traceBilin 1 z) • e 1 := hm
          _ = (u : ℝ) • e (crossProduct 1 (crossProduct 1 z)) := by rw [hec]; module
      have hzero : (u : ℝ) • F 1 (crossProduct 1 z) = 0 := by
        dsimp [F]; rw [smul_sub, hm_eq, sub_self]
      exact (smul_eq_zero_iff_right hu).mp hzero
    intro y
    rw [← hcross1_inv y]
    exact hF1cross (((1 / 2 : ℝ) * linearTrace y) • (1 : H3Octonion ℝ) - y)
  have hFdiag : ∀ y : H3Octonion ℝ, F y y = 0 := by
    have hFcross : ∀ z : H3Octonion ℝ, F (crossProduct 1 z) (crossProduct 1 z) = 0 := by
      intro z
      have hm := mccrimmon_identity_11 (e 1) (e z)
      rw [hadj1, h3Octonion_adjointQuad_similitude_intertwines e u hN z,
        crossProduct_smul_left, crossProduct_smul_right,
        h3Octonion_crossProduct_similitude_intertwines e u hN 1 z,
        adjointQuad_smul, traceBilin_smul_left,
        h3OctonionTraceInverseAdjoint_traceBilin,
        traceBilin_smul_left, h3OctonionTraceInverseAdjoint_traceBilin] at hm
      have hmc := mccrimmon_identity_11 (1 : H3Octonion ℝ) z
      rw [adjointQuad_one] at hmc
      have hec := congrArg (fun w : H3Octonion ℝ => (u : ℝ) • e w) hmc
      simp only [map_add, map_smul, smul_add] at hec
      have hm_eq : ((u : ℝ) ^ 2) • (crossProduct (eInvAdj 1) (eInvAdj (adjointQuad z)) +
              adjointQuad (eInvAdj (crossProduct 1 z))) =
            (u : ℝ) • e (crossProduct 1 (adjointQuad z) + adjointQuad (crossProduct 1 z)) := by
        rw [smul_add, sq (u : ℝ), ← smul_smul (u : ℝ) (u : ℝ), ← sq (u : ℝ), hm, map_add]
        calc ((u : ℝ) * traceBilin 1 z) • e z + ((u : ℝ) * traceBilin (adjointQuad z) 1) • e 1
            = (u : ℝ) • traceBilin 1 z • e z + (u : ℝ) • traceBilin (adjointQuad z) 1 • e 1 := by
              rw [smul_smul, smul_smul]
          _ = (u : ℝ) • (e (crossProduct 1 (adjointQuad z)) + e (adjointQuad (crossProduct 1 z))) := by
              rw [← hec, ← smul_add]
      have hcancel_u : (u : ℝ) • ((u : ℝ) • (crossProduct (eInvAdj 1)
            (eInvAdj (adjointQuad z)) + adjointQuad (eInvAdj (crossProduct 1 z))) -
            e (crossProduct 1 (adjointQuad z) + adjointQuad (crossProduct 1 z))) = 0 := by
        rw [smul_sub, smul_smul, ← sq, hm_eq, sub_self]
      have hinner := (smul_eq_zero_iff_right hu).mp hcancel_u
      have h2 := congrArg (fun w : H3Octonion ℝ => (2 : ℝ) • w) hinner
      have hrel : (2 : ℝ) • F 1 (adjointQuad z) +
          F (crossProduct 1 z) (crossProduct 1 z) = 0 := by
        calc (2 : ℝ) • F 1 (adjointQuad z) + F (crossProduct 1 z) (crossProduct 1 z)
            = (2 : ℝ) • ((u : ℝ) • (crossProduct (eInvAdj 1) (eInvAdj (adjointQuad z)) +
                adjointQuad (eInvAdj (crossProduct 1 z))) -
                e (crossProduct 1 (adjointQuad z) + adjointQuad (crossProduct 1 z))) := by
              dsimp [F]; rw [crossProduct_self, crossProduct_self, map_add, map_smul]; module
          _ = 0 := by rw [h2, smul_zero]
      rw [hF1 (adjointQuad z), smul_zero, zero_add] at hrel
      exact hrel
    intro y
    rw [← hcross1_inv y]
    exact hFcross (((1 / 2 : ℝ) * linearTrace y) • (1 : H3Octonion ℝ) - y)
  have hFpol : (2 : ℝ) • F a b = F (a + b) (a + b) - F a a - F b b := by
    dsimp [F]
    simp only [map_add, crossProduct_add_left, crossProduct_add_right]
    rw [crossProduct_symm (eInvAdj b) (eInvAdj a), crossProduct_symm b a]
    module
  rw [hFdiag (a + b), hFdiag a, hFdiag b] at hFpol
  have h2 : (2 : ℝ) • F a b = 0 := by simpa using hFpol
  exact (smul_eq_zero_iff_right (by norm_num : (2 : ℝ) ≠ 0)).mp h2

theorem h3Octonion_U_similitude_intertwines
    (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) (x z : H3Octonion ℝ) :
    U (e x) z = e (U x (h3OctonionTraceAdjoint e.toLinearMap z)) := by
  have hz : z = h3OctonionTraceInverseAdjoint e (h3OctonionTraceAdjoint e.toLinearMap z) :=
    ((h3OctonionTraceAdjointEquiv e).symm_apply_apply z).symm
  have hcross : crossProduct (adjointQuad (e x)) z =
      e (crossProduct (adjointQuad x) (h3OctonionTraceAdjoint e.toLinearMap z)) := by
    rw [h3Octonion_adjointQuad_similitude_intertwines e u hN x]
    conv_lhs => rw [hz]
    rw [crossProduct_smul_left]
    exact h3Octonion_traceInverseAdjoint_crossProduct_intertwines e u hN
      (adjointQuad x) (h3OctonionTraceAdjoint e.toLinearMap z)
  have htr : traceBilin (e x) z = traceBilin x (h3OctonionTraceAdjoint e.toLinearMap z) := by
    rw [traceBilin_symm (e x) z]
    change traceBilin z (e.toLinearMap x) = _
    rw [← h3OctonionTraceAdjoint_pair e.toLinearMap z x, traceBilin_symm]
  simp only [U, map_sub, map_smul]
  rw [hcross, htr]

theorem h3Octonion_similitude_imp_mem_StructureGroup
    (e : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) :
    e ∈ StructureGroup ℝ (H3Octonion ℝ) := by
  refine ⟨h3OctonionTraceAdjointEquiv e, fun x => ?_⟩
  apply LinearMap.ext; intro y
  change jordanU (R := ℝ) (e x) y = e (jordanU (R := ℝ) x (h3OctonionTraceAdjoint e.toLinearMap y))
  rw [jordanU_eq_h3Octonion_U, jordanU_eq_h3Octonion_U]
  exact h3Octonion_U_similitude_intertwines e u hN x y

def h3OctonionULinearEquiv (x : H3Octonion ℝ) (hN : normCubic x ≠ 0) :
    H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ :=
  LinearEquiv.ofLinearMap
    (jordanU (R := ℝ) x)
    ((normCubic x ^ 2)⁻¹ • jordanU (R := ℝ) (adjointQuad x))
    (by
      apply LinearMap.ext; intro y
      have hsq : normCubic x ^ 2 ≠ 0 := pow_ne_zero 2 hN
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
        jordanU_eq_h3Octonion_U, U_smul_right, h3Octonion_U_U_adjointQuad, smul_smul]
      rw [inv_mul_cancel₀ hsq, one_smul])
    (by
      apply LinearMap.ext; intro y
      have hsq : normCubic x ^ 2 ≠ 0 := pow_ne_zero 2 hN
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
        jordanU_eq_h3Octonion_U, h3Octonion_U_adjointQuad_U, smul_smul]
      rw [inv_mul_cancel₀ hsq, one_smul])

@[simp] theorem h3OctonionULinearEquiv_apply (x : H3Octonion ℝ) (hN : normCubic x ≠ 0)
    (y : H3Octonion ℝ) :
    h3OctonionULinearEquiv x hN y = U x y :=
  jordanU_eq_h3Octonion_U x y

theorem h3OctonionTraceAdjoint_h3OctonionULinearEquiv (x : H3Octonion ℝ) (hN : normCubic x ≠ 0) :
    h3OctonionTraceAdjoint (h3OctonionULinearEquiv x hN).toLinearMap =
      (h3OctonionULinearEquiv x hN).toLinearMap := by
  apply LinearMap.ext; intro y
  apply eq_of_traceBilin_left_eq; intro z
  rw [h3OctonionTraceAdjoint_pair]
  simp only [LinearEquiv.coe_toLinearMap, h3OctonionULinearEquiv_apply]
  exact (h3Octonion_traceBilin_U_selfAdjoint x y z).symm

theorem h3OctonionULinearEquiv_mem_StructureGroup (x : H3Octonion ℝ) (hN : normCubic x ≠ 0) :
    h3OctonionULinearEquiv x hN ∈ StructureGroup ℝ (H3Octonion ℝ) := by
  have hsq : normCubic x ^ 2 ≠ 0 := pow_ne_zero 2 hN
  refine h3Octonion_similitude_imp_mem_StructureGroup (h3OctonionULinearEquiv x hN)
    (Units.mk0 (normCubic x ^ 2) hsq) fun y => ?_
  simpa using h3Octonion_normCubic_U x y

private theorem extract_deg4_leading_oct (δ : ℝ) (hδ : 0 < δ)
    (c₀ c₁ c₂ c₃ c₄ : H3Octonion ℝ)
    (h : ∀ r : ℝ, |r| ≤ 2 * δ → c₀ + r • c₁ + r ^ 2 • c₂ + r ^ 3 • c₃ + r ^ 4 • c₄ = 0) :
    c₄ = 0 := by
  have h0 := h 0 (by simpa [abs_zero] using (by positivity : 0 ≤ 2 * δ))
  have h1 := h δ (by rw [abs_of_pos hδ]; linarith)
  have hm1 := h (-δ) (by rw [abs_neg, abs_of_pos hδ]; linarith)
  have h2 := h (2 * δ) (by rw [abs_of_pos (by linarith)])
  have hm2 := h (-2 * δ) (by rw [show (-2 : ℝ) * δ = -(2 * δ) by ring, abs_neg, abs_of_pos (by linarith)])
  have hcomb :
      (6 : ℝ) • (c₀ + (0 : ℝ) • c₁ + (0 : ℝ) ^ 2 • c₂ + (0 : ℝ) ^ 3 • c₃ + (0 : ℝ) ^ 4 • c₄) -
      (4 : ℝ) • (c₀ + δ • c₁ + δ ^ 2 • c₂ + δ ^ 3 • c₃ + δ ^ 4 • c₄) -
      (4 : ℝ) • (c₀ + (-δ) • c₁ + (-δ) ^ 2 • c₂ + (-δ) ^ 3 • c₃ + (-δ) ^ 4 • c₄) +
      (c₀ + (2 * δ) • c₁ + (2 * δ) ^ 2 • c₂ + (2 * δ) ^ 3 • c₃ + (2 * δ) ^ 4 • c₄) +
      (c₀ + (-2 * δ) • c₁ + (-2 * δ) ^ 2 • c₂ + (-2 * δ) ^ 3 • c₃ + (-2 * δ) ^ 4 • c₄) = 0 := by
    rw [h0, h1, hm1, h2, hm2]; module
  have hsimp : (24 * δ ^ 4) • c₄ = 0 := by
    have heq : (24 * δ ^ 4) • c₄ =
        (6 : ℝ) • (c₀ + (0 : ℝ) • c₁ + (0 : ℝ) ^ 2 • c₂ + (0 : ℝ) ^ 3 • c₃ + (0 : ℝ) ^ 4 • c₄) -
        (4 : ℝ) • (c₀ + δ • c₁ + δ ^ 2 • c₂ + δ ^ 3 • c₃ + δ ^ 4 • c₄) -
        (4 : ℝ) • (c₀ + (-δ) • c₁ + (-δ) ^ 2 • c₂ + (-δ) ^ 3 • c₃ + (-δ) ^ 4 • c₄) +
        (c₀ + (2 * δ) • c₁ + (2 * δ) ^ 2 • c₂ + (2 * δ) ^ 3 • c₃ + (2 * δ) ^ 4 • c₄) +
        (c₀ + (-2 * δ) • c₁ + (-2 * δ) ^ 2 • c₂ + (-2 * δ) ^ 3 • c₃ + (-2 * δ) ^ 4 • c₄) := by
      module
    rw [heq, hcomb]
  rcases smul_eq_zero.mp hsimp with h24 | hc4
  · exfalso
    have hpos : 0 < 24 * δ ^ 4 := by positivity
    linarith
  · exact hc4

/-- **Universal Fundamental Formula** on compact `H₃(𝕆)`:
`U (U X Y) Z = U X (U Y (U X Z))` for all `X, Y, Z : H3Octonion ℝ`. -/
theorem h3Octonion_U_fundamental (X Y Z : H3Octonion ℝ) :
    U (U X Y) Z = U X (U Y (U X Z)) := by
  let a := traceBilin (adjointQuad (1 : H3Octonion ℝ)) X
  let b := traceBilin (adjointQuad X) (1 : H3Octonion ℝ)
  let c := normCubic X
  obtain ⟨δ, hδpos, hδ⟩ := real_cubic_ne_zero_near_zero_oct a b c
  have hline : ∀ r : ℝ, |r| ≤ 2 * δ →
      U (U (1 + r • X) Y) Z = U (1 + r • X) (U Y (U (1 + r • X) Z)) := by
    intro r hr
    have hnr : normCubic (1 + r • X) ≠ 0 := by
      rw [normCubic_line, normCubic_one]; exact hδ r hr
    have hsq : normCubic (1 + r • X) ^ 2 ≠ 0 := pow_ne_zero 2 hnr
    have h := h3Octonion_U_similitude_intertwines (h3OctonionULinearEquiv (1 + r • X) hnr)
      (Units.mk0 (normCubic (1 + r • X) ^ 2) hsq)
      (fun w => by simpa using h3Octonion_normCubic_U (1 + r • X) w) Y Z
    rw [h3OctonionULinearEquiv_apply, h3OctonionULinearEquiv_apply,
      h3OctonionTraceAdjoint_h3OctonionULinearEquiv] at h
    simpa using h
  let A := U 1 Y
  let B := T 1 Y X
  let C := U X Y
  let A' := U 1 Z
  let B' := T 1 Z X
  let C' := U X Z
  let P := U Y A'
  let Q := U Y B'
  let R := U Y C'
  let L0 := U A Z
  let L1 := T A Z B
  let L2 := T A Z C + U B Z
  let L3 := T B Z C
  let L4 := U C Z
  let R0 := U 1 P
  let R1 := T 1 P X + U 1 Q
  let R2 := U X P + T 1 Q X + U 1 R
  let R3 := U X Q + T 1 R X
  let R4 := U X R
  have hLHS : ∀ r : ℝ, U (U (1 + r • X) Y) Z =
      L0 + r • L1 + r ^ 2 • L2 + r ^ 3 • L3 + r ^ 4 • L4 := by
    intro r
    have hU : U (1 + r • X) Y = A + (r • B + r ^ 2 • C) := by
      rw [U_add_left, T_smul_outer, U_smul_left]
      dsimp [A, B, C]; module
    rw [hU, U_add_left, T_add_outer, T_smul_outer, T_smul_outer,
      U_add_left, U_smul_left, U_smul_left, T_smul_left, T_smul_outer]
    have h2' : r ^ 2 * r = r ^ 3 := by ring
    have h4' : (r ^ 2) ^ 2 = r ^ 4 := by ring
    have hs1 : r • r ^ 2 • T B Z C = r ^ 3 • L3 := by
      rw [smul_smul]; congr 1; exact (mul_comm r (r ^ 2)).trans h2'
    have hs2 : (r ^ 2) ^ 2 • U C Z = r ^ 4 • L4 := by
      dsimp [L4]; rw [h4']
    dsimp [L0, L1, L2, L3, L4]; rw [hs1, hs2]; module
  have hRHS : ∀ r : ℝ, U (1 + r • X) (U Y (U (1 + r • X) Z)) =
      R0 + r • R1 + r ^ 2 • R2 + r ^ 3 • R3 + r ^ 4 • R4 := by
    intro r
    have hU : U (1 + r • X) Z = A' + (r • B' + r ^ 2 • C') := by
      rw [U_add_left, T_smul_outer, U_smul_left]
      dsimp [A', B', C']; module
    rw [hU, U_add_right Y A', U_add_right Y (r • B') (r ^ 2 • C'),
      U_smul_right r Y B', U_smul_right (r ^ 2) Y C']
    change U (1 + r • X) (P + (r • Q + r ^ 2 • R)) = _
    rw [U_add_right, U_add_right, U_smul_right, U_smul_right,
      U_add_left 1 (r • X) P, U_add_left 1 (r • X) Q, U_add_left 1 (r • X) R,
      T_smul_outer, T_smul_outer, T_smul_outer, U_smul_left, U_smul_left, U_smul_left]
    simp only [smul_add, smul_smul]
    dsimp [R0, R1, R2, R3, R4]
    have h4 : r ^ 2 * r ^ 2 = r ^ 4 := by ring
    have h3 : r ^ 2 * r = r ^ 3 := by ring
    have h3' : r * r ^ 2 = r ^ 3 := by ring
    have h2 : r * r = r ^ 2 := by ring
    rw [h4, h3, h3', h2]
    module
  have hc4 : L4 - R4 = 0 := by
    refine extract_deg4_leading_oct δ hδpos (L0 - R0) (L1 - R1) (L2 - R2) (L3 - R3) (L4 - R4) ?_
    intro r hr
    have h := sub_eq_zero.mpr (hline r hr)
    rw [hLHS r, hRHS r] at h
    convert h using 1
    module
  exact sub_eq_zero.mp hc4

end SimilitudeToIsotopyAndFundamentalFormula

section IsotopyToSimilitudeAndReducedGroup

theorem h3Octonion_isotopy_cubic_identity (y b : H3Octonion ℝ) :
    U y (U b y) - traceBilin b y • U y b + traceBilin (adjointQuad y) (adjointQuad b) • y =
      normCubic y • adjointQuad b := by
  have hUb : U b y = traceBilin b y • b - crossProduct (adjointQuad b) y := rfl
  rw [hUb, crossProduct_symm (adjointQuad b) y, U_sub_right, U_smul_right,
    mccrimmon_identity_17 y (adjointQuad b)]
  module

/-- **Isotopy ⇒ Cubic-Norm Similitude** on `H₃(𝕆)`: every element `g ∈ StructureGroup ℝ (H3Octonion ℝ)`
satisfies `N(g x) = N(g 1) * N(x)` for all `x`, with `N(g 1) ≠ 0`. -/
theorem h3Octonion_isotopy_imp_similitude (g : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ)
    (hg : g ∈ StructureGroup ℝ (H3Octonion ℝ)) :
    normCubic (g 1) ≠ 0 ∧ ∀ x : H3Octonion ℝ, normCubic (g x) = normCubic (g 1) * normCubic x := by
  rcases hg with ⟨gSharp, hSharp⟩
  have hU : ∀ x z : H3Octonion ℝ, U (g x) z = g (U x (gSharp z)) := by
    intro x z
    have hx := LinearMap.ext_iff.mp (hSharp x) z
    simpa only [jordanU_eq_h3Octonion_U, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_toLinearMap] using hx
  have hU1 : ∀ z : H3Octonion ℝ, U (g 1) z = g (gSharp z) := by
    intro z; rw [hU 1 z, U_one]
  let y₀ := gSharp.symm (g.symm 1)
  have hy₀ : U (g 1) y₀ = 1 := by rw [hU1 y₀]; simp [y₀]
  have hna : normCubic (g 1) ≠ 0 := by
    intro hz
    have hn := congrArg normCubic hy₀
    rw [h3Octonion_normCubic_U, hz, zero_pow (by norm_num), zero_mul, normCubic_one] at hn
    exact one_ne_zero hn.symm
  refine ⟨hna, ?_⟩
  let a := g 1
  let b : H3Octonion ℝ := (normCubic a)⁻¹ • adjointQuad a
  have hUb : ∀ z : H3Octonion ℝ, U a (U b z) = z := by
    intro z
    have hb_eq : U b z = ((normCubic a)⁻¹ ^ 2) • U (adjointQuad a) z := U_smul_left _ _ _
    rw [hb_eq, U_smul_right, h3Octonion_U_U_adjointQuad, smul_smul, sq_inv_mul_sq_eq_one hna, one_smul]
  have hSharpUb : ∀ y : H3Octonion ℝ, gSharp (U b (g y)) = y := by
    intro y; apply g.injective; rw [← hU1 (U b (g y)), hUb]
  have hUgb : ∀ x y : H3Octonion ℝ, U (g x) (U b (g y)) = g (U x y) := by
    intro x y; rw [hU x (U b (g y)), hSharpUb y]
  have hUba : U b a = b := by
    have hb_eq : U b a = ((normCubic a)⁻¹ ^ 2) • U (adjointQuad a) a := U_smul_left _ _ _
    rw [hb_eq, h3Octonion_U_adjointQuad_self, smul_smul, sq_inv_mul_eq_inv hna]
  have hUgxb : ∀ x : H3Octonion ℝ, U (g x) b = g (U x 1) := by
    intro x
    calc U (g x) b = U (g x) (U b (g 1)) := by conv_lhs => rw [← hUba]
      _ = g (U x 1) := hUgb x 1
  have hadjb : adjointQuad b = (normCubic a)⁻¹ • a := by
    dsimp [b]; rw [adjointQuad_smul, adjointQuad_adjointQuad, smul_smul, sq_inv_mul_eq_inv hna]
  have hkey : ∀ x : H3Octonion ℝ,
      (traceBilin b (g x) - linearTrace x) • U x 1 +
      (traceBilin (adjointQuad x) 1 - traceBilin (adjointQuad (g x)) (adjointQuad b)) • x +
      ((normCubic a)⁻¹ * normCubic (g x) - normCubic x) • (1 : H3Octonion ℝ) = 0 := by
    intro x
    have hidg := h3Octonion_isotopy_cubic_identity (g x) b
    rw [hUgb x x, hUgxb x, hadjb] at hidg
    have hid1 : U x x - traceBilin b (g x) • U x 1 +
        traceBilin (adjointQuad (g x)) ((normCubic a)⁻¹ • a) • x =
        ((normCubic a)⁻¹ * normCubic (g x)) • (1 : H3Octonion ℝ) := by
      apply g.injective
      simp only [map_sub, map_add, map_smul]
      change g (U x x) - traceBilin b (g x) • g (U x 1) +
          traceBilin (adjointQuad (g x)) ((normCubic a)⁻¹ • a) • g x =
        ((normCubic a)⁻¹ * normCubic (g x)) • a
      rw [smul_smul, mul_comm (normCubic (g x)) (normCubic a)⁻¹] at hidg
      exact hidg
    have hid2 := h3Octonion_isotopy_cubic_identity x 1
    rw [U_one, traceBilin_symm, traceBilin_one, adjointQuad_one] at hid2
    rw [← hadjb] at hid1
    have hsub := congrArg₂ (fun A B : H3Octonion ℝ => B - A) hid1 hid2
    calc (traceBilin b (g x) - linearTrace x) • U x 1 +
          (traceBilin (adjointQuad x) 1 - traceBilin (adjointQuad (g x)) (adjointQuad b)) • x +
          ((normCubic a)⁻¹ * normCubic (g x) - normCubic x) • (1 : H3Octonion ℝ) =
        (U x x - linearTrace x • U x 1 + traceBilin (adjointQuad x) 1 • x) -
          (U x x - traceBilin b (g x) • U x 1 +
            traceBilin (adjointQuad (g x)) (adjointQuad b) • x) -
          (normCubic x • (1 : H3Octonion ℝ) -
            ((normCubic a)⁻¹ * normCubic (g x)) • (1 : H3Octonion ℝ)) := by module
      _ = 0 := by rw [hsub, sub_self]
  intro z
  let d : H3Octonion ℝ := diagCartan 1 2 3
  have hUd1 : U d 1 = diagCartan 1 4 9 := by
    ext <;> simp [U, d, diagCartan, traceBilin, adjointQuad, crossProduct] <;> norm_num
  let u0 : H3Octonion ℝ := U d 1
  let u1 : H3Octonion ℝ := T d 1 z
  let u2 : H3Octonion ℝ := U z 1
  have hUr : ∀ r : ℝ, U (d + r • z) 1 = u0 + r • u1 + r ^ 2 • u2 := by
    intro r; rw [U_add_left, T_smul_outer, U_smul_left]
  let A : ℝ := ((2 * u1.α₃ - u1.α₂ * 3 + 9 * z.α₂ - 4 * z.α₃) -
      (u1.α₃ - u1.α₁ * 3 + 9 * z.α₁ - z.α₃) +
      (u1.α₂ - u1.α₁ * 2 + 4 * z.α₁ - z.α₂)) / 2
  let B : ℝ := ((2 * u2.α₃ + z.α₂ * u1.α₃ - u2.α₂ * 3 - u1.α₂ * z.α₃) -
      (u2.α₃ + z.α₁ * u1.α₃ - u2.α₁ * 3 - u1.α₁ * z.α₃) +
      (u2.α₂ + z.α₁ * u1.α₂ - u2.α₁ * 2 - u1.α₁ * z.α₂)) / 2
  let C : ℝ := ((z.α₂ * u2.α₃ - u2.α₂ * z.α₃) -
      (z.α₁ * u2.α₃ - u2.α₁ * z.α₃) +
      (z.α₁ * u2.α₂ - u2.α₁ * z.α₂)) / 2
  obtain ⟨δ, hδpos, hδ⟩ := real_cubic_ne_zero_near_zero_oct A B C
  have hc0_near : ∀ r : ℝ, |r| ≤ 2 * δ →
      (normCubic a)⁻¹ * normCubic (g (d + r • z)) - normCubic (d + r • z) = 0 := by
    intro r hr
    let x := d + r • z
    let c₂ := traceBilin b (g x) - linearTrace x
    let c₁ := traceBilin (adjointQuad x) 1 - traceBilin (adjointQuad (g x)) (adjointQuad b)
    let c₀ := (normCubic a)⁻¹ * normCubic (g x) - normCubic x
    have hx := hkey x
    have hα1 : c₂ * (U x 1).α₁ + c₁ * x.α₁ + c₀ = 0 := by
      dsimp [c₂, c₁, c₀]
      simpa only [add_α₁, smul_α₁, one_α₁, zero_α₁, mul_one] using congrArg H3Octonion.α₁ hx
    have hα2 : c₂ * (U x 1).α₂ + c₁ * x.α₂ + c₀ = 0 := by
      dsimp [c₂, c₁, c₀]
      simpa only [add_α₂, smul_α₂, one_α₂, zero_α₂, mul_one] using congrArg H3Octonion.α₂ hx
    have hα3 : c₂ * (U x 1).α₃ + c₁ * x.α₃ + c₀ = 0 := by
      dsimp [c₂, c₁, c₀]
      simpa only [add_α₃, smul_α₃, one_α₃, zero_α₃, mul_one] using congrArg H3Octonion.α₃ hx
    have hcancel := det3_cofactor_cancel_oct hα1 hα2 hα3
    have hx1 : x.α₁ = 1 + r * z.α₁ := rfl
    have hx2 : x.α₂ = 2 + r * z.α₂ := rfl
    have hx3 : x.α₃ = 3 + r * z.α₃ := rfl
    have hu1 : (U x 1).α₁ = 1 + r * u1.α₁ + r ^ 2 * u2.α₁ := by
      dsimp [x]; rw [hUr r]; simp only [add_α₁, smul_α₁]; dsimp [u0]; rw [hUd1]; simp [diagCartan]
    have hu2 : (U x 1).α₂ = 4 + r * u1.α₂ + r ^ 2 * u2.α₂ := by
      dsimp [x]; rw [hUr r]; simp only [add_α₂, smul_α₂]; dsimp [u0]; rw [hUd1]; simp [diagCartan]
    have hu3 : (U x 1).α₃ = 9 + r * u1.α₃ + r ^ 2 * u2.α₃ := by
      dsimp [x]; rw [hUr r]; simp only [add_α₃, smul_α₃]; dsimp [u0]; rw [hUd1]; simp [diagCartan]
    have hdet := diag123_det_poly (r := r) (A := A) (B := B) (C := C)
      (u1a := u1.α₁) (u1b := u1.α₂) (u1c := u1.α₃)
      (u2a := u2.α₁) (u2b := u2.α₂) (u2c := u2.α₃)
      (z1 := z.α₁) (z2 := z.α₂) (z3 := z.α₃) rfl rfl rfl
    rw [← hx1, ← hx2, ← hx3, ← hu1, ← hu2, ← hu3] at hdet
    rw [hdet] at hcancel
    have hnz : 2 * (1 + r * A + r ^ 2 * B + r ^ 3 * C) ≠ 0 :=
      mul_ne_zero (by norm_num) (hδ r hr)
    exact (mul_eq_zero.mp hcancel).resolve_left hnz
  have hpoly : ∀ r : ℝ, |r| ≤ 2 * δ →
      ((normCubic a)⁻¹ * normCubic (g d) - normCubic d) +
      r * ((normCubic a)⁻¹ * traceBilin (adjointQuad (g d)) (g z) - traceBilin (adjointQuad d) z) +
      r ^ 2 * ((normCubic a)⁻¹ * traceBilin (adjointQuad (g z)) (g d) - traceBilin (adjointQuad z) d) +
      r ^ 3 * ((normCubic a)⁻¹ * normCubic (g z) - normCubic z) = 0 := by
    intro r hr
    have hc := hc0_near r hr
    rw [map_add, map_smul, normCubic_line, normCubic_line] at hc
    linarith [hc]
  have hlead := extract_real_deg3_leading_oct δ hδpos _ _ _ _ hpoly
  have heq : normCubic (g z) - normCubic a * normCubic z = 0 := by
    calc normCubic (g z) - normCubic a * normCubic z
        = normCubic a * ((normCubic a)⁻¹ * normCubic (g z) - normCubic z) := by
          rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hna, one_mul]
      _ = 0 := by rw [hlead, mul_zero]
  exact sub_eq_zero.mp heq

/-- **Isotopy–Similitude Equivalence** on compact `H₃(𝕆)`:
`g ∈ StructureGroup ℝ (H3Octonion ℝ)` iff `∃ u : ℝˣ, ∀ x, normCubic (g x) = u * normCubic x`. -/
theorem h3Octonion_mem_StructureGroup_iff_similitude (g : H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) :
    g ∈ StructureGroup ℝ (H3Octonion ℝ) ↔
      ∃ u : ℝˣ, ∀ x : H3Octonion ℝ, normCubic (g x) = (u : ℝ) * normCubic x := by
  constructor
  · intro hg
    obtain ⟨hna, hsim⟩ := h3Octonion_isotopy_imp_similitude g hg
    exact ⟨Units.mk0 (normCubic (g 1)) hna, hsim⟩
  · rintro ⟨u, hsim⟩
    exact h3Octonion_similitude_imp_mem_StructureGroup g u hsim

/-- The compact reduced structure group `Str₀(H₃(𝕆)) = E₆(-26)` of cubic-norm isometries. -/
def h3OctonionReducedStructureGroup : Subgroup (H3Octonion ℝ ≃ₗ[ℝ] H3Octonion ℝ) where
  carrier := {g | ∀ x : H3Octonion ℝ, normCubic (g x) = normCubic x}
  one_mem' _ := rfl
  mul_mem' := by
    intro g h hg hh x
    change normCubic (g (h x)) = normCubic x
    rw [hg (h x), hh x]
  inv_mem' := by
    intro g hg x
    change normCubic (g.symm x) = normCubic x
    calc normCubic (g.symm x) = normCubic (g (g.symm x)) := (hg (g.symm x)).symm
      _ = normCubic x := by simp

theorem h3OctonionReducedStructureGroup_le_StructureGroup :
    h3OctonionReducedStructureGroup ≤ StructureGroup ℝ (H3Octonion ℝ) := by
  intro g hg
  exact (h3Octonion_mem_StructureGroup_iff_similitude g).mpr ⟨1, fun x => by simpa using hg x⟩

/-- Cubic-norm multiplier homomorphism `Str(H₃(𝕆)) →* ℝˣ`. -/
def h3OctonionStructureGroupMultiplier :
    StructureGroup ℝ (H3Octonion ℝ) →* ℝˣ where
  toFun g := Units.mk0 (normCubic (g.1 1)) (h3Octonion_isotopy_imp_similitude g.1 g.2).1
  map_one' := by
    apply Units.ext
    simp [normCubic_one]
  map_mul' g h := by
    apply Units.ext
    have hsim := (h3Octonion_isotopy_imp_similitude g.1 g.2).2
    change normCubic (g.1 (h.1 1)) = normCubic (g.1 1) * normCubic (h.1 1)
    exact hsim (h.1 1)

theorem h3OctonionStructureGroupMultiplier_ker_iff (g : StructureGroup ℝ (H3Octonion ℝ)) :
    g ∈ h3OctonionStructureGroupMultiplier.ker ↔
      ∀ x : H3Octonion ℝ, normCubic (g.1 x) = normCubic x := by
  constructor
  · intro hk x
    have h1 : normCubic (g.1 1) = 1 := congrArg Units.val hk
    have hsim := (h3Octonion_isotopy_imp_similitude g.1 g.2).2 x
    rw [h1, one_mul] at hsim
    exact hsim
  · intro h
    apply Units.ext
    simpa [h3OctonionStructureGroupMultiplier, normCubic_one] using h 1

/-- `h3OctonionReducedStructureGroup` (`Str₀(H₃(𝕆)) = E₆(-26)`) is canonically the
kernel of `h3OctonionStructureGroupMultiplier : Str(H₃(𝕆)) →* ℝˣ`. -/
def h3OctonionReducedStructureGroupMulEquivStructureKer :
    h3OctonionReducedStructureGroup ≃* h3OctonionStructureGroupMultiplier.ker where
  toFun e :=
    ⟨⟨e.1, h3OctonionReducedStructureGroup_le_StructureGroup e.2⟩,
      (h3OctonionStructureGroupMultiplier_ker_iff _).mpr e.2⟩
  invFun g := ⟨g.1.1, (h3OctonionStructureGroupMultiplier_ker_iff g.1).1 g.2⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

theorem H3OctonionJordanAut.mem_reducedStructureGroup (e : H3OctonionJordanAut) :
    e.toLinearEquiv ∈ h3OctonionReducedStructureGroup := by
  have hsim := (h3Octonion_isotopy_imp_similitude e.toLinearEquiv e.mem_StructureGroup).2
  intro x
  have h1 := e.map_one
  simpa [h1, normCubic_one] using hsim x

theorem h3OctonionJordanAut_of_reducedStructure (g : h3OctonionReducedStructureGroup)
    (h1 : g.1 1 = 1) :
    H3OctonionJordanAutLaws g.1 := by
  refine ⟨h1, fun x y => ?_⟩
  have hsim : ∀ w, normCubic (g.1 w) = (1 : ℝˣ) * normCubic w := fun w => by simpa using g.2 w
  have hadj : ∀ w, adjointQuad (g.1 w) = g.1 (adjointQuad w) := by
    intro w
    have hid := h3Octonion_adjointQuad_similitude_intertwines g.1 1 hsim w
    have he1 : h3OctonionTraceInverseAdjoint g.1 1 = 1 := by
      have h1a := h3Octonion_adjointQuad_similitude_intertwines g.1 1 hsim 1
      rw [h1, adjointQuad_one, Units.val_one, one_smul] at h1a
      exact h1a.symm
    have hc : ∀ z, h3OctonionTraceInverseAdjoint g.1 z = g.1 z := by
      intro z
      have hcr := h3Octonion_traceInverseAdjoint_crossProduct_intertwines g.1 1 hsim 1
        (((1 / 2 : ℝ) * linearTrace z) • (1 : H3Octonion ℝ) - z)
      have hcross1_inv : crossProduct 1 (((1 / 2 : ℝ) * linearTrace z) • (1 : H3Octonion ℝ) - z) = z := by
        rw [crossProduct_symm, crossProduct_one]
        have hlt : linearTrace (((1 / 2 : ℝ) * linearTrace z) • (1 : H3Octonion ℝ) - z) =
            (1 / 2 : ℝ) * linearTrace z := by
          rw [linearTrace_sub, linearTrace_smul, linearTrace_one]; ring
        rw [hlt]; module
      have hlt_inv : traceBilin (g.1 w) (g.1 1) = traceBilin w 1 := by
        have h1' : normCubic (1 + (1 : ℝ) • w) =
            normCubic (1 + (1 : ℝ) • g.1 w) := by simpa [map_add, map_smul, h1] using (g.2 (1 + (1 : ℝ) • w)).symm
        have h2' : normCubic (1 + (-1 : ℝ) • w) =
            normCubic (1 + (-1 : ℝ) • g.1 w) := by simpa [map_add, map_smul, h1] using (g.2 (1 + (-1 : ℝ) • w)).symm
        rw [normCubic_line, normCubic_line, adjointQuad_one, traceBilin_one_left, traceBilin_one_left,
          normCubic_one, g.2 w] at h1' h2'
        have hsub : traceBilin (g.1 w) (1 : H3Octonion ℝ) = traceBilin w (1 : H3Octonion ℝ) := by
          rw [traceBilin_symm (g.1 w), traceBilin_one_left, traceBilin_symm w, traceBilin_one_left]
          linarith [h1', h2']
        simpa [h1] using hsub
      have hginv : g.1.symm 1 = 1 := by
        apply g.1.injective; simp [h1]
      have hltr : ∀ u, linearTrace (g.1 u) = linearTrace u := by
        intro u
        have h1' : normCubic (1 + (1 : ℝ) • u) = normCubic (1 + (1 : ℝ) • g.1 u) := by
          simpa [map_add, map_smul, h1] using (g.2 (1 + (1 : ℝ) • u)).symm
        have h2' : normCubic (1 + (-1 : ℝ) • u) = normCubic (1 + (-1 : ℝ) • g.1 u) := by
          simpa [map_add, map_smul, h1] using (g.2 (1 + (-1 : ℝ) • u)).symm
        rw [normCubic_line, normCubic_line, adjointQuad_one, traceBilin_one_left, traceBilin_one_left,
          normCubic_one, g.2 u] at h1' h2'
        linarith [h1', h2']
      have hcr' : crossProduct 1 (h3OctonionTraceInverseAdjoint g.1
          (((1 / 2 : ℝ) * linearTrace z) • (1 : H3Octonion ℝ) - z)) = g.1 z := by
        simpa [he1, ← one_div, hcross1_inv] using hcr
      have heinv_smul : h3OctonionTraceInverseAdjoint g.1
          (((1 / 2 : ℝ) * linearTrace z) • (1 : H3Octonion ℝ) - z) =
          ((1 / 2 : ℝ) * linearTrace z) • 1 - h3OctonionTraceInverseAdjoint g.1 z := by
        simp [h3OctonionTraceInverseAdjoint, map_sub, map_smul,
          show h3OctonionTraceAdjoint g.1.symm.toLinearMap 1 = 1 from he1]
      rw [heinv_smul, crossProduct_symm 1, sub_eq_add_neg,
        show -(h3OctonionTraceInverseAdjoint g.1 z) =
          (-1 : ℝ) • h3OctonionTraceInverseAdjoint g.1 z by module,
        crossProduct_add_left, crossProduct_smul_left, crossProduct_smul_left,
        show crossProduct 1 1 = (2 : ℝ) • (1 : H3Octonion ℝ) by rw [crossProduct_self, adjointQuad_one],
        crossProduct_one] at hcr'
      have hlt_adj : linearTrace (h3OctonionTraceInverseAdjoint g.1 z) = linearTrace z := by
        rw [← traceBilin_one_left, ← h1, traceBilin_symm, h3OctonionTraceInverseAdjoint_traceBilin,
          traceBilin_symm, traceBilin_one_left]
      rw [hlt_adj] at hcr'
      have hs : h3OctonionTraceInverseAdjoint g.1 z = g.1 z := by
        have h1d : linearTrace (g.1 z) = linearTrace z := hltr z
        -- crossProduct 1 (((1/2) tr z) • 1 - z*) = (((1/2) tr z) • 2 • 1 - (tr z* • 1 - z*)) = z*!
        rw [← hcr']
        module
      exact hs
    rw [hid, Units.val_one, one_smul, hc]
  have hlt : ∀ u, linearTrace (g.1 u) = linearTrace u := by
    intro u
    have h1' : normCubic (1 + (1 : ℝ) • u) = normCubic (1 + (1 : ℝ) • g.1 u) := by
      simpa [map_add, map_smul, h1] using (g.2 (1 + (1 : ℝ) • u)).symm
    have h2' : normCubic (1 + (-1 : ℝ) • u) = normCubic (1 + (-1 : ℝ) • g.1 u) := by
      simpa [map_add, map_smul, h1] using (g.2 (1 + (-1 : ℝ) • u)).symm
    rw [normCubic_line, normCubic_line, adjointQuad_one, traceBilin_one_left, traceBilin_one_left,
      normCubic_one, g.2 u] at h1' h2'
    linarith [h1', h2']
  have hcross : g.1 (crossProduct x y) = crossProduct (g.1 x) (g.1 y) := by
    have ha := congrArg g.1 (adjointQuad_add x y)
    rw [map_add, map_add, ← hadj (x + y), map_add, adjointQuad_add, hadj x, hadj y] at ha
    calc g.1 (crossProduct x y)
        = (g.1 (adjointQuad x) + g.1 (crossProduct x y) + g.1 (adjointQuad y)) -
            g.1 (adjointQuad x) - g.1 (adjointQuad y) := by module
      _ = (g.1 (adjointQuad x) + crossProduct (g.1 x) (g.1 y) + g.1 (adjointQuad y)) -
            g.1 (adjointQuad x) - g.1 (adjointQuad y) := by rw [← ha]
      _ = crossProduct (g.1 x) (g.1 y) := by module
  rw [mul_trace_formula, mul_trace_formula, map_smul, map_add, map_sub, map_add, map_smul,
    map_smul, map_smul, hlt x, hlt y, h1, ← hcross, hlt (crossProduct x y)]

def h3OctonionReducedStructureFixOne : Subgroup h3OctonionReducedStructureGroup where
  carrier := {g | g.1 1 = 1}
  one_mem' := rfl
  mul_mem' := by intro g h hg hh; change g.1 (h.1 1) = 1; rw [hh, hg]
  inv_mem' := by
    intro g hg; change g.1.symm 1 = 1
    calc g.1.symm 1 = g.1.symm (g.1 1) := congrArg g.1.symm hg.symm
      _ = 1 := g.1.symm_apply_apply 1

/-- Group isomorphism `Aut(H₃(𝕆)) ≃* {g ∈ Str₀(H₃(𝕆)) | g 1 = 1}` (`F₄(-52) ⊂ E₆(-26)`). -/
def h3OctonionJordanAutMulEquivReducedStructureFixOne :
    H3OctonionJordanAut ≃* h3OctonionReducedStructureFixOne where
  toFun A := ⟨⟨A.toLinearEquiv, A.mem_reducedStructureGroup⟩, A.map_one⟩
  invFun g :=
    let hl := h3OctonionJordanAut_of_reducedStructure g.1 g.2
    ⟨g.1.1, hl.1, hl.2⟩
  left_inv A := by apply H3OctonionJordanAut.ext; rfl
  right_inv g := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Every automorphism in `Aut(H₃(𝕆))` (`F₄(-52)`) preserves `linearTrace` and the
positive-definite bilinear form `traceBilin`, proving `F₄(-52) ⊂ O(27)` is compact. -/
theorem H3OctonionJordanAut.preserves_linearTrace (e : H3OctonionJordanAut) (x : H3Octonion ℝ) :
    linearTrace (e x) = linearTrace x := by
  have h1 := e.map_one
  have hN := e.mem_reducedStructureGroup
  have h1' : normCubic (1 + (1 : ℝ) • x) = normCubic (1 + (1 : ℝ) • e x) := by
    simpa [map_add, map_smul, h1] using (hN (1 + (1 : ℝ) • x)).symm
  have h2' : normCubic (1 + (-1 : ℝ) • x) = normCubic (1 + (-1 : ℝ) • e x) := by
    simpa [map_add, map_smul, h1] using (hN (1 + (-1 : ℝ) • x)).symm
  rw [normCubic_line, normCubic_line, adjointQuad_one, traceBilin_one_left, traceBilin_one_left,
    normCubic_one, hN x] at h1' h2'
  linarith [h1', h2']

theorem H3OctonionJordanAut.preserves_traceBilin (e : H3OctonionJordanAut) (x y : H3Octonion ℝ) :
    traceBilin (e x) (e y) = traceBilin x y := by
  rw [← linearTrace_jordanMul, ← e.map_mul, e.preserves_linearTrace, linearTrace_jordanMul]

end IsotopyToSimilitudeAndReducedGroup

end InfoGeometry.Algebra
