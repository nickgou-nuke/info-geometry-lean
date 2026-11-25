/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.JordanStructureGroup
import InfoGeometry.Algebra.H3ZornCubicOperatorGeometry
import InfoGeometry.Algebra.H3ZornMcCrimmonDualIdentity
import InfoGeometry.Algebra.H3ZornAdjointProductIdentity

/-!
# Split Albert Structure Group `Str(H₃(𝕆_s))`, Reduced Structure Group `Str₀`,
  Fundamental Formula, Cubic Norm Homothety, and Isotopy–Similitude Equivalence

Directly on the full 27-dimensional split Albert Jordan algebra `H3Zorn ℝ`, this
module proves:

1. Structural quadratic-operator identities (`traceBilin_U_selfAdjoint`,
   `normCubic_adjointQuad`, `U_adjointQuad_U`, `U_U_adjointQuad`, `adjointQuad_U`)
   and **Cubic Norm Homothety** `normCubic (U X Y) = normCubic X ^ 2 * normCubic Y`.
2. Equivalence between cubic-norm similitudes and quadratic-representation
   isotopies (`g ∈ StructureGroup ℝ (H3Zorn ℝ)`), with explicit trace-adjoint
   companion `h3zornTraceAdjoint g`.
3. Every invertible `X` (`normCubic X ≠ 0`) acts via `U X ∈ StructureGroup ℝ (H3Zorn ℝ)`
   (and `∈ h3zornReducedStructureGroup` when `normCubic X = ±1`), yielding the
   universal **Fundamental Formula** `U (U X Y) Z = U X (U Y (U X Z))` for all
   `X, Y, Z : H3Zorn ℝ`.
4. The multiplicative equivalence `StructureGroup ℝ (H3Zorn ℝ) ≃* h3zornStructureGroup`,
   multiplier homomorphism `h3zornStructureGroupMultiplier : StructureGroup ℝ (H3Zorn ℝ) →* ℝˣ`
   with kernel canonically isomorphic to `h3zornReducedStructureGroup`, and both
   inclusions of `Aut(H₃(𝕆_s)) = {g ∈ Str₀(H₃(𝕆_s)) | g 1 = 1}`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn

section QuadraticAndCubicIdentities

private theorem U_add_left (X₁ X₂ Y : H3Zorn ℝ) :
    U (X₁ + X₂) Y = U X₁ Y + T X₁ Y X₂ + U X₂ Y := by
  dsimp [T]
  abel

private theorem U_smul_left (r : ℝ) (X Y : H3Zorn ℝ) :
    U (r • X) Y = (r ^ 2) • U X Y := by
  simp only [U, traceBilin_smul_left, smul_smul, adjointQuad_smul, crossProduct_smul_left,
    smul_sub]
  rw [show r * traceBilin X Y * r = r ^ 2 * traceBilin X Y by ring]

private theorem U_add_right (X Y₁ Y₂ : H3Zorn ℝ) :
    U X (Y₁ + Y₂) = U X Y₁ + U X Y₂ := by
  simp only [U, traceBilin_add_right, add_smul, crossProduct_add_right]
  abel

private theorem U_sub_right (X Y₁ Y₂ : H3Zorn ℝ) :
    U X (Y₁ - Y₂) = U X Y₁ - U X Y₂ := by
  rw [sub_eq_add_neg, show -Y₂ = (-1 : ℝ) • Y₂ by module, U_add_right]
  simp only [U, traceBilin_smul_right, crossProduct_smul_right]
  module

private theorem U_smul_right (r : ℝ) (X Y : H3Zorn ℝ) :
    U X (r • Y) = r • U X Y := by
  simp only [U, traceBilin_smul_right, smul_smul, crossProduct_smul_right, smul_sub]

theorem h3zorn_U_one (Y : H3Zorn ℝ) : U (1 : H3Zorn ℝ) Y = Y := by
  rw [U, traceBilin_symm, traceBilin_one, adjointQuad_one,
    crossProduct_symm, crossProduct_one]
  module

/-- The quadratic operator `U X` is self-adjoint with respect to `traceBilin`. -/
theorem traceBilin_U_selfAdjoint (X Y Z : H3Zorn ℝ) :
    traceBilin (U X Y) Z = traceBilin Y (U X Z) := by
  simp only [U, traceBilin_sub_left, traceBilin_smul_left,
    traceBilin_sub_right, traceBilin_smul_right]
  rw [traceBilin_symm X Y, traceBilin_symm Y X]
  have hc : traceBilin (crossProduct (adjointQuad X) Y) Z =
      traceBilin Y (crossProduct (adjointQuad X) Z) := by
    rw [crossProduct_symm (adjointQuad X) Y, traceBilin_crossProduct_assoc]
  rw [hc]
  ring

/-- The cubic norm satisfies `N(X#) = N(X)^2`. -/
theorem normCubic_adjointQuad (X : H3Zorn ℝ) :
    normCubic (adjointQuad X) = normCubic X ^ 2 := by
  have h1 := mccrimmon_identity_13 (adjointQuad X)
  have h2 := mccrimmon_identity_13 X
  have hsq : normCubic X * (3 * normCubic X) = 3 * normCubic X ^ 2 := by ring
  rw [adjointQuad_adjointQuad, traceBilin_smul_left, traceBilin_symm, h2] at h1
  linarith [h1, hsq]

/-- Evaluating `U X` on `X#` gives `N(X) • X`. -/
theorem U_self_adjointQuad (X : H3Zorn ℝ) :
    U X (adjointQuad X) = normCubic X • X := by
  rw [U, traceBilin_symm, mccrimmon_identity_13, crossProduct_self,
    adjointQuad_adjointQuad]
  module

/-- Evaluating `U (X#)` on `X` gives `N(X) • X#`. -/
theorem U_adjointQuad_self (X : H3Zorn ℝ) :
    U (adjointQuad X) X = normCubic X • adjointQuad X := by
  rw [U, mccrimmon_identity_13, adjointQuad_adjointQuad, crossProduct_smul_left,
    crossProduct_self]
  module

/-- Exact left-adjoint inverse identity `U (X#) (U X Y) = N(X)^2 • Y`. -/
theorem U_adjointQuad_U (X Y : H3Zorn ℝ) :
    U (adjointQuad X) (U X Y) = normCubic X ^ 2 • Y := by
  conv_lhs => arg 2; rw [U]
  rw [U_sub_right, U_smul_right, U_adjointQuad_self]
  have hm := mccrimmon_identity_17 (adjointQuad X) Y
  rw [adjointQuad_adjointQuad, traceBilin_smul_left, normCubic_adjointQuad] at hm
  rw [hm]
  module

/-- Exact right-adjoint inverse identity `U X (U (X#) Y) = N(X)^2 • Y`. -/
theorem U_U_adjointQuad (X Y : H3Zorn ℝ) :
    U X (U (adjointQuad X) Y) = normCubic X ^ 2 • Y := by
  have h1 : U (adjointQuad X) Y =
      traceBilin (adjointQuad X) Y • adjointQuad X -
        normCubic X • crossProduct X Y := by
    rw [U, adjointQuad_adjointQuad, crossProduct_smul_left]
  rw [h1, U_sub_right, U_smul_right, U_smul_right, U_self_adjointQuad,
    mccrimmon_identity_17]
  module

private theorem adjointQuad_sub (A B : H3Zorn ℝ) :
    adjointQuad (A - B) = adjointQuad A - crossProduct A B + adjointQuad B := by
  rw [sub_eq_add_neg, show -B = (-1 : ℝ) • B by module, adjointQuad_add,
    crossProduct_smul_right, adjointQuad_smul]
  module

/-- Structural adjoint-covariance identity `(U X Y)# = U (X#) (Y#)`. -/
theorem adjointQuad_U (X Y : H3Zorn ℝ) :
    adjointQuad (U X Y) = U (adjointQuad X) (adjointQuad Y) := by
  rw [U, adjointQuad_sub, adjointQuad_smul, crossProduct_smul_left,
    mccrimmon_identity_19 X Y]
  have hm := mccrimmon_identity_11 (adjointQuad X) Y
  rw [adjointQuad_adjointQuad] at hm
  have hadjB : adjointQuad (crossProduct (adjointQuad X) Y) =
      (normCubic X * traceBilin X Y) • Y +
        traceBilin (adjointQuad Y) (adjointQuad X) • adjointQuad X -
        crossProduct (adjointQuad (adjointQuad X)) (adjointQuad Y) := by
    rw [eq_sub_of_add_eq' hm, adjointQuad_adjointQuad, traceBilin_smul_left]
  rw [hadjB, U, traceBilin_symm (adjointQuad X) (adjointQuad Y)]
  module

/-- **Cubic Norm Homothety**: `N(U X Y) = N(X)^2 * N(Y)` on all of `H3Zorn ℝ`. -/
theorem normCubic_U (X Y : H3Zorn ℝ) :
    normCubic (U X Y) = normCubic X ^ 2 * normCubic Y := by
  have h1 := mccrimmon_identity_13 (U X Y)
  have h2 := mccrimmon_identity_13 Y
  rw [adjointQuad_U, traceBilin_U_selfAdjoint, U_adjointQuad_U,
    traceBilin_smul_right, h2] at h1
  linarith

end QuadraticAndCubicIdentities

section PolynomialHelpers

private theorem real_cubic_ne_zero_near_zero (a b c : ℝ) :
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
        calc
          |r| ≤ 2 * min (1 / 2) (1 / (8 * (|a| + |b| + |c| + 1))) := hr
          _ ≤ 2 * (1 / (8 * (|a| + |b| + |c| + 1))) := by linarith
          _ = 1 / (4 * (|a| + |b| + |c| + 1)) := by field_simp; ring
      calc
        |r| * (|a| + |b| + |c| + 1)
            ≤ (1 / (4 * (|a| + |b| + |c| + 1))) * (|a| + |b| + |c| + 1) := by
          gcongr
        _ = 1 / 4 := by field_simp [hdenom.ne']
    have hr_sq : |r ^ 2| ≤ |r| := by
      rw [sq, abs_mul]
      nlinarith [abs_nonneg r]
    have hr_cu : |r ^ 3| ≤ |r| := by
      rw [pow_succ, abs_mul]
      nlinarith [abs_nonneg r, sq_abs r]
    have hbound : |r * a + r ^ 2 * b + r ^ 3 * c| ≤ 1 / 4 := by
      calc
        |r * a + r ^ 2 * b + r ^ 3 * c|
            ≤ |r * a + r ^ 2 * b| + |r ^ 3 * c| := abs_add_le _ _
        _ ≤ |r * a| + |r ^ 2 * b| + |r ^ 3 * c| := by linarith [abs_add_le (r * a) (r ^ 2 * b)]
        _ = |r| * |a| + |r ^ 2| * |b| + |r ^ 3| * |c| := by simp [abs_mul]
        _ ≤ |r| * |a| + |r| * |b| + |r| * |c| := by
          gcongr
        _ = |r| * (|a| + |b| + |c|) := by ring
        _ ≤ |r| * (|a| + |b| + |c| + 1) := by nlinarith [abs_nonneg r]
        _ ≤ 1 / 4 := hr2
    have hneg : -(1 / 4 : ℝ) ≤ r * a + r ^ 2 * b + r ^ 3 * c := (abs_le.mp hbound).1
    linarith

private theorem extract_deg4_leading (δ : ℝ) (hδ : 0 < δ)
    (c₀ c₁ c₂ c₃ c₄ : H3Zorn ℝ)
    (h : ∀ r : ℝ, |r| ≤ 2 * δ →
      c₀ + r • c₁ + r ^ 2 • c₂ + r ^ 3 • c₃ + r ^ 4 • c₄ = 0) :
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
    rw [h0, h1, hm1, h2, hm2]
    module
  have hsimp : (24 * δ ^ 4) • c₄ = 0 := by
    calc
      (24 * δ ^ 4) • c₄ =
          (6 : ℝ) • (c₀ + (0 : ℝ) • c₁ + (0 : ℝ) ^ 2 • c₂ + (0 : ℝ) ^ 3 • c₃ + (0 : ℝ) ^ 4 • c₄) -
          (4 : ℝ) • (c₀ + δ • c₁ + δ ^ 2 • c₂ + δ ^ 3 • c₃ + δ ^ 4 • c₄) -
          (4 : ℝ) • (c₀ + (-δ) • c₁ + (-δ) ^ 2 • c₂ + (-δ) ^ 3 • c₃ + (-δ) ^ 4 • c₄) +
          (c₀ + (2 * δ) • c₁ + (2 * δ) ^ 2 • c₂ + (2 * δ) ^ 3 • c₃ + (2 * δ) ^ 4 • c₄) +
          (c₀ + (-2 * δ) • c₁ + (-2 * δ) ^ 2 • c₂ + (-2 * δ) ^ 3 • c₃ + (-2 * δ) ^ 4 • c₄) := by
        module
      _ = 0 := hcomb
  rcases smul_eq_zero.mp hsimp with h24 | hc4
  · exfalso
    have hpow : 0 < 24 * δ ^ 4 := by positivity
    linarith
  · exact hc4

private theorem extract_real_deg3_leading (δ : ℝ) (hδ : 0 < δ)
    (a₀ a₁ a₂ a₃ : ℝ)
    (h : ∀ r : ℝ, |r| ≤ 2 * δ →
      a₀ + r * a₁ + r ^ 2 * a₂ + r ^ 3 * a₃ = 0) :
    a₃ = 0 := by
  have h1 := h δ (by rw [abs_of_pos hδ]; linarith)
  have hm1 := h (-δ) (by rw [abs_neg, abs_of_pos hδ]; linarith)
  have h2 := h (2 * δ) (by rw [abs_of_pos (by linarith)])
  have hm2 := h (-2 * δ) (by rw [show (-2 : ℝ) * δ = -(2 * δ) by ring, abs_neg, abs_of_pos (by linarith)])
  have hcomb : 12 * δ ^ 3 * a₃ = 0 := by
    nlinarith [h1, hm1, h2, hm2]
  rcases mul_eq_zero.mp hcomb with h12 | ha3
  · exfalso
    have : 0 < 12 * δ ^ 3 := by positivity
    linarith
  · exact ha3

end PolynomialHelpers

section SimilitudeToIsotopy

/-- Trace-adjoint equivalence for any `e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ`:
forward map is `e† = h3zornTraceAdjoint e.toLinearMap`, inverse is `(e⁻¹)†`. -/
def h3zornTraceAdjointEquiv (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) :
    H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ :=
  LinearEquiv.ofLinearMap
    (h3zornTraceAdjoint e.toLinearMap)
    (h3zornTraceInverseAdjoint e)
    (by
      apply LinearMap.ext
      intro x
      apply H3Zorn.eq_of_traceBilin_left_eq
      intro y
      change traceBilin (h3zornTraceAdjoint e.toLinearMap
          (h3zornTraceInverseAdjoint e x)) y = traceBilin x y
      rw [h3zornTraceAdjoint_pair, h3zornTraceInverseAdjoint,
        h3zornTraceAdjoint_pair]
      simp)
    (by
      apply LinearMap.ext
      intro x
      apply H3Zorn.eq_of_traceBilin_left_eq
      intro y
      change traceBilin (h3zornTraceInverseAdjoint e
          (h3zornTraceAdjoint e.toLinearMap x)) y = traceBilin x y
      rw [h3zornTraceInverseAdjoint, h3zornTraceAdjoint_pair,
        h3zornTraceAdjoint_pair]
      simp)

@[simp] theorem h3zornTraceAdjointEquiv_apply (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (x : H3Zorn ℝ) :
    h3zornTraceAdjointEquiv e x = h3zornTraceAdjoint e.toLinearMap x := rfl

@[simp] theorem h3zornTraceAdjointEquiv_symm_apply (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (x : H3Zorn ℝ) :
    (h3zornTraceAdjointEquiv e).symm x = h3zornTraceInverseAdjoint e x := rfl

theorem h3zornTraceInverseAdjoint_traceBilin (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (x y : H3Zorn ℝ) :
    traceBilin (h3zornTraceInverseAdjoint e x) (e y) = traceBilin x y := by
  rw [h3zornTraceInverseAdjoint, h3zornTraceAdjoint_pair]
  simp

theorem h3zorn_adjointQuad_similitude_intertwines
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x)
    (x : H3Zorn ℝ) :
    adjointQuad (e x) =
      (u : ℝ) • h3zornTraceInverseAdjoint e (adjointQuad x) := by
  have hc := h3zorn_crossProduct_similitude_intertwines e u hN x x
  rw [crossProduct_self, crossProduct_self, map_smul] at hc
  have h' := congrArg (fun W : H3Zorn ℝ => (1 / 2 : ℝ) • W) hc
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using h'

/-- Under a cubic-norm similitude `N(e x) = u * N(x)`, the inverse trace adjoint
`(e⁻¹)†` intertwines the Albert cross product up to `u⁻¹`:
`u • (e⁻¹)† A × (e⁻¹)† B = e (A × B)`. -/
theorem h3zorn_traceInverseAdjoint_crossProduct_intertwines
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x)
    (A B : H3Zorn ℝ) :
    (u : ℝ) • crossProduct (h3zornTraceInverseAdjoint e A)
        (h3zornTraceInverseAdjoint e B) =
      e (crossProduct A B) := by
  let eInvAdj := h3zornTraceInverseAdjoint e
  let F : H3Zorn ℝ → H3Zorn ℝ → H3Zorn ℝ := fun X Y =>
    (u : ℝ) • crossProduct (eInvAdj X) (eInvAdj Y) - e (crossProduct X Y)
  apply sub_eq_zero.mp
  change F A B = 0
  have hu : (u : ℝ) ≠ 0 := Units.ne_zero u
  have hadj1 : adjointQuad (e (1 : H3Zorn ℝ)) = (u : ℝ) • eInvAdj 1 := by
    have h := h3zorn_adjointQuad_similitude_intertwines e u hN 1
    simpa [adjointQuad_one] using h
  have hnorm1 : normCubic (e (1 : H3Zorn ℝ)) = (u : ℝ) := by
    simpa [normCubic_one] using hN 1
  have hcross1_inv (Y : H3Zorn ℝ) :
      crossProduct 1 (((1 / 2 : ℝ) * linearTrace Y) • (1 : H3Zorn ℝ) - Y) = Y := by
    rw [crossProduct_symm, crossProduct_one]
    have hlt : linearTrace (((1 / 2 : ℝ) * linearTrace Y) • (1 : H3Zorn ℝ) - Y) =
        (1 / 2 : ℝ) * linearTrace Y := by
      rw [sub_eq_add_neg, linearTrace_add, linearTrace_smul]
      have h1 : linearTrace (1 : H3Zorn ℝ) = 3 := by change (1 : ℝ) + 1 + 1 = 3; norm_num
      have hneg : linearTrace (-Y) = -linearTrace Y := by
        rw [show -Y = (-1 : ℝ) • Y by module, linearTrace_smul]; ring
      rw [h1, hneg]
      ring
    rw [hlt]
    module
  have hF1 : ∀ Y : H3Zorn ℝ, F 1 Y = 0 := by
    have hF1cross : ∀ Z : H3Zorn ℝ, F 1 (crossProduct 1 Z) = 0 := by
      intro Z
      have hm := mccrimmon_identity_10 (e 1) (e Z)
      rw [hadj1, hnorm1, crossProduct_smul_left,
        h3zorn_crossProduct_similitude_intertwines e u hN 1 Z,
        crossProduct_smul_right, traceBilin_smul_left,
        h3zornTraceInverseAdjoint_traceBilin] at hm
      have hmc := mccrimmon_identity_10 (1 : H3Zorn ℝ) Z
      rw [adjointQuad_one, normCubic_one] at hmc
      have hec := congrArg (fun W : H3Zorn ℝ => (u : ℝ) • e W) hmc
      rw [map_add, map_smul, map_smul, smul_add] at hec
      have hm_eq : (u : ℝ) • ((u : ℝ) • crossProduct (eInvAdj 1)
            (eInvAdj (crossProduct 1 Z))) =
          (u : ℝ) • e (crossProduct 1 (crossProduct 1 Z)) := by
        calc
          (u : ℝ) • ((u : ℝ) • crossProduct (eInvAdj 1)
                (eInvAdj (crossProduct 1 Z))) =
              (u : ℝ) • (u : ℝ) • crossProduct (eInvAdj 1)
                (h3zornTraceInverseAdjoint e (crossProduct 1 Z)) := rfl
          _ = (u : ℝ) • e Z + ((u : ℝ) * traceBilin 1 Z) • e 1 := hm
          _ = (u : ℝ) • e (crossProduct 1 (crossProduct 1 Z)) := by
            rw [hec]
            module
      have hzero : (u : ℝ) • F 1 (crossProduct 1 Z) = 0 := by
        dsimp [F]
        rw [smul_sub, hm_eq, sub_self]
        rfl
      exact (smul_eq_zero_iff_right hu).mp hzero
    intro Y
    rw [← hcross1_inv Y]
    exact hF1cross (((1 / 2 : ℝ) * linearTrace Y) • (1 : H3Zorn ℝ) - Y)
  have hFdiag : ∀ Y : H3Zorn ℝ, F Y Y = 0 := by
    have hFcross : ∀ Z : H3Zorn ℝ,
        F (crossProduct 1 Z) (crossProduct 1 Z) = 0 := by
      intro Z
      have hm := mccrimmon_identity_11 (e 1) (e Z)
      rw [hadj1, h3zorn_adjointQuad_similitude_intertwines e u hN Z,
        crossProduct_smul_left, crossProduct_smul_right,
        h3zorn_crossProduct_similitude_intertwines e u hN 1 Z,
        adjointQuad_smul, traceBilin_smul_left,
        h3zornTraceInverseAdjoint_traceBilin,
        traceBilin_smul_left, h3zornTraceInverseAdjoint_traceBilin] at hm
      have hmc := mccrimmon_identity_11 (1 : H3Zorn ℝ) Z
      rw [adjointQuad_one] at hmc
      have hec := congrArg (fun W : H3Zorn ℝ => (u : ℝ) • e W) hmc
      simp only [map_add, map_smul, smul_add] at hec
      have hm_eq :
          ((u : ℝ) ^ 2) • (crossProduct (eInvAdj 1) (eInvAdj (adjointQuad Z)) +
              adjointQuad (eInvAdj (crossProduct 1 Z))) =
            (u : ℝ) • e (crossProduct 1 (adjointQuad Z) +
              adjointQuad (crossProduct 1 Z)) := by
        have hstep1 :
            ((u : ℝ) ^ 2) • (crossProduct (eInvAdj 1) (eInvAdj (adjointQuad Z)) +
                adjointQuad (eInvAdj (crossProduct 1 Z))) =
              (u : ℝ) • (u : ℝ) • crossProduct (eInvAdj 1)
                  (h3zornTraceInverseAdjoint e (adjointQuad Z)) +
                ((u : ℝ) ^ 2) • adjointQuad
                  (h3zornTraceInverseAdjoint e (crossProduct 1 Z)) := by
          rw [smul_add, smul_smul, ← sq]
        rw [hstep1, hm, map_add]
        have hsum :
            ((u : ℝ) * traceBilin 1 Z) • e Z +
                ((u : ℝ) * traceBilin (adjointQuad Z) 1) • e 1 =
              (u : ℝ) • (e (crossProduct 1 (adjointQuad Z)) +
                e (adjointQuad (crossProduct 1 Z))) := by
          calc
            ((u : ℝ) * traceBilin 1 Z) • e Z +
                ((u : ℝ) * traceBilin (adjointQuad Z) 1) • e 1 =
              (u : ℝ) • traceBilin 1 Z • e Z +
                (u : ℝ) • traceBilin (adjointQuad Z) 1 • e 1 := by
              rw [smul_smul, smul_smul]
            _ = (u : ℝ) • e (crossProduct 1 (adjointQuad Z)) +
                (u : ℝ) • e (adjointQuad (crossProduct 1 Z)) := hec.symm
            _ = (u : ℝ) • (e (crossProduct 1 (adjointQuad Z)) +
                e (adjointQuad (crossProduct 1 Z))) := (smul_add _ _ _).symm
        exact hsum
      have hcancel_u : (u : ℝ) • ((u : ℝ) • (crossProduct (eInvAdj 1)
            (eInvAdj (adjointQuad Z)) + adjointQuad (eInvAdj (crossProduct 1 Z))) -
            e (crossProduct 1 (adjointQuad Z) + adjointQuad (crossProduct 1 Z))) = 0 := by
        rw [smul_sub, smul_smul, ← sq, hm_eq, sub_self]
      have hinner := (smul_eq_zero_iff_right hu).mp hcancel_u
      have h2 := congrArg (fun W : H3Zorn ℝ => (2 : ℝ) • W) hinner
      have hrel : (2 : ℝ) • F 1 (adjointQuad Z) +
          F (crossProduct 1 Z) (crossProduct 1 Z) = 0 := by
        calc
          (2 : ℝ) • F 1 (adjointQuad Z) + F (crossProduct 1 Z) (crossProduct 1 Z) =
              (2 : ℝ) • ((u : ℝ) • (crossProduct (eInvAdj 1)
                  (eInvAdj (adjointQuad Z)) + adjointQuad (eInvAdj (crossProduct 1 Z))) -
                e (crossProduct 1 (adjointQuad Z) + adjointQuad (crossProduct 1 Z))) := by
            dsimp [F]
            rw [crossProduct_self, crossProduct_self, map_add, map_smul]
            module
          _ = 0 := by rw [h2, smul_zero]
      rw [hF1 (adjointQuad Z), smul_zero, zero_add] at hrel
      exact hrel
    intro Y
    rw [← hcross1_inv Y]
    exact hFcross (((1 / 2 : ℝ) * linearTrace Y) • (1 : H3Zorn ℝ) - Y)
  have hFpol : (2 : ℝ) • F A B = F (A + B) (A + B) - F A A - F B B := by
    dsimp [F]
    simp only [map_add, crossProduct_add_left, crossProduct_add_right]
    rw [crossProduct_symm (eInvAdj B) (eInvAdj A), crossProduct_symm B A]
    module
  rw [hFdiag (A + B), hFdiag A, hFdiag B] at hFpol
  have h2 : (2 : ℝ) • F A B = 0 := by simpa using hFpol
  exact (smul_eq_zero_iff_right (by norm_num : (2 : ℝ) ≠ 0)).mp h2

/-- A cubic-norm similitude `N(e x) = u * N(x)` satisfies the quadratic
representation isotopy `U (e x) Z = e (U x (e† Z))`. -/
theorem h3zorn_U_similitude_intertwines
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x)
    (X Z : H3Zorn ℝ) :
    U (e X) Z = e (U X (h3zornTraceAdjoint e.toLinearMap Z)) := by
  have hZ : Z = h3zornTraceInverseAdjoint e (h3zornTraceAdjoint e.toLinearMap Z) := by
    exact ((h3zornTraceAdjointEquiv e).symm_apply_apply Z).symm
  have hcross : crossProduct (adjointQuad (e X)) Z =
      e (crossProduct (adjointQuad X) (h3zornTraceAdjoint e.toLinearMap Z)) := by
    rw [h3zorn_adjointQuad_similitude_intertwines e u hN X]
    conv_lhs => rw [hZ]
    rw [crossProduct_smul_left]
    exact h3zorn_traceInverseAdjoint_crossProduct_intertwines e u hN
      (adjointQuad X) (h3zornTraceAdjoint e.toLinearMap Z)
  have htr : traceBilin (e X) Z =
      traceBilin X (h3zornTraceAdjoint e.toLinearMap Z) := by
    rw [traceBilin_symm (e X) Z]
    change traceBilin Z (e.toLinearMap X) = _
    rw [← h3zornTraceAdjoint_pair e.toLinearMap Z X, traceBilin_symm]
  simp only [U, map_sub, map_smul]
  rw [hcross, htr]

theorem h3zorn_similitude_imp_mem_StructureGroup
    (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) (u : ℝˣ)
    (hN : ∀ x, normCubic (e x) = (u : ℝ) * normCubic x) :
    e ∈ StructureGroup ℝ (H3Zorn ℝ) := by
  refine ⟨h3zornTraceAdjointEquiv e, fun x => ?_⟩
  apply LinearMap.ext
  intro y
  change jordanU (R := ℝ) (e x) y =
    e (jordanU (R := ℝ) x (h3zornTraceAdjoint e.toLinearMap y))
  rw [jordanU_eq_h3Zorn_U, jordanU_eq_h3Zorn_U]
  exact h3zorn_U_similitude_intertwines e u hN x y

end SimilitudeToIsotopy

section InvertibleUAndFundamentalFormula

/-- For any invertible element `X : H3Zorn ℝ` (`normCubic X ≠ 0`), `U X` is a
linear equivalence with explicit inverse `N(X)^(-2) • U (X#)`. -/
def h3zornULinearEquiv (X : H3Zorn ℝ) (hN : normCubic X ≠ 0) :
    H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ :=
  LinearEquiv.ofLinearMap
    (jordanU (R := ℝ) X)
    ((normCubic X ^ 2)⁻¹ • jordanU (R := ℝ) (adjointQuad X))
    (by
      apply LinearMap.ext
      intro y
      have hsq : normCubic X ^ 2 ≠ 0 := pow_ne_zero 2 hN
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply, jordanU_eq_h3Zorn_U, U_smul_right, U_U_adjointQuad,
        smul_smul]
      rw [inv_mul_cancel₀ hsq, one_smul])
    (by
      apply LinearMap.ext
      intro y
      have hsq : normCubic X ^ 2 ≠ 0 := pow_ne_zero 2 hN
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply, jordanU_eq_h3Zorn_U, U_adjointQuad_U, smul_smul]
      rw [inv_mul_cancel₀ hsq, one_smul])

@[simp] theorem h3zornULinearEquiv_apply (X : H3Zorn ℝ) (hN : normCubic X ≠ 0)
    (Y : H3Zorn ℝ) :
    h3zornULinearEquiv X hN Y = U X Y :=
  jordanU_eq_h3Zorn_U X Y

/-- `U X` is its own trace adjoint. -/
theorem h3zornTraceAdjoint_h3zornULinearEquiv (X : H3Zorn ℝ) (hN : normCubic X ≠ 0) :
    h3zornTraceAdjoint (h3zornULinearEquiv X hN).toLinearMap =
      (h3zornULinearEquiv X hN).toLinearMap := by
  apply LinearMap.ext
  intro y
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  rw [h3zornTraceAdjoint_pair]
  simp only [LinearEquiv.coe_toLinearMap, h3zornULinearEquiv_apply]
  exact (traceBilin_U_selfAdjoint X y z).symm

/-- For every invertible `X` (`normCubic X ≠ 0`), `U X` belongs to `StructureGroup ℝ (H3Zorn ℝ)`. -/
theorem h3zornULinearEquiv_mem_StructureGroup (X : H3Zorn ℝ) (hN : normCubic X ≠ 0) :
    h3zornULinearEquiv X hN ∈ StructureGroup ℝ (H3Zorn ℝ) := by
  have hsq : normCubic X ^ 2 ≠ 0 := pow_ne_zero 2 hN
  refine h3zorn_similitude_imp_mem_StructureGroup (h3zornULinearEquiv X hN)
    (Units.mk0 (normCubic X ^ 2) hsq) fun y => ?_
  simpa using normCubic_U X y

/-- When `normCubic X = 1` or `normCubic X = -1`, `U X` preserves `normCubic`
and therefore lies in `h3zornReducedStructureGroup`. -/
theorem h3zornULinearEquiv_mem_reducedStructureGroup (X : H3Zorn ℝ)
    (hN : normCubic X ≠ 0) (hpm : normCubic X = 1 ∨ normCubic X = -1) :
    h3zornULinearEquiv X hN ∈ h3zornReducedStructureGroup := by
  intro y
  have hsq : normCubic X ^ 2 = 1 := by
    rcases hpm with h | h <;> rw [h] <;> norm_num
  rw [h3zornULinearEquiv_apply, normCubic_U, hsq, one_mul]

/-- The Fundamental Formula for invertible `X` (`normCubic X ≠ 0`). -/
theorem h3zorn_U_fundamental_of_normCubic_ne_zero (X : H3Zorn ℝ)
    (hN : normCubic X ≠ 0) (Y Z : H3Zorn ℝ) :
    U (U X Y) Z = U X (U Y (U X Z)) := by
  have hsq : normCubic X ^ 2 ≠ 0 := pow_ne_zero 2 hN
  have h := h3zorn_U_similitude_intertwines (h3zornULinearEquiv X hN)
    (Units.mk0 (normCubic X ^ 2) hsq)
    (fun w => by simpa using normCubic_U X w) Y Z
  rw [h3zornULinearEquiv_apply, h3zornULinearEquiv_apply,
    h3zornTraceAdjoint_h3zornULinearEquiv] at h
  simpa using h

/-- **Universal Fundamental Formula** on the full 27D split Albert algebra
`H3Zorn ℝ`: `U (U X Y) Z = U X (U Y (U X Z))` for all `X, Y, Z : H3Zorn ℝ`. -/
theorem h3zorn_U_fundamental (X Y Z : H3Zorn ℝ) :
    U (U X Y) Z = U X (U Y (U X Z)) := by
  let a := traceBilin (adjointQuad (1 : H3Zorn ℝ)) X
  let b := traceBilin (adjointQuad X) (1 : H3Zorn ℝ)
  let c := normCubic X
  obtain ⟨δ, hδpos, hδ⟩ := real_cubic_ne_zero_near_zero a b c
  have hline : ∀ r : ℝ, |r| ≤ 2 * δ →
      U (U (1 + r • X) Y) Z = U (1 + r • X) (U Y (U (1 + r • X) Z)) := by
    intro r hr
    have hnr : normCubic (1 + r • X) ≠ 0 := by
      rw [normCubic_line, normCubic_one]
      exact hδ r hr
    exact h3zorn_U_fundamental_of_normCubic_ne_zero (1 + r • X) hnr Y Z
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
      rw [U_add_left, T_smul_right, U_smul_left]
      dsimp [A, B, C]
      module
    rw [hU, U_add_left, T_add_right, T_smul_right, T_smul_right,
      U_add_left, U_smul_left, U_smul_left, T_smul_left, T_smul_right]
    have hs1 : r • r ^ 2 • T B Z C = r ^ 3 • L3 := by
      rw [smul_smul]
      congr 1
      ring
    have hs2 : (r ^ 2) ^ 2 • U C Z = r ^ 4 • L4 := by
      congr 1
      ring
    dsimp [L0, L1, L2, L3, L4]
    rw [hs1, hs2]
    module
  have hRHS : ∀ r : ℝ, U (1 + r • X) (U Y (U (1 + r • X) Z)) =
      R0 + r • R1 + r ^ 2 • R2 + r ^ 3 • R3 + r ^ 4 • R4 := by
    intro r
    have hU : U (1 + r • X) Z = A' + (r • B' + r ^ 2 • C') := by
      rw [U_add_left, T_smul_right, U_smul_left]
      dsimp [A', B', C']
      module
    rw [hU, U_add_right Y A', U_add_right Y (r • B') (r ^ 2 • C'),
      U_smul_right r Y B', U_smul_right (r ^ 2) Y C']
    change U (1 + r • X) (P + (r • Q + r ^ 2 • R)) = _
    rw [U_add_right, U_add_right, U_smul_right, U_smul_right]
    rw [U_add_left 1 (r • X) P, U_add_left 1 (r • X) Q, U_add_left 1 (r • X) R,
      T_smul_right, T_smul_right, T_smul_right,
      U_smul_left, U_smul_left, U_smul_left]
    simp only [smul_add, smul_smul]
    dsimp [R0, R1, R2, R3, R4]
    have h4 : r ^ 2 * r ^ 2 = r ^ 4 := by ring
    have h3 : r ^ 2 * r = r ^ 3 := by ring
    have h3' : r * r ^ 2 = r ^ 3 := by ring
    have h2 : r * r = r ^ 2 := by ring
    rw [h4, h3, h3', h2]
    module
  have hc4 : L4 - R4 = 0 := by
    refine extract_deg4_leading δ hδpos (L0 - R0) (L1 - R1) (L2 - R2) (L3 - R3) (L4 - R4) ?_
    intro r hr
    have h := sub_eq_zero.mpr (hline r hr)
    rw [hLHS r, hRHS r] at h
    convert h using 1
    module
  exact sub_eq_zero.mp hc4

/-- Operator-level Fundamental Formula for `jordanU` on `H3Zorn ℝ`. -/
theorem jordanU_h3Zorn_fundamental (X Y : H3Zorn ℝ) :
    jordanU (R := ℝ) (jordanU (R := ℝ) X Y) =
      (jordanU (R := ℝ) X).comp ((jordanU (R := ℝ) Y).comp (jordanU (R := ℝ) X)) := by
  apply LinearMap.ext
  intro Z
  change jordanU (R := ℝ) (jordanU (R := ℝ) X Y) Z =
    jordanU (R := ℝ) X (jordanU (R := ℝ) Y (jordanU (R := ℝ) X Z))
  simp only [jordanU_eq_h3Zorn_U]
  exact h3zorn_U_fundamental X Y Z

end InvertibleUAndFundamentalFormula

section IsotopyToSimilitudeAndEquivalences

/-- Structural identity needed to recover cubic-norm similitude from a Jordan isotopy:
`U y (U b y) - T(b, y) U y b + T(y#, b#) y = N(y) • b#`. -/
theorem h3zorn_isotopy_cubic_identity (y b : H3Zorn ℝ) :
    U y (U b y) - traceBilin b y • U y b +
        traceBilin (adjointQuad y) (adjointQuad b) • y =
      normCubic y • adjointQuad b := by
  have hUb : U b y = traceBilin b y • b - crossProduct (adjointQuad b) y := rfl
  rw [hUb, crossProduct_symm (adjointQuad b) y, U_sub_right, U_smul_right,
    mccrimmon_identity_17 y (adjointQuad b)]
  module

private theorem det3_cofactor_cancel {c₀ c₁ c₂ x₁ x₂ x₃ u₁ u₂ u₃ : ℝ}
    (h1 : c₂ * u₁ + c₁ * x₁ + c₀ = 0)
    (h2 : c₂ * u₂ + c₁ * x₂ + c₀ = 0)
    (h3 : c₂ * u₃ + c₁ * x₃ + c₀ = 0) :
    ((x₂ * u₃ - u₂ * x₃) - (x₁ * u₃ - u₁ * x₃) + (x₁ * u₂ - u₁ * x₂)) * c₀ = 0 := by
  have hcomb :
      (x₂ * u₃ - u₂ * x₃) * (c₂ * u₁ + c₁ * x₁ + c₀) -
      (x₁ * u₃ - u₁ * x₃) * (c₂ * u₂ + c₁ * x₂ + c₀) +
      (x₁ * u₂ - u₁ * x₂) * (c₂ * u₃ + c₁ * x₃ + c₀) = 0 := by
    rw [h1, h2, h3]
    ring
  calc
    ((x₂ * u₃ - u₂ * x₃) - (x₁ * u₃ - u₁ * x₃) + (x₁ * u₂ - u₁ * x₂)) * c₀ =
        (x₂ * u₃ - u₂ * x₃) * (c₂ * u₁ + c₁ * x₁ + c₀) -
        (x₁ * u₃ - u₁ * x₃) * (c₂ * u₂ + c₁ * x₂ + c₀) +
        (x₁ * u₂ - u₁ * x₂) * (c₂ * u₃ + c₁ * x₃ + c₀) := by ring
    _ = 0 := hcomb

/-- **Isotopy ⇒ Cubic-Norm Similitude**: every element `g ∈ StructureGroup ℝ (H3Zorn ℝ)`
satisfies `N(g x) = N(g 1) * N(x)` for all `x : H3Zorn ℝ`, with `N(g 1) ≠ 0`. -/
theorem h3zorn_isotopy_imp_similitude (g : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ)
    (hg : g ∈ StructureGroup ℝ (H3Zorn ℝ)) :
    normCubic (g 1) ≠ 0 ∧
      ∀ x : H3Zorn ℝ, normCubic (g x) = normCubic (g 1) * normCubic x := by
  rcases hg with ⟨gSharp, hSharp⟩
  have hU : ∀ x z : H3Zorn ℝ, U (g x) z = g (U x (gSharp z)) := by
    intro x z
    have hx := LinearMap.ext_iff.mp (hSharp x) z
    simpa only [jordanU_eq_h3Zorn_U, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_toLinearMap] using hx
  have hU1 : ∀ z : H3Zorn ℝ, U (g 1) z = g (gSharp z) := by
    intro z
    rw [hU 1 z, h3zorn_U_one]
  let y₀ := gSharp.symm (g.symm 1)
  have hy₀ : U (g 1) y₀ = 1 := by
    rw [hU1 y₀]
    simp [y₀]
  have hna : normCubic (g 1) ≠ 0 := by
    intro hz
    have hn := congrArg normCubic hy₀
    rw [normCubic_U, hz, zero_pow (by norm_num), zero_mul, normCubic_one] at hn
    exact one_ne_zero hn.symm
  refine ⟨hna, ?_⟩
  let a := g 1
  let b : H3Zorn ℝ := (normCubic a)⁻¹ • adjointQuad a
  have hUb : ∀ z : H3Zorn ℝ, U a (U b z) = z := by
    intro z
    have hb_eq : U b z = ((normCubic a)⁻¹ ^ 2) • U (adjointQuad a) z := U_smul_left _ _ _
    rw [hb_eq, U_smul_right, U_U_adjointQuad, smul_smul]
    have hinv : (normCubic a)⁻¹ ^ 2 * normCubic a ^ 2 = 1 := by
      calc
        (normCubic a)⁻¹ ^ 2 * normCubic a ^ 2 =
            ((normCubic a)⁻¹ * normCubic a) ^ 2 := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hna, one_pow]
    rw [hinv, one_smul]
  have hSharpUb : ∀ y : H3Zorn ℝ, gSharp (U b (g y)) = y := by
    intro y
    apply g.injective
    rw [← hU1 (U b (g y)), hUb]
  have hUgb : ∀ x y : H3Zorn ℝ, U (g x) (U b (g y)) = g (U x y) := by
    intro x y
    rw [hU x (U b (g y)), hSharpUb y]
  have hUba : U b a = b := by
    have hb_eq : U b a = ((normCubic a)⁻¹ ^ 2) • U (adjointQuad a) a := U_smul_left _ _ _
    rw [hb_eq, U_adjointQuad_self, smul_smul]
    dsimp [b]
    congr 1
    calc
      (normCubic a)⁻¹ ^ 2 * normCubic a =
          ((normCubic a)⁻¹ * normCubic a) * (normCubic a)⁻¹ := by ring
      _ = (normCubic a)⁻¹ := by rw [inv_mul_cancel₀ hna, one_mul]
  have hUgxb : ∀ x : H3Zorn ℝ, U (g x) b = g (U x 1) := by
    intro x
    calc
      U (g x) b = U (g x) (U b (g 1)) := by conv_lhs => rw [← hUba]
      _ = g (U x 1) := hUgb x 1
  have hadjb : adjointQuad b = (normCubic a)⁻¹ • a := by
    dsimp [b]
    rw [adjointQuad_smul, adjointQuad_adjointQuad, smul_smul]
    congr 1
    calc
      (normCubic a)⁻¹ ^ 2 * normCubic a =
          ((normCubic a)⁻¹ * normCubic a) * (normCubic a)⁻¹ := by ring
      _ = (normCubic a)⁻¹ := by rw [inv_mul_cancel₀ hna, one_mul]
  have hkey : ∀ x : H3Zorn ℝ,
      (traceBilin b (g x) - linearTrace x) • U x 1 +
      (traceBilin (adjointQuad x) 1 - traceBilin (adjointQuad (g x)) (adjointQuad b)) • x +
      ((normCubic a)⁻¹ * normCubic (g x) - normCubic x) • (1 : H3Zorn ℝ) = 0 := by
    intro x
    have hidg := h3zorn_isotopy_cubic_identity (g x) b
    rw [hUgb x x, hUgxb x, hadjb] at hidg
    have hid1 : U x x - traceBilin b (g x) • U x 1 +
        traceBilin (adjointQuad (g x)) ((normCubic a)⁻¹ • a) • x =
        ((normCubic a)⁻¹ * normCubic (g x)) • (1 : H3Zorn ℝ) := by
      apply g.injective
      simp only [map_sub, map_add, map_smul]
      change g (U x x) - traceBilin b (g x) • g (U x 1) +
          traceBilin (adjointQuad (g x)) ((normCubic a)⁻¹ • a) • g x =
        ((normCubic a)⁻¹ * normCubic (g x)) • a
      rw [mul_comm, ← smul_smul]
      exact hidg
    have hid2 := h3zorn_isotopy_cubic_identity x 1
    rw [h3zorn_U_one, traceBilin_symm, traceBilin_one, adjointQuad_one] at hid2
    rw [← hadjb] at hid1
    have hsub := congrArg₂ (fun A B : H3Zorn ℝ => B - A) hid1 hid2
    calc
      (traceBilin b (g x) - linearTrace x) • U x 1 +
          (traceBilin (adjointQuad x) 1 -
            traceBilin (adjointQuad (g x)) (adjointQuad b)) • x +
          ((normCubic a)⁻¹ * normCubic (g x) - normCubic x) • (1 : H3Zorn ℝ) =
        (U x x - linearTrace x • U x 1 + traceBilin (adjointQuad x) 1 • x) -
          (U x x - traceBilin b (g x) • U x 1 +
            traceBilin (adjointQuad (g x)) (adjointQuad b) • x) -
          (normCubic x • (1 : H3Zorn ℝ) -
            ((normCubic a)⁻¹ * normCubic (g x)) • (1 : H3Zorn ℝ)) := by module
      _ = 0 := by
        rw [hsub, sub_self]
  intro z
  let d : H3Zorn ℝ := diagCartan 1 2 3
  have hUd1 : U d 1 = diagCartan 1 4 9 := by
    have h := (diagCartan_quadratic_U_peirce_laplace_mellin_and_semigroup
      (1 : ℝ) 2 3 1 1 1 (1 : H3Zorn ℝ)).2.2.1
    dsimp [d]
    rw [h]
    apply ext_h3 <;> simp [diagCartan, one_readback, ZornVectorMatrix.smul_zero] <;> norm_num
  let u0 : H3Zorn ℝ := U d 1
  let u1 : H3Zorn ℝ := T d 1 z
  let u2 : H3Zorn ℝ := U z 1
  have hUr : ∀ r : ℝ, U (d + r • z) 1 = u0 + r • u1 + r ^ 2 • u2 := by
    intro r
    rw [U_add_left, T_smul_right, U_smul_left]
  let A : ℝ := ((2 * u1.α₃ - u1.α₂ * 3 + 9 * z.α₂ - 4 * z.α₃) -
      (u1.α₃ - u1.α₁ * 3 + 9 * z.α₁ - z.α₃) +
      (u1.α₂ - u1.α₁ * 2 + 4 * z.α₁ - z.α₂)) / 2
  let B : ℝ := ((2 * u2.α₃ + z.α₂ * u1.α₃ - u2.α₂ * 3 - u1.α₂ * z.α₃) -
      (u2.α₃ + z.α₁ * u1.α₃ - u2.α₁ * 3 - u1.α₁ * z.α₃) +
      (u2.α₂ + z.α₁ * u1.α₂ - u2.α₁ * 2 - u1.α₁ * z.α₂)) / 2
  let C : ℝ := ((z.α₂ * u2.α₃ - u2.α₂ * z.α₃) -
      (z.α₁ * u2.α₃ - u2.α₁ * z.α₃) +
      (z.α₁ * u2.α₂ - u2.α₁ * z.α₂)) / 2
  obtain ⟨δ, hδpos, hδ⟩ := real_cubic_ne_zero_near_zero A B C
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
      simpa only [add_readback, smul_readback,
        show (1 : H3Zorn ℝ).α₁ = 1 from rfl,
        show (0 : H3Zorn ℝ).α₁ = 0 from rfl, mul_one] using congrArg H3Zorn.α₁ hx
    have hα2 : c₂ * (U x 1).α₂ + c₁ * x.α₂ + c₀ = 0 := by
      dsimp [c₂, c₁, c₀]
      simpa only [add_readback, smul_readback,
        show (1 : H3Zorn ℝ).α₂ = 1 from rfl,
        show (0 : H3Zorn ℝ).α₂ = 0 from rfl, mul_one] using congrArg H3Zorn.α₂ hx
    have hα3 : c₂ * (U x 1).α₃ + c₁ * x.α₃ + c₀ = 0 := by
      dsimp [c₂, c₁, c₀]
      simpa only [add_readback, smul_readback,
        show (1 : H3Zorn ℝ).α₃ = 1 from rfl,
        show (0 : H3Zorn ℝ).α₃ = 0 from rfl, mul_one] using congrArg H3Zorn.α₃ hx
    have hcancel := det3_cofactor_cancel hα1 hα2 hα3
    have hx1 : x.α₁ = 1 + r * z.α₁ := rfl
    have hx2 : x.α₂ = 2 + r * z.α₂ := rfl
    have hx3 : x.α₃ = 3 + r * z.α₃ := rfl
    have hu1 : (U x 1).α₁ = 1 + r * u1.α₁ + r ^ 2 * u2.α₁ := by
      dsimp [x]
      rw [hUr r]
      simp only [add_readback, smul_readback]
      dsimp [u0]
      rw [hUd1]
      simp [diagCartan]
    have hu2 : (U x 1).α₂ = 4 + r * u1.α₂ + r ^ 2 * u2.α₂ := by
      dsimp [x]
      rw [hUr r]
      simp only [add_readback, smul_readback]
      dsimp [u0]
      rw [hUd1]
      simp [diagCartan]
    have hu3 : (U x 1).α₃ = 9 + r * u1.α₃ + r ^ 2 * u2.α₃ := by
      dsimp [x]
      rw [hUr r]
      simp only [add_readback, smul_readback]
      dsimp [u0]
      rw [hUd1]
      simp [diagCartan]
    have hdet :
        (x.α₂ * (U x 1).α₃ - (U x 1).α₂ * x.α₃) -
          (x.α₁ * (U x 1).α₃ - (U x 1).α₁ * x.α₃) +
          (x.α₁ * (U x 1).α₂ - (U x 1).α₁ * x.α₂) =
        2 * (1 + r * A + r ^ 2 * B + r ^ 3 * C) := by
      rw [hx1, hx2, hx3, hu1, hu2, hu3]
      dsimp [A, B, C]
      ring
    rw [hdet] at hcancel
    have hnz : 2 * (1 + r * A + r ^ 2 * B + r ^ 3 * C) ≠ 0 :=
      mul_ne_zero (by norm_num) (hδ r hr)
    exact (mul_eq_zero.mp hcancel).resolve_left hnz
  have hpoly : ∀ r : ℝ, |r| ≤ 2 * δ →
      ((normCubic a)⁻¹ * normCubic (g d) - normCubic d) +
      r * ((normCubic a)⁻¹ * traceBilin (adjointQuad (g d)) (g z) -
        traceBilin (adjointQuad d) z) +
      r ^ 2 * ((normCubic a)⁻¹ * traceBilin (adjointQuad (g z)) (g d) -
        traceBilin (adjointQuad z) d) +
      r ^ 3 * ((normCubic a)⁻¹ * normCubic (g z) - normCubic z) = 0 := by
    intro r hr
    have hc := hc0_near r hr
    rw [map_add, map_smul, normCubic_line, normCubic_line] at hc
    linarith [hc]
  have hlead := extract_real_deg3_leading δ hδpos _ _ _ _ hpoly
  have heq : normCubic (g z) - normCubic a * normCubic z = 0 := by
    calc
      normCubic (g z) - normCubic a * normCubic z =
          normCubic a * ((normCubic a)⁻¹ * normCubic (g z) - normCubic z) := by
        rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hna, one_mul]
      _ = 0 := by rw [hlead, mul_zero]
  exact sub_eq_zero.mp heq

/-- **Isotopy–Similitude Equivalence on `H3Zorn ℝ`**:
`g ∈ StructureGroup ℝ (H3Zorn ℝ)` if and only if there exists a cubic-norm
multiplier `u : ℝˣ` such that `∀ x, normCubic (g x) = (u : ℝ) * normCubic x`. -/
theorem h3zorn_mem_StructureGroup_iff_similitude (g : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) :
    g ∈ StructureGroup ℝ (H3Zorn ℝ) ↔
      ∃ u : ℝˣ, ∀ x : H3Zorn ℝ, normCubic (g x) = (u : ℝ) * normCubic x := by
  constructor
  · intro hg
    obtain ⟨hna, hsim⟩ := h3zorn_isotopy_imp_similitude g hg
    exact ⟨Units.mk0 (normCubic (g 1)) hna, hsim⟩
  · rintro ⟨u, hu⟩
    exact h3zorn_similitude_imp_mem_StructureGroup g u hu

/-- Canonical multiplicative equivalence between the quadratic-isotopy
`StructureGroup ℝ (H3Zorn ℝ)` and the cubic-similitude subgroup `h3zornStructureGroup`. -/
def h3zornStructureGroupMulEquiv :
    StructureGroup ℝ (H3Zorn ℝ) ≃* h3zornStructureGroup where
  toFun g := by
    have hg := h3zorn_isotopy_imp_similitude g.1 g.2
    exact ⟨⟨g.1, Units.mk0 (normCubic (g.1 1)) hg.1⟩, hg.2⟩
  invFun h :=
    ⟨h.1.1, h3zorn_similitude_imp_mem_StructureGroup h.1.1 h.1.2 h.2⟩
  left_inv g := by
    apply Subtype.ext
    rfl
  right_inv h := by
    apply h3zornStructureGroup_toLinearEquiv_injective
    rfl
  map_mul' g₁ g₂ := by
    apply h3zornStructureGroup_toLinearEquiv_injective
    rfl

/-- The cubic-norm multiplier homomorphism `Str(H₃(𝕆_s)) →* ℝˣ`. -/
def h3zornStructureGroupMultiplier :
    StructureGroup ℝ (H3Zorn ℝ) →* ℝˣ :=
  h3zornStructureMultiplier.comp h3zornStructureGroupMulEquiv.toMonoidHom

@[simp] theorem h3zornStructureGroupMultiplier_val
    (g : StructureGroup ℝ (H3Zorn ℝ)) :
    (h3zornStructureGroupMultiplier g : ℝ) = normCubic (g.1 1) := rfl

theorem h3zornStructureGroupMultiplier_ker_iff
    (g : StructureGroup ℝ (H3Zorn ℝ)) :
    g ∈ h3zornStructureGroupMultiplier.ker ↔
      ∀ x : H3Zorn ℝ, normCubic (g.1 x) = normCubic x := by
  change (h3zornStructureGroupMulEquiv g) ∈ h3zornStructureMultiplier.ker ↔ _
  rw [h3zornStructureMultiplier_ker_carrier]
  rfl

/-- Alias exposing the reduced structure group `Str₀(H₃(𝕆_s))` alongside `Str(H₃(𝕆_s))`. -/
abbrev H3ZornReducedStructureGroup := h3zornReducedStructureGroup

/-- `h3zornReducedStructureGroup` is canonically the kernel of the multiplier
homomorphism `h3zornStructureGroupMultiplier : StructureGroup ℝ (H3Zorn ℝ) →* ℝˣ`. -/
def h3zornReducedStructureGroupMulEquivStructureKer :
    h3zornReducedStructureGroup ≃* h3zornStructureGroupMultiplier.ker where
  toFun e := by
    refine ⟨⟨e.1, h3zorn_similitude_imp_mem_StructureGroup e.1 1 (fun x => by simpa using e.2 x)⟩, ?_⟩
    rw [h3zornStructureGroupMultiplier_ker_iff]
    exact e.2
  invFun g :=
    ⟨g.1.1, (h3zornStructureGroupMultiplier_ker_iff g.1).1 g.2⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Converse inclusion `Aut(H₃(𝕆_s)) ⊆ Str₀(H₃(𝕆_s))`: every Jordan automorphism
preserves the split Albert cubic norm. -/
theorem H3ZornJordanAut.mem_reducedStructureGroup (e : H3ZornJordanAut) :
    H3ZornJordanAut.toLinearEquiv e ∈ h3zornReducedStructureGroup := by
  have hs := H3ZornJordanAut.mem_StructureGroup e
  have hsim := (h3zorn_isotopy_imp_similitude (H3ZornJordanAut.toLinearEquiv e) hs).2
  intro x
  have h1 : H3ZornJordanAut.toLinearEquiv e 1 = 1 := H3ZornJordanAut.map_one e
  simpa [h1, normCubic_one] using hsim x

/-- Full characterization `Aut(H₃(𝕆_s))` inside `Str₀(H₃(𝕆_s))` as the unit stabilizer. -/
theorem h3zornJordanAut_iff_reducedStructure_fix_one (e : H3Zorn ℝ ≃ₗ[ℝ] H3Zorn ℝ) :
    H3ZornJordanAutLaws e ↔
      e ∈ h3zornReducedStructureGroup ∧ e 1 = 1 := by
  constructor
  · intro he
    let A : H3ZornJordanAut := ⟨e, he⟩
    exact ⟨H3ZornJordanAut.mem_reducedStructureGroup A, he.1⟩
  · rintro ⟨hred, h1⟩
    exact (h3zornJordanAutOfReducedStructure ⟨e, hred⟩ h1).2

/-- Unit-fixing subgroup of `h3zornReducedStructureGroup`. -/
def h3zornReducedStructureFixOne : Subgroup h3zornReducedStructureGroup where
  carrier := {g | g.1 1 = 1}
  one_mem' := rfl
  mul_mem' := by
    intro g h hg hh
    change g.1 (h.1 1) = 1
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change g.1.symm 1 = 1
    calc
      g.1.symm 1 = g.1.symm (g.1 1) := congrArg g.1.symm hg.symm
      _ = 1 := g.1.symm_apply_apply 1

/-- Group isomorphism `Aut(H₃(𝕆_s)) ≃* {g ∈ Str₀(H₃(𝕆_s)) | g 1 = 1}`. -/
def h3zornJordanAutMulEquivReducedStructureFixOne :
    H3ZornJordanAut ≃* h3zornReducedStructureFixOne where
  toFun A :=
    ⟨⟨H3ZornJordanAut.toLinearEquiv A, H3ZornJordanAut.mem_reducedStructureGroup A⟩,
      H3ZornJordanAut.map_one A⟩
  invFun g := h3zornJordanAutOfReducedStructure g.1 g.2
  left_inv A := by
    apply H3ZornJordanAut.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

end IsotopyToSimilitudeAndEquivalences

end InfoGeometry.Algebra
