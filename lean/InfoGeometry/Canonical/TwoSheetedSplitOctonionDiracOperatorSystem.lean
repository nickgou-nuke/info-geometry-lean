/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornSpinor
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Two-Sheeted Split-Octonion Dirac Operator System (Zero-Scalar Dynamical Pole Generation)

Formalizes the purely associative endomorphism algebra `End_ℝ(ZornMatrix ℝ) ≅ M₈(ℝ)` over the
canonical split-octonion owner `InfoGeometry.Canonical.ZornMatrix ℝ` (`ZornSpinor.lean`), showing:

1. **Zero-Scalar Dynamical Pole Generation from Two Nilpotent Chiral Sheets**:
   The transverse sheet left-multiplication operators `V̂₊(v) = LOp (sheetPlus 0 v)` and
   `Ŵ₋(w) = LOp (sheetMinus 0 w)` are each strictly nilpotent (`V̂₊(v)² = 0`, `Ŵ₋(w)² = 0`), while
   their anticommutator inside `End_ℝ(ZornMatrix ℝ)` dynamically generates the pole projector sum
   `LOp zornPlus + LOp zornMinus = 1` scaled by `dot v w`, yielding operator invertibility (`IsUnit`)
   whenever `dot v w ≠ 0` without inserting any external scalar mass term on the diagonal.
2. **Two Transverse Operators Generate Asymmetric Poles + Non-Abelian Curl Terms**:
   In `ZornSpinor.lean`'s multiplication convention `(x₁ a₂ + b₁ y₂ - y₁ × y₂, y₁ b₂ + a₁ y₂ + x₁ × x₂)`
   (related by `(x, y) ↦ (-x, -y)` to the opposite cross sign convention), multiplying two pole-free
   elements `sheetPlus 0 v₁ + sheetMinus 0 w₁` and `sheetPlus 0 v₂ + sheetMinus 0 w₂` generates the
   diagonal pole projectors `zornPlus`, `zornMinus` plus the off-diagonal non-Abelian curl slots
   `-cross w₁ w₂` and `cross v₁ v₂`.
3. **Coupled Two-Sheeted Split-Octonion Dirac–Maxwell System & Operator Klein–Gordon Factorization**:
   `LOp D Psi = 0` is equivalent to the exact four coupled two-sheeted divergence and chiral-curl
   equations interlocking Sheet `+` and Sheet `-`, while `LOp (zornConj D)` factorizes the
   second-order wave operator onto `(d₀⁺ d₀⁻ - dot d₊ d₋) • (LOp zornPlus + LOp zornMinus)`.
4. **Faithful `M₈(ℝ)` Matrix Transfer**:
   Transports the orthogonal pole idempotents, dynamical anticommutator, and Klein–Gordon operator
   factorization into `Matrix (Fin 8) (Fin 8) ℝ` via `zornEndToMat8`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `exists_noncomm_end_zorn`, `exists_noncomm_mat8_zorn`, `exists_nonassoc_zorn_mul`,
  `exists_lop_non_hom`
* `pole_peirce_idempotents_in_end`
* `zero_scalar_dynamical_pole_generation`
* `two_sheeted_split_octonion_dirac_operator_system`
* `zornEndToMat8_dynamical_pole_and_klein_gordon`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* Operator invertibility `dot v w ≠ 0 → IsUnit (LOp (sheetPlus 0 v) + LOp (sheetMinus 0 w))` inside
  `zero_scalar_dynamical_pole_generation` and its `M₈(ℝ)` image.

#### BUCKET 3: OPEN CLOSURE DEBT
* Differential spacetime realizations `(d₀±, d⃗±) = (∂₀ ± …, ∇ ± …)` and unbounded functional-analytic
  Fredholm/spectral estimates lie outside this finite-dimensional algebraic/endomorphism module.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetedSplitOctonionDiracOperatorSystem

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix

/-- Canonical 3-vector carrier `Fin 3 → ℝ` matching `InfoGeometry.Canonical.ZornMatrix`. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Positive-chiral 4-vector sheet `U⁺(a, v) = { a := a, b := 0, x := v, y := 0 }`. -/
def sheetPlus (a : ℝ) (v : Vec3) : ZornMatrix ℝ :=
  { a := a, b := 0, x := v, y := 0 }

/-- Negative-chiral 4-vector sheet `U⁻(b, w) = { a := 0, b := b, x := 0, y := w }`. -/
def sheetMinus (b : ℝ) (w : Vec3) : ZornMatrix ℝ :=
  { a := 0, b := b, x := 0, y := w }

/-- Canonical split-octonion Zorn involution `z̅ = { a := z.b, b := z.a, x := -z.x, y := -z.y }`. -/
def zornConj (z : ZornMatrix ℝ) : ZornMatrix ℝ :=
  { a := z.b, b := z.a, x := -z.x, y := -z.y }

private lemma dot_add_left (x₁ x₂ y : Vec3) :
    dot (x₁ + x₂) y = dot x₁ y + dot x₂ y := by
  simp only [dot, Pi.add_apply]; ring

private lemma dot_add_right (x y₁ y₂ : Vec3) :
    dot x (y₁ + y₂) = dot x y₁ + dot x y₂ := by
  simp only [dot, Pi.add_apply]; ring

private lemma dot_smul_left (c : ℝ) (x y : Vec3) :
    dot (c • x) y = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]; ring

private lemma dot_smul_right (c : ℝ) (x y : Vec3) :
    dot x (c • y) = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]; ring

private lemma cross_add_right (x y₁ y₂ : Vec3) :
    cross x (y₁ + y₂) = cross x y₁ + cross x y₂ := by
  funext i; fin_cases i <;> (simp [cross]; ring)

private lemma cross_smul_right (c : ℝ) (x y : Vec3) :
    cross x (c • y) = c • cross x y := by
  funext i; fin_cases i <;> (simp [cross]; ring)

private lemma zorn_mul_add_right (z u₁ u₂ : ZornMatrix ℝ) :
    z * (u₁ + u₂) = z * u₁ + z * u₂ := by
  apply ZornMatrix.ext
  · simp only [mul_def, add_def, mul, dot_add_right]; ring
  · simp only [mul_def, add_def, mul, dot_add_right]; ring
  · funext i
    simp only [mul_def, add_def, mul, cross_add_right, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  · funext i
    simp only [mul_def, add_def, mul, cross_add_right, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

private lemma zorn_mul_smul_right (c : ℝ) (z u : ZornMatrix ℝ) :
    z * (c • u) = c • (z * u) := by
  apply ZornMatrix.ext
  · simp only [mul_def, smul_a, smul_y, dot_smul_right, mul]; ring
  · simp only [mul_def, smul_b, smul_x, dot_smul_right, mul]; ring
  · funext i
    simp only [mul_def, mul, smul_a, smul_b, smul_x, smul_y, cross_smul_right,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · funext i
    simp only [mul_def, mul, smul_a, smul_b, smul_x, smul_y, cross_smul_right,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Associative left-multiplication endomorphism `L_z ∈ End_ℝ(ZornMatrix ℝ) ≅ M₈(ℝ)`. -/
def LOp (z : ZornMatrix ℝ) : Module.End ℝ (ZornMatrix ℝ) where
  toFun u := z * u
  map_add' u₁ u₂ := zorn_mul_add_right z u₁ u₂
  map_smul' c u := zorn_mul_smul_right c z u

/-- Canonical `ℝ`-algebra isomorphism `End_ℝ(ZornMatrix ℝ) ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`. -/
def zornEndToMat8 : Module.End ℝ (ZornMatrix ℝ) ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  ((ZornMatrix.finCoordLinearEquiv (R := ℝ)).conjAlgEquiv ℝ).trans LinearMap.toMatrixAlgEquiv'

private def e1Plus : ZornMatrix ℝ := sheetPlus 0 ![1, 0, 0]
private def e2Plus : ZornMatrix ℝ := sheetPlus 0 ![0, 1, 0]
private def e3Plus : ZornMatrix ℝ := sheetPlus 0 ![0, 0, 1]
private def e1Minus : ZornMatrix ℝ := sheetMinus 0 ![1, 0, 0]

/-- Explicit non-commutativity witness inside `End_ℝ(ZornMatrix ℝ)`. -/
theorem exists_noncomm_end_zorn :
    ∃ A B : Module.End ℝ (ZornMatrix ℝ), A * B ≠ B * A := by
  refine ⟨LOp zornPlus, LOp e1Plus, fun h => ?_⟩
  have hApply := congrArg (fun T : Module.End ℝ (ZornMatrix ℝ) => (T (1 : ZornMatrix ℝ)).x 0) h
  norm_num [Module.End.mul_apply, LOp, zornPlus, e1Plus, sheetPlus, mul_def, mul, dot, cross] at hApply

/-- Explicit non-commutativity witness inside `Matrix (Fin 8) (Fin 8) ℝ` (OpenGauss T16). -/
theorem exists_noncomm_mat8_zorn :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A := by
  obtain ⟨A, B, hNE⟩ := exists_noncomm_end_zorn
  refine ⟨zornEndToMat8 A, zornEndToMat8 B, fun h => hNE ?_⟩
  apply zornEndToMat8.injective
  rwa [map_mul, map_mul]

/-- Explicit non-associativity witness for `ZornMatrix ℝ` multiplication (`e1⁺, e2⁺, e3⁺` or
`(e1⁺ * e2⁺) * e1⁻ ≠ e1⁺ * (e2⁺ * e1⁻)`), proving `LOp` is NOT a ring homomorphism on `ZornMatrix`. -/
theorem exists_nonassoc_zorn_mul_and_lop_non_hom :
    (∃ x y z : ZornMatrix ℝ, (x * y) * z ≠ x * (y * z)) ∧
    (∃ x y : ZornMatrix ℝ, LOp (x * y) ≠ LOp x * LOp y) := by
  have hNA : (e1Plus * e2Plus) * e1Minus ≠ e1Plus * (e2Plus * e1Minus) := by
    intro h
    have hx1 := congrArg (fun w : ZornMatrix ℝ => w.x 1) h
    norm_num [e1Plus, e2Plus, e1Minus, sheetPlus, sheetMinus, mul_def, mul, dot, cross] at hx1
  refine ⟨⟨e1Plus, e2Plus, e1Minus, hNA⟩, ⟨e1Plus, e2Plus, fun h => hNA ?_⟩⟩
  exact congrArg (fun T : Module.End ℝ (ZornMatrix ℝ) => T e1Minus) h

/-! ### Part 2: Pole Peirce Idempotents & Zero-Scalar Dynamical Pole Generation -/

/-- **Theorem 1A (Orthogonal Pole Peirce Idempotents in `End_ℝ(ZornMatrix ℝ)`)**:
`P₊ = LOp zornPlus` and `P₋ = LOp zornMinus` form a complete pair of orthogonal idempotents
(`P₊² = P₊`, `P₋² = P₋`, `P₊ P₋ = 0`, `P₋ P₊ = 0`, `P₊ + P₋ = 1`) in `End_ℝ(ZornMatrix ℝ)`. -/
theorem pole_peirce_idempotents_in_end :
    let P_p := LOp (zornPlus (R := ℝ))
    let P_m := LOp (zornMinus (R := ℝ))
    (P_p * P_p = P_p) ∧ (P_m * P_m = P_m) ∧
    (P_p * P_m = 0) ∧ (P_m * P_p = 0) ∧
    (P_p + P_m = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply LinearMap.ext; intro u; apply ZornMatrix.ext
    · simp [Module.End.mul_apply, LOp, zornPlus, zornMinus, mul_def, mul, dot, cross]
    · simp [Module.End.mul_apply, LOp, zornPlus, zornMinus, mul_def, mul, dot, cross]
    · funext i; fin_cases i <;>
        simp [Module.End.mul_apply, LOp, zornPlus, zornMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]
    · funext i; fin_cases i <;>
        simp [Module.End.mul_apply, LOp, zornPlus, zornMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]

/-- **Theorem 1B (Zero-Scalar Dynamical Pole Operator Generation from Nilpotent Sheets)**:
Let `V̂₊(v) = LOp (sheetPlus 0 v)` and `Ŵ₋(w) = LOp (sheetMinus 0 w)` have zero diagonal components:
1. Individual sheet operators are strictly nilpotent: `V̂₊(v)² = 0`, `Ŵ₋(w)² = 0`.
2. Their cross-sheet anticommutator equals `(dot v w) • (LOp zornPlus + LOp zornMinus)`.
3. Whenever `dot v w ≠ 0`, `V̂₊(v) + Ŵ₋(w)` is invertible (`IsUnit`) in `End_ℝ(ZornMatrix ℝ)`.
4. Multiplying two transverse elements generates diagonal pole projectors `zornPlus`, `zornMinus`
   and off-diagonal non-Abelian curl terms `-cross w₁ w₂` and `cross v₁ v₂`. -/
theorem zero_scalar_dynamical_pole_generation (v w v₁ w₁ v₂ w₂ : Vec3) :
    let Vp := LOp (sheetPlus 0 v)
    let Wm := LOp (sheetMinus 0 w)
    let P_tot := LOp (zornPlus (R := ℝ)) + LOp (zornMinus (R := ℝ))
    (Vp * Vp = 0 ∧ Wm * Wm = 0) ∧
    (P_tot = 1) ∧
    ((Vp + Wm) * (Vp + Wm) = Vp * Wm + Wm * Vp ∧
      Vp * Wm + Wm * Vp = dot v w • P_tot) ∧
    (dot v w ≠ 0 → IsUnit (Vp + Wm)) ∧
    ((sheetPlus 0 v₁ + sheetMinus 0 w₁) * (sheetPlus 0 v₂ + sheetMinus 0 w₂) =
      dot v₁ w₂ • zornPlus + dot v₂ w₁ • zornMinus +
      sheetPlus 0 (-cross w₁ w₂) + sheetMinus 0 (cross v₁ v₂)) := by
  dsimp only
  have hVp2 : LOp (sheetPlus 0 v) * LOp (sheetPlus 0 v) = 0 := by
    apply LinearMap.ext; intro u; apply ZornMatrix.ext
    · simp [Module.End.mul_apply, LOp, sheetPlus, mul_def, mul, dot, cross]; ring
    · simp [Module.End.mul_apply, LOp, sheetPlus, mul_def, mul, dot, cross]
    · funext i; fin_cases i <;>
        simp [Module.End.mul_apply, LOp, sheetPlus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]
    · funext i; fin_cases i <;>
        (simp [Module.End.mul_apply, LOp, sheetPlus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]; try ring)
  have hWm2 : LOp (sheetMinus 0 w) * LOp (sheetMinus 0 w) = 0 := by
    apply LinearMap.ext; intro u; apply ZornMatrix.ext
    · simp [Module.End.mul_apply, LOp, sheetMinus, mul_def, mul, dot, cross]
    · simp [Module.End.mul_apply, LOp, sheetMinus, mul_def, mul, dot, cross]; ring
    · funext i; fin_cases i <;>
        (simp [Module.End.mul_apply, LOp, sheetMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]; try ring)
    · funext i; fin_cases i <;>
        simp [Module.End.mul_apply, LOp, sheetMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]
  have hPtot : LOp (zornPlus (R := ℝ)) + LOp (zornMinus (R := ℝ)) = 1 :=
    pole_peirce_idempotents_in_end.2.2.2.2
  have hAnti : LOp (sheetPlus 0 v) * LOp (sheetMinus 0 w) +
      LOp (sheetMinus 0 w) * LOp (sheetPlus 0 v) =
      dot v w • (LOp (zornPlus (R := ℝ)) + LOp (zornMinus (R := ℝ))) := by
    rw [hPtot]
    apply LinearMap.ext; intro u; apply ZornMatrix.ext
    · simp [Module.End.mul_apply, LOp, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
        Matrix.vecHead, Matrix.vecTail]; ring
    · simp [Module.End.mul_apply, LOp, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
        Matrix.vecHead, Matrix.vecTail]; ring
    · funext i; fin_cases i <;>
        (simp [Module.End.mul_apply, LOp, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]; ring)
    · funext i; fin_cases i <;>
        (simp [Module.End.mul_apply, LOp, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]; ring)
  have hSq : (LOp (sheetPlus 0 v) + LOp (sheetMinus 0 w)) *
      (LOp (sheetPlus 0 v) + LOp (sheetMinus 0 w)) =
      LOp (sheetPlus 0 v) * LOp (sheetMinus 0 w) +
      LOp (sheetMinus 0 w) * LOp (sheetPlus 0 v) := by
    calc
      (LOp (sheetPlus 0 v) + LOp (sheetMinus 0 w)) *
          (LOp (sheetPlus 0 v) + LOp (sheetMinus 0 w))
          = LOp (sheetPlus 0 v) * LOp (sheetPlus 0 v) +
            (LOp (sheetPlus 0 v) * LOp (sheetMinus 0 w) +
              LOp (sheetMinus 0 w) * LOp (sheetPlus 0 v)) +
            LOp (sheetMinus 0 w) * LOp (sheetMinus 0 w) := by noncomm_ring
      _ = LOp (sheetPlus 0 v) * LOp (sheetMinus 0 w) +
            LOp (sheetMinus 0 w) * LOp (sheetPlus 0 v) := by rw [hVp2, hWm2, zero_add, add_zero]
  refine ⟨⟨hVp2, hWm2⟩, hPtot, ⟨hSq, hAnti⟩, ?_, ?_⟩
  · intro hNe
    set Z := LOp (sheetPlus 0 v) + LOp (sheetMinus 0 w)
    have hZ2 : Z * Z = dot v w • (1 : Module.End ℝ (ZornMatrix ℝ)) := by
      dsimp [Z]; rw [hSq, hAnti, hPtot]
    refine ⟨⟨Z, (dot v w)⁻¹ • Z, ?_, ?_⟩, rfl⟩
    · rw [mul_smul_comm, hZ2, smul_smul, inv_mul_cancel₀ hNe, one_smul]
    · rw [smul_mul_assoc, hZ2, smul_smul, inv_mul_cancel₀ hNe, one_smul]
  · apply ZornMatrix.ext
    · simp [sheetPlus, sheetMinus, zornPlus, zornMinus, mul_def, mul, dot, smul_a]
    · simp [sheetPlus, sheetMinus, zornPlus, zornMinus, mul_def, mul, dot, smul_b]; ring
    · funext i; fin_cases i <;>
        simp [sheetPlus, sheetMinus, zornPlus, zornMinus, mul_def, mul, cross]
    · funext i; fin_cases i <;>
        simp [sheetPlus, sheetMinus, zornPlus, zornMinus, mul_def, mul, cross]

/-! ### Part 3: Coupled Two-Sheeted Dirac–Maxwell System & Operator Klein–Gordon Factorization -/

/-- **Theorem 2 (Two-Sheeted Split-Octonion Dirac–Maxwell System & Klein–Gordon Factorization)**:
For `D = sheetPlus d₀P dP + sheetMinus d₀M dM` and `Psi = sheetPlus ψ₀P ψP + sheetMinus ψ₀M ψM`:
1. `LOp D Psi = 0` holds **if and only if** the 4 coupled two-sheeted equations hold simultaneously.
2. `LOp (zornConj D) * LOp D = (d₀P * d₀M - dot dP dM) • (LOp zornPlus + LOp zornMinus)` and
   `LOp D * LOp (zornConj D) = (d₀P * d₀M - dot dP dM) • (LOp zornPlus + LOp zornMinus)`. -/
theorem two_sheeted_split_octonion_dirac_operator_system
    (d₀P d₀M ψ₀P ψ₀M : ℝ) (dP dM ψP ψM : Vec3) :
    let D := sheetPlus d₀P dP + sheetMinus d₀M dM
    let Psi := sheetPlus ψ₀P ψP + sheetMinus ψ₀M ψM
    let P_tot := LOp (zornPlus (R := ℝ)) + LOp (zornMinus (R := ℝ))
    (LOp D Psi = 0 ↔
      (d₀P * ψ₀P + dot dP ψM = 0) ∧
      (d₀M * ψ₀M + dot dM ψP = 0) ∧
      (∀ i : Fin 3, d₀P * ψP i + ψ₀M * dP i - cross dM ψM i = 0) ∧
      (∀ i : Fin 3, d₀M * ψM i + ψ₀P * dM i + cross dP ψP i = 0)) ∧
    (LOp (zornConj D) * LOp D = (d₀P * d₀M - dot dP dM) • P_tot ∧
     LOp D * LOp (zornConj D) = (d₀P * d₀M - dot dP dM) • P_tot) := by
  dsimp only
  have hPtot : LOp (zornPlus (R := ℝ)) + LOp (zornMinus (R := ℝ)) = 1 :=
    pole_peirce_idempotents_in_end.2.2.2.2
  constructor
  · constructor
    · intro h0
      have ha := congrArg ZornMatrix.a h0
      have hb := congrArg ZornMatrix.b h0
      have hx := congrArg ZornMatrix.x h0
      have hy := congrArg ZornMatrix.y h0
      simp only [LOp, LinearMap.coe_mk, AddHom.coe_mk, sheetPlus, sheetMinus, add_def,
        mul_def, mul, zero_a, zero_b, zero_x, zero_y, zero_add, add_zero] at ha hb hx hy
      refine ⟨ha, hb, fun i => ?_, fun i => ?_⟩
      · simpa only [Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          congrFun hx i
      · simpa only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          congrFun hy i
    · rintro ⟨ha, hb, hx, hy⟩
      apply ZornMatrix.ext
      · simp only [LOp, LinearMap.coe_mk, AddHom.coe_mk, sheetPlus, sheetMinus, add_def,
          mul_def, mul, zero_a, zero_add, add_zero]
        exact ha
      · simp only [LOp, LinearMap.coe_mk, AddHom.coe_mk, sheetPlus, sheetMinus, add_def,
          mul_def, mul, zero_b, zero_add, add_zero]
        exact hb
      · funext i
        simpa only [LOp, LinearMap.coe_mk, AddHom.coe_mk, sheetPlus, sheetMinus, add_def,
          mul_def, mul, zero_x, zero_add, add_zero, Pi.zero_apply, Pi.sub_apply,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hx i
      · funext i
        simpa only [LOp, LinearMap.coe_mk, AddHom.coe_mk, sheetPlus, sheetMinus, add_def,
          mul_def, mul, zero_y, zero_add, add_zero, Pi.zero_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul] using hy i
  · constructor
    · rw [hPtot]
      apply LinearMap.ext; intro u; apply ZornMatrix.ext
      · simp [Module.End.mul_apply, LOp, zornConj, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]; ring
      · simp [Module.End.mul_apply, LOp, zornConj, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]; ring
      · funext i; fin_cases i <;>
          (simp [Module.End.mul_apply, LOp, zornConj, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
            Matrix.vecHead, Matrix.vecTail]; ring)
      · funext i; fin_cases i <;>
          (simp [Module.End.mul_apply, LOp, zornConj, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
            Matrix.vecHead, Matrix.vecTail]; ring)
    · rw [hPtot]
      apply LinearMap.ext; intro u; apply ZornMatrix.ext
      · simp [Module.End.mul_apply, LOp, zornConj, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]; ring
      · simp [Module.End.mul_apply, LOp, zornConj, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail]; ring
      · funext i; fin_cases i <;>
          (simp [Module.End.mul_apply, LOp, zornConj, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
            Matrix.vecHead, Matrix.vecTail]; ring)
      · funext i; fin_cases i <;>
          (simp [Module.End.mul_apply, LOp, zornConj, sheetPlus, sheetMinus, mul_def, mul, dot, cross,
            Matrix.vecHead, Matrix.vecTail]; ring)

/-! ### Part 4: Faithful `M₈(ℝ)` Matrix Carrier Transfer via `zornEndToMat8` -/

/-- **Theorem 3 (Faithful `M₈(ℝ)` Matrix Representation of Dynamical Poles & Klein–Gordon)**:
Transfers the orthogonal pole projectors, dynamical cross-sheet anticommutator, `IsUnit` gap,
and operator Klein–Gordon factorization into `Matrix (Fin 8) (Fin 8) ℝ` via `zornEndToMat8`. -/
theorem zornEndToMat8_dynamical_pole_and_klein_gordon
    (v w : Vec3) (d₀P d₀M : ℝ) (dP dM : Vec3) :
    let VpM := zornEndToMat8 (LOp (sheetPlus 0 v))
    let WmM := zornEndToMat8 (LOp (sheetMinus 0 w))
    let PpM := zornEndToMat8 (LOp (zornPlus (R := ℝ)))
    let PmM := zornEndToMat8 (LOp (zornMinus (R := ℝ)))
    let DM := zornEndToMat8 (LOp (sheetPlus d₀P dP + sheetMinus d₀M dM))
    let DcM := zornEndToMat8 (LOp (zornConj (sheetPlus d₀P dP + sheetMinus d₀M dM)))
    (PpM * PpM = PpM ∧ PmM * PmM = PmM ∧ PpM * PmM = 0 ∧ PmM * PpM = 0 ∧ PpM + PmM = 1) ∧
    (VpM * VpM = 0 ∧ WmM * WmM = 0) ∧
    ((VpM + WmM) * (VpM + WmM) = dot v w • (PpM + PmM)) ∧
    (dot v w ≠ 0 → IsUnit (VpM + WmM)) ∧
    (DcM * DM = (d₀P * d₀M - dot dP dM) • (PpM + PmM) ∧
     DM * DcM = (d₀P * d₀M - dot dP dM) • (PpM + PmM)) := by
  have hP := pole_peirce_idempotents_in_end
  have hD := zero_scalar_dynamical_pole_generation v w v w v w
  have hKG := (two_sheeted_split_octonion_dirac_operator_system d₀P d₀M 0 0 dP dM 0 0).2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩
  · rw [← map_mul, hP.1]
  · rw [← map_mul, hP.2.1]
  · rw [← map_mul, hP.2.2.1, map_zero]
  · rw [← map_mul, hP.2.2.2.1, map_zero]
  · rw [← map_add, hP.2.2.2.2, map_one]
  · rw [← map_mul, hD.1.1, map_zero]
  · rw [← map_mul, hD.1.2, map_zero]
  · rw [← map_add, ← map_mul, hD.2.2.1.1, hD.2.2.1.2, map_smul, map_add]
  · intro hNe
    rw [← map_add]
    exact (hD.2.2.2.1 hNe).map zornEndToMat8.toMonoidHom
  · rw [← map_mul, hKG.1, map_smul, map_add]
  · rw [← map_mul, hKG.2, map_smul, map_add]

end InfoGeometry.Canonical.TwoSheetedSplitOctonionDiracOperatorSystem
