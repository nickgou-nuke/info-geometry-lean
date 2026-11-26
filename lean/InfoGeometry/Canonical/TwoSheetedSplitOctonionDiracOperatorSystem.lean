/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.ZornMultiplicationOperators
import InfoGeometry.Canonical.ZornCl44Triality
import InfoGeometry.Canonical.KleinianZornCl44Bridge
import InfoGeometry.Physics.NCG.NoncommutativeChiralZornAlgebra
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Canonical.ThreeColorOperatorSuperBracketClosure
import InfoGeometry.Canonical.ChiralZornCasimirChannels
import InfoGeometry.Canonical.OperatorChiralDeterminantDefect
import InfoGeometry.Core.OperatorCliffordDouble
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
* `LOp_eq_leftMulLinear`, `zornCrossParity_mul`, `sheetPlus_one_not_nilpotent_in_end_zorn`,
  `cl44_sheet_diracGamma_noncomm`, `cl44_chiral_4vector_sheet_nilpotency_and_lorentz_anticommutator`
* `ncZorn_operator_ring_zero_scalar_and_commutator_defect`,
  `zornRealEquivNCReal_mul`, `zornReal_commutator_collapse`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* Operator invertibility `dot v w ≠ 0 → IsUnit (LOp (sheetPlus 0 v) + LOp (sheetMinus 0 w))` inside
  `zero_scalar_dynamical_pole_generation` and its `M₈(ℝ)` image.
* Gapped-vs-null Kleinian dichotomy (`two_sheeted_dirac_gap_vs_null_dichotomy`,
  `transverse_zero_scalar_gap_vs_null_dichotomy`) bridging to `KleinianZornCl44Bridge`.

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

/-! ### Part 5: Preexisting Zorn Multiplication, Cross-Parity, Kleinian Dichotomy, & `Cl(4,4)` `M₁₆(ℝ)` Bridge -/

section PreexistingZornCl44Bridge

/-- Definitional identification of `LOp z` with `ZornMatrix.leftMulLinear z` (`ZornMultiplicationOperators`). -/
theorem LOp_eq_leftMulLinear (z : ZornMatrix ℝ) :
    LOp z = ZornMatrix.leftMulLinear z :=
  LinearMap.ext fun _ => rfl

private lemma LOp_add (z w : ZornMatrix ℝ) : LOp (z + w) = LOp z + LOp w := by
  apply LinearMap.ext
  intro u
  apply ZornMatrix.ext
  · simp [LOp, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]; ring
  · simp [LOp, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]; ring
  · funext i
    fin_cases i <;>
      simp [LOp, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross,
        Matrix.vecHead, Matrix.vecTail] <;> ring
  · funext i
    fin_cases i <;>
      simp [LOp, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross,
        Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Sign-reflection parity involution relating `ZornMatrix.mul` (`- y₁ × y₂`, `+ x₁ × x₂`) to the
opposite cross-product parity convention (`+ w₁ × w₂`, `- v₁ × v₂`). -/
def zornCrossParity (z : ZornMatrix ℝ) : ZornMatrix ℝ :=
  { a := z.a, b := z.b, x := -z.x, y := -z.y }

/-- Alternative cross-sign Zorn multiplication (`+ y₁ × y₂`, `- x₁ × x₂`) matching `w₁ × w₂` and
`- v₁ × v₂` under transverse sheet multiplication. -/
def crossFlippedMul (z₁ z₂ : ZornMatrix ℝ) : ZornMatrix ℝ :=
  { a := z₁.a * z₂.a + ZornMatrix.dot z₁.x z₂.y
    b := z₁.b * z₂.b + ZornMatrix.dot z₁.y z₂.x
    x := z₁.a • z₂.x + z₂.b • z₁.x + ZornMatrix.cross z₁.y z₂.y
    y := z₁.b • z₂.y + z₂.a • z₁.y - ZornMatrix.cross z₁.x z₂.x }

/-- `zornCrossParity` intertwines `ZornMatrix.mul` with `crossFlippedMul`. -/
theorem zornCrossParity_mul (z₁ z₂ : ZornMatrix ℝ) :
    zornCrossParity (z₁ * z₂) = crossFlippedMul (zornCrossParity z₁) (zornCrossParity z₂) := by
  apply ZornMatrix.ext
  · simp [zornCrossParity, crossFlippedMul, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]
  · simp [zornCrossParity, crossFlippedMul, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]
  · funext i
    fin_cases i <;>
      simp [zornCrossParity, crossFlippedMul, ZornMatrix.mul_def, ZornMatrix.mul,
        ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornCrossParity, crossFlippedMul, ZornMatrix.mul_def, ZornMatrix.mul,
        ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Inside `End_ℝ(ZornMatrix ℝ)`, adding a nonzero diagonal pole component `x₀ = 1` breaks
single-sheet nilpotency (`(LOp (sheetPlus 1 0))² ≠ 0`); full 4-vector single-sheet nilpotency
holds after lifting to `Cl(4,4)` (`ZornCl44Triality.diracGamma`). -/
theorem sheetPlus_one_not_nilpotent_in_end_zorn :
    LOp (sheetPlus 1 0) * LOp (sheetPlus 1 0) ≠ 0 := by
  intro hEq
  have hApp := congrArg (fun T => (T (zornPlus (R := ℝ))).a) hEq
  simp only [Module.End.mul_apply, LOp, LinearMap.coe_mk, AddHom.coe_mk, ZornMatrix.mul_def,
    ZornMatrix.mul, sheetPlus, zornPlus, ZornMatrix.dot, LinearMap.zero_apply,
    ZornMatrix.zero_a] at hApp
  norm_num at hApp

/-- Explicit T16 non-commutativity witness inside `End_ℝ(DiracSpinor16 ℝ) ≅ M₁₆(ℝ)`. -/
theorem cl44_sheet_diracGamma_noncomm :
    ZornClifford.diracGamma (sheetPlus 0 ![1, 0, 0]) *
        ZornClifford.diracGamma (sheetMinus 0 ![1, 0, 0]) ≠
      ZornClifford.diracGamma (sheetMinus 0 ![1, 0, 0]) *
        ZornClifford.diracGamma (sheetPlus 0 ![1, 0, 0]) := by
  intro hEq
  have hApp := congrArg
    (fun T => (T ((zornPlus (R := ℝ), 0) : ZornClifford.DiracSpinor16 (R := ℝ))).1.a) hEq
  simp only [Module.End.mul_apply, ZornCl44Triality.diracGamma_apply, ZornClifford.zornConj,
    sheetPlus, sheetMinus, zornPlus] at hApp
  norm_num [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross] at hApp

/-- **Theorem 4 (Gapped Mass-Invertibility vs Null 4D Chiral Kernel Dichotomy in `M₈(ℝ)`)**:
Bridges `D = sheetPlus d₀P dP + sheetMinus d₀M dM` to `KleinianZornCl44Bridge`:
1. Explicit `M₈(ℝ)` matrix intertwining via `octSToZorn` and `leftMulMat (zornToOctS D)`.
2. Gapped sector (`d₀P * d₀M - dP · dM ≠ 0`): `IsUnit (LOp D) ∧ ker (LOp D) = ⊥`.
3. Null chiral sector (`D ≠ 0 ∧ d₀P * d₀M - dP · dM = 0`):
   `range (LOp (zornConj D)) = ker (LOp D)` and `finrank ℝ (ker (LOp D)) = 4`. -/
theorem two_sheeted_dirac_gap_vs_null_dichotomy
    (d₀P d₀M : ℝ) (dP dM : Vec3) :
    let D := sheetPlus d₀P dP + sheetMinus d₀M dM
    (∀ ψ : ZornMatrix ℝ,
      KleinianZornCl44Bridge.octSToZorn
        ((KleinianWittBornNullIncidence.leftMulMat (KleinianZornCl44Bridge.zornToOctS D)).mulVec
          (KleinianZornCl44Bridge.zornToOctS ψ)) = LOp D ψ) ∧
    (d₀P * d₀M - dot dP dM ≠ 0 →
      IsUnit (LOp D) ∧ LinearMap.ker (LOp D) = ⊥) ∧
    (D ≠ 0 ∧ d₀P * d₀M - dot dP dM = 0 →
      LinearMap.range (LOp (zornConj D)) = LinearMap.ker (LOp D) ∧
      Module.finrank ℝ (LinearMap.ker (LOp D)) = 4) := by
  dsimp only
  set D : ZornMatrix ℝ := sheetPlus d₀P dP + sheetMinus d₀M dM
  have hPtot : LOp (zornPlus (R := ℝ)) + LOp (zornMinus (R := ℝ)) = 1 :=
    pole_peirce_idempotents_in_end.2.2.2.2
  have hKG := (two_sheeted_split_octonion_dirac_operator_system d₀P d₀M 0 0 dP dM 0 0).2
  have hConjL : LOp (zornConj D) * LOp D =
      (d₀P * d₀M - dot dP dM) • (1 : Module.End ℝ (ZornMatrix ℝ)) := by
    rw [← hPtot]; exact hKG.1
  have hLConj : LOp D * LOp (zornConj D) =
      (d₀P * d₀M - dot dP dM) • (1 : Module.End ℝ (ZornMatrix ℝ)) := by
    rw [← hPtot]; exact hKG.2
  have hNormEq : ZornClifford.zornNormFun D = d₀P * d₀M - dot dP dM := by
    change D.a * D.b - dot D.x D.y = d₀P * d₀M - dot dP dM
    simp [D, sheetPlus, sheetMinus]
  refine ⟨?_, ?_, ?_⟩
  · intro ψ
    have hInt := KleinianZornCl44Bridge.leftMulLinear_intertwine
      (KleinianZornCl44Bridge.zornToOctS D) (KleinianZornCl44Bridge.zornToOctS ψ)
    rw [KleinianZornCl44Bridge.octSToZorn_zornToOctS,
      KleinianZornCl44Bridge.octSToZorn_zornToOctS, ← LOp_eq_leftMulLinear] at hInt
    exact hInt
  · intro hNe
    refine ⟨?_, ?_⟩
    · refine ⟨⟨LOp D, (d₀P * d₀M - dot dP dM)⁻¹ • LOp (zornConj D), ?_, ?_⟩, rfl⟩
      · rw [mul_smul_comm, hLConj, smul_smul, inv_mul_cancel₀ hNe, one_smul]
      · rw [smul_mul_assoc, hConjL, smul_smul, inv_mul_cancel₀ hNe, one_smul]
    · rw [LinearMap.ker_eq_bot']
      intro ψ hψ
      have hψ' : LOp D ψ = 0 := hψ
      have h0 : ((d₀P * d₀M - dot dP dM) • (1 : Module.End ℝ (ZornMatrix ℝ))) ψ = 0 := by
        rw [← hConjL, Module.End.mul_apply, hψ', map_zero]
      rw [LinearMap.smul_apply, Module.End.one_apply, smul_eq_zero] at h0
      exact h0.resolve_left hNe
  · rintro ⟨hDNe, hNull⟩
    have hNorm0 : ZornClifford.zornNormFun D = 0 := by rw [hNormEq]; exact hNull
    have hRng := KleinianZornCl44Bridge.zorn_null_range_eq_ker D hDNe hNorm0
    have hFin := KleinianZornCl44Bridge.zorn_null_ker_finrank_four D hDNe hNorm0
    rw [← LOp_eq_leftMulLinear, ← LOp_eq_leftMulLinear] at hRng
    rw [← LOp_eq_leftMulLinear] at hFin
    exact ⟨hRng, hFin⟩

private lemma scalar_zero_sub_dot (d : ℝ) : (0 : ℝ) * 0 - d = -d := by
  ring

/-- **Corollary (Zero-Scalar Transverse Dichotomy)**: specializes `two_sheeted_dirac_gap_vs_null_dichotomy`
to `d₀P = 0, d₀M = 0` for `Vp = LOp (sheetPlus 0 v)` and `Wm = LOp (sheetMinus 0 w)`. -/
theorem transverse_zero_scalar_gap_vs_null_dichotomy (v w : Vec3) :
    let Vp := LOp (sheetPlus 0 v)
    let Wm := LOp (sheetMinus 0 w)
    (dot v w ≠ 0 → IsUnit (Vp + Wm) ∧ LinearMap.ker (Vp + Wm) = ⊥) ∧
    ((v ≠ 0 ∨ w ≠ 0) ∧ dot v w = 0 →
      Module.finrank ℝ (LinearMap.ker (Vp + Wm)) = 4) := by
  dsimp only
  have hMain := two_sheeted_dirac_gap_vs_null_dichotomy 0 0 v w
  have hLin : LOp (sheetPlus 0 v + sheetMinus 0 w) =
      LOp (sheetPlus 0 v) + LOp (sheetMinus 0 w) :=
    LOp_add (sheetPlus 0 v) (sheetMinus 0 w)
  have hNorm := scalar_zero_sub_dot (dot v w)
  refine ⟨?_, ?_⟩
  · intro hNe
    have hGap := hMain.2.1 (by rw [hNorm]; exact neg_ne_zero.mpr hNe)
    rwa [← hLin]
  · rintro ⟨hVec, hDot⟩
    have hDNe : sheetPlus 0 v + sheetMinus 0 w ≠ 0 := by
      intro h0
      have hx : v = 0 := by
        simpa [sheetPlus, sheetMinus, ZornMatrix.add_x, ZornMatrix.zero_x] using
          congrArg ZornMatrix.x h0
      have hy : w = 0 := by
        simpa [sheetPlus, sheetMinus, ZornMatrix.add_y, ZornMatrix.zero_y] using
          congrArg ZornMatrix.y h0
      rcases hVec with hv | hw
      · exact hv hx
      · exact hw hy
    have hNull := (hMain.2.2 ⟨hDNe, by rw [hNorm, hDot, neg_zero]⟩).2
    rwa [← hLin]

/-- **Theorem 5 (Full 4-Vector Sheet Nilpotency & Cross-Sheet Lorentz Anticommutator in `Cl(4,4)`)**:
For arbitrary 4-vectors `(x₀, xv)` and `(p₀, pv)` lifted to `Xp = sheetPlus x₀ xv` and
`Pm = sheetMinus p₀ pv` and represented on `DiracSpinor16 ℝ` via `ZornClifford.diracGamma`:
1. Every single sheet `diracGamma Xp` and `diracGamma Pm` is strictly square-zero nilpotent
   for ALL `(x₀, xv)` and `(p₀, pv)` (even with `x₀, p₀ ≠ 0`, unlike `M₈(ℝ)`).
2. `{diracGamma Xp, diracGamma Pm} = (x₀ * p₀ - dot xv pv) • 1`.
3. `(diracGamma Xp + diracGamma Pm)² = (x₀ * p₀ - dot xv pv) • 1`.
4. Whenever `x₀ * p₀ - dot xv pv ≠ 0`, `diracGamma Xp + diracGamma Pm` is a unit with trivial kernel. -/
theorem cl44_chiral_4vector_sheet_nilpotency_and_lorentz_anticommutator
    (x₀ p₀ : ℝ) (xv pv : Vec3) :
    let Xp := sheetPlus x₀ xv
    let Pm := sheetMinus p₀ pv
    (ZornClifford.diracGamma Xp * ZornClifford.diracGamma Xp = 0 ∧
      ZornClifford.diracGamma Pm * ZornClifford.diracGamma Pm = 0) ∧
    (ZornClifford.diracGamma Xp * ZornClifford.diracGamma Pm +
        ZornClifford.diracGamma Pm * ZornClifford.diracGamma Xp =
      (x₀ * p₀ - dot xv pv) •
        (1 : Module.End ℝ (ZornClifford.DiracSpinor16 (R := ℝ)))) ∧
    ((ZornClifford.diracGamma Xp + ZornClifford.diracGamma Pm) *
        (ZornClifford.diracGamma Xp + ZornClifford.diracGamma Pm) =
      (x₀ * p₀ - dot xv pv) •
        (1 : Module.End ℝ (ZornClifford.DiracSpinor16 (R := ℝ)))) ∧
    (x₀ * p₀ - dot xv pv ≠ 0 →
      IsUnit (ZornClifford.diracGamma Xp + ZornClifford.diracGamma Pm) ∧
        LinearMap.ker (ZornClifford.diracGamma Xp + ZornClifford.diracGamma Pm) = ⊥) := by
  dsimp only
  have hXpSq : ZornClifford.diracGamma (sheetPlus x₀ xv) *
      ZornClifford.diracGamma (sheetPlus x₀ xv) = 0 := by
    rw [ZornCl44Triality.diracGamma_square]
    have hNorm : (ZornClifford.zornNorm (R := ℝ)) (sheetPlus x₀ xv) = 0 := by
      change x₀ * 0 - dot xv 0 = 0
      simp [dot]
    rw [hNorm, zero_smul]
  have hPmSq : ZornClifford.diracGamma (sheetMinus p₀ pv) *
      ZornClifford.diracGamma (sheetMinus p₀ pv) = 0 := by
    rw [ZornCl44Triality.diracGamma_square]
    have hNorm : (ZornClifford.zornNorm (R := ℝ)) (sheetMinus p₀ pv) = 0 := by
      change 0 * p₀ - dot 0 pv = 0
      simp [dot]
    rw [hNorm, zero_smul]
  have hAnti :
      ZornClifford.diracGamma (sheetPlus x₀ xv) *
          ZornClifford.diracGamma (sheetMinus p₀ pv) +
        ZornClifford.diracGamma (sheetMinus p₀ pv) *
          ZornClifford.diracGamma (sheetPlus x₀ xv) =
      (x₀ * p₀ - dot xv pv) •
        (1 : Module.End ℝ (ZornClifford.DiracSpinor16 (R := ℝ))) := by
    rw [ZornCl44Triality.diracGamma_anticommutator, ZornCl44Triality.zornBilin_apply]
    have hScalar :
        2 * ((1 / 2 : ℝ) * ((sheetPlus x₀ xv).a * (sheetMinus p₀ pv).b +
          (sheetMinus p₀ pv).a * (sheetPlus x₀ xv).b -
          dot (sheetPlus x₀ xv).x (sheetMinus p₀ pv).y -
          dot (sheetMinus p₀ pv).x (sheetPlus x₀ xv).y)) =
        x₀ * p₀ - dot xv pv := by
      simp [sheetPlus, sheetMinus, dot]
    rw [hScalar]
  have hSq :
      (ZornClifford.diracGamma (sheetPlus x₀ xv) +
          ZornClifford.diracGamma (sheetMinus p₀ pv)) *
        (ZornClifford.diracGamma (sheetPlus x₀ xv) +
          ZornClifford.diracGamma (sheetMinus p₀ pv)) =
      (x₀ * p₀ - dot xv pv) •
        (1 : Module.End ℝ (ZornClifford.DiracSpinor16 (R := ℝ))) := by
    calc
      (ZornClifford.diracGamma (sheetPlus x₀ xv) +
          ZornClifford.diracGamma (sheetMinus p₀ pv)) *
          (ZornClifford.diracGamma (sheetPlus x₀ xv) +
            ZornClifford.diracGamma (sheetMinus p₀ pv))
          = ZornClifford.diracGamma (sheetPlus x₀ xv) *
              ZornClifford.diracGamma (sheetPlus x₀ xv) +
            (ZornClifford.diracGamma (sheetPlus x₀ xv) *
                ZornClifford.diracGamma (sheetMinus p₀ pv) +
              ZornClifford.diracGamma (sheetMinus p₀ pv) *
                ZornClifford.diracGamma (sheetPlus x₀ xv)) +
            ZornClifford.diracGamma (sheetMinus p₀ pv) *
              ZornClifford.diracGamma (sheetMinus p₀ pv) := by noncomm_ring
      _ = (x₀ * p₀ - dot xv pv) •
            (1 : Module.End ℝ (ZornClifford.DiracSpinor16 (R := ℝ))) := by
            rw [hXpSq, hPmSq, hAnti, zero_add, add_zero]
  refine ⟨⟨hXpSq, hPmSq⟩, hAnti, hSq, ?_⟩
  intro hNe
  set G := ZornClifford.diracGamma (sheetPlus x₀ xv) +
    ZornClifford.diracGamma (sheetMinus p₀ pv)
  have hG2 : G * G =
      (x₀ * p₀ - dot xv pv) •
        (1 : Module.End ℝ (ZornClifford.DiracSpinor16 (R := ℝ))) := hSq
  refine ⟨?_, ?_⟩
  · refine ⟨⟨G, (x₀ * p₀ - dot xv pv)⁻¹ • G, ?_, ?_⟩, rfl⟩
    · rw [mul_smul_comm, hG2, smul_smul, inv_mul_cancel₀ hNe, one_smul]
    · rw [smul_mul_assoc, hG2, smul_smul, inv_mul_cancel₀ hNe, one_smul]
  · rw [LinearMap.ker_eq_bot']
    intro s hs
    have h0 : ((x₀ * p₀ - dot xv pv) •
        (1 : Module.End ℝ (ZornClifford.DiracSpinor16 (R := ℝ)))) s = 0 := by
      rw [← hG2, Module.End.mul_apply, hs, map_zero]
    rw [LinearMap.smul_apply, Module.End.one_apply, smul_eq_zero] at h0
    exact h0.resolve_left hNe

end PreexistingZornCl44Bridge

/-! ### Part 6: Preexisting Noncommutative Operator-Ring (`[Ring A]`, `[Ring R]`) Zorn & Clifford-Double Bridge -/

section NoncommOperatorRingBridge

/-- **Theorem 6A (Arbitrary Noncommutative Operator-Ring Zorn & Clifford-Double Laws)**:
Over ANY noncommutative coefficient ring `[Ring A]` and ANY `[Ring R] [AddCommGroup M] [Module R M]`:
1. Transverse zero-scalar product in `NCZornElement A` produces the two ordered quadratic
   diagonal channels `u · v` and `v · u` alongside off-diagonal self-cross commutators
   `-v × v` and `u × u` (`operatorZornMul_chiralOperatorZorn`), vanishing iff components pairwise commute.
2. Mixed odd superbracket recovers `nPlus (u · v) + nMinus (v · u)`, while same-chirality
   superbrackets and commutators retain operator cross-commutator defects.
3. Noncommutative `2 × 2` chiral block multiplication with adjugate retains diagonal orderings
   and off-diagonal commutators `OperatorChiralDeterminantDefect.chiralBlock_mul_adjugate`.
4. `OperatorCliffordDouble.diracPlus A_op B_op ^ 2 = lift (A_op ^ 2 + B_op ^ 2) ↔ Commute A_op B_op`. -/
theorem ncZorn_operator_ring_zero_scalar_and_commutator_defect
    {A R M : Type*} [Ring A] [Ring R] [AddCommGroup M] [Module R M]
    (u v : InfoGeometry.Canonical.OperatorVector A)
    (p m r l : A) (A_op B_op : Module.End R M) :
    (InfoGeometry.Canonical.operatorZornMul
        (InfoGeometry.Canonical.chiralOperatorZorn u v)
        (InfoGeometry.Canonical.chiralOperatorZorn u v) =
      InfoGeometry.Canonical.operatorZornCoordinates
        (InfoGeometry.Canonical.operatorDot u v)
        (InfoGeometry.Canonical.operatorDot v u)
        (-InfoGeometry.Canonical.operatorCross v v)
        (InfoGeometry.Canonical.operatorCross u u)) ∧
    (InfoGeometry.Canonical.operatorCross u u = 0 ↔
      u 1 * u 2 = u 2 * u 1 ∧ u 2 * u 0 = u 0 * u 2 ∧ u 0 * u 1 = u 1 * u 0) ∧
    (InfoGeometry.Canonical.oddOddSuperBracket
        (InfoGeometry.Canonical.sigmaPlus u) (InfoGeometry.Canonical.sigmaMinus v) =
      InfoGeometry.Canonical.operatorAdd
        (InfoGeometry.Canonical.nPlus (InfoGeometry.Canonical.operatorDot u v))
        (InfoGeometry.Canonical.nMinus (InfoGeometry.Canonical.operatorDot v u))) ∧
    (InfoGeometry.Canonical.oddOddSuperBracket
        (InfoGeometry.Canonical.sigmaPlus u) (InfoGeometry.Canonical.sigmaPlus u) =
      InfoGeometry.Canonical.sigmaMinus
        (InfoGeometry.Canonical.operatorCross u u + InfoGeometry.Canonical.operatorCross u u)) ∧
    (InfoGeometry.Canonical.operatorCommutator
        (InfoGeometry.Canonical.sigmaPlus u) (InfoGeometry.Canonical.sigmaPlus v) =
      InfoGeometry.Canonical.sigmaMinus
        (InfoGeometry.Canonical.operatorCross u v - InfoGeometry.Canonical.operatorCross v u)) ∧
    (InfoGeometry.Canonical.OperatorChiralDeterminantDefect.chiralBlock p m r l *
        InfoGeometry.Canonical.OperatorChiralDeterminantDefect.chiralAdjugate p m r l =
      !![InfoGeometry.Canonical.OperatorChiralDeterminantDefect.leftQuadraticReadout p m r l,
         InfoGeometry.Canonical.OperatorChiralDeterminantDefect.operatorCommutator r p;
         InfoGeometry.Canonical.OperatorChiralDeterminantDefect.operatorCommutator l m,
         InfoGeometry.Canonical.OperatorChiralDeterminantDefect.rightQuadraticReadout p m r l]) ∧
    (InfoGeometry.Canonical.OperatorChiralDeterminantDefect.leftQuadraticReadout p m r l -
        InfoGeometry.Canonical.OperatorChiralDeterminantDefect.rightQuadraticReadout p m r l =
      InfoGeometry.Canonical.OperatorChiralDeterminantDefect.operatorCommutator p m -
        InfoGeometry.Canonical.OperatorChiralDeterminantDefect.operatorCommutator r l) ∧
    (InfoGeometry.Core.OperatorCliffordDouble.diracPlus A_op B_op ^ 2 =
        InfoGeometry.Core.OperatorCliffordDouble.lift (A_op ^ 2 + B_op ^ 2) ↔
      Commute A_op B_op) :=
  ⟨InfoGeometry.Canonical.operatorZornMul_chiralOperatorZorn u v,
   InfoGeometry.Canonical.operatorCross_self_eq_zero_iff u,
   InfoGeometry.Canonical.sigmaPlus_superBracket_sigmaMinus u v,
   InfoGeometry.Canonical.sigmaPlus_superBracket_self u,
   InfoGeometry.Canonical.same_chiral_plus_commutator_cross_channel u v,
   InfoGeometry.Canonical.OperatorChiralDeterminantDefect.chiralBlock_mul_adjugate p m r l,
   InfoGeometry.Canonical.OperatorChiralDeterminantDefect.left_sub_right_eq_commutator_defect p m r l,
   InfoGeometry.Core.OperatorCliffordDouble.diracPlus_sq_eq_lift_iff A_op B_op⟩

/-- Explicit coordinate equivalence between `ZornMatrix ℝ` and the `A = ℝ` specialization
of the noncommutative operator carrier `InfoGeometry.Physics.NCG.NCZornElement ℝ`. -/
def zornRealEquivNCReal : ZornMatrix ℝ ≃ InfoGeometry.Physics.NCG.NCZornElement ℝ where
  toFun z := ⟨z.a, z.b, z.x, z.y⟩
  invFun w := ⟨w.n_plus, w.n_minus, w.sigma_plus, w.sigma_minus⟩
  left_inv z := by cases z; rfl
  right_inv w := by cases w; rfl

/-- `zornRealEquivNCReal` identifies `ZornMatrix ℝ` multiplication with `NCZornElement.mul` at `A = ℝ`. -/
theorem zornRealEquivNCReal_mul (z₁ z₂ : ZornMatrix ℝ) :
    zornRealEquivNCReal (z₁ * z₂) =
      InfoGeometry.Physics.NCG.NCZornElement.mul
        (zornRealEquivNCReal z₁) (zornRealEquivNCReal z₂) := by
  have hExt : ∀ {X Y : InfoGeometry.Physics.NCG.NCZornElement ℝ},
      X.n_plus = Y.n_plus → X.n_minus = Y.n_minus →
      X.sigma_plus = Y.sigma_plus → X.sigma_minus = Y.sigma_minus → X = Y := by
    intro X Y h1 h2 h3 h4
    cases X; cases Y; simp_all
  apply hExt
  · rfl
  · rfl
  · funext i
    rw [ZornMatrix.mul_def]
    fin_cases i <;>
      simp [zornRealEquivNCReal, InfoGeometry.Physics.NCG.NCZornElement.mul,
        InfoGeometry.Physics.NCG.NCZornElement.zornCross, ZornMatrix.mul, ZornMatrix.cross,
        Matrix.vecHead, Matrix.vecTail, mul_comm z₂.b]
  · funext i
    rw [ZornMatrix.mul_def]
    fin_cases i <;>
      simp [zornRealEquivNCReal, InfoGeometry.Physics.NCG.NCZornElement.mul,
        InfoGeometry.Physics.NCG.NCZornElement.zornCross, ZornMatrix.mul, ZornMatrix.cross,
        Matrix.vecHead, Matrix.vecTail, mul_comm z₂.a]

/-- Wait-free commutative-specialization corollary: at `A = ℝ`, both same-chirality
superbracket defects collapse to `0`. -/
theorem zornReal_commutator_collapse (u v : InfoGeometry.Canonical.OperatorVector ℝ) :
    InfoGeometry.Canonical.oddOddSuperBracket
        (InfoGeometry.Canonical.sigmaPlus u) (InfoGeometry.Canonical.sigmaPlus v) = 0 ∧
    InfoGeometry.Canonical.oddOddSuperBracket
        (InfoGeometry.Canonical.sigmaMinus u) (InfoGeometry.Canonical.sigmaMinus v) = 0 :=
  ⟨InfoGeometry.Canonical.sigmaPlus_oddOddSuperBracket_zero u v,
   InfoGeometry.Canonical.sigmaMinus_oddOddSuperBracket_zero u v⟩

end NoncommOperatorRingBridge

end InfoGeometry.Canonical.TwoSheetedSplitOctonionDiracOperatorSystem
