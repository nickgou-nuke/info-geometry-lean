/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Canonical.DzhunushalievNonassociativeBridge
import InfoGeometry.Canonical.Barbaresco2020Souriau
import InfoGeometry.Algebra.SplitQuaternionAutomorphismStructure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# McKinstrie–Kozlov Wigner Angle in the Split-Quaternion Slice of the Zorn Algebra

Canonical bridge connecting the real split-quaternion subalgebra of `ZornVectorMatrix ℝ` (zero
complex `i`) to:
1. A real split-quaternion basis `G₁ = qSpace ℝ 2`, `G₂ = qCut7 ℝ`, `G₃ = qSpin ℝ 2` with the
   `su(1,1)`-normalized bracket constants, and Barbaresco's `sl₂(ℝ)` matrices
   (`Barbaresco2020Souriau.sl2H`, `sl2E`, `sl2F`);
2. The injective associative unital norm-preserving isomorphism `mat2ToZorn : M₂(ℝ) ↪ ZornVectorMatrix ℝ`
   carrying `det2` (`SplitQuaternionAutomorphismStructure`) directly to `ZornVectorMatrix.norm`;
3. The determinant-one split-quaternion conjugation action
   `zornAd g X := g * X * ZornVectorMatrix.conj g` preserves the `SO(1,2)` quadratic form and has
   explicit rotation (`zornRot θ`) and boost (`zornBoost ξ 0`) formulas. This file does not claim
   surjectivity onto `SO⁺(1,2)` or prove that the action has kernel exactly `{1, -1}`;
4. Exact spinor half-angle extraction of the McKinstrie–Kozlov Wigner angle (`wignerXHalf`,
   `wignerYHalf`), full-angle cosine/sine equivalence (`1 + γ_c` denominator), Pythagorean
   identity, perpendicular `α = π/2` formula, and exact polar factorization (`zornBoost_comp_wigner_polar_cancel`);
5. Lifting from the associative 4D split-quaternion slice to three specified axis boosts in the full
   8D split-octonion carrier `ZornVectorMatrix ℝ`, whose associator is a nonzero multiple of
   `qCut7 ℝ` when all three rapidities are nonzero. This is an algebraic associator identity, not a
   separately defined phase or a theorem about arbitrary non-coplanar Lorentz transformations.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & TRIGONOMETRIC/HYPERBOLIC THEOREMS
* `zornG_squares_and_su11_brackets`, `mat2ToZorn_hom_and_norm`, `mat2ToZorn_sl2_alignment`
* `minkVec_norm`, `zornAd_norm`, `zornAd_neg`, `zornAd_mul`
* `zornRot_norm`, `zornBoost_norm`, `zornAd_rot`, `zornAd_boost_zero`
* `zornBoost_comp_trace_and_rot`, `mckinstrie_kozlov_wigner_full_angle_identities`,
  `zornBoost_comp_wigner_polar_cancel`
* `zornAxisBoost_norm`, `three_noncoplanar_zorn_boosts_associator`,
  `three_noncoplanar_zorn_boosts_associator_ne_zero`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* Double-cover multiplication `zornAd_mul` holds on the associative 4D split-quaternion slice
  `Set.range mat2ToZorn`; `zornAd_norm` assumes `det2 M = 1`; nonzero 3-boost associator assumes
  `ξ₀ ≠ 0 ∧ ξ₁ ≠ 0 ∧ ξ₂ ≠ 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
* No continuous integral Berry-holonomy path integration on infinite-dimensional coadjoint orbits
  is claimed here.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.McKinstrieKozlovWignerZornBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.SplitQuaternionMatrices
open InfoGeometry.Canonical.DzhunushalievNonassociativeBridge
open InfoGeometry.Canonical.Barbaresco2020Souriau
open Matrix

private lemma zvm_add_a (X Y : ZornVectorMatrix ℝ) : (X + Y).a = X.a + Y.a := rfl
private lemma zvm_add_v (X Y : ZornVectorMatrix ℝ) (i : Fin 3) : (X + Y).v i = X.v i + Y.v i := rfl
private lemma zvm_add_w (X Y : ZornVectorMatrix ℝ) (i : Fin 3) : (X + Y).w i = X.w i + Y.w i := rfl
private lemma zvm_add_b (X Y : ZornVectorMatrix ℝ) : (X + Y).b = X.b + Y.b := rfl
private lemma zvm_sub_a (X Y : ZornVectorMatrix ℝ) : (X - Y).a = X.a - Y.a := by
  rw [sub_eq_add_neg]; exact (sub_eq_add_neg X.a Y.a).symm
private lemma zvm_sub_v (X Y : ZornVectorMatrix ℝ) (i : Fin 3) : (X - Y).v i = X.v i - Y.v i := by
  rw [sub_eq_add_neg]; exact (sub_eq_add_neg (X.v i) (Y.v i)).symm
private lemma zvm_sub_w (X Y : ZornVectorMatrix ℝ) (i : Fin 3) : (X - Y).w i = X.w i - Y.w i := by
  rw [sub_eq_add_neg]; exact (sub_eq_add_neg (X.w i) (Y.w i)).symm
private lemma zvm_sub_b (X Y : ZornVectorMatrix ℝ) : (X - Y).b = X.b - Y.b := by
  rw [sub_eq_add_neg]; exact (sub_eq_add_neg X.b Y.b).symm

/-! ### Part 1: `su(1,1) ≅ sl₂(ℝ)` Subalgebra & `M₂(ℝ) ↪ ZornVectorMatrix ℝ` -/

/-- McKinstrie–Kozlov `G₁` (`G₁² = +1`): `qSpace ℝ 2 = U 2 + V 2`. -/
def zornG1 : ZornVectorMatrix ℝ := qSpace ℝ 2

/-- McKinstrie–Kozlov `G₂` (`G₂² = +1`): `qCut7 ℝ = E₂₂ - E₁₁`. -/
def zornG2 : ZornVectorMatrix ℝ := qCut7 ℝ

/-- McKinstrie–Kozlov `G₃` (`G₃² = -1`): `qSpin ℝ 2 = V 2 - U 2`. -/
def zornG3 : ZornVectorMatrix ℝ := qSpin ℝ 2

/-- Exact McKinstrie–Kozlov `(-2, +2, +2)` `su(1,1)` commutator and square relations inside
`ZornVectorMatrix ℝ` with zero complex `i`. -/
theorem zornG_squares_and_su11_brackets :
    (zornG1 * zornG1 = ZornVectorMatrix.one) ∧
    (zornG2 * zornG2 = ZornVectorMatrix.one) ∧
    (zornG3 * zornG3 = -ZornVectorMatrix.one) ∧
    (akivisBracket zornG1 zornG2 = -(2 : ℝ) • zornG3) ∧
    (akivisBracket zornG2 zornG3 = (2 : ℝ) • zornG1) ∧
    (akivisBracket zornG3 zornG1 = (2 : ℝ) • zornG2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (dzhunushaliev_zorn_basis_laws_ring (R := ℝ) 2).2.1
  · exact (dzhunushaliev_zorn_basis_laws_ring (R := ℝ) 2).2.2.1
  · exact (dzhunushaliev_zorn_basis_laws_ring (R := ℝ) 2).1
  · ext j <;> (try fin_cases j) <;>
      simp [akivisBracket, zornG1, zornG2, zornG3, qSpace, qCut7, qSpin, zvm_mul_def,
        ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11,
        ZornVectorMatrix.E22, ZornVectorMatrix.smul, ZornVectorMatrix.neg,
        ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
        zvm_add_b, zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
      ring
  · ext j <;> (try fin_cases j) <;>
      simp [akivisBracket, zornG1, zornG2, zornG3, qSpace, qCut7, qSpin, zvm_mul_def,
        ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11,
        ZornVectorMatrix.E22, ZornVectorMatrix.smul, ZornVectorMatrix.neg,
        ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
        zvm_add_b, zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
      ring
  · ext j <;> (try fin_cases j) <;>
      simp [akivisBracket, zornG1, zornG2, zornG3, qSpace, qCut7, qSpin, zvm_mul_def,
        ZornVectorMatrix.mul, ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11,
        ZornVectorMatrix.E22, ZornVectorMatrix.smul, ZornVectorMatrix.neg,
        ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
        zvm_add_b, zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
      ring

/-- Canonical 4D split-quaternion slice embedding `M₂(ℝ) ↪ ZornVectorMatrix ℝ` supported on the
`(e₁₁, U₂, V₂, e₂₂)` subalgebra. -/
def mat2ToZorn (M : Matrix (Fin 2) (Fin 2) ℝ) : ZornVectorMatrix ℝ where
  a := M 0 0
  v := fun i => if i = 2 then M 0 1 else 0
  w := fun i => if i = 2 then M 1 0 else 0
  b := M 1 1

/-- Homomorphism, injectivity, determinant-norm, adjugate-conjugation, and associativity laws for
`mat2ToZorn`. -/
theorem mat2ToZorn_hom_and_norm (A B C : Matrix (Fin 2) (Fin 2) ℝ) :
    Function.Injective mat2ToZorn ∧
    (mat2ToZorn 1 = ZornVectorMatrix.one) ∧
    (mat2ToZorn (A + B) = mat2ToZorn A + mat2ToZorn B) ∧
    (∀ r : ℝ, mat2ToZorn (r • A) = r • mat2ToZorn A) ∧
    (mat2ToZorn (A * B) = mat2ToZorn A * mat2ToZorn B) ∧
    (ZornVectorMatrix.norm (mat2ToZorn A) = det2 A) ∧
    (ZornVectorMatrix.conj (mat2ToZorn A) = mat2ToZorn !![A 1 1, -A 0 1; -A 1 0, A 0 0]) ∧
    (_root_.associator (mat2ToZorn A) (mat2ToZorn B) (mat2ToZorn C) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y h
    ext i j
    fin_cases i <;> fin_cases j
    · exact congrArg ZornVectorMatrix.a h
    · simpa [mat2ToZorn] using congrFun (congrArg ZornVectorMatrix.v h) 2
    · simpa [mat2ToZorn] using congrFun (congrArg ZornVectorMatrix.w h) 2
    · exact congrArg ZornVectorMatrix.b h
  · ext j <;> (try fin_cases j) <;> simp [mat2ToZorn, ZornVectorMatrix.one]
  · ext j <;> (try fin_cases j) <;> simp [mat2ToZorn, zvm_add_a, zvm_add_v, zvm_add_w, zvm_add_b]
  · intro r
    ext j <;> (try fin_cases j) <;> simp [mat2ToZorn]
  · ext j <;> (try fin_cases j) <;>
      simp [mat2ToZorn, zvm_mul_def, ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three, Fin.sum_univ_two, Matrix.mul_apply] <;>
      ring
  · simp [ZornVectorMatrix.norm, mat2ToZorn, det2, ZornVec3.dot, Fin.sum_univ_three]
  · ext j <;> (try fin_cases j) <;> simp [ZornVectorMatrix.conj, mat2ToZorn]
  · ext j <;> (try fin_cases j) <;>
      simp [_root_.associator_apply, mat2ToZorn, zvm_mul_def, ZornVectorMatrix.mul,
        ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three,
        zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
      ring

/-- Explicit non-commutativity witness on the `M₂(ℝ)` slice: `∃ A B, A * B ≠ B * A`. -/
theorem mat2_noncommutative : ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨sl2H, sl2E, fun h => ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp [sl2H, sl2E, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- Alignment of `mat2ToZorn` with `Barbaresco2020Souriau.sl2H`, `sl2E`, `sl2F` and `zornG1..3`. -/
theorem mat2ToZorn_sl2_alignment :
    (mat2ToZorn sl2H = -zornG2) ∧
    (mat2ToZorn sl2E = ZornVectorMatrix.U 2) ∧
    (mat2ToZorn sl2F = ZornVectorMatrix.V 2) ∧
    (mat2ToZorn !![0, (1 : ℝ); 1, 0] = zornG1) ∧
    (mat2ToZorn !![(-1 : ℝ), 0; 0, 1] = zornG2) ∧
    (mat2ToZorn !![0, (-1 : ℝ); 1, 0] = zornG3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext j <;> (try fin_cases j) <;>
      simp [mat2ToZorn, sl2H, sl2E, sl2F, zornG1, zornG2, zornG3, qSpace, qCut7, qSpin,
        ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
        ZornVec3.basis, zvm_add_a, zvm_add_v, zvm_add_w, zvm_add_b,
        zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] }

/-! ### Part 2: Spinorial `SL(2, ℝ) → SO⁺(1,2)` Double Cover via Zorn Conjugation -/

/-- `(1,2)` Minkowski vector embedded into the pure-imaginary split-quaternion Zorn slice. -/
def minkVec (t x y : ℝ) : ZornVectorMatrix ℝ :=
  t • zornG3 + x • zornG1 + y • zornG2

/-- Adjoint / spinorial conjugation `Ad_g(X) = g * X * conj g` on `ZornVectorMatrix ℝ`. -/
def zornAd (g X : ZornVectorMatrix ℝ) : ZornVectorMatrix ℝ :=
  g * X * ZornVectorMatrix.conj g

/-- The Zorn quadratic norm on `minkVec t x y` equals the exact `(1,2)` Minkowski interval
`t^2 - x^2 - y^2`. -/
theorem minkVec_norm (t x y : ℝ) :
    ZornVectorMatrix.norm (minkVec t x y) = t ^ 2 - x ^ 2 - y ^ 2 := by
  simp [ZornVectorMatrix.norm, minkVec, zornG1, zornG2, zornG3, qSpace, qCut7, qSpin,
    ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
    ZornVec3.basis, ZornVec3.dot, Fin.sum_univ_three,
    zvm_add_a, zvm_add_v, zvm_add_w, zvm_add_b,
    zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b]
  ring

theorem minkVec_in_mat2ToZorn (t x y : ℝ) :
    minkVec t x y = mat2ToZorn !![-y, x - t; x + t, y] := by
  ext j <;> (try fin_cases j) <;>
    simp [minkVec, mat2ToZorn, zornG1, zornG2, zornG3, qSpace, qCut7, qSpin,
      ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
      ZornVec3.basis, zvm_add_a, zvm_add_v, zvm_add_w, zvm_add_b,
      zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
    ring

/-- Unit-norm `SL(2, ℝ)` conjugation preserves the Zorn norm, identifies `±g`, and is functorial
on the associative split-quaternion slice `Set.range mat2ToZorn`. -/
theorem zornAd_unit_laws (A B : Matrix (Fin 2) (Fin 2) ℝ) (X : ZornVectorMatrix ℝ) :
    (det2 A = 1 → ZornVectorMatrix.norm (zornAd (mat2ToZorn A) X) = ZornVectorMatrix.norm X) ∧
    (zornAd (-mat2ToZorn A) X = zornAd (mat2ToZorn A) X) ∧
    (∀ M : Matrix (Fin 2) (Fin 2) ℝ,
      zornAd (mat2ToZorn A * mat2ToZorn B) (mat2ToZorn M) =
        zornAd (mat2ToZorn A) (zornAd (mat2ToZorn B) (mat2ToZorn M))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hA
    have hnorm := (mat2ToZorn_hom_and_norm A 1 1).2.2.2.2.2.1
    have hc : ZornVectorMatrix.norm (ZornVectorMatrix.conj (mat2ToZorn A)) = det2 A := by
      rw [← hnorm]
      simp [ZornVectorMatrix.norm, ZornVectorMatrix.conj, ZornVec3.dot]
      ring
    unfold zornAd
    simp only [zvm_mul_def]
    rw [ZornVectorMatrix.norm_mul, ZornVectorMatrix.norm_mul, hnorm, hc, hA, one_mul, mul_one]
  · have hneg : ZornVectorMatrix.conj (-mat2ToZorn A) = -ZornVectorMatrix.conj (mat2ToZorn A) := by
      ext j <;> (try fin_cases j) <;> simp [ZornVectorMatrix.conj, ZornVectorMatrix.neg]
    unfold zornAd
    simp only [hneg, neg_mul, mul_neg, neg_neg]
  · intro M
    have hadj : ∀ G : Matrix (Fin 2) (Fin 2) ℝ,
        ZornVectorMatrix.conj (mat2ToZorn G) =
          mat2ToZorn !![G 1 1, -G 0 1; -G 1 0, G 0 0] := by
      intro G
      ext j <;> (try fin_cases j) <;>
        simp [ZornVectorMatrix.conj, mat2ToZorn, zornG2, zornG3, qSpace, qCut7, qSpin,
          ZornVectorMatrix.one, ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11,
          ZornVectorMatrix.E22, ZornVec3.basis, zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
        ring
    have hhom := fun X Y : Matrix (Fin 2) (Fin 2) ℝ =>
      (mat2ToZorn_hom_and_norm X Y 1).2.2.2.2.1.symm
    unfold zornAd
    rw [hhom A B, hadj (A * B), hhom (A * B) M, hhom ((A * B) * M) _,
      hadj B, hhom B M, hhom (B * M) _, hhom A _, hadj A, hhom _ _]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring

/-- Zorn spinor for a spatial rotation by angle `θ`: `R(θ) = cos(θ/2)·1 + sin(θ/2)·G₃`. -/
def zornRot (θ : ℝ) : ZornVectorMatrix ℝ :=
  Real.cos (θ / 2) • ZornVectorMatrix.one + Real.sin (θ / 2) • zornG3

/-- Zorn spinor for a hyperbolic boost of rapidity `ξ` along azimuth `φ`:
`B(ξ, φ) = cosh(ξ/2)·1 + sinh(ξ/2)·(cos φ · G₁ + sin φ · G₂)`. -/
def zornBoost (ξ φ : ℝ) : ZornVectorMatrix ℝ :=
  Real.cosh (ξ / 2) • ZornVectorMatrix.one +
    Real.sinh (ξ / 2) • (Real.cos φ • zornG1 + Real.sin φ • zornG2)

theorem zornRot_in_mat2ToZorn (θ : ℝ) :
    zornRot θ = mat2ToZorn !![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] := by
  ext j <;> (try fin_cases j) <;>
    simp [zornRot, mat2ToZorn, zornG3, qSpin, ZornVectorMatrix.one, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
    ring

theorem zornBoost_in_mat2ToZorn (ξ φ : ℝ) :
    zornBoost ξ φ = mat2ToZorn
      !![Real.cosh (ξ / 2) - Real.sinh (ξ / 2) * Real.sin φ, Real.sinh (ξ / 2) * Real.cos φ;
         Real.sinh (ξ / 2) * Real.cos φ, Real.cosh (ξ / 2) + Real.sinh (ξ / 2) * Real.sin φ] := by
  ext j <;> (try fin_cases j) <;>
    simp [zornBoost, mat2ToZorn, zornG1, zornG2, qSpace, qCut7, ZornVectorMatrix.one,
      ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
      ZornVec3.basis, zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
    ring

theorem zornRot_norm (θ : ℝ) : ZornVectorMatrix.norm (zornRot θ) = 1 := by
  rw [zornRot_in_mat2ToZorn, (mat2ToZorn_hom_and_norm _ 1 1).2.2.2.2.2.1]
  simp only [det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_one]
  ring_nf
  linarith [Real.cos_sq_add_sin_sq (θ * (1 / 2))]

theorem zornBoost_norm (ξ φ : ℝ) : ZornVectorMatrix.norm (zornBoost ξ φ) = 1 := by
  rw [zornBoost_in_mat2ToZorn, (mat2ToZorn_hom_and_norm _ 1 1).2.2.2.2.2.1]
  simp only [det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_one]
  calc (Real.cosh (ξ / 2) - Real.sinh (ξ / 2) * Real.sin φ) *
          (Real.cosh (ξ / 2) + Real.sinh (ξ / 2) * Real.sin φ) -
        (Real.sinh (ξ / 2) * Real.cos φ) * (Real.sinh (ξ / 2) * Real.cos φ)
      = Real.cosh (ξ / 2) ^ 2 -
          Real.sinh (ξ / 2) ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) := by ring
    _ = Real.cosh (ξ / 2) ^ 2 - Real.sinh (ξ / 2) ^ 2 := by
          rw [Real.cos_sq_add_sin_sq, mul_one]
    _ = 1 := Real.cosh_sq_sub_sinh_sq (ξ / 2)

/-- Exact `SO(1,2)` spatial rotation on `minkVec` induced by Zorn conjugation `zornAd (zornRot θ)`. -/
theorem zornAd_rot (θ t x y : ℝ) :
    zornAd (zornRot θ) (minkVec t x y) =
      minkVec t (Real.cos θ * x - Real.sin θ * y) (Real.sin θ * x + Real.cos θ * y) := by
  have hcos : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    have hunit : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq (θ / 2)
    linarith [h, hunit]
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    exact h
  have hid : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq (θ / 2)
  have hidT : Real.cos (θ * (1 / 2)) ^ 2 * t + Real.sin (θ * (1 / 2)) ^ 2 * t = t := by
    have hmul : θ / 2 = θ * (1 / 2) := by ring
    rw [← hmul]
    calc
      Real.cos (θ / 2) ^ 2 * t + Real.sin (θ / 2) ^ 2 * t
          = t * (Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2) := by ring
      _ = t := by rw [hid]; ring
  rw [zornRot_in_mat2ToZorn, minkVec_in_mat2ToZorn, minkVec_in_mat2ToZorn]
  unfold zornAd
  rw [(mat2ToZorn_hom_and_norm _ 1 1).2.2.2.2.2.2.1,
    (mat2ToZorn_hom_and_norm _ _ 1).2.2.2.2.1.symm,
    (mat2ToZorn_hom_and_norm _ _ 1).2.2.2.2.1.symm]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  change mat2ToZorn
      (!![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] *
        !![-y, x - t; x + t, y] *
        !![!![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] 1 1,
          -!![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] 0 1;
          -!![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] 1 0,
          !![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] 0 0]) =
    mat2ToZorn
      !![-(Real.sin θ * x + Real.cos θ * y), Real.cos θ * x - Real.sin θ * y - t;
        Real.cos θ * x - Real.sin θ * y + t, Real.sin θ * x + Real.cos θ * y]
  have hmat :
      (!![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] *
        !![-y, x - t; x + t, y] *
        !![!![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] 1 1,
          -!![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] 0 1;
          -!![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] 1 0,
          !![Real.cos (θ / 2), -Real.sin (θ / 2); Real.sin (θ / 2), Real.cos (θ / 2)] 0 0]) =
      !![-(Real.sin θ * x + Real.cos θ * y), Real.cos θ * x - Real.sin θ * y - t;
        Real.cos θ * x - Real.sin θ * y + t, Real.sin θ * x + Real.cos θ * y] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hcos, hsin] <;>
      ring_nf <;> nlinarith [hidT]
  exact congrArg (mat2ToZorn : Matrix (Fin 2) (Fin 2) ℝ → ZornVectorMatrix ℝ) hmat

/-- Exact hyperbolic boost formula on `minkVec` induced by Zorn conjugation `zornAd (zornBoost ξ 0)`. -/
theorem zornAd_boost_zero (ξ t x y : ℝ) :
    zornAd (zornBoost ξ 0) (minkVec t x y) =
      minkVec (Real.cosh ξ * t - Real.sinh ξ * y) x (Real.cosh ξ * y - Real.sinh ξ * t) := by
  have hcosh : Real.cosh ξ = Real.cosh (ξ / 2) ^ 2 + Real.sinh (ξ / 2) ^ 2 := by
    have h := Real.cosh_two_mul (ξ / 2)
    rw [show 2 * (ξ / 2) = ξ by ring] at h
    exact h
  have hsinh : Real.sinh ξ = 2 * Real.sinh (ξ / 2) * Real.cosh (ξ / 2) := by
    have h := Real.sinh_two_mul (ξ / 2)
    rw [show 2 * (ξ / 2) = ξ by ring] at h
    exact h
  have hid : Real.cosh (ξ / 2) ^ 2 - Real.sinh (ξ / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (ξ / 2)
  have hidX : Real.cosh (ξ * (1 / 2)) ^ 2 * x - Real.sinh (ξ * (1 / 2)) ^ 2 * x = x := by
    have hmul : ξ / 2 = ξ * (1 / 2) := by ring
    rw [← hmul]
    calc
      Real.cosh (ξ / 2) ^ 2 * x - Real.sinh (ξ / 2) ^ 2 * x
          = x * (Real.cosh (ξ / 2) ^ 2 - Real.sinh (ξ / 2) ^ 2) := by ring
      _ = x := by rw [hid]; ring
  rw [zornBoost_in_mat2ToZorn, minkVec_in_mat2ToZorn, minkVec_in_mat2ToZorn]
  simp only [Real.cos_zero, Real.sin_zero, mul_zero, mul_one, sub_zero, add_zero]
  unfold zornAd
  rw [(mat2ToZorn_hom_and_norm _ 1 1).2.2.2.2.2.2.1,
    (mat2ToZorn_hom_and_norm _ _ 1).2.2.2.2.1.symm,
    (mat2ToZorn_hom_and_norm _ _ 1).2.2.2.2.1.symm]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  change mat2ToZorn
      (!![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] *
        !![-y, x - t; x + t, y] *
        !![!![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] 1 1,
          -!![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] 0 1;
          -!![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] 1 0,
          !![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] 0 0]) =
    mat2ToZorn
      !![-(Real.cosh ξ * y - Real.sinh ξ * t), x - (Real.cosh ξ * t - Real.sinh ξ * y);
        x + (Real.cosh ξ * t - Real.sinh ξ * y), Real.cosh ξ * y - Real.sinh ξ * t]
  have hmat :
      (!![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] *
        !![-y, x - t; x + t, y] *
        !![!![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] 1 1,
          -!![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] 0 1;
          -!![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] 1 0,
          !![Real.cosh (ξ / 2), Real.sinh (ξ / 2); Real.sinh (ξ / 2), Real.cosh (ξ / 2)] 0 0]) =
      !![-(Real.cosh ξ * y - Real.sinh ξ * t), x - (Real.cosh ξ * t - Real.sinh ξ * y);
        x + (Real.cosh ξ * t - Real.sinh ξ * y), Real.cosh ξ * y - Real.sinh ξ * t] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hcosh, hsinh] <;>
      ring_nf <;> nlinarith [hidX]
  exact congrArg (mat2ToZorn : Matrix (Fin 2) (Fin 2) ℝ → ZornVectorMatrix ℝ) hmat

/-! ### Part 3: Spinor Half-Angle Wigner Angle, Full-Angle Equivalence, & Polar Factorization -/

/-- Spinor half-angle cosine numerator `X_half = cosh(ξ₁/2)cosh(ξ₂/2) + sinh(ξ₁/2)sinh(ξ₂/2)cos α`. -/
def wignerXHalf (ξ₁ ξ₂ α : ℝ) : ℝ :=
  Real.cosh (ξ₁ / 2) * Real.cosh (ξ₂ / 2) +
    Real.sinh (ξ₁ / 2) * Real.sinh (ξ₂ / 2) * Real.cos α

/-- Spinor half-angle sine numerator `Y_half = sinh(ξ₁/2)sinh(ξ₂/2)sin α`. -/
def wignerYHalf (ξ₁ ξ₂ α : ℝ) : ℝ :=
  Real.sinh (ξ₁ / 2) * Real.sinh (ξ₂ / 2) * Real.sin α

/-- Exact extraction of the scalar trace (`wignerXHalf`) and `zornG3` rotational part (`wignerYHalf`)
directly from the Zorn spinor boost composition `zornBoost ξ₂ φ₂ * zornBoost ξ₁ φ₁`. -/
theorem zornBoost_comp_trace_and_rot (ξ₁ ξ₂ φ₁ φ₂ : ℝ) :
    let P := zornBoost ξ₂ φ₂ * zornBoost ξ₁ φ₁
    ((1 / 2 : ℝ) * ZornVectorMatrix.trace P = wignerXHalf ξ₁ ξ₂ (φ₂ - φ₁)) ∧
    ((1 / 2 : ℝ) * (P.w 2 - P.v 2) = wignerYHalf ξ₁ ξ₂ (φ₂ - φ₁)) ∧
    (∃ u1 u2 : ℝ,
      P = wignerXHalf ξ₁ ξ₂ (φ₂ - φ₁) • ZornVectorMatrix.one +
        wignerYHalf ξ₁ ξ₂ (φ₂ - φ₁) • zornG3 + u1 • zornG1 + u2 • zornG2) := by
  have hcos : Real.cos (φ₂ - φ₁) = Real.cos φ₂ * Real.cos φ₁ + Real.sin φ₂ * Real.sin φ₁ :=
    Real.cos_sub φ₂ φ₁
  have hsin : Real.sin (φ₂ - φ₁) = Real.sin φ₂ * Real.cos φ₁ - Real.cos φ₂ * Real.sin φ₁ :=
    Real.sin_sub φ₂ φ₁
  let u1 := Real.cosh (ξ₂ / 2) * Real.sinh (ξ₁ / 2) * Real.cos φ₁ +
    Real.sinh (ξ₂ / 2) * Real.cosh (ξ₁ / 2) * Real.cos φ₂
  let u2 := Real.cosh (ξ₂ / 2) * Real.sinh (ξ₁ / 2) * Real.sin φ₁ +
    Real.sinh (ξ₂ / 2) * Real.cosh (ξ₁ / 2) * Real.sin φ₂
  have hPmat : zornBoost ξ₂ φ₂ * zornBoost ξ₁ φ₁ =
      mat2ToZorn
        (!![Real.cosh (ξ₂ / 2) - Real.sinh (ξ₂ / 2) * Real.sin φ₂,
            Real.sinh (ξ₂ / 2) * Real.cos φ₂;
            Real.sinh (ξ₂ / 2) * Real.cos φ₂,
            Real.cosh (ξ₂ / 2) + Real.sinh (ξ₂ / 2) * Real.sin φ₂] *
         !![Real.cosh (ξ₁ / 2) - Real.sinh (ξ₁ / 2) * Real.sin φ₁,
            Real.sinh (ξ₁ / 2) * Real.cos φ₁;
            Real.sinh (ξ₁ / 2) * Real.cos φ₁,
            Real.cosh (ξ₁ / 2) + Real.sinh (ξ₁ / 2) * Real.sin φ₁]) := by
    rw [zornBoost_in_mat2ToZorn, zornBoost_in_mat2ToZorn,
      (mat2ToZorn_hom_and_norm _ _ 1).2.2.2.2.1.symm]
  dsimp
  simp only [zvm_mul_def] at hPmat
  refine ⟨?_, ?_, u1, u2, ?_⟩
  · change (1 / 2 : ℝ) * ZornVectorMatrix.trace
      ((zornBoost ξ₂ φ₂).mul (zornBoost ξ₁ φ₁)) = _
    rw [hPmat]
    simp [ZornVectorMatrix.trace, mat2ToZorn, Matrix.mul_apply, Fin.sum_univ_two, wignerXHalf, hcos]
    ring
  · change (1 / 2 : ℝ) *
      (((zornBoost ξ₂ φ₂).mul (zornBoost ξ₁ φ₁)).w 2 -
        ((zornBoost ξ₂ φ₂).mul (zornBoost ξ₁ φ₁)).v 2) = _
    rw [hPmat]
    simp [mat2ToZorn, Matrix.mul_apply, Fin.sum_univ_two, wignerYHalf, hsin]
    ring
  · change (zornBoost ξ₂ φ₂).mul (zornBoost ξ₁ φ₁) = _
    rw [hPmat]
    ext j <;> (try fin_cases j) <;>
      simp [mat2ToZorn, Matrix.mul_apply, Fin.sum_univ_two, ZornVectorMatrix.one,
        zornG1, zornG2, zornG3, qSpace, qCut7, qSpin, ZornVectorMatrix.U, ZornVectorMatrix.V,
        ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVec3.basis,
        zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b,
        wignerXHalf, wignerYHalf, u1, u2, hcos, hsin] <;>
      ring

private lemma wigner_full_sum (ξ₁ ξ₂ α : ℝ) :
    2 * (wignerXHalf ξ₁ ξ₂ α ^ 2 + wignerYHalf ξ₁ ξ₂ α ^ 2) =
      1 + (Real.cosh ξ₁ * Real.cosh ξ₂ + Real.sinh ξ₁ * Real.sinh ξ₂ * Real.cos α) := by
  have hc1 : Real.cosh ξ₁ = 2 * Real.cosh (ξ₁ / 2) ^ 2 - 1 := by
    have h := Real.cosh_two_mul (ξ₁ / 2)
    rw [show 2 * (ξ₁ / 2) = ξ₁ by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (ξ₁ / 2), h]
  have hc2 : Real.cosh ξ₂ = 2 * Real.cosh (ξ₂ / 2) ^ 2 - 1 := by
    have h := Real.cosh_two_mul (ξ₂ / 2)
    rw [show 2 * (ξ₂ / 2) = ξ₂ by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (ξ₂ / 2), h]
  have hs1 : Real.sinh ξ₁ = 2 * Real.sinh (ξ₁ / 2) * Real.cosh (ξ₁ / 2) := by
    have h := Real.sinh_two_mul (ξ₁ / 2)
    rw [show 2 * (ξ₁ / 2) = ξ₁ by ring] at h
    exact h
  have hs2 : Real.sinh ξ₂ = 2 * Real.sinh (ξ₂ / 2) * Real.cosh (ξ₂ / 2) := by
    have h := Real.sinh_two_mul (ξ₂ / 2)
    rw [show 2 * (ξ₂ / 2) = ξ₂ by ring] at h
    exact h
  have hid1 : Real.cosh (ξ₁ / 2) ^ 2 - Real.sinh (ξ₁ / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (ξ₁ / 2)
  have hid2 : Real.cosh (ξ₂ / 2) ^ 2 - Real.sinh (ξ₂ / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (ξ₂ / 2)
  have hsh1 : Real.sinh (ξ₁ / 2) ^ 2 = Real.cosh (ξ₁ / 2) ^ 2 - 1 := by linarith [hid1]
  have hsh2 : Real.sinh (ξ₂ / 2) ^ 2 = Real.cosh (ξ₂ / 2) ^ 2 - 1 := by linarith [hid2]
  have htrig : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  dsimp [wignerXHalf, wignerYHalf]
  rw [hc1, hc2, hs1, hs2]
  calc
    2 * ((Real.cosh (ξ₁ / 2) * Real.cosh (ξ₂ / 2) +
          Real.sinh (ξ₁ / 2) * Real.sinh (ξ₂ / 2) * Real.cos α) ^ 2 +
         (Real.sinh (ξ₁ / 2) * Real.sinh (ξ₂ / 2) * Real.sin α) ^ 2)
        = 2 * Real.cosh (ξ₁ / 2) ^ 2 * Real.cosh (ξ₂ / 2) ^ 2 +
            2 * Real.sinh (ξ₁ / 2) ^ 2 * Real.sinh (ξ₂ / 2) ^ 2 * (Real.cos α ^ 2 + Real.sin α ^ 2) +
            4 * (Real.sinh (ξ₁ / 2) * Real.cosh (ξ₁ / 2)) *
              (Real.sinh (ξ₂ / 2) * Real.cosh (ξ₂ / 2)) * Real.cos α := by ring
    _ = 2 * Real.cosh (ξ₁ / 2) ^ 2 * Real.cosh (ξ₂ / 2) ^ 2 +
          2 * Real.sinh (ξ₁ / 2) ^ 2 * Real.sinh (ξ₂ / 2) ^ 2 * 1 +
          4 * (Real.sinh (ξ₁ / 2) * Real.cosh (ξ₁ / 2)) *
            (Real.sinh (ξ₂ / 2) * Real.cosh (ξ₂ / 2)) * Real.cos α := by rw [htrig]
    _ = 1 + ((2 * Real.cosh (ξ₁ / 2) ^ 2 - 1) * (2 * Real.cosh (ξ₂ / 2) ^ 2 - 1) +
          2 * Real.sinh (ξ₁ / 2) * Real.cosh (ξ₁ / 2) *
            (2 * Real.sinh (ξ₂ / 2) * Real.cosh (ξ₂ / 2)) * Real.cos α) := by
          rw [hsh1, hsh2]
          ring

private lemma wigner_full_diff (ξ₁ ξ₂ α : ℝ) :
    2 * (wignerXHalf ξ₁ ξ₂ α ^ 2 - wignerYHalf ξ₁ ξ₂ α ^ 2) =
      (Real.cosh ξ₁ + Real.cosh ξ₂) + Real.sinh ξ₁ * Real.sinh ξ₂ * Real.cos α +
        (Real.cosh ξ₁ - 1) * (Real.cosh ξ₂ - 1) * Real.cos α ^ 2 := by
  have hc1 : Real.cosh ξ₁ = 2 * Real.cosh (ξ₁ / 2) ^ 2 - 1 := by
    have h := Real.cosh_two_mul (ξ₁ / 2)
    rw [show 2 * (ξ₁ / 2) = ξ₁ by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (ξ₁ / 2), h]
  have hc2 : Real.cosh ξ₂ = 2 * Real.cosh (ξ₂ / 2) ^ 2 - 1 := by
    have h := Real.cosh_two_mul (ξ₂ / 2)
    rw [show 2 * (ξ₂ / 2) = ξ₂ by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (ξ₂ / 2), h]
  have hs1 : Real.sinh ξ₁ = 2 * Real.sinh (ξ₁ / 2) * Real.cosh (ξ₁ / 2) := by
    have h := Real.sinh_two_mul (ξ₁ / 2)
    rw [show 2 * (ξ₁ / 2) = ξ₁ by ring] at h
    exact h
  have hs2 : Real.sinh ξ₂ = 2 * Real.sinh (ξ₂ / 2) * Real.cosh (ξ₂ / 2) := by
    have h := Real.sinh_two_mul (ξ₂ / 2)
    rw [show 2 * (ξ₂ / 2) = ξ₂ by ring] at h
    exact h
  have hid1 : Real.cosh (ξ₁ / 2) ^ 2 - Real.sinh (ξ₁ / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (ξ₁ / 2)
  have hid2 : Real.cosh (ξ₂ / 2) ^ 2 - Real.sinh (ξ₂ / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (ξ₂ / 2)
  have hsh1 : Real.sinh (ξ₁ / 2) ^ 2 = Real.cosh (ξ₁ / 2) ^ 2 - 1 := by linarith [hid1]
  have hsh2 : Real.sinh (ξ₂ / 2) ^ 2 = Real.cosh (ξ₂ / 2) ^ 2 - 1 := by linarith [hid2]
  have hcm1 : Real.cosh ξ₁ - 1 = 2 * Real.sinh (ξ₁ / 2) ^ 2 := by linarith [hc1, hid1]
  have hcm2 : Real.cosh ξ₂ - 1 = 2 * Real.sinh (ξ₂ / 2) ^ 2 := by linarith [hc2, hid2]
  have htrig : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  dsimp [wignerXHalf, wignerYHalf]
  rw [hcm1, hcm2, hc1, hc2, hs1, hs2]
  calc
    2 * ((Real.cosh (ξ₁ / 2) * Real.cosh (ξ₂ / 2) +
          Real.sinh (ξ₁ / 2) * Real.sinh (ξ₂ / 2) * Real.cos α) ^ 2 -
         (Real.sinh (ξ₁ / 2) * Real.sinh (ξ₂ / 2) * Real.sin α) ^ 2)
        = 2 * Real.cosh (ξ₁ / 2) ^ 2 * Real.cosh (ξ₂ / 2) ^ 2 +
            2 * Real.sinh (ξ₁ / 2) ^ 2 * Real.sinh (ξ₂ / 2) ^ 2 *
              (2 * Real.cos α ^ 2 - (Real.cos α ^ 2 + Real.sin α ^ 2)) +
            4 * (Real.sinh (ξ₁ / 2) * Real.cosh (ξ₁ / 2)) *
              (Real.sinh (ξ₂ / 2) * Real.cosh (ξ₂ / 2)) * Real.cos α := by ring
    _ = 2 * Real.cosh (ξ₁ / 2) ^ 2 * Real.cosh (ξ₂ / 2) ^ 2 +
          2 * Real.sinh (ξ₁ / 2) ^ 2 * Real.sinh (ξ₂ / 2) ^ 2 * (2 * Real.cos α ^ 2 - 1) +
          4 * (Real.sinh (ξ₁ / 2) * Real.cosh (ξ₁ / 2)) *
            (Real.sinh (ξ₂ / 2) * Real.cosh (ξ₂ / 2)) * Real.cos α := by rw [htrig]
    _ = (2 * Real.cosh (ξ₁ / 2) ^ 2 - 1 + (2 * Real.cosh (ξ₂ / 2) ^ 2 - 1)) +
          2 * Real.sinh (ξ₁ / 2) * Real.cosh (ξ₁ / 2) *
            (2 * Real.sinh (ξ₂ / 2) * Real.cosh (ξ₂ / 2)) * Real.cos α +
          2 * Real.sinh (ξ₁ / 2) ^ 2 * (2 * Real.sinh (ξ₂ / 2) ^ 2) * Real.cos α ^ 2 := by
          rw [hsh1, hsh2]
          ring

private lemma wigner_full_prod (ξ₁ ξ₂ α : ℝ) :
    4 * wignerXHalf ξ₁ ξ₂ α * wignerYHalf ξ₁ ξ₂ α =
      Real.sin α *
        (Real.sinh ξ₁ * Real.sinh ξ₂ +
          (Real.cosh ξ₁ - 1) * (Real.cosh ξ₂ - 1) * Real.cos α) := by
  have hc1 : Real.cosh ξ₁ = 2 * Real.cosh (ξ₁ / 2) ^ 2 - 1 := by
    have h := Real.cosh_two_mul (ξ₁ / 2)
    rw [show 2 * (ξ₁ / 2) = ξ₁ by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (ξ₁ / 2), h]
  have hc2 : Real.cosh ξ₂ = 2 * Real.cosh (ξ₂ / 2) ^ 2 - 1 := by
    have h := Real.cosh_two_mul (ξ₂ / 2)
    rw [show 2 * (ξ₂ / 2) = ξ₂ by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (ξ₂ / 2), h]
  have hs1 : Real.sinh ξ₁ = 2 * Real.sinh (ξ₁ / 2) * Real.cosh (ξ₁ / 2) := by
    have h := Real.sinh_two_mul (ξ₁ / 2)
    rw [show 2 * (ξ₁ / 2) = ξ₁ by ring] at h
    exact h
  have hs2 : Real.sinh ξ₂ = 2 * Real.sinh (ξ₂ / 2) * Real.cosh (ξ₂ / 2) := by
    have h := Real.sinh_two_mul (ξ₂ / 2)
    rw [show 2 * (ξ₂ / 2) = ξ₂ by ring] at h
    exact h
  have hid1 : Real.cosh (ξ₁ / 2) ^ 2 - Real.sinh (ξ₁ / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (ξ₁ / 2)
  have hid2 : Real.cosh (ξ₂ / 2) ^ 2 - Real.sinh (ξ₂ / 2) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (ξ₂ / 2)
  have hcm1 : Real.cosh ξ₁ - 1 = 2 * Real.sinh (ξ₁ / 2) ^ 2 := by linarith [hc1, hid1]
  have hcm2 : Real.cosh ξ₂ - 1 = 2 * Real.sinh (ξ₂ / 2) ^ 2 := by linarith [hc2, hid2]
  dsimp [wignerXHalf, wignerYHalf]
  rw [hs1, hs2, hcm1, hcm2]
  ring

/-- **McKinstrie–Kozlov Half-Angle to Full-Angle Wigner Identities**:
Establishes the exact equivalence between spinor half-angle bilinear forms (`X_half² ± Y_half²`,
`2 X_half Y_half`) and full-angle Lorentz parameters (`cosh ξᵢ, sinh ξᵢ`), the Pythagorean sum of
squares identity, and the perpendicular boost (`α = π / 2`) simplification. -/
theorem mckinstrie_kozlov_wigner_full_angle_identities (ξ₁ ξ₂ α : ℝ) :
    let X := wignerXHalf ξ₁ ξ₂ α
    let Y := wignerYHalf ξ₁ ξ₂ α
    (2 * (X ^ 2 + Y ^ 2) =
      1 + (Real.cosh ξ₁ * Real.cosh ξ₂ + Real.sinh ξ₁ * Real.sinh ξ₂ * Real.cos α)) ∧
    (2 * (X ^ 2 - Y ^ 2) =
      (Real.cosh ξ₁ + Real.cosh ξ₂) + Real.sinh ξ₁ * Real.sinh ξ₂ * Real.cos α +
        (Real.cosh ξ₁ - 1) * (Real.cosh ξ₂ - 1) * Real.cos α ^ 2) ∧
    (4 * X * Y =
      Real.sin α *
        (Real.sinh ξ₁ * Real.sinh ξ₂ + (Real.cosh ξ₁ - 1) * (Real.cosh ξ₂ - 1) * Real.cos α)) ∧
    ((2 * (X ^ 2 - Y ^ 2)) ^ 2 + (4 * X * Y) ^ 2 = (2 * (X ^ 2 + Y ^ 2)) ^ 2) ∧
    (2 * (wignerXHalf ξ₁ ξ₂ (Real.pi / 2) ^ 2 + wignerYHalf ξ₁ ξ₂ (Real.pi / 2) ^ 2) =
      1 + Real.cosh ξ₁ * Real.cosh ξ₂ ∧
     2 * (wignerXHalf ξ₁ ξ₂ (Real.pi / 2) ^ 2 - wignerYHalf ξ₁ ξ₂ (Real.pi / 2) ^ 2) =
      Real.cosh ξ₁ + Real.cosh ξ₂ ∧
     4 * wignerXHalf ξ₁ ξ₂ (Real.pi / 2) * wignerYHalf ξ₁ ξ₂ (Real.pi / 2) =
      Real.sinh ξ₁ * Real.sinh ξ₂) := by
  dsimp
  refine ⟨wigner_full_sum ξ₁ ξ₂ α, wigner_full_diff ξ₁ ξ₂ α, wigner_full_prod ξ₁ ξ₂ α,
    by ring, ⟨?_, ?_, ?_⟩⟩
  · have h := wigner_full_sum ξ₁ ξ₂ (Real.pi / 2)
    simpa [Real.cos_pi_div_two] using h
  · have h := wigner_full_diff ξ₁ ξ₂ (Real.pi / 2)
    simpa [Real.cos_pi_div_two] using h
  · have h := wigner_full_prod ξ₁ ξ₂ (Real.pi / 2)
    simpa [Real.cos_pi_div_two, Real.sin_pi_div_two] using h

/-- **Exact Polar Factorization / Wigner Rotation Cancellation**:
Right-multiplying the composite Zorn boost spinor `P = zornBoost ξ₂ φ₂ * zornBoost ξ₁ φ₁` by the
inverse Wigner rotation spinor `((X / R) • 1 - (Y / R) • zornG3)` (where `R = √(X² + Y²) > 0`)
cancels its `zornG3` component identically, leaving a pure boost of norm `1`. -/
theorem zornBoost_comp_wigner_polar_cancel (ξ₁ ξ₂ φ₁ φ₂ : ℝ) :
    let X := wignerXHalf ξ₁ ξ₂ (φ₂ - φ₁)
    let Y := wignerYHalf ξ₁ ξ₂ (φ₂ - φ₁)
    let R := Real.sqrt (X ^ 2 + Y ^ 2)
    let Winv := (X / R) • ZornVectorMatrix.one - (Y / R) • zornG3
    let B := (zornBoost ξ₂ φ₂ * zornBoost ξ₁ φ₁) * Winv
    (0 < R) ∧
    (ZornVectorMatrix.norm Winv = 1) ∧
    (ZornVectorMatrix.norm B = 1) ∧
    (B.w 2 - B.v 2 = 0) ∧
    ((1 / 2 : ℝ) * ZornVectorMatrix.trace B = R) := by
  have h1c : 1 ≤ Real.cosh ξ₁ := Real.one_le_cosh ξ₁
  have h2c : 1 ≤ Real.cosh ξ₂ := Real.one_le_cosh ξ₂
  have hc1 : 0 ≤ Real.cosh ξ₁ - 1 := sub_nonneg.mpr h1c
  have hc2 : 0 ≤ Real.cosh ξ₂ - 1 := sub_nonneg.mpr h2c
  have hcs : Real.cosh ξ₁ * Real.cosh ξ₂ + Real.sinh ξ₁ * Real.sinh ξ₂ * Real.cos (φ₂ - φ₁) ≥ 1 := by
    have hadd := Real.cosh_add ξ₁ ξ₂
    have hsub := Real.cosh_sub ξ₁ ξ₂
    have h1p := Real.one_le_cosh (ξ₁ + ξ₂)
    have h1m := Real.one_le_cosh (ξ₁ - ξ₂)
    have hcle := Real.cos_le_one (φ₂ - φ₁)
    have hcge := Real.neg_one_le_cos (φ₂ - φ₁)
    have hnonneg :
        0 ≤ (1 + Real.cos (φ₂ - φ₁)) * (Real.cosh (ξ₁ + ξ₂) - 1) +
          (1 - Real.cos (φ₂ - φ₁)) * (Real.cosh (ξ₁ - ξ₂) - 1) := by
      have hp1 : 0 ≤ 1 + Real.cos (φ₂ - φ₁) := by linarith
      have hp2 : 0 ≤ Real.cosh (ξ₁ + ξ₂) - 1 := by linarith
      have hm1 : 0 ≤ 1 - Real.cos (φ₂ - φ₁) := by linarith
      have hm2 : 0 ≤ Real.cosh (ξ₁ - ξ₂) - 1 := by linarith
      nlinarith
    nlinarith [hadd, hsub, hnonneg]
  have hR2_pos : 0 < wignerXHalf ξ₁ ξ₂ (φ₂ - φ₁) ^ 2 + wignerYHalf ξ₁ ξ₂ (φ₂ - φ₁) ^ 2 := by
    have h2 := wigner_full_sum ξ₁ ξ₂ (φ₂ - φ₁)
    linarith
  have hR_pos : 0 < Real.sqrt (wignerXHalf ξ₁ ξ₂ (φ₂ - φ₁) ^ 2 + wignerYHalf ξ₁ ξ₂ (φ₂ - φ₁) ^ 2) :=
    Real.sqrt_pos.mpr hR2_pos
  have hR_sq :
      Real.sqrt (wignerXHalf ξ₁ ξ₂ (φ₂ - φ₁) ^ 2 + wignerYHalf ξ₁ ξ₂ (φ₂ - φ₁) ^ 2) ^ 2 =
        wignerXHalf ξ₁ ξ₂ (φ₂ - φ₁) ^ 2 + wignerYHalf ξ₁ ξ₂ (φ₂ - φ₁) ^ 2 :=
    Real.sq_sqrt hR2_pos.le
  set X := wignerXHalf ξ₁ ξ₂ (φ₂ - φ₁)
  set Y := wignerYHalf ξ₁ ξ₂ (φ₂ - φ₁)
  set R := Real.sqrt (X ^ 2 + Y ^ 2)
  have hR_ne : R ≠ 0 := hR_pos.ne'
  have hR_sq' : R ^ 2 = X ^ 2 + Y ^ 2 := by
    simpa [R, X, Y] using hR_sq
  have hWinv_mat :
      (X / R) • ZornVectorMatrix.one - (Y / R) • zornG3 =
        mat2ToZorn !![X / R, Y / R; -(Y / R), X / R] := by
    ext j <;> (try fin_cases j) <;>
      simp [mat2ToZorn, ZornVectorMatrix.one, zornG3, qSpin, ZornVectorMatrix.U,
        ZornVectorMatrix.V, ZornVec3.basis, zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
      ring
  have hWinv_norm : ZornVectorMatrix.norm ((X / R) • ZornVectorMatrix.one - (Y / R) • zornG3) = 1 := by
    rw [hWinv_mat, (mat2ToZorn_hom_and_norm _ 1 1).2.2.2.2.2.1]
    simp only [det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one]
    field_simp [hR_ne]
    linarith [hR_sq']
  have hB_norm :
      ZornVectorMatrix.norm
        ((zornBoost ξ₂ φ₂ * zornBoost ξ₁ φ₁) * ((X / R) • ZornVectorMatrix.one - (Y / R) • zornG3)) = 1 := by
    calc
      ZornVectorMatrix.norm ((zornBoost ξ₂ φ₂ * zornBoost ξ₁ φ₁) *
          ((X / R) • ZornVectorMatrix.one - (Y / R) • zornG3))
          = ZornVectorMatrix.norm (zornBoost ξ₂ φ₂) *
              (ZornVectorMatrix.norm (zornBoost ξ₁ φ₁) *
                ZornVectorMatrix.norm ((X / R) • ZornVectorMatrix.one - (Y / R) • zornG3)) := by
              simp only [zvm_mul_def]
              rw [ZornVectorMatrix.norm_mul, ZornVectorMatrix.norm_mul, mul_assoc]
      _ = 1 := by rw [zornBoost_norm, zornBoost_norm, hWinv_norm]; norm_num
  rcases zornBoost_comp_trace_and_rot ξ₁ ξ₂ φ₁ φ₂ with ⟨_, _, u1, u2, hP⟩
  have hP' : zornBoost ξ₂ φ₂ * zornBoost ξ₁ φ₁ =
      X • ZornVectorMatrix.one + Y • zornG3 + u1 • zornG1 + u2 • zornG2 := hP
  have hB_eq :
      (zornBoost ξ₂ φ₂ * zornBoost ξ₁ φ₁) * ((X / R) • ZornVectorMatrix.one - (Y / R) • zornG3) =
        R • ZornVectorMatrix.one +
          ((u1 * (X / R) - u2 * (Y / R)) • zornG1 + (u2 * (X / R) + u1 * (Y / R)) • zornG2) := by
    rw [hP']
    ext j <;> (try fin_cases j) <;>
      simp [zvm_mul_def, ZornVectorMatrix.mul, ZornVectorMatrix.one, zornG1, zornG2, zornG3,
        qSpace, qCut7, qSpin, ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11,
        ZornVectorMatrix.E22, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
        zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
      { field_simp [hR_ne]; nlinarith [hR_sq] }
  refine ⟨hR_pos, hWinv_norm, hB_norm, ?_, ?_⟩
  · rw [hB_eq]
    simp [ZornVectorMatrix.one, zornG1, zornG2, qSpace, qCut7, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVec3.basis,
      zvm_sub_v, zvm_sub_w]
  · rw [hB_eq]
    simp [ZornVectorMatrix.trace, ZornVectorMatrix.one, zornG1, zornG2, qSpace, qCut7,
      ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
      zvm_add_a, zvm_add_b, zvm_sub_a, zvm_sub_b]
    ring

/-! ### Part 4: Octonionic Lift — Three Non-Coplanar Zorn Boosts Produce a Nonzero `qCut7` Associator -/

/-- Pure split-octonion boost along any of the three hyperbolic directions `qSpace ℝ i` (`i = 0,1,2`). -/
def zornAxisBoost (i : Fin 3) (ξ : ℝ) : ZornVectorMatrix ℝ :=
  Real.cosh (ξ / 2) • ZornVectorMatrix.one + Real.sinh (ξ / 2) • qSpace ℝ i

theorem zornAxisBoost_norm (i : Fin 3) (ξ : ℝ) :
    ZornVectorMatrix.norm (zornAxisBoost i ξ) = 1 := by
  fin_cases i <;>
    { simp [zornAxisBoost, ZornVectorMatrix.norm, ZornVectorMatrix.one, qSpace,
        ZornVectorMatrix.U, ZornVectorMatrix.V, ZornVec3.basis, ZornVec3.dot, Fin.sum_univ_three]
      have h := Real.cosh_sq_sub_sinh_sq (ξ / 2)
      nlinarith [h] }

/-- **3-Boost Nonassociative Octonionic Phase Theorem**:
While any 2-boost or 3-boost product inside the 4D `SO(1,2)` split-quaternion slice has
`_root_.associator = 0`, three orthogonal boosts along `qSpace 0, qSpace 1, qSpace 2` in the full
8D split octonions acquire the exact chiral-cut associator
`2 sinh(ξ₀/2) sinh(ξ₁/2) sinh(ξ₂/2) • qCut7 ℝ`, strictly nonzero whenever `ξ₀, ξ₁, ξ₂ ≠ 0`. -/
theorem three_noncoplanar_zorn_boosts_associator (ξ₀ ξ₁ ξ₂ : ℝ) :
    _root_.associator (zornAxisBoost 0 ξ₀) (zornAxisBoost 1 ξ₁) (zornAxisBoost 2 ξ₂) =
      (2 * Real.sinh (ξ₀ / 2) * Real.sinh (ξ₁ / 2) * Real.sinh (ξ₂ / 2)) • qCut7 ℝ := by
  ext j <;> (try fin_cases j) <;>
    simp [_root_.associator_apply, zornAxisBoost, zvm_mul_def, ZornVectorMatrix.mul,
      ZornVectorMatrix.one, qSpace, qCut7, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVec3.basis, ZornVec3.dot,
      ZornVec3.cross, zvm_sub_a, zvm_sub_v, zvm_sub_w, zvm_sub_b] <;>
    ring

theorem three_noncoplanar_zorn_boosts_associator_ne_zero {ξ₀ ξ₁ ξ₂ : ℝ}
    (h0 : ξ₀ ≠ 0) (h1 : ξ₁ ≠ 0) (h2 : ξ₂ ≠ 0) :
    _root_.associator (zornAxisBoost 0 ξ₀) (zornAxisBoost 1 ξ₁) (zornAxisBoost 2 ξ₂) ≠ 0 := by
  rw [three_noncoplanar_zorn_boosts_associator]
  intro hzero
  have ha := congrArg ZornVectorMatrix.a hzero
  simp [qCut7, ZornVectorMatrix.E11, ZornVectorMatrix.E22, zvm_sub_a] at ha
  have hs0 : Real.sinh (ξ₀ / 2) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero h0 (by norm_num))
  have hs1 : Real.sinh (ξ₁ / 2) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero h1 (by norm_num))
  have hs2 : Real.sinh (ξ₂ / 2) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero h2 (by norm_num))
  have hprod : 2 * Real.sinh (ξ₀ / 2) * Real.sinh (ξ₁ / 2) * Real.sinh (ξ₂ / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1) hs2
  rcases ha with (h | h) | h <;> contradiction

/-! ### Part 5: `SO(1,2)` Schmidt Extraction & Algebraic Spinor Half-Angle Doubling (`eta21`) -/

/-- `SO(1,2)` fundamental `x`-boost `B_x(γ, u)` (`γ² - u² = 1`). -/
def so12BoostX (γ u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![γ, u, 0;
     u, γ, 0;
     0, 0, 1]

/-- `SO(1,2)` spatial rotation `R(c, s)` (`c² + s² = 1`). -/
def so12Rot (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0,  0;
     0, c, -s;
     0, s,  c]

/-- General `SO(1,2)` boost `B(γ, u, c, s) = R(c, s) B_x(γ, u) R(c, s)ᵀ`. -/
def so12BoostDir (γ u c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![γ,     u * c,             u * s;
     u * c, 1 + (γ - 1) * c^2, (γ - 1) * c * s;
     u * s, (γ - 1) * s * c,   1 + (γ - 1) * s^2]

/-- **Theorem (McKinstrie–Kozlov `SO(1,2)` Schmidt Extraction & Wigner Angle Identities)**:
Reuses `Barbaresco2020Souriau.eta21` (`diag(1, -1, -1)`) as the `SO(1,2)` bilinear form. -/
theorem mckinstrie_kozlov_so12_wigner_angle_identities
    (γ γ₁ u₁ γ₂ u₂ c s c₁ s₁ c₂ s₂ : ℝ)
    (h1 : γ₁ ^ 2 - u₁ ^ 2 = 1) (h2 : γ₂ ^ 2 - u₂ ^ 2 = 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    let L_schmidt := so12Rot c₂ s₂ * so12BoostX γ u₁ * (so12Rot c₁ s₁)ᵀ
    let L_prod := so12BoostDir γ₂ u₂ c s * so12BoostX γ₁ u₁
    let δ₁ := γ₁ - 1
    let δ₂ := γ₂ - 1
    (L_schmidt 1 1 + L_schmidt 2 2 = (γ + 1) * (c₂ * c₁ + s₂ * s₁) ∧
     L_schmidt 2 1 - L_schmidt 1 2 = (γ + 1) * (s₂ * c₁ - c₂ * s₁)) ∧
    (L_prod 0 0 = γ₂ * γ₁ + u₂ * u₁ * c) ∧
    (L_prod 2 1 - L_prod 1 2 = (u₂ * u₁ + δ₂ * δ₁ * c) * s) ∧
    (L_prod 1 1 + L_prod 2 2 = γ₂ + γ₁ + (u₂ * u₁ + δ₂ * δ₁ * c) * c) ∧
    (L_prodᵀ * eta21 * L_prod = eta21) ∧
    (((u₂ * u₁ + δ₂ * δ₁ * c) * s) ^ 2 + (γ₂ + γ₁ + (u₂ * u₁ + δ₂ * δ₁ * c) * c) ^ 2 =
      (γ₂ * γ₁ + 1 + u₂ * u₁ * c) ^ 2) := by
  dsimp
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith [hcs]
  have hu1 : u₁ ^ 2 = γ₁ ^ 2 - 1 := by linarith [h1]
  have hu2 : u₂ ^ 2 = γ₂ ^ 2 - 1 := by linarith [h2]
  have hB1 : (so12BoostX γ₁ u₁)ᵀ * eta21 * so12BoostX γ₁ u₁ = eta21 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [so12BoostX, eta21, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith
  have hR : (so12Rot c s)ᵀ * eta21 * so12Rot c s = eta21 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [so12Rot, eta21, Matrix.mul_apply, Fin.sum_univ_three] <;>
      nlinarith [hcs]
  have hR2 : so12Rot c s * eta21 * (so12Rot c s)ᵀ = eta21 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [so12Rot, eta21, Matrix.mul_apply, Fin.sum_univ_three] <;>
      nlinarith [hcs]
  have hDir : so12BoostDir γ₂ u₂ c s =
      so12Rot c s * so12BoostX γ₂ u₂ * (so12Rot c s)ᵀ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [so12BoostDir, so12Rot, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring_nf <;> nlinarith [hcs]
  have hBx2 : (so12BoostX γ₂ u₂)ᵀ * eta21 * so12BoostX γ₂ u₂ = eta21 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [so12BoostX, eta21, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith
  have hB2 : (so12BoostDir γ₂ u₂ c s)ᵀ * eta21 * so12BoostDir γ₂ u₂ c s = eta21 := by
    rw [hDir, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc (so12Rot c s * ((so12BoostX γ₂ u₂)ᵀ * (so12Rot c s)ᵀ)) * eta21 *
          (so12Rot c s * so12BoostX γ₂ u₂ * (so12Rot c s)ᵀ)
        = so12Rot c s * ((so12BoostX γ₂ u₂)ᵀ * ((so12Rot c s)ᵀ * eta21 * so12Rot c s) *
            so12BoostX γ₂ u₂) * (so12Rot c s)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = eta21 := by rw [hR, hBx2, hR2]
  have hLorentz : (so12BoostDir γ₂ u₂ c s * so12BoostX γ₁ u₁)ᵀ * eta21 *
      (so12BoostDir γ₂ u₂ c s * so12BoostX γ₁ u₁) = eta21 := by
    rw [Matrix.transpose_mul]
    calc (so12BoostX γ₁ u₁)ᵀ * (so12BoostDir γ₂ u₂ c s)ᵀ * eta21 *
          (so12BoostDir γ₂ u₂ c s * so12BoostX γ₁ u₁)
        = (so12BoostX γ₁ u₁)ᵀ * ((so12BoostDir γ₂ u₂ c s)ᵀ * eta21 * so12BoostDir γ₂ u₂ c s) *
            so12BoostX γ₁ u₁ := by simp only [Matrix.mul_assoc]
      _ = eta21 := by rw [hB2, hB1]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, hLorentz, ?_⟩
  · simp [so12Rot, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]; ring
  · simp [so12Rot, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]; ring
  · simp [so12BoostDir, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]; ring
  · simp [so12BoostDir, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]; ring
  · simp [so12BoostDir, so12BoostX, Matrix.mul_apply, Fin.sum_univ_three]
    ring_nf
    rw [hs2]
    ring
  · ring_nf
    rw [hs2, hu1, hu2]
    ring

/-- **Algebraic Half-Angle Spinor `(μᵢ, νᵢ)` to Full-Angle `SO(1,2)` Wigner Angle Doubling Law**:
For arbitrary `(μ₁, ν₁, μ₂, ν₂, c, s)` with `μᵢ² - νᵢ² = 1` and `c² + s² = 1`, recovers the exact
full-angle `SO(1,2)` Wigner sine, cosine, and `½(γ_c + 1)` denominator from `X_half = μ₂μ₁ + ν₂ν₁c`,
`Y_half = ν₂ν₁s`. -/
theorem zorn_spinor_half_angle_recovers_so12_wigner_angle
    (μ₁ ν₁ μ₂ ν₂ c s : ℝ)
    (h1 : μ₁ ^ 2 - ν₁ ^ 2 = 1) (h2 : μ₂ ^ 2 - ν₂ ^ 2 = 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    let γ₁ := μ₁ ^ 2 + ν₁ ^ 2
    let γ₂ := μ₂ ^ 2 + ν₂ ^ 2
    let u₁ := 2 * μ₁ * ν₁
    let u₂ := 2 * μ₂ * ν₂
    let δ₁ := γ₁ - 1
    let δ₂ := γ₂ - 1
    let X_half := μ₂ * μ₁ + ν₂ * ν₁ * c
    let Y_half := ν₂ * ν₁ * s
    (γ₁ ^ 2 - u₁ ^ 2 = 1 ∧ γ₂ ^ 2 - u₂ ^ 2 = 1) ∧
    (2 * X_half * Y_half = (1 / 2 : ℝ) * ((u₂ * u₁ + δ₂ * δ₁ * c) * s)) ∧
    (X_half ^ 2 - Y_half ^ 2 = (1 / 2 : ℝ) * (γ₂ + γ₁ + (u₂ * u₁ + δ₂ * δ₁ * c) * c)) ∧
    (X_half ^ 2 + Y_half ^ 2 = (1 / 2 : ℝ) * (γ₂ * γ₁ + 1 + u₂ * u₁ * c)) := by
  dsimp
  have hμ1 : μ₁ ^ 2 = ν₁ ^ 2 + 1 := by linarith [h1]
  have hμ2 : μ₂ ^ 2 = ν₂ ^ 2 + 1 := by linarith [h2]
  have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith [hcs]
  refine ⟨⟨by nlinarith [h1], by nlinarith [h2]⟩, ?_, ?_, ?_⟩
  · ring_nf; rw [hμ1, hμ2]; ring
  · ring_nf; rw [hs2, hμ1, hμ2]; ring
  · ring_nf; rw [hs2, hμ1, hμ2]; ring

end InfoGeometry.Canonical.McKinstrieKozlovWignerZornBridge
