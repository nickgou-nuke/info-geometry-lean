/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Kleinian Null-Plane Incidence, 4-Mode Witt CAR, and Born Reciprocity in `Cl(4,4) ≅ M₁₆(ℝ)`

Formalizes the split-octonion `𝕆_s` left-multiplication representation inside `M₈(ℝ)`
using exact Cayley–Dickson multiplication `(a, b)(c, d) = (a c + d̄ b, d a + b c̄)` on
`(ℍ, ℓℍ)` (`ℓ² = +1`), the universal Kleinian null-plane incidence theorem
(`range (L_{x̄}) = ker (L_x)` with `finrank (ker L_x) = 4` for every nonzero null split octonion `x`),
and the `16 × 16` block Clifford representation `Cl(4,4) ≅ M₁₆(ℝ)` housing the 4-mode Witt
fermionic CAR algebra, the Born reciprocity involution `B_Born = Γ₄Γ₅Γ₆Γ₇`, and the chiral
volume element `ω_{4,4} = Γ₀⋯Γ₇ = diag(-I₈, I₈)`.
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace InfoGeometry.Canonical.KleinianWittBornNullIncidence

/-- Carrier for the 8-dimensional split-octonion algebra `𝕆_s`. -/
abbrev OctS := Fin 8 → ℝ

/-- Split-signature `(4, 4)` norm form on `𝕆_s`. -/
def octNorm (x : OctS) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 - x 4 ^ 2 - x 5 ^ 2 - x 6 ^ 2 - x 7 ^ 2

/-- Polarized split-signature `(4, 4)` bilinear pairing on `𝕆_s`. -/
def octPolar (x y : OctS) : ℝ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 -
    x 4 * y 4 - x 5 * y 5 - x 6 * y 6 - x 7 * y 7

/-- Split-octonion conjugation reversing the seven imaginary directions. -/
def octConj (x : OctS) : OctS :=
  ![x 0, -x 1, -x 2, -x 3, -x 4, -x 5, -x 6, -x 7]

/-- Exact Cayley–Dickson split-octonion multiplication `(a, b)(c, d) = (a c + d̄ b, d a + b c̄)`
over `(ℍ, ℓℍ)` with `ℓ² = +1`. -/
def octMul {R : Type*} [Ring R] (x y : Fin 8 → R) : Fin 8 → R :=
  ![ x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 + x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7,
     x 0 * y 1 + x 1 * y 0 + x 2 * y 3 - x 3 * y 2 - x 4 * y 5 + x 5 * y 4 + x 6 * y 7 - x 7 * y 6,
     x 0 * y 2 - x 1 * y 3 + x 2 * y 0 + x 3 * y 1 - x 4 * y 6 - x 5 * y 7 + x 6 * y 4 + x 7 * y 5,
     x 0 * y 3 + x 1 * y 2 - x 2 * y 1 + x 3 * y 0 - x 4 * y 7 + x 5 * y 6 - x 6 * y 5 + x 7 * y 4,
     x 0 * y 4 - x 1 * y 5 - x 2 * y 6 - x 3 * y 7 + x 4 * y 0 + x 5 * y 1 + x 6 * y 2 + x 7 * y 3,
     x 0 * y 5 + x 1 * y 4 - x 2 * y 7 + x 3 * y 6 - x 4 * y 1 + x 5 * y 0 - x 6 * y 3 + x 7 * y 2,
     x 0 * y 6 + x 1 * y 7 + x 2 * y 4 - x 3 * y 5 - x 4 * y 2 + x 5 * y 3 + x 6 * y 0 - x 7 * y 1,
     x 0 * y 7 - x 1 * y 6 + x 2 * y 5 + x 3 * y 4 - x 4 * y 3 - x 5 * y 2 + x 6 * y 1 + x 7 * y 0 ]

/-- Explicit `8 × 8` matrix representation of left multiplication `L_x : y ↦ x * y` over any ring `R`. -/
def leftMulMatGen {R : Type*} [Ring R] (x : Fin 8 → R) : Matrix (Fin 8) (Fin 8) R :=
  !![ x 0, -x 1, -x 2, -x 3,  x 4,  x 5,  x 6,  x 7;
      x 1,  x 0, -x 3,  x 2,  x 5, -x 4, -x 7,  x 6;
      x 2,  x 3,  x 0, -x 1,  x 6,  x 7, -x 4, -x 5;
      x 3, -x 2,  x 1,  x 0,  x 7, -x 6,  x 5, -x 4;
      x 4,  x 5,  x 6,  x 7,  x 0, -x 1, -x 2, -x 3;
      x 5, -x 4,  x 7, -x 6,  x 1,  x 0,  x 3, -x 2;
      x 6, -x 7, -x 4,  x 5,  x 2, -x 3,  x 0,  x 1;
      x 7,  x 6, -x 5, -x 4,  x 3,  x 2, -x 1,  x 0 ]

/-- `8 × 8` real left-multiplication matrix `L_x`. -/
def leftMulMat (x : OctS) : Matrix (Fin 8) (Fin 8) ℝ :=
  leftMulMatGen x

/-- Integer `8 × 8` left-multiplication basis matrix for kernel-checked `decide` evaluation. -/
def leftMulInt (k : Fin 8) : Matrix (Fin 8) (Fin 8) ℤ :=
  leftMulMatGen (Pi.single k (1 : ℤ))

/-- Consistency check: `(leftMulMat x) *ᵥ y = octMul x y`. -/
theorem leftMulMat_mulVec (x y : OctS) : (leftMulMat x).mulVec y = octMul x y := by
  ext i
  fin_cases i <;>
    simp [leftMulMat, leftMulMatGen, octMul, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] <;>
    ring

/-- Left-multiplication composition identity `L_x L_{x̄} = ⟨x, x⟩ I₈`. -/
theorem oct_composition_left (x : OctS) :
    leftMulMat x * leftMulMat (octConj x) = octNorm x • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftMulMat, leftMulMatGen, octConj, octNorm, Matrix.mul_apply, Fin.sum_univ_eight] <;>
    ring

private lemma leftMulMat_add (x y : OctS) : leftMulMat (x + y) = leftMulMat x + leftMulMat y := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [leftMulMat, leftMulMatGen]; try ring)

private lemma octConj_add (x y : OctS) : octConj (x + y) = octConj x + octConj y := by
  ext i
  fin_cases i <;> (simp [octConj]; try ring)

private lemma octNorm_add (x y : OctS) :
    octNorm (x + y) = octNorm x + octNorm y + 2 * octPolar x y := by
  simp [octNorm, octPolar]
  ring

/-- Polarized Clifford anticommutation `L_x L_{ȳ} + L_y L_{x̄} = 2 ⟨x, y⟩ I₈`,
derived instantaneously by polarizing `oct_composition_left`. -/
theorem oct_polarized_clifford (x y : OctS) :
    leftMulMat x * leftMulMat (octConj y) + leftMulMat y * leftMulMat (octConj x) =
      (2 * octPolar x y) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  have hxy := oct_composition_left (x + y)
  have hx := oct_composition_left x
  have hy := oct_composition_left y
  rw [leftMulMat_add, octConj_add, leftMulMat_add, add_mul, mul_add, mul_add, hx, hy,
    octNorm_add, add_smul, add_smul] at hxy
  have hEq :
      (octNorm x • (1 : Matrix (Fin 8) (Fin 8) ℝ) +
          leftMulMat x * leftMulMat (octConj y)) +
        (leftMulMat y * leftMulMat (octConj x) +
          octNorm y • (1 : Matrix (Fin 8) (Fin 8) ℝ)) =
        (octNorm x • (1 : Matrix (Fin 8) (Fin 8) ℝ) +
          octNorm y • (1 : Matrix (Fin 8) (Fin 8) ℝ)) +
          (2 * octPolar x y) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    simpa [add_assoc] using hxy
  have hDiff := congrArg
    (fun M : Matrix (Fin 8) (Fin 8) ℝ =>
      M - (octNorm x • (1 : Matrix (Fin 8) (Fin 8) ℝ) +
        octNorm y • (1 : Matrix (Fin 8) (Fin 8) ℝ))) hEq
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hDiff

/-- Non-commutativity witness for split-octonion left multiplication (`L_{e₁} L_{e₂} ≠ L_{e₂} L_{e₁}`). -/
theorem leftMulMat_noncomm :
    leftMulMat (Pi.single 1 1) * leftMulMat (Pi.single 2 1) ≠
      leftMulMat (Pi.single 2 1) * leftMulMat (Pi.single 1 1) := by
  intro h
  have h30 := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M 3 0) h
  simp [leftMulMat, leftMulMatGen, Matrix.mul_apply, Fin.sum_univ_eight] at h30
  norm_num at h30

/-- Existential T16 non-commutativity witness for `M₈(ℝ)`. -/
theorem exists_noncomm_mat8_real :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℝ, A * B ≠ B * A :=
  ⟨leftMulMat (Pi.single 1 1), leftMulMat (Pi.single 2 1), leftMulMat_noncomm⟩

/-- Non-commutativity witness for `ℤ`-valued split-octonion basis matrices `M₈(ℤ)`. -/
theorem leftMulInt_noncomm : leftMulInt 1 * leftMulInt 2 ≠ leftMulInt 2 * leftMulInt 1 := by
  decide

/-- Existential T16 non-commutativity witness for `M₈(ℤ)`. -/
theorem exists_noncomm_mat8_int :
    ∃ A B : Matrix (Fin 8) (Fin 8) ℤ, A * B ≠ B * A :=
  ⟨leftMulInt 1, leftMulInt 2, leftMulInt_noncomm⟩

/-- Universal trace identity `Tr(L_x L_{ȳ}) = 8 ⟨x, y⟩`. -/
theorem oct_universal_trace (x y : OctS) :
    Matrix.trace (leftMulMat x * leftMulMat (octConj y)) = 8 * octPolar x y := by
  simp [Matrix.trace, Matrix.diag, leftMulMat, leftMulMatGen, octConj, octPolar,
    Fin.sum_univ_eight]
  ring

/-- For any real idempotent matrix `P` (`P * P = P`), the dimension of `range P` equals `trace P`. -/
lemma finrank_range_eq_trace_of_idempotent {n : ℕ} (PM : Matrix (Fin n) (Fin n) ℝ)
    (hIdem : PM * PM = PM) :
    (Module.finrank ℝ (LinearMap.range (Matrix.toLin' PM)) : ℝ) = Matrix.trace PM := by
  let P : Module.End ℝ (Fin n → ℝ) := Matrix.toLin' PM
  have hProj : LinearMap.IsProj (LinearMap.range P) P := by
    refine ⟨fun v => ⟨v, rfl⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    change (Matrix.toLin' PM) ((Matrix.toLin' PM) w) = Matrix.toLin' PM w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hIdem]
  have hTrP : LinearMap.trace ℝ (Fin n → ℝ) P = (Module.finrank ℝ (LinearMap.range P) : ℝ) :=
    hProj.trace
  have hTrMat : LinearMap.trace ℝ (Fin n → ℝ) P = Matrix.trace PM := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin n)) P]
    congr 1
    ext i j
    simp [P, Matrix.mulVec_single]
  rw [← hTrP, hTrMat]

private lemma octConj_involutive (x : OctS) : octConj (octConj x) = x := by
  ext i
  fin_cases i <;> simp [octConj]

private lemma octNorm_octConj (x : OctS) : octNorm (octConj x) = octNorm x := by
  simp [octNorm, octConj]

private lemma octPolar_octConj (x y : OctS) : octPolar (octConj x) (octConj y) = octPolar x y := by
  simp [octPolar, octConj]

private lemma exists_half_polar (x : OctS) (hx_ne : x ≠ 0) :
    ∃ y : OctS, octPolar x y = 1 / 2 := by
  have h_sum_ne : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 +
      x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2 ≠ 0 := by
    intro h0
    have hs : ∀ i : Fin 8, x i = 0 := by
      have hnn : ∀ j : Fin 8, 0 ≤ x j ^ 2 := fun j => sq_nonneg (x j)
      have hx0 : x 0 ^ 2 = 0 := by
        linarith [hnn 0, hnn 1, hnn 2, hnn 3, hnn 4, hnn 5, hnn 6, hnn 7, h0]
      have hx1 : x 1 ^ 2 = 0 := by
        linarith [hnn 0, hnn 1, hnn 2, hnn 3, hnn 4, hnn 5, hnn 6, hnn 7, h0]
      have hx2 : x 2 ^ 2 = 0 := by
        linarith [hnn 0, hnn 1, hnn 2, hnn 3, hnn 4, hnn 5, hnn 6, hnn 7, h0]
      have hx3 : x 3 ^ 2 = 0 := by
        linarith [hnn 0, hnn 1, hnn 2, hnn 3, hnn 4, hnn 5, hnn 6, hnn 7, h0]
      have hx4 : x 4 ^ 2 = 0 := by
        linarith [hnn 0, hnn 1, hnn 2, hnn 3, hnn 4, hnn 5, hnn 6, hnn 7, h0]
      have hx5 : x 5 ^ 2 = 0 := by
        linarith [hnn 0, hnn 1, hnn 2, hnn 3, hnn 4, hnn 5, hnn 6, hnn 7, h0]
      have hx6 : x 6 ^ 2 = 0 := by
        linarith [hnn 0, hnn 1, hnn 2, hnn 3, hnn 4, hnn 5, hnn 6, hnn 7, h0]
      have hx7 : x 7 ^ 2 = 0 := by
        linarith [hnn 0, hnn 1, hnn 2, hnn 3, hnn 4, hnn 5, hnn 6, hnn 7, h0]
      intro i
      fin_cases i <;> exact sq_eq_zero_iff.mp (by assumption)
    exact hx_ne (funext hs)
  set S := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 +
    x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
  refine ⟨fun i : Fin 8 => if i.val < 4 then x i / (2 * S) else -(x i) / (2 * S), ?_⟩
  simp only [octPolar]
  norm_num
  field_simp [h_sum_ne]
  ring

/-- **Universal Kleinian Null-Plane Incidence (Exactness)**:
for every nonzero null split octonion `x ≠ 0` (`octNorm x = 0`), `im (L_{x̄}) = ker (L_x)`. -/
theorem null_octonion_range_eq_ker
    (x : OctS) (hx_ne : x ≠ 0) (hx_null : octNorm x = 0) :
    LinearMap.range (Matrix.toLin' (leftMulMat (octConj x))) =
      LinearMap.ker (Matrix.toLin' (leftMulMat x)) := by
  obtain ⟨y, hy_polar⟩ := exists_half_polar x hx_ne
  set Lx := leftMulMat x
  set Lxbar := leftMulMat (octConj x)
  set Ly := leftMulMat y
  set Lybar := leftMulMat (octConj y)
  have hComp_x : Lx * Lxbar = 0 := by
    rw [oct_composition_left x, hx_null, zero_smul]
  have hPol_xbar_ybar : Lxbar * Ly + Lybar * Lx = 1 := by
    have h2 := oct_polarized_clifford (octConj x) (octConj y)
    rw [octConj_involutive x, octConj_involutive y, octPolar_octConj x y, hy_polar] at h2
    norm_num at h2
    exact h2
  ext v
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Matrix.toLin'_apply]
  constructor
  · rintro ⟨w, rfl⟩
    rw [Matrix.mulVec_mulVec, hComp_x, Matrix.zero_mulVec]
  · intro hLxv
    refine ⟨Ly.mulVec v, ?_⟩
    have hv := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => M.mulVec v) hPol_xbar_ybar
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hLxv, Matrix.mulVec_zero, add_zero] at hv
    exact hv

/-- **Universal Kleinian Null-Plane Incidence (Dimension 4)**:
for every nonzero null split octonion `x ≠ 0` (`octNorm x = 0`), `finrank (ker L_x) = 4`. -/
theorem null_octonion_ker_finrank_four
    (x : OctS) (hx_ne : x ≠ 0) (hx_null : octNorm x = 0) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (leftMulMat x))) = 4 := by
  obtain ⟨y, hy_polar⟩ := exists_half_polar x hx_ne
  set Lx := leftMulMat x
  set Lxbar := leftMulMat (octConj x)
  set Ly := leftMulMat y
  set Lybar := leftMulMat (octConj y)
  have hComp_xbar : Lxbar * Lx = 0 := by
    have h1 := oct_composition_left (octConj x)
    rwa [octConj_involutive x, octNorm_octConj x, hx_null, zero_smul] at h1
  have hPol_xy : Lx * Lybar + Ly * Lxbar = 1 := by
    have h2 := oct_polarized_clifford x y
    rw [hy_polar] at h2
    norm_num at h2
    exact h2
  have hIdem : (Lxbar * Ly) * (Lxbar * Ly) = Lxbar * Ly := by
    have hSub : Ly * Lxbar = 1 - Lx * Lybar := eq_sub_of_add_eq' hPol_xy
    calc
      (Lxbar * Ly) * (Lxbar * Ly) = Lxbar * (Ly * Lxbar) * Ly := by
        simp only [Matrix.mul_assoc]
      _ = Lxbar * (1 - Lx * Lybar) * Ly := by rw [hSub]
      _ = Lxbar * Ly - (Lxbar * Lx) * (Lybar * Ly) := by
        rw [mul_sub, mul_one, sub_mul]
        simp only [Matrix.mul_assoc]
      _ = Lxbar * Ly := by rw [hComp_xbar, zero_mul, sub_zero]
  have hTr : Matrix.trace (Lxbar * Ly) = 4 := by
    have h' := oct_universal_trace (octConj x) (octConj y)
    rw [octConj_involutive y, octPolar_octConj, hy_polar] at h'
    norm_num at h'
    exact h'
  have hFinrankProd : Module.finrank ℝ (LinearMap.range (Matrix.toLin' (Lxbar * Ly))) = 4 := by
    have hR := finrank_range_eq_trace_of_idempotent (Lxbar * Ly) hIdem
    rw [hTr] at hR
    exact_mod_cast hR
  have hRangeEq :
      LinearMap.range (Matrix.toLin' (Lxbar * Ly)) = LinearMap.range (Matrix.toLin' Lxbar) := by
    ext v
    simp only [LinearMap.mem_range, Matrix.toLin'_apply]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Ly.mulVec w, Matrix.mulVec_mulVec w Lxbar Ly⟩
    · rintro ⟨w, rfl⟩
      refine ⟨Lxbar.mulVec w, ?_⟩
      have hSub : Ly * Lxbar = 1 - Lx * Lybar := eq_sub_of_add_eq' hPol_xy
      calc
        (Lxbar * Ly).mulVec (Lxbar.mulVec w)
            = (Lxbar * (Ly * Lxbar)).mulVec w := by
                rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = (Lxbar * (1 - Lx * Lybar)).mulVec w := by rw [hSub]
        _ = (Lxbar - (Lxbar * Lx) * Lybar).mulVec w := by
                rw [mul_sub, mul_one, Matrix.mul_assoc]
        _ = Lxbar.mulVec w := by rw [hComp_xbar, zero_mul, sub_zero]
  rw [← null_octonion_range_eq_ker x hx_ne hx_null, ← hRangeEq]
  exact hFinrankProd

/-! ### Part 2: `Cl(4,4) ≅ M₁₆(ℝ)` Witt CAR, Born Reciprocity, and Chiral Volume Element -/

/-- Split signature `(4, 4)` metric entries: `+1` for `A < 4`, `-1` for `A ≥ 4`. -/
def sig44 (A B : Fin 8) : ℝ :=
  if A = B then (if A.val < 4 then 1 else -1) else 0

/-- `16 × 16` real block-antidiagonal `Cl(4,4)` gamma generators built from `L_{e_A}` and `L_{ē_A}`. -/
def gammaMat (A : Fin 8) : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ :=
  Matrix.fromBlocks 0 (leftMulMat (Pi.single A 1)) (leftMulMat (octConj (Pi.single A 1))) 0

/-- 4-mode Witt fermionic creation operators `γ^μ = Γ_μ + Γ_{μ+4}`. -/
def wittCreate (μ : Fin 4) : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ :=
  gammaMat ⟨μ.val, by omega⟩ + gammaMat ⟨μ.val + 4, by omega⟩

/-- 4-mode Witt fermionic annihilation operators `γ̃_μ = Γ_μ - Γ_{μ+4}`. -/
def wittAnnihil (μ : Fin 4) : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ :=
  gammaMat ⟨μ.val, by omega⟩ - gammaMat ⟨μ.val + 4, by omega⟩

/-- Born reciprocity involution `B_Born = Γ₄ Γ₅ Γ₆ Γ₇` swapping creation and annihilation modes. -/
def bornInvolution : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ :=
  gammaMat 4 * gammaMat 5 * gammaMat 6 * gammaMat 7

/-- Chiral volume element `ω_{4,4} = Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇` in `Cl(4,4) ≅ M₁₆(ℝ)`. -/
def volumeCl44 : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ :=
  gammaMat 0 * gammaMat 1 * gammaMat 2 * gammaMat 3 *
    gammaMat 4 * gammaMat 5 * gammaMat 6 * gammaMat 7

/-- Fundamental `Cl(4,4)` Clifford anticommutator `{Γ_A, Γ_B} = 2 η_{AB} I₁₆`. -/
theorem cl44_anticommutator (A B : Fin 8) :
    gammaMat A * gammaMat B + gammaMat B * gammaMat A =
      (2 * sig44 A B) • (1 : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ) := by
  have h1 := oct_polarized_clifford (Pi.single A 1) (Pi.single B 1)
  have h2 : leftMulMat (octConj (Pi.single A 1)) * leftMulMat (Pi.single B 1) +
      leftMulMat (octConj (Pi.single B 1)) * leftMulMat (Pi.single A 1) =
      (2 * octPolar (Pi.single A 1) (Pi.single B 1)) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    have h := oct_polarized_clifford (octConj (Pi.single A 1)) (octConj (Pi.single B 1))
    rwa [octConj_involutive (Pi.single A 1), octConj_involutive (Pi.single B 1),
      octPolar_octConj] at h
  have hPol : octPolar (Pi.single A 1) (Pi.single B 1) = sig44 A B := by
    fin_cases A <;> fin_cases B <;> simp [octPolar, sig44]
  unfold gammaMat
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp only [zero_mul, mul_zero, zero_add, add_zero, h1, h2, hPol]
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply]

private abbrev gamma1 : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ := gammaMat 1
private abbrev gamma2 : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ := gammaMat 2

/-- Non-commutativity witness for `Cl(4,4)` block generators: `Γ₁ Γ₂ ≠ Γ₂ Γ₁`. -/
theorem gammaMat_mul_noncomm : gamma1 * gamma2 ≠ gamma2 * gamma1 := by
  intro h
  dsimp [gamma1, gamma2] at h
  have h12 : gammaMat 1 * gammaMat 2 + gammaMat 2 * gammaMat 1 = 0 := by
    simpa [sig44] using cl44_anticommutator 1 2
  rw [h, ← two_smul ℝ] at h12
  have h0 : gammaMat 2 * gammaMat 1 = 0 :=
    smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) (by simpa using h12)
  have hmul : (gammaMat 2 * gammaMat 1) * gammaMat 1 = 0 := by rw [h0, zero_mul]
  have h1sq : gammaMat 1 * gammaMat 1 = 1 := by
    have h1 := cl44_anticommutator 1 1
    simp [sig44] at h1
    rw [← two_smul ℝ] at h1
    exact smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) (by simpa using h1)
  rw [Matrix.mul_assoc, h1sq, mul_one] at hmul
  have h2sq : gammaMat 2 * gammaMat 2 = 1 := by
    have h2 := cl44_anticommutator 2 2
    simp [sig44] at h2
    rw [← two_smul ℝ] at h2
    exact smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) (by simpa using h2)
  have hmul2 : gammaMat 2 * gammaMat 2 = gammaMat 2 * 0 := congrArg (gammaMat 2 * ·) hmul
  rw [h2sq, mul_zero] at hmul2
  have h00 := congrArg (fun M : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ => M (Sum.inl 0) (Sum.inl 0)) hmul2
  simp at h00

/-- Existential T16 non-commutativity witness for `M₁₆(ℝ)` (`Cl(4,4)` block carrier). -/
theorem exists_noncomm_mat16_real :
    ∃ A B : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ, A * B ≠ B * A :=
  ⟨gamma1, gamma2, gammaMat_mul_noncomm⟩

private lemma wittCreate_anticomm_abstract {B : Type*} [Ring B] [Algebra ℝ B]
    (G : Fin 8 → B)
    (hCliff : ∀ X Y : Fin 8, G X * G Y + G Y * G X = (2 * sig44 X Y) • (1 : B))
    (μ ν : Fin 4) :
    (G ⟨μ.val, by omega⟩ + G ⟨μ.val + 4, by omega⟩) *
        (G ⟨ν.val, by omega⟩ + G ⟨ν.val + 4, by omega⟩) +
      (G ⟨ν.val, by omega⟩ + G ⟨ν.val + 4, by omega⟩) *
        (G ⟨μ.val, by omega⟩ + G ⟨μ.val + 4, by omega⟩) = 0 := by
  have hSq : ∀ X : Fin 8, G X * G X = (if X.val < 4 then (1 : ℝ) else -1) • (1 : B) := by
    intro X
    have h := hCliff X X
    simp only [sig44, ↓reduceIte, ← two_smul ℝ] at h
    have h2 := smul_right_injective B (by norm_num : (2 : ℝ) ≠ 0)
    rw [mul_smul] at h
    exact h2 h
  have hAnti : ∀ X Y : Fin 8, X ≠ Y → G X * G Y + G Y * G X = 0 := fun X Y hne => by
    simpa [sig44, hne] using hCliff X Y
  by_cases hμν : μ = ν
  · subst hμν
    have h1 : G ⟨μ.val, by omega⟩ * G ⟨μ.val, by omega⟩ = 1 := by
      rw [hSq]; have hlt : (⟨μ.val, by omega⟩ : Fin 8).val < 4 := μ.isLt; simp [hlt]
    have h2 : G ⟨μ.val + 4, by omega⟩ * G ⟨μ.val + 4, by omega⟩ = -1 := by
      rw [hSq]
      have hge : ¬ ((⟨μ.val + 4, by omega⟩ : Fin 8).val < 4) := by
        change ¬ (μ.val + 4 < 4); omega
      simp [hge]
    have hne : (⟨μ.val, by omega⟩ : Fin 8) ≠ ⟨μ.val + 4, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    have hA := hAnti _ _ hne
    simp only [add_mul, mul_add, h1, h2]
    calc
      _ = (G ⟨μ.val, by omega⟩ * G ⟨μ.val + 4, by omega⟩ +
              G ⟨μ.val + 4, by omega⟩ * G ⟨μ.val, by omega⟩) +
            (G ⟨μ.val, by omega⟩ * G ⟨μ.val + 4, by omega⟩ +
              G ⟨μ.val + 4, by omega⟩ * G ⟨μ.val, by omega⟩) := by abel
      _ = 0 := by rw [hA, add_zero]
  · have h1 : (⟨μ.val, by omega⟩ : Fin 8) ≠ ⟨ν.val, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; exact hμν (Fin.ext hv)
    have h2 : (⟨μ.val, by omega⟩ : Fin 8) ≠ ⟨ν.val + 4, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    have h3 : (⟨μ.val + 4, by omega⟩ : Fin 8) ≠ ⟨ν.val, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    have h4 : (⟨μ.val + 4, by omega⟩ : Fin 8) ≠ ⟨ν.val + 4, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; exact hμν (Fin.ext (by omega))
    simp only [add_mul, mul_add]
    calc
      _ = (G ⟨μ.val, by omega⟩ * G ⟨ν.val, by omega⟩ +
            G ⟨ν.val, by omega⟩ * G ⟨μ.val, by omega⟩) +
          (G ⟨μ.val, by omega⟩ * G ⟨ν.val + 4, by omega⟩ +
            G ⟨ν.val + 4, by omega⟩ * G ⟨μ.val, by omega⟩) +
          (G ⟨μ.val + 4, by omega⟩ * G ⟨ν.val, by omega⟩ +
            G ⟨ν.val, by omega⟩ * G ⟨μ.val + 4, by omega⟩) +
          (G ⟨μ.val + 4, by omega⟩ * G ⟨ν.val + 4, by omega⟩ +
            G ⟨ν.val + 4, by omega⟩ * G ⟨μ.val + 4, by omega⟩) := by abel
      _ = 0 := by rw [hAnti _ _ h1, hAnti _ _ h2, hAnti _ _ h3, hAnti _ _ h4]; simp

/-- Witt creation operators pairwise anticommute: `{γ^μ, γ^ν} = 0`. -/
theorem wittCreate_anticomm (μ ν : Fin 4) :
    wittCreate μ * wittCreate ν + wittCreate ν * wittCreate μ = 0 :=
  wittCreate_anticomm_abstract gammaMat cl44_anticommutator μ ν

private lemma wittAnnihil_anticomm_abstract {B : Type*} [Ring B] [Algebra ℝ B]
    (G : Fin 8 → B)
    (hCliff : ∀ X Y : Fin 8, G X * G Y + G Y * G X = (2 * sig44 X Y) • (1 : B))
    (μ ν : Fin 4) :
    (G ⟨μ.val, by omega⟩ - G ⟨μ.val + 4, by omega⟩) *
        (G ⟨ν.val, by omega⟩ - G ⟨ν.val + 4, by omega⟩) +
      (G ⟨ν.val, by omega⟩ - G ⟨ν.val + 4, by omega⟩) *
        (G ⟨μ.val, by omega⟩ - G ⟨μ.val + 4, by omega⟩) = 0 := by
  have hSq : ∀ X : Fin 8, G X * G X = (if X.val < 4 then (1 : ℝ) else -1) • (1 : B) := by
    intro X
    have h := hCliff X X
    simp only [sig44, ↓reduceIte, ← two_smul ℝ] at h
    have h2 := smul_right_injective B (by norm_num : (2 : ℝ) ≠ 0)
    rw [mul_smul] at h
    exact h2 h
  have hAnti : ∀ X Y : Fin 8, X ≠ Y → G X * G Y + G Y * G X = 0 := fun X Y hne => by
    simpa [sig44, hne] using hCliff X Y
  by_cases hμν : μ = ν
  · subst hμν
    have h1 : G ⟨μ.val, by omega⟩ * G ⟨μ.val, by omega⟩ = 1 := by
      rw [hSq]; have hlt : (⟨μ.val, by omega⟩ : Fin 8).val < 4 := μ.isLt; simp [hlt]
    have h2 : G ⟨μ.val + 4, by omega⟩ * G ⟨μ.val + 4, by omega⟩ = -1 := by
      rw [hSq]
      have hge : ¬ ((⟨μ.val + 4, by omega⟩ : Fin 8).val < 4) := by
        change ¬ (μ.val + 4 < 4); omega
      simp [hge]
    have hne : (⟨μ.val, by omega⟩ : Fin 8) ≠ ⟨μ.val + 4, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    have hA := hAnti _ _ hne
    simp only [sub_mul, mul_sub, h1, h2]
    calc
      _ = -(G ⟨μ.val, by omega⟩ * G ⟨μ.val + 4, by omega⟩ +
                G ⟨μ.val + 4, by omega⟩ * G ⟨μ.val, by omega⟩) -
              (G ⟨μ.val, by omega⟩ * G ⟨μ.val + 4, by omega⟩ +
                G ⟨μ.val + 4, by omega⟩ * G ⟨μ.val, by omega⟩) := by abel
      _ = 0 := by rw [hA, neg_zero, sub_zero]
  · have h1 : (⟨μ.val, by omega⟩ : Fin 8) ≠ ⟨ν.val, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; exact hμν (Fin.ext hv)
    have h2 : (⟨μ.val, by omega⟩ : Fin 8) ≠ ⟨ν.val + 4, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    have h3 : (⟨μ.val + 4, by omega⟩ : Fin 8) ≠ ⟨ν.val, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    have h4 : (⟨μ.val + 4, by omega⟩ : Fin 8) ≠ ⟨ν.val + 4, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; exact hμν (Fin.ext (by omega))
    simp only [sub_mul, mul_sub]
    calc
      _ = (G ⟨μ.val, by omega⟩ * G ⟨ν.val, by omega⟩ +
            G ⟨ν.val, by omega⟩ * G ⟨μ.val, by omega⟩) -
          (G ⟨μ.val, by omega⟩ * G ⟨ν.val + 4, by omega⟩ +
            G ⟨ν.val + 4, by omega⟩ * G ⟨μ.val, by omega⟩) -
          (G ⟨μ.val + 4, by omega⟩ * G ⟨ν.val, by omega⟩ +
            G ⟨ν.val, by omega⟩ * G ⟨μ.val + 4, by omega⟩) +
          (G ⟨μ.val + 4, by omega⟩ * G ⟨ν.val + 4, by omega⟩ +
            G ⟨ν.val + 4, by omega⟩ * G ⟨μ.val + 4, by omega⟩) := by abel
      _ = 0 := by rw [hAnti _ _ h1, hAnti _ _ h2, hAnti _ _ h3, hAnti _ _ h4]; simp

/-- Witt annihilation operators pairwise anticommute: `{γ̃_μ, γ̃_ν} = 0`. -/
theorem wittAnnihil_anticomm (μ ν : Fin 4) :
    wittAnnihil μ * wittAnnihil ν + wittAnnihil ν * wittAnnihil μ = 0 :=
  wittAnnihil_anticomm_abstract gammaMat cl44_anticommutator μ ν

private lemma witt_CAR_relation_abstract {B : Type*} [Ring B] [Algebra ℝ B]
    (G : Fin 8 → B)
    (hCliff : ∀ X Y : Fin 8, G X * G Y + G Y * G X = (2 * sig44 X Y) • (1 : B))
    (μ ν : Fin 4) :
    (G ⟨μ.val, by omega⟩ + G ⟨μ.val + 4, by omega⟩) *
        (G ⟨ν.val, by omega⟩ - G ⟨ν.val + 4, by omega⟩) +
      (G ⟨ν.val, by omega⟩ - G ⟨ν.val + 4, by omega⟩) *
        (G ⟨μ.val, by omega⟩ + G ⟨μ.val + 4, by omega⟩) =
      (if μ = ν then (4 : ℝ) else 0) • (1 : B) := by
  have hSq : ∀ X : Fin 8, G X * G X = (if X.val < 4 then (1 : ℝ) else -1) • (1 : B) := by
    intro X
    have h := hCliff X X
    simp only [sig44, ↓reduceIte, ← two_smul ℝ] at h
    have h2 := smul_right_injective B (by norm_num : (2 : ℝ) ≠ 0)
    rw [mul_smul] at h
    exact h2 h
  have hAnti : ∀ X Y : Fin 8, X ≠ Y → G X * G Y + G Y * G X = 0 := fun X Y hne => by
    simpa [sig44, hne] using hCliff X Y
  by_cases hμν : μ = ν
  · subst hμν
    have h1 : G ⟨μ.val, by omega⟩ * G ⟨μ.val, by omega⟩ = 1 := by
      rw [hSq]; have hlt : (⟨μ.val, by omega⟩ : Fin 8).val < 4 := μ.isLt; simp [hlt]
    have h2 : G ⟨μ.val + 4, by omega⟩ * G ⟨μ.val + 4, by omega⟩ = -1 := by
      rw [hSq]
      have hge : ¬ ((⟨μ.val + 4, by omega⟩ : Fin 8).val < 4) := by
        change ¬ (μ.val + 4 < 4); omega
      simp [hge]
    simp only [↓reduceIte, add_mul, mul_add, sub_mul, mul_sub, h1, h2]
    have hAb : (1 + G ⟨μ.val + 4, by omega⟩ * G ⟨μ.val, by omega⟩ -
          (G ⟨μ.val, by omega⟩ * G ⟨μ.val + 4, by omega⟩ + -1)) +
        (1 - G ⟨μ.val + 4, by omega⟩ * G ⟨μ.val, by omega⟩ +
          (G ⟨μ.val, by omega⟩ * G ⟨μ.val + 4, by omega⟩ - -1)) =
        ((1 + 1 + 1 + 1 : ℝ) • (1 : B)) := by
      rw [add_smul, add_smul, add_smul, one_smul]
      abel
    rw [hAb, show (1 + 1 + 1 + 1 : ℝ) = 4 by norm_num]
  · have h1 : (⟨μ.val, by omega⟩ : Fin 8) ≠ ⟨ν.val, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; exact hμν (Fin.ext hv)
    have h2 : (⟨μ.val, by omega⟩ : Fin 8) ≠ ⟨ν.val + 4, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    have h3 : (⟨μ.val + 4, by omega⟩ : Fin 8) ≠ ⟨ν.val, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; omega
    have h4 : (⟨μ.val + 4, by omega⟩ : Fin 8) ≠ ⟨ν.val + 4, by omega⟩ := fun h => by
      have hv := congrArg Fin.val h; dsimp at hv; exact hμν (Fin.ext (by omega))
    simp only [hμν, ↓reduceIte, zero_smul, add_mul, mul_add, sub_mul, mul_sub]
    calc
      _ = (G ⟨μ.val, by omega⟩ * G ⟨ν.val, by omega⟩ +
            G ⟨ν.val, by omega⟩ * G ⟨μ.val, by omega⟩) -
          (G ⟨μ.val, by omega⟩ * G ⟨ν.val + 4, by omega⟩ +
            G ⟨ν.val + 4, by omega⟩ * G ⟨μ.val, by omega⟩) +
          (G ⟨μ.val + 4, by omega⟩ * G ⟨ν.val, by omega⟩ +
            G ⟨ν.val, by omega⟩ * G ⟨μ.val + 4, by omega⟩) -
          (G ⟨μ.val + 4, by omega⟩ * G ⟨ν.val + 4, by omega⟩ +
            G ⟨ν.val + 4, by omega⟩ * G ⟨μ.val + 4, by omega⟩) := by abel
      _ = 0 := by rw [hAnti _ _ h1, hAnti _ _ h2, hAnti _ _ h3, hAnti _ _ h4]; simp

/-- 4-mode Witt fermionic CAR relation: `{γ^μ, γ̃_ν} = (if μ = ν then 4 else 0) • I₁₆`. -/
theorem witt_CAR_relation (μ ν : Fin 4) :
    wittCreate μ * wittAnnihil ν + wittAnnihil ν * wittCreate μ =
      (if μ = ν then (4 : ℝ) else 0) • (1 : Matrix (Fin 8 ⊕ Fin 8) (Fin 8 ⊕ Fin 8) ℝ) :=
  witt_CAR_relation_abstract gammaMat cl44_anticommutator μ ν

private lemma bornInvolution_sq_abstract {B : Type*} [Ring B] [Algebra ℝ B]
    (G : Fin 8 → B)
    (hCliff : ∀ X Y : Fin 8, G X * G Y + G Y * G X = (2 * sig44 X Y) • (1 : B)) :
    (G 4 * G 5 * G 6 * G 7) * (G 4 * G 5 * G 6 * G 7) = 1 := by
  have hSq : ∀ X : Fin 8, G X * G X = (if X.val < 4 then (1 : ℝ) else -1) • (1 : B) := by
    intro X
    have h := hCliff X X
    simp only [sig44, ↓reduceIte, ← two_smul ℝ] at h
    have h2 := smul_right_injective B (by norm_num : (2 : ℝ) ≠ 0)
    rw [mul_smul] at h
    exact h2 h
  have hFlip : ∀ X Y : Fin 8, X ≠ Y → G X * G Y = -(G Y * G X) := fun X Y hne =>
    eq_neg_of_add_eq_zero_left (by simpa [sig44, hne] using hCliff X Y)
  have h4sq : G 4 * G 4 = -1 := by rw [hSq]; simp
  have h5sq : G 5 * G 5 = -1 := by rw [hSq]; simp
  have h6sq : G 6 * G 6 = -1 := by rw [hSq]; simp
  have h7sq : G 7 * G 7 = -1 := by rw [hSq]; simp
  have hPush4 : G 4 * G 5 * G 6 * G 7 * G 4 = G 5 * G 6 * G 7 := by
    calc
      G 4 * G 5 * G 6 * G 7 * G 4
          = G 4 * G 5 * G 6 * (G 7 * G 4) := by simp only [mul_assoc]
      _ = -(G 4 * G 5 * (G 6 * G 4) * G 7) := by
            rw [hFlip 7 4 (by decide)]; simp only [mul_neg, mul_assoc]
      _ = G 4 * (G 5 * G 4) * G 6 * G 7 := by
            rw [hFlip 6 4 (by decide)]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -((G 4 * G 4) * G 5 * G 6 * G 7) := by
            rw [hFlip 5 4 (by decide)]; simp only [mul_neg, neg_mul, mul_assoc]
      _ = G 5 * G 6 * G 7 := by rw [h4sq, neg_one_mul, neg_mul, neg_mul, neg_neg]
  have hPush5 : G 5 * G 6 * G 7 * G 5 = -(G 6 * G 7) := by
    calc
      G 5 * G 6 * G 7 * G 5
          = G 5 * G 6 * (G 7 * G 5) := by simp only [mul_assoc]
      _ = -(G 5 * (G 6 * G 5) * G 7) := by
            rw [hFlip 7 5 (by decide)]; simp only [mul_neg, mul_assoc]
      _ = (G 5 * G 5) * G 6 * G 7 := by
            rw [hFlip 6 5 (by decide)]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -(G 6 * G 7) := by rw [h5sq, neg_one_mul, neg_mul]
  have hPush6 : G 6 * G 7 * G 6 = G 7 := by
    rw [mul_assoc, hFlip 7 6 (by decide), mul_neg, ← mul_assoc, h6sq, neg_one_mul, neg_neg]
  calc
    G 4 * G 5 * G 6 * G 7 * (G 4 * G 5 * G 6 * G 7)
        = (G 4 * G 5 * G 6 * G 7 * G 4) * G 5 * G 6 * G 7 := by simp only [mul_assoc]
    _ = (G 5 * G 6 * G 7 * G 5) * G 6 * G 7 := by rw [hPush4]
    _ = -((G 6 * G 7 * G 6) * G 7) := by rw [hPush5, neg_mul, neg_mul]
    _ = -(G 7 * G 7) := by rw [hPush6]
    _ = 1 := by rw [h7sq, neg_neg]

/-- Born reciprocity involution squares to the identity: `B_Born² = I₁₆`. -/
theorem bornInvolution_sq : bornInvolution * bornInvolution = 1 :=
  bornInvolution_sq_abstract gammaMat cl44_anticommutator

private lemma bornInvolution_comm_pos_abstract {B : Type*} [Ring B] [Algebra ℝ B]
    (G : Fin 8 → B)
    (hCliff : ∀ X Y : Fin 8, G X * G Y + G Y * G X = (2 * sig44 X Y) • (1 : B))
    (μ : Fin 4) :
    (G 4 * G 5 * G 6 * G 7) * G ⟨μ.val, by omega⟩ =
      G ⟨μ.val, by omega⟩ * (G 4 * G 5 * G 6 * G 7) := by
  have hFlip : ∀ X Y : Fin 8, X ≠ Y → G X * G Y = -(G Y * G X) := fun X Y hne =>
    eq_neg_of_add_eq_zero_left (by simpa [sig44, hne] using hCliff X Y)
  have h4 : (⟨μ.val, by omega⟩ : Fin 8) ≠ 4 := fun h => by
    have hv := congrArg Fin.val h; dsimp at hv; omega
  have h5 : (⟨μ.val, by omega⟩ : Fin 8) ≠ 5 := fun h => by
    have hv := congrArg Fin.val h; dsimp at hv; omega
  have h6 : (⟨μ.val, by omega⟩ : Fin 8) ≠ 6 := fun h => by
    have hv := congrArg Fin.val h; dsimp at hv; omega
  have h7 : (⟨μ.val, by omega⟩ : Fin 8) ≠ 7 := fun h => by
    have hv := congrArg Fin.val h; dsimp at hv; omega
  rw [mul_assoc _ (G 7), hFlip 7 _ h7.symm]
  simp only [mul_neg, mul_assoc]
  rw [← mul_assoc (G 6), hFlip 6 _ h6.symm]
  simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
  rw [← mul_assoc (G 5), hFlip 5 _ h5.symm]
  simp only [neg_mul, mul_neg, mul_assoc]
  rw [← mul_assoc (G 4), hFlip 4 _ h4.symm]
  simp only [neg_mul, neg_neg, mul_assoc]

private lemma bornInvolution_anticomm_neg_abstract {B : Type*} [Ring B] [Algebra ℝ B]
    (G : Fin 8 → B)
    (hCliff : ∀ X Y : Fin 8, G X * G Y + G Y * G X = (2 * sig44 X Y) • (1 : B))
    (μ : Fin 4) :
    (G 4 * G 5 * G 6 * G 7) * G ⟨μ.val + 4, by omega⟩ =
      -(G ⟨μ.val + 4, by omega⟩ * (G 4 * G 5 * G 6 * G 7)) := by
  have hFlip : ∀ X Y : Fin 8, X ≠ Y → G X * G Y = -(G Y * G X) := fun X Y hne =>
    eq_neg_of_add_eq_zero_left (by simpa [sig44, hne] using hCliff X Y)
  fin_cases μ
  · change G 4 * G 5 * G 6 * G 7 * G 4 = -(G 4 * (G 4 * G 5 * G 6 * G 7))
    rw [mul_assoc _ (G 7), hFlip 7 4 (by decide), mul_neg]
    rw [← mul_assoc _ (G 4) (G 7), mul_assoc (G 4 * G 5) (G 6) (G 4),
      hFlip 6 4 (by decide), mul_neg, neg_mul, neg_neg]
    rw [← mul_assoc (G 4 * G 5) (G 4) (G 6), mul_assoc (G 4) (G 5) (G 4),
      hFlip 5 4 (by decide), mul_neg, neg_mul, neg_mul]
    rw [mul_assoc (G 4) (G 4 * G 5) (G 6), mul_assoc (G 4) ((G 4 * G 5) * G 6) (G 7)]
  · change G 4 * G 5 * G 6 * G 7 * G 5 = -(G 5 * (G 4 * G 5 * G 6 * G 7))
    have h455 : G 4 * G 5 * G 5 = -(G 5 * G 4 * G 5) := by
      rw [hFlip 4 5 (by decide), neg_mul]
    rw [mul_assoc _ (G 7), hFlip 7 5 (by decide), mul_neg]
    rw [← mul_assoc _ (G 5) (G 7), mul_assoc (G 4 * G 5) (G 6) (G 5),
      hFlip 6 5 (by decide), mul_neg, neg_mul, neg_neg]
    rw [← mul_assoc (G 4 * G 5) (G 5) (G 6), h455, neg_mul, neg_mul]
    rw [mul_assoc (G 5) (G 4) (G 5), mul_assoc (G 5) (G 4 * G 5) (G 6),
      mul_assoc (G 5) ((G 4 * G 5) * G 6) (G 7)]
  · change G 4 * G 5 * G 6 * G 7 * G 6 = -(G 6 * (G 4 * G 5 * G 6 * G 7))
    calc
      G 4 * G 5 * G 6 * G 7 * G 6
          = G 4 * G 5 * G 6 * (G 7 * G 6) := by simp only [mul_assoc]
      _ = -(G 4 * (G 5 * G 6) * G 6 * G 7) := by
            rw [hFlip 7 6 (by decide)]; simp only [mul_neg, mul_assoc]
      _ = (G 4 * G 6) * G 5 * G 6 * G 7 := by
            rw [hFlip 5 6 (by decide)]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -(G 6 * (G 4 * G 5 * G 6 * G 7)) := by
            rw [hFlip 4 6 (by decide)]; simp only [neg_mul, mul_assoc]
  · change G 4 * G 5 * G 6 * G 7 * G 7 = -(G 7 * (G 4 * G 5 * G 6 * G 7))
    calc
      G 4 * G 5 * G 6 * G 7 * G 7
          = G 4 * G 5 * (G 6 * G 7) * G 7 := by simp only [mul_assoc]
      _ = -(G 4 * (G 5 * G 7) * G 6 * G 7) := by
            rw [hFlip 6 7 (by decide)]; simp only [neg_mul, mul_neg, mul_assoc]
      _ = (G 4 * G 7) * G 5 * G 6 * G 7 := by
            rw [hFlip 5 7 (by decide)]; simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
      _ = -(G 7 * (G 4 * G 5 * G 6 * G 7)) := by
            rw [hFlip 4 7 (by decide)]; simp only [neg_mul, mul_assoc]

private lemma bornInvolution_conj_create_abstract {B : Type*} [Ring B] [Algebra ℝ B]
    (G : Fin 8 → B)
    (hCliff : ∀ X Y : Fin 8, G X * G Y + G Y * G X = (2 * sig44 X Y) • (1 : B))
    (μ : Fin 4) :
    (G 4 * G 5 * G 6 * G 7) * (G ⟨μ.val, by omega⟩ + G ⟨μ.val + 4, by omega⟩) *
        (G 4 * G 5 * G 6 * G 7) =
      G ⟨μ.val, by omega⟩ - G ⟨μ.val + 4, by omega⟩ := by
  have hSq := bornInvolution_sq_abstract G hCliff
  rw [mul_add, add_mul,
    bornInvolution_comm_pos_abstract G hCliff μ,
    bornInvolution_anticomm_neg_abstract G hCliff μ,
    neg_mul,
    mul_assoc (G ⟨μ.val, by omega⟩),
    mul_assoc (G ⟨μ.val + 4, by omega⟩),
    hSq, mul_one, mul_one, ← sub_eq_add_neg]

/-- Born reciprocity conjugates Witt creation into Witt annihilation: `B_Born γ^μ B_Born = γ̃_μ`. -/
theorem bornInvolution_conj_create (μ : Fin 4) :
    bornInvolution * wittCreate μ * bornInvolution = wittAnnihil μ :=
  bornInvolution_conj_create_abstract gammaMat cl44_anticommutator μ

private lemma bornInvolution_conj_annihil_abstract {B : Type*} [Ring B] [Algebra ℝ B]
    (G : Fin 8 → B)
    (hCliff : ∀ X Y : Fin 8, G X * G Y + G Y * G X = (2 * sig44 X Y) • (1 : B))
    (μ : Fin 4) :
    (G 4 * G 5 * G 6 * G 7) * (G ⟨μ.val, by omega⟩ - G ⟨μ.val + 4, by omega⟩) *
        (G 4 * G 5 * G 6 * G 7) =
      G ⟨μ.val, by omega⟩ + G ⟨μ.val + 4, by omega⟩ := by
  have hSq := bornInvolution_sq_abstract G hCliff
  rw [mul_sub, sub_mul,
    bornInvolution_comm_pos_abstract G hCliff μ,
    bornInvolution_anticomm_neg_abstract G hCliff μ,
    neg_mul,
    mul_assoc (G ⟨μ.val, by omega⟩),
    mul_assoc (G ⟨μ.val + 4, by omega⟩),
    hSq, mul_one, mul_one, sub_neg_eq_add]

/-- Born reciprocity conjugates Witt annihilation into Witt creation: `B_Born γ̃_μ B_Born = γ^μ`. -/
theorem bornInvolution_conj_annihil (μ : Fin 4) :
    bornInvolution * wittAnnihil μ * bornInvolution = wittCreate μ :=
  bornInvolution_conj_annihil_abstract gammaMat cl44_anticommutator μ

private lemma leftMulMatGen_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x : Fin 8 → R) :
    leftMulMatGen (fun i => f (x i)) = (leftMulMatGen x).map f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMulMatGen]

private lemma leftMulMat_eq_map_leftMulInt (k : Fin 8) :
    leftMulMat (Pi.single k 1) = (leftMulInt k).map (Int.castRingHom ℝ) := by
  rw [leftMulMat, leftMulInt, ← leftMulMatGen_map]
  congr 1
  ext i
  simp [Pi.single_apply, apply_ite]

private lemma leftMulMat_neg (x : OctS) : leftMulMat (-x) = -(leftMulMat x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMulMat, leftMulMatGen]

private lemma octConj_single_ne_zero {k : Fin 8} (hk : k ≠ 0) :
    octConj (Pi.single k (1 : ℝ)) = -(Pi.single k 1) := by
  ext i
  fin_cases k
  · exact absurd rfl hk
  all_goals { fin_cases i <;> simp [octConj] }

private lemma leftMulInt_prod_neg_one :
    leftMulInt 1 * leftMulInt 2 * leftMulInt 3 * leftMulInt 4 *
      leftMulInt 5 * leftMulInt 6 * leftMulInt 7 = -1 := by
  decide

private lemma blocks_prod8_formula
    (U₀ U₁ U₂ U₃ U₄ U₅ U₆ U₇ : Matrix (Fin 8) (Fin 8) ℝ)
    (hU0 : U₀ = 1) (hProd : U₁ * U₂ * U₃ * U₄ * U₅ * U₆ * U₇ = -1) :
    Matrix.fromBlocks (0 : Matrix (Fin 8) (Fin 8) ℝ) U₀ U₀ 0 *
      Matrix.fromBlocks 0 U₁ (-U₁) 0 *
      Matrix.fromBlocks 0 U₂ (-U₂) 0 * Matrix.fromBlocks 0 U₃ (-U₃) 0 *
      Matrix.fromBlocks 0 U₄ (-U₄) 0 * Matrix.fromBlocks 0 U₅ (-U₅) 0 *
      Matrix.fromBlocks 0 U₆ (-U₆) 0 * Matrix.fromBlocks 0 U₇ (-U₇) 0 =
      Matrix.fromBlocks (-1 : Matrix (Fin 8) (Fin 8) ℝ) 0 0 1 := by
  subst hU0
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_neg]
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, neg_mul]
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, mul_neg]
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, neg_mul]
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, mul_neg]
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, neg_mul]
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, zero_add, add_zero, mul_neg, neg_mul, neg_neg, Matrix.mul_assoc]
  have hProdR : U₁ * (U₂ * (U₃ * (U₄ * (U₅ * (U₆ * U₇))))) = -1 := by
    simpa [Matrix.mul_assoc] using hProd
  rw [hProdR, neg_neg]

/-- The `Cl(4,4)` chiral volume element `ω_{4,4} = Γ₀⋯Γ₇` equals `diag(-I₈, I₈)`. -/
theorem volumeCl44_eq_chiral_diag :
    volumeCl44 = Matrix.fromBlocks (-1 : Matrix (Fin 8) (Fin 8) ℝ) 0 0 1 := by
  have hProd7Real :
      leftMulMat (Pi.single 1 1) * leftMulMat (Pi.single 2 1) * leftMulMat (Pi.single 3 1) *
        leftMulMat (Pi.single 4 1) * leftMulMat (Pi.single 5 1) * leftMulMat (Pi.single 6 1) *
        leftMulMat (Pi.single 7 1) = -(1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [leftMulMat_eq_map_leftMulInt 1, leftMulMat_eq_map_leftMulInt 2,
      leftMulMat_eq_map_leftMulInt 3, leftMulMat_eq_map_leftMulInt 4,
      leftMulMat_eq_map_leftMulInt 5, leftMulMat_eq_map_leftMulInt 6,
      leftMulMat_eq_map_leftMulInt 7]
    simp only [← Matrix.map_mul, leftMulInt_prod_neg_one]
    ext i j
    by_cases h : i = j <;> simp [h]
  have hConjSingle : ∀ {k : Fin 8}, k ≠ 0 →
      leftMulMat (octConj (Pi.single k 1)) = -(leftMulMat (Pi.single k 1)) := by
    intro k hk
    rw [octConj_single_ne_zero hk, leftMulMat_neg]
  have hL0 : leftMulMat (Pi.single 0 1) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [leftMulMat, leftMulMatGen]
  have hConj0 : octConj (Pi.single 0 1) = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [octConj]
  unfold volumeCl44 gammaMat
  rw [hConj0, hConjSingle (by decide), hConjSingle (by decide), hConjSingle (by decide),
    hConjSingle (by decide), hConjSingle (by decide), hConjSingle (by decide),
    hConjSingle (by decide)]
  exact blocks_prod8_formula
    (leftMulMat (Pi.single 0 1)) (leftMulMat (Pi.single 1 1))
    (leftMulMat (Pi.single 2 1)) (leftMulMat (Pi.single 3 1))
    (leftMulMat (Pi.single 4 1)) (leftMulMat (Pi.single 5 1))
    (leftMulMat (Pi.single 6 1)) (leftMulMat (Pi.single 7 1))
    hL0 hProd7Real

/-- The chiral volume element squares to the identity: `ω_{4,4}² = I₁₆`. -/
theorem volumeCl44_sq : volumeCl44 * volumeCl44 = 1 := by
  rw [volumeCl44_eq_chiral_diag, Matrix.fromBlocks_multiply]
  simp only [one_mul, zero_mul, mul_zero, neg_mul, mul_neg, neg_neg, add_zero, zero_add]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

/-- The chiral volume element anticommutes with all eight generators `Γ_A`. -/
theorem volumeCl44_anticomm_gamma (A : Fin 8) :
    volumeCl44 * gammaMat A + gammaMat A * volumeCl44 = 0 := by
  rw [volumeCl44_eq_chiral_diag]
  unfold gammaMat
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp only [one_mul, mul_one, zero_mul, mul_zero, neg_mul, mul_neg, zero_add, add_zero]
  ext (i | i) (j | j) <;> simp

end InfoGeometry.Canonical.KleinianWittBornNullIncidence
