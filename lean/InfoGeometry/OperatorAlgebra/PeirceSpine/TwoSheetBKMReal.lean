/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetBKM
import InfoGeometry.NCG.OppositePeirceRealMetric
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FinCases

/-!
# Real-API two-sheet BKM bridge and finite-trace vs Type III separation

This module lifts the complex-matrix two-sheet Bogoliubov–Kubo–Mori (BKM)
resolvent integral theorems of `TwoSheetBKM` to the real full matrix algebra
`Matrix ι ι ℝ` via entrywise complexification `Matrix.map · Complex.ofReal`.

Key components:
1. `RealTwoSheetBKMContext`: a `Type`-valued higher-grade context bundling
   an orthogonal real projection `P`, positive sheet weights `p, q > 0`, and
   a real symmetric Peirce-odd perturbation `Φ` (with constructors both for
   coupled Peirce corners `component10 P A + component01 P Aᵀ` and for
   odd anticommuting inputs `P * Φ + Φ * P = Φ`), without bundling conclusions
   as structure fields.
2. Real-API BKM lifting theorems: `real_twoSheetResolvent_trace_left`,
   `real_twoSheetResolvent_quadratic_trace`,
   `real_twoSheetResolvent_quadratic_nonneg`, and
   `real_twoSheetResolvent_quadratic_pos`, together with `IntegrableOn` and
   `ContinuousLinearMap.integral_comp_comm` (`Complex.ofRealCLM` /
   `Complex.reCLM`) compatibility and an equivalence to
   `OppositePeirceRealMetric.trace_square_pos_iff`.
3. `FiniteTraceBKMVsTypeIIISeparation`: a `Type`-valued separation structure
   contrasting the finite-dimensional faithful-trace Dedekind-finite real BKM
   regime on `Matrix ι ι ℝ` (even when the density `twoSheetReal P p q` has
   `p ≠ q` and defines a non-tracial weighted functional) against infinite /
   Type-III-halving algebras admitting proper one-sided isometries and
   whole-projection halving `1 ~ P`, `1 ~ 1 - P` (instantiated concretely on
   `Matrix (Fin 2) (Fin 2) ℝ` vs `Module.End ℝ (ℕ → ℝ)`).
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetBKMReal

open MeasureTheory Set InfoGeometry.Analysis InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Core.PeirceDecomposition (component10 component01 peirce_decomposition)
open scoped Matrix Matrix.Norms.L2Operator

/-! ## Real Two-Sheet Operators, Resolvent, and Complexification -/

section BasicComplexification

variable {ι : Type*}

theorem complexify_eq_mapHom (A : Matrix ι ι ℝ) :
    A.map Complex.ofReal = A.map Complex.ofRealHom := rfl

theorem complexify_one [DecidableEq ι] :
    (1 : Matrix ι ι ℝ).map Complex.ofReal = (1 : Matrix ι ι ℂ) :=
  Matrix.map_one Complex.ofReal Complex.ofReal_zero Complex.ofReal_one

theorem complexify_zero :
    (0 : Matrix ι ι ℝ).map Complex.ofReal = (0 : Matrix ι ι ℂ) :=
  Matrix.map_zero Complex.ofReal Complex.ofReal_zero

theorem complexify_add (A B : Matrix ι ι ℝ) :
    (A + B).map Complex.ofReal = A.map Complex.ofReal + B.map Complex.ofReal :=
  Matrix.map_add Complex.ofReal Complex.ofReal_add A B

theorem complexify_sub (A B : Matrix ι ι ℝ) :
    (A - B).map Complex.ofReal = A.map Complex.ofReal - B.map Complex.ofReal :=
  Matrix.map_sub Complex.ofReal Complex.ofReal_sub A B

theorem complexify_mul [Fintype ι] (A B : Matrix ι ι ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

theorem complexify_smul (r : ℝ) (A : Matrix ι ι ℝ) :
    (r • A).map Complex.ofReal = r • (A.map Complex.ofReal) := by
  ext i j
  simp [Complex.real_smul]

theorem complexify_transpose (A : Matrix ι ι ℝ) :
    Aᵀ.map Complex.ofReal = (A.map Complex.ofReal)ᵀ :=
  Matrix.transpose_map

theorem complexify_trace [Fintype ι] (A : Matrix ι ι ℝ) :
    Matrix.trace (A.map Complex.ofReal) = Complex.ofReal (Matrix.trace A) := by
  simp [Matrix.trace]

theorem complexify_trace_re [Fintype ι] (A : Matrix ι ι ℝ) :
    (Matrix.trace (A.map Complex.ofReal)).re = Matrix.trace A := by
  rw [complexify_trace, Complex.ofReal_re]

theorem complexify_idempotent [Fintype ι] {P : Matrix ι ι ℝ} (hP : P * P = P) :
    P.map Complex.ofReal * P.map Complex.ofReal = P.map Complex.ofReal := by
  rw [← complexify_mul, hP]

theorem complexify_isHermitian_iff (A : Matrix ι ι ℝ) :
    (A.map Complex.ofReal).IsHermitian ↔ Aᵀ = A := by
  rw [Matrix.isHermitian_map_iff (fun x => (Complex.conj_ofReal x).symm)
    Complex.ofReal_injective, Matrix.isHermitian_iff_isSymm]
  rfl

theorem complexify_injective :
    Function.Injective (fun A : Matrix ι ι ℝ => A.map Complex.ofReal) :=
  Matrix.map_injective Complex.ofReal_injective

end BasicComplexification

section Complexification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Two-sheet positive operator `p • P + q • (1 - P)` on `Matrix ι ι ℝ`. -/
def twoSheetReal (P : Matrix ι ι ℝ) (p q : ℝ) : Matrix ι ι ℝ :=
  twoSheet P p q

/-- Native real matrix resolvent `(twoSheetReal P p q + s • 1)⁻¹`. -/
def twoSheetResolventReal (P : Matrix ι ι ℝ) (p q s : ℝ) : Matrix ι ι ℝ :=
  (twoSheetReal P p q + s • (1 : Matrix ι ι ℝ))⁻¹

/-- Real resolvent BKM pairing on `Matrix ι ι ℝ` (matching `bkmResolventPairing`). -/
def realBKMResolventPairing (P : Matrix ι ι ℝ) (p q : ℝ)
    (X Y : Matrix ι ι ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ),
    Matrix.trace (Xᵀ * twoSheetResolventReal P p q s * Y * twoSheetResolventReal P p q s)

theorem complexify_inv (A : Matrix ι ι ℝ) :
    (A⁻¹).map Complex.ofReal = (A.map Complex.ofReal)⁻¹ := by
  have hsmul : ∀ (r : ℝ) (M : Matrix ι ι ℂ), r • M = (r : ℂ) • M := by
    intro r M
    ext i j
    simp [Complex.real_smul]
  rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv,
    complexify_smul, hsmul, Complex.ofReal_inv]
  have hdet : (A.map Complex.ofReal).det = (A.det : ℂ) := by
    simpa [complexify_eq_mapHom] using (RingHom.map_det Complex.ofRealHom A).symm
  have hadj : (A.map Complex.ofReal).adjugate = A.adjugate.map Complex.ofReal := by
    simpa [complexify_eq_mapHom] using (RingHom.map_adjugate Complex.ofRealHom A).symm
  rw [hdet, hadj]

theorem complexify_genPhi (P A C : Matrix ι ι ℝ) :
    (genPhi P A C).map Complex.ofReal =
      genPhi (P.map Complex.ofReal) (A.map Complex.ofReal) (C.map Complex.ofReal) := by
  simp only [genPhi, conePlus, coneMinus, complexify_add, complexify_mul,
    complexify_sub, complexify_one]

theorem complexify_genV (P A C : Matrix ι ι ℝ) :
    (genV P A C).map Complex.ofReal =
      genV (P.map Complex.ofReal) (A.map Complex.ofReal) (C.map Complex.ofReal) := by
  simp only [genV, anticomm, conePlus, coneMinus, complexify_add, complexify_mul,
    complexify_sub, complexify_one]

theorem twoSheetReal_complexify (P : Matrix ι ι ℝ) (p q : ℝ) :
    (twoSheetReal P p q).map Complex.ofReal = twoSheet (P.map Complex.ofReal) p q := by
  simp only [twoSheetReal, twoSheet, complexify_add, complexify_smul,
    complexify_sub, complexify_one]

theorem matrix_twoSheetReal_inv (P : Matrix ι ι ℝ) (hP : P * P = P)
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (twoSheetReal P a b)⁻¹ = twoSheetReal P a⁻¹ b⁻¹ := by
  unfold twoSheetReal
  apply Matrix.inv_eq_right_inv
  rw [twoSheet_mul P hP, mul_inv_cancel₀ ha, mul_inv_cancel₀ hb,
    twoSheet_equal, one_smul]

theorem twoSheetResolventReal_eq (P : Matrix ι ι ℝ) (hP : P * P = P)
    {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    twoSheetResolventReal P p q s = twoSheetReal P (p + s)⁻¹ (q + s)⁻¹ := by
  unfold twoSheetResolventReal twoSheetReal
  rw [twoSheet_add_smul_one]
  exact matrix_twoSheetReal_inv P hP
    (add_pos_of_pos_of_nonneg hp hs).ne'
    (add_pos_of_pos_of_nonneg hq hs).ne'

theorem twoSheetResolventReal_complexify (P : Matrix ι ι ℝ) (p q s : ℝ) :
    (twoSheetResolventReal P p q s).map Complex.ofReal =
      twoSheetResolvent (P.map Complex.ofReal) p q s := by
  unfold twoSheetResolventReal twoSheetResolvent
  rw [complexify_inv, complexify_add, twoSheetReal_complexify, complexify_smul,
    complexify_one]

theorem eq_genPhi_of_diag_zero (P Φ : Matrix ι ι ℝ)
    (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0) :
    Φ = genPhi P Φ Φ := by
  have hdec := peirce_decomposition P Φ
  have h11 : InfoGeometry.Core.PeirceDecomposition.component11 P Φ = 0 := hΦ11
  have h00 : InfoGeometry.Core.PeirceDecomposition.component00 P Φ = 0 := hΦ00
  have h10 : component10 P Φ = conePlus P Φ := rfl
  have h01 : component01 P Φ = coneMinus P Φ := rfl
  rw [h11, h00, h10, h01, zero_add, add_zero] at hdec
  simpa only [genPhi] using hdec

theorem eq_coupledCorner_of_diag_zero_of_symm (P Φ : Matrix ι ι ℝ)
    (hΦT : Φᵀ = Φ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0) :
    Φ = component10 P Φ + component01 P Φᵀ := by
  rw [hΦT]
  exact eq_genPhi_of_diag_zero P Φ hΦ11 hΦ00

end Complexification

/-! ## `RealTwoSheetBKMContext` Structure and Constructors -/

/-- Explicit higher-grade context for the real-matrix two-sheet BKM metric.
All BKM integral identities, positive definiteness of the two-sheet density,
and quadratic positivity theorems are proved over this context rather than
assumed as structure fields. -/
structure RealTwoSheetBKMContext (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- Orthogonal projection defining the two-sheet cut. -/
  P : Matrix ι ι ℝ
  /-- Idempotency of `P`. -/
  P_idempotent : P * P = P
  /-- Real symmetry (self-adjointness) of `P`. -/
  P_symm : Pᵀ = P
  /-- Strictly positive weight on the `P` sheet. -/
  p : ℝ
  /-- Strictly positive weight on the `1 - P` sheet. -/
  q : ℝ
  /-- Positivity of `p`. -/
  p_pos : 0 < p
  /-- Positivity of `q`. -/
  q_pos : 0 < q
  /-- Real symmetric Peirce-odd perturbation `Φ`. -/
  Φ : Matrix ι ι ℝ
  /-- Real symmetry of `Φ`. -/
  Φ_symm : Φᵀ = Φ
  /-- Vanishing `11`-block `P * Φ * P = 0`. -/
  P_mul_Φ_mul_P : P * Φ * P = 0
  /-- Vanishing `00`-block `(1 - P) * Φ * (1 - P) = 0`. -/
  one_sub_P_mul_Φ_mul_one_sub_P : (1 - P) * Φ * (1 - P) = 0

namespace RealTwoSheetBKMContext

section ContextHelpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Construct a `RealTwoSheetBKMContext` from an arbitrary matrix `A` via the
symmetric coupled Peirce corner `component10 P A + component01 P Aᵀ`. -/
def ofCoupledCorner (P : Matrix ι ι ℝ) (hP : P * P = P) (hPT : Pᵀ = P)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (A : Matrix ι ι ℝ) :
    RealTwoSheetBKMContext ι where
  P := P
  P_idempotent := hP
  P_symm := hPT
  p := p
  q := q
  p_pos := hp
  q_pos := hq
  Φ := component10 P A + component01 P Aᵀ
  Φ_symm := by
    have hPs : P.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hPT
    have hHerm : (component10 P A + component01 P Aᴴ).IsHermitian :=
      InfoGeometry.NCG.OppositePeirceTrace.adjoint_sum_isHermitian hPs A
    exact hHerm.eq
  P_mul_Φ_mul_P := by
    change P * (conePlus P A + coneMinus P Aᵀ) * P = 0
    peirce_nf hP
  one_sub_P_mul_Φ_mul_one_sub_P := by
    change (1 - P) * (conePlus P A + coneMinus P Aᵀ) * (1 - P) = 0
    peirce_nf hP

/-- Construct a `RealTwoSheetBKMContext` from an odd anticommuting symmetric
matrix `Φ` satisfying `P * Φ + Φ * P = Φ`. -/
def ofOddAnticomm (P : Matrix ι ι ℝ) (hP : P * P = P) (hPT : Pᵀ = P)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (Φ : Matrix ι ι ℝ) (hΦT : Φᵀ = Φ) (hOdd : P * Φ + Φ * P = Φ) :
    RealTwoSheetBKMContext ι where
  P := P
  P_idempotent := hP
  P_symm := hPT
  p := p
  q := q
  p_pos := hp
  q_pos := hq
  Φ := Φ
  Φ_symm := hΦT
  P_mul_Φ_mul_P := by
    have hdouble : 0 + P * Φ * P = P * Φ * P + P * Φ * P := by
      rw [zero_add]
      calc P * Φ * P = P * (P * Φ + Φ * P) * P := by rw [hOdd]
        _ = (P * P) * Φ * P + P * Φ * (P * P) := by noncomm_ring
        _ = P * Φ * P + P * Φ * P := by rw [hP]
    exact (add_right_cancel hdouble).symm
  one_sub_P_mul_Φ_mul_one_sub_P := by
    have h10 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
    have h01 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
    calc (1 - P) * Φ * (1 - P)
        = (1 - P) * (P * Φ + Φ * P) * (1 - P) := by rw [hOdd]
      _ = ((1 - P) * P) * Φ * (1 - P) + (1 - P) * Φ * (P * (1 - P)) := by noncomm_ring
      _ = 0 := by rw [h01, h10]; simp

/-- The two-sheet positive density operator `twoSheetReal ctx.P ctx.p ctx.q`. -/
def density (ctx : RealTwoSheetBKMContext ι) : Matrix ι ι ℝ :=
  twoSheetReal ctx.P ctx.p ctx.q

/-- The real resolvent `(ctx.density + s • 1)⁻¹`. -/
def resolvent (ctx : RealTwoSheetBKMContext ι) (s : ℝ) : Matrix ι ι ℝ :=
  twoSheetResolventReal ctx.P ctx.p ctx.q s

/-- The real BKM resolvent pairing induced by `ctx`. -/
def bkmPairing (ctx : RealTwoSheetBKMContext ι) (X Y : Matrix ι ι ℝ) : ℝ :=
  realBKMResolventPairing ctx.P ctx.p ctx.q X Y

theorem P_isIdempotentElem (ctx : RealTwoSheetBKMContext ι) :
    IsIdempotentElem ctx.P :=
  ctx.P_idempotent

theorem P_isHermitian (ctx : RealTwoSheetBKMContext ι) :
    ctx.P.IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr ctx.P_symm

theorem Φ_eq_genPhi (ctx : RealTwoSheetBKMContext ι) :
    ctx.Φ = genPhi ctx.P ctx.Φ ctx.Φ :=
  eq_genPhi_of_diag_zero ctx.P ctx.Φ ctx.P_mul_Φ_mul_P ctx.one_sub_P_mul_Φ_mul_one_sub_P

theorem Φ_sq_eq_genV (ctx : RealTwoSheetBKMContext ι) :
    ctx.Φ * ctx.Φ = genV ctx.P ctx.Φ ctx.Φ := by
  conv_lhs => rw [ctx.Φ_eq_genPhi]
  exact (archetype_A3_nilpotent_cones_and_tetraktys_table ctx.P_idempotent ctx.Φ ctx.Φ).2.2.1

/-- Positive definiteness of the two-sheet density operator `twoSheetReal ctx.P ctx.p ctx.q`,
proved from `P * P = P`, `Pᵀ = P`, `0 < p`, `0 < q`. -/
theorem twoSheetReal_posDef (ctx : RealTwoSheetBKMContext ι) :
    (twoSheetReal ctx.P ctx.p ctx.q).PosDef := by
  have hHerm : (twoSheetReal ctx.P ctx.p ctx.q).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    change (twoSheetReal ctx.P ctx.p ctx.q)ᵀ = twoSheetReal ctx.P ctx.p ctx.q
    simp only [twoSheetReal, twoSheet, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_sub, Matrix.transpose_one, ctx.P_symm]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  let u : ι → ℝ := ctx.P *ᵥ x
  let v : ι → ℝ := (1 - ctx.P) *ᵥ x
  have hdecomp : u + v = x := by
    dsimp [u, v]
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hu_dot : x ⬝ᵥ u = u ⬝ᵥ u := by
    dsimp [u]
    calc x ⬝ᵥ (ctx.P *ᵥ x) = x ⬝ᵥ ((ctx.P * ctx.P) *ᵥ x) := by rw [ctx.P_idempotent]
      _ = x ⬝ᵥ (ctx.P *ᵥ (ctx.P *ᵥ x)) := by rw [Matrix.mulVec_mulVec]
      _ = (x ᵥ* ctx.P) ⬝ᵥ (ctx.P *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
      _ = (ctx.Pᵀ *ᵥ x) ⬝ᵥ (ctx.P *ᵥ x) := by rw [Matrix.mulVec_transpose]
      _ = (ctx.P *ᵥ x) ⬝ᵥ (ctx.P *ᵥ x) := by rw [ctx.P_symm]
  have hv_symm : (1 - ctx.P)ᵀ = 1 - ctx.P := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, ctx.P_symm]
  have hv_idem : (1 - ctx.P) * (1 - ctx.P) = 1 - ctx.P := by
    calc (1 - ctx.P) * (1 - ctx.P) = 1 - ctx.P - ctx.P + ctx.P * ctx.P := by noncomm_ring
      _ = 1 - ctx.P := by rw [ctx.P_idempotent]; noncomm_ring
  have hv_dot : x ⬝ᵥ v = v ⬝ᵥ v := by
    dsimp [v]
    calc x ⬝ᵥ ((1 - ctx.P) *ᵥ x)
        = x ⬝ᵥ (((1 - ctx.P) * (1 - ctx.P)) *ᵥ x) := by rw [hv_idem]
      _ = x ⬝ᵥ ((1 - ctx.P) *ᵥ ((1 - ctx.P) *ᵥ x)) := by rw [Matrix.mulVec_mulVec]
      _ = (x ᵥ* (1 - ctx.P)) ⬝ᵥ ((1 - ctx.P) *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
      _ = ((1 - ctx.P)ᵀ *ᵥ x) ⬝ᵥ ((1 - ctx.P) *ᵥ x) := by rw [Matrix.mulVec_transpose]
      _ = ((1 - ctx.P) *ᵥ x) ⬝ᵥ ((1 - ctx.P) *ᵥ x) := by rw [hv_symm]
  have hquad : star x ⬝ᵥ (twoSheetReal ctx.P ctx.p ctx.q *ᵥ x) =
      ctx.p * (u ⬝ᵥ u) + ctx.q * (v ⬝ᵥ v) := by
    simp only [star_trivial, twoSheetReal, twoSheet, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    change ctx.p * (x ⬝ᵥ u) + ctx.q * (x ⬝ᵥ v) = ctx.p * (u ⬝ᵥ u) + ctx.q * (v ⬝ᵥ v)
    rw [hu_dot, hv_dot]
  rw [hquad]
  have dot_nonneg : ∀ y : ι → ℝ, 0 ≤ y ⬝ᵥ y := fun y =>
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (y i))
  have dot_eq_zero : ∀ y : ι → ℝ, y ⬝ᵥ y = 0 → y = 0 := by
    intro y hy
    have hsum := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (y i))).mp hy
    ext i
    exact mul_self_eq_zero.mp (hsum i (Finset.mem_univ i))
  have hu_nn : 0 ≤ u ⬝ᵥ u := dot_nonneg u
  have hv_nn : 0 ≤ v ⬝ᵥ v := dot_nonneg v
  have huv_ne : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    rw [← hdecomp, h.1, h.2, add_zero]
  rcases huv_ne with hu_ne | hv_ne
  · have hu_pos : 0 < u ⬝ᵥ u := lt_of_le_of_ne hu_nn (Ne.symm (mt (dot_eq_zero u) hu_ne))
    exact add_pos_of_pos_of_nonneg (mul_pos ctx.p_pos hu_pos) (mul_nonneg ctx.q_pos.le hv_nn)
  · have hv_pos : 0 < v ⬝ᵥ v := lt_of_le_of_ne hv_nn (Ne.symm (mt (dot_eq_zero v) hv_ne))
    exact add_pos_of_nonneg_of_pos (mul_nonneg ctx.p_pos.le hu_nn) (mul_pos ctx.q_pos hv_pos)

end ContextHelpers

end RealTwoSheetBKMContext

/-! ## Real-API BKM Resolvent Integrals (Lifted from `TwoSheetBKM`) -/

section RealBKMLifting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise operator-level real resolvent identity with arbitrary left probe `X`. -/
theorem real_twoSheetResolvent_left_product
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ X : Matrix ι ι ℝ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    X * twoSheetResolventReal P p q s * Φ * twoSheetResolventReal P p q s =
      (1 / ((p + s) * (q + s))) • (X * Φ) := by
  apply complexify_injective
  dsimp only
  have hΦeq : Φ = genPhi P Φ Φ := eq_genPhi_of_diag_zero P Φ hΦ11 hΦ00
  rw [complexify_mul, complexify_mul, complexify_mul, twoSheetResolventReal_complexify,
    complexify_smul, complexify_mul]
  conv_lhs =>
    arg 1; arg 2
    rw [hΦeq, complexify_genPhi]
  conv_rhs =>
    arg 2; arg 2
    rw [hΦeq, complexify_genPhi]
  exact InfoGeometry.OperatorAlgebra.PeirceSpine.twoSheetResolvent_left_product
    (P.map Complex.ofReal) (complexify_idempotent hP)
    (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) (X.map Complex.ofReal) hp hq hs

/-- Pointwise trace identity for the real two-sheet resolvent integrand. -/
theorem real_twoSheetResolvent_trace_left_pointwise
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ X : Matrix ι ι ℝ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s) :
    Matrix.trace (X * twoSheetResolventReal P p q s * Φ * twoSheetResolventReal P p q s) =
      (1 / ((p + s) * (q + s))) * Matrix.trace (X * Φ) := by
  rw [real_twoSheetResolvent_left_product P hP Φ X hΦ11 hΦ00 hp hq hs,
    Matrix.trace_smul, smul_eq_mul]

/-- Integrability of the real two-sheet resolvent trace integrand on `Ioi 0`. -/
theorem integrableOn_real_twoSheetResolvent_trace_left
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ X : Matrix ι ι ℝ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ =>
      Matrix.trace (X * twoSheetResolventReal P p q s * Φ * twoSheetResolventReal P p q s))
      (Ioi 0) := by
  have hbase : IntegrableOn (fun s : ℝ =>
      (1 / ((p + s) * (q + s))) * Matrix.trace (X * Φ)) (Ioi 0) :=
    (integrableOn_Ioi_logResolventKernel hp hq).mul_const _
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro s hs
  exact (real_twoSheetResolvent_trace_left_pointwise P hP Φ X hΦ11 hΦ00 hp hq hs.le).symm

/-- Compatibility of the real trace integral with `Complex.ofRealCLM` via
`ContinuousLinearMap.integral_comp_comm`. -/
theorem complex_ofReal_integral_twoSheetResolvent_trace_left
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ X : Matrix ι ι ℝ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ),
      Matrix.trace ((X * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s).map Complex.ofReal)) =
      Complex.ofReal (∫ s in Ioi (0 : ℝ),
        Matrix.trace (X * twoSheetResolventReal P p q s * Φ *
          twoSheetResolventReal P p q s)) := by
  have hint := integrableOn_real_twoSheetResolvent_trace_left P hP Φ X hΦ11 hΦ00 hp hq
  have hcomm := Complex.ofRealCLM.integral_comp_comm hint
  simp_rw [complexify_trace]
  simpa only [Complex.ofRealCLM_apply] using hcomm

/-- Compatibility of the real trace integral with `Complex.reCLM` and the
`TwoSheetBKM` integrand on `Matrix ι ι ℂ`. -/
theorem integral_twoSheetResolvent_trace_left_eq_re_complex
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ X : Matrix ι ι ℝ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ),
      Matrix.trace (X * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s)) =
      (∫ s in Ioi (0 : ℝ),
        (Matrix.trace ((X.map Complex.ofReal) *
          twoSheetResolvent (P.map Complex.ofReal) p q s *
          genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) *
          twoSheetResolvent (P.map Complex.ofReal) p q s)).re) := by
  have hint := integrableOn_real_twoSheetResolvent_trace_left P hP Φ X hΦ11 hΦ00 hp hq
  have hintC : IntegrableOn (fun s : ℝ =>
      Complex.ofRealCLM (Matrix.trace (X * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s))) (Ioi 0) :=
    Complex.ofRealCLM.integrable_comp hint
  have hcomm := Complex.reCLM.integral_comp_comm hintC
  have hre : (∫ s in Ioi (0 : ℝ),
      Complex.reCLM (Complex.ofRealCLM
        (Matrix.trace (X * twoSheetResolventReal P p q s * Φ *
          twoSheetResolventReal P p q s)))) =
      ∫ s in Ioi (0 : ℝ),
        Matrix.trace (X * twoSheetResolventReal P p q s * Φ *
          twoSheetResolventReal P p q s) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _
    simp [Complex.reCLM_apply, Complex.ofRealCLM_apply]
  have hΦeq : Φ = genPhi P Φ Φ := eq_genPhi_of_diag_zero P Φ hΦ11 hΦ00
  have hΦc : Φ.map Complex.ofReal =
      genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) := by
    conv_lhs => rw [hΦeq, complexify_genPhi]
  have hpt : ∀ s : ℝ,
      Complex.ofRealCLM
        (Matrix.trace (X * twoSheetResolventReal P p q s * Φ *
          twoSheetResolventReal P p q s)) =
      Matrix.trace ((X.map Complex.ofReal) *
        twoSheetResolvent (P.map Complex.ofReal) p q s *
        genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) *
        twoSheetResolvent (P.map Complex.ofReal) p q s) := by
    intro s
    rw [Complex.ofRealCLM_apply, ← complexify_trace, complexify_mul, complexify_mul,
      complexify_mul, twoSheetResolventReal_complexify, ← hΦc]
  have hinner : (∫ s in Ioi (0 : ℝ),
      Complex.ofRealCLM
        (Matrix.trace (X * twoSheetResolventReal P p q s * Φ *
          twoSheetResolventReal P p q s))) =
      ∫ s in Ioi (0 : ℝ),
        Matrix.trace ((X.map Complex.ofReal) *
          twoSheetResolvent (P.map Complex.ofReal) p q s *
          genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) *
          twoSheetResolvent (P.map Complex.ofReal) p q s) :=
    setIntegral_congr_fun measurableSet_Ioi (fun s _ => hpt s)
  have hintC2 : IntegrableOn (fun s : ℝ =>
      Matrix.trace ((X.map Complex.ofReal) *
        twoSheetResolvent (P.map Complex.ofReal) p q s *
        genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) *
        twoSheetResolvent (P.map Complex.ofReal) p q s)) (Ioi 0) :=
    hintC.congr_fun (fun s _ => hpt s) measurableSet_Ioi
  rw [← hre, hcomm, hinner, ← Complex.reCLM.integral_comp_comm hintC2]
  rfl

/-- Operator-valued Bochner sandwich integral on `Matrix ι ι ℝ`. -/
theorem integral_twoSheetResolventReal_sandwich
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ : Matrix ι ι ℝ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ),
      twoSheetResolventReal P p q s * Φ * twoSheetResolventReal P p q s) =
      logDividedDifference p q • Φ := by
  have hpt : ∀ s : ℝ, 0 ≤ s →
      twoSheetResolventReal P p q s * Φ * twoSheetResolventReal P p q s =
        (1 / ((p + s) * (q + s))) • Φ := by
    intro s hs
    have h := real_twoSheetResolvent_left_product P hP Φ (1 : Matrix ι ι ℝ)
      hΦ11 hΦ00 hp hq hs
    simpa only [one_mul] using h
  calc
    (∫ s in Ioi (0 : ℝ),
        twoSheetResolventReal P p q s * Φ * twoSheetResolventReal P p q s) =
      ∫ s in Ioi (0 : ℝ), (1 / ((p + s) * (q + s))) • Φ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        exact hpt s hs.le
    _ = (∫ s in Ioi (0 : ℝ), 1 / ((p + s) * (q + s))) • Φ := integral_smul_const _ _
    _ = logDividedDifference p q • Φ := by rw [integral_Ioi_logResolventKernel hp hq]

/-- Real-matrix two-sheet resolvent trace identity with arbitrary left probe `X`,
lifted directly from `TwoSheetBKM.integral_twoSheetResolvent_trace_left`. -/
theorem real_twoSheetResolvent_trace_left
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ X : Matrix ι ι ℝ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ),
      Matrix.trace (X * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s)) =
      logDividedDifference p q * Matrix.trace (X * Φ) := by
  have hΦeq : Φ = genPhi P Φ Φ := eq_genPhi_of_diag_zero P Φ hΦ11 hΦ00
  rw [integral_twoSheetResolvent_trace_left_eq_re_complex P hP Φ X hΦ11 hΦ00 hp hq]
  rw [InfoGeometry.OperatorAlgebra.PeirceSpine.integral_twoSheetResolvent_trace_left
    (P.map Complex.ofReal) (complexify_idempotent hP)
    (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) (X.map Complex.ofReal) hp hq]
  congr 1
  conv_lhs =>
    arg 1; arg 1; arg 2
    rw [← complexify_genPhi, ← hΦeq]
  rw [← complexify_mul, complexify_trace_re]

/-- Real-matrix quadratic BKM resolvent trace readout:
`(∫ s in Ioi 0, trace (Φ * R(s) * Φ * R(s))) = logDividedDifference p q * trace (Φ * Φ)`,
matching `TwoSheetBKM.integral_twoSheetResolvent_quadratic_trace` via
`Φ = genPhi P Φ Φ` and `Φ * Φ = genV P Φ Φ`. -/
theorem real_twoSheetResolvent_quadratic_trace
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ : Matrix ι ι ℝ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ),
      Matrix.trace (Φ * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s)) =
      logDividedDifference p q * Matrix.trace (Φ * Φ) := by
  have hΦeq : Φ = genPhi P Φ Φ := eq_genPhi_of_diag_zero P Φ hΦ11 hΦ00
  have hΦc : Φ.map Complex.ofReal =
      genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) := by
    conv_lhs => rw [hΦeq, complexify_genPhi]
  have hΦsq : Φ * Φ = genV P Φ Φ := by
    conv_lhs => rw [hΦeq]
    exact (archetype_A3_nilpotent_cones_and_tetraktys_table hP Φ Φ).2.2.1
  rw [integral_twoSheetResolvent_trace_left_eq_re_complex P hP Φ Φ hΦ11 hΦ00 hp hq]
  have hC := InfoGeometry.OperatorAlgebra.PeirceSpine.integral_twoSheetResolvent_quadratic_trace
    (P.map Complex.ofReal) (complexify_idempotent hP)
    (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) hp hq
  conv_lhs =>
    arg 2; ext s; arg 1; arg 1; arg 1; arg 1; arg 1
    rw [hΦc]
  rw [hC, hΦsq, ← complexify_genV, complexify_trace_re]

/-- Every real symmetric Peirce-odd perturbation has nonnegative quadratic BKM integral,
lifted from `TwoSheetBKM.integral_twoSheetResolvent_quadratic_nonneg`. -/
theorem real_twoSheetResolvent_quadratic_nonneg
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ : Matrix ι ι ℝ) (hΦT : Φᵀ = Φ)
    (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    0 ≤ ∫ s in Ioi (0 : ℝ),
      Matrix.trace (Φ * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s) := by
  have hΦeq : Φ = genPhi P Φ Φ := eq_genPhi_of_diag_zero P Φ hΦ11 hΦ00
  have hΦc_eq : genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) =
      Φ.map Complex.ofReal := by
    rw [← complexify_genPhi, ← hΦeq]
  have hΦc_herm :
      (genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal)).IsHermitian := by
    rw [hΦc_eq]
    exact (complexify_isHermitian_iff Φ).mpr hΦT
  rw [integral_twoSheetResolvent_trace_left_eq_re_complex P hP Φ Φ hΦ11 hΦ00 hp hq]
  have hnn := InfoGeometry.OperatorAlgebra.PeirceSpine.integral_twoSheetResolvent_quadratic_nonneg
    (P.map Complex.ofReal) (complexify_idempotent hP)
    (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) hp hq hΦc_herm
  simpa only [hΦc_eq] using hnn

/-- Every nonzero real symmetric Peirce-odd perturbation has strictly positive
quadratic BKM resolvent integral, lifted from
`TwoSheetBKM.integral_twoSheetResolvent_quadratic_pos`. -/
theorem real_twoSheetResolvent_quadratic_pos
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ : Matrix ι ι ℝ) (hΦT : Φᵀ = Φ)
    (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    (hΦ_ne : Φ ≠ 0) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    0 < ∫ s in Ioi (0 : ℝ),
      Matrix.trace (Φ * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s) := by
  have hΦeq : Φ = genPhi P Φ Φ := eq_genPhi_of_diag_zero P Φ hΦ11 hΦ00
  have hΦc_eq : genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) =
      Φ.map Complex.ofReal := by
    rw [← complexify_genPhi, ← hΦeq]
  have hΦc_herm :
      (genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal)).IsHermitian := by
    rw [hΦc_eq]
    exact (complexify_isHermitian_iff Φ).mpr hΦT
  have hΦc_ne :
      genPhi (P.map Complex.ofReal) (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) ≠ 0 := by
    rw [hΦc_eq]
    intro hz
    exact hΦ_ne (complexify_injective (hz.trans complexify_zero.symm))
  rw [integral_twoSheetResolvent_trace_left_eq_re_complex P hP Φ Φ hΦ11 hΦ00 hp hq]
  have hpos := InfoGeometry.OperatorAlgebra.PeirceSpine.integral_twoSheetResolvent_quadratic_pos
    (P.map Complex.ofReal) (complexify_idempotent hP)
    (Φ.map Complex.ofReal) (Φ.map Complex.ofReal) hp hq hΦc_herm hΦc_ne
  simpa only [hΦc_eq] using hpos

/-- Strict positivity iff nonvanishing of `Φ`. -/
theorem real_twoSheetResolvent_quadratic_pos_iff
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ : Matrix ι ι ℝ) (hΦT : Φᵀ = Φ)
    (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    0 < (∫ s in Ioi (0 : ℝ),
      Matrix.trace (Φ * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s)) ↔ Φ ≠ 0 := by
  constructor
  · intro hpos hz
    subst hz
    simp only [zero_mul, Matrix.trace_zero, integral_zero] at hpos
    exact lt_irrefl 0 hpos
  · intro hne
    exact real_twoSheetResolvent_quadratic_pos P hP Φ hΦT hΦ11 hΦ00 hne hp hq

/-- Equivalence between strict positivity of the real coupled-corner BKM integral
and `OppositePeirceRealMetric.trace_square_pos_iff` (`component10 P A ≠ 0`). -/
theorem real_twoSheetResolvent_coupledCorner_pos_iff
    (P : Matrix ι ι ℝ) (hP : P * P = P) (hPT : Pᵀ = P)
    (A : Matrix ι ι ℝ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    0 < (∫ s in Ioi (0 : ℝ),
      Matrix.trace ((component10 P A + component01 P Aᵀ) *
        twoSheetResolventReal P p q s *
        (component10 P A + component01 P Aᵀ) *
        twoSheetResolventReal P p q s)) ↔
      component10 P A ≠ 0 := by
  let Φ := component10 P A + component01 P Aᵀ
  have hΦ11 : P * Φ * P = 0 := by
    change P * (conePlus P A + coneMinus P Aᵀ) * P = 0
    peirce_nf hP
  have hΦ00 : (1 - P) * Φ * (1 - P) = 0 := by
    change (1 - P) * (conePlus P A + coneMinus P Aᵀ) * (1 - P) = 0
    peirce_nf hP
  have htr : (∫ s in Ioi (0 : ℝ),
      Matrix.trace (Φ * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s)) =
      logDividedDifference p q * Matrix.trace (Φ * Φ) :=
    real_twoSheetResolvent_quadratic_trace P hP Φ hΦ11 hΦ00 hp hq
  have hlog : 0 < logDividedDifference p q := logDividedDifference_pos hp hq
  have hPs : P.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hPT
  have hsq : 0 < Matrix.trace (Φ * Φ) ↔ component10 P A ≠ 0 :=
    InfoGeometry.NCG.OppositePeirceRealMetric.trace_square_pos_iff hP hPs A
  rw [htr, ← hsq]
  exact mul_pos_iff_of_pos_left hlog

end RealBKMLifting

namespace RealTwoSheetBKMContext

section ContextMethods

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_left (ctx : RealTwoSheetBKMContext ι) (X : Matrix ι ι ℝ) :
    (∫ s in Ioi (0 : ℝ),
      Matrix.trace (X * ctx.resolvent s * ctx.Φ * ctx.resolvent s)) =
      logDividedDifference ctx.p ctx.q * Matrix.trace (X * ctx.Φ) :=
  real_twoSheetResolvent_trace_left ctx.P ctx.P_idempotent ctx.Φ X
    ctx.P_mul_Φ_mul_P ctx.one_sub_P_mul_Φ_mul_one_sub_P ctx.p_pos ctx.q_pos

theorem quadratic_trace (ctx : RealTwoSheetBKMContext ι) :
    (∫ s in Ioi (0 : ℝ),
      Matrix.trace (ctx.Φ * ctx.resolvent s * ctx.Φ * ctx.resolvent s)) =
      logDividedDifference ctx.p ctx.q * Matrix.trace (ctx.Φ * ctx.Φ) :=
  real_twoSheetResolvent_quadratic_trace ctx.P ctx.P_idempotent ctx.Φ
    ctx.P_mul_Φ_mul_P ctx.one_sub_P_mul_Φ_mul_one_sub_P ctx.p_pos ctx.q_pos

theorem quadratic_nonneg (ctx : RealTwoSheetBKMContext ι) :
    0 ≤ ∫ s in Ioi (0 : ℝ),
      Matrix.trace (ctx.Φ * ctx.resolvent s * ctx.Φ * ctx.resolvent s) :=
  real_twoSheetResolvent_quadratic_nonneg ctx.P ctx.P_idempotent ctx.Φ ctx.Φ_symm
    ctx.P_mul_Φ_mul_P ctx.one_sub_P_mul_Φ_mul_one_sub_P ctx.p_pos ctx.q_pos

theorem quadratic_pos (ctx : RealTwoSheetBKMContext ι) (hΦ_ne : ctx.Φ ≠ 0) :
    0 < ∫ s in Ioi (0 : ℝ),
      Matrix.trace (ctx.Φ * ctx.resolvent s * ctx.Φ * ctx.resolvent s) :=
  real_twoSheetResolvent_quadratic_pos ctx.P ctx.P_idempotent ctx.Φ ctx.Φ_symm
    ctx.P_mul_Φ_mul_P ctx.one_sub_P_mul_Φ_mul_one_sub_P hΦ_ne ctx.p_pos ctx.q_pos

theorem bkmPairing_self_eq_quadratic (ctx : RealTwoSheetBKMContext ι) :
    ctx.bkmPairing ctx.Φ ctx.Φ =
      ∫ s in Ioi (0 : ℝ),
        Matrix.trace (ctx.Φ * ctx.resolvent s * ctx.Φ * ctx.resolvent s) := by
  simp only [bkmPairing, realBKMResolventPairing, resolvent, ctx.Φ_symm]

theorem bkmPairing_self_pos (ctx : RealTwoSheetBKMContext ι) (hΦ_ne : ctx.Φ ≠ 0) :
    0 < ctx.bkmPairing ctx.Φ ctx.Φ := by
  rw [ctx.bkmPairing_self_eq_quadratic]
  exact ctx.quadratic_pos hΦ_ne

end ContextMethods

end RealTwoSheetBKMContext

/-! ## Finite Faithful Traces vs Type III Factor Obstructions -/

/-- Unital tracial `ℝ`-linear functional on an associative `ℝ`-algebra. -/
structure UnitalTracialFunctional (A : Type*) [Ring A] [Algebra ℝ A] where
  /-- Underlying `ℝ`-linear functional. -/
  τ : A →ₗ[ℝ] ℝ
  /-- Traciality: `τ (a * b) = τ (b * a)`. -/
  tracial : ∀ a b : A, τ (a * b) = τ (b * a)
  /-- Strictly positive unit trace. -/
  unit_pos : 0 < τ 1

/-- Unital tracial functional that is nonnegative and faithful on idempotents (star-free). -/
structure IdempotentFaithfulTrace (A : Type*) [Ring A] [Algebra ℝ A]
    extends UnitalTracialFunctional A where
  /-- Nonnegativity on idempotents. -/
  idempotent_nonneg : ∀ e : A, e * e = e → 0 ≤ τ e
  /-- Faithfulness on idempotents. -/
  idempotent_faithful : ∀ e : A, e * e = e → τ e = 0 → e = 0

/-- Faithful positive finite tracial state on a real star-algebra. -/
structure FiniteFaithfulStarTrace (A : Type*) [Ring A] [Algebra ℝ A] [StarRing A]
    extends UnitalTracialFunctional A where
  /-- Nonnegativity on `star x * x`. -/
  star_mul_nonneg : ∀ x : A, 0 ≤ τ (star x * x)
  /-- Faithfulness on `star x * x`. -/
  star_mul_faithful : ∀ x : A, τ (star x * x) = 0 → x = 0

theorem FiniteFaithfulStarTrace.starProjection_faithful
    {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    (T : FiniteFaithfulStarTrace A) {p : A} (hps : star p = p) (hpi : p * p = p)
    (hz : T.τ p = 0) : p = 0 :=
  T.star_mul_faithful p (by rw [hps, hpi]; exact hz)

section MatrixTraces

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Native unital trace on `Matrix ι ι ℝ`. -/
def matrixUnitalTrace : UnitalTracialFunctional (Matrix ι ι ℝ) where
  τ := Matrix.traceLinearMap ι ℝ ℝ
  tracial a b := Matrix.trace_mul_comm a b
  unit_pos := by
    simp only [Matrix.traceLinearMap_apply, Matrix.trace_one, Fintype.card_pos, Nat.cast_pos]

/-- Native finite faithful star-trace on `Matrix ι ι ℝ`. -/
def matrixStarTrace : FiniteFaithfulStarTrace (Matrix ι ι ℝ) where
  toUnitalTracialFunctional := matrixUnitalTrace ι
  star_mul_nonneg x := (Matrix.posSemidef_conjTranspose_mul_self x).trace_nonneg
  star_mul_faithful _ hx := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hx

/-- Native idempotent-faithful trace on `Matrix ι ι ℝ`. -/
def matrixIdempotentFaithfulTrace : IdempotentFaithfulTrace (Matrix ι ι ℝ) where
  toUnitalTracialFunctional := matrixUnitalTrace ι
  idempotent_nonneg e he := by
    have he' : IsIdempotentElem e.toLin' := by
      change e.toLin' * e.toLin' = e.toLin'
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
    change 0 ≤ Matrix.trace e
    rw [← Matrix.trace_toLin'_eq e, (LinearMap.IsIdempotentElem.isProj_range e.toLin' he').trace]
    exact Nat.cast_nonneg _
  idempotent_faithful e he hτ := by
    have he' : IsIdempotentElem e.toLin' := by
      change e.toLin' * e.toLin' = e.toLin'
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
    change Matrix.trace e = 0 at hτ
    rw [← Matrix.trace_toLin'_eq e, LinearMap.IsIdempotentElem.trace_eq_zero_iff he'] at hτ
    exact Matrix.toLin'.injective (hτ.trans (map_zero Matrix.toLin').symm)

end MatrixTraces

section AlgebraicSeparations

/-- Any star-isometry in an algebra with a faithful finite star-trace is unitary. -/
theorem no_nonunitary_starIsometry_of_faithful_starTrace
    {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    (T : FiniteFaithfulStarTrace A) (V : A) (hV : star V * V = 1) :
    V * star V = 1 := by
  let P : A := 1 - V * star V
  have hP_star : star P = P := by
    simp only [P, star_sub, star_one, star_mul, star_star]
  have hP_idem : P * P = P := by
    calc P * P = (1 - V * star V) * (1 - V * star V) := rfl
      _ = 1 - V * star V - V * star V + V * (star V * V) * star V := by noncomm_ring
      _ = P := by rw [hV]; dsimp [P]; noncomm_ring
  have hP_trace : T.τ (star P * P) = 0 := by
    rw [hP_star, hP_idem]
    simp only [P, map_sub, T.tracial V (star V), hV, sub_self]
  exact (sub_eq_zero.mp (T.star_mul_faithful P hP_trace)).symm

/-- Contrapositive form: no non-unitary star-isometry exists under a faithful star-trace. -/
theorem not_exists_nonunitary_starIsometry_of_faithful_starTrace
    {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    (T : FiniteFaithfulStarTrace A) :
    ¬ ∃ V : A, star V * V = 1 ∧ V * star V ≠ 1 := by
  rintro ⟨V, h1, h2⟩
  exact h2 (no_nonunitary_starIsometry_of_faithful_starTrace T V h1)

/-- Star-free Dedekind-finiteness: any one-sided inverse is two-sided under an
idempotent-faithful trace. -/
theorem no_oneSided_inverse_of_idempotent_faithful_trace
    {A : Type*} [Ring A] [Algebra ℝ A]
    (T : IdempotentFaithfulTrace A) (L V : A) (hLV : L * V = 1) :
    V * L = 1 := by
  let P : A := 1 - V * L
  have hP_idem : P * P = P := by
    calc P * P = (1 - V * L) * (1 - V * L) := rfl
      _ = 1 - V * L - V * L + V * (L * V) * L := by noncomm_ring
      _ = P := by rw [hLV]; dsimp [P]; noncomm_ring
  have hP_trace : T.τ P = 0 := by
    simp only [P, map_sub, T.tracial V L, hLV, sub_self]
  exact (sub_eq_zero.mp (T.idempotent_faithful P hP_idem hP_trace)).symm

/-- Type III projection halving (`P ~ 1` and `(1 - P) ~ 1`) is impossible for any
nonzero unital tracial linear functional (even without faithfulness). -/
theorem no_typeIII_halving_of_unital_tracial
    {A : Type*} [Ring A] [Algebra ℝ A]
    (τ : A →ₗ[ℝ] ℝ) (h_tracial : ∀ a b : A, τ (a * b) = τ (b * a))
    (h_one : τ 1 ≠ 0) :
    ¬ ∃ P u₁ v₁ u₂ v₂ : A,
      u₁ * v₁ = 1 ∧ v₁ * u₁ = P ∧ u₂ * v₂ = 1 ∧ v₂ * u₂ = 1 - P := by
  rintro ⟨P, u₁, v₁, u₂, v₂, h₁, hp₁, h₂, hp₂⟩
  have hτP : τ P = τ 1 := by rw [← hp₁, h_tracial, h₁]
  have hτQ : τ (1 - P) = τ 1 := by rw [← hp₂, h_tracial, h₂]
  have hsum : τ 1 = τ P + τ (1 - P) := by rw [← map_add, add_sub_cancel]
  rw [hτP, hτQ] at hsum
  have h0 : 0 + τ 1 = τ 1 + τ 1 := by rw [zero_add]; exact hsum
  exact h_one (add_right_cancel h0).symm

/-- Star-isometry (Cuntz `O₂`) version of Type III projection halving impossibility. -/
theorem no_star_typeIII_halving_of_unital_tracial
    {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    (T : UnitalTracialFunctional A) :
    ¬ ∃ P V₁ V₂ : A,
      star V₁ * V₁ = 1 ∧ V₁ * star V₁ = P ∧
      star V₂ * V₂ = 1 ∧ V₂ * star V₂ = 1 - P := by
  rintro ⟨P, V₁, V₂, h₁, hp₁, h₂, hp₂⟩
  exact no_typeIII_halving_of_unital_tracial T.τ T.tracial T.unit_pos.ne'
    ⟨P, star V₁, V₁, star V₂, V₂, h₁, hp₁, h₂, hp₂⟩

/-- No unital `ℝ`-algebra homomorphism exists from a Type-III-halving algebra into any
algebra carrying a unital tracial functional. -/
theorem no_algHom_of_halving_to_unital_tracial
    {B_inf A : Type*} [Ring B_inf] [Algebra ℝ B_inf] [Ring A] [Algebra ℝ A]
    (T : UnitalTracialFunctional A)
    (u₁ v₁ u₂ v₂ : B_inf)
    (h₁ : u₁ * v₁ = 1) (h₂ : u₂ * v₂ = 1)
    (hsum : v₁ * u₁ + v₂ * u₂ = 1) :
    IsEmpty (B_inf →ₐ[ℝ] A) := by
  refine ⟨fun φ => ?_⟩
  have hφ1 : φ 1 = 1 := map_one φ
  have hφm : ∀ x y : B_inf, φ (x * y) = φ x * φ y := fun x y => map_mul φ x y
  have hτ_sum : T.τ (φ 1) = T.τ (φ (v₁ * u₁)) + T.τ (φ (v₂ * u₂)) := by
    rw [← hsum, map_add, map_add]
  rw [hφ1, hφm, hφm, T.tracial (φ v₁) (φ u₁), T.tracial (φ v₂) (φ u₂),
    ← hφm, ← hφm, h₁, h₂, hφ1] at hτ_sum
  have h0 : 0 + T.τ 1 = T.τ 1 + T.τ 1 := by rw [zero_add]; exact hτ_sum
  exact T.unit_pos.ne' (add_right_cancel h0).symm

end AlgebraicSeparations

/-- Higher-grade structural separation between the finite-dimensional faithful-trace
two-sheet BKM regime on `Matrix ι ι ℝ` and an infinite / Type-III-halving boundary
algebra `B_inf` admitting both one-sided shifts and whole-projection halving
`1 ~ P`, `1 ~ 1 - P`. -/
structure FiniteTraceBKMVsTypeIIISeparation
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B_inf : Type*) [Ring B_inf] [Algebra ℝ B_inf] where
  /-- Finite-dimensional real two-sheet BKM context. -/
  bkmContext : RealTwoSheetBKMContext ι
  /-- Finite faithful star-trace on `Matrix ι ι ℝ`. -/
  finiteStarTrace : FiniteFaithfulStarTrace (Matrix ι ι ℝ)
  /-- Finite idempotent-faithful trace on `Matrix ι ι ℝ`. -/
  finiteIdemTrace : IdempotentFaithfulTrace (Matrix ι ι ℝ)
  /-- Left-inverse shift element in the infinite algebra `B_inf`. -/
  infLeft : B_inf
  /-- Right-inverse shift element in the infinite algebra `B_inf`. -/
  infRight : B_inf
  /-- One-sided inverse identity `infLeft * infRight = 1`. -/
  inf_one_sided_left : infLeft * infRight = 1
  /-- Strict one-sidedness `infRight * infLeft ≠ 1`. -/
  inf_one_sided_right_ne : infRight * infLeft ≠ 1
  /-- First halving left-inverse in `B_inf`. -/
  halvingU₁ : B_inf
  /-- First halving isometry in `B_inf`. -/
  halvingV₁ : B_inf
  /-- Second halving left-inverse in `B_inf`. -/
  halvingU₂ : B_inf
  /-- Second halving isometry in `B_inf`. -/
  halvingV₂ : B_inf
  /-- First halving identity `halvingU₁ * halvingV₁ = 1`. -/
  halving_one : halvingU₁ * halvingV₁ = 1
  /-- Second halving identity `halvingU₂ * halvingV₂ = 1`. -/
  halving_two : halvingU₂ * halvingV₂ = 1
  /-- Complementary projection halving `halvingV₁ * halvingU₁ + halvingV₂ * halvingU₂ = 1`. -/
  halving_sum : halvingV₁ * halvingU₁ + halvingV₂ * halvingU₂ = 1

namespace FiniteTraceBKMVsTypeIIISeparation

section SeparationTheorems

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {B_inf : Type*} [Ring B_inf] [Algebra ℝ B_inf]

/-- No non-unitary star-isometry exists in the finite matrix algebra of `S`. -/
theorem finite_no_nonunitary_starIsometry
    (S : FiniteTraceBKMVsTypeIIISeparation ι B_inf) :
    ¬ ∃ V : Matrix ι ι ℝ, star V * V = 1 ∧ V * star V ≠ 1 :=
  not_exists_nonunitary_starIsometry_of_faithful_starTrace S.finiteStarTrace

/-- Dedekind-finiteness of the finite matrix algebra via `S.finiteIdemTrace`. -/
theorem finiteMatrix_dedekindFinite
    (S : FiniteTraceBKMVsTypeIIISeparation ι B_inf) (A C : Matrix ι ι ℝ)
    (hAC : A * C = 1) : C * A = 1 :=
  no_oneSided_inverse_of_idempotent_faithful_trace S.finiteIdemTrace A C hAC

/-- No Type III projection halving exists in the finite matrix algebra of `S`. -/
theorem finite_no_typeIII_halving
    (S : FiniteTraceBKMVsTypeIIISeparation ι B_inf) :
    ¬ ∃ P u₁ v₁ u₂ v₂ : Matrix ι ι ℝ,
      u₁ * v₁ = 1 ∧ v₁ * u₁ = P ∧ u₂ * v₂ = 1 ∧ v₂ * u₂ = 1 - P :=
  no_typeIII_halving_of_unital_tracial S.finiteStarTrace.τ S.finiteStarTrace.tracial
    S.finiteStarTrace.unit_pos.ne'

/-- Faithfulness and positivity of `S.finiteStarTrace.τ` on `Aᵀ * A`. -/
theorem finiteTrace_faithful_pos
    (S : FiniteTraceBKMVsTypeIIISeparation ι B_inf) (A : Matrix ι ι ℝ) (hA : A ≠ 0) :
    0 < S.finiteStarTrace.τ (Aᵀ * A) := by
  have hnn : 0 ≤ S.finiteStarTrace.τ (star A * A) := S.finiteStarTrace.star_mul_nonneg A
  have hne : S.finiteStarTrace.τ (star A * A) ≠ 0 := by
    intro hz
    exact hA (S.finiteStarTrace.star_mul_faithful A hz)
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-- Strict positivity of the finite real BKM pairing on `S.bkmContext.Φ ≠ 0`. -/
theorem finiteMatrix_bkm_pos
    (S : FiniteTraceBKMVsTypeIIISeparation ι B_inf) (hΦ_ne : S.bkmContext.Φ ≠ 0) :
    0 < S.bkmContext.bkmPairing S.bkmContext.Φ S.bkmContext.Φ :=
  S.bkmContext.bkmPairing_self_pos hΦ_ne

/-- No nonzero unital tracial linear functional exists on the infinite boundary
algebra `B_inf`. -/
theorem boundary_no_unital_tracial_functional
    (S : FiniteTraceBKMVsTypeIIISeparation ι B_inf) :
    ¬ ∃ τ : B_inf →ₗ[ℝ] ℝ, (∀ a b : B_inf, τ (a * b) = τ (b * a)) ∧ τ 1 ≠ 0 := by
  rintro ⟨τ, h_tracial, h_one⟩
  exact no_typeIII_halving_of_unital_tracial τ h_tracial h_one
    ⟨S.halvingV₁ * S.halvingU₁, S.halvingU₁, S.halvingV₁, S.halvingU₂, S.halvingV₂,
      S.halving_one, rfl, S.halving_two, by rw [← S.halving_sum]; abel⟩

/-- No idempotent-faithful trace exists on `B_inf`. -/
theorem boundary_no_idempotent_faithful_trace
    (S : FiniteTraceBKMVsTypeIIISeparation ι B_inf) :
    IsEmpty (IdempotentFaithfulTrace B_inf) :=
  ⟨fun T => S.inf_one_sided_right_ne
    (no_oneSided_inverse_of_idempotent_faithful_trace T S.infLeft S.infRight
      S.inf_one_sided_left)⟩

/-- No unital `ℝ`-algebra homomorphism maps `B_inf` into `Matrix ι ι ℝ`. -/
theorem no_algHom_boundary_to_finite
    (S : FiniteTraceBKMVsTypeIIISeparation ι B_inf) :
    IsEmpty (B_inf →ₐ[ℝ] Matrix ι ι ℝ) :=
  no_algHom_of_halving_to_unital_tracial S.finiteStarTrace.toUnitalTracialFunctional
    S.halvingU₁ S.halvingV₁ S.halvingU₂ S.halvingV₂
    S.halving_one S.halving_two S.halving_sum

/-- When the sheet weights differ (`p ≠ q`) and `Φ ≠ 0`, the density-weighted
functional `X ↦ Matrix.trace (ctx.density * X)` is strictly non-tracial on the
Peirce corners `conePlus P Φ` and `coneMinus P Φ`, while `S.finiteStarTrace.τ`
remains finite, tracial, and faithful on `Matrix ι ι ℝ`. -/
theorem nonTracial_density_when_weights_differ
    (S : FiniteTraceBKMVsTypeIIISeparation ι B_inf)
    (hpq : S.bkmContext.p ≠ S.bkmContext.q) (hΦ_ne : S.bkmContext.Φ ≠ 0) :
    Matrix.trace (S.bkmContext.density *
        (conePlus S.bkmContext.P S.bkmContext.Φ * coneMinus S.bkmContext.P S.bkmContext.Φ)) ≠
      Matrix.trace (S.bkmContext.density *
        (coneMinus S.bkmContext.P S.bkmContext.Φ * conePlus S.bkmContext.P S.bkmContext.Φ)) ∧
      (∀ A B : Matrix ι ι ℝ,
        S.finiteStarTrace.τ (A * B) = S.finiteStarTrace.τ (B * A)) := by
  let P := S.bkmContext.P
  let Φ := S.bkmContext.Φ
  let Np := conePlus P Φ
  let Nm := coneMinus P Φ
  have hP : P * P = P := S.bkmContext.P_idempotent
  have hNm_eq : Nm = Npᵀ := by
    dsimp [Nm, Np, coneMinus, conePlus]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      S.bkmContext.P_symm, S.bkmContext.Φ_symm, mul_assoc]
  have hNp_ne : Np ≠ 0 := by
    intro h0
    apply hΦ_ne
    have hΦ_eq := S.bkmContext.Φ_eq_genPhi
    have hNm0 : Nm = 0 := by rw [hNm_eq, h0, Matrix.transpose_zero]
    rw [hΦ_eq]
    change Np + Nm = 0
    rw [h0, hNm0, add_zero]
  have htr_pos : 0 < Matrix.trace (Np * Nm) := by
    have hnn : 0 ≤ Matrix.trace (Np * Npᴴ) := by
      have hps := (Matrix.posSemidef_conjTranspose_mul_self Npᴴ).trace_nonneg
      simpa only [Matrix.conjTranspose_conjTranspose] using hps
    have hne : Matrix.trace (Np * Npᴴ) ≠ 0 := by
      intro hz
      exact hNp_ne (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hz)
    have hpos : 0 < Matrix.trace (Np * Npᴴ) := lt_of_le_of_ne hnn (Ne.symm hne)
    have hconj : Npᴴ = Npᵀ := Matrix.conjTranspose_eq_transpose_of_trivial Np
    rw [hconj, ← hNm_eq] at hpos
    exact hpos
  have hPNp : P * Np = Np := P_mul_conePlus hP Φ
  have h1PNp : (1 - P) * Np = 0 := by
    dsimp [Np, conePlus]
    rw [← mul_assoc, ← mul_assoc, sub_mul, one_mul, hP, sub_self, zero_mul, zero_mul]
  have hPNm : P * Nm = 0 := P_mul_coneMinus hP Φ
  have h1PNm : (1 - P) * Nm = Nm := by
    dsimp [Nm, coneMinus]
    have h1P : (1 - P) * (1 - P) = 1 - P := by
      calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        _ = 1 - P := by rw [hP]; noncomm_ring
    rw [← mul_assoc, ← mul_assoc, h1P]
  have hρNp : S.bkmContext.density * Np = S.bkmContext.p • Np := by
    change (S.bkmContext.p • P + S.bkmContext.q • (1 - P)) * Np = S.bkmContext.p • Np
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, hPNp, h1PNp, smul_zero, add_zero]
  have hρNm : S.bkmContext.density * Nm = S.bkmContext.q • Nm := by
    change (S.bkmContext.p • P + S.bkmContext.q • (1 - P)) * Nm = S.bkmContext.q • Nm
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, hPNm, h1PNm, smul_zero, zero_add]
  have hLHS : Matrix.trace (S.bkmContext.density * (Np * Nm)) =
      S.bkmContext.p * Matrix.trace (Np * Nm) := by
    rw [← mul_assoc, hρNp, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
  have hRHS : Matrix.trace (S.bkmContext.density * (Nm * Np)) =
      S.bkmContext.q * Matrix.trace (Np * Nm) := by
    rw [← mul_assoc, hρNm, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul,
      Matrix.trace_mul_comm Nm Np]
  refine ⟨?_, S.finiteStarTrace.tracial⟩
  rw [hLHS, hRHS]
  intro heq
  exact hpq (mul_right_cancel₀ htr_pos.ne' heq)

end SeparationTheorems

end FiniteTraceBKMVsTypeIIISeparation

/-! ## Concrete Infinite-Dimensional Witness on `Module.End ℝ (ℕ → ℝ)` -/

/-- Left shift on `ℕ → ℝ`: `(natSeqLeftShift f) n = f (n + 1)`. -/
def natSeqLeftShift : Module.End ℝ (ℕ → ℝ) where
  toFun f n := f (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Right shift on `ℕ → ℝ`: inserts `0` at index `0` and shifts right by `1`. -/
def natSeqRightShift : Module.End ℝ (ℕ → ℝ) where
  toFun f n := Nat.casesOn n 0 f
  map_add' f g := by ext n; cases n <;> simp
  map_smul' r f := by ext n; cases n <;> simp

theorem natSeqLeftShift_mul_rightShift : natSeqLeftShift * natSeqRightShift = 1 := by
  ext f n
  rfl

theorem natSeqRightShift_mul_leftShift_ne : natSeqRightShift * natSeqLeftShift ≠ 1 := by
  intro h
  have h0 := congrArg (fun T : Module.End ℝ (ℕ → ℝ) => T (fun _ => 1) 0) h
  norm_num [natSeqRightShift, natSeqLeftShift] at h0

/-- Concrete T16 noncommutativity witness on `Module.End ℝ (ℕ → ℝ)`. -/
theorem natSeq_shift_noncommuting :
    natSeqRightShift * natSeqLeftShift ≠ natSeqLeftShift * natSeqRightShift := by
  rw [natSeqLeftShift_mul_rightShift]
  exact natSeqRightShift_mul_leftShift_ne

/-- Extract the even-indexed subsequence `n ↦ f (2 * n)`. -/
def natSeqEvenExtract : Module.End ℝ (ℕ → ℝ) where
  toFun f n := f (2 * n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Embed a sequence into the even indices. -/
def natSeqEvenEmbed : Module.End ℝ (ℕ → ℝ) where
  toFun f n := if n % 2 = 0 then f (n / 2) else 0
  map_add' f g := by
    ext n
    by_cases h : n % 2 = 0 <;> simp [h]
  map_smul' r f := by
    ext n
    by_cases h : n % 2 = 0 <;> simp [h]

/-- Extract the odd-indexed subsequence `n ↦ f (2 * n + 1)`. -/
def natSeqOddExtract : Module.End ℝ (ℕ → ℝ) where
  toFun f n := f (2 * n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Embed a sequence into the odd indices. -/
def natSeqOddEmbed : Module.End ℝ (ℕ → ℝ) where
  toFun f n := if n % 2 = 1 then f (n / 2) else 0
  map_add' f g := by
    ext n
    by_cases h : n % 2 = 1 <;> simp [h]
  map_smul' r f := by
    ext n
    by_cases h : n % 2 = 1 <;> simp [h]

theorem natSeqEvenExtract_mul_evenEmbed : natSeqEvenExtract * natSeqEvenEmbed = 1 := by
  ext f n
  have hmod : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  simp [natSeqEvenExtract, natSeqEvenEmbed, hmod, hdiv]

theorem natSeqOddExtract_mul_oddEmbed : natSeqOddExtract * natSeqOddEmbed = 1 := by
  ext f n
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [natSeqOddExtract, natSeqOddEmbed, hmod, hdiv]

theorem natSeqEven_add_odd_proj_eq_one :
    natSeqEvenEmbed * natSeqEvenExtract + natSeqOddEmbed * natSeqOddExtract = 1 := by
  ext f n
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hmul : 2 * (n / 2) = n := by omega
    simp [natSeqEvenEmbed, natSeqEvenExtract, natSeqOddEmbed, natSeqOddExtract, h, hmul]
  · have hmul : 2 * (n / 2) + 1 = n := by omega
    simp [natSeqEvenEmbed, natSeqEvenExtract, natSeqOddEmbed, natSeqOddExtract, h, hmul]

/-- No nonzero unital tracial linear functional exists on `Module.End ℝ (ℕ → ℝ)`. -/
theorem no_unital_tracial_functional_on_end_nat :
    ¬ ∃ τ : Module.End ℝ (ℕ → ℝ) →ₗ[ℝ] ℝ,
      (∀ a b : Module.End ℝ (ℕ → ℝ), τ (a * b) = τ (b * a)) ∧ τ 1 ≠ 0 := by
  rintro ⟨τ, h_tracial, h_one⟩
  exact no_typeIII_halving_of_unital_tracial τ h_tracial h_one
    ⟨natSeqEvenEmbed * natSeqEvenExtract,
     natSeqEvenExtract, natSeqEvenEmbed,
     natSeqOddExtract, natSeqOddEmbed,
     natSeqEvenExtract_mul_evenEmbed, rfl,
     natSeqOddExtract_mul_oddEmbed,
     by rw [← natSeqEven_add_odd_proj_eq_one]; abel⟩

/-- No idempotent-faithful trace exists on `Module.End ℝ (ℕ → ℝ)`. -/
theorem no_idempotent_faithful_trace_on_end_nat :
    IsEmpty (IdempotentFaithfulTrace (Module.End ℝ (ℕ → ℝ))) :=
  ⟨fun T => natSeqRightShift_mul_leftShift_ne
    (no_oneSided_inverse_of_idempotent_faithful_trace T natSeqLeftShift natSeqRightShift
      natSeqLeftShift_mul_rightShift)⟩

/-- No unital `ℝ`-algebra homomorphism maps `Module.End ℝ (ℕ → ℝ)` into `Matrix ι ι ℝ`. -/
theorem no_algHom_end_nat_to_matrix (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    IsEmpty (Module.End ℝ (ℕ → ℝ) →ₐ[ℝ] Matrix ι ι ℝ) :=
  no_algHom_of_halving_to_unital_tracial (matrixUnitalTrace ι)
    natSeqEvenExtract natSeqEvenEmbed natSeqOddExtract natSeqOddEmbed
    natSeqEvenExtract_mul_evenEmbed natSeqOddExtract_mul_oddEmbed
    natSeqEven_add_odd_proj_eq_one

/-! ## Zero-Binder Concrete T17 & T16 Witnesses (Outside `variable` Sections) -/

/-- Concrete zero-binder T17 witness for `RealTwoSheetBKMContext (Fin 2)`. -/
def concreteRealTwoSheetBKMContext : RealTwoSheetBKMContext (Fin 2) where
  P := !![1, 0; 0, 0]
  P_idempotent := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  P_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  p := 1
  q := 2
  p_pos := by norm_num
  q_pos := by norm_num
  Φ := !![0, 1; 1, 0]
  Φ_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  P_mul_Φ_mul_P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  one_sub_P_mul_Φ_mul_one_sub_P := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete zero-binder T17 witness for `UnitalTracialFunctional`. -/
def matrix2UnitalTrace : UnitalTracialFunctional (Matrix (Fin 2) (Fin 2) ℝ) :=
  matrixUnitalTrace (Fin 2)

/-- Concrete zero-binder T17 witness for `FiniteFaithfulStarTrace`. -/
def matrix2StarTrace : FiniteFaithfulStarTrace (Matrix (Fin 2) (Fin 2) ℝ) :=
  matrixStarTrace (Fin 2)

/-- Concrete zero-binder T17 witness for `IdempotentFaithfulTrace`. -/
def matrix2IdempotentFaithfulTrace : IdempotentFaithfulTrace (Matrix (Fin 2) (Fin 2) ℝ) :=
  matrixIdempotentFaithfulTrace (Fin 2)

/-- Concrete zero-binder T17 witness separating `Matrix (Fin 2) (Fin 2) ℝ`
from `Module.End ℝ (ℕ → ℝ)`. -/
def canonicalFiniteTraceVsTypeIIISeparation :
    FiniteTraceBKMVsTypeIIISeparation (Fin 2) (Module.End ℝ (ℕ → ℝ)) where
  bkmContext := concreteRealTwoSheetBKMContext
  finiteStarTrace := matrix2StarTrace
  finiteIdemTrace := matrix2IdempotentFaithfulTrace
  infLeft := natSeqLeftShift
  infRight := natSeqRightShift
  inf_one_sided_left := natSeqLeftShift_mul_rightShift
  inf_one_sided_right_ne := natSeqRightShift_mul_leftShift_ne
  halvingU₁ := natSeqEvenExtract
  halvingV₁ := natSeqEvenEmbed
  halvingU₂ := natSeqOddExtract
  halvingV₂ := natSeqOddEmbed
  halving_one := natSeqEvenExtract_mul_evenEmbed
  halving_two := natSeqOddExtract_mul_oddEmbed
  halving_sum := natSeqEven_add_odd_proj_eq_one

/-- Concrete T16 noncommutativity witness for `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem matrix2_noncommuting_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨!![0, 1; 1, 0], !![1, 1; 1, 0], ?_⟩
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hentry

end InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetBKMReal
