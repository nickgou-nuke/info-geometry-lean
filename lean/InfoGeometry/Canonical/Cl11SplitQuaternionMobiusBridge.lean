/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors.
-/
import InfoGeometry.BottPeriodicityReconciliation
import InfoGeometry.Geometry.RealMoebiusAction
import InfoGeometry.Topology.MobiusGeometry
import Mathlib.Topology.Constructions

/-!
# The split-quaternion shadow of `Cl(1,1)`

The existing `BottPeriodicityReconciliation` owner supplies the real matrix
model of `Cl(1,1)`.  We expose its four basis elements with the conventional
split-quaternion names:

* `splitI` squares to `-1`;
* `splitL` squares to `+1`;
* `splitI` and `splitL` anticommute;
* `splitIL` is their product;
* `splitL + splitI` is a nonzero square-zero (parabolic/null) element.

This is the algebraic content needed before any Möbius-flow interpretation;
no analytic classification is inferred here.
-/

namespace InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge

open Matrix
open BottPeriodicityReconciliation

abbrev SplitQuaternion := Matrix (Fin 2) (Fin 2) ℝ

def splitOne : SplitQuaternion := I2

def splitI : SplitQuaternion := epsilon

def splitL : SplitQuaternion := sigma1

def splitIL : SplitQuaternion := splitI * splitL

def splitNull : SplitQuaternion := splitL + splitI

/-- Standard `sl₂` basis element `H` in the split-quaternion matrix model. -/
def splitLieH : SplitQuaternion := splitL

/-- Standard `sl₂` raising operator `E` in the split-quaternion matrix model. -/
noncomputable def splitLieE : SplitQuaternion := (1 / 2 : ℝ) • (splitIL - splitI)

/-- Standard `sl₂` lowering operator `F` in the split-quaternion matrix model. -/
noncomputable def splitLieF : SplitQuaternion := (1 / 2 : ℝ) • (splitIL + splitI)

theorem splitI_sq : splitI * splitI = -splitOne := by
  exact cl11_generator_relations.2.1

theorem splitL_sq : splitL * splitL = splitOne := by
  exact cl11_generator_relations.1

theorem splitI_splitL_anticommute :
    splitI * splitL + splitL * splitI = 0 := by
  simpa [add_comm] using cl11_generator_relations.2.2

theorem splitI_splitL_commutator :
    splitI * splitL - splitL * splitI = (2 : ℝ) • splitIL := by
  rw [show splitIL = splitI * splitL by rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitIL, splitI, splitL, epsilon, sigma1,
      InfoGeometryCore.sigma1R, InfoGeometryCore.sigma3R,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem splitL_splitIL_commutator :
    splitL * splitIL - splitIL * splitL = (-2 : ℝ) • splitI := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitIL, splitI, splitL, epsilon, sigma1,
      InfoGeometryCore.sigma1R, InfoGeometryCore.sigma3R,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem splitIL_splitI_commutator :
    splitIL * splitI - splitI * splitIL = (2 : ℝ) • splitL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitIL, splitI, splitL, epsilon, sigma1,
      InfoGeometryCore.sigma1R, InfoGeometryCore.sigma3R,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem splitLieH_splitLieE_commutator :
    splitLieH * splitLieE - splitLieE * splitLieH = (2 : ℝ) • splitLieE := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitLieH, splitLieE, splitIL, splitI, splitL, epsilon, sigma1,
      InfoGeometryCore.sigma1R, InfoGeometryCore.sigma3R,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem splitLieH_splitLieF_commutator :
    splitLieH * splitLieF - splitLieF * splitLieH = (-2 : ℝ) • splitLieF := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitLieH, splitLieF, splitIL, splitI, splitL, epsilon, sigma1,
      InfoGeometryCore.sigma1R, InfoGeometryCore.sigma3R,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem splitLieE_splitLieF_commutator :
    splitLieE * splitLieF - splitLieF * splitLieE = splitLieH := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitLieH, splitLieE, splitLieF, splitIL, splitI, splitL,
      epsilon, sigma1, InfoGeometryCore.sigma1R, InfoGeometryCore.sigma3R,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The split-quaternion Lie closure matches the standard `sl₂` commutator
table after the usual linear change of basis. -/
theorem splitLie_sl2_table :
    splitLieH * splitLieE - splitLieE * splitLieH = (2 : ℝ) • splitLieE ∧
    splitLieH * splitLieF - splitLieF * splitLieH = (-2 : ℝ) • splitLieF ∧
    splitLieE * splitLieF - splitLieF * splitLieE = splitLieH := by
  refine ⟨splitLieH_splitLieE_commutator, ?_, ?_⟩
  · exact splitLieH_splitLieF_commutator
  · exact splitLieE_splitLieF_commutator

theorem splitIL_eq_sigma3 : splitIL = sigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitIL, splitI, splitL, epsilon, sigma1,
      InfoGeometryCore.sigma1R, InfoGeometryCore.sigma3R,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem splitIL_sq : splitIL * splitIL = splitOne := by
  rw [splitIL_eq_sigma3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [splitOne, I2, sigma3, InfoGeometryCore.sigma3R,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem splitNull_sq : splitNull * splitNull = 0 := by
  calc
    splitNull * splitNull =
        splitL * splitL + (splitL * splitI + splitI * splitL) +
          splitI * splitI := by
            simp only [splitNull, add_mul, mul_add]
            abel
    _ = 0 := by
      have hcross : splitL * splitI + splitI * splitL = 0 := by
        simpa [add_comm] using splitI_splitL_anticommute
      rw [splitL_sq, splitI_sq, hcross]
      simp [splitOne]

theorem splitNull_ne_zero : splitNull ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : SplitQuaternion => A 0 1) h
  norm_num [splitNull, splitL, splitI, sigma1, InfoGeometryCore.sigma1R,
    epsilon] at hentry

/-- The unipotent 1-parameter family generated by a matrix `N`: `U(t) = 1 + t • N`. -/
def unipotentFlow (N : SplitQuaternion) (t : ℝ) : SplitQuaternion :=
  splitOne + t • N

/-- For any nilpotent generator `N² = 0`, the unipotent family satisfies `U(s) * U(t) = U(s + t)`. -/
theorem unipotentFlow_add (N : SplitQuaternion) (hN : N * N = 0) (s t : ℝ) :
    unipotentFlow N s * unipotentFlow N t = unipotentFlow N (s + t) := by
  unfold unipotentFlow
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hN, smul_zero, add_zero]
  have hone : splitOne * splitOne = splitOne := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitOne, I2, Matrix.mul_apply, Fin.sum_univ_two]
  have hleft : N * splitOne = N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitOne, I2, Matrix.mul_apply, Fin.sum_univ_two]
  have hright : splitOne * N = N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [splitOne, I2, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hone, hleft, hright]
  rw [add_assoc, ← add_smul]

/-- The unipotent identity element `U(0) = 1`. -/
theorem unipotentFlow_zero (N : SplitQuaternion) :
    unipotentFlow N 0 = splitOne := by
  unfold unipotentFlow
  simp

/-- **The Inverse Law for the Unipotent Family**: `U(−t) · U(t) = 1` and `U(t) · U(−t) = 1`. -/
theorem unipotentFlow_inv_law (N : SplitQuaternion) (hN : N * N = 0) (t : ℝ) :
    unipotentFlow N (-t) * unipotentFlow N t = splitOne ∧
    unipotentFlow N t * unipotentFlow N (-t) = splitOne := by
  constructor
  · rw [unipotentFlow_add N hN, neg_add_cancel, unipotentFlow_zero]
  · rw [unipotentFlow_add N hN, add_neg_cancel, unipotentFlow_zero]

/-- The unipotent flow generated by the split null element `splitNull`: `U_null(t) = 1 + t • splitNull`. -/
def splitNullUnipotentFlow (t : ℝ) : SplitQuaternion :=
  unipotentFlow splitNull t

/-- **Unipotent Inverse Law for the Null Element**: `U_null(−t) · U_null(t) = 1` and `U_null(t) · U_null(−t) = 1`. -/
theorem splitNull_unipotentFlow_inverse_law (t : ℝ) :
    splitNullUnipotentFlow (-t) * splitNullUnipotentFlow t = splitOne ∧
    splitNullUnipotentFlow t * splitNullUnipotentFlow (-t) = splitOne :=
  unipotentFlow_inv_law splitNull splitNull_sq t

theorem splitQuaternion_basis_span (A : SplitQuaternion) :
    ∃ (a b c d : ℝ),
      A = a • splitOne + b • splitL + c • splitI + d • splitIL := by
  obtain ⟨a, b, c, d, h⟩ := cl11_basis_spans_M2 A
  refine ⟨a, b, c, d, ?_⟩
  rw [splitIL_eq_sigma3]
  exact h

inductive MobiusDiscriminantClass
  | elliptic
  | parabolic
  | hyperbolic
  deriving DecidableEq, Repr

instance : TopologicalSpace MobiusDiscriminantClass := ⊥

instance : DiscreteTopology MobiusDiscriminantClass := ⟨rfl⟩

/- The trace convention for a `2 × 2` matrix, written without depending on
   an imported generic trace namespace.  This is the scalar trace used by the
   finite characteristic-polynomial discriminant below. -/
def splitTrace (A : SplitQuaternion) : ℝ :=
  A 0 0 + A 1 1

theorem two_by_two_cayley_hamilton (A : SplitQuaternion) :
    A * A - splitTrace A • A + A.det • splitOne = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTrace, splitOne, I2, Matrix.det_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
  <;> ring

theorem splitNull_trace_zero : splitTrace splitNull = 0 := by
  norm_num [splitTrace, splitNull, splitL, splitI, sigma1,
    InfoGeometryCore.sigma1R, epsilon]

theorem splitNull_det_zero : splitNull.det = 0 := by
  norm_num [splitNull, splitL, splitI, sigma1,
    InfoGeometryCore.sigma1R, epsilon, Matrix.det_fin_two]

theorem splitNull_cayley_hamilton_reduces_to_nilpotency :
    splitNull * splitNull = 0 := by
  have h := two_by_two_cayley_hamilton splitNull
  rw [splitNull_trace_zero, splitNull_det_zero] at h
  simpa using h

def mobiusDiscriminant (A : SplitQuaternion) : ℝ :=
  (splitTrace A) ^ 2 - 4 * A.det

theorem splitNull_mobiusDiscriminant_zero :
    mobiusDiscriminant splitNull = 0 := by
  simp [mobiusDiscriminant, splitNull_trace_zero, splitNull_det_zero]

/- The cross-multiplied finite fixed-point equation for the real fractional
   linear expression associated with `A`.  This is deliberately an algebraic
   polynomial: the projective pole case is handled by the separate sphere
   owner, not silently folded into this definition. -/
def fixedPointEquation (A : SplitQuaternion) (z : ℝ) : ℝ :=
  A 1 0 * z ^ 2 + (A 1 1 - A 0 0) * z - A 0 1

theorem fixedPointEquation_eq_crossMultiplied (A : SplitQuaternion) (z : ℝ) :
    fixedPointEquation A z =
      z * (A 1 0 * z + A 1 1) - (A 0 0 * z + A 0 1) := by
  unfold fixedPointEquation
  ring

theorem fixedPointEquation_discriminant_eq_mobiusDiscriminant
    (A : SplitQuaternion) :
    (A 1 1 - A 0 0) ^ 2 - 4 * A 1 0 * (-A 0 1) =
      mobiusDiscriminant A := by
  simp [mobiusDiscriminant, splitTrace, Matrix.det_fin_two]
  ring

/- The complex `MobiusTransform` owner uses the same quadratic fixed-point
   coefficients.  This identity is the exact algebraic bridge; it does not
   assert a real sign classification for complex coefficients. -/
theorem mobiusTransform_discriminant_eq_fixedPoint_discriminant
    (M : InfoGeometry.MobiusTransform) :
    (M.d - M.a) ^ 2 - 4 * M.c * (-M.b) =
      M.discriminant := by
  unfold InfoGeometry.MobiusTransform.discriminant
  ring

noncomputable def toComplexMobius (A : SplitQuaternion) (hdet : A.det ≠ 0) :
    InfoGeometry.MobiusTransform :=
  { a := A 0 0
    b := A 0 1
    c := A 1 0
    d := A 1 1
    det_ne_zero := by
      have hdet' : ((A.det : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hdet
      simpa [Matrix.det_fin_two] using hdet' }

theorem toComplexMobius_discriminant_eq_cast
    (A : SplitQuaternion) (hdet : A.det ≠ 0) :
    (toComplexMobius A hdet).discriminant = (mobiusDiscriminant A : ℂ) := by
  unfold toComplexMobius InfoGeometry.MobiusTransform.discriminant
  simp [mobiusDiscriminant, splitTrace, Matrix.det_fin_two]

/- The determinant and discriminant of a representative both scale under a
   change of matrix representative.  Their quotient is therefore the natural
   finite, projective normalization (when the representative is invertible).
   We keep this at representative level: the quotient owner uses function
   equivalence, and descent from that relation requires a separate
   proportionality theorem. -/
def mobiusDet (M : InfoGeometry.MobiusTransform) : ℂ :=
  M.a * M.d - M.b * M.c

noncomputable def normalizedMobiusDiscriminant (M : InfoGeometry.MobiusTransform) : ℂ :=
  M.discriminant / (4 * mobiusDet M)

noncomputable def scaleMobius (M : InfoGeometry.MobiusTransform)
    (lam : ℂ) (hlam : lam ≠ 0) : InfoGeometry.MobiusTransform :=
  { a := lam * M.a
    b := lam * M.b
    c := lam * M.c
    d := lam * M.d
    det_ne_zero := by
      dsimp [mobiusDet]
      have hscale :
          lam * M.a * (lam * M.d) - lam * M.b * (lam * M.c) =
            (lam * lam) * (M.a * M.d - M.b * M.c) := by ring
      rw [hscale]
      exact mul_ne_zero (mul_ne_zero hlam hlam) M.det_ne_zero }

theorem scaleMobius_equiv (M : InfoGeometry.MobiusTransform)
    (lam : ℂ) (hlam : lam ≠ 0) :
    InfoGeometry.MobiusTransform.equiv M (scaleMobius M lam hlam) := by
  simpa [scaleMobius] using InfoGeometry.pgl_equivalence M lam hlam

theorem equiv_comp_inv_is_identity
    {M N : InfoGeometry.MobiusTransform}
    (h : InfoGeometry.MobiusTransform.equiv M N) :
    ∀ z, (InfoGeometry.comp (InfoGeometry.inv M) N).eval z = z := by
  intro z
  rw [InfoGeometry.eval_comp, ← h z]
  exact InfoGeometry.eval_inv_left M z

theorem identity_mobius_matrix_is_scalar
    (C : InfoGeometry.MobiusTransform)
    (hidentity : ∀ z, C.eval z = z) :
    ∃ lam : ℂ, lam ≠ 0 ∧ C.a = lam ∧ C.b = 0 ∧ C.c = 0 ∧ C.d = lam := by
  have hc : C.c = 0 := by
    by_contra hc
    have hInf := hidentity (none : InfoGeometry.RiemannSphere)
    simpa [InfoGeometry.MobiusTransform.eval, hc] using hInf
  have hd : C.d ≠ 0 := by
    intro hd
    apply C.det_ne_zero
    simp [hc, hd]
  have hb : C.b = 0 := by
    have hzero := hidentity (some 0 : InfoGeometry.RiemannSphere)
    have hsome : some (C.b / C.d) = some 0 := by
      convert hzero using 1 <;>
        simp [InfoGeometry.MobiusTransform.eval, hc, hd]
    have hratio : C.b / C.d = 0 := Option.some.inj hsome
    exact (div_eq_zero_iff.mp hratio).resolve_right hd
  have ha : C.a ≠ 0 := by
    intro ha
    apply C.det_ne_zero
    simp [hc, hb, ha]
  have had : C.a = C.d := by
    have hone := hidentity (some 1 : InfoGeometry.RiemannSphere)
    have hsome : some (C.a / C.d) = some 1 := by
      convert hone using 1 <;>
        simp [InfoGeometry.MobiusTransform.eval, hc, hb, hd]
    have hratio : C.a / C.d = 1 := Option.some.inj hsome
    simpa using (div_eq_iff hd).mp hratio
  refine ⟨C.a, ha, rfl, hb, hc, ?_⟩
  exact had.symm

theorem mobiusDet_scaleMobius (M : InfoGeometry.MobiusTransform)
    (lam : ℂ) (hlam : lam ≠ 0) :
    mobiusDet (scaleMobius M lam hlam) = lam ^ 2 * mobiusDet M := by
  unfold scaleMobius mobiusDet
  dsimp
  ring

theorem mobiusDiscriminant_scaleMobius (M : InfoGeometry.MobiusTransform)
    (lam : ℂ) (hlam : lam ≠ 0) :
    (scaleMobius M lam hlam).discriminant =
      lam ^ 2 * M.discriminant := by
  unfold scaleMobius InfoGeometry.MobiusTransform.discriminant
  dsimp
  ring

theorem normalizedMobiusDiscriminant_scale_invariant
    (M : InfoGeometry.MobiusTransform) (lam : ℂ) (hlam : lam ≠ 0) :
    normalizedMobiusDiscriminant (scaleMobius M lam hlam) =
      normalizedMobiusDiscriminant M := by
  unfold normalizedMobiusDiscriminant
  rw [mobiusDiscriminant_scaleMobius, mobiusDet_scaleMobius]
  have hdet : mobiusDet M ≠ 0 := M.det_ne_zero
  field_simp [hlam, hdet]

theorem normalizedMobiusDiscriminant_eq_trace_det_normalization
    (M : InfoGeometry.MobiusTransform) :
    normalizedMobiusDiscriminant M =
      ((M.a + M.d) ^ 2 / (4 * mobiusDet M)) - 1 := by
  unfold normalizedMobiusDiscriminant mobiusDet
  unfold InfoGeometry.MobiusTransform.discriminant
  have hdet : M.a * M.d - M.b * M.c ≠ 0 := M.det_ne_zero
  field_simp [hdet]

def toRealMobius (A : SplitQuaternion) (hdet : A.det ≠ 0) :
    InfoGeometry.RealMobiusTransform :=
  { a := A 0 0
    b := A 0 1
    c := A 1 0
    d := A 1 1
    det_ne_zero := by
      simpa [Matrix.det_fin_two] using hdet }

theorem toRealMobius_eval_eq_self_iff
    (A : SplitQuaternion) (hdet : A.det ≠ 0) (x : ℝ)
    (hden : A 1 0 * x + A 1 1 ≠ 0) :
    (toRealMobius A hdet).eval x = x ↔ fixedPointEquation A x = 0 := by
  unfold toRealMobius InfoGeometry.RealMobiusTransform.eval fixedPointEquation
  rw [div_eq_iff hden]
  ring_nf
  constructor <;> intro h
  · nlinarith [h]
  · nlinarith [h]

theorem fixedPointEquation_denominator_ne_zero
    (A : SplitQuaternion) (hdet : A.det ≠ 0) (x : ℝ)
    (hx : fixedPointEquation A x = 0) :
    A 1 0 * x + A 1 1 ≠ 0 := by
  intro hden
  have hlin : A 0 0 * x + A 0 1 = 0 := by
    calc
      A 0 0 * x + A 0 1 =
          -(fixedPointEquation A x) + x * (A 1 0 * x + A 1 1) := by
            unfold fixedPointEquation
            ring
      _ = 0 := by rw [hx, hden]; ring
  apply hdet
  rw [Matrix.det_fin_two]
  have hd : A 1 1 = -(A 1 0 * x) :=
    eq_neg_of_add_eq_zero_right hden
  rw [hd]
  calc
    A 0 0 * -(A 1 0 * x) - A 0 1 * A 1 0 =
        -A 1 0 * (A 0 0 * x + A 0 1) := by ring
    _ = 0 := by rw [hlin]; ring

theorem fixedPointEquation_root_is_realMobius_fixed
    (A : SplitQuaternion) (hdet : A.det ≠ 0) (x : ℝ)
    (hx : fixedPointEquation A x = 0) :
    (toRealMobius A hdet).eval x = x := by
  apply (toRealMobius_eval_eq_self_iff A hdet x
    (fixedPointEquation_denominator_ne_zero A hdet x hx)).2
  exact hx

theorem quadratic_no_real_root_of_discriminant_neg
    (a b c : ℝ) (hΔ : b ^ 2 - 4 * a * c < 0) :
    ∀ x : ℝ, a * x ^ 2 + b * x + c ≠ 0 := by
  intro x hx
  have hidentity : (2 * a * x + b) ^ 2 = b ^ 2 - 4 * a * c := by
    calc
      (2 * a * x + b) ^ 2 =
          4 * a * (a * x ^ 2 + b * x + c) + (b ^ 2 - 4 * a * c) := by ring
      _ = b ^ 2 - 4 * a * c := by rw [hx]; ring
  have hnonneg : 0 ≤ (2 * a * x + b) ^ 2 := sq_nonneg _
  nlinarith

theorem quadratic_two_real_roots_of_discriminant_pos
    (a b c : ℝ) (ha : a ≠ 0) (hΔ : 0 < b ^ 2 - 4 * a * c) :
    ∃ x y : ℝ,
      x ≠ y ∧
      a * x ^ 2 + b * x + c = 0 ∧
      a * y ^ 2 + b * y + c = 0 := by
  let s : ℝ := Real.sqrt (b ^ 2 - 4 * a * c)
  have hs : s ^ 2 = b ^ 2 - 4 * a * c := by
    dsimp [s]
    exact Real.sq_sqrt hΔ.le
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hΔ
  have htwoa : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  refine ⟨(-b + s) / (2 * a), (-b - s) / (2 * a), ?_, ?_, ?_⟩
  · intro hxy
    field_simp [htwoa] at hxy
    nlinarith
  · field_simp [htwoa]
    nlinarith [hs]
  · field_simp [htwoa]
    ring_nf
    nlinarith [hs]

theorem quadratic_real_root_of_discriminant_zero
    (a b c : ℝ) (ha : a ≠ 0) (hΔ : b ^ 2 - 4 * a * c = 0) :
    ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
  have htwoa : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
  refine ⟨-b / (2 * a), ?_⟩
  field_simp [htwoa]
  nlinarith [hΔ]

theorem fixedPointEquation_no_real_root_of_discriminant_neg
    (A : SplitQuaternion) (hΔ : mobiusDiscriminant A < 0) :
    ∀ x : ℝ, fixedPointEquation A x ≠ 0 := by
  intro x
  have hquad :
      (A 1 1 - A 0 0) ^ 2 - 4 * A 1 0 * (-A 0 1) < 0 := by
    rw [fixedPointEquation_discriminant_eq_mobiusDiscriminant A]
    exact hΔ
  exact quadratic_no_real_root_of_discriminant_neg
    (a := A 1 0) (b := A 1 1 - A 0 0) (c := -A 0 1) hquad x

theorem fixedPointEquation_two_real_roots_of_discriminant_pos
    (A : SplitQuaternion) (ha : A 1 0 ≠ 0)
    (hΔ : 0 < mobiusDiscriminant A) :
    ∃ x y : ℝ,
      x ≠ y ∧ fixedPointEquation A x = 0 ∧ fixedPointEquation A y = 0 := by
  obtain ⟨x, y, hxy, hx, hy⟩ :=
    quadratic_two_real_roots_of_discriminant_pos
      (a := A 1 0) (b := A 1 1 - A 0 0) (c := -A 0 1) ha (by
        rw [fixedPointEquation_discriminant_eq_mobiusDiscriminant A]
        exact hΔ)
  exact ⟨x, y, hxy, by simpa [fixedPointEquation] using hx,
    by simpa [fixedPointEquation] using hy⟩

theorem fixedPointEquation_real_root_of_discriminant_zero
    (A : SplitQuaternion) (ha : A 1 0 ≠ 0)
    (hΔ : mobiusDiscriminant A = 0) :
    ∃ x : ℝ, fixedPointEquation A x = 0 := by
  obtain ⟨x, hx⟩ :=
    quadratic_real_root_of_discriminant_zero
      (a := A 1 0) (b := A 1 1 - A 0 0) (c := -A 0 1) ha (by
        rw [fixedPointEquation_discriminant_eq_mobiusDiscriminant A]
        exact hΔ)
  exact ⟨x, by simpa [fixedPointEquation] using hx⟩

noncomputable def classifyMobiusDiscriminant (A : SplitQuaternion) :
    MobiusDiscriminantClass :=
  if mobiusDiscriminant A < 0 then
    .elliptic
  else if mobiusDiscriminant A = 0 then
    .parabolic
  else
    .hyperbolic

theorem classifyMobiusDiscriminant_trichotomy (A : SplitQuaternion) :
    classifyMobiusDiscriminant A = .elliptic ∨
      classifyMobiusDiscriminant A = .parabolic ∨
      classifyMobiusDiscriminant A = .hyperbolic := by
  unfold classifyMobiusDiscriminant
  by_cases hneg : mobiusDiscriminant A < 0
  · exact Or.inl (by simp [hneg])
  · have hnonneg : 0 ≤ mobiusDiscriminant A := le_of_not_gt hneg
    by_cases hzero : mobiusDiscriminant A = 0
    · exact Or.inr (Or.inl (by simp [hzero]))
    · have hpos : 0 < mobiusDiscriminant A :=
        lt_of_le_of_ne hnonneg (by
          intro h
          exact hzero h.symm)
      exact Or.inr (Or.inr (by simp [hneg, hzero]))

theorem classifyMobiusDiscriminant_eq_elliptic_iff (A : SplitQuaternion) :
    classifyMobiusDiscriminant A = .elliptic ↔
      mobiusDiscriminant A < 0 := by
  unfold classifyMobiusDiscriminant
  by_cases hneg : mobiusDiscriminant A < 0
  · simp [hneg]
  · by_cases hzero : mobiusDiscriminant A = 0 <;> simp [hneg, hzero]

theorem classifyMobiusDiscriminant_eq_parabolic_iff (A : SplitQuaternion) :
    classifyMobiusDiscriminant A = .parabolic ↔
      mobiusDiscriminant A = 0 := by
  unfold classifyMobiusDiscriminant
  by_cases hneg : mobiusDiscriminant A < 0
  · by_cases hzero : mobiusDiscriminant A = 0 <;> simp [hneg, hzero]
  · by_cases hzero : mobiusDiscriminant A = 0 <;> simp [hneg, hzero]

theorem classifyMobiusDiscriminant_eq_hyperbolic_iff (A : SplitQuaternion) :
    classifyMobiusDiscriminant A = .hyperbolic ↔
      0 < mobiusDiscriminant A := by
  unfold classifyMobiusDiscriminant
  by_cases hneg : mobiusDiscriminant A < 0
  · have hnotpos : ¬ 0 < mobiusDiscriminant A :=
      not_lt_of_ge (le_of_lt hneg)
    simp [hneg, hnotpos]
  · have hnonneg : 0 ≤ mobiusDiscriminant A := le_of_not_gt hneg
    by_cases hzero : mobiusDiscriminant A = 0
    · simp [hzero]
    · have hpos : 0 < mobiusDiscriminant A :=
        lt_of_le_of_ne hnonneg (by
          intro h
          exact hzero h.symm)
      simp [hneg, hzero, hpos]

theorem splitNull_classify_parabolic :
    classifyMobiusDiscriminant splitNull = .parabolic := by
  exact (classifyMobiusDiscriminant_eq_parabolic_iff splitNull).2
    splitNull_mobiusDiscriminant_zero

/- The determinant-normalized real discriminant is the finite matrix version of
   `Δ/(4 det)`.  The determinant-one specialization is the familiar
   `(trace/2)^2 - 1` expression. -/
noncomputable def normalizedSplitDiscriminant (A : SplitQuaternion) : ℝ :=
  mobiusDiscriminant A / (4 * A.det)

theorem normalizedSplitDiscriminant_det_one
    (A : SplitQuaternion) (hdet : A.det = 1) :
    normalizedSplitDiscriminant A = (splitTrace A) ^ 2 / 4 - 1 := by
  simp [normalizedSplitDiscriminant, mobiusDiscriminant, hdet]
  ring

/- The repository's existing upper-half-plane owner already supplies the
   genuine `SL(2,ℝ)` action.  This theorem is the algebraic compatibility
   edge: on that special-linear subgroup, the determinant-normalized
   discriminant is exactly `trace^2 - 4`. -/
theorem classifyMobiusDiscriminant_eq_parabolic_iff_normalizedSplitDiscriminant_eq_zero
    (A : SplitQuaternion) (hdet : A.det ≠ 0) :
    classifyMobiusDiscriminant A = .parabolic ↔
      normalizedSplitDiscriminant A = 0 := by
  rw [classifyMobiusDiscriminant_eq_parabolic_iff]
  unfold normalizedSplitDiscriminant
  have hden : (4 : ℝ) * A.det ≠ 0 :=
    mul_ne_zero (by norm_num) hdet
  exact ((div_eq_zero_iff).trans (or_iff_left hden)).symm

def sl2Discriminant (g : InfoGeometry.Geometry.SL2R) : ℝ :=
  mobiusDiscriminant (g : SplitQuaternion)

theorem sl2Discriminant_eq_trace_sq_sub_four
    (g : InfoGeometry.Geometry.SL2R) :
    sl2Discriminant g = (splitTrace (g : SplitQuaternion)) ^ 2 - 4 := by
  unfold sl2Discriminant mobiusDiscriminant
  have hdet : (g : SplitQuaternion).det = 1 := by
    exact Matrix.SpecialLinearGroup.det_coe g
  rw [hdet]
  ring

theorem sl2_parabolic_iff_trace_sq_eq_four
    (g : InfoGeometry.Geometry.SL2R) :
    classifyMobiusDiscriminant (g : SplitQuaternion) = .parabolic ↔
      (splitTrace (g : SplitQuaternion)) ^ 2 = 4 := by
  rw [classifyMobiusDiscriminant_eq_parabolic_iff]
  change sl2Discriminant g = 0 ↔ _
  rw [sl2Discriminant_eq_trace_sq_sub_four]
  constructor <;> intro h
  · linarith
  · linarith

theorem sl2_elliptic_iff_trace_sq_lt_four
    (g : InfoGeometry.Geometry.SL2R) :
    classifyMobiusDiscriminant (g : SplitQuaternion) = .elliptic ↔
      (splitTrace (g : SplitQuaternion)) ^ 2 < 4 := by
  rw [classifyMobiusDiscriminant_eq_elliptic_iff]
  change sl2Discriminant g < 0 ↔ _
  rw [sl2Discriminant_eq_trace_sq_sub_four]
  constructor <;> intro h <;> linarith

theorem sl2_hyperbolic_iff_trace_sq_gt_four
    (g : InfoGeometry.Geometry.SL2R) :
    classifyMobiusDiscriminant (g : SplitQuaternion) = .hyperbolic ↔
      4 < (splitTrace (g : SplitQuaternion)) ^ 2 := by
  rw [classifyMobiusDiscriminant_eq_hyperbolic_iff]
  change 0 < sl2Discriminant g ↔ _
  rw [sl2Discriminant_eq_trace_sq_sub_four]
  constructor <;> intro h <;> linarith

theorem continuous_sl2Discriminant :
    Continuous (fun g : InfoGeometry.Geometry.SL2R => sl2Discriminant g) := by
  have heq : (fun g : InfoGeometry.Geometry.SL2R => sl2Discriminant g) =
      (fun g : InfoGeometry.Geometry.SL2R =>
        (splitTrace (g : SplitQuaternion)) ^ 2 - 4) := by
    funext g
    exact sl2Discriminant_eq_trace_sq_sub_four g
  rw [heq]
  unfold splitTrace
  have h00 : Continuous (fun g : InfoGeometry.Geometry.SL2R =>
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) := by
    exact (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)
  have h11 : Continuous (fun g : InfoGeometry.Geometry.SL2R =>
      (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := by
    exact (continuous_apply 1).comp ((continuous_apply 1).comp continuous_subtype_val)
  have htrace : Continuous (fun g : InfoGeometry.Geometry.SL2R =>
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := h00.add h11
  exact (htrace.pow 2).sub continuous_const

def sl2EllipticLocus : Set InfoGeometry.Geometry.SL2R :=
  {g | sl2Discriminant g < 0}

def sl2ParabolicLocus : Set InfoGeometry.Geometry.SL2R :=
  {g | sl2Discriminant g = 0}

def sl2HyperbolicLocus : Set InfoGeometry.Geometry.SL2R :=
  {g | 0 < sl2Discriminant g}

theorem sl2EllipticLocus_isOpen : IsOpen sl2EllipticLocus := by
  exact IsOpen.preimage continuous_sl2Discriminant isOpen_Iio

theorem sl2ParabolicLocus_isClosed : IsClosed sl2ParabolicLocus := by
  exact IsClosed.preimage continuous_sl2Discriminant isClosed_singleton

theorem sl2HyperbolicLocus_isOpen : IsOpen sl2HyperbolicLocus := by
  exact IsOpen.preimage continuous_sl2Discriminant isOpen_Ioi

theorem sl2EllipticLocus_mem_iff
    (g : InfoGeometry.Geometry.SL2R) :
    g ∈ sl2EllipticLocus ↔
      classifyMobiusDiscriminant (g : SplitQuaternion) = .elliptic := by
  change sl2Discriminant g < 0 ↔ _
  change mobiusDiscriminant (g : SplitQuaternion) < 0 ↔ _
  exact (classifyMobiusDiscriminant_eq_elliptic_iff (g : SplitQuaternion)).symm

theorem sl2ParabolicLocus_mem_iff
    (g : InfoGeometry.Geometry.SL2R) :
    g ∈ sl2ParabolicLocus ↔
      classifyMobiusDiscriminant (g : SplitQuaternion) = .parabolic := by
  change sl2Discriminant g = 0 ↔ _
  change mobiusDiscriminant (g : SplitQuaternion) = 0 ↔ _
  exact (classifyMobiusDiscriminant_eq_parabolic_iff (g : SplitQuaternion)).symm

theorem sl2HyperbolicLocus_mem_iff
    (g : InfoGeometry.Geometry.SL2R) :
    g ∈ sl2HyperbolicLocus ↔
      classifyMobiusDiscriminant (g : SplitQuaternion) = .hyperbolic := by
  change 0 < sl2Discriminant g ↔ _
  change 0 < mobiusDiscriminant (g : SplitQuaternion) ↔ _
  exact (classifyMobiusDiscriminant_eq_hyperbolic_iff (g : SplitQuaternion)).symm

theorem sl2_loci_cover (g : InfoGeometry.Geometry.SL2R) :
    g ∈ sl2EllipticLocus ∨ g ∈ sl2ParabolicLocus ∨
      g ∈ sl2HyperbolicLocus := by
  rcases lt_trichotomy (sl2Discriminant g) 0 with hneg | heq | hpos
  · exact Or.inl hneg
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr hpos)

theorem sl2_loci_pairwise_disjoint :
    Disjoint sl2EllipticLocus sl2ParabolicLocus ∧
      Disjoint sl2EllipticLocus sl2HyperbolicLocus ∧
      Disjoint sl2ParabolicLocus sl2HyperbolicLocus := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro g he hp
    change sl2Discriminant g < 0 at he
    change sl2Discriminant g = 0 at hp
    linarith
  · rw [Set.disjoint_left]
    intro g he hh
    change sl2Discriminant g < 0 at he
    change 0 < sl2Discriminant g at hh
    linarith
  · rw [Set.disjoint_left]
    intro g hp hh
    change sl2Discriminant g = 0 at hp
    change 0 < sl2Discriminant g at hh
    linarith

theorem sl2_loci_union_eq_univ :
    sl2EllipticLocus ∪ sl2ParabolicLocus ∪ sl2HyperbolicLocus = Set.univ := by
  ext g
  constructor
  · intro h
    exact Set.mem_univ g
  · intro h
    rcases sl2_loci_cover g with he | hp | hh
    · exact Or.inl (Or.inl he)
    · exact Or.inl (Or.inr hp)
    · exact Or.inr hh

noncomputable def sl2Classify :
    InfoGeometry.Geometry.SL2R → MobiusDiscriminantClass :=
  fun g => classifyMobiusDiscriminant (g : SplitQuaternion)

theorem sl2Classify_preimage_elliptic :
    sl2Classify ⁻¹' ({.elliptic} : Set MobiusDiscriminantClass) =
      sl2EllipticLocus := by
  ext g
  change classifyMobiusDiscriminant (g : SplitQuaternion) = .elliptic ↔ _
  exact (sl2EllipticLocus_mem_iff g).symm

theorem sl2Classify_preimage_parabolic :
    sl2Classify ⁻¹' ({.parabolic} : Set MobiusDiscriminantClass) =
      sl2ParabolicLocus := by
  ext g
  change classifyMobiusDiscriminant (g : SplitQuaternion) = .parabolic ↔ _
  exact (sl2ParabolicLocus_mem_iff g).symm

theorem sl2Classify_preimage_hyperbolic :
    sl2Classify ⁻¹' ({.hyperbolic} : Set MobiusDiscriminantClass) =
      sl2HyperbolicLocus := by
  ext g
  change classifyMobiusDiscriminant (g : SplitQuaternion) = .hyperbolic ↔ _
  exact (sl2HyperbolicLocus_mem_iff g).symm

theorem sl2Classify_eq_elliptic_on_elliptic :
    Set.EqOn sl2Classify (fun _ => .elliptic) sl2EllipticLocus := by
  intro g hg
  change classifyMobiusDiscriminant (g : SplitQuaternion) = .elliptic
  exact (sl2EllipticLocus_mem_iff g).1 hg

theorem sl2Classify_eq_parabolic_on_parabolic :
    Set.EqOn sl2Classify (fun _ => .parabolic) sl2ParabolicLocus := by
  intro g hg
  change classifyMobiusDiscriminant (g : SplitQuaternion) = .parabolic
  exact (sl2ParabolicLocus_mem_iff g).1 hg

theorem sl2Classify_eq_hyperbolic_on_hyperbolic :
    Set.EqOn sl2Classify (fun _ => .hyperbolic) sl2HyperbolicLocus := by
  intro g hg
  change classifyMobiusDiscriminant (g : SplitQuaternion) = .hyperbolic
  exact (sl2HyperbolicLocus_mem_iff g).1 hg

theorem continuousOn_sl2Classify_elliptic :
    ContinuousOn sl2Classify sl2EllipticLocus := by
  exact continuousOn_const.congr sl2Classify_eq_elliptic_on_elliptic

theorem continuousOn_sl2Classify_parabolic :
    ContinuousOn sl2Classify sl2ParabolicLocus := by
  exact continuousOn_const.congr sl2Classify_eq_parabolic_on_parabolic

theorem continuousOn_sl2Classify_hyperbolic :
    ContinuousOn sl2Classify sl2HyperbolicLocus := by
  exact continuousOn_const.congr sl2Classify_eq_hyperbolic_on_hyperbolic

def kleinQuadric : Set SplitQuaternion :=
  {A | A.det = 0}

theorem continuous_splitDet :
    Continuous (fun A : SplitQuaternion => A.det) := by
  have hdet : (fun A : SplitQuaternion => A.det) =
      (fun A : SplitQuaternion =>
        A 0 0 * A 1 1 - A 0 1 * A 1 0) := by
    funext A
    rw [Matrix.det_fin_two]
  rw [hdet]
  fun_prop

theorem kleinQuadric_isClosed : IsClosed kleinQuadric := by
  exact IsClosed.preimage continuous_splitDet isClosed_singleton

theorem splitNull_mem_kleinQuadric : splitNull ∈ kleinQuadric := by
  exact splitNull_det_zero

def nilpotentCone : Set SplitQuaternion :=
  {A | A * A = 0}

theorem continuous_matrixSquare :
    Continuous (fun A : SplitQuaternion => A * A) := by
  exact continuous_mul.comp (continuous_id.prodMk continuous_id)

theorem nilpotentCone_isClosed : IsClosed nilpotentCone := by
  exact IsClosed.preimage continuous_matrixSquare isClosed_singleton

theorem nilpotentCone_subset_kleinQuadric :
    nilpotentCone ⊆ kleinQuadric := by
  intro A hA
  change A.det = 0
  have hdet := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_zero (by infer_instance)] at hdet
  exact mul_self_eq_zero.mp hdet

theorem splitNull_mem_nilpotentCone : splitNull ∈ nilpotentCone := by
  exact splitNull_sq

/- Conjugation by an invertible real matrix preserves both trace and
   determinant, hence preserves the discriminant class. -/
def conjugateSplitMatrix
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    SplitQuaternion :=
  (P : SplitQuaternion) * A * (↑(P⁻¹) : SplitQuaternion)

theorem continuous_conjugateSplitMatrix
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    Continuous (fun A : SplitQuaternion => conjugateSplitMatrix P A) := by
  unfold conjugateSplitMatrix
  exact (continuous_const.mul continuous_id).mul continuous_const

def conjugationAction :
    Matrix.GeneralLinearGroup (Fin 2) ℝ × SplitQuaternion → SplitQuaternion :=
  fun q => conjugateSplitMatrix q.1 q.2

theorem continuous_conjugationAction : Continuous conjugationAction := by
  unfold conjugationAction conjugateSplitMatrix
  have hv : Continuous (fun P : Matrix.GeneralLinearGroup (Fin 2) ℝ =>
      (P : SplitQuaternion)) := Units.continuous_val
  have hP : Continuous (fun q :
      Matrix.GeneralLinearGroup (Fin 2) ℝ × SplitQuaternion =>
      (q.1 : SplitQuaternion)) :=
    hv.comp continuous_fst
  have hA : Continuous (fun q :
      Matrix.GeneralLinearGroup (Fin 2) ℝ × SplitQuaternion => q.2) :=
    continuous_snd
  have hi : Continuous (fun q :
      Matrix.GeneralLinearGroup (Fin 2) ℝ × SplitQuaternion => q.1⁻¹) :=
    continuous_inv.comp continuous_fst
  have hPinv : Continuous (fun q :
      Matrix.GeneralLinearGroup (Fin 2) ℝ × SplitQuaternion =>
      (↑(q.1⁻¹) : SplitQuaternion)) :=
    hv.comp hi
  exact (hP.mul hA).mul hPinv

theorem conjugateSplitMatrix_one (A : SplitQuaternion) :
    conjugateSplitMatrix (1 : Matrix.GeneralLinearGroup (Fin 2) ℝ) A = A := by
  unfold conjugateSplitMatrix
  simp

theorem conjugateSplitMatrix_mul_action
    (P Q : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    conjugateSplitMatrix (P * Q) A = conjugateSplitMatrix P (conjugateSplitMatrix Q A) := by
  have hinv : (↑((P * Q)⁻¹) : SplitQuaternion) =
      (↑(Q⁻¹) : SplitQuaternion) * (↑(P⁻¹) : SplitQuaternion) := by
    simpa using congrArg (fun U : Matrix.GeneralLinearGroup (Fin 2) ℝ =>
      (U : SplitQuaternion))
      (show (P * Q)⁻¹ = Q⁻¹ * P⁻¹ by simp)
  unfold conjugateSplitMatrix
  rw [hinv]
  simp only [Units.val_mul, Matrix.mul_assoc]

theorem splitTrace_conjugateSplitMatrix
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    splitTrace (conjugateSplitMatrix P A) = splitTrace A := by
  unfold splitTrace conjugateSplitMatrix
  rw [← Matrix.trace_fin_two, Matrix.trace_mul_cycle]
  have hcancel :
      (↑(P⁻¹) : SplitQuaternion) * (P : SplitQuaternion) = 1 := by
    exact Units.inv_val P
  rw [hcancel, Matrix.one_mul]
  rw [Matrix.trace_fin_two]

theorem splitDet_conjugateSplitMatrix
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    (conjugateSplitMatrix P A).det = A.det := by
  unfold conjugateSplitMatrix
  rw [Matrix.det_mul, Matrix.det_mul]
  have hcancel :
      (P : SplitQuaternion) * (↑(P⁻¹) : SplitQuaternion) = 1 := by
    exact Units.val_inv P
  have hdet_cancel :
      (P : SplitQuaternion).det * (↑(P⁻¹) : SplitQuaternion).det = 1 := by
    rw [← Matrix.det_mul, hcancel, Matrix.det_one]
  calc
    (P : SplitQuaternion).det * A.det * (↑(P⁻¹) : SplitQuaternion).det =
        ((P : SplitQuaternion).det * (↑(P⁻¹) : SplitQuaternion).det) * A.det := by ring
    _ = A.det := by rw [hdet_cancel, one_mul]

theorem conjugateSplitMatrix_mem_kleinQuadric_iff
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    conjugateSplitMatrix P A ∈ kleinQuadric ↔ A ∈ kleinQuadric := by
  change (conjugateSplitMatrix P A).det = 0 ↔ A.det = 0
  rw [splitDet_conjugateSplitMatrix]

theorem conjugateSplitMatrix_mul
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A B : SplitQuaternion) :
    conjugateSplitMatrix P (A * B) =
      conjugateSplitMatrix P A * conjugateSplitMatrix P B := by
  unfold conjugateSplitMatrix
  have hleft : (↑(P⁻¹) : SplitQuaternion) * (P : SplitQuaternion) = 1 :=
    Units.inv_val P
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (↑(P⁻¹) : SplitQuaternion) (P : SplitQuaternion),
    hleft, Matrix.one_mul]

theorem conjugateSplitMatrix_inv_conjugate
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    conjugateSplitMatrix (P⁻¹) (conjugateSplitMatrix P A) = A := by
  unfold conjugateSplitMatrix
  have hleft : (↑(P⁻¹) : SplitQuaternion) * (P : SplitQuaternion) = 1 :=
    Units.inv_val P
  simp only [inv_inv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (↑(P⁻¹) : SplitQuaternion) (P : SplitQuaternion), hleft]
  simp

theorem conjugateSplitMatrix_mem_nilpotentCone_iff
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    conjugateSplitMatrix P A ∈ nilpotentCone ↔ A ∈ nilpotentCone := by
  constructor
  · intro h
    have hsq : conjugateSplitMatrix P A * conjugateSplitMatrix P A = 0 := h
    have hsq' := congrArg (conjugateSplitMatrix (P⁻¹)) hsq
    rw [← conjugateSplitMatrix_mul, conjugateSplitMatrix_inv_conjugate] at hsq'
    have hz : conjugateSplitMatrix (P⁻¹) 0 = 0 := by
      unfold conjugateSplitMatrix
      simp
    rw [hz] at hsq'
    exact hsq'
  · intro h
    change conjugateSplitMatrix P A * conjugateSplitMatrix P A = 0
    rw [← conjugateSplitMatrix_mul, h]
    unfold conjugateSplitMatrix
    simp

theorem conjugateSplitMatrix_image_kleinQuadric
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    conjugateSplitMatrix P '' kleinQuadric = kleinQuadric := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (conjugateSplitMatrix_mem_kleinQuadric_iff P B).2 hB
  · intro hA
    refine ⟨conjugateSplitMatrix (P⁻¹) A, ?_, ?_⟩
    · exact (conjugateSplitMatrix_mem_kleinQuadric_iff (P⁻¹) A).2 hA
    · simpa using (conjugateSplitMatrix_inv_conjugate (P⁻¹) A)

theorem conjugateSplitMatrix_image_nilpotentCone
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    conjugateSplitMatrix P '' nilpotentCone = nilpotentCone := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (conjugateSplitMatrix_mem_nilpotentCone_iff P B).2 hB
  · intro hA
    refine ⟨conjugateSplitMatrix (P⁻¹) A, ?_, ?_⟩
    · exact (conjugateSplitMatrix_mem_nilpotentCone_iff (P⁻¹) A).2 hA
    · simpa using (conjugateSplitMatrix_inv_conjugate (P⁻¹) A)

def splitNullConjugationOrbit : Set SplitQuaternion :=
  Set.range (fun P : Matrix.GeneralLinearGroup (Fin 2) ℝ =>
    conjugateSplitMatrix P splitNull)

theorem splitNullConjugationOrbit_subset_nilpotentCone :
    splitNullConjugationOrbit ⊆ nilpotentCone := by
  rintro A ⟨P, rfl⟩
  exact (conjugateSplitMatrix_mem_nilpotentCone_iff P splitNull).2
    splitNull_mem_nilpotentCone

theorem splitNullConjugationOrbit_subset_kleinQuadric :
    splitNullConjugationOrbit ⊆ kleinQuadric := by
  rintro A ⟨P, rfl⟩
  exact (conjugateSplitMatrix_mem_kleinQuadric_iff P splitNull).2
    splitNull_mem_kleinQuadric

theorem splitNull_mem_conjugationOrbit :
    splitNull ∈ splitNullConjugationOrbit := by
  refine ⟨1, ?_⟩
  simp [splitNullConjugationOrbit, conjugateSplitMatrix]

def splitNullConjugationStabilizer :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ) where
  carrier := {P | conjugateSplitMatrix P splitNull = splitNull}
  one_mem' := conjugateSplitMatrix_one splitNull
  mul_mem' := by
    intro P Q hP hQ
    change conjugateSplitMatrix P splitNull = splitNull at hP
    change conjugateSplitMatrix Q splitNull = splitNull at hQ
    change conjugateSplitMatrix (P * Q) splitNull = splitNull
    rw [conjugateSplitMatrix_mul_action, hQ, hP]
  inv_mem' := by
    intro P hP
    change conjugateSplitMatrix P splitNull = splitNull at hP
    change conjugateSplitMatrix (P⁻¹) splitNull = splitNull
    have h := congrArg (conjugateSplitMatrix (P⁻¹)) hP
    rw [conjugateSplitMatrix_inv_conjugate] at h
    exact h.symm

theorem mem_splitNullConjugationStabilizer_iff
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    P ∈ splitNullConjugationStabilizer ↔
      conjugateSplitMatrix P splitNull = splitNull := Iff.rfl

theorem mem_splitNullConjugationStabilizer_iff_commutes
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    P ∈ splitNullConjugationStabilizer ↔
      (P : SplitQuaternion) * splitNull =
        splitNull * (P : SplitQuaternion) := by
  constructor
  · intro h
    change conjugateSplitMatrix P splitNull = splitNull at h
    have h' := congrArg (fun X : SplitQuaternion => X * (P : SplitQuaternion)) h
    change ((P : SplitQuaternion) * splitNull *
      (↑(P⁻¹) : SplitQuaternion)) * (P : SplitQuaternion) =
      splitNull * (P : SplitQuaternion) at h'
    simp only [Matrix.mul_assoc] at h'
    have hcancel : (↑(P⁻¹) : SplitQuaternion) * (P : SplitQuaternion) = 1 :=
      Units.inv_val P
    rw [hcancel, Matrix.mul_one] at h'
    exact h'
  · intro h
    change conjugateSplitMatrix P splitNull = splitNull
    unfold conjugateSplitMatrix
    rw [h, Matrix.mul_assoc]
    have hcancel : (P : SplitQuaternion) * (↑(P⁻¹) : SplitQuaternion) = 1 :=
      Units.val_inv P
    rw [hcancel, Matrix.mul_one]

theorem splitNull_stabilizer_coordinate_iff
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    P ∈ splitNullConjugationStabilizer ↔
      (P : SplitQuaternion) 1 0 = 0 ∧
        (P : SplitQuaternion) 1 1 = (P : SplitQuaternion) 0 0 := by
  rw [mem_splitNullConjugationStabilizer_iff_commutes]
  constructor
  · intro h
    have h00 := congrFun (congrFun (congrArg (fun X : SplitQuaternion => X) h) 0) 0
    have h01 := congrFun (congrFun (congrArg (fun X : SplitQuaternion => X) h) 0) 1
    have h10 := congrFun (congrFun (congrArg (fun X : SplitQuaternion => X) h) 1) 0
    have h11 := congrFun (congrFun (congrArg (fun X : SplitQuaternion => X) h) 1) 1
    norm_num [splitNull, splitL, splitI, sigma1, epsilon,
      InfoGeometryCore.sigma1R, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    constructor
    · exact h00
    · linarith [h01]
  · rintro ⟨h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [splitNull, splitL, splitI, sigma1, epsilon,
        InfoGeometryCore.sigma1R, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | exact h10 | linarith [h11] | ring

theorem splitNull_stabilizer_parameterization
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    P ∈ splitNullConjugationStabilizer ↔
      ∃ a b : ℝ, a ≠ 0 ∧
        (P : SplitQuaternion) = !![a, b; 0, a] := by
  constructor
  · intro h
    have hc := (splitNull_stabilizer_coordinate_iff P).1 h
    refine ⟨(P : SplitQuaternion) 0 0, (P : SplitQuaternion) 0 1, ?_, ?_⟩
    · intro ha
      apply P.det_ne_zero
      change Matrix.det (P : SplitQuaternion) = 0
      rw [Matrix.det_fin_two]
      rw [hc.1, hc.2, ha]
      ring
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hc.1, hc.2]
  · rintro ⟨a, b, ha, hP⟩
    apply (splitNull_stabilizer_coordinate_iff P).2
    constructor
    · rw [hP]
      norm_num
    · rw [hP]
      norm_num

theorem splitNull_stabilizer_det_eq_square
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hP : P ∈ splitNullConjugationStabilizer) :
    (P : SplitQuaternion).det = ((P : SplitQuaternion) 0 0) ^ 2 := by
  have hc := (splitNull_stabilizer_coordinate_iff P).1 hP
  rw [Matrix.det_fin_two]
  rw [hc.1, hc.2]
  ring

theorem splitNull_stabilizer_det_pos
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hP : P ∈ splitNullConjugationStabilizer) :
    0 < (P : SplitQuaternion).det := by
  rw [splitNull_stabilizer_det_eq_square P hP]
  apply sq_pos_of_ne_zero
  intro ha
  apply P.det_ne_zero
  change Matrix.det (P : SplitQuaternion) = 0
  rw [Matrix.det_fin_two]
  have hc := (splitNull_stabilizer_coordinate_iff P).1 hP
  rw [hc.1, hc.2, ha]
  ring

noncomputable def splitNullUnipotent (t : ℝ) :
    Matrix.GeneralLinearGroup (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mk'' !![1, t; 0, 1] (by
    rw [Matrix.det_fin_two]
    norm_num)

theorem splitNullUnipotent_coe (t : ℝ) :
    (splitNullUnipotent t : SplitQuaternion) = !![1, t; 0, 1] := rfl

theorem splitNullUnipotent_mem_stabilizer (t : ℝ) :
    splitNullUnipotent t ∈ splitNullConjugationStabilizer := by
  apply (splitNull_stabilizer_parameterization (splitNullUnipotent t)).2
  refine ⟨1, t, one_ne_zero, ?_⟩
  rfl

theorem splitNullUnipotent_conjugates_splitNull (t : ℝ) :
    conjugateSplitMatrix (splitNullUnipotent t) splitNull = splitNull :=
  (mem_splitNullConjugationStabilizer_iff (splitNullUnipotent t)).1
    (splitNullUnipotent_mem_stabilizer t)

theorem splitNullUnipotent_injective :
    Function.Injective splitNullUnipotent := by
  intro s t h
  have hentry := congrArg (fun P : Matrix.GeneralLinearGroup (Fin 2) ℝ =>
    (P : SplitQuaternion) 0 1) h
  simpa [splitNullUnipotent] using hentry

theorem splitNullUnipotent_mul (s t : ℝ) :
    splitNullUnipotent s * splitNullUnipotent t =
      splitNullUnipotent (s + t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitNullUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem splitNullUnipotent_zero :
    splitNullUnipotent 0 = (1 : Matrix.GeneralLinearGroup (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitNullUnipotent]

theorem splitNullUnipotent_inv (t : ℝ) :
    (splitNullUnipotent t)⁻¹ = splitNullUnipotent (-t) := by
  have hprod : splitNullUnipotent t * splitNullUnipotent (-t) =
      (1 : Matrix.GeneralLinearGroup (Fin 2) ℝ) := by
    rw [splitNullUnipotent_mul, show t + -t = 0 by ring,
      splitNullUnipotent_zero]
  calc
    (splitNullUnipotent t)⁻¹ = (splitNullUnipotent t)⁻¹ * 1 := by simp
    _ = (splitNullUnipotent t)⁻¹ *
        (splitNullUnipotent t * splitNullUnipotent (-t)) := by rw [hprod]
    _ = ((splitNullUnipotent t)⁻¹ * splitNullUnipotent t) *
        splitNullUnipotent (-t) := by rw [mul_assoc]
    _ = splitNullUnipotent (-t) := by simp

theorem continuous_unipotentFlow (N : SplitQuaternion) :
    Continuous (fun t : ℝ => unipotentFlow N t) := by
  unfold unipotentFlow
  exact continuous_const.add (continuous_id.smul continuous_const)

theorem continuous_splitNullUnipotentFlow :
    Continuous (fun t : ℝ => splitNullUnipotentFlow t) := by
  exact continuous_unipotentFlow splitNull

theorem splitNull_conjugation_fiber_iff
    (P Q : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    conjugateSplitMatrix P splitNull = conjugateSplitMatrix Q splitNull ↔
      Q⁻¹ * P ∈ splitNullConjugationStabilizer := by
  constructor
  · intro h
    change conjugateSplitMatrix (Q⁻¹ * P) splitNull = splitNull
    rw [conjugateSplitMatrix_mul_action]
    have h' := congrArg (conjugateSplitMatrix (Q⁻¹)) h
    rw [conjugateSplitMatrix_inv_conjugate] at h'
    exact h'
  · intro h
    change conjugateSplitMatrix (Q⁻¹ * P) splitNull = splitNull at h
    have hQP : Q * (Q⁻¹ * P) = P := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    calc
      conjugateSplitMatrix P splitNull =
          conjugateSplitMatrix Q
            (conjugateSplitMatrix (Q⁻¹ * P) splitNull) := by
              rw [← conjugateSplitMatrix_mul_action, hQP]
      _ = conjugateSplitMatrix Q splitNull := by rw [h]

theorem continuous_conjugation_on_splitNull :
    Continuous (fun P : Matrix.GeneralLinearGroup (Fin 2) ℝ =>
      conjugateSplitMatrix P splitNull) := by
  exact continuous_conjugationAction.comp
    (continuous_id.prodMk continuous_const)

/-!
The orbit is represented as a subtype, so the orbit map carries the
subspace topology inherited from `SplitQuaternion`.  This is the native
topological interface used below; no quotient or choice of representatives
is introduced.
-/
def splitNullOrbitMap :
    Matrix.GeneralLinearGroup (Fin 2) ℝ → splitNullConjugationOrbit :=
  fun P => ⟨conjugateSplitMatrix P splitNull, ⟨P, rfl⟩⟩

theorem continuous_splitNullOrbitMap : Continuous splitNullOrbitMap := by
  exact continuous_conjugation_on_splitNull.subtype_mk
    (fun P => ⟨P, rfl⟩)

theorem splitNullOrbitMap_surjective : Function.Surjective splitNullOrbitMap := by
  intro A
  rcases A.property with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  apply Subtype.ext
  change conjugateSplitMatrix P splitNull = (A : SplitQuaternion)
  exact hP

/-! The subtype orbit retains the exact stabilizer-fiber relation of the raw
matrix orbit. -/
theorem splitNullOrbitMap_eq_iff
    (P Q : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    splitNullOrbitMap P = splitNullOrbitMap Q ↔
      Q⁻¹ * P ∈ splitNullConjugationStabilizer := by
  constructor
  · intro h
    apply (splitNull_conjugation_fiber_iff P Q).1
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact (splitNull_conjugation_fiber_iff P Q).2 h

theorem splitNullOrbitMap_eq_base_iff
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    splitNullOrbitMap P = splitNullOrbitMap 1 ↔
      P ∈ splitNullConjugationStabilizer := by
  simpa using (splitNullOrbitMap_eq_iff P 1)

theorem splitNullConjugationOrbit_eq_range_splitNullOrbitMap :
    Set.range (splitNullOrbitMap :
      Matrix.GeneralLinearGroup (Fin 2) ℝ → splitNullConjugationOrbit) = Set.univ := by
  exact Set.range_eq_univ.2 splitNullOrbitMap_surjective

theorem splitNullConjugationStabilizer_isClosed :
    IsClosed (splitNullConjugationStabilizer : Set
      (Matrix.GeneralLinearGroup (Fin 2) ℝ)) := by
  change IsClosed {P : Matrix.GeneralLinearGroup (Fin 2) ℝ |
    conjugateSplitMatrix P splitNull = splitNull}
  exact IsClosed.preimage continuous_conjugation_on_splitNull
    isClosed_singleton

theorem mobiusDiscriminant_conjugateSplitMatrix
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    mobiusDiscriminant (conjugateSplitMatrix P A) = mobiusDiscriminant A := by
  unfold mobiusDiscriminant
  rw [splitTrace_conjugateSplitMatrix P A, splitDet_conjugateSplitMatrix P A]

theorem normalizedSplitDiscriminant_conjugateSplitMatrix
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    normalizedSplitDiscriminant (conjugateSplitMatrix P A) =
      normalizedSplitDiscriminant A := by
  unfold normalizedSplitDiscriminant
  rw [mobiusDiscriminant_conjugateSplitMatrix,
    splitDet_conjugateSplitMatrix]

theorem classifyMobiusDiscriminant_conjugateSplitMatrix
    (P : Matrix.GeneralLinearGroup (Fin 2) ℝ) (A : SplitQuaternion) :
    classifyMobiusDiscriminant (conjugateSplitMatrix P A) =
      classifyMobiusDiscriminant A := by
  unfold classifyMobiusDiscriminant
  rw [mobiusDiscriminant_conjugateSplitMatrix]

noncomputable def discriminantSign (x : ℝ) : ℤ :=
  if x < 0 then -1 else if x = 0 then 0 else 1

@[simp] theorem discriminantSign_of_neg {x : ℝ} (hx : x < 0) :
    discriminantSign x = -1 := by
  simp [discriminantSign, hx]

@[simp] theorem discriminantSign_of_zero {x : ℝ} (hx : x = 0) :
    discriminantSign x = 0 := by
  simp [discriminantSign, hx]

@[simp] theorem discriminantSign_of_pos {x : ℝ} (hx : 0 < x) :
    discriminantSign x = 1 := by
  have hnotneg : ¬ x < 0 := not_lt_of_ge (le_of_lt hx)
  have hneq : x ≠ 0 := ne_of_gt hx
  simp [discriminantSign, hnotneg, hneq]

def mobiusClassSign : MobiusDiscriminantClass → ℤ
  | .elliptic => -1
  | .parabolic => 0
  | .hyperbolic => 1

theorem classifyMobiusDiscriminant_sign (A : SplitQuaternion) :
    mobiusClassSign (classifyMobiusDiscriminant A) =
      discriminantSign (mobiusDiscriminant A) := by
  unfold classifyMobiusDiscriminant
  by_cases hneg : mobiusDiscriminant A < 0
  · simp [hneg, discriminantSign, mobiusClassSign]
  · have hnonneg : 0 ≤ mobiusDiscriminant A := le_of_not_gt hneg
    by_cases hzero : mobiusDiscriminant A = 0
    · simp [hzero, discriminantSign, mobiusClassSign]
    · have hpos : 0 < mobiusDiscriminant A :=
        lt_of_le_of_ne hnonneg (by
          intro h
          exact hzero h.symm)
      simp [hneg, hzero, discriminantSign, mobiusClassSign]

/-! ### Functional coefficient descent

The following lemma isolates the division-free algebra behind the descent from
functional equality of two fractional-linear maps to proportional matrix
coefficients.  Its hypotheses are the three coefficient identities obtained by
cross-multiplication, and the conclusion is the adjugate proportionality
identity with the determinant of the second matrix as scalar.
-/

theorem mobius_functional_equivalence_to_proportionality
    {K : Type*} [Field K]
    (a b c d a' b' c' d' : K)
    (h1 : a * c' = a' * c)
    (h2 : b * d' = b' * d)
    (h3 : a * d' + b * c' = a' * d + b' * c)
    (h_det : a' * d' - b' * c' ≠ 0) :
    let detB := a' * d' - b' * c'
    let lam := a * d' - b * c'
    detB * a = lam * a' ∧
    detB * b = lam * b' ∧
    detB * c = lam * c' ∧
    detB * d = lam * d' := by
  intros detB lam
  have L1_pre :
      (a * b' - a' * b) * (a' * d' - b' * c') =
        b' * b' * (a' * c - a * c') := by
    calc
      (a * b' - a' * b) * (a' * d' - b' * c')
          = a * a' * b' * d' - a * b' * b' * c'
              - a' * a' * (b * d') + a' * b * b' * c' := by ring
      _ = a * a' * b' * d' - a * b' * b' * c'
              - a' * a' * (b' * d) + a' * b * b' * c' := by rw [h2]
      _ = b' * (a' * (a * d' + b * c') - a * b' * c' - a' * a' * d) := by ring
      _ = b' * (a' * (a' * d + b' * c) - a * b' * c' - a' * a' * d) := by rw [h3]
      _ = b' * b' * (a' * c - a * c') := by ring
  have L1_zero :
      (a * b' - a' * b) * (a' * d' - b' * c') = 0 := by
    rw [L1_pre, ← h1]
    ring
  have h_ab : a * b' = a' * b := by
    rcases mul_eq_zero.mp L1_zero with h | h
    · exact sub_eq_zero.mp h
    · exact False.elim (h_det h)
  have L2_pre :
      (c * d' - c' * d) * (a' * d' - b' * c') =
        c' * c' * (b' * d - b * d') := by
    calc
      (c * d' - c' * d) * (a' * d' - b' * c')
          = (a' * c) * d' * d' - c * b' * c' * d'
              - c' * a' * d * d' + c' * b' * c' * d := by ring
      _ = (a * c') * d' * d' - c * b' * c' * d'
              - c' * a' * d * d' + c' * b' * c' * d := by rw [← h1]
      _ = c' * (d' * (a * d' + b * c') - b' * c * d'
              - a' * d * d' - d' * b * c' + b' * c' * d) := by ring
      _ = c' * (d' * (a' * d + b' * c) - b' * c * d'
              - a' * d * d' - d' * b * c' + b' * c' * d) := by rw [h3]
      _ = c' * c' * (b' * d - b * d') := by ring
  have L2_zero :
      (c * d' - c' * d) * (a' * d' - b' * c') = 0 := by
    rw [L2_pre, ← h2]
    ring
  have h_cd : c * d' = c' * d := by
    rcases mul_eq_zero.mp L2_zero with h | h
    · exact sub_eq_zero.mp h
    · exact False.elim (h_det h)
  have L3_pre :
      (b * c' - b' * c) * (a' * d' - b' * c') =
        b' * c' * ((a' * d + b' * c) - (a * d' + b * c')) := by
    calc
      (b * c' - b' * c) * (a' * d' - b' * c')
          = a' * c' * (b * d') - b * b' * c' * c'
              - (a' * c) * b' * d' + b' * b' * c * c' := by ring
      _ = a' * c' * (b' * d) - b * b' * c' * c'
              - (a * c') * b' * d' + b' * b' * c * c' := by rw [h2, ← h1]
      _ = b' * c' * ((a' * d + b' * c) - (a * d' + b * c')) := by ring
  have L3_zero :
      (b * c' - b' * c) * (a' * d' - b' * c') = 0 := by
    rw [L3_pre, ← h3]
    ring
  have h_bc : b * c' = b' * c := by
    rcases mul_eq_zero.mp L3_zero with h | h
    · exact sub_eq_zero.mp h
    · exact False.elim (h_det h)
  have prop_a : detB * a = lam * a' := by
    calc
      detB * a = a * a' * d' - a * b' * c' := by dsimp [detB]; ring
      _ = a * a' * d' - (a' * b) * c' := by rw [← h_ab]
      _ = lam * a' := by dsimp [lam]; ring
  have prop_b : detB * b = lam * b' := by
    calc
      detB * b = a' * b * d' - b * b' * c' := by dsimp [detB]; ring
      _ = (a * b') * d' - b * b' * c' := by rw [h_ab]
      _ = lam * b' := by dsimp [lam]; ring
  have prop_c : detB * c = lam * c' := by
    calc
      detB * c = (a' * c) * d' - (b' * c) * c' := by dsimp [detB]; ring
      _ = (a * c') * d' - (b * c') * c' := by rw [← h1, ← h_bc]
      _ = lam * c' := by dsimp [lam]; ring
  have prop_d : detB * d = lam * d' := by
    calc
      detB * d = a' * d * d' - (b' * d) * c' := by dsimp [detB]; ring
      _ = a' * d * d' - (b * d') * c' := by rw [← h2]
      _ = (a' * d + b' * c) * d' - b' * c * d' - b * c' * d' := by ring
      _ = (a * d' + b * c') * d' - (b * c') * d' - b * c' * d' := by rw [← h3, ← h_bc]
      _ = lam * d' := by dsimp [lam]; ring
  exact ⟨prop_a, prop_b, prop_c, prop_d⟩

/-! The preceding coefficient lemma now descends actual Möbius functional
equivalence.  Composition with the explicit inverse reduces the statement to
the identity-map scalar lemma above; the four determinant identities are then
obtained by direct linear combinations of the resulting matrix entries. -/

theorem mobius_equiv_implies_determinant_proportional
    (M N : InfoGeometry.MobiusTransform)
    (h : InfoGeometry.MobiusTransform.equiv M N) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      (M.a * M.d - M.b * M.c) * N.a = lam * M.a ∧
      (M.a * M.d - M.b * M.c) * N.b = lam * M.b ∧
      (M.a * M.d - M.b * M.c) * N.c = lam * M.c ∧
      (M.a * M.d - M.b * M.c) * N.d = lam * M.d := by
  have hidentity :
      ∀ z, (InfoGeometry.comp (InfoGeometry.inv M) N).eval z = z :=
    equiv_comp_inv_is_identity h
  obtain ⟨lam, hlam, hCa, hCb, hCc, hCd⟩ :=
    identity_mobius_matrix_is_scalar
      (InfoGeometry.comp (InfoGeometry.inv M) N) hidentity
  have hCa' : M.d * N.a - M.b * N.c = lam := by
    simpa [InfoGeometry.comp, InfoGeometry.inv] using hCa
  have hCb' : M.d * N.b - M.b * N.d = 0 := by
    simpa [InfoGeometry.comp, InfoGeometry.inv] using hCb
  have hCc' : -M.c * N.a + M.a * N.c = 0 := by
    simpa [InfoGeometry.comp, InfoGeometry.inv] using hCc
  have hCd' : -M.c * N.b + M.a * N.d = lam := by
    simpa [InfoGeometry.comp, InfoGeometry.inv] using hCd
  have hA : (M.a * M.d - M.b * M.c) * N.a = lam * M.a := by
    calc
      (M.a * M.d - M.b * M.c) * N.a
          = (M.d * N.a - M.b * N.c) * M.a := by
              linear_combination M.b * hCc'
      _ = lam * M.a := by rw [hCa']
  have hB : (M.a * M.d - M.b * M.c) * N.b = lam * M.b := by
    calc
      (M.a * M.d - M.b * M.c) * N.b
          = (-M.c * N.b + M.a * N.d) * M.b := by
              linear_combination M.a * hCb'
      _ = lam * M.b := by rw [hCd']
  have hC : (M.a * M.d - M.b * M.c) * N.c = lam * M.c := by
    calc
      (M.a * M.d - M.b * M.c) * N.c
          = (M.d * N.a - M.b * N.c) * M.c := by
              linear_combination M.d * hCc'
      _ = lam * M.c := by rw [hCa']
  have hD : (M.a * M.d - M.b * M.c) * N.d = lam * M.d := by
    calc
      (M.a * M.d - M.b * M.c) * N.d
          = (-M.c * N.b + M.a * N.d) * M.d := by
              linear_combination M.c * hCb'
      _ = lam * M.d := by rw [hCd']
  exact ⟨lam, hlam, hA, hB, hC, hD⟩

theorem mobius_equiv_implies_scalar_proportional
    (M N : InfoGeometry.MobiusTransform)
    (h : InfoGeometry.MobiusTransform.equiv M N) :
    ∃ k : ℂ, k ≠ 0 ∧ N.a = k * M.a ∧ N.b = k * M.b ∧
      N.c = k * M.c ∧ N.d = k * M.d := by
  obtain ⟨lam, hlam, hA, hB, hC, hD⟩ :=
    mobius_equiv_implies_determinant_proportional M N h
  let detM : ℂ := M.a * M.d - M.b * M.c
  have hdet : detM ≠ 0 := by
    simpa [detM] using M.det_ne_zero
  refine ⟨lam / detM, div_ne_zero hlam hdet, ?_, ?_, ?_, ?_⟩
  · field_simp [hdet]
    simpa [detM, mul_comm, mul_left_comm, mul_assoc] using hA
  · field_simp [hdet]
    simpa [detM, mul_comm, mul_left_comm, mul_assoc] using hB
  · field_simp [hdet]
    simpa [detM, mul_comm, mul_left_comm, mul_assoc] using hC
  · field_simp [hdet]
    simpa [detM, mul_comm, mul_left_comm, mul_assoc] using hD

theorem mobius_equiv_iff_scalar_proportional
    (M N : InfoGeometry.MobiusTransform) :
    InfoGeometry.MobiusTransform.equiv M N ↔
      ∃ k : ℂ, k ≠ 0 ∧ N.a = k * M.a ∧ N.b = k * M.b ∧
        N.c = k * M.c ∧ N.d = k * M.d := by
  constructor
  · exact mobius_equiv_implies_scalar_proportional M N
  · rintro ⟨k, hk, ha, hb, hc, hd⟩
    have hs := InfoGeometry.pgl_equivalence M k hk
    change ∀ z, M.eval z = N.eval z
    simpa [scaleMobius, InfoGeometry.MobiusTransform.eval, ha, hb, hc, hd] using hs

theorem pgl_equal_representatives_imply_scalar_proportional
    (M N : InfoGeometry.MobiusTransform)
    (h : (Quotient.mk' M : InfoGeometry.PGL2C) = Quotient.mk' N) :
    ∃ k : ℂ, k ≠ 0 ∧ N.a = k * M.a ∧ N.b = k * M.b ∧
      N.c = k * M.c ∧ N.d = k * M.d := by
  exact mobius_equiv_implies_scalar_proportional M N (Quotient.exact h)

theorem scalar_proportional_implies_pgl_equal
    (M N : InfoGeometry.MobiusTransform) (k : ℂ) (hk : k ≠ 0)
    (ha : N.a = k * M.a) (hb : N.b = k * M.b)
    (hc : N.c = k * M.c) (hd : N.d = k * M.d) :
    (Quotient.mk' M : InfoGeometry.PGL2C) = Quotient.mk' N := by
  apply Quotient.sound
  have hs := InfoGeometry.pgl_equivalence M k hk
  change ∀ z, M.eval z = N.eval z
  simpa [scaleMobius, InfoGeometry.MobiusTransform.eval, ha, hb, hc, hd] using hs

theorem pgl_equal_iff_scalar_proportional
    (M N : InfoGeometry.MobiusTransform) :
    (Quotient.mk' M : InfoGeometry.PGL2C) = Quotient.mk' N ↔
      ∃ k : ℂ, k ≠ 0 ∧ N.a = k * M.a ∧ N.b = k * M.b ∧
        N.c = k * M.c ∧ N.d = k * M.d := by
  constructor
  · intro h
    exact pgl_equal_representatives_imply_scalar_proportional M N h
  · rintro ⟨k, hk, ha, hb, hc, hd⟩
    exact scalar_proportional_implies_pgl_equal M N k hk ha hb hc hd

theorem normalizedMobiusDiscriminant_eq_of_scalar_proportional
    (M N : InfoGeometry.MobiusTransform) (k : ℂ) (hk : k ≠ 0)
    (ha : N.a = k * M.a) (hb : N.b = k * M.b)
    (hc : N.c = k * M.c) (hd : N.d = k * M.d) :
    normalizedMobiusDiscriminant N = normalizedMobiusDiscriminant M := by
  rw [normalizedMobiusDiscriminant_eq_trace_det_normalization,
    normalizedMobiusDiscriminant_eq_trace_det_normalization]
  have hM : mobiusDet M ≠ 0 := M.det_ne_zero
  have hN : mobiusDet N ≠ 0 := N.det_ne_zero
  unfold mobiusDet
  rw [ha, hb, hc, hd]
  field_simp [hM, hN, hk]

noncomputable def pglNormalizedMobiusDiscriminant : InfoGeometry.PGL2C → ℂ :=
  Quotient.lift normalizedMobiusDiscriminant (by
    intro M N h
    obtain ⟨k, hk, ha, hb, hc, hd⟩ :=
      mobius_equiv_implies_scalar_proportional M N h
    exact (normalizedMobiusDiscriminant_eq_of_scalar_proportional
      M N k hk ha hb hc hd).symm)

@[simp] theorem pglNormalizedMobiusDiscriminant_mk
    (M : InfoGeometry.MobiusTransform) :
    pglNormalizedMobiusDiscriminant (Quotient.mk' M) =
      normalizedMobiusDiscriminant M := by
  rfl

/-! The quotient also carries the canonical quotient topology once the
coefficient topology on representatives is made explicit. -/

def mobiusCoordinates (M : InfoGeometry.MobiusTransform) : ℂ × ℂ × ℂ × ℂ :=
  (M.a, M.b, M.c, M.d)

instance : TopologicalSpace InfoGeometry.MobiusTransform :=
  TopologicalSpace.induced mobiusCoordinates inferInstance

instance : TopologicalSpace InfoGeometry.PGL2C :=
  inferInstanceAs (TopologicalSpace (Quotient InfoGeometry.mobiusSetoid))

theorem continuous_mobiusCoordinates : Continuous mobiusCoordinates :=
  continuous_induced_dom

theorem continuous_pgl_quotient :
    Continuous (Quotient.mk' : InfoGeometry.MobiusTransform → InfoGeometry.PGL2C) :=
  continuous_quotient_mk'

theorem continuous_mobius_a :
    Continuous (fun M : InfoGeometry.MobiusTransform => M.a) :=
  continuous_mobiusCoordinates.fst

theorem continuous_mobius_b :
    Continuous (fun M : InfoGeometry.MobiusTransform => M.b) := by
  exact continuous_mobiusCoordinates.snd.fst

theorem continuous_mobius_c :
    Continuous (fun M : InfoGeometry.MobiusTransform => M.c) := by
  exact continuous_mobiusCoordinates.snd.snd.fst

theorem continuous_mobius_d :
    Continuous (fun M : InfoGeometry.MobiusTransform => M.d) := by
  exact continuous_mobiusCoordinates.snd.snd.snd

theorem continuous_mobiusDiscriminant :
    Continuous (fun M : InfoGeometry.MobiusTransform => M.discriminant) := by
  unfold InfoGeometry.MobiusTransform.discriminant
  have ha : Continuous (fun M : InfoGeometry.MobiusTransform => M.a) :=
    continuous_mobius_a
  have hb : Continuous (fun M : InfoGeometry.MobiusTransform => M.b) :=
    continuous_mobius_b
  have hc : Continuous (fun M : InfoGeometry.MobiusTransform => M.c) :=
    continuous_mobius_c
  have hd : Continuous (fun M : InfoGeometry.MobiusTransform => M.d) :=
    continuous_mobius_d
  fun_prop

theorem mobiusDiscriminant_zero_isClosed :
    IsClosed {M : InfoGeometry.MobiusTransform | M.discriminant = 0} := by
  exact IsClosed.preimage continuous_mobiusDiscriminant isClosed_singleton

/-! Scalar change of representative is continuous for the coefficient topology.
This is a representative-level statement; the quotient-level invariant is
provided separately by `scaleMobius_equiv` and the normalized discriminant
descent below. -/

theorem continuous_scaleMobius (lam : ℂ) (hlam : lam ≠ 0) :
    Continuous (fun M : InfoGeometry.MobiusTransform =>
      scaleMobius M lam hlam) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun M : InfoGeometry.MobiusTransform =>
    (lam * M.a, lam * M.b, lam * M.c, lam * M.d))
  have ha : Continuous (fun M : InfoGeometry.MobiusTransform => lam * M.a) :=
    continuous_const.mul continuous_mobius_a
  have hb : Continuous (fun M : InfoGeometry.MobiusTransform => lam * M.b) :=
    continuous_const.mul continuous_mobius_b
  have hc : Continuous (fun M : InfoGeometry.MobiusTransform => lam * M.c) :=
    continuous_const.mul continuous_mobius_c
  have hd : Continuous (fun M : InfoGeometry.MobiusTransform => lam * M.d) :=
    continuous_const.mul continuous_mobius_d
  exact ha.prodMk (hb.prodMk (hc.prodMk hd))

theorem continuous_pgl_scaleMobius (lam : ℂ) (hlam : lam ≠ 0) :
    Continuous (fun M : InfoGeometry.MobiusTransform =>
      (Quotient.mk' (scaleMobius M lam hlam) : InfoGeometry.PGL2C)) := by
  exact continuous_pgl_quotient.comp (continuous_scaleMobius lam hlam)

theorem continuous_normalizedMobiusDiscriminant :
    Continuous normalizedMobiusDiscriminant := by
  rw [continuous_iff_continuousAt]
  intro M
  unfold normalizedMobiusDiscriminant
    InfoGeometry.MobiusTransform.discriminant mobiusDet
  have ha : ContinuousAt
      (fun M : InfoGeometry.MobiusTransform => M.a) M :=
    continuous_mobius_a.continuousAt
  have hb : ContinuousAt
      (fun M : InfoGeometry.MobiusTransform => M.b) M :=
    continuous_mobius_b.continuousAt
  have hc : ContinuousAt
      (fun M : InfoGeometry.MobiusTransform => M.c) M :=
    continuous_mobius_c.continuousAt
  have hd : ContinuousAt
      (fun M : InfoGeometry.MobiusTransform => M.d) M :=
    continuous_mobius_d.continuousAt
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact mul_ne_zero (by norm_num) M.det_ne_zero

theorem continuous_pglNormalizedMobiusDiscriminant :
    Continuous pglNormalizedMobiusDiscriminant := by
  change Continuous (Quotient.lift normalizedMobiusDiscriminant _)
  apply Continuous.quotient_lift
  exact continuous_normalizedMobiusDiscriminant

def pglParabolicLocus : Set InfoGeometry.PGL2C :=
  pglNormalizedMobiusDiscriminant ⁻¹' ({0} : Set ℂ)

theorem pglParabolicLocus_isClosed : IsClosed pglParabolicLocus := by
  unfold pglParabolicLocus
  exact IsClosed.preimage continuous_pglNormalizedMobiusDiscriminant
    isClosed_singleton

theorem pglParabolicLocus_nonempty : pglParabolicLocus.Nonempty := by
  refine ⟨Quotient.mk' (InfoGeometry.parabolic_matrix 1 0 one_ne_zero), ?_⟩
  change pglNormalizedMobiusDiscriminant
      (Quotient.mk' (InfoGeometry.parabolic_matrix 1 0 one_ne_zero)) = 0
  simp [normalizedMobiusDiscriminant,
    InfoGeometry.MobiusTransform.discriminant, mobiusDet,
    InfoGeometry.parabolic_matrix]
  norm_num

theorem pglParabolicLocus_mk_iff
    (M : InfoGeometry.MobiusTransform) :
    (Quotient.mk' M : InfoGeometry.PGL2C) ∈ pglParabolicLocus ↔
      M.discriminant = 0 := by
  change pglNormalizedMobiusDiscriminant (Quotient.mk' M) = 0 ↔ _
  rw [pglNormalizedMobiusDiscriminant_mk]
  unfold normalizedMobiusDiscriminant
  have hden : (4 : ℂ) * mobiusDet M ≠ 0 :=
    mul_ne_zero (by norm_num) M.det_ne_zero
  exact (div_eq_zero_iff).trans (or_iff_left hden)

theorem pglParabolicLocus_pullback_eq_discriminant_zero :
    (Quotient.mk' : InfoGeometry.MobiusTransform → InfoGeometry.PGL2C) ⁻¹'
        pglParabolicLocus =
      {M : InfoGeometry.MobiusTransform | M.discriminant = 0} := by
  ext M
  exact pglParabolicLocus_mk_iff M

def pglNonParabolicLocus : Set InfoGeometry.PGL2C :=
  pglParabolicLocusᶜ

theorem pglNonParabolicLocus_isOpen : IsOpen pglNonParabolicLocus := by
  exact pglParabolicLocus_isClosed.isOpen_compl

theorem pglNonParabolicLocus_mk_iff
    (M : InfoGeometry.MobiusTransform) :
    (Quotient.mk' M : InfoGeometry.PGL2C) ∈ pglNonParabolicLocus ↔
      M.discriminant ≠ 0 := by
  constructor
  · intro h hz
    exact h ((pglParabolicLocus_mk_iff M).2 hz)
  · intro h hm
    exact h ((pglParabolicLocus_mk_iff M).1 hm)

theorem pglNonParabolicLocus_pullback_eq_discriminant_ne_zero :
    (Quotient.mk' : InfoGeometry.MobiusTransform → InfoGeometry.PGL2C) ⁻¹'
        pglNonParabolicLocus =
      {M : InfoGeometry.MobiusTransform | M.discriminant ≠ 0} := by
  ext M
  exact pglNonParabolicLocus_mk_iff M

theorem pglNonParabolicLocus_nonempty : pglNonParabolicLocus.Nonempty := by
  let M : InfoGeometry.MobiusTransform :=
    { a := 2, b := 0, c := 0, d := 1, det_ne_zero := by norm_num }
  refine ⟨Quotient.mk' M, (pglNonParabolicLocus_mk_iff M).2 ?_⟩
  simp [M, InfoGeometry.MobiusTransform.discriminant]
  norm_num

theorem isQuotientMap_pgl_projection :
    Topology.IsQuotientMap
      (Quotient.mk' : InfoGeometry.MobiusTransform → InfoGeometry.PGL2C) :=
  isQuotientMap_quotient_mk'

theorem pglParabolicLocus_isClosed_of_quotient_pullback :
    IsClosed pglParabolicLocus := by
  apply (isQuotientMap_pgl_projection.isClosed_preimage).mp
  rw [pglParabolicLocus_pullback_eq_discriminant_zero]
  exact mobiusDiscriminant_zero_isClosed

end InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge
