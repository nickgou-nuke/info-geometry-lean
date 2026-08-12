import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.NumberTheory.Cyclotomic.Basic
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import InfoGeometry.Canonical.QutritWeylOperatorBasis

noncomputable section
namespace SixStateGeneralizedPauliBasis

open Matrix

/-- Local definitions to avoid dependency on TwoSheetThreeColorWeyl chain -/

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev SixIndex := Fin 2 × Fin 3
abbrev M6C := Matrix SixIndex SixIndex ℂ

local notation A "⊗ₖ" B => Matrix.kroneckerMap (fun a b : ℂ => a * b) A B

def sheetPlus : M2C := !![1, 0; 0, 0]
def sheetMinus : M2C := !![0, 0; 0, 1]
def sheetFlip : M2C := !![0, 1; 1, 0]
def sheetGamma : M2C := sheetPlus - sheetMinus

def colorShift : M3C := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
def colorClock (ω : ℂ) : M3C := !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]

def tensor (A : M2C) (B : M3C) : M6C :=
  A ⊗ₖ B

/-- A concrete primitive cubic root used by the finite colour clock. -/
def ω3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- ω3 is a primitive cubic root: ω3² + ω3 + 1 = 0 -/
theorem omega3_root : ω3 ^ 2 + ω3 + 1 = 0 := by
  have hωprim : IsPrimitiveRoot ω3 3 := by
    simpa [ω3] using (Complex.isPrimitiveRoot_exp 3 (by decide))
  have hroot := IsPrimitiveRoot.isRoot_cyclotomic (R := ℂ) (n := 3) (by decide) hωprim
  simpa [Polynomial.cyclotomic_three, ω3] using hroot

/-- Color Weyl relations (inlined from TwoSheetThreeColorWeyl) -/
lemma color_shift_cube : colorShift ^ 3 = (1 : M3C) := by
  exact InfoGeometry.Canonical.TwoSheetThreeColorWeyl.colorShift_cubed

lemma color_clock_cube : colorClock ω3 ^ 3 = (1 : M3C) := by
  have hω3 : ω3 ^ 3 = 1 := by
    calc
      ω3 ^ 3 = (ω3 ^ 2 + ω3 + 1) * (ω3 - 1) + 1 := by ring
      _ = 1 := by rw [omega3_root]; ring
  exact InfoGeometry.Canonical.TwoSheetThreeColorWeyl.colorClock_cubed ω3 hω3

lemma color_weyl_comm : colorClock ω3 * colorShift = (ω3 : ℂ) • (colorShift * colorClock ω3) := by
  have hω3 : ω3 ^ 3 = 1 := by
    calc
      ω3 ^ 3 = (ω3 ^ 2 + ω3 + 1) * (ω3 - 1) + 1 := by ring
      _ = 1 := by rw [omega3_root]; ring
  exact InfoGeometry.Canonical.TwoSheetThreeColorWeyl.color_weyl_relation ω3 hω3

/-- Sheet Weyl operators on `M₂(ℂ) = ℂ² ⊗ ℂ²` indexed by `ZMod 2 × ZMod 2`.
sheetWeyl a b = Xᵃ Zᵇ where X = sheetFlip, Z = sheetGamma. -/
def sheetWeyl (a b : ZMod 2) : M2C :=
  sheetFlip ^ (a.val : ℕ) * sheetGamma ^ (b.val : ℕ)

/-- Color Weyl operators on `M₃(ℂ)` indexed by `ZMod 3 × ZMod 3`.
colorWeyl c d = Sᶜ Cᵈ where S = colorShift, C = colorClock ω₃. -/
def colorWeyl (c d : ZMod 3) : M3C :=
  colorShift ^ (c.val : ℕ) * colorClock ω3 ^ (d.val : ℕ)

/-- Six-state generalized Pauli operators on `M₆(ℂ) = M₂(ℂ) ⊗ M₃(ℂ)`.
sixWeyl a b c d = tensor (sheetWeyl a b) (colorWeyl c d). -/
def sixWeyl (a b : ZMod 2) (c d : ZMod 3) : M6C :=
  tensor (sheetWeyl a b) (colorWeyl c d)

/-- The complete 36-element basis indexed by `ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3`. -/
def sixWeylBasis : Finset (ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3) :=
  Finset.univ

/-- Sheet multiplication rule: Xᵃ Zᵇ Xᶜ Zᵈ = (-1)ᵇᶜ Xᵃ⁺ᶜ Zᵇ⁺ᵈ. -/
theorem sheetWeyl_mul (a b c d : ZMod 2) :
    sheetWeyl a b * sheetWeyl c d =
      ((if (b.val : ℕ) * (c.val : ℕ) = 1 then (-1 : ℂ) else (1 : ℂ)) : ℂ) •
        sheetWeyl (a + c) (b + d) := by
  have hflip : sheetFlip * sheetFlip = (1 : M2C) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sheetFlip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have hgamma : sheetGamma * sheetGamma = (1 : M2C) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sheetGamma, sheetPlus, sheetMinus, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.one_apply]
  have hanti : sheetGamma * sheetFlip = -(sheetFlip * sheetGamma) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sheetGamma, sheetPlus, sheetMinus, sheetFlip,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have h0 : (0 : Fin 0 → ℂ) = ![] := by
    funext i
    exact Fin.elim0 i
  have h1 : (0 : Fin 1 → ℂ) = ![0] := by
    funext i
    fin_cases i
    rfl
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [sheetWeyl, sheetFlip, sheetGamma, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply, pow_two,
      pow_succ, ZMod.val, ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_zero, ZMod.val_one,
      hflip, hgamma, hanti] <;>
    first
    | (ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [sheetPlus, sheetMinus, sheetFlip, sheetGamma,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
          Matrix.one_apply, Matrix.single, h0, h1] <;>
        try exact ⟨h0, h1⟩)
    | norm_num [sheetPlus, sheetMinus, sheetFlip, sheetGamma,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
        Matrix.one_apply, Matrix.single, h0, h1] <;>
      try exact ⟨h0, h1⟩

/-- Color commutation: Cⁿ S = ω₃ⁿ S Cⁿ. -/
lemma color_clock_shift_comm (n : ℕ) :
    colorClock ω3 ^ n * colorShift = (ω3 ^ n : ℂ) • (colorShift * colorClock ω3 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simp only [mul_assoc]
      rw [color_weyl_comm]
      simp only [mul_smul_comm, smul_mul_assoc]
      rw [← mul_assoc, ih]
      rw [smul_mul_assoc, smul_smul, pow_succ]
      simp only [mul_assoc]
      module

/-- Color commutation: Cⁿ Sᵐ = ω₃ⁿᵐ Sᵐ Cⁿ. -/
lemma color_clock_shift_pow_comm (n m : ℕ) :
    colorClock ω3 ^ n * colorShift ^ m =
      (ω3 ^ (n * m) : ℂ) • (colorShift ^ m * colorClock ω3 ^ n) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ← mul_assoc, ih]
      simp only [smul_mul_assoc]
      rw [mul_assoc, color_clock_shift_comm n]
      rw [mul_smul_comm, smul_smul]
      simp only [mul_assoc]
      rw [Nat.mul_succ, pow_add]

/-- Color multiplication rule: Sᶜ Cᵈ Sᶜ' Cᵈ' = ω₃ᶜᵈ' Sᶜ⁺ᶜ' Cᵈ⁺ᵈ'. -/
theorem colorWeyl_mul (c d c' d' : ZMod 3) :
    colorWeyl c d * colorWeyl c' d' =
      ((ω3 : ℂ) ^ ((d.val : ℕ) * (c'.val : ℕ))) •
        colorWeyl (c + c') (d + d') := by
  have hω3 : ω3 ^ 3 = 1 := by
    calc
      ω3 ^ 3 = (ω3 ^ 2 + ω3 + 1) * (ω3 - 1) + 1 := by ring
      _ = 1 := by rw [omega3_root]; ring
  have h12 : ((1 : ZMod 3) + 2).val = 0 := by decide
  have h21 : ((2 : ZMod 3) + 1).val = 0 := by decide
  have h22 : ((2 : ZMod 3) + 2).val = 1 := by decide
  have hshift_add : ∀ x y : ZMod 3,
      colorShift ^ x.val * colorShift ^ y.val = colorShift ^ (x + y).val := by
    intro x y
    rw [ZMod.val_add]
    fin_cases x <;> fin_cases y <;>
      norm_num [ZMod.val, ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_zero,
        ZMod.val_one, ZMod.val_add, h12, h21, h22, pow_two, pow_succ,
        color_shift_cube]
    all_goals first
      | simpa [pow_three, mul_assoc] using color_shift_cube
      | calc
          colorShift * colorShift * (colorShift * colorShift) =
              (colorShift * colorShift * colorShift) * colorShift := by noncomm_ring
          _ = 1 * colorShift := by
            simpa [pow_three, mul_assoc] using
              congrArg (fun z : M3C => z * colorShift) color_shift_cube
          _ = colorShift := by simp
  have hclock_add : ∀ x y : ZMod 3,
      colorClock ω3 ^ x.val * colorClock ω3 ^ y.val =
        colorClock ω3 ^ (x + y).val := by
    intro x y
    rw [ZMod.val_add]
    fin_cases x <;> fin_cases y <;>
      norm_num [ZMod.val, ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_zero,
        ZMod.val_one, ZMod.val_add, h12, h21, h22, pow_two, pow_succ,
        hω3, color_clock_cube]
    all_goals first
      | simpa [pow_three, mul_assoc] using color_clock_cube
      | calc
          colorClock ω3 * colorClock ω3 * (colorClock ω3 * colorClock ω3) =
              (colorClock ω3 * colorClock ω3 * colorClock ω3) * colorClock ω3 := by noncomm_ring
          _ = 1 * colorClock ω3 := by
            simpa [pow_three, mul_assoc] using
              congrArg (fun z : M3C => z * colorClock ω3) color_clock_cube
          _ = colorClock ω3 := by simp
  unfold colorWeyl
  calc
    colorShift ^ c.val * colorClock ω3 ^ d.val *
        (colorShift ^ c'.val * colorClock ω3 ^ d'.val) =
        colorShift ^ c.val *
          (colorClock ω3 ^ d.val * colorShift ^ c'.val) *
            colorClock ω3 ^ d'.val := by noncomm_ring
    _ = colorShift ^ c.val *
          (((ω3 : ℂ) ^ (d.val * c'.val)) •
            (colorShift ^ c'.val * colorClock ω3 ^ d.val)) *
              colorClock ω3 ^ d'.val := by
      rw [color_clock_shift_pow_comm]
    _ = ((ω3 : ℂ) ^ (d.val * c'.val)) •
          ((colorShift ^ c.val * colorShift ^ c'.val) *
            (colorClock ω3 ^ d.val * colorClock ω3 ^ d'.val)) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    _ = ((ω3 : ℂ) ^ (d.val * c'.val)) •
          (colorShift ^ (c + c').val * colorClock ω3 ^ (d + d').val) := by
      rw [hshift_add, hclock_add]

/-- Combined six-state multiplication rule. -/
theorem sixWeyl_mul (a b : ZMod 2 × ZMod 2) (c d : ZMod 3 × ZMod 3) (a' b' : ZMod 2 × ZMod 2) (c' d' : ZMod 3 × ZMod 3) :
    sixWeyl a.1 a.2 c.1 c.2 * sixWeyl a'.1 a'.2 c'.1 c'.2 =
      (((if (a.2.val : ℕ) * (a'.1.val : ℕ) = 1 then (-1 : ℂ) else (1 : ℂ)) : ℂ) *
        (ω3 : ℂ) ^ ((c.2.val : ℕ) * (c'.1.val : ℕ))) •
        sixWeyl (a.1 + a'.1) (a.2 + a'.2) (c.1 + c'.1) (c.2 + c'.2) := by
  unfold sixWeyl tensor
  rw [← Matrix.mul_kronecker_mul]
  rw [sheetWeyl_mul, colorWeyl_mul]
  ext i j
  simp [Matrix.kroneckerMap, mul_assoc, mul_comm, mul_left_comm]

/-- Sheet Weyl trace: Tr(Xᵃ Zᵇ) = 2 if a=b=0, else 0. -/
theorem sheetWeyl_trace (a b : ZMod 2) :
    trace (sheetWeyl a b) = if a = 0 ∧ b = 0 then (2 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [sheetWeyl, sheetFlip, sheetGamma, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, pow_two,
      pow_succ, ZMod.val, ZMod.val_natCast, ZMod.val_ofNat, sheetPlus,
      sheetMinus, sheetGamma]

/-- Color Weyl trace: Tr(Sᶜ Cᵈ) = 3 if c=d=0, else 0. -/
theorem colorWeyl_trace (c d : ZMod 3) :
    trace (colorWeyl c d) = if c = 0 ∧ d = 0 then (3 : ℂ) else 0 := by
  let fc : Fin 3 := ⟨c.val, c.isLt⟩
  let fd : Fin 3 := ⟨d.val, d.isLt⟩
  have hω : InfoGeometry.Topology.Parafermion.omega = ω3 := rfl
  simpa [colorWeyl,
    InfoGeometry.Canonical.QutritWeylOperatorBasis.weylWord, fc, fd, hω] using
    (InfoGeometry.Canonical.QutritWeylOperatorBasis.weylWord_trace fc fd)

/-- Sheet Weyl adjoint: (Xᵃ Zᵇ)† = (-1)^{ab} Xᵃ Zᵇ (self-adjoint up to sign). -/
theorem sheetWeyl_star (a b : ZMod 2) :
    star (sheetWeyl a b) = ((-1 : ℂ) ^ ((a.val : ℕ) * (b.val : ℕ))) • sheetWeyl a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [sheetWeyl, sheetFlip, sheetGamma, Matrix.conjTranspose,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.one_apply, pow_two, pow_succ,
      ZMod.val, ZMod.val_natCast, ZMod.val_ofNat, starRingEnd_apply,
      sheetPlus, sheetMinus] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.conjTranspose_apply, sheetPlus, sheetMinus,
        sheetFlip, sheetGamma, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.one_apply]

/-- Hilbert–Schmidt orthogonality for sheet Weyl: Tr((Xᵃ Zᵇ)† Xᶜ Zᵈ) = 2 δ_{a,c} δ_{b,d}. -/
theorem sheetWeyl_trace_orthogonal (a b a' b' : ZMod 2) :
    trace (star (sheetWeyl a b) * sheetWeyl a' b') =
      (if a = a' ∧ b = b' then (2 : ℂ) else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    norm_num [sheetWeyl, sheetFlip, sheetGamma, Matrix.conjTranspose,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.one_apply, pow_two, pow_succ,
      ZMod.val, ZMod.val_natCast, ZMod.val_ofNat, sheetPlus, sheetMinus,
      Matrix.trace]

/-- Hilbert–Schmidt orthogonality for color Weyl: Tr((Sᶜ Cᵈ)† Sᶜ' Cᵈ') = 3 δ_{c,c'} δ_{d,d'}. -/
theorem colorWeyl_trace_orthogonal (c d c' d' : ZMod 3) :
    trace (star (colorWeyl c d) * colorWeyl c' d') =
      (if c = c' ∧ d = d' then (3 : ℂ) else 0) := by
  let fc : Fin 3 := ⟨c.val, c.isLt⟩
  let fd : Fin 3 := ⟨d.val, d.isLt⟩
  let fc' : Fin 3 := ⟨c'.val, c'.isLt⟩
  let fd' : Fin 3 := ⟨d'.val, d'.isLt⟩
  have hω : InfoGeometry.Topology.Parafermion.omega = ω3 := rfl
  convert (InfoGeometry.Canonical.QutritWeylOperatorBasis.weylWord_hs_orthogonal
    fc fd fc' fd') using 1 <;>
    simp [Matrix.star_eq_conjTranspose, colorWeyl,
      InfoGeometry.Canonical.QutritWeylOperatorBasis.weylWord,
      fc, fd, fc', fd', hω]

/-- Hilbert–Schmidt orthogonality for six-state Weyl: Tr((sixWeyl)† sixWeyl) = 6 δ. -/
theorem sixWeyl_trace_orthogonal (a b : ZMod 2 × ZMod 2) (c d : ZMod 3 × ZMod 3) (a' b' : ZMod 2 × ZMod 2) (c' d' : ZMod 3 × ZMod 3) :
    trace (star (sixWeyl a.1 a.2 c.1 c.2) * sixWeyl a'.1 a'.2 c'.1 c'.2) =
      (if a.1 = a'.1 ∧ a.2 = a'.2 ∧ c.1 = c'.1 ∧ c.2 = c'.2 then (6 : ℂ) else 0) := by
  have hstar_kron (A : M2C) (B : M3C) :
      star (tensor A B) = tensor (star A) (star B) := by
    ext i j
    simp only [tensor, Matrix.star_eq_conjTranspose,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply]
    exact map_mul (starRingEnd ℂ) _ _
  unfold sixWeyl
  rw [hstar_kron]
  unfold tensor
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.trace_kronecker]
  rw [sheetWeyl_trace_orthogonal, colorWeyl_trace_orthogonal]
  split_ifs <;> norm_num at * <;> aesop

/- The concrete 36-channel Weyl family is linearly independent.  The proof
uses the already computed Hilbert--Schmidt pairing and does not postulate a
second abstract operator basis. -/
theorem sixWeyl_linearIndependent :
    LinearIndependent ℂ
      (fun p : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3 =>
        sixWeyl p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  rw [Fintype.linearIndependent_iff]
  intro c h
  intro p
  let wp : M6C := sixWeyl p.1 p.2.1 p.2.2.1 p.2.2.2
  have hpair := congrArg (fun M : M6C => trace (star wp * M)) h
  have hpair' :
      ∑ q : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3,
          c q * trace (star wp *
            sixWeyl q.1 q.2.1 q.2.2.1 q.2.2.2) = 0 := by
    have hzero :
        trace (star wp *
          (∑ q : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3,
            c q • sixWeyl q.1 q.2.1 q.2.2.1 q.2.2.2)) = 0 := by
      rw [h]
      simp
    calc
      _ = trace (star wp *
          (∑ q : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3,
            c q • sixWeyl q.1 q.2.1 q.2.2.1 q.2.2.2)) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
        simp [Matrix.trace_smul, smul_eq_mul, mul_assoc]
      _ = 0 := hzero
  have hterm := hpair'
  have hsingle :
      ∑ q : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3,
          c q * trace (star wp *
            sixWeyl q.1 q.2.1 q.2.2.1 q.2.2.2) =
        c p * trace (star wp * wp) := by
    apply Finset.sum_eq_single p
    · intro q _ hqp
      have hneq :
          ¬(p.1 = q.1 ∧ p.2.1 = q.2.1 ∧
            p.2.2.1 = q.2.2.1 ∧ p.2.2.2 = q.2.2.2) := by
        intro heq
        rcases heq with ⟨h1, h2, h3, h4⟩
        apply hqp
        apply Prod.ext
        · exact h1.symm
        · apply Prod.ext
          · exact h2.symm
          · apply Prod.ext
            · exact h3.symm
            · exact h4.symm
      have horth :
          trace (star wp *
            sixWeyl q.1 q.2.1 q.2.2.1 q.2.2.2) = 0 := by
        simpa [wp, hneq] using
          (sixWeyl_trace_orthogonal
            (p.1, p.2.1) (p.1, p.2.1)
            (p.2.2.1, p.2.2.2) (p.2.2.1, p.2.2.2)
            (q.1, q.2.1) (q.1, q.2.1)
            (q.2.2.1, q.2.2.2) (q.2.2.1, q.2.2.2))
      rw [horth]
      simp
    · intro hp
      exact False.elim (hp (Finset.mem_univ p))
  rw [hsingle] at hterm
  have hdiag :
        trace (star wp * wp) = (6 : ℂ) := by
    simpa [wp] using
      (sixWeyl_trace_orthogonal
        (p.1, p.2.1) (p.1, p.2.1)
        (p.2.2.1, p.2.2.2) (p.2.2.1, p.2.2.2)
        (p.1, p.2.1) (p.1, p.2.1)
        (p.2.2.1, p.2.2.2) (p.2.2.1, p.2.2.2))
  rw [hdiag] at hterm
  exact (mul_eq_zero.mp hterm).resolve_right (by norm_num)

noncomputable def sixWeylModuleBasis :
    Module.Basis (ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3) ℂ M6C :=
  basisOfLinearIndependentOfCardEqFinrank sixWeyl_linearIndependent (by
    rw [show Fintype.card (ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3) = 36 by decide]
    simp [M6C, Module.finrank_matrix])

@[simp] theorem sixWeylModuleBasis_apply
    (p : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3) :
    sixWeylModuleBasis p = sixWeyl p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp [sixWeylModuleBasis]

def sixWeylCoefficient (A : M6C)
    (p : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3) : ℂ :=
  (sixWeylModuleBasis.repr A) p

theorem sixWeyl_expansion (A : M6C) :
    ∑ p : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3,
        sixWeylCoefficient A p •
          sixWeyl p.1 p.2.1 p.2.2.1 p.2.2.2 = A := by
  simpa [sixWeylCoefficient] using
    Module.Basis.sum_repr sixWeylModuleBasis A

theorem sixWeyl_expansion_unique (A : M6C)
    (c : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3 → ℂ)
    (h : ∑ p : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3,
        c p • sixWeyl p.1 p.2.1 p.2.2.1 p.2.2.2 = A) :
    ∀ p, c p = sixWeylCoefficient A p := by
  have hzero :
      ∑ p : ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3,
        (c p - sixWeylCoefficient A p) •
          sixWeyl p.1 p.2.1 p.2.2.1 p.2.2.2 = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, h, sixWeyl_expansion]
    simp
  have hcoeff :=
    (Fintype.linearIndependent_iff.mp sixWeyl_linearIndependent)
      (fun p => c p - sixWeylCoefficient A p) hzero
  intro p
  exact sub_eq_zero.mp (hcoeff p)

/-- The indexing set has the expected 36 labels.  Linear independence and
orthogonality are separate theorems below; this cardinality statement does
not pretend to prove them. -/
theorem sixWeyl_index_card :
    Fintype.card (ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3) = 36 := by
  decide

end SixStateGeneralizedPauliBasis
end noncomputable section
