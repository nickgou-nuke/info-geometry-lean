import Mathlib
import InfoGeometry.Canonical.PrimePartitionPolynomials
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Analysis.HurwitzAsanoColimitLimitBridge

/-!
# Actual N=2 prime-partition Lee--Yang bridge

This is a finite, concrete witness for the polynomial defined by
`PrimePartitionPolynomials.partitionPolynomial`.  It is deliberately not a
universal `LeeYangPolynomialWitness`: the arbitrary-`N` stability theorem is a
separate open input to the colimit/RH corridor.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangActualN2

open scoped BigOperators
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimePartitionPolynomials
open InfoGeometry.Canonical.PrimeHurwitzLimit
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Analysis.AsanoLeeYangCircle
open InfoGeometry.Analysis.HurwitzAsano

def configEquiv : (Fin 2 → Bool) ≃ (Bool × Bool) where
  toFun := fun σ => (σ 0, σ 1)
  invFun := fun p i => Fin.cases p.1 (fun j => Fin.cases p.2 (fun k => nomatch k) j) i
  left_inv := by intro σ; funext i; fin_cases i <;> rfl
  right_inv := by intro p; rcases p with ⟨b₀, b₁⟩; cases b₀ <;> cases b₁ <;> rfl

theorem interactionEnergy_formula
    (D : FinitePrimeChainData 2) (lam : ℝ) (b₀ b₁ : Bool) :
    interactionEnergy D lam (configEquiv.symm (b₀, b₁)) =
      if b₀ = b₁ then lam * D.ell 0 * D.ell 1
      else -(lam * D.ell 0 * D.ell 1) := by
  cases b₀ <;> cases b₁
  · have h : configEquiv.symm (false, false) = (fun _ : Fin 2 => false) := by
      funext i; fin_cases i <;> rfl
    rw [h]
    simp [interactionEnergy, FinitePrimeChainData.spinCoupling, spinSign]
    ring
  · have h : configEquiv.symm (false, true) = (fun i : Fin 2 => i = 1) := by
      funext i; fin_cases i <;> rfl
    rw [h]
    simp [interactionEnergy, FinitePrimeChainData.spinCoupling, spinSign]
    ring
  · have h : configEquiv.symm (true, false) = (fun i : Fin 2 => i = 0) := by
      funext i; fin_cases i <;> rfl
    rw [h]
    simp [interactionEnergy, FinitePrimeChainData.spinCoupling, spinSign]
    ring
  · have h : configEquiv.symm (true, true) = (fun _ : Fin 2 => true) := by
      funext i; fin_cases i <;> rfl
    rw [h]
    simp [interactionEnergy, FinitePrimeChainData.spinCoupling, spinSign]
    ring

theorem partitionPolynomial_formula
    (D : FinitePrimeChainData 2) (lam : ℝ) :
    partitionPolynomial D lam =
      Polynomial.C (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) +
      Polynomial.C (2 * Real.exp (-(lam * D.ell 0 * D.ell 1)) : ℂ) * Polynomial.X +
      Polynomial.C (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) * Polynomial.X ^ 2 := by
  classical
  unfold partitionPolynomial
  let e := configEquiv
  let f : (Fin 2 → Bool) → Polynomial ℂ := fun σ =>
    Polynomial.C ((configurationWeight D lam σ : ℝ) : ℂ) *
      Polynomial.X ^ occupiedCount σ
  let g : (Bool × Bool) → Polynomial ℂ := fun p => f (e.symm p)
  change (∑ σ : Fin 2 → Bool, f σ) = _
  rw [Fintype.sum_equiv e f g]
  · rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
    have h00 : e.symm (false, false) = (fun _ : Fin 2 => false) := by
      funext i; fin_cases i <;> rfl
    have h01 : e.symm (false, true) = (fun i : Fin 2 => i = 1) := by
      funext i; fin_cases i <;> rfl
    have h10 : e.symm (true, false) = (fun i : Fin 2 => i = 0) := by
      funext i; fin_cases i <;> rfl
    have h11 : e.symm (true, true) = (fun _ : Fin 2 => true) := by
      funext i; fin_cases i <;> rfl
    simp only [g, Fintype.sum_bool]
    rw [h00, h01, h10, h11]
    have hc0 : (({x : Fin 2 | x = 0} : Finset (Fin 2))).card = 1 := by decide
    have hc1 : (({x : Fin 2 | x = 1} : Finset (Fin 2))).card = 1 := by decide
    simp [f, configurationWeight, interactionEnergy, occupiedCount,
      FinitePrimeChainData.spinCoupling, spinSign, hc0, hc1]
    rw [Polynomial.C_ofNat]
    ring
  · intro σ
    simp [g]

theorem palindromic_quadratic_root_on_unit_circle
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    {z : ℂ}
    (hz : (Polynomial.C (a : ℂ) + Polynomial.C (2 * b : ℂ) * Polynomial.X +
      Polynomial.C (a : ℂ) * Polynomial.X ^ 2).IsRoot z) :
    OnUnitCircle z := by
  have hpoly : (a : ℂ) + (2 * b : ℂ) * z + (a : ℂ) * z ^ 2 = 0 := by
    simpa [Polynomial.IsRoot, add_comm, add_left_comm, add_assoc] using hz
  have hre := congrArg Complex.re hpoly
  have him := congrArg Complex.im hpoly
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  by_cases hy : z.im = 0
  · have hreal : a * z.re ^ 2 + 2 * b * z.re + a = 0 := by
      rw [hy] at hre
      nlinarith [hre]
    have hsquare : 0 ≤ (a * z.re + b) ^ 2 := sq_nonneg (a * z.re + b)
    have hdiff : 0 ≤ a ^ 2 - b ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    have hmul : a * (a * z.re ^ 2 + 2 * b * z.re + a) = 0 := by
      rw [hreal, mul_zero]
    have hsum : (a * z.re + b) ^ 2 + (a ^ 2 - b ^ 2) = 0 := by
      nlinarith [hmul]
    have hsquare0 : (a * z.re + b) ^ 2 = 0 := by nlinarith
    have hdiff0 : a ^ 2 - b ^ 2 = 0 := by nlinarith
    have hab : a = b := by nlinarith [sq_nonneg (a - b)]
    have hlin : a * z.re + b = 0 := (sq_eq_zero_iff.mp hsquare0)
    have hx : z.re = -1 := by nlinarith [hlin]
    simp [OnUnitCircle, Complex.normSq, hy, hx]
  · have himfac : 2 * z.im * (a * z.re + b) = 0 := by
      nlinarith [him]
    have hrel : a * z.re + b = 0 := by
      rcases mul_eq_zero.mp himfac with hy0 | hrel0
      · exact (hy (by nlinarith [hy0])).elim
      · exact hrel0
    have hrelx : a * z.re ^ 2 + b * z.re = 0 := by
      linear_combination z.re * hrel
    have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
      nlinarith [hre, hrel, hrelx]
    simpa [OnUnitCircle, Complex.normSq, pow_two] using hnorm

theorem root_on_unit_circle
    (D : FinitePrimeChainData 2) {lam : ℝ} (hLam : 0 ≤ lam)
    {z : ℂ} (hz : (partitionPolynomial D lam).IsRoot z) :
    OnUnitCircle z := by
  rw [partitionPolynomial_formula D lam] at hz
  let q : ℝ := lam * D.ell 0 * D.ell 1
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (mul_nonneg hLam (le_of_lt (D.ell_pos 0)))
      (le_of_lt (D.ell_pos 1))
  have ha : 0 < Real.exp q := Real.exp_pos q
  have hb : 0 < Real.exp (-q) := Real.exp_pos (-q)
  have hba : Real.exp (-q) ≤ Real.exp q := by
    apply Real.exp_le_exp.mpr
    linarith
  exact palindromic_quadratic_root_on_unit_circle ha hb hba (by
    simpa [q] using hz)

theorem root_re_ne_neg_one
    (D : FinitePrimeChainData 2) {lam : ℝ} (hlam : 0 < lam)
    {z : ℂ} (hz : (partitionPolynomial D lam).IsRoot z) :
    z.re ≠ -1 := by
  rw [partitionPolynomial_formula D lam] at hz
  intro hzr
  have hqpos : 0 < lam * D.ell 0 * D.ell 1 := by
    exact mul_pos (mul_pos hlam (D.ell_pos 0)) (D.ell_pos 1)
  have hlt : Real.exp (-(lam * D.ell 0 * D.ell 1)) <
      Real.exp (lam * D.ell 0 * D.ell 1) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have harg :
      (↑lam * ↑(D.ell 0) * ↑(D.ell 1) : ℂ) =
        ((lam * D.ell 0 * D.ell 1 : ℝ) : ℂ) := by
    push_cast
    ring
  have hargneg :
      -(↑lam * ↑(D.ell 0) * ↑(D.ell 1) : ℂ) =
        ((-(lam * D.ell 0 * D.ell 1) : ℝ) : ℂ) := by
    rw [harg]
    push_cast
    ring
  have hargneg' :
      -((lam * D.ell 0 * D.ell 1 : ℝ) : ℂ) =
        ((-(lam * D.ell 0 * D.ell 1) : ℝ) : ℂ) := by
    push_cast
    ring
  have hzval := hz
  simp [Polynomial.IsRoot] at hzval
  rw [harg, hargneg'] at hzval
  have hpos_re :
      (Complex.exp (↑lam * ↑(D.ell 0) * ↑(D.ell 1))).re =
        Real.exp (lam * D.ell 0 * D.ell 1) := by
    rw [harg]
    exact Complex.exp_ofReal_re _
  have hneg_re :
      (Complex.exp (-(↑lam * ↑(D.ell 0) * ↑(D.ell 1)))).re =
        Real.exp (-(lam * D.ell 0 * D.ell 1)) := by
    rw [hargneg]
    exact Complex.exp_ofReal_re _
  have him := congrArg Complex.im hzval
  simp only [Complex.exp_ofReal_im, Complex.mul_im, Complex.add_im,
    Complex.sub_im, Complex.ofReal_im, mul_zero, sub_zero, zero_mul,
    add_zero, zero_add, pow_two] at him
  simp [hzr] at him
  rw [hpos_re, hneg_re] at him
  have him_zero : z.im = 0 := by
    nlinarith [hlt]
  have hzneg : z = (-1 : ℂ) := by
    apply Complex.ext
    · simpa using hzr
    · simp [him_zero]
  rw [hzneg] at hzval
  have hreal := congrArg Complex.re hzval
  simp [Polynomial.IsRoot] at hreal
  rw [hpos_re, hneg_re] at hreal
  nlinarith [hlt]

theorem partitionFunction_zero_root_on_unit_circle
    (D : FinitePrimeChainData 2) {lam : ℝ} (hLam : 0 < lam)
    {z : ℂ} (hz : partitionFunction D lam z = 0) :
    OnUnitCircle z := by
  exact root_on_unit_circle D (le_of_lt hLam) (by
    simpa [partitionFunction_eq_eval, Polynomial.IsRoot] using hz)

theorem partitionFunction_zero_root_re_ne_neg_one
    (D : FinitePrimeChainData 2) {lam : ℝ} (hLam : 0 < lam)
    {z : ℂ} (hz : partitionFunction D lam z = 0) :
    z.re ≠ -1 := by
  exact root_re_ne_neg_one D hLam (by
    simpa [partitionFunction_eq_eval, Polynomial.IsRoot] using hz)

private theorem partitionFunction_formula_eval
    (D : FinitePrimeChainData 2) (lam : ℝ) (z : ℂ) :
    partitionFunction D lam z =
      (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) +
      (2 * Real.exp (-(lam * D.ell 0 * D.ell 1)) : ℂ) * z +
      (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) * z ^ 2 := by
  rw [partitionFunction_eq_eval, partitionPolynomial_formula]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

theorem partitionFunction_zeroFreeInUnitDisk
    (D : FinitePrimeChainData 2) {lam : ℝ} (hLam : 0 ≤ lam) :
    ZeroFreeInUnitDisk (partitionFunction D lam) := by
  intro z hz_disk hz_zero
  have hcircle : OnUnitCircle z :=
    root_on_unit_circle D hLam (by
      simpa [partitionFunction_eq_eval, Polynomial.IsRoot] using hz_zero)
  rw [OnUnitCircle, Complex.normSq_eq_norm_sq] at hcircle
  nlinarith [norm_nonneg z, hz_disk]

theorem partitionFunction_reciprocalZeroSymmetric
    (D : FinitePrimeChainData 2) (lam : ℝ) :
    ReciprocalZeroSymmetric (partitionFunction D lam) := by
  intro z hz0
  constructor
  · intro hz
    rw [partitionFunction_formula_eval D lam z] at hz
    rw [partitionFunction_formula_eval D lam z⁻¹]
    have hscaled :
        z ^ 2 *
            ((Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) +
              (2 * Real.exp (-(lam * D.ell 0 * D.ell 1)) : ℂ) * z⁻¹ +
              (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) * (z⁻¹) ^ 2) =
          (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) * z ^ 2 +
            (2 * Real.exp (-(lam * D.ell 0 * D.ell 1)) : ℂ) * z +
            (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) := by
      field_simp [hz0]
      ring
    have hzero :
        z ^ 2 *
            ((Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) +
              (2 * Real.exp (-(lam * D.ell 0 * D.ell 1)) : ℂ) * z⁻¹ +
              (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) * (z⁻¹) ^ 2) = 0 := by
      rw [hscaled]
      simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hz
    exact (mul_eq_zero.mp hzero).resolve_left (sq_ne_zero hz0)
  · intro hz
    rw [partitionFunction_formula_eval D lam z] 
    rw [partitionFunction_formula_eval D lam z⁻¹] at hz
    have hscaled :
        z ^ 2 *
            ((Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) +
              (2 * Real.exp (-(lam * D.ell 0 * D.ell 1)) : ℂ) * z⁻¹ +
              (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) * (z⁻¹) ^ 2) =
          (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) * z ^ 2 +
            (2 * Real.exp (-(lam * D.ell 0 * D.ell 1)) : ℂ) * z +
            (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) := by
      field_simp [hz0]
      ring
    have hzero :
        z ^ 2 *
            ((Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) +
              (2 * Real.exp (-(lam * D.ell 0 * D.ell 1)) : ℂ) * z⁻¹ +
              (Real.exp (lam * D.ell 0 * D.ell 1) : ℂ) * (z⁻¹) ^ 2) = 0 := by
      rw [hz, mul_zero]
    rw [hscaled] at hzero
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hzero

theorem root_maps_to_critical_line
    (D : FinitePrimeChainData 2) {lam : ℝ} (hlam : 0 < lam)
    {z : ℂ} (hz : (partitionPolynomial D lam).IsRoot z) :
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnCriticalLine
      (cayleyToTemperature z) := by
  exact cayleyToTemperature_mem_criticalLine_of_unitCircle z
    (root_on_unit_circle D (le_of_lt hlam) hz)
    (root_re_ne_neg_one D hlam hz)

theorem partitionFunction_zero_maps_to_critical_line
    (D : FinitePrimeChainData 2) {lam : ℝ} (hLam : 0 < lam)
    {z : ℂ} (hz : partitionFunction D lam z = 0) :
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.OnCriticalLine
      (cayleyToTemperature z) := by
  exact cayleyToTemperature_mem_criticalLine_of_unitCircle z
    (partitionFunction_zero_root_on_unit_circle D hLam hz)
    (partitionFunction_zero_root_re_ne_neg_one D hLam hz)

theorem partitionFunction_zero_to_riemannCayleyInverse_critical_line
    (D : FinitePrimeChainData 2) {lam : ℝ} (hLam : 0 < lam)
    {z : ℂ} (hz : partitionFunction D lam z = 0) :
    (riemannCayleyInverse z).re = 1 / 2 := by
  have h_disk_free : ZeroFreeInUnitDisk (partitionFunction D lam) :=
    partitionFunction_zeroFreeInUnitDisk D (le_of_lt hLam)
  have h_symm : ReciprocalZeroSymmetric (partitionFunction D lam) :=
    partitionFunction_reciprocalZeroSymmetric D lam
  have hz_ne : z ≠ -1 := by
    intro hz_neg
    apply partitionFunction_zero_root_re_ne_neg_one D hLam hz
    simpa [hz_neg]
  exact reciprocal_root_to_critical_line h_disk_free h_symm hz hz_ne

end InfoGeometry.Canonical.PrimeLeeYangActualN2
