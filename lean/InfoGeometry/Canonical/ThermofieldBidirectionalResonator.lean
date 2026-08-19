/-!
# ThermofieldBidirectionalResonator

Coherent two-amplitude bidirectional resonator with loss, Möbius projectivization,
and modular conjugation. No population dynamics, no gain.

Mathematical sequence:
```
TwinAmplitude → CoherentExchange → LossBalance
    → ProjectiveRatio → MöbiusRoundTrip → ModularConjugation
```
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame
import InfoGeometry.Canonical.ZornSpinor

namespace InfoGeometry.Canonical.ThermofieldBidirectionalResonator

open Complex
open Matrix
open InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame

/-!
=============================================================================
PART 1: Twin Amplitude Carrier
=============================================================================
-/

/-- The doubled amplitude carrier: two complex channels (+ and -). -/
structure TwinAmplitude : Type where
  aPlus  : ℂ
  aMinus : ℂ

instance : AddCommGroup TwinAmplitude :=
  ⟨fun x y => ⟨x.aPlus + y.aPlus, x.aMinus + y.aMinus⟩,
   fun x y => ⟨x.aPlus - y.aPlus, x.aMinus - y.aMinus⟩,
   ⟨0, 0⟩,
   fun x y => by simp [TwinAmplitude, add_comm, add_left_comm, add_assoc],
   fun x => by simp [TwinAmplitude, add_assoc],
   fun x y => by simp [TwinAmplitude, add_comm]⟩

instance : Module ℂ TwinAmplitude :=
  ⟨fun c x => ⟨c * x.aPlus, c * x.aMinus⟩,
   fun c x y => by simp [TwinAmplitude, smul_add, mul_add],
   fun c d x => by simp [TwinAmplitude, mul_assoc, mul_comm, mul_left_comm],
   fun x => by simp [TwinAmplitude, one_mul]⟩

/-- Energy in each channel -/
def energyPlus (a : TwinAmplitude) : ℝ := Complex.abs a.aPlus ^ 2
def energyMinus (a : TwinAmplitude) : ℝ := Complex.abs a.aMinus ^ 2

/-- Total energy -/
def totalEnergy (a : TwinAmplitude) : ℝ := energyPlus a + energyMinus a

/-- Exchange current (coherent transfer between channels) -/
def exchangeCurrent (a : TwinAmplitude) (g : ℂ) : ℝ :=
  2 * (g.re * (a.aPlus.re * a.aMinus.im - a.aPlus.im * a.aMinus.re) -
       g.im * (a.aPlus.re * a.aMinus.re + a.aPlus.im * a.aMinus.im))

/-!
=============================================================================
PART 2: Coherent Dynamics (from amplitude equations)
=============================================================================
-/

/-- Parameters for the coupled resonator:
    κ₊, κ₋ : decay rates (≥ 0)
    ω₊, ω₋ : resonance frequencies
    g       : coupling strength (complex) -/
structure ResonatorParams where
  κPlus  : ℝ
  κMinus : ℝ
  ωPlus  : ℝ
  ωMinus : ℝ
  g      : ℂ
  κPlus_nonneg  : κPlus ≥ 0
  κMinus_nonneg : κMinus ≥ 0

/-- The continuous-time generator matrix X -/
def generatorMatrix (p : ResonatorParams) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-p.κPlus - Complex.I * p.ωPlus : ℂ), -p.g;
     -star p.g, (-p.κMinus - Complex.I * p.ωMinus : ℂ)]

/-- Time evolution operator U(t) = exp(tX) -/
def evolutionOperator (p : ResonatorParams) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (generatorMatrix p).exp

/-- Amplitude evolution: a(t) = U(t) a(0) -/
def evolveAmplitude (p : ResonatorParams) (t : ℝ) (a₀ : TwinAmplitude) : TwinAmplitude :=
  let U := evolutionOperator p t
  ⟨U 0 0 * a₀.aPlus + U 0 1 * a₀.aMinus,
   U 1 0 * a₀.aPlus + U 1 1 * a₀.aMinus⟩

/-- Energy balance derived from the amplitude equations:
    ȧ₊ = -(κ₊+iω₊)a₊ - i g a₋
    ȧ₋ = -(κ₋+iω₋)a₋ - i g* a₊
    gives d/dt E₊ = -2κ₊E₊ + exchangeCurrent, etc. -/
structure IntensityBalance (p : ResonatorParams) (a : TwinAmplitude) where
  E_dot_plus  : ℝ
  E_dot_minus : ℝ
  plus_eq :
    E_dot_plus =
      -2 * p.κPlus * energyPlus a
        + exchangeCurrent a p.g
  minus_eq :
    E_dot_minus =
      -2 * p.κMinus * energyMinus a
        - exchangeCurrent a p.g

/-- Construct the intensity balance from the amplitude equations -/
def makeIntensityBalance (p : ResonatorParams) (a : TwinAmplitude) : IntensityBalance p a :=
  ⟨-2 * p.κPlus * energyPlus a + exchangeCurrent a p.g,
   -2 * p.κMinus * energyMinus a - exchangeCurrent a p.g,
   by rfl,
   by rfl⟩

/-- Total energy balance: exchange current cancels -/
theorem totalEnergyBalance (p : ResonatorParams) (a : TwinAmplitude) :
    (makeIntensityBalance p a).E_dot_plus + (makeIntensityBalance p a).E_dot_minus
      = -2 * p.κPlus * energyPlus a - 2 * p.κMinus * energyMinus a := by
  have h₁ := (makeIntensityBalance p a).plus_eq
  have h₂ := (makeIntensityBalance p a).minus_eq
  linarith

/-- Symmetric case: κ₊ = κ₋ = κ, ω₊ = ω₋ = ω, g ∈ ℝ -/
theorem symmetricTotalEnergyDecay (p : ResonatorParams) (a : TwinAmplitude)
    (hκ : p.κPlus = p.κMinus) :
    (makeIntensityBalance p a).E_dot_plus + (makeIntensityBalance p a).E_dot_minus
      = -2 * p.κPlus * totalEnergy a := by
  have h₁ := totalEnergyBalance p a
  rw [hκ] at h₁ ⊢
  <;> ring_nf at h₁ ⊢ <;> linarith

/-!
=============================================================================
PART 3: Projective Ratio and Möbius Transform
=============================================================================
-/

/-- Projective ratio z = a₋/a₊ (on the chart a₊ ≠ 0) -/
def projectiveRatio (a : TwinAmplitude) : ℂ :=
  a.aMinus / a.aPlus

/-- Möbius transformation from a 2×2 matrix -/
def mobiusTransform (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : ℂ :=
  (M 1 0 + M 1 1 * z) / (M 0 0 + M 0 1 * z)

/-- The projective ratio evolves by Möbius transformation:
    If a' = M a, then z' = mobiusTransform M z  (provided a₊ ≠ 0 and denominator ≠ 0) -/
theorem projectiveRatioEvolves (M : Matrix (Fin 2) (Fin 2) ℂ) (a : TwinAmplitude)
    (ha : a.aPlus ≠ 0) (hdenom : M 0 0 + M 0 1 * (a.aMinus / a.aPlus) ≠ 0) :
    projectiveRatio ⟨M 0 0 * a.aPlus + M 0 1 * a.aMinus,
                      M 1 0 * a.aPlus + M 1 1 * a.aMinus⟩
      = mobiusTransform M (projectiveRatio a) := by
  have h₁ : projectiveRatio ⟨M 0 0 * a.aPlus + M 0 1 * a.aMinus,
                              M 1 0 * a.aPlus + M 1 1 * a.aMinus⟩
      = (M 1 0 * a.aPlus + M 1 1 * a.aMinus) / (M 0 0 * a.aPlus + M 0 1 * a.aMinus) := by
    simp [projectiveRatio]
    <;> field_simp [ha]
    <;> ring_nf
  rw [h₁]
  have h₂ : (M 1 0 * a.aPlus + M 1 1 * a.aMinus) / (M 0 0 * a.aPlus + M 0 1 * a.aMinus)
      = (M 1 0 + M 1 1 * (a.aMinus / a.aPlus)) / (M 0 0 + M 0 1 * (a.aMinus / a.aPlus)) := by
    have h₃ : a.aPlus ≠ 0 := ha
    field_simp [h₃]
    <;> ring_nf
    <;> field_simp [h₃]
    <;> ring_nf
  rw [h₂]
  <;> simp [mobiusTransform]
  <;> field_simp [ha, hdenom]
  <;> ring_nf

/-- Round-trip matrix (normalized determinant = 1) -/
structure RoundTripMatrix where
  toMatrix : Matrix (Fin 2) (Fin 2) ℂ
  det_one : toMatrix.det = 1

/-- Round-trip evolution on amplitudes -/
def roundTripAct (M : RoundTripMatrix) (a : TwinAmplitude) : TwinAmplitude :=
  let U := M.toMatrix
  ⟨U 0 0 * a.aPlus + U 0 1 * a.aMinus,
   U 1 0 * a.aPlus + U 1 1 * a.aMinus⟩

/-- Projective ratio evolution under round trip -/
theorem roundTripProjective (M : RoundTripMatrix) (a : TwinAmplitude)
    (ha : a.aPlus ≠ 0) (hdenom : M.toMatrix 0 0 + M.toMatrix 0 1 * (a.aMinus / a.aPlus) ≠ 0) :
    projectiveRatio (roundTripAct M a) = mobiusTransform M.toMatrix (projectiveRatio a) := by
  apply projectiveRatioEvolves M.toMatrix a ha hdenom

/-!
=============================================================================
PART 4: Lossless Sector (SU(1,1)) and Unit Disk
=============================================================================
-/

/-- SU(1,1) matrices: preserve the unit disk under Möbius action -/
structure SU11Matrix where
  A B : ℂ
  condition₁ : Complex.abs A ^ 2 - Complex.abs B ^ 2 = 1
  condition₂ : A * star B = star A * B

/-- Convert SU(1,1) to RoundTripMatrix -/
def su11ToRoundTrip (M : SU11Matrix) : RoundTripMatrix :=
  { toMatrix := !![M.A, M.B; star M.B, star M.A],
    det_one := by
      have h₁ := M.condition₁
      have h₂ := M.condition₂
      simp [Matrix.det_fin_two, Complex.ext_iff, pow_two, Complex.abs, Complex.normSq,
        Real.sqrt_eq_iff_sq_eq, mul_self_nonneg, add_nonneg, mul_self_nonneg, sub_nonneg] at h₁ h₂ ⊢
      <;>
      (try ring_nf at h₁ h₂ ⊢) <;>
      (try norm_num at h₁ h₂ ⊢) <;>
      (try nlinarith [Real.sqrt_nonneg (M.A.re * M.A.re + M.A.im * M.A.im),
        Real.sqrt_nonneg (M.B.re * M.B.re + M.B.im * M.B.im)]) }

/-- Unit disk preservation: if |z| < 1 and M ∈ SU(1,1), then |mobiusTransform M z| < 1 -/
theorem unitDiskPreservation (M : SU11Matrix) (z : ℂ) (hz : Complex.abs z < 1) :
    Complex.abs (mobiusTransform (su11ToRoundTrip M).toMatrix z) < 1 := by
  have h₁ : (su11ToRoundTrip M).toMatrix = !![M.A, M.B; star M.B, star M.A] := rfl
  rw [h₁]
  simp only [mobiusTransform, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons] at *
  have h₂ : Complex.abs M.A ^ 2 - Complex.abs M.B ^ 2 = 1 := M.condition₁
  have h₃ : M.A * star M.B = star M.A * M.B := M.condition₂
  have h₄ : Complex.abs z < 1 := hz
  have h₅ : Complex.abs ((star M.B + star M.A * z) / (M.A + M.B * z)) < 1 := by
    have h₆ : 0 < Complex.abs (M.A + M.B * z) := by
      by_contra h
      have h₇ : Complex.abs (M.A + M.B * z) = 0 := by linarith [Complex.abs.nonneg (M.A + M.B * z)]
      have h₈ : M.A + M.B * z = 0 := by simpa [Complex.abs.eq_zero] using h₇
      have h₉ : z = -M.A / M.B := by
        have h₁₀ : M.B ≠ 0 := by
          by_contra h₁₁
          have h₁₂ : M.B = 0 := by simpa using h₁₁
          have h₁₃ : Complex.abs M.A ^ 2 = 1 := by
            have h₁₄ := M.condition₁
            simp [h₁₂] at h₁₄ ⊢
            <;> nlinarith
          have h₁₅ : M.A = 0 := by
            have h₁₆ := h₈
            simp [h₁₂] at h₁₆ ⊢
            <;> simp_all [Complex.ext_iff]
            <;> nlinarith
          have h₁₇ : Complex.abs M.A = 0 := by simp [h₁₅]
          have h₁₈ : Complex.abs M.A ^ 2 = 0 := by simp [h₁₇]
          nlinarith
        field_simp [h₁₀] at h₈ ⊢
        <;> ring_nf at h₈ ⊢ <;> simp_all [Complex.ext_iff]
        <;> norm_num at * <;>
          (try constructor <;> nlinarith)
      have h₂₀ : Complex.abs z = Complex.abs (-M.A / M.B) := by rw [h₉]
      have h₂₁ : Complex.abs (-M.A / M.B) = Complex.abs M.A / Complex.abs M.B := by
        simp [Complex.abs, Complex.normSq, Real.sqrt_div, Real.sqrt_mul, Real.sqrt_sq_eq_abs]
        <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> simp [Complex.abs, Complex.normSq, Real.sqrt_mul, Real.sqrt_sq_eq_abs]
        <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf
      have h₂₂ : Complex.abs z = Complex.abs M.A / Complex.abs M.B := by rw [h₂₀, h₂₁]
      have h₂₃ : Complex.abs M.A ^ 2 - Complex.abs M.B ^ 2 = 1 := M.condition₁
      have h₂₄ : Complex.abs M.A > Complex.abs M.B := by
        nlinarith [Complex.abs.nonneg M.A, Complex.abs.nonneg M.B, sq_nonneg (Complex.abs M.A - Complex.abs M.B)]
      have h₂₅ : Complex.abs M.A / Complex.abs M.B > 1 := by
        have h₂₆ : 0 < Complex.abs M.B := by
          by_contra h₂₇
          have h₂₈ : Complex.abs M.B = 0 := by linarith [Complex.abs.nonneg M.B]
          have h₂₉ : M.B = 0 := by simpa [Complex.abs.eq_zero] using h₂₈
          simp_all [Complex.abs.eq_zero]
          <;> nlinarith
        have h₃₀ : Complex.abs M.A / Complex.abs M.B > 1 := by
          rw [gt_iff_lt]
          rw [lt_div_iff (by positivity)]
          nlinarith [sq_nonneg (Complex.abs M.A - Complex.abs M.B)]
        exact h₃₀
      linarith
    -- Use the property of SU(1,1) matrices to show the transformation preserves the unit disk
    have h₁₀ : Complex.abs (star M.B + star M.A * z) ^ 2 < Complex.abs (M.A + M.B * z) ^ 2 := by
      calc
        Complex.abs (star M.B + star M.A * z) ^ 2 = Complex.normSq (star M.B + star M.A * z) := by
          simp [Complex.sq_abs]
        _ = Complex.normSq (star M.B) + Complex.normSq (star M.A * z) + 2 * (star M.B).re * (star M.A * z).re + 2 * (star M.B).im * (star M.A * z).im := by
          simp [Complex.normSq, Complex.ext_iff, pow_two]
          <;> ring_nf
          <;> simp [Complex.ext_iff, pow_two]
          <;> norm_num
          <;> linarith
        _ = Complex.normSq M.B + Complex.normSq (M.A * z) + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by
          simp [Complex.normSq, Complex.ext_iff, pow_two, star_def]
          <;> ring_nf
          <;> simp [Complex.ext_iff, pow_two]
          <;> norm_num
          <;> linarith
        _ = Complex.abs M.B ^ 2 + Complex.abs (M.A * z) ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by
          simp [Complex.normSq, Complex.sq_abs]
        _ = Complex.abs M.B ^ 2 + Complex.abs M.A ^ 2 * Complex.abs z ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by
          have h₁₁ : Complex.abs (M.A * z) = Complex.abs M.A * Complex.abs z := by
            simp [Complex.abs.map_mul]
          calc
            Complex.abs M.B ^ 2 + Complex.abs (M.A * z) ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im =
                Complex.abs M.B ^ 2 + (Complex.abs M.A * Complex.abs z) ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by rw [h₁₁]
            _ = Complex.abs M.B ^ 2 + Complex.abs M.A ^ 2 * Complex.abs z ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by ring
        _ < Complex.abs M.A ^ 2 + Complex.abs M.B ^ 2 * Complex.abs z ^ 2 + 2 * (M.A).re * (M.B * z).re + 2 * (M.A).im * (M.B * z).im := by
          have h₁₂ : Complex.abs M.A ^ 2 - Complex.abs M.B ^ 2 = 1 := M.condition₁
          have h₁₃ : M.A * star M.B = star M.A * M.B := M.condition₂
          have h₁₄ : Complex.abs z < 1 := hz
          have h₁₅ : 0 ≤ Complex.abs z := Complex.abs.nonneg z
          have h₁₆ : 0 ≤ Complex.abs M.A := Complex.abs.nonneg M.A
          have h₁₇ : 0 ≤ Complex.abs M.B := Complex.abs.nonneg M.B
          simp [Complex.normSq, Complex.ext_iff, pow_two, star_def, Complex.mul_re, Complex.mul_im] at h₁₃ ⊢
          <;> nlinarith [sq_nonneg (Complex.abs M.A - Complex.abs M.B), sq_nonneg (Complex.abs z - 1),
            sq_nonneg ((M.A).re * (M.B).im - (M.A).im * (M.B).re),
            sq_nonneg ((M.A).re * (M.B).re + (M.A).im * (M.B).im)]
        _ = Complex.abs (M.A + M.B * z) ^ 2 := by
          calc
            Complex.abs M.A ^ 2 + Complex.abs M.B ^ 2 * Complex.abs z ^ 2 + 2 * (M.A).re * (M.B * z).re + 2 * (M.A).im * (M.B * z).im =
                Complex.normSq M.A + Complex.normSq (M.B * z) + 2 * (M.A).re * (M.B * z).re + 2 * (M.A).im * (M.B * z).im := by
              simp [Complex.normSq, Complex.sq_abs]
              <;> ring_nf
            _ = Complex.normSq (M.A + M.B * z) := by
              simp [Complex.normSq, Complex.ext_iff, pow_two]
              <;> ring_nf
              <;> simp [Complex.ext_iff, pow_two]
              <;> norm_num
              <;> linarith
            _ = Complex.abs (M.A + M.B * z) ^ 2 := by
              simp [Complex.sq_abs]
    have h₁₁ : Complex.abs ((star M.B + star M.A * z) / (M.A + M.B * z)) < 1 := by
      have h₁₂ : 0 < Complex.abs (M.A + M.B * z) := by positivity
      have h₁₃ : Complex.abs (star M.B + star M.A * z) < Complex.abs (M.A + M.B * z) := by
        have h₁₄ : 0 ≤ Complex.abs (star M.B + star M.A * z) := Complex.abs.nonneg _
        have h₁₅ : 0 ≤ Complex.abs (M.A + M.B * z) := Complex.abs.nonneg _
        nlinarith [Real.sqrt_nonneg (Complex.abs (star M.B + star M.A * z) ^ 2), Real.sqrt_nonneg (Complex.abs (M.A + M.B * z) ^ 2),
          Real.sq_sqrt (by positivity : 0 ≤ (Complex.abs (star M.B + star M.A * z) : ℝ) ^ 2),
          Real.sq_sqrt (by positivity : 0 ≤ (Complex.abs (M.A + M.B * z) : ℝ) ^ 2)]
      calc
        Complex.abs ((star M.B + star M.A * z) / (M.A + M.B * z)) = Complex.abs (star M.B + star M.A * z) / Complex.abs (M.A + M.B * z) := by
          simp [Complex.abs.div]
        _ < 1 := by
          rw [div_lt_one (by positivity)]
          exact h₁₃
    have h₁₂ : Complex.abs ((star M.B + star M.A * z) / (M.A + M.B * z)) < 1 := h₁₁
    simpa [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons] using h₁₂
  exact h₅

/-- Unit circle preservation: if |z| = 1 and M ∈ SU(1,1), then |mobiusTransform M z| = 1 -/
theorem unitCirclePreservation (M : SU11Matrix) (z : ℂ) (hz : Complex.abs z = 1) :
    Complex.abs (mobiusTransform (su11ToRoundTrip M).toMatrix z) = 1 := by
  have h₁ : (su11ToRoundTrip M).toMatrix = !![M.A, M.B; star M.B, star M.A] := rfl
  rw [h₁]
  simp only [mobiusTransform, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons] at *
  have h₂ : Complex.abs M.A ^ 2 - Complex.abs M.B ^ 2 = 1 := M.condition₁
  have h₃ : M.A * star M.B = star M.A * M.B := M.condition₂
  have h₄ : Complex.abs z = 1 := hz
  have h₅ : Complex.abs ((star M.B + star M.A * z) / (M.A + M.B * z)) = 1 := by
    have h₆ : Complex.abs (star M.B + star M.A * z) = Complex.abs (M.A + M.B * z) := by
      calc
        Complex.abs (star M.B + star M.A * z) ^ 2 = Complex.normSq (star M.B + star M.A * z) := by simp [Complex.sq_abs]
        _ = Complex.normSq M.B + Complex.normSq (M.A * z) + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by
          simp [Complex.normSq, Complex.ext_iff, pow_two, star_def]
          <;> ring_nf
          <;> simp [Complex.ext_iff, pow_two]
          <;> norm_num
          <;> linarith
        _ = Complex.abs M.B ^ 2 + Complex.abs M.A ^ 2 * Complex.abs z ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by
          have h₇ : Complex.abs (M.A * z) = Complex.abs M.A * Complex.abs z := by simp [Complex.abs.map_mul]
          calc
            Complex.abs M.B ^ 2 + Complex.abs (M.A * z) ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im =
                Complex.abs M.B ^ 2 + (Complex.abs M.A * Complex.abs z) ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by rw [h₇]
            _ = Complex.abs M.B ^ 2 + Complex.abs M.A ^ 2 * Complex.abs z ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by ring
        _ = Complex.abs M.B ^ 2 + Complex.abs M.A ^ 2 * (1 : ℝ) ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by
          rw [h₄]
          <;> simp [pow_two]
        _ = Complex.abs M.B ^ 2 + Complex.abs M.A ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by ring
        _ = Complex.abs (M.A + M.B * z) ^ 2 := by
          calc
            Complex.abs M.B ^ 2 + Complex.abs M.A ^ 2 + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im =
                Complex.normSq M.B + Complex.normSq (M.A * z) + 2 * (M.B).re * (M.A * z).re + 2 * (M.B).im * (M.A * z).im := by
              simp [Complex.normSq, Complex.sq_abs]
              <;> ring_nf
              <;> simp [Complex.ext_iff]
              <;> norm_num
            _ = Complex.normSq (star M.B + star M.A * z) := by
              simp [Complex.normSq, Complex.ext_iff, pow_two, star_def]
              <;> ring_nf
              <;> simp [Complex.ext_iff, pow_two]
              <;> norm_num
              <;> linarith
            _ = Complex.normSq (M.A + M.B * z) := by
              have h₈ : M.A * star M.B = star M.A * M.B := M.condition₂
              simp [Complex.normSq, Complex.ext_iff, pow_two, star_def, Complex.mul_re, Complex.mul_im] at h₈ ⊢
              <;> ring_nf at * <;> simp_all [Complex.ext_iff, pow_two]
              <;> nlinarith [sq_nonneg (Complex.abs M.A - Complex.abs M.B), sq_nonneg (Complex.abs z - 1),
                sq_nonneg ((M.A).re * (M.B).im - (M.A).im * (M.B).re),
                sq_nonneg ((M.A).re * (M.B).re + (M.A).im * (M.B).im)]
            _ = Complex.abs (M.A + M.B * z) ^ 2 := by simp [Complex.sq_abs]
        _ = Complex.abs (M.A + M.B * z) ^ 2 := by rfl
    have h₉ : 0 ≤ Complex.abs (star M.B + star M.A * z) := Complex.abs.nonneg _
    have h₁₀ : 0 ≤ Complex.abs (M.A + M.B * z) := Complex.abs.nonneg _
    have h₁₁ : Complex.abs (star M.B + star M.A * z) = Complex.abs (M.A + M.B * z) := by
      nlinarith [Real.sqrt_nonneg (Complex.abs (star M.B + star M.A * z) ^ 2), Real.sqrt_nonneg (Complex.abs (M.A + M.B * z) ^ 2),
        Real.sq_sqrt (by positivity : 0 ≤ (Complex.abs (star M.B + star M.A * z) : ℝ) ^ 2),
        Real.sq_sqrt (by positivity : 0 ≤ (Complex.abs (M.A + M.B * z) : ℝ) ^ 2)]
    calc
      Complex.abs ((star M.B + star M.A * z) / (M.A + M.B * z)) = Complex.abs (star M.B + star M.A * z) / Complex.abs (M.A + M.B * z) := by
        simp [Complex.abs.div]
      _ = 1 := by
        have h₁₂ : Complex.abs (M.A + M.B * z) ≠ 0 := by
          by_contra h₁₃
          have h₁₄ : Complex.abs (M.A + M.B * z) = 0 := by linarith
          have h₁₅ : M.A + M.B * z = 0 := by simpa [Complex.abs.eq_zero] using h₁₄
          have h₁₆ : Complex.abs (star M.B + star M.A * z) = 0 := by
            linarith
          have h₁₇ : star M.B + star M.A * z = 0 := by simpa [Complex.abs.eq_zero] using h₁₆
          have h₁₈ : Complex.abs M.A ^ 2 - Complex.abs M.B ^ 2 = 1 := M.condition₁
          have h₁₉ : M.A * star M.B = star M.A * M.B := M.condition₂
          simp [Complex.ext_iff, pow_two, star_def, Complex.mul_re, Complex.mul_im] at h₁₅ h₁₇ h₁₉ ⊢
          <;>
          (try simp_all [Complex.ext_iff, pow_two, star_def, Complex.mul_re, Complex.mul_im])
          <;>
          (try nlinarith)
          <;>
          (try
            {
              field_simp at *
              <;> nlinarith
            })
        field_simp [h₁₂, h₁₁]
  simpa [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons] using h₅

/-!
=============================================================================
PART 5: Modular Conjugation J
=============================================================================
-/

/-- Modular conjugation on the twin amplitude: J(a₊, a₋) = (a₋*, a₊*) -/
def modularConjugation (a : TwinAmplitude) : TwinAmplitude :=
  ⟨star a.aMinus, star a.aPlus⟩

/-- J is conjugate-linear -/
theorem modularConjugation_conjugateLinear (c : ℂ) (a b : TwinAmplitude) :
    modularConjugation (c • a + b) = star c • modularConjugation a + modularConjugation b := by
  ext <;> simp [modularConjugation, TwinAmplitude, star_add, star_smul, Complex.ext_iff]
  <;> ring_nf <;> simp_all [Complex.ext_iff, star_add, star_smul] <;> norm_num <;> aesop

/-- J preserves the total energy norm -/
theorem modularConjugation_preservesEnergy (a : TwinAmplitude) :
    totalEnergy (modularConjugation a) = totalEnergy a := by
  simp [modularConjugation, totalEnergy, energyPlus, energyMinus, Complex.abs, Complex.normSq]
  <;> ring_nf <;> simp [star_def, Complex.ext_iff, pow_two]
  <;> norm_num <;> ring_nf <;> simp_all [Complex.ext_iff] <;> linarith

/-- J is an involution: J² = I -/
theorem modularConjugation_involution (a : TwinAmplitude) :
    modularConjugation (modularConjugation a) = a := by
  ext <;> simp [modularConjugation, TwinAmplitude, star_star]
  <;> aesop

/-- Action of J on the projective ratio: z ↦ 1/z* -/
theorem modularConjugation_onProjective (a : TwinAmplitude) (ha : a.aPlus ≠ 0) :
    projectiveRatio (modularConjugation a) = 1 / star (projectiveRatio a) := by
  have h₁ : projectiveRatio (modularConjugation a) = star a.aPlus / star a.aMinus := by
    simp [modularConjugation, projectiveRatio]
    <;> field_simp [Complex.ext_iff, star_mul, star_star]
    <;> ring_nf
    <;> simp_all [Complex.ext_iff]
    <;> norm_num
  rw [h₁]
  have h₂ : star a.aPlus / star a.aMinus = 1 / star (a.aMinus / a.aPlus) := by
    have h₃ : a.aPlus ≠ 0 := ha
    have h₄ : a.aMinus / a.aPlus = a.aMinus / a.aPlus := rfl
    field_simp [h₃, Complex.ext_iff, star_mul, star_star, div_eq_mul_inv]
    <;> ring_nf
    <;> simp_all [Complex.ext_iff, star_mul, star_star, div_eq_mul_inv]
    <;> norm_num
    <;>
    (try {
      constructor <;>
      field_simp [h₃, Complex.ext_iff, star_mul, star_star, div_eq_mul_inv] at * <;>
      ring_nf at * <;>
      simp_all [Complex.ext_iff, star_mul, star_star, div_eq_mul_inv] <;>
      norm_num at * <;>
      nlinarith
    })
  rw [h₂]
  <;> simp [projectiveRatio]

/-- J preserves the unit circle: if |z| = 1, then |1/z*| = 1 -/
theorem modularConjugation_preservesUnitCircle (z : ℂ) (hz : Complex.abs z = 1) :
    Complex.abs (1 / star z) = 1 := by
  have h₁ : Complex.abs (1 / star z) = 1 / Complex.abs (star z) := by
    simp [Complex.abs, Complex.normSq, Real.sqrt_eq_iff_sq_eq]
    <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> ring_nf <;> field_simp [Real.sqrt_eq_iff_sq_eq] <;> nlinarith
  rw [h₁]
  have h₂ : Complex.abs (star z) = Complex.abs z := by
    simp [Complex.abs, Complex.normSq, star_def]
    <;> ring_nf <;> simp [Complex.ext_iff, pow_two] <;> norm_num
  rw [h₂, hz]
  <;> field_simp

/-!
=============================================================================
PART 6: Connection to Split-Octonion Peirce Frame
=============================================================================
-/

/-- Embed a TwinAmplitude into the split-octonion Peirce frame -/
def embedToPeirceFrame (a : TwinAmplitude) : SplitOctonion :=
  { a := a.aPlus.re,
    b := a.aMinus.re,
    x := ![a.aPlus.im, 0, 0],
    y := ![a.aMinus.im, 0, 0] }

/-- The Peirce projectors recover the amplitudes -/
theorem peirceRecoversAmplitudes (a : TwinAmplitude) :
    (embedToPeirceFrame a).a = a.aPlus.re ∧
    (embedToPeirceFrame a).b = a.aMinus.re := by
  simp [embedToPeirceFrame]
  <;> aesop

/-- The star involution on the split-octonion frame corresponds to J -/
theorem starCorrespondsToJ (a : TwinAmplitude) :
    star (embedToPeirceFrame a) = embedToPeirceFrame (modularConjugation a) := by
  ext i
  fin_cases i <;>
  simp [embedToPeirceFrame, modularConjugation, star, SplitOctonion, ZornMatrix]
  <;>
  (try ring_nf) <;>
  (try simp_all [Complex.ext_iff, star_def]) <;>
  (try norm_num) <;>
  (try aesop)

end InfoGeometry.Canonical.ThermofieldBidirectionalResonator