import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Complex Matrix

/-!
# Iwasawa (KAN) decomposition witness for `M₂(ℂ)`

This file records the group-theoretic skeleton:
* `K(θ)`: compact phase/rotation,
* `A(β)`: real dilation,
* `N(z)`: nilpotent shear/unipotent shift.

It also includes the Cayley compactification map
`W(s) = (s - 1/2)/(s + 1/2)`.

Tiny bridge note:
The determinant signatures here `(det K = 1, det A = 1, det N = 1)` and boundary sector `det (N - I) = 0`
mirror the `DeterminantSupergrading` package's parity/sign table: unit determinants for the
compact–dilation KAN core and grade boundary at zero determinant for the nilpotent channel.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cayley

/-- Compact phase (rotation) block: `K(θ)`. -/
def KPart (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp ((θ : ℂ) * Complex.I), 0; 0, Complex.exp (-((θ : ℂ) * Complex.I))]

/-- Real scaling (dilation) block: `A(β)`. -/
def APart (β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (β : ℂ), 0; 0, Complex.exp (-(β : ℂ))]

/-- Nilpotent shear (unipotent) block: `N(z)`. -/
def NPart (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, z; 0, 1]

/-- Shear displacement from identity, used for the null/Nilpotent boundary sector. -/
def nilpotentShear (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NPart z - (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Cayley compactification map on the one-dimensional spectral coordinate. -/
def cayleyCompact (s : ℂ) : ℂ := (s - (1 / 2 : ℂ)) / (s + (1 / 2 : ℂ))

/-- Inverse map of `cayleyCompact`. -/
def cayleyCompactInv (w : ℂ) : ℂ := ((1 / 2 : ℂ) * (1 + w)) / (1 - w)

/-- `K(θ)` has unit determinant. -/
theorem det_KPart (θ : ℝ) : (KPart θ).det = 1 := by
  let a : ℂ := (θ : ℂ) * Complex.I
  rw [Matrix.det_fin_two]
  simp [KPart]
  calc
    Complex.exp a * Complex.exp (-a) = Complex.exp (a + -a) := by
      simpa [a] using (Complex.exp_add a (-a)).symm
    _ = Complex.exp 0 := by simp
    _ = 1 := by simp
/-- `A(β)` has unit determinant. -/
theorem det_APart (β : ℝ) : (APart β).det = 1 := by
  have hfac :
      Complex.exp (β : ℂ) * Complex.exp (-(β : ℂ)) = 1 := by
    calc
      Complex.exp (β : ℂ) * Complex.exp (-(β : ℂ))
          = Complex.exp ((β : ℂ) + (-(β : ℂ))) := by
              rw [← Complex.exp_add]
      _ = Complex.exp 0 := by ring_nf
      _ = 1 := by simp
  rw [Matrix.det_fin_two]
  simp [APart, hfac]
/-- `N(z)` has unit determinant (unipotent determinant = 1). -/
theorem det_NPart (z : ℂ) : (NPart z).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [NPart]

/-- KAN product is an explicit triangular witness matrix. -/
theorem KAN_form (θ β : ℝ) (z : ℂ) :
    KPart θ * APart β * NPart z =
      !![Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (β : ℂ),
        Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (β : ℂ) * z;
        0, Complex.exp (-((θ : ℂ) * Complex.I)) * Complex.exp (-(β : ℂ))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KPart, APart, NPart, Matrix.mul_apply, Fin.sum_univ_two]

/-- The KAN product has determinant `1`. -/
theorem det_KAN (θ β : ℝ) (z : ℂ) : (KPart θ * APart β * NPart z).det = 1 := by
  rw [Matrix.det_mul, Matrix.det_mul, det_KPart, det_APart, det_NPart]
  norm_num

/-- Nilpotent shear displacement squares to zero: `(N(z)-I)^2 = 0`. -/
theorem nilpotentShear_sq (z : ℂ) :
    (nilpotentShear z) * (nilpotentShear z) = 0 := by
  have hform : nilpotentShear z = !![0, z; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilpotentShear, NPart]
  rw [hform]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Nilpotent shear displacement has vanishing determinant: `det(N(z)-I) = 0`. -/
theorem det_nilpotentShear (z : ℂ) : (nilpotentShear z).det = 0 := by
  have hform : nilpotentShear z = !![0, z; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nilpotentShear, NPart]
  rw [hform]
  rw [Matrix.det_fin_two]
  simp

/-- `cayleyCompact` and `cayleyCompactInv` are mutual inverses on their domains. -/
theorem cayley_inv (s : ℂ) (hs : s + (1 / 2 : ℂ) ≠ 0) :
    cayleyCompactInv (cayleyCompact s) = s := by
  unfold cayleyCompact cayleyCompactInv
  set t : ℂ := s + (1 / 2 : ℂ)
  have ht : t ≠ 0 := by
    simpa [t] using hs
  have hs1 : s - (1 / 2 : ℂ) = t - 1 := by
    dsimp [t]
    ring
  have hs2 : s = t - (1 / 2 : ℂ) := by
    dsimp [t]
    ring
  rw [hs1, hs2]
  field_simp [ht]
  ring

/-- `cayleyCompactInv` is also inverse on its denominator-open domain. -/
theorem inv_cayley (w : ℂ) (hw : w ≠ 1) :
    cayleyCompact (cayleyCompactInv w) = w := by
  unfold cayleyCompact cayleyCompactInv
  set t : ℂ := 1 - w
  have ht : t ≠ 0 := by
    intro h
    apply hw
    have h' : 1 - w = 0 := by
      simpa [t] using h
    have hw0 : w - 1 = 0 := by
      calc
        w - 1 = -(1 - w) := by ring_nf
        _ = -0 := by rw [h']
        _ = 0 := by ring_nf
    exact sub_eq_zero.mp hw0
  have h3 : w = 1 - t := by
    dsimp [t]
    ring_nf
  rw [h3]
  field_simp [ht]
  ring_nf

/-- Bundled dictionary-style lemma for K/A/N signatures. -/
theorem kan_cayley_dictionary (θ β : ℝ) (z : ℂ) :
    (KPart θ).det = 1 ∧
      (APart β).det = 1 ∧
      (NPart z).det = 1 ∧
      ((nilpotentShear z) * (nilpotentShear z) = 0) ∧
      ((nilpotentShear z).det = 0) := by
  constructor
  · exact det_KPart θ
  constructor
  · exact det_APart β
  constructor
  · exact det_NPart z
  constructor
  · exact nilpotentShear_sq z
  · exact det_nilpotentShear z

/-- Thermal-ray Cayley compactification on the real axis. -/
noncomputable def kanThermalCayley (β : ℝ) : ℝ :=
  (β - 1) / (β + 1)

/--
The thermal-ray Cayley compactification tends to the boundary point `1` at
zero temperature (`β → +∞`).

This is the mirror-package owner theorem used by GT's extracted seed file.
-/
theorem kanThermalCayley_tendsto_atTop_one :
    Filter.Tendsto kanThermalCayley Filter.atTop (nhds (1 : ℝ)) := by
  have hden :
      Filter.Tendsto (fun β : ℝ => β + 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro β hβ
    linarith
  have hzero :
      Filter.Tendsto (fun β : ℝ => (2 : ℝ) / (β + 1)) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hden
  have hmain :
      Filter.Tendsto (fun β : ℝ => 1 - (2 : ℝ) / (β + 1))
        Filter.atTop (nhds (1 - 0 : ℝ)) :=
    tendsto_const_nhds.sub hzero
  have heq :
      kanThermalCayley =ᶠ[Filter.atTop]
        fun β : ℝ => 1 - (2 : ℝ) / (β + 1) := by
    filter_upwards [Filter.eventually_gt_atTop (-1 : ℝ)] with β hβ
    have hβ' : β + 1 ≠ 0 := by linarith
    unfold kanThermalCayley
    field_simp [hβ']
    ring
  simpa using hmain.congr' heq.symm

end InfoGeometry.Canonical.Cayley
