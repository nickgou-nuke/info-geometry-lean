import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Canonical.KreinDoubledCartanPeirceBridge
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A finite polarized shear and spin frame

This finite real matrix model reuses the native `Cl(1,1)` representation and
the existing two sheet Peirce projectors.  Its generator is
`L = s J1 + w Eminus = [[0, s+w], [s-w, 0]]`.

The elliptic condition `|s| < w` gives a positive quadratic energy whose
directional derivative along `x' = L x - nu x` is exactly `-2 nu` times that
energy.  No Navier--Stokes equation, continuum completion, or fluid regularity
claim is encoded by this finite model.
-/

noncomputable section

namespace InfoGeometry.Canonical.PolarizedShearSpinFrame

open Matrix

abbrev Mat2 := InfoGeometry.Clifford.Cl11Matrix.Mat2
abbrev Vec2 := Fin 2 → ℝ

open InfoGeometry.Clifford.Cl11Matrix (J1 Eminus)
open InfoGeometry.Canonical.KreinDoubledCartanPeirce (P_plus P_minus)

/-- Symmetric shear and skew rotation in the existing real Clifford basis. -/
def generator (s w : ℝ) : Mat2 := s • J1 + w • Eminus

theorem generator_eq (s w : ℝ) :
    generator s w = !![0, s + w; s - w, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [generator, J1, Eminus, sub_eq_add_neg]

/-- The sign of `s²-w²` is the finite generator's quadratic discriminant. -/
theorem generator_sq (s w : ℝ) :
    generator s w * generator s w = (s ^ 2 - w ^ 2) • (1 : Mat2) := by
  rw [generator_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The negative-to-positive transfer carries amplitude `s+w`. -/
theorem plusMinus_corner (s w : ℝ) :
    P_plus * generator s w * P_minus = !![0, s + w; 0, 0] := by
  rw [generator_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The positive-to-negative transfer carries amplitude `s-w`. -/
theorem minusPlus_corner (s w : ℝ) :
    P_minus * generator s w * P_plus = !![0, 0; s - w, 0] := by
  rw [generator_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, Matrix.mul_apply, Fin.sum_univ_two]

theorem generator_eq_offDiagonal_corners (s w : ℝ) :
    generator s w =
      P_plus * generator s w * P_minus +
        P_minus * generator s w * P_plus := by
  rw [plusMinus_corner, minusPlus_corner, generator_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The transpose-symmetric component is exactly the shear term. -/
theorem symmetric_part (s w : ℝ) :
    (1 / 2 : ℝ) • (generator s w + (generator s w)ᵀ) = s • J1 := by
  rw [generator_eq]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [J1] <;> ring

/-- The transpose-skew component is exactly the rotation term. -/
theorem skew_part (s w : ℝ) :
    (1 / 2 : ℝ) • (generator s w - (generator s w)ᵀ) = w • Eminus := by
  rw [generator_eq]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [Eminus] <;> ring

/-- The quadratic energy adapted to the two off-diagonal amplitudes. -/
def energy (s w : ℝ) (x : Vec2) : ℝ :=
  (w - s) * x 0 ^ 2 + (w + s) * x 1 ^ 2

/-- Coercivity is quantitative and uses the Euclidean coordinate square sum. -/
theorem energy_lower_bound (s w : ℝ) (x : Vec2) :
    (w - |s|) * (x 0 ^ 2 + x 1 ^ 2) ≤ energy s w x := by
  have hminus : 0 ≤ |s| - s := sub_nonneg.mpr (le_abs_self s)
  have hplus : 0 ≤ |s| + s := by linarith [neg_abs_le s]
  have h0 := mul_nonneg hminus (sq_nonneg (x 0))
  have h1 := mul_nonneg hplus (sq_nonneg (x 1))
  dsimp [energy]
  nlinarith

theorem energy_upper_bound (s w : ℝ) (x : Vec2) :
    energy s w x ≤ (w + |s|) * (x 0 ^ 2 + x 1 ^ 2) := by
  have hminus : 0 ≤ |s| - s := sub_nonneg.mpr (le_abs_self s)
  have hplus : 0 ≤ |s| + s := by linarith [neg_abs_le s]
  have h0 := mul_nonneg hplus (sq_nonneg (x 0))
  have h1 := mul_nonneg hminus (sq_nonneg (x 1))
  dsimp [energy]
  nlinarith

theorem energy_nonneg {s w : ℝ} (h : |s| < w) (x : Vec2) :
    0 ≤ energy s w x := by
  have hgap : 0 ≤ w - |s| := le_of_lt (sub_pos.mpr h)
  exact le_trans (mul_nonneg hgap (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (energy_lower_bound s w x)

theorem energy_pos {s w : ℝ} (h : |s| < w) {x : Vec2} (hx : x ≠ 0) :
    0 < energy s w x := by
  have hcoords : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    apply hx
    ext i
    fin_cases i <;> simp_all
  have hsq : 0 < x 0 ^ 2 + x 1 ^ 2 := by
    rcases hcoords with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 1)]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0)]
  exact lt_of_lt_of_le (mul_pos (sub_pos.mpr h) hsq) (energy_lower_bound s w x)

/-- The finite linear vector field with scalar damping. -/
def velocity (s w nu : ℝ) (x : Vec2) : Vec2 :=
  generator s w *ᵥ x - nu • x

theorem velocity_zero_coordinate (s w nu : ℝ) (x : Vec2) :
    velocity s w nu x 0 = (s + w) * x 1 - nu * x 0 := by
  simp [velocity, generator_eq, dotProduct, Fin.sum_univ_two]

theorem velocity_one_coordinate (s w nu : ℝ) (x : Vec2) :
    velocity s w nu x 1 = (s - w) * x 0 - nu * x 1 := by
  simp [velocity, generator_eq, dotProduct, Fin.sum_univ_two]

/-- The polynomial directional derivative of the quadratic energy. -/
def energyRate (s w : ℝ) (x v : Vec2) : ℝ :=
  2 * (w - s) * x 0 * v 0 + 2 * (w + s) * x 1 * v 1

/-- Shear and rotation cancel exactly in the adapted energy pairing. -/
theorem energyRate_velocity (s w nu : ℝ) (x : Vec2) :
    energyRate s w x (velocity s w nu x) = -2 * nu * energy s w x := by
  unfold energyRate
  rw [velocity_zero_coordinate, velocity_one_coordinate]
  dsimp [energy]
  ring

theorem energyRate_velocity_nonpos {s w nu : ℝ}
    (h : |s| < w) (hnu : 0 ≤ nu) (x : Vec2) :
    energyRate s w x (velocity s w nu x) ≤ 0 := by
  rw [energyRate_velocity]
  have henergy := energy_nonneg h x
  have hprod := mul_nonneg hnu henergy
  nlinarith

/-- The polynomial pairing is the actual derivative along every differentiable
trajectory satisfying the finite ODE at the stated time. -/
theorem hasDerivAt_energy {s w nu t : ℝ} {x : ℝ → Vec2}
    (hx : ∀ i : Fin 2, HasDerivAt (fun tau => x tau i)
      (velocity s w nu (x t) i) t) :
    HasDerivAt (fun tau => energy s w (x tau))
      (-2 * nu * energy s w (x t)) t := by
  have hbase := (((hx 0).mul (hx 0)).const_mul (w - s)).add
    (((hx 1).mul (hx 1)).const_mul (w + s))
  have hrate : HasDerivAt (fun tau => energy s w (x tau))
      (energyRate s w (x t) (velocity s w nu (x t))) t := by
    convert hbase using 1
    · funext tau
      simp [energy, pow_two]
    · dsimp [energyRate]
      ring
  rwa [energyRate_velocity] at hrate

end InfoGeometry.Canonical.PolarizedShearSpinFrame
