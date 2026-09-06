import InfoGeometry.Fibonacci.FibAnyonThm3
import InfoGeometry.Physics.B3PresentedGroup

/-!
# The `R² + I` spectral obstruction

The Fibonacci `R`-matrix has diagonal eigenvalues `q⁻⁴` and `q³`, where
`q⁵ = 1`.  Neither squared eigenvalue is `-1`; consequently `R² + I` is
invertible.  This is the concrete negative spectral statement available on
the existing Fibonacci carrier.
-/

namespace InfoGeometry.Fibonacci.FibAnyonSpectralObstruction

open Matrix
open InfoGeometry.Fibonacci.FibAnyonThm3
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Physics.JonesBraidB3

private theorem q_ne_neg_one : q ≠ -1 := by
  intro h
  have hpow := q_fifth_power
  rw [h] at hpow
  norm_num at hpow

private theorem q_sq_ne_neg_one : q ^ 2 ≠ -1 := by
  intro h
  have hpow : q ^ 5 = 1 := q_fifth_power
  have hq4 : q ^ 4 = 1 := by
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = (-1 : ℂ) ^ 2 := by rw [h]
      _ = 1 := by norm_num
  have hq : q = 1 := by
    calc
      q = q ^ 4 * q := by rw [hq4]; ring
      _ = q ^ 5 := by ring
      _ = 1 := hpow
  rw [hq] at h
  norm_num at h

theorem R_sq_add_one_det_ne_zero :
    Matrix.det (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0 := by
  intro hdet
  have hdiag :
      (q ^ (-4 : ℤ) * q ^ (-4 : ℤ) + 1) *
          (q ^ 3 * q ^ 3 + 1) = 0 := by
    simpa [R, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.one_apply] using hdet
  rcases mul_eq_zero.mp hdiag with hleft | hright
  · have hleft' : q ^ 2 + 1 = 0 := by
      have hq8 : q ^ 8 = -1 := by
        field_simp [q_ne_zero] at hleft
        simp at hleft
        linear_combination hleft
      have hq3 : q ^ 3 = -1 := by
        calc
          q ^ 3 = q ^ 3 * 1 := by ring
          _ = q ^ 3 * q ^ 5 := by rw [q_fifth_power]
          _ = q ^ 8 := by ring
          _ = -1 := hq8
      calc
        q ^ 2 + 1 = q ^ 2 + q ^ 5 := by rw [q_fifth_power]
        _ = q ^ 2 + q ^ 2 * q ^ 3 := by ring
        _ = q ^ 2 + q ^ 2 * (-1) := by rw [hq3]
        _ = 0 := by ring
    exact q_sq_ne_neg_one (eq_neg_of_add_eq_zero_left hleft')
  · have hright' : q + 1 = 0 := by
      have hq6 : q ^ 6 = -1 := by
        have htmp := hright
        ring_nf at htmp
        linear_combination htmp
      have hq6eq : q ^ 6 = q := by
        calc
          q ^ 6 = q * q ^ 5 := by ring
          _ = q := by rw [q_fifth_power]; simp
      have hqneg : q = -1 := by
        rw [← hq6eq]
        exact hq6
      exact add_eq_zero_iff_eq_neg.mpr hqneg
    exact q_ne_neg_one (eq_neg_of_add_eq_zero_left hright')

/-! The determinant obstruction has the expected linear-algebra consequence. -/

theorem R_sq_add_one_trivial_kernel
    (x : Fin 2 → ℂ)
    (hx : (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec x = 0) :
    x = 0 := by
  have hdet := R_sq_add_one_det_ne_zero
  have hunit : IsUnit (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by
      rwa [isUnit_iff_ne_zero])
  let u := hunit.unit
  have hu_val :
      (u : Matrix (Fin 2) (Fin 2) ℂ) =
        R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ) := hunit.unit_spec
  have h_inv_mul :
      (u⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *
          (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    rw [← hu_val]
    simp
  calc
    x = (1 : Matrix (Fin 2) (Fin 2) ℂ).mulVec x := by simp
    _ = ((u⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *
        (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ))).mulVec x := by
          rw [h_inv_mul]
    _ = (u⁻¹ : Matrix (Fin 2) (Fin 2) ℂ).mulVec
        ((R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec x) := by
          rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hx]; simp

theorem R_sq_add_one_kernel_eq_bot :
    LinearMap.ker
        ((R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVecLin) =
      (⊥ : Submodule ℂ (Fin 2 → ℂ)) := by
  apply le_antisymm
  · intro x hx
    have hxzero : x = 0 := R_sq_add_one_trivial_kernel x hx
    simp [hxzero]
  · exact bot_le

/-! The obstruction kills every intertwiner for the first native `B₃`
generator.  This is the concrete representation-level negative theorem; no
unbundled or hypothetical `ℂ²_Fib` representation is introduced. -/

theorem no_first_B3_generator_intertwiner
    (T : Matrix (Fin 2) (Fin 8) ℂ)
    (hT : T * InfoGeometry.Physics.JonesBraidB3.s0 = R * T) :
    T = 0 := by
  have hsq :
      T * (InfoGeometry.Physics.JonesBraidB3.s0 *
          InfoGeometry.Physics.JonesBraidB3.s0) = (R * R) * T := by
    calc
      T * (InfoGeometry.Physics.JonesBraidB3.s0 *
          InfoGeometry.Physics.JonesBraidB3.s0) =
          (T * InfoGeometry.Physics.JonesBraidB3.s0) *
            InfoGeometry.Physics.JonesBraidB3.s0 := by
            simp [Matrix.mul_assoc]
      _ = (R * T) * InfoGeometry.Physics.JonesBraidB3.s0 := by rw [hT]
      _ = R * (T * InfoGeometry.Physics.JonesBraidB3.s0) := by
        simp [Matrix.mul_assoc]
      _ = (R * R) * T := by rw [hT]; simp [Matrix.mul_assoc]
  have hzero :
      (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * T = 0 := by
    calc
      (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * T =
          (R * R) * T + T := by
            rw [Matrix.add_mul, Matrix.one_mul]
      _ = T * (InfoGeometry.Physics.JonesBraidB3.s0 *
          InfoGeometry.Physics.JonesBraidB3.s0) + T := by rw [← hsq]
      _ = 0 := by rw [s0_sq_eq_neg_one]; simp
  have hdet :
      (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 :=
    R_sq_add_one_det_ne_zero
  have hunit : IsUnit (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hdet)
  let u := hunit.unit
  have hu_val :
      (u : Matrix (Fin 2) (Fin 2) ℂ) =
        R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ) := hunit.unit_spec
  have h_inv_mul :
      (u⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *
          (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    rw [← hu_val]
    simp
  calc
    T = (1 : Matrix (Fin 2) (Fin 2) ℂ) * T := by simp
    _ = ((u⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *
        (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ))) * T := by
          rw [h_inv_mul]
    _ = (u⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) *
        ((R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * T) := by
          rw [Matrix.mul_assoc]
    _ = 0 := by rw [hzero]; simp

/-! The concrete finite Hom-space for the two presented B₃ generator
representations.  This is the matrix realization of generator-wise group
intertwiners; no hypothetical Fibonacci B₃ representation is introduced. -/

def b3RepresentationHom : Submodule ℂ (Matrix (Fin 2) (Fin 8) ℂ) where
  carrier := {T | T * InfoGeometry.Physics.JonesBraidB3.s0 = R * T ∧
    T * InfoGeometry.Physics.JonesBraidB3.s1 =
      InfoGeometry.Fibonacci.FibAnyonThm3.R * T}
  zero_mem' := by
    constructor <;> simp
  add_mem' := by
    intro T U hT hU
    constructor
    · simpa [Matrix.add_mul, Matrix.mul_add] using congrArg₂ (· + ·) hT.1 hU.1
    · simpa [Matrix.add_mul, Matrix.mul_add] using congrArg₂ (· + ·) hT.2 hU.2
  smul_mem' := by
    intro c T hT
    constructor
    · simpa [Matrix.smul_mul, Matrix.mul_smul] using congrArg (c • ·) hT.1
    · simpa [Matrix.smul_mul, Matrix.mul_smul] using congrArg (c • ·) hT.2

theorem mem_b3RepresentationHom_iff (T : Matrix (Fin 2) (Fin 8) ℂ) :
    T ∈ b3RepresentationHom ↔
      T * InfoGeometry.Physics.JonesBraidB3.s0 = R * T ∧
        T * InfoGeometry.Physics.JonesBraidB3.s1 = R * T := by
  rfl

theorem b3RepresentationHom_eq_bot :
    b3RepresentationHom = ⊥ := by
  apply le_antisymm
  · intro T hT
    have hzero : T = 0 :=
      no_first_B3_generator_intertwiner T hT.1
    simpa [hzero]
  · exact bot_le

theorem b3RepresentationHom_finrank_zero :
    Module.finrank ℂ b3RepresentationHom = 0 := by
  rw [b3RepresentationHom_eq_bot]
  simp

end InfoGeometry.Fibonacci.FibAnyonSpectralObstruction
