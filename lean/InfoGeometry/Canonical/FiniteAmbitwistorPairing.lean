import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite ambitwistor incidence

This module records the finite algebraic shadow of an ambitwistor quadric.
It uses a vector and its dual covector, with projective rescaling handled
explicitly.  No claim about null-geodesic reduction or analytic twistor
cohomology is made here.
-/

namespace InfoGeometry.Canonical.FiniteAmbitwistorPairing

abbrev Twistor4 := Fin 4 → ℝ
abbrev DualTwistor4 := Fin 4 → ℝ

def pairing (W : DualTwistor4) (Z : Twistor4) : ℝ := ∑ i, W i * Z i

def IsNullPair (W : DualTwistor4) (Z : Twistor4) : Prop := pairing W Z = 0

@[simp] theorem pairing_zero_left (Z : Twistor4) : pairing 0 Z = 0 := by
  simp [pairing]

@[simp] theorem pairing_zero_right (W : DualTwistor4) : pairing W 0 = 0 := by
  simp [pairing]

theorem pairing_add_left (W₁ W₂ : DualTwistor4) (Z : Twistor4) :
    pairing (W₁ + W₂) Z = pairing W₁ Z + pairing W₂ Z := by
  simp [pairing, Pi.add_apply, Finset.sum_add_distrib, add_mul]

theorem pairing_add_right (W : DualTwistor4) (Z₁ Z₂ : Twistor4) :
    pairing W (Z₁ + Z₂) = pairing W Z₁ + pairing W Z₂ := by
  simp [pairing, Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem pairing_smul_left (c : ℝ) (W : DualTwistor4) (Z : Twistor4) :
    pairing (c • W) Z = c * pairing W Z := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, c * W i * Z i) = ∑ i, c * (W i * Z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * ∑ i, W i * Z i := by rw [Finset.mul_sum]

theorem pairing_smul_right (c : ℝ) (W : DualTwistor4) (Z : Twistor4) :
    pairing W (c • Z) = c * pairing W Z := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, W i * (c * Z i)) = ∑ i, c * (W i * Z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = c * ∑ i, W i * Z i := by rw [Finset.mul_sum]

theorem null_pair_rescale_left (c : ℝ) (W : DualTwistor4) (Z : Twistor4)
    (h : IsNullPair W Z) : IsNullPair (c • W) Z := by
  rw [IsNullPair, pairing_smul_left, h]
  ring

theorem null_pair_rescale_right (c : ℝ) (W : DualTwistor4) (Z : Twistor4)
    (h : IsNullPair W Z) : IsNullPair W (c • Z) := by
  rw [IsNullPair, pairing_smul_right, h]
  ring

theorem pairing_swap_scale (c d : ℝ) (W : DualTwistor4) (Z : Twistor4) :
    pairing (c • W) (d • Z) = (c * d) * pairing W Z := by
  rw [pairing_smul_left, pairing_smul_right]
  ring

theorem null_pair_zero_twistor (W : DualTwistor4) : IsNullPair W 0 := by
  simp [IsNullPair]

theorem null_pair_zero_dual (Z : Twistor4) : IsNullPair 0 Z := by
  simp [IsNullPair]

end InfoGeometry.Canonical.FiniteAmbitwistorPairing
