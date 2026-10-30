import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.ZMod.Basic

namespace InfoGeometry.Canonical.FiniteDimensionalCCRObstruction

/-!
The finite-dimensional CCR obstruction in coordinate-free form.  This is the
same trace argument as the matrix theorem, but it applies to arbitrary finite
endomorphism algebras and does not choose a basis.
-/

/-- In a finite-dimensional endomorphism algebra over any field, a scalar
commutator forces the scalar times the dimension to vanish. This is the exact
characteristic-sensitive alternative to the characteristic-zero no-CCR result. -/
theorem scalar_commutator_forces_dimension_scalar_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (f g : Module.End K V) (c : K)
    (h : f * g - g * f = algebraMap K (Module.End K V) c) :
    c * (Module.finrank K V : K) = 0 := by
  have ht := congrArg (LinearMap.trace K V) h
  rw [map_sub, LinearMap.trace_mul_comm, sub_self] at ht
  have hscalar : algebraMap K (Module.End K V) c = c • (1 : Module.End K V) := by
    simp [Algebra.smul_def]
  rw [hscalar, map_smul, LinearMap.trace_one] at ht
  simpa [Algebra.smul_def] using ht.symm

/-- When the dimension survives in the coefficient field, the only scalar
commutator is zero. No characteristic-zero assumption is needed. -/
theorem scalar_commutator_iff_zero_and_commute
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (hdim : (Module.finrank K V : K) ≠ 0)
    (f g : Module.End K V) (c : K) :
    f * g - g * f = algebraMap K (Module.End K V) c ↔
      c = 0 ∧ Commute f g := by
  constructor
  · intro h
    have hc : c = 0 :=
      (mul_eq_zero.mp
        (scalar_commutator_forces_dimension_scalar_zero f g c h)).resolve_right hdim
    refine ⟨hc, ?_⟩
    rw [hc, map_zero] at h
    exact sub_eq_zero.mp h
  · rintro ⟨rfl, hcomm⟩
    rw [map_zero, sub_eq_zero]
    exact hcomm

/-- A concrete characteristic-two matrix pair realizes the scalar
commutator relation. This shows why the characteristic-zero hypothesis in the
impossibility corollary cannot be dropped. -/
abbrev CharTwoMatrix := Matrix (Fin 2) (Fin 2) (ZMod 2)

def charTwoUpper : CharTwoMatrix := Matrix.single 0 1 1

def charTwoLower : CharTwoMatrix := Matrix.single 1 0 1

def charTwoCommutator (x y : CharTwoMatrix) : CharTwoMatrix := x * y - y * x

theorem charTwo_commutator_eq_one :
    charTwoCommutator charTwoUpper charTwoLower = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [charTwoCommutator, charTwoUpper, charTwoLower,
    Matrix.mul_apply, Matrix.single, Fin.sum_univ_succ]
  all_goals decide

theorem charTwo_upper_lower_do_not_commute :
    charTwoUpper * charTwoLower ≠ charTwoLower * charTwoUpper := by
  intro h
  have hcomm := congrArg (fun z : CharTwoMatrix => z - charTwoLower * charTwoUpper) h
  have hzero : charTwoCommutator charTwoUpper charTwoLower = 0 := by
    simpa [charTwoCommutator, sub_eq_add_neg, add_assoc] using hcomm
  rw [charTwo_commutator_eq_one] at hzero
  exact one_ne_zero hzero

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]

theorem no_scalar_commutator_one
    (f g : Module.End K V)
    (h : f * g - g * f = 1) : False := by
  have ht := congrArg (LinearMap.trace K V) h
  rw [map_sub, LinearMap.trace_mul_comm, sub_self, LinearMap.trace_one] at ht
  have hpos : 0 < Module.finrank K V := Module.finrank_pos
  have hne : (Module.finrank K V : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  exact hne ht.symm

theorem no_nonzero_scalar_commutator
    (f g : Module.End K V) (c : K) (hc : c ≠ 0)
    (h : f * g - g * f = algebraMap K (Module.End K V) c) : False := by
  have ht := congrArg (LinearMap.trace K V) h
  rw [map_sub, LinearMap.trace_mul_comm, sub_self] at ht
  have hscalar : algebraMap K (Module.End K V) c = c • (1 : Module.End K V) := by
    simp [Algebra.smul_def]
  rw [hscalar, map_smul, LinearMap.trace_one] at ht
  have hpos : 0 < Module.finrank K V := Module.finrank_pos
  have hdim : (Module.finrank K V : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  have : c * (Module.finrank K V : K) = 0 := by simpa using ht
  exact hc ((mul_eq_zero.mp this).resolve_right hdim)

end InfoGeometry.Canonical.FiniteDimensionalCCRObstruction
