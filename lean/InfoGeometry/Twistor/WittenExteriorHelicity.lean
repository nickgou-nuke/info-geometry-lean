/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Clifford.ExteriorDegreeFourierClock
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior Euler number and Witten's four-mode helicity

The Euler operator is the actual sum `∑ η_A ∂/∂η_A` of native wedge and
contraction endomorphisms.  Its action on every homogeneous exterior power is
proved from CAR and spanning, rather than stored as an assumed spectrum.
Specializing to four complex modes gives `h = 1 - Nψ / 2`, equation (2.40),
and degree dimensions `1,4,6,4,1`.  The existing exterior phase map supplies
the homogeneous scaling law on the same carrier.

This exterior degree is distinct from the five-lane adjoint number grading
of the ten-generator Clifford Lie algebra and from the signed chiral charge.
-/

noncomputable section

namespace InfoGeometry.Twistor.WittenExteriorHelicity

open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Clifford.ExteriorDegreeFourierClock
open scoped BigOperators

section Euler

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Explicit coordinate generators for a finite exterior algebra. -/
def coordinateVector (i : Fin n) : Fin n → R := Pi.single i 1

def coordinateCovector (i : Fin n) : Module.Dual R (Fin n → R) :=
  LinearMap.proj i

@[simp] theorem coordinateCovector_apply (i : Fin n) (v : Fin n → R) :
    coordinateCovector i v = v i := rfl

@[simp] theorem coordinateCovector_vector (i j : Fin n) :
    coordinateCovector (R := R) i (coordinateVector j) =
      if i = j then 1 else 0 := by
  simp [coordinateVector, Pi.single_apply, eq_comm]

/-- Exterior multiplication by the selected generator. -/
def coordinateWedge (i : Fin n) :
    Module.End R (ExteriorAlgebra R (Fin n → R)) :=
  Algebra.lmul R _ (ExteriorAlgebra.ι R (coordinateVector i))

/-- The repaired native contraction operator, with its actual CAR action. -/
def coordinateDerivative (i : Fin n) :
    Module.End R (ExteriorAlgebra R (Fin n → R)) :=
  contractionOp (coordinateCovector i)

@[simp] theorem coordinateWedge_apply (i : Fin n)
    (ψ : ExteriorAlgebra R (Fin n → R)) :
    coordinateWedge i ψ = ExteriorAlgebra.ι R (coordinateVector i) * ψ := rfl

@[simp] theorem coordinateDerivative_one (i : Fin n) :
    coordinateDerivative (R := R) i 1 = 0 := by
  change contractionOp (R := R) (V := Fin n → R)
    (coordinateCovector (R := R) i) 1 = 0
  exact contraction_op_one (R := R) (V := Fin n → R)
    (coordinateCovector (R := R) i)

theorem coordinateDerivative_generator_mul (i : Fin n) (v : Fin n → R)
    (ψ : ExteriorAlgebra R (Fin n → R)) :
    coordinateDerivative i (ExteriorAlgebra.ι R v * ψ) =
      v i • ψ - ExteriorAlgebra.ι R v * coordinateDerivative i ψ := by
  change contractionOp (R := R) (V := Fin n → R)
      (coordinateCovector (R := R) i) (ExteriorAlgebra.ι R v * ψ) =
    coordinateCovector (R := R) i v • ψ - ExteriorAlgebra.ι R v *
      contractionOp (R := R) (V := Fin n → R) (coordinateCovector (R := R) i) ψ
  exact contraction_op_generator_mul (R := R) (V := Fin n → R)
    (coordinateCovector (R := R) i) v ψ

theorem coordinateDerivative_ne_zero [Nontrivial R] (i : Fin n) :
    coordinateDerivative (R := R) i ≠ 0 := by
  change contractionOp (R := R) (V := Fin n → R) (coordinateCovector (R := R) i) ≠ 0
  exact contraction_op_ne_zero (R := R) (V := Fin n → R)
    (coordinateCovector (R := R) i) (coordinateVector (R := R) i)
    (by simp [coordinateVector])

/-- Ordinary exterior degree, expressed by genuine multiplication and contraction. -/
def exteriorEuler (R : Type*) [CommRing R] (n : ℕ) :
    Module.End R (ExteriorAlgebra R (Fin n → R)) :=
  ∑ i : Fin n, coordinateWedge i * coordinateDerivative i

@[simp] theorem exteriorEuler_apply (ψ : ExteriorAlgebra R (Fin n → R)) :
    exteriorEuler R n ψ = ∑ i : Fin n,
      ExteriorAlgebra.ι R (coordinateVector i) * coordinateDerivative i ψ := by
  simp [exteriorEuler]

@[simp] theorem exteriorEuler_one : exteriorEuler R n 1 = 0 := by
  simp

theorem coordinate_reconstruction (v : Fin n → R) :
    (∑ i : Fin n, v i • coordinateVector (R := R) i) = v := by
  funext j
  simp [coordinateVector, Pi.single_apply, eq_comm]

theorem generator_reconstruction (v : Fin n → R) :
    (∑ i : Fin n, v i • ExteriorAlgebra.ι R (coordinateVector i)) =
      ExteriorAlgebra.ι R v := by
  simp_rw [← map_smul]
  rw [← map_sum, coordinate_reconstruction]

/-- Degree increases by one under multiplication by any exterior generator. -/
theorem exteriorEuler_generator_mul (v : Fin n → R)
    (ψ : ExteriorAlgebra R (Fin n → R)) :
    exteriorEuler R n (ExteriorAlgebra.ι R v * ψ) =
      ExteriorAlgebra.ι R v * ψ +
        ExteriorAlgebra.ι R v * exteriorEuler R n ψ := by
  have hterm (i : Fin n) :
      ExteriorAlgebra.ι R (coordinateVector i) *
          coordinateDerivative i (ExteriorAlgebra.ι R v * ψ) =
        v i • (ExteriorAlgebra.ι R (coordinateVector i) * ψ) +
          ExteriorAlgebra.ι R v *
            (ExteriorAlgebra.ι R (coordinateVector i) * coordinateDerivative i ψ) := by
    have hswap : ExteriorAlgebra.ι R (coordinateVector i) * ExteriorAlgebra.ι R v =
        -(ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R (coordinateVector i)) :=
      eq_neg_of_add_eq_zero_left
        (ExteriorAlgebra.ι_add_mul_swap (R := R) (coordinateVector i) v)
    rw [coordinateDerivative_generator_mul]
    simp only [mul_sub, Algebra.mul_smul_comm, ← mul_assoc, hswap,
      neg_mul, sub_neg_eq_add]
  calc
    exteriorEuler R n (ExteriorAlgebra.ι R v * ψ) =
        ∑ i : Fin n, (v i • (ExteriorAlgebra.ι R (coordinateVector i) * ψ) +
          ExteriorAlgebra.ι R v *
            (ExteriorAlgebra.ι R (coordinateVector i) * coordinateDerivative i ψ)) := by
      rw [exteriorEuler_apply]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i : Fin n, v i • ExteriorAlgebra.ι R (coordinateVector i)) * ψ +
        ExteriorAlgebra.ι R v *
          (∑ i : Fin n,
            ExteriorAlgebra.ι R (coordinateVector i) * coordinateDerivative i ψ) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      simp only [Algebra.smul_mul_assoc]
    _ = ExteriorAlgebra.ι R v * ψ +
        ExteriorAlgebra.ι R v * exteriorEuler R n ψ := by
      rw [generator_reconstruction, exteriorEuler_apply]

/-- The degree law on native alternating products of arbitrary vectors. -/
theorem exteriorEuler_ιMulti (r : ℕ) (v : Fin r → (Fin n → R)) :
    exteriorEuler R n (ExteriorAlgebra.ιMulti R r v) =
      (r : R) • ExteriorAlgebra.ιMulti R r v := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, exteriorEuler_generator_mul,
        ih (Matrix.vecTail v), Algebra.mul_smul_comm]
      push_cast
      module

/-- The full homogeneous subspace satisfies the degree law, by actual spanning. -/
theorem exteriorEuler_homogeneous (r : ℕ) (ψ : ⋀[R]^r (Fin n → R)) :
    exteriorEuler R n (ψ : ExteriorAlgebra R (Fin n → R)) =
      (r : R) • (ψ : ExteriorAlgebra R (Fin n → R)) := by
  have hmem : (ψ : ExteriorAlgebra R (Fin n → R)) ∈
      Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R r)) := by
    rw [ExteriorAlgebra.ιMulti_span_fixedDegree]
    exact ψ.property
  refine Submodule.span_induction
    (p := fun x _ => exteriorEuler R n x = (r : R) • x) ?_ ?_ ?_ ?_ hmem
  · rintro x ⟨v, rfl⟩
    exact exteriorEuler_ιMulti r v
  · simp
  · intro x y hx hy hEx hEy
    simp only [map_add, hEx, hEy, smul_add]
  · intro c x hx hEx
    simp only [map_smul, hEx, smul_smul, mul_comm]

end Euler

/-- The four odd coordinates of one Witten supermultiplet, over `ℂ`. -/
abbrev FourModeSpace := Fin 4 → ℂ
abbrev FourModeForms := ExteriorAlgebra ℂ FourModeSpace

/-- Witten's equation (2.40) on the genuine four-mode exterior representation. -/
def fermionicHelicity : Module.End ℂ FourModeForms :=
  1 - (1 / 2 : ℂ) • exteriorEuler ℂ 4

theorem fermionicHelicity_homogeneous (r : ℕ) (ψ : ⋀[ℂ]^r FourModeSpace) :
    fermionicHelicity (ψ : FourModeForms) =
      (1 - (r : ℂ) / 2) • (ψ : FourModeForms) := by
  simp only [fermionicHelicity, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, exteriorEuler_homogeneous, smul_smul]
  rw [sub_smul, one_smul]
  congr 2
  ring

theorem fourMode_degree_finrank (r : ℕ) :
    Module.finrank ℂ (⋀[ℂ]^r FourModeSpace) = Nat.choose 4 r := by
  rw [exteriorPower.finrank_eq]
  simp [FourModeSpace, Module.finrank_pi]

theorem fourMode_degree_dimensions :
    (Module.finrank ℂ (⋀[ℂ]^0 FourModeSpace),
      Module.finrank ℂ (⋀[ℂ]^1 FourModeSpace),
      Module.finrank ℂ (⋀[ℂ]^2 FourModeSpace),
      Module.finrank ℂ (⋀[ℂ]^3 FourModeSpace),
      Module.finrank ℂ (⋀[ℂ]^4 FourModeSpace)) = (1, 4, 6, 4, 1) := by
  norm_num [fourMode_degree_finrank] <;> decide

theorem exteriorEuler_wedgeWord (vs : List FourModeSpace) :
    exteriorEuler ℂ 4 (wedgeWord vs) = (vs.length : ℂ) • wedgeWord vs := by
  induction vs with
  | nil => simp [wedgeWord]
  | cons v vs ih =>
      rw [wedgeWord, exteriorEuler_generator_mul, ih, Algebra.mul_smul_comm]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      module

/-- Degree, helicity and the existing phase operator are linked on the same
native exterior words; no independent phase action is introduced. -/
theorem fourMode_helicity_and_phase_word (z : ℂ) (vs : List FourModeSpace) :
    fermionicHelicity (wedgeWord vs) =
        (1 - (vs.length : ℂ) / 2) • wedgeWord vs ∧
      phaseMap z (wedgeWord vs) = z ^ vs.length • wedgeWord vs := by
  constructor
  · simp only [fermionicHelicity, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, exteriorEuler_wedgeWord, smul_smul]
    rw [sub_smul, one_smul]
    congr 2
    ring
  · exact phaseMap_wedgeWord z vs

end InfoGeometry.Twistor.WittenExteriorHelicity
