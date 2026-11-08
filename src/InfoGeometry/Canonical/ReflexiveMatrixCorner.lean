/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveNilpotentFlows
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import Mathlib.RingTheory.Idempotents

/-!
# Matrix representation of a reflexive square-zero pair

Contract: `d² = B² = 0`, `dBd = d`, `BdB = B` in an associative
`R`-algebra. The four derived matrix units give a native ring homomorphism
into Mathlib's corner at `dB + Bd`. Neither faithfulness nor equality of
this corner unit with the ambient unit is asserted.
-/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

def pairMatrixUnit (d B : A) : Fin 2 → Fin 2 → A := !![d * B, d; B, B * d]

variable {d B : A} (hd : d * d = 0) (hB : B * B = 0)
  (hr : d * B * d = d) (hs : B * d * B = B)

/-- A nonzero reflexive square-zero arrow forces noncommutativity. -/
theorem reflexive_pair_noncommute (hd : d * d = 0) (hr : d * B * d = d)
    (hne : d ≠ 0) : d * B ≠ B * d := by
  intro h
  apply hne
  calc
    d = d * B * d := hr.symm
    _ = B * d * d := congrArg (fun x : A => x * d) h
    _ = 0 := by rw [mul_assoc, hd, mul_zero]

include hd hB hr hs in
theorem pairMatrixUnit_mul (i j k l : Fin 2) :
    pairMatrixUnit d B i j * pairMatrixUnit d B k l =
      if j = k then pairMatrixUnit d B i l else 0 := by
  have hr' : d * (B * d) = d := by simpa only [mul_assoc] using hr
  have hs' : B * (d * B) = B := by simpa only [mul_assoc] using hs
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [pairMatrixUnit, mul_assoc, hd, hB, hr', hs',
      ← mul_assoc d d, ← mul_assoc B B]

/-- Scalar-linear realization in the ambient algebra. -/
def pairMatrixLinear (d B : A) : Matrix (Fin 2) (Fin 2) R →ₗ[R] A where
  toFun M := M 0 0 • pairMatrixUnit d B 0 0 + M 0 1 • pairMatrixUnit d B 0 1 +
    M 1 0 • pairMatrixUnit d B 1 0 + M 1 1 • pairMatrixUnit d B 1 1
  map_add' M N := by simp only [Matrix.add_apply, add_smul]; abel
  map_smul' r M := by simp [smul_add, smul_smul]

@[simp] theorem pairMatrixLinear_apply (M : Matrix (Fin 2) (Fin 2) R) :
    pairMatrixLinear d B M =
      M 0 0 • pairMatrixUnit d B 0 0 + M 0 1 • pairMatrixUnit d B 0 1 +
      M 1 0 • pairMatrixUnit d B 1 0 + M 1 1 • pairMatrixUnit d B 1 1 := rfl

include hd hB hr hs in
theorem pairMatrixLinear_mul (M N : Matrix (Fin 2) (Fin 2) R) :
    pairMatrixLinear d B (M * N) = pairMatrixLinear d B M * pairMatrixLinear d B N := by
  simp only [pairMatrixLinear_apply, Matrix.mul_apply, Fin.sum_univ_two,
    add_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    pairMatrixUnit_mul hd hB hr hs]
  norm_num
  simp only [smul_smul, mul_comm]
  abel

@[simp] theorem pairMatrixLinear_one :
    pairMatrixLinear d B (1 : Matrix (Fin 2) (Fin 2) R) = support d B := by
  simp [pairMatrixLinear, pairMatrixUnit, support]

include hd hB hr hs in
theorem pairMatrixLinear_mem_corner (M : Matrix (Fin 2) (Fin 2) R) :
    pairMatrixLinear d B M ∈ Subsemigroup.corner (support d B) := by
  apply (Subsemigroup.mem_corner_iff (show IsIdempotentElem (support d B) from
    support_sq hd hB hr hs)).mpr
  constructor
  · rw [← pairMatrixLinear_one (R := R), ← pairMatrixLinear_mul hd hB hr hs, one_mul]
  · rw [← pairMatrixLinear_one (R := R), ← pairMatrixLinear_mul hd hB hr hs, mul_one]

/-- A unital representation into the active corner, rather than the ambient ring. -/
def pairMatrixCornerHom : Matrix (Fin 2) (Fin 2) R →+*
    (show IsIdempotentElem (support d B) from support_sq hd hB hr hs).Corner where
  toFun M := ⟨pairMatrixLinear d B M, pairMatrixLinear_mem_corner hd hB hr hs M⟩
  map_one' := Subtype.ext pairMatrixLinear_one
  map_zero' := Subtype.ext (map_zero (pairMatrixLinear d B))
  map_add' M N := Subtype.ext (map_add (pairMatrixLinear d B) M N)
  map_mul' M N := Subtype.ext (pairMatrixLinear_mul hd hB hr hs M N)

/-- With full support, the same representation is a native algebra homomorphism. -/
def pairMatrixAlgHom (hfull : support d B = 1) : Matrix (Fin 2) (Fin 2) R →ₐ[R] A where
  toFun := pairMatrixLinear d B
  map_one' := pairMatrixLinear_one.trans hfull
  map_zero' := map_zero (pairMatrixLinear d B)
  map_add' := map_add (pairMatrixLinear d B)
  map_mul' := pairMatrixLinear_mul hd hB hr hs
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, pairMatrixLinear_one, hfull,
      Algebra.algebraMap_eq_smul_one]

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
