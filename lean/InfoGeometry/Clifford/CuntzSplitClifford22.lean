/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzMatrixUnitRepresentation
import InfoGeometry.Clifford.Cl11Matrix

/-!
# The real split Clifford representation induced by Cuntz matrix units

The existing real `Cl(1,1)` atom supplies `u`, `v`, and `w`. Four explicit
blocks satisfy signature `(2,2)` and induce a native `CliffordAlgebra.lift`.
The matrix-unit algebra map transports this representation to every real
algebra with the existing two-generator algebraic Cuntz presentation.

The fundamental symmetry below is a real linear matrix. It is not a
Tomita--Takesaki antiunitary. No topology or evolution law follows from this
finite algebraic representation alone.
-/

noncomputable section

namespace InfoGeometry.Clifford.CuntzSplitClifford22

open Matrix
open InfoGeometry.Algebra.Cuntz

abbrev Atom := Matrix (Fin 2) (Fin 2) ℝ

def _witness_a : Atom := Matrix.single 0 1 1
def _witness_b : Atom := Matrix.single 1 0 1

theorem _witness_noncommute : _witness_a * _witness_b ≠ _witness_b * _witness_a := by
  intro h
  have h₁ : _witness_a * _witness_b = Matrix.single 0 0 (1 : ℝ) := by
    simp [_witness_a, _witness_b, Matrix.single_mul_single_same]
  have h₂ : _witness_b * _witness_a = Matrix.single 1 1 (1 : ℝ) := by
    simp [_witness_a, _witness_b, Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h₃ := congrFun (congrFun h 0) 0
  norm_num at h₃

abbrev Block := Matrix (Fin 2) (Fin 2) (Atom)
abbrev Vector22 := ℝ × ℝ × ℝ × ℝ

abbrev u : Atom := Cl11Matrix.J1
abbrev v : Atom := Cl11Matrix.Eplus
abbrev w : Atom := Cl11Matrix.Eminus

/-- The real `Cl(1,1)` generators are noncommuting operators on the atom. -/
theorem atom_generators_noncommute :
    (u : Atom) * (w : Atom) ≠ (w : Atom) * (u : Atom) := by
  intro h
  have h00 := congrArg (fun M : Atom => M 0 0) h
  norm_num [u, w, Cl11Matrix.J1, Cl11Matrix.Eminus,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

def gamma0 : Block := !![0, 1; 1, 0]
def gamma1 : Block := !![0, w; -w, 0]
def gamma2 : Block := !![0, u; -u, 0]
def gamma3 : Block := !![0, v; -v, 0]
def gamma : Fin 4 → Block := ![gamma0, gamma1, gamma2, gamma3]
def signature : Fin 4 → ℝ := ![1, 1, -1, -1]

@[simp] theorem gamma_zero : gamma 0 = gamma0 := rfl
@[simp] theorem gamma_one : gamma 1 = gamma1 := rfl
@[simp] theorem gamma_two : gamma 2 = gamma2 := rfl
@[simp] theorem gamma_three : gamma 3 = gamma3 := rfl

/-- The volume element of the explicit real `(2,2)` Clifford frame. -/
def volumeElement : Block := gamma0 * gamma1 * gamma2 * gamma3

/-- In signature `(2,2)`, the volume element squares to `+1`; no imaginary
scalar extension is needed for the chiral split. -/
theorem volumeElement_sq : volumeElement * volumeElement = 1 := by
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [volumeElement, gamma0, gamma1, gamma2, gamma3, u, v, w,
      Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The two real chiral projectors associated to the split volume element. -/
def chiralPlus : Block := (1 / 2 : ℝ) • (1 + volumeElement)
def chiralMinus : Block := (1 / 2 : ℝ) • (1 - volumeElement)

/-- The positive chirality operator is an idempotent. -/
theorem chiralPlus_idempotent : chiralPlus * chiralPlus = chiralPlus := by
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [chiralPlus, volumeElement, gamma0, gamma1, gamma2, gamma3,
      u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The negative chirality operator is an idempotent. -/
theorem chiralMinus_idempotent : chiralMinus * chiralMinus = chiralMinus := by
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [chiralMinus, volumeElement, gamma0, gamma1, gamma2, gamma3,
      u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The real chiral projectors are orthogonal and sum to the identity. -/
theorem chiral_projectors_orthogonal_sum :
    chiralPlus * chiralMinus = 0 ∧
    chiralMinus * chiralPlus = 0 ∧
    chiralPlus + chiralMinus = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [chiralPlus, chiralMinus, volumeElement, gamma0, gamma1, gamma2, gamma3,
        u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
        Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [chiralPlus, chiralMinus, volumeElement, gamma0, gamma1, gamma2, gamma3,
        u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
        Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [chiralPlus, chiralMinus, volumeElement, gamma0, gamma1, gamma2, gamma3,
        u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
        Matrix.mul_apply, Fin.sum_univ_two]

set_option maxHeartbeats 2000000 in
/-- All sixteen Clifford relations, including their diagonal signs. -/
theorem gamma_anticommutator (a b : Fin 4) :
    gamma a * gamma b + gamma b * gamma a =
      if a = b then (2 * signature a) • (1 : Block) else 0 := by
  fin_cases a <;> fin_cases b <;> ext i j k l <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [gamma, gamma0, gamma1, gamma2, gamma3, signature,
      u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

set_option maxHeartbeats 2000000 in
/-- Every represented vector generator anticommutes with the volume element.
This is the grading law that exchanges the two real chiral sectors. -/
theorem gamma_volumeElement_anticommute (a : Fin 4) :
    gamma a * volumeElement = -(volumeElement * gamma a) := by
  fin_cases a <;> ext i j k l <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [gamma, volumeElement, gamma0, gamma1, gamma2, gamma3,
      u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The represented Clifford generators witness genuine noncommutativity of
the explicit `(2,2)` operator algebra. -/
theorem gamma0_gamma1_noncommute :
    (gamma0 : Block) * (gamma1 : Block) ≠
      (gamma1 : Block) * (gamma0 : Block) := by
  intro h
  have hOuter := congrArg (fun M : Block => M 0 0) h
  have hInner := congrArg (fun M : Atom => M 0 1) hOuter
  norm_num [gamma0, gamma1, w, Cl11Matrix.Eminus,
    Matrix.mul_apply, Fin.sum_univ_two] at hInner

/-- Explicit existential noncommutativity witness for nested `2 × 2` block matrices. -/
theorem block_noncommute :
    ∃ matI matJ : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℝ),
      matI * matJ ≠ matJ * matI :=
  ⟨gamma0, gamma1, gamma0_gamma1_noncommute⟩

def q22 : QuadraticForm ℝ Vector22 :=
  QuadraticMap.sq.prod
    (QuadraticMap.sq.prod ((-QuadraticMap.sq).prod (-QuadraticMap.sq)))

@[simp] theorem q22_apply (t x y z : ℝ) :
    q22 (t, x, y, z) = t ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 := by
  simp [q22]
  ring

def generator : Vector22 →ₗ[ℝ] Block where
  toFun x := x.1 • gamma0 + x.2.1 • gamma1 +
    x.2.2.1 • gamma2 + x.2.2.2 • gamma3
  map_add' x y := by simp [add_smul]; abel
  map_smul' r x := by simp [smul_add, smul_smul]

theorem generator_sq (x : Vector22) :
    generator x * generator x = q22 x • (1 : Block) := by
  rcases x with ⟨t, x, y, z⟩
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [generator, q22_apply, gamma0, gamma1, gamma2, gamma3,
      u, v, w, Cl11Matrix.J1, Cl11Matrix.Eplus, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A genuine universal Clifford algebra representation over the real numbers. -/
def matrixRepresentation : CliffordAlgebra q22 →ₐ[ℝ] Block :=
  CliffordAlgebra.lift q22 ⟨generator, fun x => by
    simpa [Algebra.algebraMap_eq_smul_one] using generator_sq x⟩

@[simp] theorem matrixRepresentation_iota (x : Vector22) :
    matrixRepresentation (CliffordAlgebra.ι q22 x) = generator x := by
  exact CliffordAlgebra.lift_ι_apply _ _ x

section Transport

variable {A : Type*} [Ring A] [Algebra ℝ A]
variable (P : AlgebraicCuntzNPresentation ℝ 2 A)

/-- Apply the derived matrix-unit algebra homomorphism to each outer block. -/
def blockHom : Block →ₐ[ℝ] Matrix (Fin 2) (Fin 2) A where
  toFun M i j := P.matrixTwoHom (M i j)
  map_zero' := by
    ext i j
    exact map_zero P.matrixTwoHom
  map_one' := by
    ext i j
    simp only [Matrix.one_apply, apply_ite, map_one, map_zero]
    by_cases h : i = j <;> simp [h]
  map_add' M K := by
    ext i j
    exact map_add P.matrixTwoHom (M i j) (K i j)
  map_mul' M K := by
    ext i j
    change P.matrixTwoHom (∑ k, M i k * K k j) =
      ∑ k, P.matrixTwoHom (M i k) * P.matrixTwoHom (K k j)
    simp only [map_sum, map_mul]
  commutes' r := by
    ext i j
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply,
      Matrix.one_apply, map_smul, apply_ite, map_one, map_zero]
    by_cases h : i = j <;> simp [h]

def cuntzGamma (a : Fin 4) : Matrix (Fin 2) (Fin 2) A :=
  blockHom P (gamma a)

def cuntzRepresentation :
    CliffordAlgebra q22 →ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  (blockHom P).comp matrixRepresentation

@[simp] theorem cuntzRepresentation_iota (x : Vector22) :
    cuntzRepresentation P (CliffordAlgebra.ι q22 x) = blockHom P (generator x) := by
  simp [cuntzRepresentation]

theorem cuntzGamma_anticommutator (a b : Fin 4) :
    cuntzGamma P a * cuntzGamma P b + cuntzGamma P b * cuntzGamma P a =
      if a = b then (2 * signature a) • (1 : Matrix (Fin 2) (Fin 2) A) else 0 := by
  have h := congrArg (blockHom P) (gamma_anticommutator a b)
  simpa [cuntzGamma, apply_ite] using h

/-- Readback of the off-diagonal involution as the sum of Cuntz matrix units. -/
theorem matrixTwoHom_u :
    P.matrixTwoHom u = P.matrixUnit 0 1 + P.matrixUnit 1 0 := by
  simp [u, Cl11Matrix.J1]

theorem matrixTwoHom_v :
    P.matrixTwoHom v = P.matrixUnit 0 0 - P.matrixUnit 1 1 := by
  simp [v, Cl11Matrix.Eplus, sub_eq_add_neg]

theorem matrixTwoHom_w :
    P.matrixTwoHom w = P.matrixUnit 0 1 - P.matrixUnit 1 0 := by
  simp [w, Cl11Matrix.Eminus, sub_eq_add_neg]

end Transport

/-- The algebraic real Cuntz quotient supplies a concrete instantiation. -/
def quotientRepresentation : CliffordAlgebra q22 →ₐ[ℝ]
    Matrix (Fin 2) (Fin 2) (CuntzTensorQuotient ℝ 2) :=
  cuntzRepresentation (cuntzTensorQuotientPresentation ℝ 2)

private def seqZeroShift : Module.End ℝ (ℕ → ℝ) where
  toFun f n := if n % 2 = 0 then f (n / 2) else 0
  map_add' f g := by funext n; by_cases h : n % 2 = 0 <;> simp [h]
  map_smul' r f := by funext n; by_cases h : n % 2 = 0 <;> simp [h]

private def seqOneShift : Module.End ℝ (ℕ → ℝ) where
  toFun f n := if n % 2 = 1 then f (n / 2) else 0
  map_add' f g := by funext n; by_cases h : n % 2 = 1 <;> simp [h]
  map_smul' r f := by funext n; by_cases h : n % 2 = 1 <;> simp [h]

private def seqZeroAdj : Module.End ℝ (ℕ → ℝ) where
  toFun f k := f (2 * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def seqOneAdj : Module.End ℝ (ℕ → ℝ) where
  toFun f k := f (2 * k + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def seqCuntzPresentation :
    AlgebraicCuntzNPresentation ℝ 2 (Module.End ℝ (ℕ → ℝ)) where
  S i := if i = 0 then seqZeroShift else seqOneShift
  T i := if i = 0 then seqZeroAdj else seqOneAdj
  isometry i j := by
    fin_cases i <;> fin_cases j <;> ext f k
    · change seqZeroShift f (2 * k) = f k
      simp [seqZeroShift]
    · change seqOneShift f (2 * k) = 0
      simp [seqOneShift]
    · change seqZeroShift f (2 * k + 1) = 0
      simp [seqZeroShift]
    · change seqOneShift f (2 * k + 1) = f k
      have hk1 : (2 * k + 1) % 2 = 1 := by omega
      have hk2 : (2 * k + 1) / 2 = k := by omega
      simp [seqOneShift, hk1, hk2]
  range_sum := by
    rw [Fin.sum_univ_two]
    ext f n
    change seqZeroShift (seqZeroAdj f) n + seqOneShift (seqOneAdj f) n = f n
    by_cases h : n % 2 = 0
    · have hdiv : 2 * (n / 2) = n := by omega
      simp [seqZeroShift, seqZeroAdj, seqOneShift, seqOneAdj, h, hdiv]
    · have h1 : n % 2 = 1 := by omega
      have hdiv : 2 * (n / 2) + 1 = n := by omega
      simp [seqZeroShift, seqZeroAdj, seqOneShift, seqOneAdj, h1, hdiv]

theorem cuntzTensorQuotient2_nontrivial :
    Nontrivial (CuntzTensorQuotient ℝ 2) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have hmap := congrArg seqCuntzPresentation.lift h
  rw [map_one, map_zero] at hmap
  have hval := congrFun (LinearMap.congr_fun hmap (fun _ => (1 : ℝ))) 0
  simp at hval

theorem cuntzQuotient_matrix_noncommute :
    ∃ matI matJ : Matrix (Fin 2) (Fin 2) (CuntzTensorQuotient ℝ 2),
      matI * matJ ≠ matJ * matI := by
  have : Nontrivial (CuntzTensorQuotient ℝ 2) := cuntzTensorQuotient2_nontrivial
  refine ⟨!![(0 : CuntzTensorQuotient ℝ 2), 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (CuntzTensorQuotient ℝ 2) => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

@[simp] theorem gamma0_sq : gamma0 * gamma0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem gamma0_star : star gamma0 = gamma0 := by
  ext i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [gamma0, Matrix.star_apply]

/-- The adjoint defined by the additional fundamental symmetry. -/
def kreinAdjoint (T : Block) : Block := gamma0 * star T * gamma0

theorem kreinAdjoint_involutive (T : Block) :
    kreinAdjoint (kreinAdjoint T) = T := by
  simp only [kreinAdjoint, Matrix.star_mul, gamma0_star, star_star]
  calc
    _ = (gamma0 * gamma0) * T * (gamma0 * gamma0) := by noncomm_ring
    _ = T := by simp

theorem kreinAdjoint_mul (T U : Block) :
    kreinAdjoint (T * U) = kreinAdjoint U * kreinAdjoint T := by
  simp only [kreinAdjoint, Matrix.star_mul]
  symm
  calc
    (gamma0 * star U * gamma0) * (gamma0 * star T * gamma0) =
        gamma0 * star U * (gamma0 * gamma0) * star T * gamma0 := by noncomm_ring
    _ = gamma0 * (star U * star T) * gamma0 := by simp [mul_assoc]

end InfoGeometry.Clifford.CuntzSplitClifford22
