/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Clifford.BrauerWeylMatrixStep

/-!
# A noncommuting finite block realization of Weyl braiding holonomy

The coefficients of the outer block matrices are themselves operators in
`M₂(ℤ)`.  This file verifies their involutions, the ordered braiding identity,
and the parabolic infinite-order element in one diagonal block of the
holonomy.  It makes no claim about general classification of braid actions.
-/

namespace InfoGeometry.OperatorAlgebra.NonabelianSylvesterHolonomy

open Matrix

abbrev Op := Matrix (Fin 2) (Fin 2) ℤ
abbrev BlockOp := Matrix (Fin 2) (Fin 2) Op

def clock0 : Op := ![![0, 1], ![1, 0]]
def clock1 : Op := ![![1, 0], ![0, -1]]
def link : Op := ![![1, -1], ![0, 1]]
def linkInv : Op := ![![1, 1], ![0, 1]]

def shift : BlockOp := ![![0, link], ![linkInv, 0]]
def vertexClock : BlockOp := ![![clock0, 0], ![0, clock1]]
def plaquette : BlockOp := (vertexClock * shift) * (vertexClock * shift)

def parabolic : Op := ![![0, -1], ![1, 2]]

def parabolicPowerFormula (n : ℕ) : Op :=
  ![![1 - (n : ℤ), -(n : ℤ)], ![(n : ℤ), 1 + (n : ℤ)]]

theorem link_mul_linkInv : link * linkInv = 1 := by decide
theorem linkInv_mul_link : linkInv * link = 1 := by decide
theorem shift_sq : shift * shift = 1 := by decide
theorem vertexClock_sq : vertexClock * vertexClock = 1 := by decide

/-- The plaquette's first operator block is the nontrivial parabolic matrix. -/
theorem plaquette_00 : plaquette 0 0 = parabolic := by decide

/-- The plaquette is block diagonal; its off-diagonal operator blocks vanish. -/
theorem plaquette_offDiagonal : plaquette 0 1 = 0 ∧ plaquette 1 0 = 0 := by decide

/-- The defining Weyl relation uses the full noncommuting block operators. -/
theorem block_braiding :
    vertexClock * shift = plaquette * shift * vertexClock := by decide

/-- The plaquette holonomy is genuinely noncentral relative to both
generators of this finite operator representation. -/
theorem plaquette_noncommutes_with_shift :
    plaquette * shift ≠ shift * plaquette := by decide

theorem plaquette_noncommutes_with_clock :
    plaquette * vertexClock ≠ vertexClock * plaquette := by decide

/-- The order-two shift conjugates the plaquette holonomy to its inverse. -/
theorem shift_conjugates_plaquette_inverse :
    shift * plaquette * shift * plaquette = 1 := by decide

/-- The upper-left operator block has the exact parabolic power formula. -/
theorem parabolic_pow (n : ℕ) :
    parabolic ^ n = parabolicPowerFormula n := by
  induction n with
  | zero =>
      rw [pow_zero]
      decide
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      change (∑ k : Fin 2, parabolicPowerFormula n i k * parabolic k j) =
        parabolicPowerFormula (n + 1) i j
      fin_cases i <;> fin_cases j <;>
        simp [parabolicPowerFormula, parabolic, Fin.sum_univ_two] <;> ring

private theorem blockDiagonal_pow_00 (n : ℕ) :
    (plaquette ^ n) 0 0 = parabolic ^ n := by
  induction n with
  | zero => simp [plaquette]
  | succ n ih =>
      calc
        (plaquette ^ (n + 1)) 0 0 = (plaquette ^ n * plaquette) 0 0 := by
          rw [pow_succ]
        _ = (plaquette ^ n) 0 0 * plaquette 0 0 +
              (plaquette ^ n) 0 1 * plaquette 1 0 := by
          simp [Matrix.mul_apply, Fin.sum_univ_two]
        _ = parabolic ^ n * parabolic := by
          rw [ih, plaquette_00, (plaquette_offDiagonal).2]
          simp
        _ = parabolic ^ (n + 1) := by rw [pow_succ]

/-- The nested block holonomy has infinite order, detected by an entry of its
first operator block.  This is an operator-matrix statement over `ℤ`. -/
theorem plaquette_infinite_order (n : ℕ) (hn : 0 < n) :
    plaquette ^ n ≠ 1 := by
  intro h
  have hentry := congrArg (fun M : BlockOp => (M 0 0) 1 0) h
  rw [blockDiagonal_pow_00, parabolic_pow] at hentry
  have hn0 : (n : ℤ) = 0 := by simpa [parabolicPowerFormula] using hentry
  exact Nat.ne_of_gt hn (Int.ofNat.inj hn0)

/-! ## General permutation-indexed operator braiding

The finite integer example above is a witness.  The following statements
give the construction over an arbitrary, potentially noncommutative operator
ring, with a finite set of sites and operator-valued edge and vertex units.
-/

section PermutationBraiding

variable {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]

/-- Vertex operators act diagonally on the site-indexed operator module. -/
def vertexMatrix (v : ι → Aˣ) : Matrix ι ι A :=
  Matrix.diagonal (fun i => (v i : A))

/-- A permutation shift with an operator-valued weight on each directed edge. -/
def permutationShift (σ : Equiv.Perm ι) (u : ι → Aˣ) : Matrix ι ι A :=
  fun i j => if j = σ i then (u i : A) else 0

/-- The ordered operator plaquette attached to a weighted permutation edge. -/
def permutationPhaseUnit (σ : Equiv.Perm ι) (u v : ι → Aˣ) (i : ι) : Aˣ :=
  v i * u i * (v (σ i))⁻¹ * (u i)⁻¹

def permutationPhase (σ : Equiv.Perm ι) (u v : ι → Aˣ) : ι → A :=
  fun i => (permutationPhaseUnit σ u v i : A)

@[simp] theorem diagonal_mul_apply (d : ι → A) (M : Matrix ι ι A) (i j : ι) :
    (Matrix.diagonal d * M) i j = d i * M i j := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

@[simp] theorem mul_diagonal_apply (M : Matrix ι ι A) (d : ι → A) (i j : ι) :
    (M * Matrix.diagonal d) i j = M i j * d j := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq']

/-- Exact operator-valued Weyl relation for a permutation shift.  Coefficient
order is retained, and no commutativity assumption is made on `A`. -/
theorem vertex_braiding (σ : Equiv.Perm ι) (u v : ι → Aˣ) :
    vertexMatrix v * permutationShift σ u =
      vertexMatrix (fun i => permutationPhaseUnit σ u v i) *
        permutationShift σ u * vertexMatrix v := by
  ext i j
  by_cases hij : j = σ i
  · subst j
    simp only [vertexMatrix, permutationShift, diagonal_mul_apply,
      mul_diagonal_apply]
    change (v i : A) * (u i : A) =
      (((v i : A) * (u i : A)) * ↑((v (σ i))⁻¹) * ↑((u i)⁻¹)) *
        (u i : A) * (v (σ i) : A)
    have hv : (↑((v (σ i))⁻¹) : A) * (v (σ i) : A) = 1 := Units.inv_mul _
    have hu : (↑((u i)⁻¹) : A) * (u i : A) = 1 := Units.inv_mul _
    have hcancel :
        (((v i : A) * (u i : A)) * ↑((v (σ i))⁻¹) * ↑((u i)⁻¹)) *
            (u i : A) * (v (σ i) : A) = (v i : A) * (u i : A) := by
      calc
        _ = ((v i : A) * (u i : A)) *
            (↑((v (σ i))⁻¹) * (↑((u i)⁻¹) * (u i : A)) * (v (σ i) : A)) := by
              noncomm_ring
        _ = ((v i : A) * (u i : A)) *
            (↑((v (σ i))⁻¹) * 1 * (v (σ i) : A)) := by rw [hu]
        _ = (v i : A) * (u i : A) := by simp [hv]
    exact hcancel.symm
  · simp [vertexMatrix, permutationShift, hij]

end PermutationBraiding

section PermutationPhaseGauge

variable {A ι : Type*} [Ring A]

/-- Vertex gauge changes act on the plaquette by conjugation at the source
site.  This is the operator-valued coboundary covariance law. -/
theorem permutationPhaseUnit_gauge_covariant (σ : Equiv.Perm ι)
    (u v g : ι → Aˣ) (i : ι) :
    permutationPhaseUnit σ
        (fun j => g j * u j * (g (σ j))⁻¹)
        (fun j => g j * v j * (g j)⁻¹) i =
      g i * permutationPhaseUnit σ u v i * (g i)⁻¹ := by
  dsimp [permutationPhaseUnit]
  group

theorem permutationPhase_gauge_covariant (σ : Equiv.Perm ι)
    (u v g : ι → Aˣ) (i : ι) :
    permutationPhase σ
        (fun j => g j * u j * (g (σ j))⁻¹)
        (fun j => g j * v j * (g j)⁻¹) i =
      (g i : A) * permutationPhase σ u v i * ↑((g i)⁻¹) := by
  simpa [permutationPhase, permutationPhaseUnit] using
    congrArg (fun x : Aˣ => (x : A))
      (permutationPhaseUnit_gauge_covariant σ u v g i)

end PermutationPhaseGauge

/-! ## A universal square-zero block holonomy

The integer example above exhibits infinite order in one concrete operator
ring.  Here the same mechanism is expressed over an arbitrary coefficient
ring, using the actual nested matrix carrier `M₂(M₂(A))`.  The power formula
is unconditional; infinite order additionally needs characteristic zero.
-/

section UniversalNilpotentHolonomy

def nilpotentCorner (A : Type*) [Ring A] :
    InfoGeometry.Clifford.BrauerWeylMatrixStep.Op₂ A := !![-1, -1; 1, 1]
def linkPlus (A : Type*) [Ring A] :
    InfoGeometry.Clifford.BrauerWeylMatrixStep.Op₂ A :=
  1 + InfoGeometry.Clifford.BrauerWeylMatrixStep.create
def linkMinus (A : Type*) [Ring A] :
    InfoGeometry.Clifford.BrauerWeylMatrixStep.Op₂ A :=
  1 - InfoGeometry.Clifford.BrauerWeylMatrixStep.create

def universalShift (A : Type*) [Ring A] :
    InfoGeometry.Clifford.BrauerWeylMatrixStep.NestedOp₂ A :=
  !![0, linkMinus A; linkPlus A, 0]
def universalClock (A : Type*) [Ring A] :
    InfoGeometry.Clifford.BrauerWeylMatrixStep.NestedOp₂ A :=
  !![InfoGeometry.Clifford.BrauerWeylMatrixStep.shift, 0; 0,
    InfoGeometry.Clifford.BrauerWeylMatrixStep.chirality]
def universalDefect (A : Type*) [Ring A] :
    InfoGeometry.Clifford.BrauerWeylMatrixStep.NestedOp₂ A :=
  !![nilpotentCorner A, 0; 0,
    -InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate]
def universalPlaquette (A : Type*) [Ring A] :
    InfoGeometry.Clifford.BrauerWeylMatrixStep.NestedOp₂ A :=
  (universalClock A * universalShift A) * (universalClock A * universalShift A)

variable {A : Type*} [Ring A]

theorem universalShift_sq : universalShift A * universalShift A = 1 := by
  ext i j k l <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;>
    simp [universalShift, linkPlus, linkMinus,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.create,
      Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

theorem universalClock_sq : universalClock A * universalClock A = 1 := by
  ext i j k l <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;>
    simp [universalClock, InfoGeometry.Clifford.BrauerWeylMatrixStep.shift,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.chirality,
      Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

theorem universalPlaquette_eq_one_add_defect :
    universalPlaquette A = 1 + universalDefect A := by
  ext i j k l <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;>
      simp [universalPlaquette, universalClock, universalShift,
        universalDefect, InfoGeometry.Clifford.BrauerWeylMatrixStep.shift,
        InfoGeometry.Clifford.BrauerWeylMatrixStep.chirality, linkPlus, linkMinus,
        InfoGeometry.Clifford.BrauerWeylMatrixStep.create,
        InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate, nilpotentCorner,
        Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ,
        Fin.sum_univ_two, Matrix.one_apply, Finset.filter_singleton] <;>
    split_ifs <;> simp

theorem universalDefect_sq : universalDefect A * universalDefect A = 0 := by
  ext i j k l <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;>
      simp [universalDefect, nilpotentCorner,
        InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate,
        Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

theorem universalShift_conjugates_defect :
    universalShift A * universalDefect A * universalShift A = -universalDefect A := by
  ext i j k l <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;>
      simp [universalShift, universalDefect, linkPlus, linkMinus,
        InfoGeometry.Clifford.BrauerWeylMatrixStep.create,
        InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate, nilpotentCorner,
        Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

theorem universalClock_conjugates_defect :
    universalClock A * universalDefect A * universalClock A = -universalDefect A := by
  ext i j k l <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;> fin_cases l <;>
      simp [universalClock, universalDefect,
        InfoGeometry.Clifford.BrauerWeylMatrixStep.shift,
        InfoGeometry.Clifford.BrauerWeylMatrixStep.chirality,
        InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate, nilpotentCorner,
        Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

theorem universalPlaquette_braiding :
    universalClock A * universalShift A =
      universalPlaquette A * universalShift A * universalClock A := by
  symm
  change (universalClock A * universalShift A) *
      (universalClock A * universalShift A) * universalShift A * universalClock A =
    universalClock A * universalShift A
  calc
    _ = universalClock A * universalShift A * universalClock A *
          (universalShift A * universalShift A) * universalClock A := by noncomm_ring
    _ = universalClock A * universalShift A * universalClock A * 1 * universalClock A := by
          rw [universalShift_sq]
    _ = universalClock A * universalShift A *
          (universalClock A * universalClock A) := by noncomm_ring
    _ = universalClock A * universalShift A * 1 := by rw [universalClock_sq]
    _ = universalClock A * universalShift A := by simp

theorem universalPlaquette_pow (n : ℕ) :
    universalPlaquette A ^ n = 1 + n • universalDefect A := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, universalPlaquette_eq_one_add_defect,
        add_nsmul, one_nsmul]
      have hmul : (n • universalDefect A) * universalDefect A = 0 := by
        rw [nsmul_eq_mul, mul_assoc, universalDefect_sq, mul_zero]
      calc
        (1 + n • universalDefect A) * (1 + universalDefect A)
            = 1 + (n • universalDefect A + universalDefect A) +
                (n • universalDefect A) * universalDefect A := by noncomm_ring
        _ = 1 + (n • universalDefect A + universalDefect A) := by
              rw [hmul, add_zero]

theorem universalPlaquette_infinite_order [CharZero A]
    (n : ℕ) (hn : 0 < n) : universalPlaquette A ^ n ≠ 1 := by
  intro h
  have hentry := congrArg
    (fun M : InfoGeometry.Clifford.BrauerWeylMatrixStep.NestedOp₂ A => (M 0 0) 1 0) h
  rw [universalPlaquette_pow] at hentry
  have hnat : (n : A) = 0 := by
    simpa [universalDefect, nilpotentCorner] using hentry
  have hncast : (n : A) = ((0 : ℕ) : A) := by simpa using hnat
  have hn0 : n = 0 := Nat.cast_injective hncast
  exact Nat.ne_of_gt hn hn0

end UniversalNilpotentHolonomy

end InfoGeometry.OperatorAlgebra.NonabelianSylvesterHolonomy
