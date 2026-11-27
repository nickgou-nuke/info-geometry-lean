/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev
import InfoGeometry.Superalgebra.WittenMoebiusChiralParity
import InfoGeometry.Physics.MengChPSelectionRules
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge
import InfoGeometry.Physics.NuclearTwoModeCARFiveGrade

/-!
# Internal versus external parity for operator-valued Soloviev blocks

The operator super-Soloviev lane contains two independent `ℤ₂` involutions.
They must not be conflated:

* `internalParity = diag(Γ,Γ)` applies the internal grading to every block.
  For even diagonal coefficients and odd transition coefficients it produces
  the genuine Soloviev reflection `V,W ↦ -V,-W`.
* `externalFockParity = diag(1,-1)` changes only the two-sector Fock sign and
  therefore reflects every off-diagonal block independently of its internal
  grade.
* `totalParity = diag(Γ,-Γ)` is their product.  Hence on internally odd
  transition channels the two sign changes cancel and the full
  super-Hamiltonian is invariant.

All statements are identities over an arbitrary associative ring.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearInternalExternalParityFactorization

open Matrix
open InfoGeometry.Physics.NuclearOperatorSuperSoloviev

variable {A : Type*} [Ring A]

/-- Pure internal grading on the two-sector carrier: `diag(Γ,Γ)`. -/
def internalParity (P : InternalParity A) : Block2 A :=
  !![P.gamma, 0; 0, P.gamma]

/-- Pure outer/Fock grading: `diag(1,-1)`. -/
def externalFockParity : Block2 A :=
  !![(1 : A), 0; 0, -1]

/-- Internal parity is an involution. -/
theorem internalParity_sq (P : InternalParity A) :
    internalParity P * internalParity P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [internalParity, Matrix.mul_apply, Fin.sum_univ_two, P.gamma_sq]

/-- External Fock parity is an involution. -/
theorem externalFockParity_sq :
    (externalFockParity : Block2 A) * externalFockParity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [externalFockParity, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pure internal conjugation applies `P.act` independently to all four blocks. -/
theorem internalParity_conjugation_formula
    (P : InternalParity A) (E0 E1 V W : A) :
    internalParity P * blockHamiltonian E0 E1 V W * internalParity P =
      blockHamiltonian (P.act E0) (P.act E1) (P.act V) (P.act W) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [internalParity, blockHamiltonian, InternalParity.act,
      Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

/-- Pure internal grading gives the Soloviev reflection when the diagonal
coefficients are internally even and the transition channels are internally
odd. -/
theorem internalParity_reflection_of_even_diagonal_odd_offDiagonal
    (P : InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1)
    (hV : P.IsOdd V) (hW : P.IsOdd W) :
    internalParity P * blockHamiltonian E0 E1 V W * internalParity P =
      reflectOffDiagonal E0 E1 V W := by
  rw [internalParity_conjugation_formula]
  unfold InternalParity.IsEven at hE0 hE1
  unfold InternalParity.IsOdd at hV hW
  rw [hE0, hE1, hV, hW]
  rfl

/-- Pure external/Fock parity always reflects the off-diagonal channels. -/
theorem externalFockParity_reflection
    (E0 E1 V W : A) :
    externalFockParity * blockHamiltonian E0 E1 V W * externalFockParity =
      reflectOffDiagonal E0 E1 V W := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [externalFockParity, blockHamiltonian, reflectOffDiagonal,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Internal and external parity commute. -/
theorem internalParity_mul_externalFockParity
    (P : InternalParity A) :
    internalParity P * externalFockParity = totalParity P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [internalParity, externalFockParity, totalParity,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The opposite multiplication order gives the same total parity. -/
theorem externalFockParity_mul_internalParity
    (P : InternalParity A) :
    externalFockParity * internalParity P = totalParity P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [internalParity, externalFockParity, totalParity,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact factorization of the total grading into commuting internal and outer
Fock involutions. -/
theorem parity_factorization_packet (P : InternalParity A) :
    internalParity P * externalFockParity = totalParity P ∧
      externalFockParity * internalParity P = totalParity P ∧
      internalParity P * externalFockParity =
        externalFockParity * internalParity P :=
  ⟨internalParity_mul_externalFockParity P,
    externalFockParity_mul_internalParity P,
    (internalParity_mul_externalFockParity P).trans
      (externalFockParity_mul_internalParity P).symm⟩

/-- On an internally odd transition channel the internal reflection and outer
Fock reflection cancel in the product grading, giving total super-invariance. -/
theorem totalParity_invariance_from_double_reflection
    (P : InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1)
    (hV : P.IsOdd V) (hW : P.IsOdd W) :
    totalParity P * blockHamiltonian E0 E1 V W * totalParity P =
      blockHamiltonian E0 E1 V W := by
  exact invariant_of_even_diagonal_odd_offDiagonal P E0 E1 V W
    hE0 hE1 hV hW

/-- Consolidated distinction between the three parity actions. -/
theorem internal_external_total_parity_packet
    (P : InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1)
    (hV : P.IsOdd V) (hW : P.IsOdd W) :
    internalParity P * blockHamiltonian E0 E1 V W * internalParity P =
        reflectOffDiagonal E0 E1 V W ∧
      externalFockParity * blockHamiltonian E0 E1 V W * externalFockParity =
        reflectOffDiagonal E0 E1 V W ∧
      totalParity P * blockHamiltonian E0 E1 V W * totalParity P =
        blockHamiltonian E0 E1 V W :=
  ⟨internalParity_reflection_of_even_diagonal_odd_offDiagonal
      P E0 E1 V W hE0 hE1 hV hW,
    externalFockParity_reflection E0 E1 V W,
    totalParity_invariance_from_double_reflection
      P E0 E1 V W hE0 hE1 hV hW⟩

/-! ## Generalized Multi-Mode CAR Fermion Number Parity `(-1)^N` -/

section GeneralCARFermionParity

open InfoGeometry.Physics.NuclearQuasiparticleCAR

variable {ι : Type*} [DecidableEq ι] {A : Type*} [Ring A] [Algebra ℝ A]

/-- Number operator `N_i = a†_i a_i` for a canonical fermionic mode `i`. -/
def modeNumber (car : QuasiparticleCAR ι A) (i : ι) : A :=
  car.adag i * car.a i

/-- Single-mode fermion parity involution `(-1)^{N_i} = 1 - 2 N_i`. -/
def modeParity (car : QuasiparticleCAR ι A) (i : ι) : A :=
  1 - (2 : A) * modeNumber car i

omit [Algebra ℝ A] in
private theorem two_mul_ring (x : A) : (2 : A) * x = x + x := by
  rw [one_add_one_eq_two.symm, add_mul, one_mul]

private theorem adag_mul_a_mul_adag_same (car : QuasiparticleCAR ι A) (i : ι) :
    car.adag i * car.a i * car.adag i = car.adag i := by
  rw [mul_assoc, car.a_mul_adag_same i, mul_sub, mul_one, ← mul_assoc, car.adag_sq i, zero_mul,
    sub_zero]

theorem modeNumber_idem (car : QuasiparticleCAR ι A) (i : ι) :
    modeNumber car i * modeNumber car i = modeNumber car i := by
  unfold modeNumber
  calc
    (car.adag i * car.a i) * (car.adag i * car.a i) =
        (car.adag i * car.a i * car.adag i) * car.a i := by
      simp only [mul_assoc]
    _ = car.adag i * car.a i := by rw [adag_mul_a_mul_adag_same]

theorem modeParity_sq (car : QuasiparticleCAR ι A) (i : ι) :
    modeParity car i * modeParity car i = 1 := by
  unfold modeParity
  have hid : modeNumber car i * modeNumber car i = modeNumber car i := modeNumber_idem car i
  calc
    (1 - (2 : A) * modeNumber car i) * (1 - (2 : A) * modeNumber car i) =
        1 - (2 : A) * modeNumber car i - (2 : A) * modeNumber car i +
          (2 : A) * (2 : A) * (modeNumber car i * modeNumber car i) := by
      noncomm_ring
    _ = 1 - (modeNumber car i + modeNumber car i) - (modeNumber car i + modeNumber car i) +
          (modeNumber car i + modeNumber car i + (modeNumber car i + modeNumber car i)) := by
      rw [hid, two_mul_ring, two_mul_ring]
      noncomm_ring
    _ = 1 := by abel

omit [Algebra ℝ A] in
private theorem modeNumber_comm_adag_ne (car : QuasiparticleCAR ι A) (i j : ι) (hij : i ≠ j) :
    modeNumber car i * car.adag j = car.adag j * modeNumber car i := by
  unfold modeNumber
  have h1 : car.a i * car.adag j = -(car.adag j * car.a i) :=
    car.a_mul_adag_distinct i j hij
  have h2 : car.adag i * car.adag j = -(car.adag j * car.adag i) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_adag_adag i j)
  calc
    (car.adag i * car.a i) * car.adag j = car.adag i * (car.a i * car.adag j) := mul_assoc _ _ _
    _ = car.adag i * (-(car.adag j * car.a i)) := by rw [h1]
    _ = -(car.adag i * car.adag j) * car.a i := by rw [mul_neg, ← mul_assoc, neg_mul]
    _ = -(-(car.adag j * car.adag i)) * car.a i := by rw [h2]
    _ = car.adag j * (car.adag i * car.a i) := by rw [neg_neg, mul_assoc]

omit [Algebra ℝ A] in
private theorem modeNumber_comm_a_ne (car : QuasiparticleCAR ι A) (i j : ι) (hij : i ≠ j) :
    modeNumber car i * car.a j = car.a j * modeNumber car i := by
  unfold modeNumber
  have h1 : car.a i * car.a j = -(car.a j * car.a i) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_a_a i j)
  have h2 : car.adag i * car.a j = -(car.a j * car.adag i) := by
    have h := car.anticomm_a_adag j i
    simp only [hij.symm, ↓reduceIte] at h
    exact eq_neg_of_add_eq_zero_right h
  calc
    (car.adag i * car.a i) * car.a j = car.adag i * (car.a i * car.a j) := mul_assoc _ _ _
    _ = car.adag i * (-(car.a j * car.a i)) := by rw [h1]
    _ = -(car.adag i * car.a j) * car.a i := by rw [mul_neg, ← mul_assoc, neg_mul]
    _ = -(-(car.a j * car.adag i)) * car.a i := by rw [h2]
    _ = car.a j * (car.adag i * car.a i) := by rw [neg_neg, mul_assoc]

omit [Algebra ℝ A] in
theorem modeNumber_comm (car : QuasiparticleCAR ι A) (i j : ι) :
    modeNumber car i * modeNumber car j = modeNumber car j * modeNumber car i := by
  by_cases hij : i = j
  · subst hij; rfl
  · calc
      modeNumber car i * modeNumber car j =
          (modeNumber car i * car.adag j) * car.a j := by
        unfold modeNumber; simp only [mul_assoc]
      _ = (car.adag j * modeNumber car i) * car.a j := by
        rw [modeNumber_comm_adag_ne car i j hij]
      _ = car.adag j * (modeNumber car i * car.a j) := mul_assoc _ _ _
      _ = car.adag j * (car.a j * modeNumber car i) := by
        rw [modeNumber_comm_a_ne car i j hij]
      _ = modeNumber car j * modeNumber car i := by
        unfold modeNumber; rw [← mul_assoc]

omit [Algebra ℝ A] in
theorem modeParity_comm (car : QuasiparticleCAR ι A) (i j : ι) :
    modeParity car i * modeParity car j = modeParity car j * modeParity car i := by
  unfold modeParity
  have hc := modeNumber_comm car i j
  simp only [one_sub_mul, mul_one_sub]
  have h1 : (2 : A) * modeNumber car i * ((2 : A) * modeNumber car j) =
      (2 : A) * modeNumber car j * ((2 : A) * modeNumber car i) := by
    simp only [two_mul_ring, add_mul, mul_add, hc]
  rw [h1]
  abel

/-- Noncommutativity obstruction: single-mode fermion parity anticommutes with `a†_i`,
assigning `a†_i` odd fermionic grade. -/
theorem modeParity_anticomm_adag_same (car : QuasiparticleCAR ι A) (i : ι) :
    modeParity car i * car.adag i + car.adag i * modeParity car i = 0 := by
  unfold modeParity modeNumber
  have hL : (car.adag i * car.a i) * car.adag i = car.adag i := adag_mul_a_mul_adag_same car i
  have hR : car.adag i * (car.adag i * car.a i) = 0 := by
    rw [← mul_assoc, car.adag_sq i, zero_mul]
  calc
    (1 - (2 : A) * (car.adag i * car.a i)) * car.adag i +
        car.adag i * (1 - (2 : A) * (car.adag i * car.a i)) =
        car.adag i - (2 : A) * ((car.adag i * car.a i) * car.adag i) +
          (car.adag i - (2 : A) * (car.adag i * (car.adag i * car.a i))) := by
      noncomm_ring
    _ = car.adag i - (2 : A) * car.adag i + car.adag i := by rw [hL, hR, mul_zero, sub_zero]
    _ = car.adag i - (car.adag i + car.adag i) + car.adag i := by rw [two_mul_ring]
    _ = 0 := by abel

omit [Algebra ℝ A] in
theorem modeParity_comm_adag_ne (car : QuasiparticleCAR ι A) (i j : ι) (hij : i ≠ j) :
    modeParity car i * car.adag j = car.adag j * modeParity car i := by
  unfold modeParity
  have hc := modeNumber_comm_adag_ne car i j hij
  calc
    (1 - (2 : A) * modeNumber car i) * car.adag j =
        car.adag j - (2 : A) * (modeNumber car i * car.adag j) := by noncomm_ring
    _ = car.adag j - (2 : A) * (car.adag j * modeNumber car i) := by rw [hc]
    _ = car.adag j * (1 - (2 : A) * modeNumber car i) := by
      rw [mul_sub, mul_one, show car.adag j * ((2 : A) * modeNumber car i) =
          (2 : A) * (car.adag j * modeNumber car i) by
        rw [two_mul_ring, two_mul_ring, mul_add]]

omit [Algebra ℝ A] in
private theorem modeParity_pairwise_comm (car : QuasiparticleCAR ι A) (s : Finset ι) :
    (s : Set ι).Pairwise (Function.onFun Commute (modeParity car)) := by
  intro i _ j _ _
  exact modeParity_comm car i j

/-- Multi-mode fermion number parity `(-1)^{N_s} = ∏_{i ∈ s} (1 - 2 N_i)` over any finite
mode set `s : Finset ι`. -/
def finsetFermionParity (car : QuasiparticleCAR ι A) (s : Finset ι) : A :=
  s.noncommProd (modeParity car) (modeParity_pairwise_comm car s)

theorem finsetFermionParity_sq (car : QuasiparticleCAR ι A) (s : Finset ι) :
    finsetFermionParity car s * finsetFermionParity car s = 1 := by
  unfold finsetFermionParity
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty, mul_one]
  | @insert i s hi ih =>
    have hcomm : Commute (modeParity car i)
        (s.noncommProd (modeParity car) (modeParity_pairwise_comm car s)) := by
      apply Finset.noncommProd_commute
      intro j _
      exact modeParity_comm car i j
    have hins : (insert i s).noncommProd (modeParity car)
        (modeParity_pairwise_comm car (insert i s)) =
        modeParity car i * s.noncommProd (modeParity car) (modeParity_pairwise_comm car s) :=
      Finset.noncommProd_insert_of_notMem s i (modeParity car) _ hi
    rw [hins]
    let prodS : A := s.noncommProd (modeParity car) (modeParity_pairwise_comm car s)
    change (modeParity car i * prodS) * (modeParity car i * prodS) = 1
    calc
      (modeParity car i * prodS) * (modeParity car i * prodS) =
          (modeParity car i * modeParity car i) * (prodS * prodS) := by
        rw [mul_assoc, ← mul_assoc prodS (modeParity car i), ← hcomm.eq,
          mul_assoc, ← mul_assoc (modeParity car i) (modeParity car i)]
      _ = 1 := by rw [modeParity_sq car i, show prodS * prodS = 1 from ih, one_mul]

omit [Algebra ℝ A] in
theorem finsetFermionParity_comm (car : QuasiparticleCAR ι A) (s t : Finset ι) :
    finsetFermionParity car s * finsetFermionParity car t =
      finsetFermionParity car t * finsetFermionParity car s := by
  unfold finsetFermionParity
  have hmem : ∀ x ∈ s, Commute (modeParity car x)
      (t.noncommProd (modeParity car) (modeParity_pairwise_comm car t)) := by
    intro x _
    apply Finset.noncommProd_commute
    intro y _
    exact modeParity_comm car x y
  exact (Finset.noncommProd_commute s (modeParity car) _ _ fun x hx => (hmem x hx).symm).symm.eq

/-- Obstruction-driven odd fermionic grade: for ANY `s : Finset ι` and ANY `i ∈ s`,
`{ (-1)^{N_s}, a†_i } = 0`. -/
theorem finsetFermionParity_anticomm_adag (car : QuasiparticleCAR ι A) (s : Finset ι)
    {i : ι} (hi : i ∈ s) :
    finsetFermionParity car s * car.adag i + car.adag i * finsetFermionParity car s = 0 := by
  have hs : s = insert i (s.erase i) := (Finset.insert_erase hi).symm
  have hnot : i ∉ s.erase i := Finset.notMem_erase i s
  have hcomm_rest : Commute (car.adag i)
      ((s.erase i).noncommProd (modeParity car) (modeParity_pairwise_comm car (s.erase i))) := by
    apply Finset.noncommProd_commute
    intro j hj
    exact (modeParity_comm_adag_ne car j i (Finset.ne_of_mem_erase hj)).symm
  unfold finsetFermionParity
  have hcongr :
      s.noncommProd (modeParity car) (modeParity_pairwise_comm car s) =
        (insert i (s.erase i)).noncommProd (modeParity car)
          (modeParity_pairwise_comm car (insert i (s.erase i))) :=
    Finset.noncommProd_congr hs (fun _ _ => rfl) _
  have hins :
      (insert i (s.erase i)).noncommProd (modeParity car)
          (modeParity_pairwise_comm car (insert i (s.erase i))) =
        modeParity car i * (s.erase i).noncommProd (modeParity car)
          (modeParity_pairwise_comm car (s.erase i)) :=
    Finset.noncommProd_insert_of_notMem (s.erase i) i (modeParity car) _ hnot
  rw [hcongr, hins]
  calc
    (modeParity car i * (s.erase i).noncommProd (modeParity car) _) * car.adag i +
        car.adag i * (modeParity car i * (s.erase i).noncommProd (modeParity car) _) =
        modeParity car i * ((s.erase i).noncommProd (modeParity car) _ * car.adag i) +
          (car.adag i * modeParity car i) * (s.erase i).noncommProd (modeParity car) _ := by
      rw [mul_assoc, mul_assoc]
    _ = modeParity car i * (car.adag i * (s.erase i).noncommProd (modeParity car) _) +
          (car.adag i * modeParity car i) * (s.erase i).noncommProd (modeParity car) _ := by
      rw [hcomm_rest.eq]
    _ = (modeParity car i * car.adag i + car.adag i * modeParity car i) *
          (s.erase i).noncommProd (modeParity car) _ := by
      rw [← mul_assoc, add_mul]
    _ = 0 := by rw [modeParity_anticomm_adag_same car i, zero_mul]

/-- Emergent even pairing grade: `(-1)^{N_s}` commutes with any quasiparticle pair operator
`a†_i a†_j` (`i, j ∈ s`) because two odd anticommutation signs cancel. -/
theorem finsetFermionParity_comm_pairCreation (car : QuasiparticleCAR ι A) (s : Finset ι)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    finsetFermionParity car s * (car.adag i * car.adag j) =
      (car.adag i * car.adag j) * finsetFermionParity car s := by
  have hi' : finsetFermionParity car s * car.adag i = -(car.adag i * finsetFermionParity car s) :=
    eq_neg_of_add_eq_zero_left (finsetFermionParity_anticomm_adag car s hi)
  have hj' : finsetFermionParity car s * car.adag j = -(car.adag j * finsetFermionParity car s) :=
    eq_neg_of_add_eq_zero_left (finsetFermionParity_anticomm_adag car s hj)
  calc
    finsetFermionParity car s * (car.adag i * car.adag j) =
        (finsetFermionParity car s * car.adag i) * car.adag j := (mul_assoc _ _ _).symm
    _ = -(car.adag i * (finsetFermionParity car s * car.adag j)) := by
      rw [hi', neg_mul, mul_assoc]
    _ = (car.adag i * car.adag j) * finsetFermionParity car s := by
      rw [hj', mul_neg, neg_neg, mul_assoc]

end GeneralCARFermionParity

/-! ## Generalized Zorn / Witten–Möbius Involution & `[K₀, P_WM]` Obstruction -/

section GeneralZornWittenMoebius

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Superalgebra.WittenMoebiusParity

variable {R : Type*} [CommRing R]

/-- Left-alternative law in `ZornCell R`: `X * (X * Y) = (X * X) * Y`. -/
theorem zorn_mulZ_left_alternative (X Y : ZornCell R) :
    ZornCell.mulZ X (ZornCell.mulZ X Y) = ZornCell.mulZ (ZornCell.mulZ X X) Y := by
  refine ZornCell.ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (dsimp [ZornCell.mulZ]; ring)

theorem zorn_mulZ_oneZ_left (Y : ZornCell R) :
    ZornCell.mulZ (oneZ (R := R)) Y = Y := by
  refine ZornCell.ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (dsimp [ZornCell.mulZ, oneZ]; ring)

/-- Exact `[K₀, P_WM]` noncommutativity obstruction measuring chiral sheet mixing `U + V`. -/
theorem zorn_k0_wm_commutator_obstruction (c s u₁ u₂ u₃ v₁ v₂ v₃ : R) :
    subZ (ZornCell.mulZ (paraSymplecticK0 (R := R))
        (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃))
      (ZornCell.mulZ (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃)
        (paraSymplecticK0 (R := R))) =
      smulZ (-2 * s) (ZornCell.addZ (sheetU u₁ u₂ u₃) (sheetV v₁ v₂ v₃)) := by
  refine ZornCell.ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (dsimp [subZ, smulZ, ZornCell.mulZ, ZornCell.addZ, paraSymplecticK0,
      wittenMoebiusOperator, sheetU, sheetV]; ring)

def zornToVec (X : ZornCell R) : Fin 8 → R :=
  ![X.r, X.s, X.x1, X.x2, X.x3, X.y1, X.y2, X.y3]

def vecToZorn (v : Fin 8 → R) : ZornCell R :=
  ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7⟩

omit [CommRing R] in
private theorem vecToZorn_zornToVec (X : ZornCell R) : vecToZorn (zornToVec X) = X := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rfl

omit [CommRing R] in
private theorem zornToVec_vecToZorn (v : Fin 8 → R) : zornToVec (vecToZorn v) = v := by
  ext i
  fin_cases i <;> rfl

/-- Left multiplication operator `L_X` on `Fin 8 → R` induced by any `X : ZornCell R`. -/
def zornLeftOp (X : ZornCell R) : Module.End R (Fin 8 → R) where
  toFun v := zornToVec (ZornCell.mulZ X (vecToZorn v))
  map_add' v w := by
    ext i
    fin_cases i <;> (dsimp [zornToVec, ZornCell.mulZ, vecToZorn]; ring)
  map_smul' a v := by
    ext i
    fin_cases i <;> (dsimp [zornToVec, ZornCell.mulZ, vecToZorn]; ring)

theorem zornLeftOp_sq (X : ZornCell R) :
    zornLeftOp X * zornLeftOp X = zornLeftOp (ZornCell.mulZ X X) := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, zornLeftOp, LinearMap.coe_mk, AddHom.coe_mk,
    vecToZorn_zornToVec, zorn_mulZ_left_alternative]

theorem zornLeftOp_sq_one_of_mulZ_sq (X : ZornCell R)
    (hX : ZornCell.mulZ X X = oneZ) :
    zornLeftOp X * zornLeftOp X = 1 := by
  rw [zornLeftOp_sq X, hX]
  apply LinearMap.ext
  intro v
  simp only [zornLeftOp, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply,
    zorn_mulZ_oneZ_left, zornToVec_vecToZorn]

/-- Generalized Witten–Möbius parity operator in `Module.End R (Fin 8 → R)` is an involution
whenever `c^2 + s^2 = 1` and `u · v = -1`. -/
theorem wmZornLeftOp_sq (c s u₁ u₂ u₃ v₁ v₂ v₃ : R)
    (h_trig : c ^ 2 + s ^ 2 = 1)
    (h_epr : u₁ * v₁ + u₂ * v₂ + u₃ * v₃ = -1) :
    zornLeftOp (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃) *
      zornLeftOp (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃) = 1 := by
  apply zornLeftOp_sq_one_of_mulZ_sq
  exact (wittenMoebius_epr_singlet_involution c s u₁ u₂ u₃ v₁ v₂ v₃ h_trig h_epr).1

end GeneralZornWittenMoebius

/-! ## Generalized Four-Parity Tensor-Product Separation & 16 Joint Projectors -/

section GeneralFourParityTensor

open TensorProduct

variable {K : Type*} [Field K]
variable {V₁ V₂ V₃ V₄ : Type*}
variable [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup V₂] [Module K V₂]
variable [AddCommGroup V₃] [Module K V₃]
variable [AddCommGroup V₄] [Module K V₄]

abbrev FourFactorTensor (K V₁ V₂ V₃ V₄ : Type*) [CommRing K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    [AddCommGroup V₃] [Module K V₃] [AddCommGroup V₄] [Module K V₄] :=
  (V₁ ⊗[K] V₂) ⊗[K] (V₃ ⊗[K] V₄)

def liftFactor1 (f : Module.End K V₁) : Module.End K (FourFactorTensor K V₁ V₂ V₃ V₄) :=
  TensorProduct.map (TensorProduct.map f LinearMap.id) LinearMap.id

def liftFactor2 (f : Module.End K V₂) : Module.End K (FourFactorTensor K V₁ V₂ V₃ V₄) :=
  TensorProduct.map (TensorProduct.map LinearMap.id f) LinearMap.id

def liftFactor3 (f : Module.End K V₃) : Module.End K (FourFactorTensor K V₁ V₂ V₃ V₄) :=
  TensorProduct.map LinearMap.id (TensorProduct.map f LinearMap.id)

def liftFactor4 (f : Module.End K V₄) : Module.End K (FourFactorTensor K V₁ V₂ V₃ V₄) :=
  TensorProduct.map LinearMap.id (TensorProduct.map LinearMap.id f)

private theorem liftFactor1_mul (f g : Module.End K V₁) :
    liftFactor1 (K := K) (V₂ := V₂) (V₃ := V₃) (V₄ := V₄) (f * g) =
      liftFactor1 f * liftFactor1 g := by
  ext v₁ v₂ v₃ v₄
  simp [liftFactor1]

private theorem liftFactor2_mul (f g : Module.End K V₂) :
    liftFactor2 (K := K) (V₁ := V₁) (V₃ := V₃) (V₄ := V₄) (f * g) =
      liftFactor2 f * liftFactor2 g := by
  ext v₁ v₂ v₃ v₄
  simp [liftFactor2]

private theorem liftFactor3_mul (f g : Module.End K V₃) :
    liftFactor3 (K := K) (V₁ := V₁) (V₂ := V₂) (V₄ := V₄) (f * g) =
      liftFactor3 f * liftFactor3 g := by
  ext v₁ v₂ v₃ v₄
  simp [liftFactor3]

private theorem liftFactor4_mul (f g : Module.End K V₄) :
    liftFactor4 (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) (f * g) =
      liftFactor4 f * liftFactor4 g := by
  ext v₁ v₂ v₃ v₄
  simp [liftFactor4]

private theorem liftFactor1_one :
    liftFactor1 (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) (V₄ := V₄) 1 = 1 := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor1]

private theorem liftFactor2_one :
    liftFactor2 (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) (V₄ := V₄) 1 = 1 := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor2]

private theorem liftFactor3_one :
    liftFactor3 (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) (V₄ := V₄) 1 = 1 := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor3]

private theorem liftFactor4_one :
    liftFactor4 (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) (V₄ := V₄) 1 = 1 := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor4]

theorem liftFactor_1_2_comm (f : Module.End K V₁) (g : Module.End K V₂) :
    liftFactor1 (K := K) (V₃ := V₃) (V₄ := V₄) f * liftFactor2 g =
      liftFactor2 (K := K) (V₁ := V₁) (V₃ := V₃) (V₄ := V₄) g * liftFactor1 f := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor1, liftFactor2]

theorem liftFactor_1_3_comm (f : Module.End K V₁) (g : Module.End K V₃) :
    liftFactor1 (K := K) (V₂ := V₂) (V₄ := V₄) f * liftFactor3 g =
      liftFactor3 (K := K) (V₁ := V₁) (V₂ := V₂) (V₄ := V₄) g * liftFactor1 f := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor1, liftFactor3]

theorem liftFactor_1_4_comm (f : Module.End K V₁) (g : Module.End K V₄) :
    liftFactor1 (K := K) (V₂ := V₂) (V₃ := V₃) f * liftFactor4 g =
      liftFactor4 (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) g * liftFactor1 f := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor1, liftFactor4]

theorem liftFactor_2_3_comm (f : Module.End K V₂) (g : Module.End K V₃) :
    liftFactor2 (K := K) (V₁ := V₁) (V₄ := V₄) f * liftFactor3 g =
      liftFactor3 (K := K) (V₁ := V₁) (V₂ := V₂) (V₄ := V₄) g * liftFactor2 f := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor2, liftFactor3]

theorem liftFactor_2_4_comm (f : Module.End K V₂) (g : Module.End K V₄) :
    liftFactor2 (K := K) (V₁ := V₁) (V₃ := V₃) f * liftFactor4 g =
      liftFactor4 (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) g * liftFactor2 f := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor2, liftFactor4]

theorem liftFactor_3_4_comm (f : Module.End K V₃) (g : Module.End K V₄) :
    liftFactor3 (K := K) (V₁ := V₁) (V₂ := V₂) f * liftFactor4 g =
      liftFactor4 (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) g * liftFactor3 f := by
  ext v₁ v₂ v₃ v₄; simp [liftFactor3, liftFactor4]

section CharZeroProjectors

variable [CharZero K]

/-- Spectral eigensector projector `½ (1 ± P)` of an arbitrary involution `P`. -/
def involutionProjector {V : Type*} [AddCommGroup V] [Module K V]
    (P : Module.End K V) (b : Bool) : Module.End K V :=
  (1 / 2 : K) • (1 + (if b then (1 : K) else -1) • P)

theorem involutionProjector_idem {V : Type*} [AddCommGroup V] [Module K V]
    (P : Module.End K V) (hP : P * P = 1) (b : Bool) :
    involutionProjector (K := K) P b * involutionProjector (K := K) P b =
      involutionProjector (K := K) P b := by
  unfold involutionProjector
  rw [smul_mul_smul, show (1 / 2 : K) * (1 / 2 : K) = 1 / 4 by ring]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_smul, one_smul, add_mul, mul_add, one_mul,
      mul_one, neg_mul, mul_neg, smul_add, smul_neg, hP]
    module
  · simp only [↓reduceIte, one_smul, add_mul, mul_add, one_mul, mul_one, smul_add, hP]
    module

omit [CharZero K] in
theorem involutionProjector_orth {V : Type*} [AddCommGroup V] [Module K V]
    (P : Module.End K V) (hP : P * P = 1) (b b' : Bool) (h : b ≠ b') :
    involutionProjector (K := K) P b * involutionProjector (K := K) P b' = 0 := by
  unfold involutionProjector
  rw [smul_mul_smul]
  cases b <;> cases b' <;> simp at h
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_smul, one_smul, add_mul, mul_add,
      one_mul, mul_one, neg_mul, hP]
    apply smul_eq_zero_of_right
    abel
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_smul, one_smul, add_mul, mul_add,
      one_mul, mul_one, mul_neg, hP]
    apply smul_eq_zero_of_right
    abel

theorem involutionProjector_add {V : Type*} [AddCommGroup V] [Module K V]
    (P : Module.End K V) :
    involutionProjector (K := K) P true + involutionProjector (K := K) P false = 1 := by
  unfold involutionProjector
  simp only [↓reduceIte, Bool.false_eq_true, one_smul, neg_smul]
  module

omit [CharZero K] in
theorem mul_involutionProjector {V : Type*} [AddCommGroup V] [Module K V]
    (P : Module.End K V) (hP : P * P = 1) (b : Bool) :
    P * involutionProjector (K := K) P b =
      (if b then (1 : K) else -1) • involutionProjector (K := K) P b := by
  unfold involutionProjector
  rw [mul_smul_comm]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_smul, mul_add, mul_neg, mul_one, hP]
    rw [← smul_neg]
    congr 1
    abel
  · simp only [↓reduceIte, one_smul, mul_add, mul_one, hP, add_comm]

/-- Sixteen commuting joint projectors on `FourFactorTensor K V₁ V₂ V₃ V₄`. -/
def generalFourParityProjector
    (P₁ : Module.End K V₁) (P₂ : Module.End K V₂)
    (P₃ : Module.End K V₃) (P₄ : Module.End K V₄)
    (b : Fin 4 → Bool) : Module.End K (FourFactorTensor K V₁ V₂ V₃ V₄) :=
  liftFactor1 (involutionProjector (K := K) P₁ (b 0)) *
  liftFactor2 (involutionProjector (K := K) P₂ (b 1)) *
  liftFactor3 (involutionProjector (K := K) P₃ (b 2)) *
  liftFactor4 (involutionProjector (K := K) P₄ (b 3))

omit [CharZero K] in
theorem generalFourParityProjector_apply_tmul
    (P₁ : Module.End K V₁) (P₂ : Module.End K V₂)
    (P₃ : Module.End K V₃) (P₄ : Module.End K V₄)
    (b : Fin 4 → Bool) (v₁ : V₁) (v₂ : V₂) (v₃ : V₃) (v₄ : V₄) :
    generalFourParityProjector (K := K) P₁ P₂ P₃ P₄ b ((v₁ ⊗ₜ[K] v₂) ⊗ₜ[K] (v₃ ⊗ₜ[K] v₄)) =
      (involutionProjector (K := K) P₁ (b 0) v₁ ⊗ₜ[K] involutionProjector (K := K) P₂ (b 1) v₂) ⊗ₜ[K]
      (involutionProjector (K := K) P₃ (b 2) v₃ ⊗ₜ[K] involutionProjector (K := K) P₄ (b 3) v₄) := by
  unfold generalFourParityProjector
  simp [Module.End.mul_apply, liftFactor1, liftFactor2, liftFactor3, liftFactor4]

theorem generalFourParityProjector_idem
    (P₁ : Module.End K V₁) (P₂ : Module.End K V₂)
    (P₃ : Module.End K V₃) (P₄ : Module.End K V₄)
    (h1 : P₁ * P₁ = 1) (h2 : P₂ * P₂ = 1) (h3 : P₃ * P₃ = 1) (h4 : P₄ * P₄ = 1)
    (b : Fin 4 → Bool) :
    generalFourParityProjector (K := K) P₁ P₂ P₃ P₄ b *
      generalFourParityProjector (K := K) P₁ P₂ P₃ P₄ b =
      generalFourParityProjector (K := K) P₁ P₂ P₃ P₄ b := by
  ext v₁ v₂ v₃ v₄
  change generalFourParityProjector (K := K) P₁ P₂ P₃ P₄ b
      (generalFourParityProjector (K := K) P₁ P₂ P₃ P₄ b ((v₁ ⊗ₜ[K] v₂) ⊗ₜ[K] (v₃ ⊗ₜ[K] v₄))) =
    generalFourParityProjector (K := K) P₁ P₂ P₃ P₄ b ((v₁ ⊗ₜ[K] v₂) ⊗ₜ[K] (v₃ ⊗ₜ[K] v₄))
  simp only [generalFourParityProjector_apply_tmul]
  rw [← Module.End.mul_apply, involutionProjector_idem P₁ h1,
    ← Module.End.mul_apply, involutionProjector_idem P₂ h2,
    ← Module.End.mul_apply, involutionProjector_idem P₃ h3,
    ← Module.End.mul_apply, involutionProjector_idem P₄ h4]

omit [CharZero K] in
private theorem eig_of_non_scalar_involution {V : Type*} [AddCommGroup V] [Module K V]
    (P : Module.End K V) (hP : P * P = 1) (hne1 : P ≠ 1) (hnem1 : P ≠ -1) :
    (∃ vPos : V, vPos ≠ 0 ∧ P vPos = vPos) ∧ (∃ vNeg : V, vNeg ≠ 0 ∧ P vNeg = -vNeg) := by
  refine ⟨?_, ?_⟩
  · have hex : ∃ x : V, P x ≠ -x := by
      by_contra hall
      push Not at hall
      apply hnem1
      ext x
      exact hall x
    rcases hex with ⟨x, hx⟩
    refine ⟨x + P x, ?_, ?_⟩
    · intro hz
      apply hx
      exact eq_neg_of_add_eq_zero_right hz
    · rw [map_add, ← Module.End.mul_apply, hP, Module.End.one_apply, add_comm]
  · have hex : ∃ y : V, P y ≠ y := by
      by_contra hall
      push Not at hall
      apply hne1
      ext y
      exact hall y
    rcases hex with ⟨y, hy⟩
    refine ⟨y - P y, ?_, ?_⟩
    · intro hz
      apply hy
      exact (sub_eq_zero.mp hz).symm
    · rw [map_sub, ← Module.End.mul_apply, hP, Module.End.one_apply, neg_sub]

omit [CharZero K] in
private theorem basis_coord_ne_zero {V ι : Type*} [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {v : V} (hv : v ≠ 0) : ∃ i : ι, b.coord i v ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hv
  apply b.ext_elem
  intro i
  simpa using hall i

private theorem involutionProjector_apply_eig {V : Type*} [AddCommGroup V] [Module K V]
    (P : Module.End K V) (vp vm : V) (hp : P vp = vp) (hm : P vm = -vm) (c : Bool) :
    involutionProjector (K := K) P c (if c then vp else vm) = if c then vp else vm := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero
  unfold involutionProjector
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, neg_smul, one_smul, LinearMap.neg_apply, hm, neg_neg]
    rw [← two_smul K, smul_smul, show (1 / 2 : K) * 2 = 1 by field_simp [h2K], one_smul]
  · simp only [↓reduceIte, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
      one_smul, hp]
    rw [← two_smul K, smul_smul, show (1 / 2 : K) * 2 = 1 by field_simp [h2K], one_smul]

omit [CharZero K] in
private theorem tmul_four_ne_zero (v₁ : V₁) (v₂ : V₂) (v₃ : V₃) (v₄ : V₄)
    (h1 : v₁ ≠ 0) (h2 : v₂ ≠ 0) (h3 : v₃ ≠ 0) (h4 : v₄ ≠ 0) :
    ((v₁ ⊗ₜ[K] v₂) ⊗ₜ[K] (v₃ ⊗ₜ[K] v₄)) ≠ 0 := by
  obtain ⟨ι₁, ⟨b₁⟩⟩ := Module.Basis.exists_basis K V₁
  obtain ⟨ι₂, ⟨b₂⟩⟩ := Module.Basis.exists_basis K V₂
  obtain ⟨ι₃, ⟨b₃⟩⟩ := Module.Basis.exists_basis K V₃
  obtain ⟨ι₄, ⟨b₄⟩⟩ := Module.Basis.exists_basis K V₄
  obtain ⟨i₁, hi₁⟩ := basis_coord_ne_zero (K := K) b₁ h1
  obtain ⟨i₂, hi₂⟩ := basis_coord_ne_zero (K := K) b₂ h2
  obtain ⟨i₃, hi₃⟩ := basis_coord_ne_zero (K := K) b₃ h3
  obtain ⟨i₄, hi₄⟩ := basis_coord_ne_zero (K := K) b₄ h4
  let Φ₁₂ : V₁ ⊗[K] V₂ →ₗ[K] K :=
    (TensorProduct.lid K K).toLinearMap.comp (TensorProduct.map (b₁.coord i₁) (b₂.coord i₂))
  let Φ₃₄ : V₃ ⊗[K] V₄ →ₗ[K] K :=
    (TensorProduct.lid K K).toLinearMap.comp (TensorProduct.map (b₃.coord i₃) (b₄.coord i₄))
  let Φ : FourFactorTensor K V₁ V₂ V₃ V₄ →ₗ[K] K :=
    (TensorProduct.lid K K).toLinearMap.comp (TensorProduct.map Φ₁₂ Φ₃₄)
  intro hz
  have hval : Φ ((v₁ ⊗ₜ[K] v₂) ⊗ₜ[K] (v₃ ⊗ₜ[K] v₄)) = 0 := by
    rw [hz, map_zero]
  have hcalc : Φ ((v₁ ⊗ₜ[K] v₂) ⊗ₜ[K] (v₃ ⊗ₜ[K] v₄)) =
      ((b₁.coord i₁ v₁) * (b₂.coord i₂ v₂)) * ((b₃.coord i₃ v₃) * (b₄.coord i₄ v₄)) := by
    simp [Φ, Φ₁₂, Φ₃₄, smul_eq_mul]
  rw [hcalc] at hval
  exact mul_ne_zero (mul_ne_zero hi₁ hi₂) (mul_ne_zero hi₃ hi₄) hval

/-- **Generalized Four-Parity Separation & 16-Sector Compatibility Theorem**:
For ANY four involutions `P₁, P₂, P₃, P₄` on arbitrary `K`-modules `V₁, V₂, V₃, V₄`
with `Pᵢ^2 = 1` and `Pᵢ ≠ ±1`, the lifted operators on `V₁ ⊗ V₂ ⊗ V₃ ⊗ V₄`:
1. remain involutions (`Lᵢ^2 = 1`);
2. mutually commute pairwise;
3. are pairwise strictly distinct (`Lᵢ ≠ Lⱼ` for all `i ≠ j`);
4. induce 16 nonzero idempotent commuting eigensector projectors `Q(b) ≠ 0`. -/
theorem general_four_parity_separation_and_compatibility
    (P₁ : Module.End K V₁) (P₂ : Module.End K V₂)
    (P₃ : Module.End K V₃) (P₄ : Module.End K V₄)
    (h1 : P₁ * P₁ = 1) (h2 : P₂ * P₂ = 1) (h3 : P₃ * P₃ = 1) (h4 : P₄ * P₄ = 1)
    (hne1 : P₁ ≠ 1 ∧ P₁ ≠ -1) (hne2 : P₂ ≠ 1 ∧ P₂ ≠ -1)
    (hne3 : P₃ ≠ 1 ∧ P₃ ≠ -1) (hne4 : P₄ ≠ 1 ∧ P₄ ≠ -1) :
    let L₁ := liftFactor1 (K := K) (V₂ := V₂) (V₃ := V₃) (V₄ := V₄) P₁
    let L₂ := liftFactor2 (K := K) (V₁ := V₁) (V₃ := V₃) (V₄ := V₄) P₂
    let L₃ := liftFactor3 (K := K) (V₁ := V₁) (V₂ := V₂) (V₄ := V₄) P₃
    let L₄ := liftFactor4 (K := K) (V₁ := V₁) (V₂ := V₂) (V₃ := V₃) P₄
    (L₁ * L₁ = 1 ∧ L₂ * L₂ = 1 ∧ L₃ * L₃ = 1 ∧ L₄ * L₄ = 1) ∧
    (L₁ * L₂ = L₂ * L₁ ∧ L₁ * L₃ = L₃ * L₁ ∧ L₁ * L₄ = L₄ * L₁ ∧
     L₂ * L₃ = L₃ * L₂ ∧ L₂ * L₄ = L₄ * L₂ ∧ L₃ * L₄ = L₄ * L₃) ∧
    (L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₁ ≠ L₄ ∧ L₂ ≠ L₃ ∧ L₂ ≠ L₄ ∧ L₃ ≠ L₄) ∧
    (∀ b : Fin 4 → Bool, generalFourParityProjector (K := K) P₁ P₂ P₃ P₄ b ≠ 0) := by
  dsimp only
  obtain ⟨⟨v1p, hv1p, hP1p⟩, ⟨v1m, hv1m, hP1m⟩⟩ :=
    eig_of_non_scalar_involution P₁ h1 hne1.1 hne1.2
  obtain ⟨⟨v2p, hv2p, hP2p⟩, ⟨v2m, hv2m, hP2m⟩⟩ :=
    eig_of_non_scalar_involution P₂ h2 hne2.1 hne2.2
  obtain ⟨⟨v3p, hv3p, hP3p⟩, ⟨v3m, hv3m, hP3m⟩⟩ :=
    eig_of_non_scalar_involution P₃ h3 hne3.1 hne3.2
  obtain ⟨⟨v4p, hv4p, hP4p⟩, ⟨v4m, hv4m, hP4m⟩⟩ :=
    eig_of_non_scalar_involution P₄ h4 hne4.1 hne4.2
  have h2K : (2 : K) ≠ 0 := two_ne_zero
  have neg_ne_self : ∀ {w : FourFactorTensor K V₁ V₂ V₃ V₄}, w ≠ 0 → -w ≠ w := by
    intro w hw heq
    apply hw
    have h2w : (2 : K) • w = 0 := by
      rw [two_smul]
      calc
        w + w = (-w) + w := by rw [heq]
        _ = 0 := neg_add_cancel w
    have := congrArg (fun x => (1 / 2 : K) • x) h2w
    rw [smul_smul, show (1 / 2 : K) * 2 = 1 by field_simp [h2K], one_smul, smul_zero] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← liftFactor1_mul, h1, liftFactor1_one]
    · rw [← liftFactor2_mul, h2, liftFactor2_one]
    · rw [← liftFactor3_mul, h3, liftFactor3_one]
    · rw [← liftFactor4_mul, h4, liftFactor4_one]
  · exact ⟨liftFactor_1_2_comm P₁ P₂, liftFactor_1_3_comm P₁ P₃, liftFactor_1_4_comm P₁ P₄,
      liftFactor_2_3_comm P₂ P₃, liftFactor_2_4_comm P₂ P₄, liftFactor_3_4_comm P₃ P₄⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have hv := congrArg (fun op => op ((v1p ⊗ₜ[K] v2m) ⊗ₜ[K] (v3p ⊗ₜ[K] v4p))) h
      simp only [liftFactor1, liftFactor2, TensorProduct.map_tmul, LinearMap.id_coe,
        id_eq, hP1p, hP2m, tmul_neg, neg_tmul] at hv
      exact neg_ne_self (tmul_four_ne_zero v1p v2m v3p v4p hv1p hv2m hv3p hv4p) hv.symm
    · intro h
      have hv := congrArg (fun op => op ((v1p ⊗ₜ[K] v2p) ⊗ₜ[K] (v3m ⊗ₜ[K] v4p))) h
      simp only [liftFactor1, liftFactor3, TensorProduct.map_tmul, LinearMap.id_coe,
        id_eq, hP1p, hP3m, tmul_neg, neg_tmul] at hv
      exact neg_ne_self (tmul_four_ne_zero v1p v2p v3m v4p hv1p hv2p hv3m hv4p) hv.symm
    · intro h
      have hv := congrArg (fun op => op ((v1p ⊗ₜ[K] v2p) ⊗ₜ[K] (v3p ⊗ₜ[K] v4m))) h
      simp only [liftFactor1, liftFactor4, TensorProduct.map_tmul, LinearMap.id_coe,
        id_eq, hP1p, hP4m, tmul_neg] at hv
      exact neg_ne_self (tmul_four_ne_zero v1p v2p v3p v4m hv1p hv2p hv3p hv4m) hv.symm
    · intro h
      have hv := congrArg (fun op => op ((v1p ⊗ₜ[K] v2p) ⊗ₜ[K] (v3m ⊗ₜ[K] v4p))) h
      simp only [liftFactor2, liftFactor3, TensorProduct.map_tmul, LinearMap.id_coe,
        id_eq, hP2p, hP3m, tmul_neg, neg_tmul] at hv
      exact neg_ne_self (tmul_four_ne_zero v1p v2p v3m v4p hv1p hv2p hv3m hv4p) hv.symm
    · intro h
      have hv := congrArg (fun op => op ((v1p ⊗ₜ[K] v2p) ⊗ₜ[K] (v3p ⊗ₜ[K] v4m))) h
      simp only [liftFactor2, liftFactor4, TensorProduct.map_tmul, LinearMap.id_coe,
        id_eq, hP2p, hP4m, tmul_neg] at hv
      exact neg_ne_self (tmul_four_ne_zero v1p v2p v3p v4m hv1p hv2p hv3p hv4m) hv.symm
    · intro h
      have hv := congrArg (fun op => op ((v1p ⊗ₜ[K] v2p) ⊗ₜ[K] (v3p ⊗ₜ[K] v4m))) h
      simp only [liftFactor3, liftFactor4, TensorProduct.map_tmul, LinearMap.id_coe,
        id_eq, hP3p, hP4m, tmul_neg] at hv
      exact neg_ne_self (tmul_four_ne_zero v1p v2p v3p v4m hv1p hv2p hv3p hv4m) hv.symm
  · intro b hb
    let u₁ : V₁ := if b 0 then v1p else v1m
    let u₂ : V₂ := if b 1 then v2p else v2m
    let u₃ : V₃ := if b 2 then v3p else v3m
    let u₄ : V₄ := if b 3 then v4p else v4m
    have hu₁ : u₁ ≠ 0 := by dsimp [u₁]; split_ifs <;> assumption
    have hu₂ : u₂ ≠ 0 := by dsimp [u₂]; split_ifs <;> assumption
    have hu₃ : u₃ ≠ 0 := by dsimp [u₃]; split_ifs <;> assumption
    have hu₄ : u₄ ≠ 0 := by dsimp [u₄]; split_ifs <;> assumption
    have hact := congrArg (fun op => op ((u₁ ⊗ₜ[K] u₂) ⊗ₜ[K] (u₃ ⊗ₜ[K] u₄))) hb
    rw [generalFourParityProjector_apply_tmul, LinearMap.zero_apply] at hact
    have heq₁ : involutionProjector (K := K) P₁ (b 0) u₁ = u₁ := by
      dsimp only [u₁]; exact involutionProjector_apply_eig (K := K) P₁ v1p v1m hP1p hP1m (b 0)
    have heq₂ : involutionProjector (K := K) P₂ (b 1) u₂ = u₂ := by
      dsimp only [u₂]; exact involutionProjector_apply_eig (K := K) P₂ v2p v2m hP2p hP2m (b 1)
    have heq₃ : involutionProjector (K := K) P₃ (b 2) u₃ = u₃ := by
      dsimp only [u₃]; exact involutionProjector_apply_eig (K := K) P₃ v3p v3m hP3p hP3m (b 2)
    have heq₄ : involutionProjector (K := K) P₄ (b 3) u₄ = u₄ := by
      dsimp only [u₄]; exact involutionProjector_apply_eig (K := K) P₄ v4p v4m hP4p hP4m (b 3)
    rw [heq₁, heq₂, heq₃, heq₄] at hact
    exact tmul_four_ne_zero u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ hact

end CharZeroProjectors

end GeneralFourParityTensor

/-! ## Concrete Four-Parity Carrier Witness (Spatial `π`, `(-1)^N`, `P_WM`/`K₀`, Meng `ChP`) -/

section ConcreteFourParityWitness

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Superalgebra.WittenMoebiusParity
open InfoGeometry.Physics.NuclearTwoModeCARFiveGrade

/-- Concrete 4D Meng chiral-parity carrier `(c, p) ∈ Fin 2 × Fin 2` matching `ChpCarrierSpace`. -/
abbrev ChpCarrierSpace := Fin 2 × Fin 2 → ℂ

def chpRotationOp : Module.End ℂ ChpCarrierSpace where
  toFun ψ := fun cp => (if cp.2 = 0 then (1 : ℂ) else -1) * ψ (Equiv.swap 0 1 cp.1, cp.2)
  map_add' ψ φ := by ext ⟨c, p⟩; fin_cases p <;> (simp; try abel)
  map_smul' a ψ := by ext ⟨c, p⟩; fin_cases p <;> simp

def chpExchangeOp : Module.End ℂ ChpCarrierSpace := 1

def chpIntrinsicParityOp : Module.End ℂ ChpCarrierSpace where
  toFun ψ := fun cp => (if cp.2 = 0 then (1 : ℂ) else -1) * ψ cp
  map_add' ψ φ := by ext ⟨c, p⟩; fin_cases p <;> (simp; try abel)
  map_smul' a ψ := by ext ⟨c, p⟩; fin_cases p <;> simp

def chpChitureOp : Module.End ℂ ChpCarrierSpace :=
  MengChPSelectionRules.chiture chpRotationOp chpExchangeOp chpIntrinsicParityOp

def chpChiplexOp : Module.End ℂ ChpCarrierSpace :=
  MengChPSelectionRules.chiplex chpChitureOp chpIntrinsicParityOp

theorem chpChitureOp_sq : chpChitureOp * chpChitureOp = 1 := by
  ext ψ ⟨c, p⟩
  fin_cases c <;> fin_cases p <;>
    simp [chpChitureOp, MengChPSelectionRules.chiture, chpRotationOp, chpExchangeOp,
      chpIntrinsicParityOp, Module.End.mul_apply]

theorem chpIntrinsicParityOp_sq : chpIntrinsicParityOp * chpIntrinsicParityOp = 1 := by
  ext ψ ⟨c, p⟩
  fin_cases c <;> fin_cases p <;> simp [chpIntrinsicParityOp, Module.End.mul_apply]

theorem chpChiplexOp_sq : chpChiplexOp * chpChiplexOp = 1 := by
  ext ψ ⟨c, p⟩
  fin_cases c <;> fin_cases p <;>
    simp [chpChiplexOp, MengChPSelectionRules.chiplex, chpChitureOp, MengChPSelectionRules.chiture,
      chpRotationOp, chpExchangeOp, chpIntrinsicParityOp, Module.End.mul_apply]

/-- Joint concrete carrier combining spatial parity `Fin 2`, two-mode Fock space `Fin 4`,
split-octonion Zorn cell `Fin 8`, and triaxial Meng chiral-parity space `Fin 2 × Fin 2`. -/
abbrev FourParityCarrier :=
  (Fin 2 × Fin 4 × Fin 8 × (Fin 2 × Fin 2)) → ℂ

private def liftSector1 (op : Module.End ℂ (Fin 2 → ℂ)) : Module.End ℂ FourParityCarrier where
  toFun ψ := fun x => op (fun a => ψ (a, x.2.1, x.2.2.1, x.2.2.2)) x.1
  map_add' ψ φ := by
    ext ⟨a, b, c, d⟩
    change op (fun a' => ψ (a', b, c, d) + φ (a', b, c, d)) a = _
    rw [show (fun a' => ψ (a', b, c, d) + φ (a', b, c, d)) =
        (fun a' => ψ (a', b, c, d)) + (fun a' => φ (a', b, c, d)) from rfl,
      map_add, Pi.add_apply]
    rfl
  map_smul' r ψ := by
    ext ⟨a, b, c, d⟩
    change op (fun a' => r * ψ (a', b, c, d)) a = _
    rw [show (fun a' => r * ψ (a', b, c, d)) = r • (fun a' => ψ (a', b, c, d)) from rfl,
      map_smul, Pi.smul_apply]
    rfl

private def liftSector2 (op : Module.End ℂ (Fin 4 → ℂ)) : Module.End ℂ FourParityCarrier where
  toFun ψ := fun x => op (fun b => ψ (x.1, b, x.2.2.1, x.2.2.2)) x.2.1
  map_add' ψ φ := by
    ext ⟨a, b, c, d⟩
    change op (fun b' => ψ (a, b', c, d) + φ (a, b', c, d)) b = _
    rw [show (fun b' => ψ (a, b', c, d) + φ (a, b', c, d)) =
        (fun b' => ψ (a, b', c, d)) + (fun b' => φ (a, b', c, d)) from rfl,
      map_add, Pi.add_apply]
    rfl
  map_smul' r ψ := by
    ext ⟨a, b, c, d⟩
    change op (fun b' => r * ψ (a, b', c, d)) b = _
    rw [show (fun b' => r * ψ (a, b', c, d)) = r • (fun b' => ψ (a, b', c, d)) from rfl,
      map_smul, Pi.smul_apply]
    rfl

private def liftSector3 (op : Module.End ℂ (Fin 8 → ℂ)) : Module.End ℂ FourParityCarrier where
  toFun ψ := fun x => op (fun c => ψ (x.1, x.2.1, c, x.2.2.2)) x.2.2.1
  map_add' ψ φ := by
    ext ⟨a, b, c, d⟩
    change op (fun c' => ψ (a, b, c', d) + φ (a, b, c', d)) c = _
    rw [show (fun c' => ψ (a, b, c', d) + φ (a, b, c', d)) =
        (fun c' => ψ (a, b, c', d)) + (fun c' => φ (a, b, c', d)) from rfl,
      map_add, Pi.add_apply]
    rfl
  map_smul' r ψ := by
    ext ⟨a, b, c, d⟩
    change op (fun c' => r * ψ (a, b, c', d)) c = _
    rw [show (fun c' => r * ψ (a, b, c', d)) = r • (fun c' => ψ (a, b, c', d)) from rfl,
      map_smul, Pi.smul_apply]
    rfl

private def liftSector4 (op : Module.End ℂ ChpCarrierSpace) :
    Module.End ℂ FourParityCarrier where
  toFun ψ := fun x => op (fun d => ψ (x.1, x.2.1, x.2.2.1, d)) x.2.2.2
  map_add' ψ φ := by
    ext ⟨a, b, c, d⟩
    change op (fun d' => ψ (a, b, c, d') + φ (a, b, c, d')) d = _
    rw [show (fun d' => ψ (a, b, c, d') + φ (a, b, c, d')) =
        (fun d' => ψ (a, b, c, d')) + (fun d' => φ (a, b, c, d')) from rfl,
      map_add, Pi.add_apply]
    rfl
  map_smul' r ψ := by
    ext ⟨a, b, c, d⟩
    change op (fun d' => r * ψ (a, b, c, d')) d = _
    rw [show (fun d' => r * ψ (a, b, c, d')) = r • (fun d' => ψ (a, b, c, d')) from rfl,
      map_smul, Pi.smul_apply]
    rfl

private theorem liftSector1_mul (f g : Module.End ℂ (Fin 2 → ℂ)) :
    liftSector1 (f * g) = liftSector1 f * liftSector1 g := by
  ext ψ ⟨a, b, c, d⟩
  simp [liftSector1, Module.End.mul_apply]

private theorem liftSector2_mul (f g : Module.End ℂ (Fin 4 → ℂ)) :
    liftSector2 (f * g) = liftSector2 f * liftSector2 g := by
  ext ψ ⟨a, b, c, d⟩
  simp [liftSector2, Module.End.mul_apply]

private theorem liftSector3_mul (f g : Module.End ℂ (Fin 8 → ℂ)) :
    liftSector3 (f * g) = liftSector3 f * liftSector3 g := by
  ext ψ ⟨a, b, c, d⟩
  simp [liftSector3, Module.End.mul_apply]

private theorem liftSector4_mul (f g : Module.End ℂ ChpCarrierSpace) :
    liftSector4 (f * g) = liftSector4 f * liftSector4 g := by
  ext ψ ⟨a, b, c, d⟩
  simp [liftSector4, Module.End.mul_apply]

private theorem liftSector1_one : liftSector1 1 = 1 := by
  ext ψ ⟨a, b, c, d⟩; simp [liftSector1]

private theorem liftSector2_one : liftSector2 1 = 1 := by
  ext ψ ⟨a, b, c, d⟩; simp [liftSector2]

private theorem liftSector3_one : liftSector3 1 = 1 := by
  ext ψ ⟨a, b, c, d⟩; simp [liftSector3]

private theorem liftSector4_one : liftSector4 1 = 1 := by
  ext ψ ⟨a, b, c, d⟩; simp [liftSector4]

private theorem fun_expand_single {α : Type*} [Fintype α] [DecidableEq α] (v : α → ℂ) :
    v = ∑ x : α, v x • Pi.single x (1 : ℂ) := by
  ext y
  simp [Finset.sum_apply, Pi.single_apply]

private theorem end_apply_sum_comm {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (op₁ : Module.End ℂ (α → ℂ)) (op₂ : Module.End ℂ (β → ℂ))
    (ψ : α → β → ℂ) (a : α) (b : β) :
    op₁ (fun a' => op₂ (fun b' => ψ a' b') b) a =
      op₂ (fun b' => op₁ (fun a' => ψ a' b') a) b := by
  have hrow : ∀ a' : α,
      op₂ (fun b' => ψ a' b') b = ∑ b' : β, op₂ (Pi.single b' (1 : ℂ)) b * ψ a' b' := by
    intro a'
    conv_lhs => rw [fun_expand_single (fun b' => ψ a' b')]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hcol : ∀ b' : β,
      op₁ (fun a' => ψ a' b') a = ∑ a' : α, op₁ (Pi.single a' (1 : ℂ)) a * ψ a' b' := by
    intro b'
    conv_lhs => rw [fun_expand_single (fun a' => ψ a' b')]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hf1 : (fun a' => op₂ (fun b' => ψ a' b') b) =
      ∑ b' : β, op₂ (Pi.single b' (1 : ℂ)) b • (fun a' => ψ a' b') := by
    ext a'
    rw [Finset.sum_apply, hrow a']
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp [smul_eq_mul]
  have hf2 : (fun b' => op₁ (fun a' => ψ a' b') a) =
      ∑ a' : α, op₁ (Pi.single a' (1 : ℂ)) a • (fun b' => ψ a' b') := by
    ext b'
    rw [Finset.sum_apply, hcol b']
    refine Finset.sum_congr rfl fun a' _ => ?_
    simp [smul_eq_mul]
  rw [hf1, hf2, map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, hcol, hrow, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
  ring

theorem liftSector_1_2_comm (f : Module.End ℂ (Fin 2 → ℂ)) (g : Module.End ℂ (Fin 4 → ℂ)) :
    liftSector1 f * liftSector2 g = liftSector2 g * liftSector1 f := by
  apply LinearMap.ext; intro ψ; ext ⟨a, b, c, d⟩
  exact end_apply_sum_comm f g (fun a' b' => ψ (a', b', c, d)) a b

theorem liftSector_1_3_comm (f : Module.End ℂ (Fin 2 → ℂ)) (g : Module.End ℂ (Fin 8 → ℂ)) :
    liftSector1 f * liftSector3 g = liftSector3 g * liftSector1 f := by
  apply LinearMap.ext; intro ψ; ext ⟨a, b, c, d⟩
  exact end_apply_sum_comm f g (fun a' c' => ψ (a', b, c', d)) a c

theorem liftSector_1_4_comm (f : Module.End ℂ (Fin 2 → ℂ)) (g : Module.End ℂ ChpCarrierSpace) :
    liftSector1 f * liftSector4 g = liftSector4 g * liftSector1 f := by
  apply LinearMap.ext; intro ψ; ext ⟨a, b, c, d⟩
  exact end_apply_sum_comm f g (fun a' d' => ψ (a', b, c, d')) a d

theorem liftSector_2_3_comm (f : Module.End ℂ (Fin 4 → ℂ)) (g : Module.End ℂ (Fin 8 → ℂ)) :
    liftSector2 f * liftSector3 g = liftSector3 g * liftSector2 f := by
  apply LinearMap.ext; intro ψ; ext ⟨a, b, c, d⟩
  exact end_apply_sum_comm f g (fun b' c' => ψ (a, b', c', d)) b c

theorem liftSector_2_4_comm (f : Module.End ℂ (Fin 4 → ℂ)) (g : Module.End ℂ ChpCarrierSpace) :
    liftSector2 f * liftSector4 g = liftSector4 g * liftSector2 f := by
  apply LinearMap.ext; intro ψ; ext ⟨a, b, c, d⟩
  exact end_apply_sum_comm f g (fun b' d' => ψ (a, b', c, d')) b d

theorem liftSector_3_4_comm (f : Module.End ℂ (Fin 8 → ℂ)) (g : Module.End ℂ ChpCarrierSpace) :
    liftSector3 f * liftSector4 g = liftSector4 g * liftSector3 f := by
  apply LinearMap.ext; intro ψ; ext ⟨a, b, c, d⟩
  exact end_apply_sum_comm f g (fun c' d' => ψ (a, b, c', d')) c d

/-- Spatial parity base involution `π` on `Fin 2 → ℂ` (`+1` on `0`, `-1` on `1`). -/
def piBaseOp : Module.End ℂ (Fin 2 → ℂ) where
  toFun v := ![v 0, -v 1]
  map_add' v w := by ext i; fin_cases i <;> (simp; try ring)
  map_smul' r v := by ext i; fin_cases i <;> simp

theorem piBaseOp_sq : piBaseOp * piBaseOp = 1 := by
  ext v i
  fin_cases i <;> simp [piBaseOp, Module.End.mul_apply]

/-- Two-mode fermion number parity `(-1)^{N_1 + N_2} = (1 - 2 N_1)(1 - 2 N_2)` on `Fock4`. -/
def fermionBaseOp : Module.End ℂ Fock4 :=
  (1 - (2 : ℂ) • numberOne) * (1 - (2 : ℂ) • numberTwo)

theorem fermionBaseOp_apply (ψ : Fock4) :
    fermionBaseOp ψ = ![ψ 0, -ψ 1, -ψ 2, ψ 3] := by
  ext i
  fin_cases i <;>
    (simp [fermionBaseOp, Module.End.mul_apply, numberOne, numberTwo,
      creationOne_apply, annihilationOne_apply, creationTwo_apply, annihilationTwo_apply];
     dsimp [Matrix.vecHead, Matrix.vecTail];
     try ring)

theorem fermionBaseOp_sq : fermionBaseOp * fermionBaseOp = 1 := by
  ext ψ i
  fin_cases i <;> simp [Module.End.mul_apply, fermionBaseOp_apply]

/-- Obstruction-driven odd fermionic grade: `fermionBaseOp` anticommutes with single-quasiparticle
creation `creationOne`. -/
theorem fermionBaseOp_anticomm_creationOne :
    fermionBaseOp * creationOne + creationOne * fermionBaseOp = 0 := by
  ext ψ i
  fin_cases i <;> simp [Module.End.mul_apply, fermionBaseOp_apply, creationOne_apply]

/-- Even pairing grade: `fermionBaseOp` commutes with pair creation `a†_1 a†_2`. -/
theorem fermionBaseOp_comm_pairCreation :
    fermionBaseOp * pairCreation = pairCreation * fermionBaseOp := by
  ext ψ i
  fin_cases i <;>
    simp [Module.End.mul_apply, fermionBaseOp_apply, pairCreation, creationOne_apply,
      creationTwo_apply]

/-- Witten–Möbius parity base operator on `Fin 8 → ℂ`. -/
def wmBaseOp (c s u₁ u₂ u₃ v₁ v₂ v₃ : ℂ) : Module.End ℂ (Fin 8 → ℂ) :=
  zornLeftOp (wittenMoebiusOperator c s u₁ u₂ u₃ v₁ v₂ v₃)

/-- Symplectic Zorn grading involution `K_0` on `Fin 8 → ℂ`. -/
def k0BaseOp : Module.End ℂ (Fin 8 → ℂ) :=
  zornLeftOp (paraSymplecticK0 (R := ℂ))

theorem k0BaseOp_sq : k0BaseOp * k0BaseOp = 1 := by
  apply zornLeftOp_sq_one_of_mulZ_sq
  refine ZornCell.ext_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (dsimp [ZornCell.mulZ, paraSymplecticK0, oneZ]; ring)

theorem wmBaseOp_sq (c s u₁ u₂ u₃ v₁ v₂ v₃ : ℂ)
    (h_trig : c ^ 2 + s ^ 2 = 1) (h_epr : u₁ * v₁ + u₂ * v₂ + u₃ * v₃ = -1) :
    wmBaseOp c s u₁ u₂ u₃ v₁ v₂ v₃ * wmBaseOp c s u₁ u₂ u₃ v₁ v₂ v₃ = 1 := by
  unfold wmBaseOp
  exact wmZornLeftOp_sq c s u₁ u₂ u₃ v₁ v₂ v₃ h_trig h_epr

/-- Canonical EPR Witten–Möbius involution (`c = 3/5, s = 4/5, u = (1,0,0), v = (-1,0,0)`). -/
def canonicalWMBaseOp : Module.End ℂ (Fin 8 → ℂ) :=
  wmBaseOp (3 / 5) (4 / 5) 1 0 0 (-1) 0 0

theorem canonicalWMBaseOp_sq : canonicalWMBaseOp * canonicalWMBaseOp = 1 := by
  unfold canonicalWMBaseOp
  apply wmBaseOp_sq <;> norm_num

/-- `[k0BaseOp, canonicalWMBaseOp] ≠ 0` obstruction in the Zorn sector: `K₀` does not commute
with the rotated Witten–Möbius parity (`s = 4/5 ≠ 0`), measuring Klein-bottle sheet twisting. -/
theorem k0BaseOp_canonicalWMBaseOp_noncomm :
    k0BaseOp * canonicalWMBaseOp ≠ canonicalWMBaseOp * k0BaseOp := by
  intro heq
  have hv := congrArg (fun op => op (zornToVec (sheetU (1 : ℂ) 0 0)) 1) heq
  simp only [k0BaseOp, canonicalWMBaseOp, wmBaseOp, Module.End.mul_apply, zornLeftOp,
    LinearMap.coe_mk, AddHom.coe_mk, zornToVec, vecToZorn, ZornCell.mulZ,
    paraSymplecticK0, wittenMoebiusOperator, subZ, smulZ, sheetU, sheetV] at hv
  norm_num at hv

/-- Lifted four-parity operators on `FourParityCarrier`. -/
def piOp : Module.End ℂ FourParityCarrier := liftSector1 piBaseOp
def fermionOp : Module.End ℂ FourParityCarrier := liftSector2 fermionBaseOp
def wmOp : Module.End ℂ FourParityCarrier := liftSector3 canonicalWMBaseOp
def k0Op : Module.End ℂ FourParityCarrier := liftSector3 k0BaseOp
def chitureOp : Module.End ℂ FourParityCarrier := liftSector4 chpChitureOp
def mengParityOp : Module.End ℂ FourParityCarrier := liftSector4 chpIntrinsicParityOp
def chiplexOp : Module.End ℂ FourParityCarrier := liftSector4 chpChiplexOp

theorem piOp_sq : piOp * piOp = 1 := by
  unfold piOp; rw [← liftSector1_mul, piBaseOp_sq, liftSector1_one]

theorem fermionOp_sq : fermionOp * fermionOp = 1 := by
  unfold fermionOp; rw [← liftSector2_mul, fermionBaseOp_sq, liftSector2_one]

theorem wmOp_sq : wmOp * wmOp = 1 := by
  unfold wmOp; rw [← liftSector3_mul, canonicalWMBaseOp_sq, liftSector3_one]

theorem k0Op_sq : k0Op * k0Op = 1 := by
  unfold k0Op; rw [← liftSector3_mul, k0BaseOp_sq, liftSector3_one]

theorem chitureOp_sq : chitureOp * chitureOp = 1 := by
  unfold chitureOp
  rw [← liftSector4_mul, chpChitureOp_sq, liftSector4_one]

theorem mengParityOp_sq : mengParityOp * mengParityOp = 1 := by
  unfold mengParityOp
  rw [← liftSector4_mul, chpIntrinsicParityOp_sq, liftSector4_one]

theorem chiplexOp_sq : chiplexOp * chiplexOp = 1 := by
  unfold chiplexOp
  rw [← liftSector4_mul, chpChiplexOp_sq, liftSector4_one]

private def baseEig1 (b : Bool) : Fin 2 → ℂ :=
  if b then Pi.single 0 1 else Pi.single 1 1

private theorem piBaseOp_eig (b : Bool) :
    piBaseOp (baseEig1 b) = (if b then (1 : ℂ) else -1) • baseEig1 b := by
  cases b <;> ext i <;> fin_cases i <;> simp [baseEig1, piBaseOp]

private def baseEig2 (b : Bool) : Fock4 :=
  if b then Pi.single 0 1 else Pi.single 1 1

private theorem fermionBaseOp_eig (b : Bool) :
    fermionBaseOp (baseEig2 b) = (if b then (1 : ℂ) else -1) • baseEig2 b := by
  cases b <;> ext i <;> fin_cases i <;> simp [baseEig2, fermionBaseOp_apply]

private def baseEig3 (b : Bool) : Fin 8 → ℂ :=
  if b then ![4 / 5, 0, 0, 0, 0, -2 / 5, 0, 0] else ![2 / 5, 0, 0, 0, 0, 4 / 5, 0, 0]

private theorem canonicalWMBaseOp_eig (b : Bool) :
    canonicalWMBaseOp (baseEig3 b) = (if b then (1 : ℂ) else -1) • baseEig3 b := by
  cases b <;> ext i <;> fin_cases i <;>
    (simp [canonicalWMBaseOp, wmBaseOp, zornLeftOp, baseEig3, zornToVec, vecToZorn,
      ZornCell.mulZ, wittenMoebiusOperator, subZ, smulZ, paraSymplecticK0, sheetU, sheetV];
     try norm_num)

private def baseEig4 (b : Bool) : ChpCarrierSpace :=
  if b then Pi.single (0, 0) 1 else Pi.single (0, 1) 1

private theorem mengParityBase_eig (b : Bool) :
    chpIntrinsicParityOp (baseEig4 b) = (if b then (1 : ℂ) else -1) • baseEig4 b := by
  cases b <;> ext ⟨c, p⟩ <;> fin_cases c <;> fin_cases p <;>
    simp [baseEig4, chpIntrinsicParityOp]

private def productState (v₁ : Fin 2 → ℂ) (v₂ : Fock4) (v₃ : Fin 8 → ℂ)
    (v₄ : ChpCarrierSpace) : FourParityCarrier :=
  fun x => v₁ x.1 * v₂ x.2.1 * v₃ x.2.2.1 * v₄ x.2.2.2

private def jointState (b : Fin 4 → Bool) : FourParityCarrier :=
  productState (baseEig1 (b 0)) (baseEig2 (b 1)) (baseEig3 (b 2)) (baseEig4 (b 3))

private theorem productState_ne_zero_of_coords
    {v₁ : Fin 2 → ℂ} {v₂ : Fock4} {v₃ : Fin 8 → ℂ} {v₄ : ChpCarrierSpace}
    {a : Fin 2} {j : Fin 4} {c : Fin 8} {d : Fin 2 × Fin 2}
    (ha : v₁ a ≠ 0) (hj : v₂ j ≠ 0) (hc : v₃ c ≠ 0) (hd : v₄ d ≠ 0) :
    productState v₁ v₂ v₃ v₄ ≠ 0 := by
  intro hz
  have hval := congrArg (fun f => f (a, j, c, d)) hz
  dsimp [productState] at hval
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha hj) hc) hd hval

private theorem jointState_ne_zero (b : Fin 4 → Bool) : jointState b ≠ 0 := by
  unfold jointState
  have h1 : baseEig1 (b 0) (if b 0 then 0 else 1) ≠ 0 := by cases b 0 <;> simp [baseEig1]
  have h2 : baseEig2 (b 1) (if b 1 then 0 else 1) ≠ 0 := by cases b 1 <;> simp [baseEig2]
  have h3 : baseEig3 (b 2) 0 ≠ 0 := by cases b 2 <;> (simp [baseEig3]; try norm_num)
  have h4 : baseEig4 (b 3) (if b 3 then (0, 0) else (0, 1)) ≠ 0 := by cases b 3 <;> simp [baseEig4]
  exact productState_ne_zero_of_coords h1 h2 h3 h4

private theorem liftSector1_productState (op : Module.End ℂ (Fin 2 → ℂ))
    (v₁ : Fin 2 → ℂ) (v₂ : Fock4) (v₃ : Fin 8 → ℂ) (v₄ : ChpCarrierSpace)
    (lam : ℂ) (heig : op v₁ = lam • v₁) :
    liftSector1 op (productState v₁ v₂ v₃ v₄) = lam • productState v₁ v₂ v₃ v₄ := by
  ext ⟨a, j, c, d⟩
  have hfn : (fun a' => productState v₁ v₂ v₃ v₄ (a', j, c, d)) = (v₂ j * v₃ c * v₄ d) • v₁ := by
    ext a'; simp [productState, smul_eq_mul]; ring
  change op (fun a' => productState v₁ v₂ v₃ v₄ (a', j, c, d)) a = _
  rw [hfn, map_smul, heig, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  dsimp [productState]; ring

private theorem liftSector2_productState (op : Module.End ℂ Fock4)
    (v₁ : Fin 2 → ℂ) (v₂ : Fock4) (v₃ : Fin 8 → ℂ) (v₄ : ChpCarrierSpace)
    (lam : ℂ) (heig : op v₂ = lam • v₂) :
    liftSector2 op (productState v₁ v₂ v₃ v₄) = lam • productState v₁ v₂ v₃ v₄ := by
  ext ⟨a, j, c, d⟩
  have hfn : (fun j' => productState v₁ v₂ v₃ v₄ (a, j', c, d)) = (v₁ a * v₃ c * v₄ d) • v₂ := by
    ext j'; simp [productState, smul_eq_mul]; ring
  change op (fun j' => productState v₁ v₂ v₃ v₄ (a, j', c, d)) j = _
  rw [hfn, map_smul, heig, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  dsimp [productState]; ring

private theorem liftSector3_productState (op : Module.End ℂ (Fin 8 → ℂ))
    (v₁ : Fin 2 → ℂ) (v₂ : Fock4) (v₃ : Fin 8 → ℂ) (v₄ : ChpCarrierSpace)
    (lam : ℂ) (heig : op v₃ = lam • v₃) :
    liftSector3 op (productState v₁ v₂ v₃ v₄) = lam • productState v₁ v₂ v₃ v₄ := by
  ext ⟨a, j, c, d⟩
  have hfn : (fun c' => productState v₁ v₂ v₃ v₄ (a, j, c', d)) = (v₁ a * v₂ j * v₄ d) • v₃ := by
    ext c'; simp [productState, smul_eq_mul]; ring
  change op (fun c' => productState v₁ v₂ v₃ v₄ (a, j, c', d)) c = _
  rw [hfn, map_smul, heig, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  dsimp [productState]; ring

private theorem liftSector4_productState (op : Module.End ℂ ChpCarrierSpace)
    (v₁ : Fin 2 → ℂ) (v₂ : Fock4) (v₃ : Fin 8 → ℂ) (v₄ : ChpCarrierSpace)
    (lam : ℂ) (heig : op v₄ = lam • v₄) :
    liftSector4 op (productState v₁ v₂ v₃ v₄) = lam • productState v₁ v₂ v₃ v₄ := by
  ext ⟨a, j, c, d⟩
  have hfn : (fun d' => productState v₁ v₂ v₃ v₄ (a, j, c, d')) = (v₁ a * v₂ j * v₃ c) • v₄ := by
    ext d'; simp [productState, smul_eq_mul]
  change op (fun d' => productState v₁ v₂ v₃ v₄ (a, j, c, d')) d = _
  rw [hfn, map_smul, heig, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  dsimp [productState]; ring

private theorem liftSector1_jointState (op : Module.End ℂ (Fin 2 → ℂ)) (b : Fin 4 → Bool)
    (lam : ℂ) (heig : op (baseEig1 (b 0)) = lam • baseEig1 (b 0)) :
    liftSector1 op (jointState b) = lam • jointState b := by
  unfold jointState
  exact liftSector1_productState op (baseEig1 (b 0)) (baseEig2 (b 1)) (baseEig3 (b 2)) (baseEig4 (b 3)) lam heig

private theorem liftSector2_jointState (op : Module.End ℂ (Fin 4 → ℂ)) (b : Fin 4 → Bool)
    (lam : ℂ) (heig : op (baseEig2 (b 1)) = lam • baseEig2 (b 1)) :
    liftSector2 op (jointState b) = lam • jointState b := by
  unfold jointState
  exact liftSector2_productState op (baseEig1 (b 0)) (baseEig2 (b 1)) (baseEig3 (b 2)) (baseEig4 (b 3)) lam heig

private theorem liftSector3_jointState (op : Module.End ℂ (Fin 8 → ℂ)) (b : Fin 4 → Bool)
    (lam : ℂ) (heig : op (baseEig3 (b 2)) = lam • baseEig3 (b 2)) :
    liftSector3 op (jointState b) = lam • jointState b := by
  unfold jointState
  exact liftSector3_productState op (baseEig1 (b 0)) (baseEig2 (b 1)) (baseEig3 (b 2)) (baseEig4 (b 3)) lam heig

private theorem liftSector4_jointState (op : Module.End ℂ ChpCarrierSpace) (b : Fin 4 → Bool)
    (lam : ℂ) (heig : op (baseEig4 (b 3)) = lam • baseEig4 (b 3)) :
    liftSector4 op (jointState b) = lam • jointState b := by
  unfold jointState
  exact liftSector4_productState op (baseEig1 (b 0)) (baseEig2 (b 1)) (baseEig3 (b 2)) (baseEig4 (b 3)) lam heig

/-- Sixteen commuting joint spectral projectors on `FourParityCarrier`, splitting
`piOp × fermionOp × wmOp × mengParityOp` into all 16 eigensectors. -/
def fourParityProjector (b : Fin 4 → Bool) : Module.End ℂ FourParityCarrier :=
  involutionProjector (K := ℂ) piOp (b 0) *
  involutionProjector (K := ℂ) fermionOp (b 1) *
  involutionProjector (K := ℂ) wmOp (b 2) *
  involutionProjector (K := ℂ) mengParityOp (b 3)

theorem fourParityProjector_eq_sector_prod (b : Fin 4 → Bool) :
    fourParityProjector b =
      liftSector1 (involutionProjector (K := ℂ) piBaseOp (b 0)) *
      liftSector2 (involutionProjector (K := ℂ) fermionBaseOp (b 1)) *
      liftSector3 (involutionProjector (K := ℂ) canonicalWMBaseOp (b 2)) *
      liftSector4 (involutionProjector (K := ℂ) chpIntrinsicParityOp (b 3)) := by
  have h1 : involutionProjector (K := ℂ) piOp (b 0) =
      liftSector1 (involutionProjector (K := ℂ) piBaseOp (b 0)) := by
    ext ψ ⟨a, j, c, d⟩
    unfold involutionProjector piOp liftSector1
    cases b 0 <;> (simp; try ring)
  have h2 : involutionProjector (K := ℂ) fermionOp (b 1) =
      liftSector2 (involutionProjector (K := ℂ) fermionBaseOp (b 1)) := by
    ext ψ ⟨a, j, c, d⟩
    unfold involutionProjector fermionOp liftSector2
    cases b 1 <;> (simp; try ring)
  have h3 : involutionProjector (K := ℂ) wmOp (b 2) =
      liftSector3 (involutionProjector (K := ℂ) canonicalWMBaseOp (b 2)) := by
    ext ψ ⟨a, j, c, d⟩
    unfold involutionProjector wmOp liftSector3
    cases b 2 <;> (simp; try ring)
  have h4 : involutionProjector (K := ℂ) mengParityOp (b 3) =
      liftSector4 (involutionProjector (K := ℂ) chpIntrinsicParityOp (b 3)) := by
    ext ψ ⟨a, j, c, d⟩
    unfold involutionProjector mengParityOp liftSector4
    cases b 3 <;> (simp; try ring)
  rw [fourParityProjector, h1, h2, h3, h4]

private theorem liftSector_quad_mul
    (f₁ g₁ : Module.End ℂ (Fin 2 → ℂ)) (f₂ g₂ : Module.End ℂ (Fin 4 → ℂ))
    (f₃ g₃ : Module.End ℂ (Fin 8 → ℂ)) (f₄ g₄ : Module.End ℂ ChpCarrierSpace) :
    (liftSector1 f₁ * liftSector2 f₂ * liftSector3 f₃ * liftSector4 f₄) *
    (liftSector1 g₁ * liftSector2 g₂ * liftSector3 g₃ * liftSector4 g₄) =
      liftSector1 (f₁ * g₁) * liftSector2 (f₂ * g₂) *
      liftSector3 (f₃ * g₃) * liftSector4 (f₄ * g₄) := by
  have c12 := fun u v => liftSector_1_2_comm u v
  have c13 := fun u v => liftSector_1_3_comm u v
  have c14 := fun u v => liftSector_1_4_comm u v
  have c23 := fun u v => liftSector_2_3_comm u v
  have c24 := fun u v => liftSector_2_4_comm u v
  have c34 := fun u v => liftSector_3_4_comm u v
  calc
    (liftSector1 f₁ * liftSector2 f₂ * liftSector3 f₃ * liftSector4 f₄) *
        (liftSector1 g₁ * liftSector2 g₂ * liftSector3 g₃ * liftSector4 g₄) =
        ((liftSector1 f₁ * liftSector2 f₂ * liftSector3 f₃) * (liftSector4 f₄ * liftSector1 g₁)) *
          (liftSector2 g₂ * liftSector3 g₃ * liftSector4 g₄) := by simp only [mul_assoc]
    _ = ((liftSector1 f₁ * liftSector2 f₂) * (liftSector3 f₃ * liftSector1 g₁)) *
          liftSector4 f₄ * (liftSector2 g₂ * liftSector3 g₃ * liftSector4 g₄) := by
          rw [(c14 g₁ f₄).symm]; simp only [mul_assoc]
    _ = (liftSector1 f₁ * (liftSector2 f₂ * liftSector1 g₁)) *
          liftSector3 f₃ * liftSector4 f₄ * (liftSector2 g₂ * liftSector3 g₃ * liftSector4 g₄) := by
          rw [(c13 g₁ f₃).symm]; simp only [mul_assoc]
    _ = liftSector1 (f₁ * g₁) *
          ((liftSector2 f₂ * liftSector3 f₃) * (liftSector4 f₄ * liftSector2 g₂) *
            (liftSector3 g₃ * liftSector4 g₄)) := by
          rw [(c12 g₁ f₂).symm, liftSector1_mul]; simp only [mul_assoc]
    _ = liftSector1 (f₁ * g₁) *
          ((liftSector2 f₂ * (liftSector3 f₃ * liftSector2 g₂) * liftSector4 f₄) *
            (liftSector3 g₃ * liftSector4 g₄)) := by
          rw [(c24 g₂ f₄).symm]; simp only [mul_assoc]
    _ = liftSector1 (f₁ * g₁) * liftSector2 (f₂ * g₂) *
          (liftSector3 f₃ * (liftSector4 f₄ * liftSector3 g₃) * liftSector4 g₄) := by
          rw [(c23 g₂ f₃).symm, liftSector2_mul]; simp only [mul_assoc]
    _ = liftSector1 (f₁ * g₁) * liftSector2 (f₂ * g₂) *
          liftSector3 (f₃ * g₃) * liftSector4 (f₄ * g₄) := by
          rw [(c34 g₃ f₄).symm, liftSector3_mul, liftSector4_mul]; simp only [mul_assoc]

theorem fourParityProjector_idem (b : Fin 4 → Bool) :
    fourParityProjector b * fourParityProjector b = fourParityProjector b := by
  rw [fourParityProjector_eq_sector_prod, liftSector_quad_mul,
    involutionProjector_idem piBaseOp piBaseOp_sq,
    involutionProjector_idem fermionBaseOp fermionBaseOp_sq,
    involutionProjector_idem canonicalWMBaseOp canonicalWMBaseOp_sq,
    involutionProjector_idem chpIntrinsicParityOp chpIntrinsicParityOp_sq]

theorem fourParityProjector_mul_ne (b b' : Fin 4 → Bool) (h : b ≠ b') :
    fourParityProjector b * fourParityProjector b' = 0 := by
  rw [fourParityProjector_eq_sector_prod, fourParityProjector_eq_sector_prod, liftSector_quad_mul]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have hls10 : liftSector1 (0 : Module.End ℂ (Fin 2 → ℂ)) = 0 := by ext; rfl
  have hls20 : liftSector2 (0 : Module.End ℂ Fock4) = 0 := by ext; rfl
  have hls30 : liftSector3 (0 : Module.End ℂ (Fin 8 → ℂ)) = 0 := by ext; rfl
  have hls40 : liftSector4 (0 : Module.End ℂ ChpCarrierSpace) = 0 := by ext; rfl
  fin_cases i
  · rw [involutionProjector_orth piBaseOp piBaseOp_sq (b 0) (b' 0) hi, hls10, zero_mul, zero_mul,
      zero_mul]
  · rw [involutionProjector_orth fermionBaseOp fermionBaseOp_sq (b 1) (b' 1) hi, hls20, mul_zero,
      zero_mul, zero_mul]
  · rw [involutionProjector_orth canonicalWMBaseOp canonicalWMBaseOp_sq (b 2) (b' 2) hi, hls30,
      mul_zero, zero_mul]
  · rw [involutionProjector_orth chpIntrinsicParityOp chpIntrinsicParityOp_sq (b 3) (b' 3) hi, hls40,
      mul_zero]

theorem fourParityProjector_ne_zero (b : Fin 4 → Bool) : fourParityProjector b ≠ 0 := by
  intro hz
  have hact := congrArg (fun op => op (jointState b)) hz
  rw [LinearMap.zero_apply] at hact
  have hp1 : involutionProjector (K := ℂ) piOp (b 0) (jointState b) = jointState b := by
    unfold involutionProjector
    rw [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      piOp, liftSector1_jointState piBaseOp b _ (piBaseOp_eig (b 0))]
    cases b 0 <;> simp <;> module
  have hp2 : involutionProjector (K := ℂ) fermionOp (b 1) (jointState b) = jointState b := by
    unfold involutionProjector
    rw [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      fermionOp, liftSector2_jointState fermionBaseOp b _ (fermionBaseOp_eig (b 1))]
    cases b 1 <;> simp <;> module
  have hp3 : involutionProjector (K := ℂ) wmOp (b 2) (jointState b) = jointState b := by
    unfold involutionProjector
    rw [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      wmOp, liftSector3_jointState canonicalWMBaseOp b _ (canonicalWMBaseOp_eig (b 2))]
    cases b 2 <;> simp <;> module
  have hp4 : involutionProjector (K := ℂ) mengParityOp (b 3) (jointState b) = jointState b := by
    unfold involutionProjector
    rw [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
      mengParityOp, liftSector4_jointState chpIntrinsicParityOp b _ (mengParityBase_eig (b 3))]
    cases b 3 <;> simp <;> module
  have hfull : fourParityProjector b (jointState b) = jointState b := by
    unfold fourParityProjector
    simp only [Module.End.mul_apply, hp4, hp3, hp2, hp1]
  rw [hfull] at hact
  exact jointState_ne_zero b hact

theorem fourParityProjector_sum_eq_one :
    (∑ b : Fin 4 → Bool, fourParityProjector b) = 1 := by
  have hp1 : involutionProjector (K := ℂ) piOp true +
      involutionProjector (K := ℂ) piOp false = 1 := involutionProjector_add piOp
  have hp2 : involutionProjector (K := ℂ) fermionOp true +
      involutionProjector (K := ℂ) fermionOp false = 1 := involutionProjector_add fermionOp
  have hp3 : involutionProjector (K := ℂ) wmOp true +
      involutionProjector (K := ℂ) wmOp false = 1 := involutionProjector_add wmOp
  have hp4 : involutionProjector (K := ℂ) mengParityOp true +
      involutionProjector (K := ℂ) mengParityOp false = 1 := involutionProjector_add mengParityOp
  have hexpand :
      (∑ b : Fin 4 → Bool, fourParityProjector b) =
        (involutionProjector (K := ℂ) piOp true + involutionProjector (K := ℂ) piOp false) *
        (involutionProjector (K := ℂ) fermionOp true + involutionProjector (K := ℂ) fermionOp false) *
        (involutionProjector (K := ℂ) wmOp true + involutionProjector (K := ℂ) wmOp false) *
        (involutionProjector (K := ℂ) mengParityOp true + involutionProjector (K := ℂ) mengParityOp false) := by
    have hsplit : ∀ (f : (Fin 4 → Bool) → Module.End ℂ FourParityCarrier),
        (∑ b : Fin 4 → Bool, f b) =
          ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool, ∑ b3 : Bool,
            f ![b0, b1, b2, b3] := by
      intro f
      let e : (Bool × Bool × Bool × Bool) ≃ (Fin 4 → Bool) :=
        { toFun := fun ⟨b0, b1, b2, b3⟩ => ![b0, b1, b2, b3]
          invFun := fun b => (b 0, b 1, b 2, b 3)
          left_inv := fun ⟨b0, b1, b2, b3⟩ => rfl
          right_inv := fun b => by ext i; fin_cases i <;> rfl }
      rw [← Fintype.sum_equiv e (fun q => f (e q)) f (fun _ => rfl)]
      simp only [e, Equiv.coe_fn_mk, Fintype.sum_prod_type]
    rw [hsplit]
    simp only [Fintype.sum_bool, fourParityProjector, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
      add_mul, mul_add]
    abel
  rw [hexpand, hp1, hp2, hp3, hp4, one_mul, one_mul, one_mul]

private def chitureAnti0 : ChpCarrierSpace :=
  Pi.single (0, 0) (1 : ℂ) - Pi.single (1, 0) (1 : ℂ)

private def chitureSym1 : ChpCarrierSpace :=
  Pi.single (0, 1) (1 : ℂ) + Pi.single (1, 1) (1 : ℂ)

private theorem chitureAnti0_eig_chiture :
    chpChitureOp chitureAnti0 = (-1 : ℂ) • chitureAnti0 := by
  ext ⟨c, p⟩
  fin_cases c <;> fin_cases p <;>
    simp [chitureAnti0, chpChitureOp, MengChPSelectionRules.chiture,
      chpRotationOp, chpExchangeOp, chpIntrinsicParityOp, Module.End.mul_apply]

private theorem chitureAnti0_eig_parity :
    chpIntrinsicParityOp chitureAnti0 = (1 : ℂ) • chitureAnti0 := by
  ext ⟨c, p⟩
  fin_cases c <;> fin_cases p <;>
    simp [chitureAnti0, chpIntrinsicParityOp]

private theorem chitureAnti0_eig_chiplex :
    chpChiplexOp chitureAnti0 = (-1 : ℂ) • chitureAnti0 := by
  change (chpChitureOp * chpIntrinsicParityOp) chitureAnti0 = _
  rw [Module.End.mul_apply, chitureAnti0_eig_parity, one_smul, chitureAnti0_eig_chiture]

private theorem chitureSym1_eig_chiture :
    chpChitureOp chitureSym1 = (1 : ℂ) • chitureSym1 := by
  ext ⟨c, p⟩
  fin_cases c <;> fin_cases p <;>
    simp [chitureSym1, chpChitureOp, MengChPSelectionRules.chiture,
      chpRotationOp, chpExchangeOp, chpIntrinsicParityOp, Module.End.mul_apply]

private theorem chitureSym1_eig_chiplex :
    chpChiplexOp chitureSym1 = (-1 : ℂ) • chitureSym1 := by
  have hp : chpIntrinsicParityOp chitureSym1 = (-1 : ℂ) • chitureSym1 := by
    ext ⟨c, p⟩
    fin_cases c <;> fin_cases p <;> simp [chitureSym1, chpIntrinsicParityOp]
  change (chpChitureOp * chpIntrinsicParityOp) chitureSym1 = _
  rw [Module.End.mul_apply, hp, map_smul, chitureSym1_eig_chiture, one_smul]

private theorem neg_productState_ne {ψ : FourParityCarrier} (hψ : ψ ≠ 0) : -ψ ≠ ψ := by
  intro heq
  apply hψ
  have h2 : (2 : ℂ) • ψ = 0 := by
    rw [two_smul]
    calc
      ψ + ψ = (-ψ) + ψ := by rw [heq]
      _ = 0 := neg_add_cancel _
  have hs := congrArg (fun x => (1 / 2 : ℂ) • x) h2
  rw [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul, smul_zero] at hs
  exact hs

/-- Universal concrete four-parity separation & compatibility theorem on `FourParityCarrier`:
1. all four parities (`piOp`, `fermionOp`, `wmOp`, `mengParityOp`, `chitureOp`, `chiplexOp`)
   are involutions (`^2 = 1`);
2. cross-sector parities commute pairwise;
3. intra-sector ChP commutator `chitureOp * mengParityOp = chiplexOp` holds while
   `k0Op` and `wmOp` exhibit noncommutativity `[k0Op, wmOp] ≠ 0`;
4. EVERY pair among distinct physical parities is strictly unequal (`≠`);
5. all 16 joint spectral projectors `fourParityProjector b` are nonzero, idempotent, and sum to `1`. -/
private theorem piOp_eig_joint (b : Fin 4 → Bool) :
    piOp (jointState b) = (if b 0 then (1 : ℂ) else -1) • jointState b := by
  unfold piOp
  exact liftSector1_jointState piBaseOp b _ (piBaseOp_eig (b 0))

private theorem fermionOp_eig_joint (b : Fin 4 → Bool) :
    fermionOp (jointState b) = (if b 1 then (1 : ℂ) else -1) • jointState b := by
  unfold fermionOp
  exact liftSector2_jointState fermionBaseOp b _ (fermionBaseOp_eig (b 1))

private theorem wmOp_eig_joint (b : Fin 4 → Bool) :
    wmOp (jointState b) = (if b 2 then (1 : ℂ) else -1) • jointState b := by
  unfold wmOp
  exact liftSector3_jointState canonicalWMBaseOp b _ (canonicalWMBaseOp_eig (b 2))

private theorem mengParityOp_eig_joint (b : Fin 4 → Bool) :
    mengParityOp (jointState b) = (if b 3 then (1 : ℂ) else -1) • jointState b := by
  unfold mengParityOp
  exact liftSector4_jointState chpIntrinsicParityOp b _ (mengParityBase_eig (b 3))

theorem four_parity_separation_and_compatibility :
    (piOp * piOp = 1 ∧ fermionOp * fermionOp = 1 ∧ wmOp * wmOp = 1 ∧
     k0Op * k0Op = 1 ∧ chitureOp * chitureOp = 1 ∧
     mengParityOp * mengParityOp = 1 ∧ chiplexOp * chiplexOp = 1) ∧
    (piOp * fermionOp = fermionOp * piOp ∧ piOp * wmOp = wmOp * piOp ∧
     piOp * mengParityOp = mengParityOp * piOp ∧ fermionOp * wmOp = wmOp * fermionOp ∧
     fermionOp * mengParityOp = mengParityOp * fermionOp ∧
     wmOp * mengParityOp = mengParityOp * wmOp ∧
     chitureOp * mengParityOp = chiplexOp) ∧
    (k0Op * wmOp ≠ wmOp * k0Op ∧
     piOp ≠ fermionOp ∧ piOp ≠ wmOp ∧ piOp ≠ mengParityOp ∧
     piOp ≠ chitureOp ∧ piOp ≠ chiplexOp ∧
     fermionOp ≠ wmOp ∧ fermionOp ≠ mengParityOp ∧
     fermionOp ≠ chitureOp ∧ fermionOp ≠ chiplexOp ∧
     wmOp ≠ mengParityOp ∧ wmOp ≠ chitureOp ∧ wmOp ≠ chiplexOp ∧
     mengParityOp ≠ chitureOp ∧ mengParityOp ≠ chiplexOp ∧ chitureOp ≠ chiplexOp) ∧
    (∀ b : Fin 4 → Bool, fourParityProjector b ≠ 0) := by
  have hk0_ne_wm : k0Op * wmOp ≠ wmOp * k0Op := by
    intro heq
    let ψ : FourParityCarrier := fun x => zornToVec (sheetU (1 : ℂ) 0 0) x.2.2.1
    have hact := congrArg (fun op => op ψ (0, 0, 1, (0, 0))) heq
    have hf : (fun c => ψ (0, 0, c, (0, 0))) = zornToVec (sheetU (1 : ℂ) 0 0) := rfl
    simp only [k0Op, wmOp, Module.End.mul_apply, liftSector3, LinearMap.coe_mk, AddHom.coe_mk] at hact
    have hact' : (k0BaseOp * canonicalWMBaseOp) (zornToVec (sheetU (1 : ℂ) 0 0)) 1 =
        (canonicalWMBaseOp * k0BaseOp) (zornToVec (sheetU (1 : ℂ) 0 0)) 1 := by
      simpa [Module.End.mul_apply, hf] using hact
    simp only [k0BaseOp, canonicalWMBaseOp, wmBaseOp, Module.End.mul_apply, zornLeftOp,
      LinearMap.coe_mk, AddHom.coe_mk, zornToVec, vecToZorn, ZornCell.mulZ,
      paraSymplecticK0, wittenMoebiusOperator, subZ, smulZ, sheetU, sheetV] at hact'
    norm_num at hact'
  have hpi_ne_ferm : piOp ≠ fermionOp := by
    intro h
    have hv := congrArg (fun op => op (jointState ![true, false, true, true])) h
    rw [piOp_eig_joint, fermionOp_eig_joint] at hv
    simp at hv
    exact neg_productState_ne (jointState_ne_zero ![true, false, true, true]) hv.symm
  have hpi_ne_wm : piOp ≠ wmOp := by
    intro h
    have hv := congrArg (fun op => op (jointState ![true, true, false, true])) h
    rw [piOp_eig_joint, wmOp_eig_joint] at hv
    simp at hv
    exact neg_productState_ne (jointState_ne_zero ![true, true, false, true]) hv.symm
  have hpi_ne_meng : piOp ≠ mengParityOp := by
    intro h
    have hv := congrArg (fun op => op (jointState ![true, true, true, false])) h
    rw [piOp_eig_joint, mengParityOp_eig_joint] at hv
    simp at hv
    exact neg_productState_ne (jointState_ne_zero ![true, true, true, false]) hv.symm
  have hferm_ne_wm : fermionOp ≠ wmOp := by
    intro h
    have hv := congrArg (fun op => op (jointState ![true, true, false, true])) h
    rw [fermionOp_eig_joint, wmOp_eig_joint] at hv
    simp at hv
    exact neg_productState_ne (jointState_ne_zero ![true, true, false, true]) hv.symm
  have hferm_ne_meng : fermionOp ≠ mengParityOp := by
    intro h
    have hv := congrArg (fun op => op (jointState ![true, true, true, false])) h
    rw [fermionOp_eig_joint, mengParityOp_eig_joint] at hv
    simp at hv
    exact neg_productState_ne (jointState_ne_zero ![true, true, true, false]) hv.symm
  have hwm_ne_meng : wmOp ≠ mengParityOp := by
    intro h
    have hv := congrArg (fun op => op (jointState ![true, true, true, false])) h
    rw [wmOp_eig_joint, mengParityOp_eig_joint] at hv
    simp at hv
    exact neg_productState_ne (jointState_ne_zero ![true, true, true, false]) hv.symm
  have hca_ne : productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureAnti0 ≠ 0 := by
    apply productState_ne_zero_of_coords (a := 0) (j := 0) (c := 0) (d := (0, 0))
    · simp [baseEig1]
    · simp [baseEig2]
    · simp [baseEig3]; try norm_num
    · simp [chitureAnti0]
  have hcs1_ne : productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureSym1 ≠ 0 := by
    apply productState_ne_zero_of_coords (a := 0) (j := 0) (c := 0) (d := (0, 1))
    · simp [baseEig1]
    · simp [baseEig2]
    · simp [baseEig3]; try norm_num
    · simp [chitureSym1]
  have hp1 : piBaseOp (baseEig1 true) = (1 : ℂ) • baseEig1 true := by simpa using piBaseOp_eig true
  have hp2 : fermionBaseOp (baseEig2 true) = (1 : ℂ) • baseEig2 true := by simpa using fermionBaseOp_eig true
  have hp3 : canonicalWMBaseOp (baseEig3 true) = (1 : ℂ) • baseEig3 true := by simpa using canonicalWMBaseOp_eig true
  have hpi_ne_ch : piOp ≠ chitureOp := by
    intro h
    have hv := congrArg (fun op => op (productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureAnti0)) h
    rw [piOp, liftSector1_productState piBaseOp _ _ _ _ 1 hp1,
      chitureOp, liftSector4_productState chpChitureOp _ _ _ _ (-1) chitureAnti0_eig_chiture,
      one_smul, neg_one_smul] at hv
    exact neg_productState_ne hca_ne hv.symm
  have hpi_ne_cpx : piOp ≠ chiplexOp := by
    intro h
    have hv := congrArg (fun op => op (productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureAnti0)) h
    rw [piOp, liftSector1_productState piBaseOp _ _ _ _ 1 hp1,
      chiplexOp, liftSector4_productState chpChiplexOp _ _ _ _ (-1) chitureAnti0_eig_chiplex,
      one_smul, neg_one_smul] at hv
    exact neg_productState_ne hca_ne hv.symm
  have hferm_ne_ch : fermionOp ≠ chitureOp := by
    intro h
    have hv := congrArg (fun op => op (productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureAnti0)) h
    rw [fermionOp, liftSector2_productState fermionBaseOp _ _ _ _ 1 hp2,
      chitureOp, liftSector4_productState chpChitureOp _ _ _ _ (-1) chitureAnti0_eig_chiture,
      one_smul, neg_one_smul] at hv
    exact neg_productState_ne hca_ne hv.symm
  have hferm_ne_cpx : fermionOp ≠ chiplexOp := by
    intro h
    have hv := congrArg (fun op => op (productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureAnti0)) h
    rw [fermionOp, liftSector2_productState fermionBaseOp _ _ _ _ 1 hp2,
      chiplexOp, liftSector4_productState chpChiplexOp _ _ _ _ (-1) chitureAnti0_eig_chiplex,
      one_smul, neg_one_smul] at hv
    exact neg_productState_ne hca_ne hv.symm
  have hwm_ne_ch : wmOp ≠ chitureOp := by
    intro h
    have hv := congrArg (fun op => op (productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureAnti0)) h
    rw [wmOp, liftSector3_productState canonicalWMBaseOp _ _ _ _ 1 hp3,
      chitureOp, liftSector4_productState chpChitureOp _ _ _ _ (-1) chitureAnti0_eig_chiture,
      one_smul, neg_one_smul] at hv
    exact neg_productState_ne hca_ne hv.symm
  have hwm_ne_cpx : wmOp ≠ chiplexOp := by
    intro h
    have hv := congrArg (fun op => op (productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureAnti0)) h
    rw [wmOp, liftSector3_productState canonicalWMBaseOp _ _ _ _ 1 hp3,
      chiplexOp, liftSector4_productState chpChiplexOp _ _ _ _ (-1) chitureAnti0_eig_chiplex,
      one_smul, neg_one_smul] at hv
    exact neg_productState_ne hca_ne hv.symm
  have hmeng_ne_ch : mengParityOp ≠ chitureOp := by
    intro h
    have hv := congrArg (fun op => op (productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureAnti0)) h
    rw [mengParityOp, liftSector4_productState chpIntrinsicParityOp _ _ _ _ 1 chitureAnti0_eig_parity,
      chitureOp, liftSector4_productState chpChitureOp _ _ _ _ (-1) chitureAnti0_eig_chiture,
      one_smul, neg_one_smul] at hv
    exact neg_productState_ne hca_ne hv.symm
  have hmeng_ne_cpx : mengParityOp ≠ chiplexOp := by
    intro h
    have hv := congrArg (fun op => op (productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureAnti0)) h
    rw [mengParityOp, liftSector4_productState chpIntrinsicParityOp _ _ _ _ 1 chitureAnti0_eig_parity,
      chiplexOp, liftSector4_productState chpChiplexOp _ _ _ _ (-1) chitureAnti0_eig_chiplex,
      one_smul, neg_one_smul] at hv
    exact neg_productState_ne hca_ne hv.symm
  have hch_ne_cpx : chitureOp ≠ chiplexOp := by
    intro h
    have hv := congrArg (fun op => op (productState (baseEig1 true) (baseEig2 true) (baseEig3 true) chitureSym1)) h
    rw [chitureOp, liftSector4_productState chpChitureOp _ _ _ _ 1 chitureSym1_eig_chiture,
      chiplexOp, liftSector4_productState chpChiplexOp _ _ _ _ (-1) chitureSym1_eig_chiplex,
      one_smul, neg_one_smul] at hv
    exact neg_productState_ne hcs1_ne hv.symm
  refine ⟨⟨piOp_sq, fermionOp_sq, wmOp_sq, k0Op_sq, chitureOp_sq, mengParityOp_sq, chiplexOp_sq⟩,
    ⟨liftSector_1_2_comm _ _, liftSector_1_3_comm _ _, liftSector_1_4_comm _ _,
     liftSector_2_3_comm _ _, liftSector_2_4_comm _ _, liftSector_3_4_comm _ _, rfl⟩,
    ⟨hk0_ne_wm, hpi_ne_ferm, hpi_ne_wm, hpi_ne_meng, hpi_ne_ch, hpi_ne_cpx,
     hferm_ne_wm, hferm_ne_meng, hferm_ne_ch, hferm_ne_cpx,
     hwm_ne_meng, hwm_ne_ch, hwm_ne_cpx, hmeng_ne_ch, hmeng_ne_cpx, hch_ne_cpx⟩,
    fourParityProjector_ne_zero⟩

end ConcreteFourParityWitness

end InfoGeometry.Physics.NuclearInternalExternalParityFactorization

end noncomputable section
