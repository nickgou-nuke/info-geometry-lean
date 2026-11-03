/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorZornFourPotentialGauge
import InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator
import InfoGeometry.OperatorAlgebra.PeirceSpine.RingHomTransport
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.Physics.BdGChiralBlockMatrix

/-!
# Carrier Bridge from `OperatorZornFourPotentialGauge` to the Peirce Tetraktys

Over an arbitrary noncommutative associative coefficient ring `[Ring A]` (with no scalar
field and no commutativity hypothesis on `A`), this module constructs the explicit carrier
maps connecting the nonassociative Zorn gauge theory in
`InfoGeometry.Canonical.OperatorZornFourPotentialGauge` to the associative Peirce Tetraktys
`(conePlus, coneMinus, genPhi, genJ, genV, genSig)` in `Matrix (Fin 2) (Fin 2) A`.

## Main Definitions and Theorems

1. `peirceSheetProj`: The canonical upper-sheet idempotent `!![1, 0; 0, 0]` in
   `Matrix (Fin 2) (Fin 2) A`.
2. `zornChiralPlaneMatrix i X`: The `i`-th spatial chiral plane slice
   `!![X.n_plus, X.sigma_plus i; X.sigma_minus i, X.n_minus]` in `Matrix (Fin 2) (Fin 2) A`.
3. `zornChiralPlane_conePlus`, `zornChiralPlane_coneMinus`, `zornChiralPlane_genPhi`,
   `zornChiralPlane_genJ`, `zornChiralPlane_genV`, `zornChiralPlane_genSig`:
   Explicit matrix evaluations showing that the Peirce Tetraktys generators of
   `zornChiralPlaneMatrix i X` and `zornChiralPlaneMatrix i Y` carry the exact ordered
   operator products `X.sigma_plus i * Y.sigma_minus i` and `Y.sigma_minus i * X.sigma_plus i`.
4. `sum_zornChiralPlane_genV`: Summing the Peirce scale operator `genV` over the three
   spatial axes `i : Fin 3` produces the diagonal operator matrix
   `!![zornDot X.sigma_plus Y.sigma_minus, 0; 0, zornDot Y.sigma_minus X.sigma_plus]`.
5. `zornMul_diagonal_from_peirce_genV`, `zornBracket_diagonal_from_peirce_genV`, and
   `fieldStrength_diagonal_from_peirce_genV`: Exact decomposition of the upper and lower
   sheet components of the Zorn product `X * Y`, Zorn commutator `bracket X Y`, and
   nonassociative gauge curvature `fieldStrength p Phi mu nu` in terms of coefficient
   commutators and the Peirce Tetraktys scale operator `genV`.
6. `zornChiralPlane_zero_mul_defect`: Exact formula for the difference between the
   slice of the Zorn product `zornChiralPlaneMatrix 0 (X * Y)` and the `2 × 2` matrix
   product `zornChiralPlaneMatrix 0 X * zornChiralPlaneMatrix 0 Y`, isolating the
   transverse chiral dot terms and the octonionic `zornCross` terms.
7. `fourPotential_chiralPlane_tetraktys_and_double_commutator`: For any four-potential
   `Phi : FourPotential A`, indices `mu nu : Fin 4`, and spatial axis `i : Fin 3`, selected
   mass-weighted Tetraktys identities for `(zornChiralPlaneMatrix i (Phi mu),
   zornChiralPlaneMatrix i (Phi nu))` and `curvatureDoubleCommutator_quadratic_phi`.
   Since `genPhi ^ 2 = genV` and `genJ ^ 2 = -genV`, these are not a normalized `Cl(1,1)`
   representation absent an additional normalization hypothesis.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge

open InfoGeometry.Physics.NCG
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine
open scoped BigOperators Matrix

variable {A : Type*} [Ring A]

/-! ## 1. The Chiral-Plane Matrix Carrier Map and Sheet Idempotent -/

/-- The canonical upper-sheet Peirce idempotent `!![1, 0; 0, 0]` in `Matrix (Fin 2) (Fin 2) A`. -/
def peirceSheetProj : Matrix (Fin 2) (Fin 2) A :=
  !![(1 : A), 0; 0, 0]

/-- The `i`-th spatial chiral-plane `2 × 2` operator matrix extracted from an
`OperatorZornMatrix A` element `X`. -/
def zornChiralPlaneMatrix (i : Fin 3) (X : OperatorZornMatrix A) :
    Matrix (Fin 2) (Fin 2) A :=
  !![X.n_plus, X.sigma_plus i; X.sigma_minus i, X.n_minus]

theorem peirceSheetProj_idem :
    (peirceSheetProj : Matrix (Fin 2) (Fin 2) A) * peirceSheetProj = peirceSheetProj := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [peirceSheetProj, Matrix.mul_apply, Fin.sum_univ_two]

/-- The upper-corner raising matrix unit `!![0, 1; 0, 0]` in `Matrix (Fin 2) (Fin 2) A`. -/
def peirceRaisingUnit : Matrix (Fin 2) (Fin 2) A :=
  !![(0 : A), 1; 0, 0]

/-- Explicit non-commutativity witness in `Matrix (Fin 2) (Fin 2) A`: the sheet idempotent
`peirceSheetProj` and the off-diagonal raising unit `peirceRaisingUnit` do not commute over
any nontrivial coefficient ring `[Nontrivial A]`. -/
theorem peirceSheetProj_mul_peirceRaisingUnit_ne [Nontrivial A] :
    (peirceSheetProj : Matrix (Fin 2) (Fin 2) A) * peirceRaisingUnit ≠
      peirceRaisingUnit * peirceSheetProj := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 1) h
  simp [peirceSheetProj, peirceRaisingUnit, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-! ## 2. Explicit Peirce Tetraktys Evaluations on Chiral Planes -/

theorem zornChiralPlane_conePlus (i : Fin 3) (X : OperatorZornMatrix A) :
    conePlus (peirceSheetProj (A := A)) (zornChiralPlaneMatrix i X) =
      !![(0 : A), X.sigma_plus i; 0, 0] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [conePlus, peirceSheetProj, zornChiralPlaneMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem zornChiralPlane_coneMinus (i : Fin 3) (Y : OperatorZornMatrix A) :
    coneMinus (peirceSheetProj (A := A)) (zornChiralPlaneMatrix i Y) =
      !![(0 : A), 0; Y.sigma_minus i, 0] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [coneMinus, peirceSheetProj, zornChiralPlaneMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem zornChiralPlane_genPhi (i : Fin 3) (X Y : OperatorZornMatrix A) :
    genPhi (peirceSheetProj (A := A))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i Y) =
      !![(0 : A), X.sigma_plus i; Y.sigma_minus i, 0] := by
  rw [genPhi, zornChiralPlane_conePlus, zornChiralPlane_coneMinus]
  ext r s
  fin_cases r <;> fin_cases s <;> simp

theorem zornChiralPlane_genJ (i : Fin 3) (X Y : OperatorZornMatrix A) :
    genJ (peirceSheetProj (A := A))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i Y) =
      !![(0 : A), X.sigma_plus i; -Y.sigma_minus i, 0] := by
  rw [genJ, zornChiralPlane_conePlus, zornChiralPlane_coneMinus]
  ext r s
  fin_cases r <;> fin_cases s <;> simp

theorem zornChiralPlane_genV (i : Fin 3) (X Y : OperatorZornMatrix A) :
    genV (peirceSheetProj (A := A))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i Y) =
      !![X.sigma_plus i * Y.sigma_minus i, 0;
         0, Y.sigma_minus i * X.sigma_plus i] := by
  rw [genV, anticomm, zornChiralPlane_conePlus, zornChiralPlane_coneMinus]
  ext r s
  fin_cases r <;> fin_cases s <;> simp

theorem zornChiralPlane_genSig (i : Fin 3) (X Y : OperatorZornMatrix A) :
    genSig (peirceSheetProj (A := A))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i Y) =
      !![X.sigma_plus i * Y.sigma_minus i, 0;
         0, -(Y.sigma_minus i * X.sigma_plus i)] := by
  rw [genSig, PeirceSpine.comm, zornChiralPlane_conePlus, zornChiralPlane_coneMinus]
  ext r s
  fin_cases r <;> fin_cases s <;> simp

/-! ## 3. Spatial Summation of `genV` and Bridge to `OperatorZornFourPotentialGauge` -/

/-- Summing the Peirce scale operator `genV` across all three spatial planes reproduces
the ordered chiral dot contractions `zornDot X.sigma_plus Y.sigma_minus` and
`zornDot Y.sigma_minus X.sigma_plus` on the two sheets. -/
theorem sum_zornChiralPlane_genV (X Y : OperatorZornMatrix A) :
    (∑ i : Fin 3,
      genV (peirceSheetProj (A := A))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i Y)) =
      !![NCZornElement.zornDot X.sigma_plus Y.sigma_minus, 0;
         0, NCZornElement.zornDot Y.sigma_minus X.sigma_plus] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Fin.sum_univ_three, zornChiralPlane_genV, NCZornElement.zornDot, add_assoc]

/-- The diagonal sheet entries of the nonassociative Zorn product `X * Y` are given by
the sheet product plus the spatial trace of the Peirce Tetraktys scale operator `genV`. -/
theorem zornMul_diagonal_from_peirce_genV (X Y : OperatorZornMatrix A) :
    (X * Y).n_plus =
      X.n_plus * Y.n_plus +
        (∑ i : Fin 3,
          genV (peirceSheetProj (A := A))
            (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i Y) 0 0) ∧
    (X * Y).n_minus =
      X.n_minus * Y.n_minus +
        (∑ i : Fin 3,
          genV (peirceSheetProj (A := A))
            (zornChiralPlaneMatrix i Y) (zornChiralPlaneMatrix i X) 1 1) := by
  constructor
  · simp [Fin.sum_univ_three, zornChiralPlane_genV, NCZornElement.zornDot, add_assoc]
  · simp [Fin.sum_univ_three, zornChiralPlane_genV, NCZornElement.zornDot, add_assoc]

/-- The diagonal sheet entries of the Zorn commutator `bracket X Y` are governed by the
antisymmetrized Peirce scale operator `genV`. -/
theorem zornBracket_diagonal_from_peirce_genV (X Y : OperatorZornMatrix A) :
    (bracket X Y).n_plus =
      coefficientBracket X.n_plus Y.n_plus +
        ∑ i : Fin 3,
          (genV (peirceSheetProj (A := A))
              (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i Y) 0 0 -
            genV (peirceSheetProj (A := A))
              (zornChiralPlaneMatrix i Y) (zornChiralPlaneMatrix i X) 0 0) ∧
    (bracket X Y).n_minus =
      coefficientBracket X.n_minus Y.n_minus +
        ∑ i : Fin 3,
          (genV (peirceSheetProj (A := A))
              (zornChiralPlaneMatrix i Y) (zornChiralPlaneMatrix i X) 1 1 -
            genV (peirceSheetProj (A := A))
              (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i Y) 1 1) := by
  constructor
  · simp [bracket, coefficientBracket, Fin.sum_univ_three,
      zornChiralPlane_genV, NCZornElement.zornDot]
    abel
  · simp [bracket, coefficientBracket, Fin.sum_univ_three,
      zornChiralPlane_genV, NCZornElement.zornDot]
    abel

/-- Exact decomposition of the upper and lower sheet components of the nonassociative
gauge curvature `fieldStrength p Phi mu nu` into background operator commutators,
diagonal sheet commutators, and the Peirce Tetraktys scale operator `genV`. -/
theorem fieldStrength_diagonal_from_peirce_genV
    (p : Fin 4 → A) (Phi : FourPotential A) (mu nu : Fin 4) :
    (fieldStrength p Phi mu nu).n_plus =
      coefficientBracket (p mu) (Phi nu).n_plus -
        coefficientBracket (p nu) (Phi mu).n_plus +
        coefficientBracket (Phi mu).n_plus (Phi nu).n_plus +
        ∑ i : Fin 3,
          (genV (peirceSheetProj (A := A))
              (zornChiralPlaneMatrix i (Phi mu)) (zornChiralPlaneMatrix i (Phi nu)) 0 0 -
            genV (peirceSheetProj (A := A))
              (zornChiralPlaneMatrix i (Phi nu)) (zornChiralPlaneMatrix i (Phi mu)) 0 0) ∧
    (fieldStrength p Phi mu nu).n_minus =
      coefficientBracket (p mu) (Phi nu).n_minus -
        coefficientBracket (p nu) (Phi mu).n_minus +
        coefficientBracket (Phi mu).n_minus (Phi nu).n_minus +
        ∑ i : Fin 3,
          (genV (peirceSheetProj (A := A))
              (zornChiralPlaneMatrix i (Phi nu)) (zornChiralPlaneMatrix i (Phi mu)) 1 1 -
            genV (peirceSheetProj (A := A))
              (zornChiralPlaneMatrix i (Phi mu)) (zornChiralPlaneMatrix i (Phi nu)) 1 1) := by
  rcases zornBracket_diagonal_from_peirce_genV (Phi mu) (Phi nu) with ⟨hPlus, hMinus⟩
  constructor
  · change (coefficientDeriv (p mu) (Phi nu) - coefficientDeriv (p nu) (Phi mu)).n_plus +
        (bracket (Phi mu) (Phi nu)).n_plus = _
    rw [hPlus]
    simp only [zornSub_nPlus, coefficientDeriv_nPlus, add_assoc]
  · change (coefficientDeriv (p mu) (Phi nu) - coefficientDeriv (p nu) (Phi mu)).n_minus +
        (bracket (Phi mu) (Phi nu)).n_minus = _
    rw [hMinus]
    simp only [zornSub_nMinus, coefficientDeriv_nMinus, add_assoc]

/-- On the `0`-th spatial chiral plane, the difference between the slice of the Zorn product
`zornChiralPlaneMatrix 0 (X * Y)` and the associative `2 × 2` matrix product
`zornChiralPlaneMatrix 0 X * zornChiralPlaneMatrix 0 Y` consists precisely of the transverse
Peirce scale operators (`i = 1, 2`) on the diagonal and the octonionic cross-product terms
`∓ zornCross` on the off-diagonal. -/
theorem zornChiralPlane_zero_mul_defect (X Y : OperatorZornMatrix A) :
    zornChiralPlaneMatrix 0 (X * Y) -
      zornChiralPlaneMatrix 0 X * zornChiralPlaneMatrix 0 Y =
      !![genV (peirceSheetProj (A := A))
            (zornChiralPlaneMatrix 1 X) (zornChiralPlaneMatrix 1 Y) 0 0 +
          genV (peirceSheetProj (A := A))
            (zornChiralPlaneMatrix 2 X) (zornChiralPlaneMatrix 2 Y) 0 0,
         -NCZornElement.zornCross X.sigma_minus Y.sigma_minus 0;
         NCZornElement.zornCross X.sigma_plus Y.sigma_plus 0,
         genV (peirceSheetProj (A := A))
            (zornChiralPlaneMatrix 1 Y) (zornChiralPlaneMatrix 1 X) 1 1 +
          genV (peirceSheetProj (A := A))
            (zornChiralPlaneMatrix 2 Y) (zornChiralPlaneMatrix 2 X) 1 1] := by
  rw [zornChiralPlane_genV, zornChiralPlane_genV, zornChiralPlane_genV, zornChiralPlane_genV]
  ext r s
  fin_cases r <;> fin_cases s
  · simp [zornChiralPlaneMatrix, NCZornElement.zornDot]; abel
  · simp [zornChiralPlaneMatrix, NCZornElement.zornDot]
  · simp [zornChiralPlaneMatrix, NCZornElement.zornDot]; abel
  · simp [zornChiralPlaneMatrix, NCZornElement.zornDot]; abel

/-! ## 4. Full Peirce Tetraktys and Double-Commutator Identities for `FourPotential A` -/

/-- Every spatial chiral plane `i : Fin 3` of a nonassociative Zorn four-potential
`Phi : FourPotential A` satisfies the selected mass-weighted Peirce Tetraktys identities
(`N_+² = N_-² = 0`, `Phi² = +V`, `J² = -V`, `Sigma² = V²`, `J Phi = Sigma`), the quadratic
curvature double-commutator identity `curvatureDoubleCommutator_quadratic_phi`, and the exact
curvature-action associator formula `curvatureAction_eq`. These identities do not assert a
normalized `Cl(1,1)` representation. -/
theorem fourPotential_chiralPlane_tetraktys_and_double_commutator
    (p : Fin 4 → A) (Phi : FourPotential A) (mu nu : Fin 4) (i : Fin 3)
    (X : OperatorZornMatrix A) :
    let P := peirceSheetProj (A := A)
    let Mmu := zornChiralPlaneMatrix i (Phi mu)
    let Mnu := zornChiralPlaneMatrix i (Phi nu)
    conePlus P Mmu * conePlus P Mmu = 0 ∧
    coneMinus P Mnu * coneMinus P Mnu = 0 ∧
    genPhi P Mmu Mnu * genPhi P Mmu Mnu = genV P Mmu Mnu ∧
    genJ P Mmu Mnu * genJ P Mmu Mnu = -genV P Mmu Mnu ∧
    genSig P Mmu Mnu * genSig P Mmu Mnu = genV P Mmu Mnu * genV P Mmu Mnu ∧
    genJ P Mmu Mnu * genPhi P Mmu Mnu = genSig P Mmu Mnu ∧
    curvatureDoubleCommutator P Mmu Mnu
        (curvatureDoubleCommutator P Mmu Mnu (genPhi P Mmu Mnu)) +
      (4 : ℤ) • (genV P Mmu Mnu * curvatureDoubleCommutator P Mmu Mnu (genPhi P Mmu Mnu)) -
      (4 : ℤ) • ((genV P Mmu Mnu * genV P Mmu Mnu) * genPhi P Mmu Mnu) = 0 ∧
    curvatureAction p Phi mu nu X =
      coefficientDeriv (coefficientBracket (p mu) (p nu)) X +
        fieldStrength p Phi mu nu * X -
          associator (Phi mu) (Phi nu) X + associator (Phi nu) (Phi mu) X := by
  dsimp only
  have hP := peirceSheetProj_idem (A := A)
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table hP
    (zornChiralPlaneMatrix i (Phi mu)) (zornChiralPlaneMatrix i (Phi nu)) with
    ⟨hNp, hNm, hPhi2, hJ2, _, hJPhi, _⟩
  have hSig2 :
      genSig (peirceSheetProj (A := A))
          (zornChiralPlaneMatrix i (Phi mu)) (zornChiralPlaneMatrix i (Phi nu)) *
        genSig (peirceSheetProj (A := A))
          (zornChiralPlaneMatrix i (Phi mu)) (zornChiralPlaneMatrix i (Phi nu)) =
      genV (peirceSheetProj (A := A))
          (zornChiralPlaneMatrix i (Phi mu)) (zornChiralPlaneMatrix i (Phi nu)) *
        genV (peirceSheetProj (A := A))
          (zornChiralPlaneMatrix i (Phi mu)) (zornChiralPlaneMatrix i (Phi nu)) := by
    peirce_nf hP
  exact ⟨hNp, hNm, hPhi2, hJ2, hSig2, hJPhi,
    curvatureDoubleCommutator_quadratic_phi hP
      (zornChiralPlaneMatrix i (Phi mu)) (zornChiralPlaneMatrix i (Phi nu)),
    curvatureAction_eq p Phi mu nu X⟩

/-! ## 5. Non-Commutative Peirce–BdG Massive Hamiltonian & Zorn–Dirac Intertwining

Over any associative ring `[Ring B]`, we define the general non-commutative Peirce–BdG massive
operator `peirceBdGHamiltonian P D A C := evenGrade P D * invS P + genPhi P A C`, prove its
universal non-commutative square `evenGrade P D * evenGrade P D + genV P A C + comm (evenGrade P D) (genJ P A C)`
(without assuming `D` commutes with `A` or `C`), prove its homomorphism transport and `StarRing`
quadratic decomposition, and identify its `Matrix (Fin 2) (Fin 2) A` realizations with
`zornChiralPlaneMatrix`, `massiveBdGHamiltonian`, `diracOperator`, and `diracSquare`. -/

section PeirceBdG

variable {B C_ring : Type*} [Ring B] [Ring C_ring]

/-- **Definition (`peirceBdGHamiltonian`)**:
The general non-commutative Peirce–BdG massive operator
`evenGrade P D * invS P + genPhi P A C = (P * D * P - (1 - P) * D * (1 - P)) + (conePlus P A + coneMinus P C)`. -/
def peirceBdGHamiltonian (P D A C : B) : B :=
  evenGrade P D * invS P + genPhi P A C

/-- Every ring homomorphism `f : B →+* C_ring` intertwines `evenGrade`, `oddGrade`, and
`peirceBdGHamiltonian`. -/
theorem map_peirceBdGHamiltonian (f : B →+* C_ring) (P D A C : B) :
    f (evenGrade P D) = evenGrade (f P) (f D) ∧
    f (oddGrade P D) = oddGrade (f P) (f D) ∧
    f (peirceBdGHamiltonian P D A C) = peirceBdGHamiltonian (f P) (f D) (f A) (f C) := by
  have hEven : f (evenGrade P D) = evenGrade (f P) (f D) := by
    unfold evenGrade
    simp only [map_add, map_sub, map_mul, map_one]
  have hOdd : f (oddGrade P D) = oddGrade (f P) (f D) := by
    unfold oddGrade
    simp only [map_add, map_sub, map_mul, map_one]
  refine ⟨hEven, hOdd, ?_⟩
  unfold peirceBdGHamiltonian
  rw [map_add, map_mul, hEven, map_invS, map_genPhi]

/-- **Lemma (`peirceBdGHamiltonian_grading_relations`)**:
For any idempotent `P` (`P * P = P`) and any `D, A, C : B`:
1. `evenGrade P (peirceBdGHamiltonian P D A C) = evenGrade P D * invS P`;
2. `oddGrade P (peirceBdGHamiltonian P D A C) = genPhi P A C`;
3. `anticomm (peirceBdGHamiltonian P D A C) (invS P) = (2 : ℤ) • evenGrade P D`;
4. `PeirceSpine.comm (peirceBdGHamiltonian P D A C) (invS P) = -(2 : ℤ) • genJ P A C`. -/
theorem peirceBdGHamiltonian_grading_relations {P : B} (hP : P * P = P) (D A C : B) :
    evenGrade P (peirceBdGHamiltonian P D A C) = evenGrade P D * invS P ∧
    oddGrade P (peirceBdGHamiltonian P D A C) = genPhi P A C ∧
    anticomm (peirceBdGHamiltonian P D A C) (invS P) = (2 : ℤ) • evenGrade P D ∧
    PeirceSpine.comm (peirceBdGHamiltonian P D A C) (invS P) = -(2 : ℤ) • genJ P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirceBdGHamiltonian]; peirce_nf hP)

/-- **Theorem (`peirceBdGHamiltonian_sq`)**:
For any idempotent `P` (`P * P = P`) and any `D, A, C : B` (with zero commutativity assumptions),
the square of `peirceBdGHamiltonian P D A C` decomposes into the even-grade mass square
`evenGrade P D * evenGrade P D`, the Peirce horizon operator `genV P A C`, and the odd-grade
commutator obstruction `PeirceSpine.comm (evenGrade P D) (genJ P A C)`:
`peirceBdGHamiltonian P D A C * peirceBdGHamiltonian P D A C =
  evenGrade P D * evenGrade P D + genV P A C + PeirceSpine.comm (evenGrade P D) (genJ P A C)`. -/
theorem peirceBdGHamiltonian_sq {P : B} (hP : P * P = P) (D A C : B) :
    peirceBdGHamiltonian P D A C * peirceBdGHamiltonian P D A C =
      evenGrade P D * evenGrade P D + genV P A C +
        PeirceSpine.comm (evenGrade P D) (genJ P A C) := by
  simp only [peirceBdGHamiltonian]
  peirce_nf hP

/-- **Corollary (`peirceBdGHamiltonian_sq_of_comm_genJ`)**:
When `evenGrade P D` commutes with the chiral generator `genJ P A C`
(`PeirceSpine.comm (evenGrade P D) (genJ P A C) = 0`), the off-diagonal interference vanishes and
`peirceBdGHamiltonian P D A C * peirceBdGHamiltonian P D A C = evenGrade P D * evenGrade P D + genV P A C`. -/
theorem peirceBdGHamiltonian_sq_of_comm_genJ {P : B} (hP : P * P = P) (D A C : B)
    (hComm : PeirceSpine.comm (evenGrade P D) (genJ P A C) = 0) :
    peirceBdGHamiltonian P D A C * peirceBdGHamiltonian P D A C =
      evenGrade P D * evenGrade P D + genV P A C := by
  rw [peirceBdGHamiltonian_sq hP D A C, hComm, add_zero]

/-- **Theorem (`peirceBdGHamiltonian_selfAdjoint_and_quadratic_form`)**:
In any `[Ring B] [StarRing B]`, if `P * P = P`, `star P = P`, and `star D = D`:
1. `star (evenGrade P D) = evenGrade P D` and
   `star (peirceBdGHamiltonian P D A (star A)) = peirceBdGHamiltonian P D A (star A)`;
2. The horizon quadratic form factors into non-negative Gram squares:
   `star X * genV P A (star A) * X =
     star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) +
     star (conePlus P A * X) * (conePlus P A * X)`;
3. When `PeirceSpine.comm (evenGrade P D) (genJ P A (star A)) = 0`, the massive BdG squared
   quadratic form splits into the sum of the mass Gram square and the horizon quadratic form:
   `star X * (peirceBdGHamiltonian P D A (star A) * peirceBdGHamiltonian P D A (star A)) * X =
     star (evenGrade P D * X) * (evenGrade P D * X) + star X * genV P A (star A) * X`. -/
theorem peirceBdGHamiltonian_selfAdjoint_and_quadratic_form
    [StarRing B] {P D : B} (hP : P * P = P) (hPs : star P = P) (hDs : star D = D)
    (A X : B) (hComm : PeirceSpine.comm (evenGrade P D) (genJ P A (star A)) = 0) :
    star (evenGrade P D) = evenGrade P D ∧
    star (peirceBdGHamiltonian P D A (star A)) = peirceBdGHamiltonian P D A (star A) ∧
    star X * genV P A (star A) * X =
      star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) +
        star (conePlus P A * X) * (conePlus P A * X) ∧
    star X * (peirceBdGHamiltonian P D A (star A) * peirceBdGHamiltonian P D A (star A)) * X =
      star (evenGrade P D * X) * (evenGrade P D * X) +
        star X * genV P A (star A) * X := by
  have hStarOneSub : star (1 - P) = 1 - P := by
    rw [star_sub, star_one, hPs]
  have hStarEven : star (evenGrade P D) = evenGrade P D := by
    unfold evenGrade
    simp only [star_add, star_mul, hPs, hDs, hStarOneSub, mul_assoc]
  have hEvenCommS : evenGrade P D * invS P = invS P * evenGrade P D := by
    peirce_nf hP
  have hStarBdG : star (peirceBdGHamiltonian P D A (star A)) = peirceBdGHamiltonian P D A (star A) := by
    unfold peirceBdGHamiltonian
    rw [star_add, star_mul, star_invS hPs, hStarEven, ← hEvenCommS, star_genPhi hPs A]
  have hGramV :
      star X * genV P A (star A) * X =
        star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) +
          star (conePlus P A * X) * (conePlus P A * X) := by
    unfold genV anticomm
    rw [star_mul, star_mul, star_coneMinus hPs (star A), star_star, star_conePlus hPs A]
    noncomm_ring
  have hQuad :
      star X * (peirceBdGHamiltonian P D A (star A) * peirceBdGHamiltonian P D A (star A)) * X =
        star (evenGrade P D * X) * (evenGrade P D * X) +
          star X * genV P A (star A) * X := by
    rw [peirceBdGHamiltonian_sq_of_comm_genJ hP D A (star A) hComm, star_mul, hStarEven]
    noncomm_ring
  exact ⟨hStarEven, hStarBdG, hGramV, hQuad⟩

end PeirceBdG

section MatrixAndZornBdGRealization

theorem one_sub_peirceSheetProj :
    (1 : Matrix (Fin 2) (Fin 2) A) - peirceSheetProj = !![(0 : A), 0; 0, 1] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [peirceSheetProj]

/-- The Peirce grading involution `invS (peirceSheetProj (A := A))` on `Matrix (Fin 2) (Fin 2) A`
is identically `InfoGeometry.Physics.chiralGrading = !![1, 0; 0, -1]`. -/
theorem invS_peirceSheetProj_eq_chiralGrading :
    invS (peirceSheetProj (A := A)) = InfoGeometry.Physics.chiralGrading := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [invS, peirceSheetProj, InfoGeometry.Physics.chiralGrading]

/-- Every spatial chiral plane `zornChiralPlaneMatrix i X` of an `OperatorZornMatrix A` is an
instance of `peirceBdGHamiltonian` with diagonal sheet operator `!![X.n_plus, 0; 0, -X.n_minus]`. -/
theorem zornChiralPlaneMatrix_eq_peirceBdGHamiltonian
    (i : Fin 3) (X : OperatorZornMatrix A) :
    zornChiralPlaneMatrix i X =
      peirceBdGHamiltonian (peirceSheetProj (A := A))
        !![X.n_plus, 0; 0, -X.n_minus]
        (zornChiralPlaneMatrix i X)
        (zornChiralPlaneMatrix i X) := by
  rw [peirceBdGHamiltonian, zornChiralPlane_genPhi, evenGrade,
    invS_peirceSheetProj_eq_chiralGrading, one_sub_peirceSheetProj]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [zornChiralPlaneMatrix, peirceSheetProj, InfoGeometry.Physics.chiralGrading]

/-- The mass-coupled BdG block Hamiltonian `massiveBdGHamiltonian D M = !![D, M; M, -D]` is the
exact `peirceBdGHamiltonian` of `D_diag = !![D, 0; 0, D]` and `M_off = !![0, M; M, 0]`, and its
general non-commutative square (without assuming `D * M = M * D`) separates into the diagonal
`!![D * D + M * M, 0; 0, M * M + D * D]` plus the off-diagonal Connes commutator differential
`connesDifferential !![D, 0; 0, D] !![0, M; -M, 0]`. -/
theorem massiveBdGHamiltonian_peirce_and_noncomm_sq [StarRing A] (D M : A) :
    InfoGeometry.Physics.massiveBdGHamiltonian D M =
      peirceBdGHamiltonian (peirceSheetProj (A := A))
        !![D, 0; 0, D] !![0, M; 0, 0] !![0, 0; M, 0] ∧
    InfoGeometry.Physics.massiveBdGHamiltonian D M *
        InfoGeometry.Physics.massiveBdGHamiltonian D M =
      !![D * D + M * M, D * M - M * D;
         M * D - D * M, M * M + D * D] ∧
    InfoGeometry.Physics.massiveBdGHamiltonian D M *
        InfoGeometry.Physics.massiveBdGHamiltonian D M =
      !![D * D + M * M, 0; 0, M * M + D * D] +
        InfoGeometry.Physics.connesDifferential !![D, 0; 0, D] !![0, M; -M, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [peirceBdGHamiltonian, evenGrade, invS_peirceSheetProj_eq_chiralGrading,
      genPhi, conePlus, coneMinus, one_sub_peirceSheetProj]
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [InfoGeometry.Physics.massiveBdGHamiltonian, peirceSheetProj,
        InfoGeometry.Physics.chiralGrading]
  · ext r s
    fin_cases r <;> fin_cases s <;>
      simp [InfoGeometry.Physics.massiveBdGHamiltonian, Matrix.mul_apply, Fin.sum_univ_two] <;>
      noncomm_ring
  · ext r s
    fin_cases r <;> fin_cases s <;>
      simp [InfoGeometry.Physics.massiveBdGHamiltonian, InfoGeometry.Physics.connesDifferential,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
      abel

/-- In any `[Ring A] [StarRing A]`, when an `OperatorZornMatrix A` element `X` satisfies the
Hermitian pairing relation `X.sigma_minus i = star (X.sigma_plus i)` on spatial axis `i : Fin 3`,
its Peirce Tetraktys chiral operator `genPhi` and horizon metric `genV` coincide with
`InfoGeometry.Physics.diracOperator (X.sigma_plus i)` and
`InfoGeometry.Physics.diracSquare (X.sigma_plus i)`. -/
theorem zornChiralPlane_genPhi_and_genV_eq_dirac [StarRing A]
    (i : Fin 3) (X : OperatorZornMatrix A)
    (hAdj : X.sigma_minus i = star (X.sigma_plus i)) :
    genPhi (peirceSheetProj (A := A))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X) =
      InfoGeometry.Physics.diracOperator (X.sigma_plus i) ∧
    genV (peirceSheetProj (A := A))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X) =
      InfoGeometry.Physics.diracSquare (X.sigma_plus i) := by
  refine ⟨?_, ?_⟩
  · rw [zornChiralPlane_genPhi, hAdj]
    rfl
  · rw [zornChiralPlane_genV, InfoGeometry.Physics.diracSquare_eq_diagonal, hAdj]

end MatrixAndZornBdGRealization

end InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
