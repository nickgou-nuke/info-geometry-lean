/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorZornFourPotentialGauge
import InfoGeometry.OperatorAlgebra.PeirceSpine.CurvatureDoubleCommutator

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

end InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
