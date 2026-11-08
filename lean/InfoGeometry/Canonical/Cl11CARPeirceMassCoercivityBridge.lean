/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.Clifford.Cl11MarkovJonesEngine
import InfoGeometry.Physics.BdGChiralBlockMatrix
import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

/-!
# CAR mass seed and Peirce–Hodge coercivity on the real UHF colimit

One finite Cl(5,5) Jordan–Wigner CAR mode supplies the self-adjoint Peirce
projection and unit Tetraktys mass used by the existing finite-to-colimit
coercivity theorem. The normalized matrix traces are descended through the
actual module direct limit, so the final inequality has no assumed trace map.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The occupied projection of one finite CAR mode in the native five-stage
real matrix Fock carrier. -/
def carMassProjection : Stage 5 := creation 0 * annihilation 0

/-- The self-adjoint Majorana combination of the same finite CAR mode. -/
def carMassOperator : Stage 5 := creation 0 + annihilation 0

/-- Coefficient extension of the finite CAR mass matrix to the complex matrix
operator carrier used by the finite-dimensional spectral theory. -/
def carMassOperatorComplex : Matrix
    (InfoGeometry.Clifford.TowerMatrix.Idx 5)
    (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ :=
  carMassOperator.map Complex.ofRealHom

/-- The complex Jordan Gram endomorphism of the coefficient-extended CAR
mass. -/
def carMassJordanGramComplex : Module.End ℂ
    (Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 5)
      (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ) :=
  InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℂ)
    (carMassOperatorComplex * star carMassOperatorComplex +
      star carMassOperatorComplex * carMassOperatorComplex)

private theorem carCreation_star : star (creation 0) = annihilation 0 := by
  simpa only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using creation_transpose 0

private theorem carAnnihilation_star : star (annihilation 0) = creation 0 := by
  rw [← carCreation_star, star_star]

/-- The one-mode CAR occupation is a self-adjoint idempotent. -/
theorem carMassProjection_structure :
    carMassProjection * carMassProjection = carMassProjection ∧
    star carMassProjection = carMassProjection := by
  have hc := creation_same_site_sq (0 : Fin 5)
  have ha := annihilation_same_site_sq (0 : Fin 5)
  have hca := creation_annihilation_same_site (0 : Fin 5)
  have hac : annihilation 0 * creation 0 = 1 - creation 0 * annihilation 0 := by
    rw [← hca]
    noncomm_ring
  constructor
  · change (creation 0 * annihilation 0) *
      (creation 0 * annihilation 0) = creation 0 * annihilation 0
    calc
      (creation 0 * annihilation 0) * (creation 0 * annihilation 0) =
          creation 0 * (annihilation 0 * creation 0) * annihilation 0 := by
            noncomm_ring
      _ = creation 0 * (1 - creation 0 * annihilation 0) * annihilation 0 := by
            rw [hac]
      _ = creation 0 * annihilation 0 := by
            noncomm_ring [hc, ha]
  · change star (creation 0 * annihilation 0) = creation 0 * annihilation 0
    rw [star_mul, carAnnihilation_star, carCreation_star]

/-- The Majorana sum is self-adjoint and its Peirce Tetraktys mass is the
identity, by the finite CAR anticommutator. -/
theorem carMassOperator_unit_horizon :
    star carMassOperator = carMassOperator ∧
    genV carMassProjection carMassOperator (star carMassOperator) = 1 := by
  have hc := creation_same_site_sq (0 : Fin 5)
  have ha := annihilation_same_site_sq (0 : Fin 5)
  have hca := creation_annihilation_same_site (0 : Fin 5)
  have hac : annihilation 0 * creation 0 = 1 - creation 0 * annihilation 0 := by
    rw [← hca]
    noncomm_ring
  have hcaUnit : creation 0 * annihilation 0 * creation 0 = creation 0 := by
    calc
      creation 0 * annihilation 0 * creation 0 =
          creation 0 * (annihilation 0 * creation 0) := by noncomm_ring
      _ = creation 0 * (1 - creation 0 * annihilation 0) := by rw [hac]
      _ = creation 0 := by
        rw [mul_sub, mul_one]
        have hzero : creation 0 * (creation 0 * annihilation 0) = 0 := by
          rw [← mul_assoc, hc, zero_mul]
        rw [hzero, sub_zero]
  have hacUnit : annihilation 0 * creation 0 * annihilation 0 = annihilation 0 := by
    have hac' : creation 0 * annihilation 0 = 1 - annihilation 0 * creation 0 := by
      rw [← hca]
      noncomm_ring
    calc
      annihilation 0 * creation 0 * annihilation 0 =
          annihilation 0 * (creation 0 * annihilation 0) := by noncomm_ring
      _ = annihilation 0 * (1 - annihilation 0 * creation 0) := by rw [hac']
      _ = annihilation 0 := by
        rw [mul_sub, mul_one]
        have hzero : annihilation 0 * (annihilation 0 * creation 0) = 0 := by
          rw [← mul_assoc, ha, zero_mul]
        rw [hzero, sub_zero]
  have hPA : (creation 0 * annihilation 0) *
      (creation 0 + annihilation 0) = creation 0 := by
    rw [mul_add]
    have hzero : creation 0 * annihilation 0 * annihilation 0 = 0 := by
      rw [mul_assoc, ha, mul_zero]
    rw [hcaUnit, hzero, add_zero]
  have hAP : (annihilation 0 * creation 0) *
      (creation 0 + annihilation 0) = annihilation 0 := by
    rw [mul_add]
    have hzero : annihilation 0 * creation 0 * creation 0 = 0 := by
      rw [mul_assoc, hc, mul_zero]
    rw [hzero, hacUnit, zero_add]
  have hccorner : conePlus carMassProjection carMassOperator = creation 0 := by
    change (creation 0 * annihilation 0) *
      (creation 0 + annihilation 0) * (1 - creation 0 * annihilation 0) = creation 0
    calc
      _ = creation 0 * annihilation 0 * creation 0 := by
        rw [hac.symm]
        rw [hPA]
        noncomm_ring
      _ = creation 0 := hcaUnit
  have hacorner : coneMinus carMassProjection carMassOperator = annihilation 0 := by
    change (1 - creation 0 * annihilation 0) *
      (creation 0 + annihilation 0) * (creation 0 * annihilation 0) = annihilation 0
    rw [hac.symm]
    calc
      (annihilation 0 * creation 0) * (creation 0 + annihilation 0) *
          (creation 0 * annihilation 0) =
          annihilation 0 * creation 0 * annihilation 0 := by
            rw [hAP]
            noncomm_ring
      _ = annihilation 0 := hacUnit
  have hAst : star carMassOperator = carMassOperator := by
    change star (creation 0 + annihilation 0) = creation 0 + annihilation 0
    rw [star_add, carCreation_star, carAnnihilation_star]
    exact add_comm _ _
  constructor
  · exact hAst
  · rw [hAst]
    change genV (creation 0 * annihilation 0)
      (creation 0 + annihilation 0) (creation 0 + annihilation 0) = 1
    change conePlus (creation 0 * annihilation 0) (creation 0 + annihilation 0) =
      creation 0 at hccorner
    change coneMinus (creation 0 * annihilation 0) (creation 0 + annihilation 0) =
      annihilation 0 at hacorner
    unfold genV anticomm
    change conePlus (creation 0 * annihilation 0) (creation 0 + annihilation 0) *
        coneMinus (creation 0 * annihilation 0) (creation 0 + annihilation 0) +
      coneMinus (creation 0 * annihilation 0) (creation 0 + annihilation 0) *
        conePlus (creation 0 * annihilation 0) (creation 0 + annihilation 0) = 1
    rw [show conePlus (creation 0 * annihilation 0) (creation 0 + annihilation 0) =
          creation 0 by exact hccorner,
        show coneMinus (creation 0 * annihilation 0) (creation 0 + annihilation 0) =
          annihilation 0 by exact hacorner]
    exact hca

/-- The self-adjoint CAR mass operator is an involution. This is the finite
operator identity underlying its two-sided inverse and unit mass scale. -/
theorem carMassOperator_square_eq_one : carMassOperator * carMassOperator = 1 := by
  have hc := creation_same_site_sq (0 : Fin 5)
  have ha := annihilation_same_site_sq (0 : Fin 5)
  have hca := creation_annihilation_same_site (0 : Fin 5)
  change (creation 0 + annihilation 0) * (creation 0 + annihilation 0) = 1
  calc
    (creation 0 + annihilation 0) * (creation 0 + annihilation 0) =
        creation 0 * annihilation 0 + annihilation 0 * creation 0 := by
          noncomm_ring [hc, ha]
    _ = 1 := hca

/-- Real coefficient extension preserves the self-adjointness of the CAR
Majorana mass. -/
theorem carMassOperatorComplex_selfAdjoint :
    star carMassOperatorComplex = carMassOperatorComplex := by
  have hrealStar : star carMassOperator = carMassOperator :=
    carMassOperator_unit_horizon.1
  apply Matrix.ext
  intro i j
  have hentry := congrArg (fun M : Stage 5 => M i j) hrealStar
  have hsymm : carMassOperator j i = carMassOperator i j := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      star_trivial] using hentry
  change starRingEnd ℂ (Complex.ofReal (carMassOperator j i)) =
    Complex.ofReal (carMassOperator i j)
  rw [Complex.conj_ofReal, hsymm]

/-- The complexified CAR Majorana remains an involution. -/
theorem carMassOperatorComplex_square :
    carMassOperatorComplex * carMassOperatorComplex = 1 := by
  change carMassOperator.map Complex.ofRealHom *
      carMassOperator.map Complex.ofRealHom = 1
  rw [← Matrix.map_mul, carMassOperator_square_eq_one]
  simp

/-- The CAR mass Gram is twice the identity matrix. -/
theorem carMassOperatorComplex_gram :
    carMassOperatorComplex * star carMassOperatorComplex +
      star carMassOperatorComplex * carMassOperatorComplex =
        (2 : ℂ) • (1 : Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 5)
          (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ) := by
  rw [carMassOperatorComplex_selfAdjoint, carMassOperatorComplex_square]
  exact (two_smul ℂ (1 : Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 5)
    (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ)).symm

/-- The coefficient-extended CAR Jordan Gram acts as `4 • id` on the whole
complex matrix algebra. -/
theorem carMassJordanGramComplex_apply (X : Matrix
    (InfoGeometry.Clifford.TowerMatrix.Idx 5)
    (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ) :
    carMassJordanGramComplex X = (4 : ℂ) • X := by
  change (carMassOperatorComplex * star carMassOperatorComplex +
      star carMassOperatorComplex * carMassOperatorComplex) * X +
      X * (carMassOperatorComplex * star carMassOperatorComplex +
        star carMassOperatorComplex * carMassOperatorComplex) = _
  rw [carMassOperatorComplex_gram]
  calc
    (2 : ℂ) • (1 : Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 5)
        (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ) * X +
        X * ((2 : ℂ) • (1 : Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 5)
          (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ)) =
        (2 : ℂ) • X + (2 : ℂ) • X := by
          simp [Algebra.smul_def, Algebra.commutes]
    _ = ((2 : ℂ) + 2) • X := by rw [← add_smul]
    _ = (4 : ℂ) • X := by norm_num

/-- Every eigenvalue of the finite complexified CAR Jordan Gram is exactly
`4`; this is the algebraic spectral gap of the concrete finite mass operator. -/
theorem carMassJordanGramComplex_eigenvalue_eq_four {μ : ℂ}
    (hμ : carMassJordanGramComplex.HasEigenvalue μ) : μ = 4 := by
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have hact := carMassJordanGramComplex_apply X
  have hscalar : ((4 : ℂ) - μ) • X = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (hact.symm.trans hX.apply_eq_smul)
  have hcoeff : (4 : ℂ) - μ = 0 :=
    (smul_eq_zero.mp hscalar).resolve_right hX.2
  exact (sub_eq_zero.mp hcoeff).symm

/-- The native algebraic spectrum of the finite complexified CAR Jordan Gram
is the singleton `{4}`. -/
theorem carMassJordanGramComplex_spectrum :
    spectrum ℂ carMassJordanGramComplex = {4} := by
  ext μ
  constructor
  · intro hμ
    have heig : carMassJordanGramComplex.HasEigenvalue μ :=
      (Module.End.HasEigenvalue.of_mem_spectrum hμ)
    have hfour := carMassJordanGramComplex_eigenvalue_eq_four heig
    exact Set.mem_singleton_iff.mpr hfour
  · intro hμ
    have hfour : μ = 4 := by simpa using hμ
    subst μ
    apply (Module.End.hasEigenvalue_iff_mem_spectrum).mp
    apply (Module.End.hasEigenvalue_iff).2
    have hone : (1 : Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 5)
        (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ) ∈
        carMassJordanGramComplex.eigenspace 4 := by
      rw [Module.End.mem_eigenspace_iff]
      exact carMassJordanGramComplex_apply _
    intro hbot
    have honeBot : (1 : Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 5)
        (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ) ∈
        (⊥ : Submodule ℂ (Matrix (InfoGeometry.Clifford.TowerMatrix.Idx 5)
          (InfoGeometry.Clifford.TowerMatrix.Idx 5) ℂ)) := by
      rw [← hbot]
      exact hone
    exact one_ne_zero ((Submodule.mem_bot ℂ).mp honeBot)

/-- At the finite CAR seed, the mass horizon generates the exact Jordan/Hodge
operator `2 • id` on the full noncommutative matrix algebra. This is the
operator-level spectral value underlying the normalized-trace coercivity
estimate; it is proved from the CAR anticommutator, not assumed as a gap. -/
theorem carMass_jordan_hodge_action_stage (x : Stage 5) :
    InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℝ)
        (genV carMassProjection carMassOperator (star carMassOperator)) x =
      (2 : ℝ) • x := by
  have hV := carMassOperator_unit_horizon.2
  change (genV carMassProjection carMassOperator (star carMassOperator)) * x +
      x * (genV carMassProjection carMassOperator (star carMassOperator)) = _
  rw [hV]
  simp only [one_mul, mul_one, two_smul]

/-- The same CAR-generated Jordan/Hodge operator is exactly `2 • id` after
the canonical stage-five map into the actual UHF colimit. Thus the finite
mass eigenvalue is preserved by the colimit map, alongside the separate
quadratic coercivity descent. -/
theorem carMass_jordan_hodge_action_limit (x : Limit) :
    InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℝ)
        (genV (ofStage 5 carMassProjection) (ofStage 5 carMassOperator)
          (star (ofStage 5 carMassOperator))) x = (2 : ℝ) • x := by
  have hV : genV (ofStage 5 carMassProjection) (ofStage 5 carMassOperator)
      (star (ofStage 5 carMassOperator)) = 1 := by
    rw [← ofStage_star]
    simpa only [map_genV, map_one] using
      congrArg (ofStage 5) carMassOperator_unit_horizon.2
  change (genV (ofStage 5 carMassProjection) (ofStage 5 carMassOperator)
      (star (ofStage 5 carMassOperator))) * x +
      x * (genV (ofStage 5 carMassProjection) (ofStage 5 carMassOperator)
        (star (ofStage 5 carMassOperator))) = _
  rw [hV]
  simp only [one_mul, mul_one, two_smul]

/-- The commutator anomaly in the finite CAR BdG square is precisely the
Peirce parity operator of the occupation projection used by the coercivity
seed. This identifies the interaction defect with the mass operator's
particle-hole grading in the same matrix carrier. -/
theorem carBdGSquare_offdiag_eq_massParity :
    (InfoGeometry.Physics.massiveBdGHamiltonian (creation 0) (annihilation 0) *
      InfoGeometry.Physics.massiveBdGHamiltonian (creation 0) (annihilation 0)) 0 1 =
      invS carMassProjection := by
  have hca := creation_annihilation_same_site (0 : Fin 5)
  have hParity : creation 0 * annihilation 0 - annihilation 0 * creation 0 =
      invS carMassProjection := by
    change creation 0 * annihilation 0 - annihilation 0 * creation 0 =
      (creation 0 * annihilation 0) - (1 - creation 0 * annihilation 0)
    rw [← hca]
    noncomm_ring
  rw [InfoGeometry.Physics.massiveBdGHamiltonian_sq_with_commutator]
  simpa [InfoGeometry.Physics.massiveBdGHamiltonian, Matrix.of_apply] using hParity

/-- Andreev-reflecting the CAR BdG interaction changes its off-diagonal
parity term to its negative, so the particle and hole contributions cancel. -/
theorem carBdGSquare_hole_reflection_cancels_massParity :
    let H : InfoGeometry.Physics.BdGBlock (Stage 5) :=
      InfoGeometry.Physics.massiveBdGHamiltonian (creation 0) (annihilation 0)
    let K : InfoGeometry.Physics.BdGBlock (Stage 5) :=
      H * H + InfoGeometry.Physics.andreevSwap (A := Stage 5) * (H * H) *
        InfoGeometry.Physics.andreevSwap (A := Stage 5)
    K 0 1 = 0 := by
  dsimp only
  rw [InfoGeometry.Physics.andreevSwap_conj]
  simp only [Matrix.add_apply]
  rw [carBdGSquare_offdiag_eq_massParity]
  rw [InfoGeometry.Physics.massiveBdGHamiltonian_sq_with_commutator]
  have hca := creation_annihilation_same_site (0 : Fin 5)
  have hLower : annihilation 0 * creation 0 - creation 0 * annihilation 0 =
      -invS carMassProjection := by
    change annihilation 0 * creation 0 - creation 0 * annihilation 0 =
      -((creation 0 * annihilation 0) - (1 - creation 0 * annihilation 0))
    rw [← hca]
    noncomm_ring
  rw [hLower]
  exact add_neg_cancel _

/-- The CAR BdG square is the off-diagonal matrix of the occupation parity.
This is the concrete block realization of the interaction defect identified
above. -/
theorem carBdGSquare_parity_matrix :
    let H := InfoGeometry.Physics.massiveBdGHamiltonian (creation 0) (annihilation 0)
    H * H = !![0, invS carMassProjection; -invS carMassProjection, 0] := by
  dsimp only
  have hc := creation_same_site_sq (0 : Fin 5)
  have ha := annihilation_same_site_sq (0 : Fin 5)
  have hca := creation_annihilation_same_site (0 : Fin 5)
  have hParity : creation 0 * annihilation 0 - annihilation 0 * creation 0 =
      invS carMassProjection := by
    change creation 0 * annihilation 0 - annihilation 0 * creation 0 =
      (creation 0 * annihilation 0) - (1 - creation 0 * annihilation 0)
    rw [← hca]
    noncomm_ring
  have hLower : annihilation 0 * creation 0 - creation 0 * annihilation 0 =
      -invS carMassProjection := by
    change annihilation 0 * creation 0 - creation 0 * annihilation 0 =
      -((creation 0 * annihilation 0) - (1 - creation 0 * annihilation 0))
    rw [← hca]
    noncomm_ring
  have hDiag : creation 0 * creation 0 + annihilation 0 * annihilation 0 = 0 := by
    rw [hc, ha, zero_add]
  have hDiagEntry : ∀ i j : Clifford.TowerMatrix.Idx 5,
      (creation 0 * creation 0) i j + (annihilation 0 * annihilation 0) i j = 0 := by
    intro i j
    have h := congrArg (fun X : Stage 5 => X i j) hDiag
    simpa only [Matrix.add_apply, Matrix.zero_apply] using h
  have hDiagEntryRev : ∀ i j : Clifford.TowerMatrix.Idx 5,
      (annihilation 0 * annihilation 0) i j + (creation 0 * creation 0) i j = 0 := by
    intro i j
    rw [add_comm]
    exact hDiagEntry i j
  rw [InfoGeometry.Physics.massiveBdGHamiltonian_sq_with_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, hDiagEntry, hDiagEntryRev,
      hParity, hLower]

/-- At the finite CAR mode, the operator-valued twelfth cyclotomic Higgs
polynomial is hole-odd and has square `-1`. In particular it is a nonzero
operator interaction, not a scalar spectral surrogate. -/
theorem carBdGCyclotomicHiggs_hole_odd_and_quartic_residue :
    let H := InfoGeometry.Physics.massiveBdGHamiltonian (creation 0) (annihilation 0)
    InfoGeometry.Physics.andreevSwap (A := Stage 5) *
        InfoGeometry.Physics.operatorCyclotomicHiggs H *
        InfoGeometry.Physics.andreevSwap (A := Stage 5) =
      -InfoGeometry.Physics.operatorCyclotomicHiggs H ∧
    InfoGeometry.Physics.operatorCyclotomicHiggs H *
        InfoGeometry.Physics.operatorCyclotomicHiggs H = -1 := by
  dsimp only
  let S : InfoGeometry.Physics.BdGBlock (Stage 5) :=
    InfoGeometry.Physics.massiveBdGHamiltonian (creation 0) (annihilation 0)
  have hSquare := carBdGSquare_parity_matrix
  have hParitySq : invS carMassProjection * invS carMassProjection = 1 := by
    rcases carMassProjection_structure with ⟨hP, _⟩
    change (carMassProjection - (1 - carMassProjection)) *
        (carMassProjection - (1 - carMassProjection)) = 1
    noncomm_ring [hP]
  have hSquareSquare :
      (!![0, invS carMassProjection; -invS carMassProjection, 0] :
        InfoGeometry.Physics.BdGBlock (Stage 5)) ^ 2 = -1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hParitySq]
  have hSquare : S * S =
      !![0, invS carMassProjection; -invS carMassProjection, 0] := by
    exact carBdGSquare_parity_matrix
  have hPower : S ^ 4 = (S * S) * (S * S) := by
    calc
      S ^ 4 = S ^ (2 + 2) := by norm_num
      _ = S ^ 2 * S ^ 2 := by rw [pow_add]
      _ = (S * S) * (S * S) := by rw [pow_two]
  have hFourth : S ^ 4 = -1 := by
    rw [hPower, hSquare, ← pow_two]
    exact hSquareSquare
  have hHiggs : InfoGeometry.Physics.operatorCyclotomicHiggs S = -(S * S) := by
    unfold InfoGeometry.Physics.operatorCyclotomicHiggs
    rw [hFourth]
    noncomm_ring
  have hSquareOdd :
      InfoGeometry.Physics.andreevSwap (A := Stage 5) * (S * S) *
        InfoGeometry.Physics.andreevSwap (A := Stage 5) = -(S * S) := by
    rw [InfoGeometry.Physics.andreevSwap_conj, hSquare]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hOdd :
    InfoGeometry.Physics.andreevSwap (A := Stage 5) *
        InfoGeometry.Physics.operatorCyclotomicHiggs S *
        InfoGeometry.Physics.andreevSwap (A := Stage 5) =
      -InfoGeometry.Physics.operatorCyclotomicHiggs S := by
    calc
      InfoGeometry.Physics.andreevSwap (A := Stage 5) *
          InfoGeometry.Physics.operatorCyclotomicHiggs S *
          InfoGeometry.Physics.andreevSwap (A := Stage 5) =
          -(InfoGeometry.Physics.andreevSwap (A := Stage 5) *
            (S * S) * InfoGeometry.Physics.andreevSwap (A := Stage 5)) := by
            rw [hHiggs]
            noncomm_ring
      _ = -(-(S * S)) := by rw [hSquareOdd]
      _ = -InfoGeometry.Physics.operatorCyclotomicHiggs S := by
            rw [hHiggs]
  have hResidue :
      InfoGeometry.Physics.operatorCyclotomicHiggs S *
        InfoGeometry.Physics.operatorCyclotomicHiggs S = -1 := by
    rw [hHiggs]
    calc
      -(S * S) * -(S * S) = (S * S) * (S * S) := by noncomm_ring
      _ = S ^ 4 := hPower.symm
      _ = -1 := hFourth
  exact ⟨hOdd, hResidue⟩

/-- The finite CAR mass-parity identity is preserved by the actual stage-5
inclusion into the UHF colimit.  In particular, the colimit BdG square is
still the off-diagonal Peirce grading of the occupied-mode projection. -/
theorem carBdGSquare_parity_matrix_at_limit :
    let f := ofStage 5
    let D : Limit := f (creation 0)
    let M : Limit := f (annihilation 0)
    let P : Limit := f carMassProjection
    let H := InfoGeometry.Physics.massiveBdGHamiltonian D M
    H * H = !![0, invS P; -invS P, 0] := by
  dsimp only
  have hDsq : ofStage 5 (creation 0) * ofStage 5 (creation 0) = 0 := by
    rw [← map_mul, creation_same_site_sq, map_zero]
  have hMsq : ofStage 5 (annihilation 0) * ofStage 5 (annihilation 0) = 0 := by
    rw [← map_mul, annihilation_same_site_sq, map_zero]
  have hCAR : ofStage 5 (creation 0) * ofStage 5 (annihilation 0) +
      ofStage 5 (annihilation 0) * ofStage 5 (creation 0) = 1 := by
    simpa only [map_add, map_mul, map_one] using
      congrArg (ofStage 5) (creation_annihilation_same_site (0 : Fin 5))
  have hParity : ofStage 5 (creation 0) * ofStage 5 (annihilation 0) -
      ofStage 5 (annihilation 0) * ofStage 5 (creation 0) =
        invS (ofStage 5 carMassProjection) := by
    unfold invS
    dsimp [carMassProjection]
    rw [map_mul]
    have hrev : ofStage 5 (annihilation 0) * ofStage 5 (creation 0) =
        1 - ofStage 5 (creation 0) * ofStage 5 (annihilation 0) := by
      rw [← hCAR]
      abel
    rw [hrev]
  have hLower : ofStage 5 (annihilation 0) * ofStage 5 (creation 0) -
      ofStage 5 (creation 0) * ofStage 5 (annihilation 0) =
        -invS (ofStage 5 carMassProjection) := by
    calc
      _ = -(ofStage 5 (creation 0) * ofStage 5 (annihilation 0) -
          ofStage 5 (annihilation 0) * ofStage 5 (creation 0)) := by abel
      _ = -invS (ofStage 5 carMassProjection) := congrArg Neg.neg hParity
  rw [InfoGeometry.Physics.massiveBdGHamiltonian_sq_with_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hDsq, hMsq, hParity, hLower]

/-- The limiting CAR mass projection remains a self-adjoint idempotent, and
its chiral grading squares to one.  This is the projection identity used by
the limit coercivity theorem, now aligned with the BdG interaction above. -/
theorem carMassProjection_limit_structure :
    let P : Limit := ofStage 5 carMassProjection
    P * P = P ∧ star P = P ∧ invS P * invS P = 1 := by
  dsimp only
  rcases carMassProjection_structure with ⟨hidem, hstar⟩
  have hIdem := congrArg (ofStage 5) hidem
  have hStar := congrArg (ofStage 5) hstar
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_mul] using hIdem
  · simpa only [ofStage_star] using hStar
  · change (ofStage 5 carMassProjection - (1 - ofStage 5 carMassProjection)) *
      (ofStage 5 carMassProjection - (1 - ofStage 5 carMassProjection)) = 1
    noncomm_ring [by simpa only [map_mul] using hIdem]

/-- The CAR interaction in the mass-coupled BdG square does not disappear in
the UHF limit.  Its off-diagonal entry is an involution, by the transported
Peirce projection identity. -/
theorem carBdG_mass_interaction_survives_limit :
    let D : Limit := ofStage 5 (creation 0)
    let M : Limit := ofStage 5 (annihilation 0)
    let H := InfoGeometry.Physics.massiveBdGHamiltonian D M
    (H * H) 0 1 ≠ 0 := by
  dsimp only
  have hSquare := carBdGSquare_parity_matrix_at_limit
  have hEntry := congrArg (fun X : InfoGeometry.Physics.BdGBlock Limit => X 0 1) hSquare
  have hEntry' :
      (InfoGeometry.Physics.massiveBdGHamiltonian
          (ofStage 5 (creation 0)) (ofStage 5 (annihilation 0)) *
        InfoGeometry.Physics.massiveBdGHamiltonian
          (ofStage 5 (creation 0)) (ofStage 5 (annihilation 0))) 0 1 =
        invS (ofStage 5 carMassProjection) := by
    simpa using hEntry
  have hParity := carMassProjection_limit_structure.2.2
  intro hzero
  have hInvZero : invS (ofStage 5 carMassProjection) = 0 := by
    calc
      invS (ofStage 5 carMassProjection) =
          (InfoGeometry.Physics.massiveBdGHamiltonian
            (ofStage 5 (creation 0)) (ofStage 5 (annihilation 0)) *
           InfoGeometry.Physics.massiveBdGHamiltonian
            (ofStage 5 (creation 0)) (ofStage 5 (annihilation 0))) 0 1 := hEntry'.symm
      _ = 0 := hzero
  rw [hInvZero] at hParity
  simp at hParity

/-- The normalized trace on the algebraic UHF colimit, induced by the
compatible finite normalized traces of the real matrix stages. -/
def normalizedTraceLimit : Limit →ₗ[ℝ] ℝ where
  toFun := DirectLimit.lift
    (fun m n h => bondMap stageBond m n h)
    (fun n x => normalizedTrace n x)
    (by
      intro m n h x
      change normalizedTrace m x =
        normalizedTrace n (bondMap stageBond m n h x)
      induction h with
      | refl => simp [bondMap_refl]
      | @step n h ih =>
          rw [bondMap_succ]
          change normalizedTrace m x = normalizedTrace (n + 1)
            (stageEmbed n (bondMap stageBond m n h x))
          rw [stageEmbed_apply, normalizedTrace_matStageEmbed, ← ih])
  map_add' := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ n a b =>
        rw [DirectLimit.add_def, DirectLimit.lift_def]
        exact (normalizedTraceLinear n).map_add a b
  map_smul' := by
    intro c x
    induction x using DirectLimit.induction with
    | _ n a =>
        rw [Algebra.smul_def']
        change DirectLimit.lift
          (fun m n h => bondMap stageBond m n h)
          (fun n x => normalizedTrace n x) _
          (realAlgebraMap c * (⟦⟨n, a⟩⟧ : Limit)) = _
        rw [realAlgebraMap_stage n]
        change DirectLimit.lift
          (fun m n h => bondMap stageBond m n h)
          (fun n x => normalizedTrace n x) _
          ((⟦⟨n, algebraMap ℝ (Stage n) c⟩⟧ : Limit) *
            (⟦⟨n, a⟩⟧ : Limit)) = _
        rw [DirectLimit.mul_def, DirectLimit.lift_def]
        change normalizedTrace n (algebraMap ℝ (Stage n) c * a) =
          c • normalizedTrace n a
        rw [← Algebra.smul_def']
        exact (normalizedTraceLinear n).map_smul c a

/-- A finite CAR mode gives the explicit colimit Peirce–Hodge coercive bound
with constant `2` on every element of the actual algebraic UHF limit. -/
theorem cl55_car_mass_peirce_coercivity_at_limit (x : Limit) :
    (2 : ℝ) * normalizedTraceLimit
        (star (x - ofStage 5 carMassProjection * x * ofStage 5 carMassProjection) *
          (x - ofStage 5 carMassProjection * x * ofStage 5 carMassProjection)) ≤
      normalizedTraceLimit
        (star x *
          (genV (ofStage 5 carMassProjection) (ofStage 5 carMassOperator)
              (star (ofStage 5 carMassOperator)) * x +
            x * genV (ofStage 5 carMassProjection) (ofStage 5 carMassOperator)
              (star (ofStage 5 carMassOperator)))) := by
  apply seed_unit_horizon_mass_coercivity_descends
    5 normalizedTraceLimit
    (fun n y => by rfl)
    carMassProjection carMassOperator
    carMassProjection_structure.1 carMassProjection_structure.2
    carMassOperator_unit_horizon.2 x

end InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge

end
