/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
import InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry
import InfoGeometry.OperatorAlgebra.BanachNewtonPeirceConvergence

/-!
# InfoGeometry.Clifford.CliffordKreinPeirceBruhatBridge

Unification bridge joining:
1. Universal chiral involutions (`ChiralInvolution`) with noncommutative Peirce–Bruhat
   twists, Maurer–Cartan covariant constancy, and finite-stage meta-towers
   (`PeirceBruhatAporiaTowerAndMatrixGeometry`);
2. Split `Cl(1,1)` real Pauli representations (`PauliPeirceKreinBridge`,
   `RealPlaneMatrixBridge.kreinPlus`) with canonical `peirceCut2` and an explicit
   spacelike-vs-timelike signature defect dichotomy on `Matrix (Fin 2) (Fin 2) ℝ`;
3. Minkowski `Cl(3,1)` `ℕ`-graded Grace contraction (`GradedGraceContraction.graceOperator`,
   `hTrace_cl`, `kreinFlip31`, `graceBladeInner`) with non-nilpotent `-φ⁻¹ / 4`
   chiral idempotency defect towers;
4. Analytic Banach Newton–Peirce healing (`BanachNewtonPeirceConvergence`) on
   `(Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)` for the golden-contracted chiral operator
   (`‖idempotencyDefect graceContractedClmCut‖ ≤ φ⁻¹ / 4 < 1 / 6`), proving
   non-nilpotency at every finite stage alongside norm convergence to an idempotent
   commuting with both `graceContractedClmCut` and `clmCut`.

## Three-Bucket Audit Map

* **BUCKET 1 (Reused upstream owners)**:
  - `InfoGeometry.Clifford.GradedGraceContraction`: `cliffordGradeProj_zero_algebraMap`,
    `cliffordGradeProj_one_ι`, `clifford_ι_injective`, `hTrace_cl`, `cliffordBladeBasis`,
    `repr_cliffordGradeProj`, `repr_graceOperator`, `graceBladeInner_self_nonneg`,
    `Q31`, `Cl31`, `Q31_basis_vector`, `not_nonneg_cliffordKreinPairing_Q31`,
    `cliffordKreinPairing_Q31_kreinFlip_self_nonneg`.
  - `InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge`: `pauliChiral`, `pauliChiral_chi`,
    `pauliChiral_Pleft`, `pauliChiral_Pright`, `e2m_jLin_eq_pauliChiral_chi`,
    `e2m_kreinPlus_eq_pauliChiral_Pleft`, `e2m_kreinMinus_eq_pauliChiral_Pright`.
  - `InfoGeometry.Clifford.Cl11Matrix`: `Eplus`, `Eminus`, `J1`, `Eplus_sq`, `Eminus_sq`,
    `cl11EquivMat`, `cl11EquivMat_iota_pos`, `cl11EquivMat_iota_neg`.
  - `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry`:
    `peirceCut2`, `chartBruhatRingEquiv`, `all_depth_meta_tower_covariant_constancy_and_bruhat_invariance`.
  - `InfoGeometry.OperatorAlgebra.BanachNewtonPeirceConvergence`: `clmCut`,
    `banach_newtonPeirce_limit_idempotent_and_intertwiner`.
* **BUCKET 2 (New theorems proved here)**:
  - `chiralInvolution_peirce_bruhat_and_meta_tower`, `cl11_krein_peirce_signature_split`,
    `graceOperator_algebraMap`, `graceOperator_ι`,
    `idempotencyDefect_graceOperator_cl31Chiral0_Pleft_pow`,
    `graceContractedClmCut_non_nilpotent_and_banach_healed`,
    `cliffordKreinPeirceGraceBridgeArchetype`.
* **BUCKET 3 (Out-of-scope / excluded)**:
  - Infinite-dimensional Krein spaces and Lorentz-group representation theory beyond `Cl31`.
-/

set_option autoImplicit false

namespace InfoGeometry.Clifford.CliffordKreinPeirceBruhatBridge

open CliffordAlgebra
open Filter Topology
open InfoGeometry.Riemannian
open InfoGeometry.Clifford.GradedGraceContraction
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry
open InfoGeometry.OperatorAlgebra.BanachNewtonPeirceConvergence
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.MetaCompiler
open scoped goldenRatio Matrix

section ScalarHelpers

private theorem scalar_inv_phi_eq_sub_one : φ ^ (-(1 : ℤ)) = φ - 1 := by
  have hne : φ ≠ 0 := Real.goldenRatio_ne_zero
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  rw [zpow_neg_one]
  refine mul_left_cancel₀ hne ?_
  rw [mul_inv_cancel₀ hne]
  nlinarith [hsq]

private theorem scalar_quarter_add_sq_sub_half :
    (1 / 4 : ℝ) + (1 / 4 : ℝ) * (φ ^ (-(1 : ℤ))) ^ 2 - (1 / 2 : ℝ) =
      -(φ ^ (-(1 : ℤ)) / 4) := by
  have hinv : φ ^ (-(1 : ℤ)) = φ - 1 := scalar_inv_phi_eq_sub_one
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  rw [hinv]
  nlinarith [hsq]

private theorem scalar_quarter_two_sub_half (r : ℝ) :
    (1 / 4 : ℝ) * (r + r) - (1 / 2 : ℝ) * r = 0 := by
  ring

private theorem scalar_grace_chiral_pos_defect :
    (1 / 2 : ℝ) * (1 + φ ^ (-(1 : ℤ))) * ((1 / 2 : ℝ) * (1 + φ ^ (-(1 : ℤ)))) -
        (1 / 2 : ℝ) * (1 + φ ^ (-(1 : ℤ))) =
      -(φ ^ (-(1 : ℤ)) / 4) := by
  have hinv : φ ^ (-(1 : ℤ)) = φ - 1 := scalar_inv_phi_eq_sub_one
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  rw [hinv]
  nlinarith [hsq]

private theorem scalar_grace_chiral_neg_defect :
    (1 / 2 : ℝ) * (1 - φ ^ (-(1 : ℤ))) * ((1 / 2 : ℝ) * (1 - φ ^ (-(1 : ℤ)))) -
        (1 / 2 : ℝ) * (1 - φ ^ (-(1 : ℤ))) =
      -(φ ^ (-(1 : ℤ)) / 4) := by
  have hinv : φ ^ (-(1 : ℤ)) = φ - 1 := scalar_inv_phi_eq_sub_one
  have hsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  rw [hinv]
  nlinarith [hsq]

private theorem scalar_inv_phi_div_four_pos_and_lt_sixth :
    0 < φ ^ (-(1 : ℤ)) / 4 ∧ φ ^ (-(1 : ℤ)) / 4 < 1 / 6 := by
  have hpos : 0 < φ ^ (-(1 : ℤ)) / 4 := by
    exact div_pos (zpow_pos Real.goldenRatio_pos _) (by norm_num)
  have hsqrt5 : Real.sqrt 5 < 7 / 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hphi : φ < 5 / 3 := by
    rw [Real.goldenRatio]
    linarith [hsqrt5]
  have hinv : φ ^ (-(1 : ℤ)) = φ - 1 := scalar_inv_phi_eq_sub_one
  refine ⟨hpos, ?_⟩
  linarith [hphi, hinv]

private theorem scalar_neg_inv_phi_div_four_pow_ne_zero (n : ℕ) :
    (-(φ ^ (-(1 : ℤ)) / 4)) ^ (n + 1) ≠ 0 := by
  exact pow_ne_zero _ (neg_ne_zero.mpr scalar_inv_phi_div_four_pos_and_lt_sixth.1.ne')

private theorem scalar_norm_neg_inv_phi_div_four :
    ‖-(φ ^ (-(1 : ℤ)) / 4)‖ = φ ^ (-(1 : ℤ)) / 4 := by
  rw [Real.norm_eq_abs, abs_neg, abs_of_pos scalar_inv_phi_div_four_pos_and_lt_sixth.1]

private theorem scalar_half_quarter_sum :
    (1 / 4 : ℝ) * 1 + (1 / 4 : ℝ) * (-1) - (1 / 2 : ℝ) * 1 = -(1 / 2 : ℝ) := by
  norm_num

private theorem scalar_half_quarter_cross :
    (1 / 4 : ℝ) * 1 + (1 / 4 : ℝ) * 1 - (1 / 2 : ℝ) * 1 = 0 := by
  norm_num

private theorem scalar_two_mul_coord (a : ℝ) : 2 * a - a = a := by
  ring

private theorem scalar_zero_sub (a : ℝ) : (0 : ℝ) - a = -a := by
  ring

private theorem scalar_grace_coord0 (r x : ℝ) : (1 / 2 : ℝ) * (x + r * x) = (1 / 2 : ℝ) * (1 + r) * x := by
  ring

private theorem scalar_grace_coord1 (r x : ℝ) : (1 / 2 : ℝ) * (x + r * (-x)) = (1 / 2 : ℝ) * (1 - r) * x := by
  ring

end ScalarHelpers

/-! ## Section 1: Universal `ChiralInvolution` ↔ Peirce–Bruhat–Tower Bridge -/

section UniversalChiralPeirceBridge

/-- For any constructive chiral involution `C` over an `[ℝ]`-algebra `Op`, the Peirce grading
involution `invS C.Pleft` recovers `C.chi` verbatim. -/
theorem chiralInvolution_invS_Pleft_eq_chi
    {Op : Type*} [Ring Op] [Algebra ℝ Op] (C : ChiralInvolution Op) :
    invS C.Pleft = C.chi := by
  have hcomp : (1 : Op) - C.Pleft = C.Pright := by
    rw [← C.Pleft_add_Pright, add_sub_cancel_left]
  rw [invS, hcomp]
  exact C.Pleft_sub_Pright

/-- Lifting any `ChiralInvolution` into the full Peirce–Bruhat–Maurer–Cartan infrastructure:
exact zero idempotency defect, chiral complement `1 - Pleft = Pright`, unipotent Bruhat conjugation
preserving idempotency, and covariant constancy `peirceCovariantDeriv = 0`. -/
theorem chiralInvolution_peirce_bruhat_and_meta_tower
    {Op : Type*} [Ring Op] [Algebra ℝ Op] (C : ChiralInvolution Op) (A B : Op) :
    idempotencyDefect C.Pleft = 0 ∧
      invS C.Pleft = C.chi ∧
      (1 : Op) - C.Pleft = C.Pright ∧
      idempotencyDefect (chartBruhatRingEquiv C.Pleft_idem A B C.Pleft) = 0 ∧
      peirceCovariantDeriv C.Pleft A B (genV C.Pleft A B) = 0 := by
  have hIdem : idempotencyDefect C.Pleft = 0 := idempotencyDefect_eq_zero_iff.mpr C.Pleft_idem
  have hInv : invS C.Pleft = C.chi := chiralInvolution_invS_Pleft_eq_chi C
  have hComp : (1 : Op) - C.Pleft = C.Pright := by
    rw [← C.Pleft_add_Pright, add_sub_cancel_left]
  have hTower := all_depth_meta_tower_covariant_constancy_and_bruhat_invariance C.Pleft_idem A B 0 0
  have hCov : peirceCovariantDeriv C.Pleft A B (genV C.Pleft A B) = 0 := by
    simpa only [Function.iterate_zero_apply] using hTower.1
  have hBruhat : idempotencyDefect (chartBruhatRingEquiv C.Pleft_idem A B C.Pleft) = 0 := by
    rw [idempotencyDefect_eq_zero_iff, ← map_mul, C.Pleft_idem]
  exact ⟨hIdem, hInv, hComp, hBruhat, hCov⟩

end UniversalChiralPeirceBridge

/-! ## Section 2: Split `Cl(1,1)` Pauli Representation, Krein Sheets, and Signature Aporia -/

section SplitCl11PauliSignatureBridge

/-- The Pauli chiral `+1` projector in `Cl11Matrix.Mat2` is literally `peirceCut2 (B := ℝ)`. -/
theorem pauliChiral_Pleft_eq_peirceCut2 :
    pauliChiral.Pleft = peirceCut2 (B := ℝ) := by
  rw [pauliChiral_Pleft]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceCut2]

/-- The Pauli chiral `-1` projector is literally the complementary matrix cut `1 - peirceCut2`. -/
theorem pauliChiral_Pright_eq_one_sub_peirceCut2 :
    pauliChiral.Pright = (1 : Mat2) - peirceCut2 (B := ℝ) := by
  rw [pauliChiral_Pright]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceCut2]

/-- Explicit closed `Matrix (Fin 2) (Fin 2) ℝ` noncommutativity witness via the Pauli chiral
generator `Eplus` and elliptic generator `Eminus` (`σ₃ ε ≠ ε σ₃`). -/
theorem mat2_Eplus_Eminus_noncomm :
    ∃ X Y : Matrix (Fin 2) (Fin 2) ℝ, X * Y ≠ Y * X := by
  refine ⟨Eplus, Eminus, ?_⟩
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  norm_num [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Concrete `Cl(1,1)` ↔ Krein ↔ Peirce unification & signature aporia on `Mat2`:
1. The real-plane Krein `+1` spectral projector `endToMatrix kreinPlus` equals `peirceCut2 (B := ℝ)`.
2. The spacelike `Cl(1,1)` generator image `Eplus` produces an exact idempotent half-projector
   with `idempotencyDefect ((1/2) • (1 + Eplus)) = 0`.
3. By contrast, the timelike/elliptic `Cl(1,1)` generator image `Eminus` (`Eminus^2 = -1`)
   produces a nonzero central idempotency defect `-(1/2) • 1 ≠ 0` when substituted into the same
   chiral formula. -/
theorem cl11_krein_peirce_signature_split :
    InfoGeometry.Krein.RealPlaneMatrixBridge.endToMatrix kreinPlus = peirceCut2 (B := ℝ) ∧
      idempotencyDefect ((1 / 2 : ℝ) • ((1 : Mat2) +
        cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)))) = 0 ∧
      idempotencyDefect ((1 / 2 : ℝ) • ((1 : Mat2) +
        cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)))) = -(1 / 2 : ℝ) • (1 : Mat2) ∧
      idempotencyDefect ((1 / 2 : ℝ) • ((1 : Mat2) +
        cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)))) ≠ 0 ∧
      Eplus * Eminus ≠ Eminus * Eplus := by
  have hKrein : InfoGeometry.Krein.RealPlaneMatrixBridge.endToMatrix kreinPlus =
      peirceCut2 (B := ℝ) := by
    rw [e2m_kreinPlus_eq_pauliChiral_Pleft, pauliChiral_Pleft_eq_peirceCut2]
  have hPos : idempotencyDefect ((1 / 2 : ℝ) • ((1 : Mat2) +
      cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)))) = 0 := by
    rw [cl11EquivMat_iota_pos, ← pauliChiral_chi]
    exact idempotencyDefect_eq_zero_iff.mpr pauliChiral.Pleft_idem
  have hNeg : idempotencyDefect ((1 / 2 : ℝ) • ((1 : Mat2) +
      cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)))) = -(1 / 2 : ℝ) • (1 : Mat2) := by
    rw [cl11EquivMat_iota_neg, idempotencyDefect]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Eminus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply,
        Matrix.sub_apply] <;> norm_num
  have hNegNe : idempotencyDefect ((1 / 2 : ℝ) • ((1 : Mat2) +
      cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)))) ≠ 0 := by
    rw [hNeg]
    intro h0
    have h00 := congrArg (fun M : Mat2 => M 0 0) h0
    norm_num at h00
  obtain ⟨X, Y, hXY⟩ := mat2_Eplus_Eminus_noncomm
  have hEP : Eplus * Eminus ≠ Eminus * Eplus := by
    intro h
    have h01 := congrArg (fun M : Mat2 => M 0 1) h
    norm_num [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two] at h01
  exact ⟨hKrein, hPos, hNeg, hNegNe, hEP⟩

end SplitCl11PauliSignatureBridge

/-! ## Section 3: Minkowski `Cl(3,1)` Grace Contraction, Krein Flip, and `-φ⁻¹ / 4` Defect Tower -/

section MinkowskiCl31GraceAndKreinAporia

/-- Evaluating `hTrace_cl` on an embedded scalar returns the scalar directly. -/
private theorem hTrace_cl_algebraMap {R : Type*} [CommRing R] [Invertible (2 : R)]
    {M : Type*} [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (r : R) :
    hTrace_cl Q (algebraMap R (CliffordAlgebra Q) r) = r := by
  rw [hTrace_cl, LinearMap.comp_apply]
  change ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior Q
    (algebraMap R (CliffordAlgebra Q) r)) = r
  rw [equivExterior_algebraMap, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

/-- The `ℕ`-graded Grace operator `graceOperator Q` fixes grade-0 scalars. -/
theorem graceOperator_algebraMap {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (r : ℝ) :
    graceOperator Q (algebraMap ℝ (CliffordAlgebra Q) r) =
      algebraMap ℝ (CliffordAlgebra Q) r := by
  apply (cliffordBladeBasis Q).repr.injective
  ext S
  rw [repr_graceOperator]
  by_cases hS : S.card = 0
  · simp only [hS, Nat.cast_zero, neg_zero, zpow_zero, one_mul]
  · have hz : (cliffordBladeBasis Q).repr (algebraMap ℝ (CliffordAlgebra Q) r) S = 0 := by
      have hpr : cliffordGradeProj Q 0 (algebraMap ℝ (CliffordAlgebra Q) r) =
          algebraMap ℝ (CliffordAlgebra Q) r := cliffordGradeProj_zero_algebraMap Q r
      have hr := congrArg (fun x => (cliffordBladeBasis Q).repr x S) hpr
      rw [repr_cliffordGradeProj] at hr
      simp only [hS, ite_false] at hr
      exact hr.symm
    rw [hz, mul_zero]

/-- In particular `graceOperator Q 1 = 1`. -/
theorem graceOperator_one {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) :
    graceOperator Q 1 = 1 := by
  have h := graceOperator_algebraMap Q 1
  simpa only [map_one] using h

/-- The `ℕ`-graded Grace operator contracts every grade-1 vector by `φ⁻¹ = φ ^ (-(1 : ℤ))`. -/
theorem graceOperator_ι {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (v : Fin n → ℝ) :
    graceOperator Q (CliffordAlgebra.ι Q v) = (φ ^ (-(1 : ℤ))) • CliffordAlgebra.ι Q v := by
  apply (cliffordBladeBasis Q).repr.injective
  ext S
  rw [repr_graceOperator, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hS : S.card = 1
  · simp only [hS, Nat.cast_one]
  · have hz : (cliffordBladeBasis Q).repr (CliffordAlgebra.ι Q v) S = 0 := by
      have hpr : cliffordGradeProj Q 1 (CliffordAlgebra.ι Q v) = CliffordAlgebra.ι Q v :=
        cliffordGradeProj_one_ι Q v
      have hr := congrArg (fun x => (cliffordBladeBasis Q).repr x S) hpr
      rw [repr_cliffordGradeProj] at hr
      simp only [hS, ite_false] at hr
      exact hr.symm
    rw [hz, mul_zero, mul_zero]

/-- Canonical Minkowski basis gamma generators `γᵢ = ι Q31 eᵢ` inside `Cl31`. -/
noncomputable def cl31Gamma (i : Fin 4) : Cl31 :=
  CliffordAlgebra.ι Q31 (Pi.single i (1 : ℝ))

/-- Spacelike unit generator `cl31E0 = γ₀` in `Cl31`. -/
noncomputable def cl31E0 : Cl31 := cl31Gamma 0

/-- Timelike unit generator `cl31E3 = γ₃` in `Cl31`. -/
noncomputable def cl31E3 : Cl31 := cl31Gamma 3

theorem cl31E0_sq : cl31E0 * cl31E0 = 1 := by
  dsimp [cl31E0, cl31Gamma]
  rw [CliffordAlgebra.ι_sq_scalar, Q31_basis_vector]
  change algebraMap ℝ Cl31 (1 : ℝ) = 1
  exact map_one _

theorem cl31E3_sq : cl31E3 * cl31E3 = -1 := by
  dsimp [cl31E3, cl31Gamma]
  rw [CliffordAlgebra.ι_sq_scalar, Q31_basis_vector]
  change algebraMap ℝ Cl31 (-1 : ℝ) = -1
  rw [map_neg, map_one]

/-- `cl31E0` and `cl31E3` strictly anticommute in `Cl(3,1)`. -/
theorem cl31E0_mul_cl31E3_anticomm :
    cl31E0 * cl31E3 + cl31E3 * cl31E0 = 0 := by
  have hsum : cl31E0 + cl31E3 =
      CliffordAlgebra.ι Q31 (Pi.single 0 (1 : ℝ) + Pi.single 3 (1 : ℝ)) := by
    dsimp [cl31E0, cl31E3, cl31Gamma]
    exact (map_add (CliffordAlgebra.ι Q31) _ _).symm
  have hq : Q31 (Pi.single 0 (1 : ℝ) + Pi.single 3 (1 : ℝ)) = 0 := by
    rw [Q31, QuadraticMap.weightedSumSquares_apply]
    simp only [Pi.add_apply, smul_eq_mul, Fin.sum_univ_four, Pi.single_apply]
    norm_num [signatureWeights31]
  have hsq : (cl31E0 + cl31E3) * (cl31E0 + cl31E3) = 0 := by
    rw [hsum, CliffordAlgebra.ι_sq_scalar, hq, map_zero]
  have hexp :
      (cl31E0 + cl31E3) * (cl31E0 + cl31E3) =
        (cl31E0 * cl31E0 + cl31E3 * cl31E3) + (cl31E0 * cl31E3 + cl31E3 * cl31E0) := by
    rw [mul_add, add_mul, add_mul]
    abel
  rw [hexp, cl31E0_sq, cl31E3_sq, add_neg_cancel, zero_add] at hsq
  exact hsq

/-- Closed noncommutativity witness inside `Cl31`: `cl31E0 * cl31E3 ≠ cl31E3 * cl31E0`. -/
theorem cl31E0_mul_cl31E3_ne : cl31E0 * cl31E3 ≠ cl31E3 * cl31E0 := by
  intro heq
  have hant := cl31E0_mul_cl31E3_anticomm
  rw [← heq] at hant
  have hmul : cl31E0 * (cl31E0 * cl31E3 + cl31E0 * cl31E3) * cl31E3 = 0 := by
    rw [hant, mul_zero, zero_mul]
  have hterm : cl31E0 * (cl31E0 * cl31E3) * cl31E3 = (-1 : Cl31) := by
    rw [← mul_assoc cl31E0 cl31E0 cl31E3, cl31E0_sq, one_mul, cl31E3_sq]
  have h1 :
      cl31E0 * (cl31E0 * cl31E3 + cl31E0 * cl31E3) * cl31E3 = (-2 : ℝ) • (1 : Cl31) := by
    rw [mul_add, add_mul, hterm, ← neg_add, ← two_smul ℝ (1 : Cl31), ← neg_smul]
  rw [h1, ← Algebra.algebraMap_eq_smul_one] at hmul
  have htr := congrArg (hTrace_cl Q31) hmul
  rw [hTrace_cl_algebraMap, map_zero] at htr
  norm_num at htr

/-- Spatial chiral involution constructed from the spacelike `Cl31` generator `γ₀`. -/
noncomputable def cl31Chiral0 : ChiralInvolution Cl31 where
  chi := cl31E0
  chi_sq := cl31E0_sq

/-- Applying the `ℕ`-graded Grace operator to `cl31Chiral0.Pleft` leaves grade `0` fixed while
damping the grade-1 chiral direction by `φ⁻¹`. -/
theorem graceOperator_cl31Chiral0_Pleft :
    graceOperator Q31 cl31Chiral0.Pleft =
      (1 / 2 : ℝ) • ((1 : Cl31) + (φ ^ (-(1 : ℤ))) • cl31E0) := by
  dsimp [ChiralInvolution.Pleft, cl31Chiral0]
  rw [map_smul, map_add, graceOperator_one, cl31E0, cl31Gamma, graceOperator_ι]

/-- Explicit closed form of the Grace-induced idempotency defect and all its positive powers
inside `Cl31`:
`(idempotencyDefect (graceOperator Q31 cl31Chiral0.Pleft)) ^ (n + 1) = (-(φ⁻¹ / 4)) ^ (n + 1) • 1 ≠ 0`. -/
theorem idempotencyDefect_graceOperator_cl31Chiral0_Pleft_pow (n : ℕ) :
    idempotencyDefect (graceOperator Q31 cl31Chiral0.Pleft) =
        (-(φ ^ (-(1 : ℤ)) / 4)) • (1 : Cl31) ∧
      (idempotencyDefect (graceOperator Q31 cl31Chiral0.Pleft)) ^ (n + 1) =
        ((-(φ ^ (-(1 : ℤ)) / 4)) ^ (n + 1)) • (1 : Cl31) ∧
      (idempotencyDefect (graceOperator Q31 cl31Chiral0.Pleft)) ^ (n + 1) ≠ 0 := by
  have hdef :
      idempotencyDefect (graceOperator Q31 cl31Chiral0.Pleft) =
        (-(φ ^ (-(1 : ℤ)) / 4)) • (1 : Cl31) := by
    rw [graceOperator_cl31Chiral0_Pleft, idempotencyDefect]
    set r : ℝ := φ ^ (-(1 : ℤ))
    have hsq :
        ((1 / 2 : ℝ) • ((1 : Cl31) + r • cl31E0)) *
            ((1 / 2 : ℝ) • ((1 : Cl31) + r • cl31E0)) =
          (1 / 4 : ℝ) • ((1 : Cl31) + r • cl31E0 + r • cl31E0 + (r * r) • (1 : Cl31)) := by
      have h14 : (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 := by norm_num
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, h14]
      congr 1
      simp only [mul_add, add_mul, one_mul, mul_one, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
        smul_add, smul_smul, cl31E0_sq]
      abel
    rw [hsq]
    have hcomb :
        (1 / 4 : ℝ) • ((1 : Cl31) + r • cl31E0 + r • cl31E0 + (r * r) • (1 : Cl31)) -
            (1 / 2 : ℝ) • ((1 : Cl31) + r • cl31E0) =
          ((1 / 4 : ℝ) + (1 / 4 : ℝ) * r ^ 2 - (1 / 2 : ℝ)) • (1 : Cl31) +
            ((1 / 4 : ℝ) * (r + r) - (1 / 2 : ℝ) * r) • cl31E0 := by
      simp only [smul_add, smul_smul, add_smul, sub_smul, sq, mul_add]
      abel
    rw [hcomb, scalar_quarter_two_sub_half r, zero_smul, add_zero]
    rw [show r = φ ^ (-(1 : ℤ)) from rfl, scalar_quarter_add_sq_sub_half]
  have hpow :
      (idempotencyDefect (graceOperator Q31 cl31Chiral0.Pleft)) ^ (n + 1) =
        ((-(φ ^ (-(1 : ℤ)) / 4)) ^ (n + 1)) • (1 : Cl31) := by
    rw [hdef, smul_pow, one_pow]
  have hne : (idempotencyDefect (graceOperator Q31 cl31Chiral0.Pleft)) ^ (n + 1) ≠ 0 := by
    rw [hpow, ← Algebra.algebraMap_eq_smul_one]
    intro h0
    have htr := congrArg (hTrace_cl Q31) h0
    rw [hTrace_cl_algebraMap, map_zero] at htr
    exact scalar_neg_inv_phi_div_four_pow_ne_zero n htr
  exact ⟨hdef, hpow, hne⟩

/-- Combined Minkowski `Cl(3,1)` Krein/Grace signature theorem uniting:
- indefinite scalar reversal pairing (`not_nonneg_cliffordKreinPairing_Q31`),
- Krein-flipped positive-definite vector pairing (`cliffordKreinPairing_Q31_kreinFlip_self_nonneg`),
- Grade-weighted Euclidean `graceBladeInner Q31` positivity,
- Noncommutative anticommuting generators `cl31E0 * cl31E3 ≠ cl31E3 * cl31E0`,
- Non-nilpotent Grace chiral defect tower `-(φ⁻¹ / 4)` in `Cl31`. -/
theorem minkowski_cl31_krein_grace_signature_and_aporia :
    (¬ ∀ u : Cl31, 0 ≤ cliffordKreinPairing Q31 u u) ∧
      (∀ v : Fin 4 → ℝ,
        0 ≤ cliffordKreinPairing Q31 (CliffordAlgebra.ι Q31 (kreinFlip31 v))
          (CliffordAlgebra.ι Q31 v)) ∧
      (∀ u : Cl31, 0 ≤ graceBladeInner Q31 u u) ∧
      cl31E0 * cl31E3 ≠ cl31E3 * cl31E0 ∧
      (∀ n : ℕ, (idempotencyDefect (graceOperator Q31 cl31Chiral0.Pleft)) ^ (n + 1) ≠ 0) := by
  refine ⟨not_nonneg_cliffordKreinPairing_Q31, cliffordKreinPairing_Q31_kreinFlip_self_nonneg,
    graceBladeInner_self_nonneg Q31, cl31E0_mul_cl31E3_ne, ?_⟩
  intro n
  exact (idempotencyDefect_graceOperator_cl31Chiral0_Pleft_pow n).2.2

end MinkowskiCl31GraceAndKreinAporia

/-! ## Section 4: Banach Newton–Peirce Healing of the Grace-Contracted Chiral Cut -/

section BanachHealingOfGraceContractedCut

/-- Real chiral involution on `Fin 2 → ℝ` induced by `clmCut` (`clmChi = 2 • clmCut - 1`). -/
noncomputable def clmChi : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (2 : ℝ) • clmCut - 1

/-- Grace-contracted chiral operator `(1 / 2) • (1 + φ⁻¹ • clmChi)` on `(Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)`,
whose eigenvalues `(1 + φ⁻¹) / 2` and `(1 - φ⁻¹) / 2` mirror `graceOperator Q31 cl31Chiral0.Pleft`
with exact non-nilpotent defect `-(φ⁻¹ / 4) • 1`. -/
noncomputable def graceContractedClmCut : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (1 / 2 : ℝ) • (1 + (φ ^ (-(1 : ℤ))) • clmChi)

private theorem clmChi_apply (v : Fin 2 → ℝ) :
    clmChi v = ![v 0, -v 1] := by
  have hCut : ∀ w : Fin 2 → ℝ, clmCut w = ![w 0, 0] := fun _ => rfl
  dsimp [clmChi]
  rw [sub_apply, smul_apply, one_apply_eq_self, hCut]
  ext i
  fin_cases i
  · change (2 : ℝ) * v 0 - v 0 = v 0
    exact scalar_two_mul_coord (v 0)
  · change (2 : ℝ) * 0 - v 1 = -v 1
    rw [mul_zero]
    exact scalar_zero_sub (v 1)

private theorem graceContractedClmCut_apply (v : Fin 2 → ℝ) :
    graceContractedClmCut v =
      ![(1 / 2 : ℝ) * (1 + φ ^ (-(1 : ℤ))) * v 0,
        (1 / 2 : ℝ) * (1 - φ ^ (-(1 : ℤ))) * v 1] := by
  dsimp [graceContractedClmCut]
  rw [smul_apply, add_apply, one_apply_eq_self, smul_apply, clmChi_apply]
  ext i
  fin_cases i
  · change (1 / 2 : ℝ) * (v 0 + φ ^ (-(1 : ℤ)) * v 0) = _
    exact scalar_grace_coord0 (φ ^ (-(1 : ℤ))) (v 0)
  · change (1 / 2 : ℝ) * (v 1 + φ ^ (-(1 : ℤ)) * (-v 1)) = _
    exact scalar_grace_coord1 (φ ^ (-(1 : ℤ))) (v 1)

/-- Closed formula for the idempotency defect of `graceContractedClmCut`: it equals the exact
scalar multiple `-(φ⁻¹ / 4) • 1` on `(Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)`. -/
theorem idempotencyDefect_graceContractedClmCut_eq_smul_one :
    idempotencyDefect graceContractedClmCut =
      (-(φ ^ (-(1 : ℤ)) / 4)) • (1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) := by
  ext v i
  dsimp [idempotencyDefect]
  rw [sub_apply, smul_apply, one_apply_eq_self]
  change graceContractedClmCut (graceContractedClmCut v) i - graceContractedClmCut v i =
    (-(φ ^ (-(1 : ℤ)) / 4)) * v i
  rw [graceContractedClmCut_apply, graceContractedClmCut_apply]
  fin_cases i
  · change ((1 / 2 : ℝ) * (1 + φ ^ (-(1 : ℤ)))) * ((1 / 2 : ℝ) * (1 + φ ^ (-(1 : ℤ))) * v 0) -
        (1 / 2 : ℝ) * (1 + φ ^ (-(1 : ℤ))) * v 0 = -(φ ^ (-(1 : ℤ)) / 4) * v 0
    rw [← mul_assoc, ← sub_mul, scalar_grace_chiral_pos_defect]
  · change ((1 / 2 : ℝ) * (1 - φ ^ (-(1 : ℤ)))) * ((1 / 2 : ℝ) * (1 - φ ^ (-(1 : ℤ))) * v 1) -
        (1 / 2 : ℝ) * (1 - φ ^ (-(1 : ℤ))) * v 1 = -(φ ^ (-(1 : ℤ)) / 4) * v 1
    rw [← mul_assoc, ← sub_mul, scalar_grace_chiral_neg_defect]

private theorem commute_clmCut_graceContractedClmCut :
    Commute clmCut graceContractedClmCut := by
  have hCut : ∀ w : Fin 2 → ℝ, clmCut w = ![w 0, 0] := fun _ => rfl
  ext v i
  change clmCut (graceContractedClmCut v) i = graceContractedClmCut (clmCut v) i
  rw [graceContractedClmCut_apply, hCut, hCut, graceContractedClmCut_apply]
  fin_cases i
  · change (1 / 2 : ℝ) * (1 + φ ^ (-(1 : ℤ))) * v 0 =
        (1 / 2 : ℝ) * (1 + φ ^ (-(1 : ℤ))) * ![v 0, 0] 0
    simp only [Matrix.cons_val_zero]
  · change (0 : ℝ) = (1 / 2 : ℝ) * (1 - φ ^ (-(1 : ℤ))) * ![v 0, 0] 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero]

/-- **Banach Healing of the Grace-Contracted Chiral Cut**:
Even though algebraic nilpotency fails at every finite depth
(`(idempotencyDefect graceContractedClmCut) ^ (n + 1) ≠ 0` for all `n : ℕ`),
its operator norm satisfies `‖idempotencyDefect graceContractedClmCut‖ ≤ φ⁻¹ / 4 < 1 / 6`
because `φ = (1 + √5)/2 < 5/3 ⇒ φ⁻¹ / 4 < 1/6`. Therefore `banach_newtonPeirce_limit_idempotent_and_intertwiner`
heals the Grace-contracted cut analytically to a genuine idempotent `e` commuting with both
`graceContractedClmCut` and `clmCut`. -/
theorem graceContractedClmCut_non_nilpotent_and_banach_healed :
    (∀ n : ℕ, (idempotencyDefect graceContractedClmCut) ^ (n + 1) ≠ 0) ∧
      ‖idempotencyDefect graceContractedClmCut‖ ≤ φ ^ (-(1 : ℤ)) / 4 ∧
      ‖idempotencyDefect graceContractedClmCut‖ < 1 / 6 ∧
      ∃ e : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ),
        Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] graceContractedClmCut)
          Filter.atTop (nhds e) ∧
        e * e = e ∧
        Commute graceContractedClmCut e ∧
        Commute clmCut e := by
  have hNonNil : ∀ n : ℕ, (idempotencyDefect graceContractedClmCut) ^ (n + 1) ≠ 0 := by
    intro n h0
    have hpow :
        (idempotencyDefect graceContractedClmCut) ^ (n + 1) =
          ((-(φ ^ (-(1 : ℤ)) / 4)) ^ (n + 1)) • (1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) := by
      rw [idempotencyDefect_graceContractedClmCut_eq_smul_one, smul_pow, one_pow]
    have hApp := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => T ![1, 0] 0) h0
    rw [hpow, smul_apply, one_apply_eq_self, zero_apply] at hApp
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at hApp
    exact scalar_neg_inv_phi_div_four_pow_ne_zero n hApp
  have hNorm : ‖idempotencyDefect graceContractedClmCut‖ ≤ φ ^ (-(1 : ℤ)) / 4 := by
    rw [idempotencyDefect_graceContractedClmCut_eq_smul_one]
    refine ContinuousLinearMap.opNorm_le_bound _
      (le_of_lt scalar_inv_phi_div_four_pos_and_lt_sixth.1) fun v => ?_
    rw [smul_apply, one_apply_eq_self, norm_smul, scalar_norm_neg_inv_phi_div_four]
  have hLt : ‖idempotencyDefect graceContractedClmCut‖ < 1 / 6 :=
    lt_of_le_of_lt hNorm scalar_inv_phi_div_four_pos_and_lt_sixth.2
  obtain ⟨e, heLim, heIdem, heCommSelf, heCommAll, _⟩ :=
    banach_newtonPeirce_limit_idempotent_and_intertwiner hLt
  exact ⟨hNonNil, hNorm, hLt, e, heLim, heIdem, heCommSelf,
    heCommAll clmCut commute_clmCut_graceContractedClmCut⟩

end BanachHealingOfGraceContractedCut

/-! ## Section 5: QMS Archetype Registration & Kernel Audit -/

/-- QMS `TypedArchetype` certifying the complete four-lane unification across `ChiralInvolution`,
`Cl(1,1)` real Pauli/Krein geometry, `Cl(3,1)` Minkowski Grace contraction (`-φ⁻¹ / 4` tower),
and analytic Banach Newton–Peirce healing on `(Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)`. -/
noncomputable def cliffordKreinPeirceGraceBridgeArchetype : TypedArchetype Unit .proved where
  name := `CliffordKreinPeirceGraceBridge
  phase := 6
  claim := fun _ =>
    (∀ (A B : Cl31),
      idempotencyDefect cl31Chiral0.Pleft = 0 ∧
      invS cl31Chiral0.Pleft = cl31Chiral0.chi ∧
      peirceCovariantDeriv cl31Chiral0.Pleft A B (genV cl31Chiral0.Pleft A B) = 0) ∧
    (InfoGeometry.Krein.RealPlaneMatrixBridge.endToMatrix kreinPlus = peirceCut2 (B := ℝ) ∧
      Eplus * Eminus ≠ Eminus * Eplus) ∧
    (cl31E0 * cl31E3 ≠ cl31E3 * cl31E0 ∧
      ∀ n : ℕ, (idempotencyDefect (graceOperator Q31 cl31Chiral0.Pleft)) ^ (n + 1) ≠ 0) ∧
    (‖idempotencyDefect graceContractedClmCut‖ < 1 / 6 ∧
      ∃ e : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ),
        Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] graceContractedClmCut)
          Filter.atTop (nhds e) ∧
        e * e = e ∧
        Commute graceContractedClmCut e ∧
        Commute clmCut e)
  evidence := fun _ => by
    have hChiral : ∀ (A B : Cl31),
        idempotencyDefect cl31Chiral0.Pleft = 0 ∧
        invS cl31Chiral0.Pleft = cl31Chiral0.chi ∧
        peirceCovariantDeriv cl31Chiral0.Pleft A B (genV cl31Chiral0.Pleft A B) = 0 := by
      intro A B
      have hT := chiralInvolution_peirce_bruhat_and_meta_tower cl31Chiral0 A B
      exact ⟨hT.1, hT.2.1, hT.2.2.2.2⟩
    have hCl11 := cl11_krein_peirce_signature_split
    have hCl31 := minkowski_cl31_krein_grace_signature_and_aporia
    have hBan := graceContractedClmCut_non_nilpotent_and_banach_healed
    exact ⟨hChiral, ⟨hCl11.1, hCl11.2.2.2.2⟩, ⟨hCl31.2.2.2.1, hCl31.2.2.2.2⟩,
      ⟨hBan.2.2.1, hBan.2.2.2⟩⟩

#register_archetype cliffordKreinPeirceGraceBridgeArchetype
#audit_archetype cliffordKreinPeirceGraceBridgeArchetype

end InfoGeometry.Clifford.CliffordKreinPeirceBruhatBridge
