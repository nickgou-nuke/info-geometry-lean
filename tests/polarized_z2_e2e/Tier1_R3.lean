/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
import InfoGeometry.OperatorAlgebra.ProjectorCurvatureSplitting
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Canonical.TensorLimitExactConnection
import Mathlib.Tactic
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option autoImplicit false

noncomputable section

namespace PolarizedZ2E2E.Tier1R3

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
open InfoGeometry.OperatorAlgebra.ProjectorCurvatureSplitting
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorLimitExactConnection

/-! ## Local non-commutativity witnesses and concrete helpers -/

private theorem local_mat2_noncomm :
    (!![(0 : ℝ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 0; 1, 0] ≠
      !![0, 0; 1, 0] * !![0, 1; 0, 0] := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

private theorem local_mat3_noncomm :
    (!![(0 : ℝ), 0, 1; 0, 0, 0; -1, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ) *
        !![0, 0, 0; 0, 0, 1; 0, -1, 0] ≠
      !![0, 0, 0; 0, 0, 1; 0, -1, 0] * !![0, 0, 1; 0, 0, 0; -1, 0, 0] := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_three] at h01

private def mat3PIdemp : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 0; 0, 0, 0]

private theorem mat3PIdemp_sq : mat3PIdemp * mat3PIdemp = mat3PIdemp := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mat3PIdemp, Matrix.mul_apply, Fin.sum_univ_three]

private def mat3BlockMat (x : Witnesses.UpperAff2) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 0, x.u, x.v; 0, 0, 0]

private theorem mat3BlockMat_bracket (x y : Witnesses.UpperAff2) :
    mat3BlockMat ⁅x, y⁆ = mat3BlockMat x * mat3BlockMat y - mat3BlockMat y * mat3BlockMat x := by
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    (simp [mat3BlockMat, Bracket.bracket]; try ring)

private def mat3BlockActFun (x : Witnesses.UpperAff2) :
    NonAssocDerivation.derivations ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  ⟨{ toFun := fun M => mat3BlockMat x * M - M * mat3BlockMat x
     map_add' := fun M N => by noncomm_ring
     map_smul' := fun c M => by simp [smul_sub] },
   fun M N => by dsimp; noncomm_ring⟩

private def mat3BlockAct :
    Witnesses.UpperAff2 →ₗ⁅ℝ⁆ NonAssocDerivation.derivations ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  toFun := mat3BlockActFun
  map_add' x y := by
    apply Subtype.ext; apply LinearMap.ext; intro M
    change mat3BlockMat (x + y) * M - M * mat3BlockMat (x + y) =
      (mat3BlockMat x * M - M * mat3BlockMat x) + (mat3BlockMat y * M - M * mat3BlockMat y)
    have hadd : mat3BlockMat (x + y) = mat3BlockMat x + mat3BlockMat y := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [mat3BlockMat]
    rw [hadd]; noncomm_ring
  map_smul' c x := by
    apply Subtype.ext; apply LinearMap.ext; intro M
    change mat3BlockMat (c • x) * M - M * mat3BlockMat (c • x) =
      c • (mat3BlockMat x * M - M * mat3BlockMat x)
    have hsmul : mat3BlockMat (c • x) = c • mat3BlockMat x := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [mat3BlockMat]
    rw [hsmul, smul_mul_assoc, mul_smul_comm, ← smul_sub]
  map_lie' {x y} := by
    apply Subtype.ext; apply LinearMap.ext; intro M
    change mat3BlockMat ⁅x, y⁆ * M - M * mat3BlockMat ⁅x, y⁆ =
      (mat3BlockMat x * (mat3BlockMat y * M - M * mat3BlockMat y) -
        (mat3BlockMat y * M - M * mat3BlockMat y) * mat3BlockMat x) -
      (mat3BlockMat y * (mat3BlockMat x * M - M * mat3BlockMat x) -
        (mat3BlockMat x * M - M * mat3BlockMat x) * mat3BlockMat y)
    rw [mat3BlockMat_bracket]; noncomm_ring

private def mat3BlockLane : DerivationLieLane ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  L := Witnesses.UpperAff2
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := mat3BlockAct
  faithful := by
    intro x y h
    have hev := congrArg (fun D : NonAssocDerivation.derivations ℝ (Matrix (Fin 3) (Fin 3) ℝ) =>
      (D : Module.End ℝ (Matrix (Fin 3) (Fin 3) ℝ)) !![0, 0, 0; 0, 0, 0; 0, 1, 0]) h
    have hv := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) hev
    have hu := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 1) hev
    simp only [mat3BlockAct, LieHom.coe_mk, mat3BlockActFun, LinearMap.coe_mk, AddHom.coe_mk] at hv hu
    have hv' : x.v = y.v := by
      simpa [mat3BlockMat, Matrix.mul_apply, Fin.sum_univ_three] using hv
    have hu' : x.u = y.u := by
      simpa [mat3BlockMat, Matrix.mul_apply, Fin.sum_univ_three] using hu
    exact Witnesses.UpperAff2.ext hu' hv'

private def mat3CoupledUnit : (Matrix (Fin 3) (Fin 3) ℝ)ˣ where
  val := !![1, 1, 0; 1, 2, 0; 0, 0, 1]
  inv := !![2, -1, 0; -1, 1, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three]

private def localDiagPairUnit : Witnesses.PairMat2ˣ where
  val := (!![2, 0; 0, 1], 1)
  inv := (!![(2⁻¹ : ℝ), 0; 0, 1], 1)
  val_inv := by
    ext1
    · ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · simp
  inv_val := by
    ext1
    · ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · simp

private theorem localDiagPairUnit_mem_H : localDiagPairUnit ∈ Witnesses.witnessH := by
  change Commute localDiagPairUnit.val Witnesses.witnessP
  ext1
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [localDiagPairUnit, Witnesses.witnessP, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [localDiagPairUnit, Witnesses.witnessP]

private noncomputable def localFullMat2Lane : DerivationLieLane ℝ Witnesses.Mat2 where
  L := NonAssocDerivation.derivations ℝ Witnesses.Mat2
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := LieHom.id
  faithful := Function.injective_id

private noncomputable def localInnerMat2 (H : Witnesses.Mat2) : localFullMat2Lane.L :=
  ⟨{ toFun := fun A => H * A - A * H
     map_add' := by intro A B; noncomm_ring
     map_smul' := by intro c A; simp [smul_sub] },
    by intro A B; dsimp; noncomm_ring⟩

private def localShearMat2 : Witnesses.Mat2ˣ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private def localDiagMat2 : Witnesses.Mat2ˣ where
  val := !![2, 0; 0, 1]
  inv := !![(2⁻¹ : ℝ), 0; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Feature F9: Graded gauge/soldering splitting `θ = ϖ + e` -/

theorem t1_f9_peirce_split_flat_cartan_and_torsion
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) {P : A} (hP : P * P = P)
    (hKP : ∀ x : K.L, K.operatorAction x P = 0)
    (θ : OneForm K) (hflat : SatisfiesMaurerCartan K θ) (x y : K.L) :
    let ϖ := peirceEvenOneForm K P θ
    let e := peirceOddOneForm K P θ
    θ = ϖ + e ∧
    connectionCurvature K ϖ x y = -(e x * e y - e y * e x) ∧
    exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
      (ϖ y * e x - e x * ϖ y) = 0 := by
  have hcurv0 : connectionCurvature K θ = 0 := hflat
  exact graded_split_flat_cartan_equations K hP hKP θ hcurv0 x y

theorem t1_f9_gaugeForm_split_unconditional_cartan
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) {P : A} (hP : P * P = P)
    (hKP : ∀ x : K.L, K.operatorAction x P = 0)
    (g : Aˣ) (x y : K.L) :
    let ϖ := peirceEvenOneForm K P (gaugeForm K g)
    let e := peirceOddOneForm K P (gaugeForm K g)
    gaugeForm K g = ϖ + e ∧
    evenGrade P (ϖ x) = ϖ x ∧
    oddGrade P (e x) = e x ∧
    connectionCurvature K ϖ x y = -(e x * e y - e y * e x) ∧
    exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
      (ϖ y * e x - e x * ϖ y) = 0 := by
  have hsplit := gaugeForm_graded_split_cartan_equations K hP hKP g x y
  have hEven : evenGrade P (peirceEvenOneForm K P (gaugeForm K g) x) =
      peirceEvenOneForm K P (gaugeForm K g) x :=
    (grade_projection_laws hP (gaugeForm K g x)).1
  have hOdd : oddGrade P (peirceOddOneForm K P (gaugeForm K g) x) =
      peirceOddOneForm K P (gaugeForm K g) x :=
    (grade_projection_laws hP (gaugeForm K g x)).2.2.2.1
  exact ⟨hsplit.1, hEven, hOdd, hsplit.2.1, hsplit.2.2⟩

theorem t1_f9_parity_automorphism_matches_peirce_split
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Invertible (2 : R)]
    (K : DerivationLieLane R A) {P : A} (hP : P * P = P)
    (hKP : ∀ x : K.L, K.operatorAction x P = 0)
    (θ : OneForm K) (hflat : connectionCurvature K θ = 0) (x y : K.L) :
    let α := peirceParityAlgEquiv (R := R) P hP
    parityEvenOneForm K α θ = peirceEvenOneForm K P θ ∧
    parityOddOneForm K α θ = peirceOddOneForm K P θ ∧
    connectionCurvature K (parityEvenOneForm K α θ) x y =
      -(parityOddOneForm K α θ x * parityOddOneForm K α θ y -
        parityOddOneForm K α θ y * parityOddOneForm K α θ x) ∧
    exteriorDerivativeOne K (parityOddOneForm K α θ) x y +
      (parityEvenOneForm K α θ x * parityOddOneForm K α θ y -
        parityOddOneForm K α θ y * parityEvenOneForm K α θ x) -
      (parityEvenOneForm K α θ y * parityOddOneForm K α θ x -
        parityOddOneForm K α θ x * parityEvenOneForm K α θ y) = 0 := by
  let α := peirceParityAlgEquiv (R := R) P hP
  have hEven : parityEvenOneForm K α θ = peirceEvenOneForm K P θ :=
    parityEvenOneForm_peirceParityAlgEquiv K hP θ
  have hOdd : parityOddOneForm K α θ = peirceOddOneForm K P θ :=
    parityOddOneForm_peirceParityAlgEquiv K hP θ
  have hKα : ∀ (z : K.L) (a : A), α (K.operatorAction z a) = K.operatorAction z (α a) := by
    intro z a
    change peirceParityAlgEquiv (R := R) P hP (K.operatorAction z a) =
      K.operatorAction z (peirceParityAlgEquiv (R := R) P hP a)
    rw [peirceParityAlgEquiv_apply_eq (R := R) P hP,
      peirceParityAlgEquiv_apply_eq (R := R) P hP,
      map_sub, ← operatorAction_evenGrade_of_kill K hKP z a,
      ← operatorAction_oddGrade_of_kill K hKP z a]
  have hpar := parity_graded_split_flat_cartan_equations K α
    (peirceParityAlgEquiv_involutive (R := R) P hP) hKα θ hflat x y
  exact ⟨hEven, hOdd, hpar.2.1, hpar.2.2⟩

theorem t1_f9_grading_preserving_iff_kills_projector
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) {P : A} (hP : P * P = P) :
    ((∀ x : K.L, K.operatorAction x P = 0) ↔
      (∀ (x : K.L) (a : A),
        K.operatorAction x (evenGrade P a) = evenGrade P (K.operatorAction x a))) ∧
    ((∀ x : K.L, K.operatorAction x P = 0) →
      ∀ (x : K.L) (a : A),
        K.operatorAction x (oddGrade P a) = oddGrade P (K.operatorAction x a)) := by
  refine ⟨operatorAction_kill_iff_evenGrade K hP, ?_⟩
  intro hKP x a
  exact operatorAction_oddGrade_of_kill K hKP x a

theorem t1_f9_mat3_nonabelian_gauge_split_nonzero_curvature :
    let K := mat3BlockLane
    let D₁ : K.L := Witnesses.UpperAff2.mk 1 0
    let D₂ : K.L := Witnesses.UpperAff2.mk 0 1
    let θ := gaugeForm K mat3CoupledUnit
    let ϖ := peirceEvenOneForm K mat3PIdemp θ
    let e := peirceOddOneForm K mat3PIdemp θ
    θ = ϖ + e ∧
    connectionCurvature K ϖ D₁ D₂ = -(e D₁ * e D₂ - e D₂ * e D₁) ∧
    connectionCurvature K ϖ D₁ D₂ ≠ 0 ∧
    exteriorDerivativeOne K e D₁ D₂ + (ϖ D₁ * e D₂ - e D₂ * ϖ D₁) -
      (ϖ D₂ * e D₁ - e D₁ * ϖ D₂) = 0 := by
  let K := mat3BlockLane
  let D₁ : K.L := Witnesses.UpperAff2.mk 1 0
  let D₂ : K.L := Witnesses.UpperAff2.mk 0 1
  have hKP : ∀ d : K.L, K.operatorAction d mat3PIdemp = 0 := by
    intro d
    change mat3BlockMat d * mat3PIdemp - mat3PIdemp * mat3BlockMat d = 0
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat3BlockMat, mat3PIdemp]
  have hsplit := gaugeForm_graded_split_cartan_equations K mat3PIdemp_sq hKP mat3CoupledUnit D₁ D₂
  have he1 : peirceOddOneForm K mat3PIdemp (gaugeForm K mat3CoupledUnit) D₁ =
      !![0, -2, 0; 1, 0, 0; 0, 0, 0] := by
    change oddGrade mat3PIdemp (mat3CoupledUnit.inv *
        (mat3BlockMat D₁ * mat3CoupledUnit.val - mat3CoupledUnit.val * mat3BlockMat D₁)) =
      !![0, -2, 0; 1, 0, 0; 0, 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [oddGrade, mat3PIdemp, mat3CoupledUnit, mat3BlockMat, D₁,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]; try norm_num)
  have he2 : peirceOddOneForm K mat3PIdemp (gaugeForm K mat3CoupledUnit) D₂ =
      !![0, 0, -1; 0, 0, 0; 0, 0, 0] := by
    change oddGrade mat3PIdemp (mat3CoupledUnit.inv *
        (mat3BlockMat D₂ * mat3CoupledUnit.val - mat3CoupledUnit.val * mat3BlockMat D₂)) =
      !![0, 0, -1; 0, 0, 0; 0, 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [oddGrade, mat3PIdemp, mat3CoupledUnit, mat3BlockMat, D₂,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]; try norm_num)
  have hne : connectionCurvature K (peirceEvenOneForm K mat3PIdemp (gaugeForm K mat3CoupledUnit)) D₁ D₂ ≠ 0 := by
    rw [hsplit.2.1]
    intro hzero
    rw [he1, he2] at hzero
    have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 2) hzero
    norm_num [Matrix.mul_apply, Fin.sum_univ_three] at h12
  exact ⟨hsplit.1, hsplit.2.1, hne, hsplit.2.2⟩

/-! ## Feature F10: Soldering equivariance & nondegeneracy hypotheses -/

theorem t1_f10_isotropy_right_gauge_inhomogeneous_vs_tensorial
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) {P : A} (hP : P * P = P)
    (hKP : ∀ x : K.L, K.operatorAction x P = 0)
    (g : Aˣ) {h : Aˣ} (hh : h ∈ peirceIsotropySubgroup A P) (x : K.L) :
    peirceEvenOneForm K P (gaugeForm K (g * h)) x =
      frameTransport h (peirceEvenOneForm K P (gaugeForm K g) x) + gaugeForm K h x ∧
    peirceOddOneForm K P (gaugeForm K (g * h)) x =
      frameTransport h (peirceOddOneForm K P (gaugeForm K g) x) ∧
    oddGrade P (gaugeForm K h x) = 0 := by
  have htr := peirceSplit_gaugeForm_isotropy_transform K hP hKP g hh x
  have hev := gaugeForm_mem_even_of_isotropy K hP hKP hh x
  exact ⟨htr.1, htr.2, hev.1⟩

theorem t1_f10_soldering_frame_isomorphism_and_ker_range
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {K : DerivationLieLane R A} {P : A} {H : Subgroup Aˣ}
    (S : SolderingOneForm K P H) (x : K.L) :
    LinearMap.ker S.toOneForm = ⊥ ∧
    LinearMap.range S.toOneForm = peirceOddSubmodule R A P ∧
    Function.Bijective S.frameEquiv ∧
    ((S.frameEquiv x : peirceOddSubmodule R A P) : A) = S.toOneForm x := by
  refine ⟨S.ker_eq_bot, S.range_eq_odd, S.frameEquiv.bijective, S.frameEquiv_apply x⟩

theorem t1_f10_soldering_equivariant_action_compatibility
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {K : DerivationLieLane R A} {P : A} {H : Subgroup Aˣ}
    (S : SolderingOneForm K P H) (h₁ h₂ : H) (x : K.L) :
    S.toOneForm (S.baseRightAct (h₁ * h₂) x) =
      frameTransport (h₂.1 : Aˣ) (frameTransport (h₁.1 : Aˣ) (S.toOneForm x)) ∧
    S.toOneForm (S.baseRightAct 1 x) = S.toOneForm x := by
  refine ⟨?_, ?_⟩
  · rw [S.baseRightAct_mul, S.equivariant h₂, S.equivariant h₁]
  · rw [S.baseRightAct_one]

theorem t1_f10_witness_soldering_concrete_nontrivial_transport :
    ∃ (h : Witnesses.witnessH) (x : Witnesses.witnessLane.L),
      Witnesses.witnessSoldering.toOneForm (Witnesses.witnessSoldering.baseRightAct h x) =
        frameTransport (h.1 : Witnesses.PairMat2ˣ) (Witnesses.witnessSoldering.toOneForm x) ∧
      Witnesses.witnessSoldering.toOneForm (Witnesses.witnessSoldering.baseRightAct h x) ≠
        Witnesses.witnessSoldering.toOneForm x ∧
      Function.Bijective Witnesses.witnessSoldering.frameEquiv := by
  have hodd : oddGrade Witnesses.witnessP ((!![0, 1; 0, 0], 0) : Witnesses.PairMat2) =
      (!![0, 1; 0, 0], 0) := by
    ext1
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Witnesses.witnessP, oddGrade, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.vecMul, dotProduct]
    · simp [Witnesses.witnessP, oddGrade]
  rcases Witnesses.witnessSoldering.surjective_odd (!![0, 1; 0, 0], 0) hodd with ⟨x, hx⟩
  let h : Witnesses.witnessH := ⟨localDiagPairUnit, localDiagPairUnit_mem_H⟩
  have heq := Witnesses.witnessSoldering.equivariant h x
  refine ⟨h, x, heq, ?_, Witnesses.witnessSoldering.frameEquiv.bijective⟩
  intro hsame
  rw [heq, hx] at hsame
  have h01 := congrArg (fun p : Witnesses.PairMat2 => p.1 0 1) hsame
  norm_num [frameTransport, localDiagPairUnit, Matrix.mul_apply, Fin.sum_univ_two, h] at h01

theorem t1_f10_isotropy_preserves_peirce_subspaces
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (P : A) {h₁ h₂ : Aˣ}
    (hh₁ : h₁ ∈ peirceIsotropySubgroup A P) (hh₂ : h₂ ∈ peirceIsotropySubgroup A P)
    (a : A) :
    h₁ * h₂ ∈ peirceIsotropySubgroup A P ∧
    h₁⁻¹ ∈ peirceIsotropySubgroup A P ∧
    frameTransport h₁ (evenGrade P a) = evenGrade P (frameTransport h₁ a) ∧
    frameTransport h₁ (oddGrade P a) = oddGrade P (frameTransport h₁ a) ∧
    (a ∈ peirceOddSubmodule R A P → frameTransport h₁ a ∈ peirceOddSubmodule R A P) := by
  refine ⟨(peirceIsotropySubgroup A P).mul_mem hh₁ hh₂,
    (peirceIsotropySubgroup A P).inv_mem hh₁,
    frameTransport_evenGrade hh₁ a,
    frameTransport_oddGrade hh₁ a, ?_⟩
  intro ha
  rw [mem_peirceOddSubmodule] at ha ⊢
  rw [← frameTransport_oddGrade hh₁ a, ha]

/-! ## Feature F11: Projector differentiation & two-direction projected curvature -/

theorem t1_f11_deriv_splits_coneMinus_add_conePlus
    {A : Type*} [Ring A] {P : A} (hP : P * P = P)
    (D : A → A) (hD : ∀ a b : A, D (a * b) = D a * b + a * D b) :
    D P = coneMinus P (D P) + conePlus P (D P) ∧
    P * D P * P = 0 ∧
    (1 - P) * D P * (1 - P) = 0 ∧
    evenGrade P (D P) = 0 ∧
    oddGrade P (D P) = D P := by
  have hdiag := projector_deriv_diagonal_corners_zero hP D hD
  exact ⟨projector_deriv_peirce_split hP D hD, hdiag.1, hdiag.2,
    projector_deriv_evenGrade_zero hP D hD, projector_deriv_oddGrade_eq hP D hD⟩

theorem t1_f11_two_direction_curvature_and_complement_blocks
    {A : Type*} [Ring A] {P : A} (hP : P * P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b) :
    let X₁ := coneMinus P (D₁ P)
    let Y₁ := conePlus P (D₁ P)
    let X₂ := coneMinus P (D₂ P)
    let Y₂ := conePlus P (D₂ P)
    P * (D₁ P * D₂ P - D₂ P * D₁ P) * P = Y₁ * X₂ - Y₂ * X₁ ∧
    (1 - P) * (D₁ P * D₂ P - D₂ P * D₁ P) * (1 - P) = X₁ * Y₂ - X₂ * Y₁ ∧
    D₁ P * D₂ P - D₂ P * D₁ P = (Y₁ * X₂ - Y₂ * X₁) + (X₁ * Y₂ - X₂ * Y₁) ∧
    evenGrade P (D₁ P * D₂ P - D₂ P * D₁ P) = D₁ P * D₂ P - D₂ P * D₁ P := by
  have heven := projector_deriv_commutator_evenGrade hP D₁ D₂ hD₁ hD₂
  exact ⟨projected_two_direction_curvature hP D₁ D₂ hD₁ hD₂,
    projected_complement_two_direction_curvature hP D₁ D₂ hD₁ hD₂,
    projector_deriv_commutator_decomposition hP D₁ D₂ hD₁ hD₂,
    heven.1⟩

theorem t1_f11_derivation_lane_and_exact_oneForm_curvature
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) {P : A} (hP : P * P = P)
    (D₁ D₂ : NonAssocDerivation.derivations R A) (x y : K.L) :
    (D₁ : Module.End R A) P =
      coneMinus P ((D₁ : Module.End R A) P) + conePlus P ((D₁ : Module.End R A) P) ∧
    P * ((D₁ : Module.End R A) P * (D₂ : Module.End R A) P -
          (D₂ : Module.End R A) P * (D₁ : Module.End R A) P) * P =
      conePlus P ((D₁ : Module.End R A) P) * coneMinus P ((D₂ : Module.End R A) P) -
        conePlus P ((D₂ : Module.End R A) P) * coneMinus P ((D₁ : Module.End R A) P) ∧
    P * connectionCurvature K (exteriorDerivativeZero K P) x y * P =
      conePlus P (K.operatorAction x P) * coneMinus P (K.operatorAction y P) -
        conePlus P (K.operatorAction y P) * coneMinus P (K.operatorAction x P) := by
  exact ⟨nonAssocDerivation_projector_deriv_peirce_split hP D₁,
    nonAssocDerivation_projected_two_direction_curvature hP D₁ D₂,
    lane_projected_exactCurvature K hP x y⟩

theorem t1_f11_star_adjoint_and_cyclic_trace_specializations
    {A S : Type*} [Ring A] [StarRing A] [AddCommGroup S]
    (tr : A →+ S) (htr : ∀ a b : A, tr (a * b) = tr (b * a))
    {P : A} (hP : P * P = P) (hPs : star P = P)
    (D₁ D₂ : A → A)
    (hD₁ : ∀ a b : A, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b : A, D₂ (a * b) = D₂ a * b + a * D₂ b)
    (hD₁star : ∀ a : A, D₁ (star a) = star (D₁ a))
    (hD₂star : ∀ a : A, D₂ (star a) = star (D₂ a)) :
    star (coneMinus P (D₁ P)) = conePlus P (D₁ P) ∧
    P * (D₁ P * D₂ P - D₂ P * D₁ P) * P =
      star (coneMinus P (D₁ P)) * coneMinus P (D₂ P) -
        star (coneMinus P (D₂ P)) * coneMinus P (D₁ P) ∧
    tr (P * (D₁ P * D₂ P - D₂ P * D₁ P) * P) =
      tr (conePlus P (D₁ P) * coneMinus P (D₂ P)) -
        tr (conePlus P (D₂ P) * coneMinus P (D₁ P)) ∧
    tr (P * (D₁ P * D₂ P - D₂ P * D₁ P) * P) +
      tr ((1 - P) * (D₁ P * D₂ P - D₂ P * D₁ P) * (1 - P)) = 0 := by
  exact ⟨(star_projector_deriv_corners hPs D₁ hD₁star).1,
    projected_two_direction_curvature_star hP hPs D₁ D₂ hD₁ hD₂ hD₁star hD₂star,
    trace_projected_two_direction_curvature tr hP D₁ D₂ hD₁ hD₂,
    trace_projected_curvature_add_complement_eq_zero tr htr hP D₁ D₂ hD₁ hD₂⟩

theorem t1_f11_cl11_limit_and_mat3_star_nonzero_witnesses
    {P : Limit} (hP : P * P = P) (D₁ D₂ : limitDerivationsLane.L) :
    P * (limitDerivationsLane.operatorAction D₁ P * limitDerivationsLane.operatorAction D₂ P -
          limitDerivationsLane.operatorAction D₂ P * limitDerivationsLane.operatorAction D₁ P) * P =
      conePlus P (limitDerivationsLane.operatorAction D₁ P) *
          coneMinus P (limitDerivationsLane.operatorAction D₂ P) -
        conePlus P (limitDerivationsLane.operatorAction D₂ P) *
          coneMinus P (limitDerivationsLane.operatorAction D₁ P) ∧
    (let P₀ := ofStage 2 InfoGeometry.Examples.RealMatrixModeWitness.p
     let d₁ := InfoGeometry.Canonical.TensorLimitExactConnection.limitInnerLieHom
       (ofStage 2 InfoGeometry.Examples.RealMatrixModeWitness.x)
     let d₂ := InfoGeometry.Canonical.TensorLimitExactConnection.limitInnerLieHom
       (ofStage 2 (star InfoGeometry.Examples.RealMatrixModeWitness.x))
     P₀ * (limitDerivationsLane.operatorAction d₁ P₀ * limitDerivationsLane.operatorAction d₂ P₀ -
           limitDerivationsLane.operatorAction d₂ P₀ * limitDerivationsLane.operatorAction d₁ P₀) * P₀ ≠ 0) ∧
    (let d₁ := matrixInnerLieHom ℝ (Fin 3) mat3S1
     let d₂ := matrixInnerLieHom ℝ (Fin 3) mat3S2
     let X₁ := coneMinus mat3P ((matrixDerivationsLane ℝ (Fin 3)).operatorAction d₁ mat3P)
     let X₂ := coneMinus mat3P ((matrixDerivationsLane ℝ (Fin 3)).operatorAction d₂ mat3P)
     mat3P * ((matrixDerivationsLane ℝ (Fin 3)).operatorAction d₁ mat3P *
               (matrixDerivationsLane ℝ (Fin 3)).operatorAction d₂ mat3P -
             (matrixDerivationsLane ℝ (Fin 3)).operatorAction d₂ mat3P *
               (matrixDerivationsLane ℝ (Fin 3)).operatorAction d₁ mat3P) * mat3P =
       star X₁ * X₂ - star X₂ * X₁) := by
  exact ⟨limit_projected_two_direction_curvature hP D₁ D₂,
    limit_denseMode_projected_curvature.2,
    mat3_projected_curvature_star_ne_zero.1⟩

/-! ## Feature F12: Logarithmic derivative identity separation -/

theorem t1_f12_gaugeForm_product_and_flat_general_ring
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (g h : Aˣ) (x : K.L) :
    gaugeForm K (g * h) x = (↑h⁻¹ : A) * gaugeForm K g x * ↑h + gaugeForm K h x ∧
    connectionCurvature K (gaugeForm K g) = 0 ∧
    connectionCurvature K (gaugeForm K h) = 0 ∧
    connectionCurvature K (gaugeForm K (g * h)) = 0 := by
  exact ⟨gaugeForm_product K g h x, gaugeForm_flat K g, gaugeForm_flat K h,
    gaugeForm_flat K (g * h)⟩

theorem t1_f12_general_separation_cocycle_unit_inverse_defect
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (g h : Aˣ) (x : K.L) :
    gaugeForm K (g * h) x = frameTransport h (gaugeForm K g x) + gaugeForm K h x ∧
    gaugeForm K (1 : Aˣ) x = 0 ∧
    gaugeForm K g⁻¹ x = -((↑g : A) * gaugeForm K g x * (↑g⁻¹ : A)) ∧
    connectionCurvature K (gaugeForm K (g * h)) = 0 ∧
    gaugeForm K (g * h) x - (gaugeForm K g x + gaugeForm K h x) =
      frameTransport h (gaugeForm K g x) - gaugeForm K g x ∧
    (Commute (↑h : A) (gaugeForm K g x) →
      gaugeForm K (g * h) x = gaugeForm K g x + gaugeForm K h x) :=
  gaugeForm_product_general_separation K g h x

theorem t1_f12_triple_product_cocycle_consistency
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (g₁ g₂ g₃ : Aˣ) (x : K.L) :
    gaugeForm K ((g₁ * g₂) * g₃) x =
      frameTransport (g₂ * g₃) (gaugeForm K g₁ x) +
        frameTransport g₃ (gaugeForm K g₂ x) +
        gaugeForm K g₃ x ∧
    gaugeForm K ((g₁ * g₂) * g₃) x = gaugeForm K (g₁ * (g₂ * g₃)) x := by
  refine ⟨?_, ?_⟩
  · rw [gaugeForm_product K (g₁ * g₂) g₃ x, gaugeForm_product K g₁ g₂ x]
    change frameTransport g₃ (frameTransport g₂ (gaugeForm K g₁ x) + gaugeForm K g₂ x) +
        gaugeForm K g₃ x = _
    simp only [frameTransport, Units.val_mul, mul_inv_rev, mul_add, add_mul, mul_assoc]
  · rw [mul_assoc]

theorem t1_f12_covariant_frameTransport_and_constant_sections
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) (g : Aˣ) (x : K.L) (a b : A)
    (hb : K.operatorAction x b = 0) :
    covariantDerivative K (gaugeForm K g) x (frameTransport g a) =
      frameTransport g (K.operatorAction x a) ∧
    covariantDerivative K (gaugeForm K g) x (frameTransport g b) = 0 := by
  exact ⟨covariant_frameTransport K g x a, covariant_frameTransport_zero K g x b hb⟩

theorem t1_f12_nonabelian_mat2_retains_conjugation_and_order :
    let x := localInnerMat2 !![1, 0; 0, 0]
    gaugeForm localFullMat2Lane (localShearMat2 * localDiagMat2) x =
      (↑localDiagMat2⁻¹ : Witnesses.Mat2) * gaugeForm localFullMat2Lane localShearMat2 x *
        ↑localDiagMat2 + gaugeForm localFullMat2Lane localDiagMat2 x ∧
    gaugeForm localFullMat2Lane (localShearMat2 * localDiagMat2) x ≠
      gaugeForm localFullMat2Lane localShearMat2 x +
        gaugeForm localFullMat2Lane localDiagMat2 x ∧
    gaugeForm localFullMat2Lane (localShearMat2 * localDiagMat2) x ≠
      gaugeForm localFullMat2Lane (localDiagMat2 * localShearMat2) x ∧
    connectionCurvature localFullMat2Lane
      (gaugeForm localFullMat2Lane (localShearMat2 * localDiagMat2)) = 0 := by
  let x := localInnerMat2 !![1, 0; 0, 0]
  have hG : gaugeForm localFullMat2Lane localShearMat2 x = !![0, 1; 0, 0] := by
    rw [gaugeForm_apply]
    change localShearMat2.inv *
        (!![1, 0; 0, 0] * localShearMat2.val - localShearMat2.val * !![1, 0; 0, 0]) =
      !![0, 1; 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [localShearMat2, Matrix.mul_apply, Fin.sum_univ_two]
  have hH : gaugeForm localFullMat2Lane localDiagMat2 x = 0 := by
    rw [gaugeForm_apply]
    change localDiagMat2.inv *
        (!![1, 0; 0, 0] * localDiagMat2.val - localDiagMat2.val * !![1, 0; 0, 0]) = 0
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [localDiagMat2, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨gaugeForm_product localFullMat2Lane localShearMat2 localDiagMat2 x, ?_, ?_,
    gaugeForm_flat localFullMat2Lane (localShearMat2 * localDiagMat2)⟩
  · intro hEq
    rw [gaugeForm_product localFullMat2Lane localShearMat2 localDiagMat2 x, hG, hH, add_zero] at hEq
    have h01 := congrArg (fun M : Witnesses.Mat2 => M 0 1) hEq
    norm_num [localDiagMat2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  · intro hEq
    rw [gaugeForm_product localFullMat2Lane localShearMat2 localDiagMat2 x,
      gaugeForm_product localFullMat2Lane localDiagMat2 localShearMat2 x, hG, hH] at hEq
    have h01 := congrArg (fun M : Witnesses.Mat2 => M 0 1) hEq
    norm_num [localShearMat2, localDiagMat2, Matrix.mul_apply, Fin.sum_univ_two] at h01

end PolarizedZ2E2E.Tier1R3

section E2EAxiomAudit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in env.constants do
    if (env.getModuleIdxFor? name).isSome then continue
    if name.toString.startsWith "_private." then continue
    match info with
    | .thmInfo _ | .defnInfo _ =>
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial E2E declaration: {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in E2E declaration {name}"
      audited := audited + 1
    | .axiomInfo _ =>
      throwError "Disallowed axiom declaration in E2E file: {name}"
    | _ => pure ()
  if audited == 0 then
    throwError "E2EAxiomAudit found 0 declarations in current module"
  logInfo m!"E2E_AXIOM_AUDIT_PASS: {audited} local declarations verified"
end E2EAxiomAudit
