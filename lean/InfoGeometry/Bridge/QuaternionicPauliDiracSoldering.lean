/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BiQuaternionKahlerFinite
import InfoGeometry.Canonical.PauliHestenesSpinMomentum


/-!
# Quaternionic Pauli--Dirac soldering

This is the native bridge between the existing Pauli paravector carrier and
the existing finite quaternionic operator carrier.  It records only finite
algebraic identities; no analytic Dirac operator or curved connection is
introduced.
-/

noncomputable section

namespace InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

open Matrix
open scoped Matrix
open InfoGeometry.Canonical.PauliHestenesSpinMomentum

abbrev PauliBlock := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev WeylSpinor := InfoGeometry.Algebra.FiniteSpin.Vec2C
abbrev DiracSpinor := WeylSpinor × WeylSpinor

def coSolderingMap (P : PauliParavector) : PauliBlock :=
  !![((P.energy - P.pz : ℝ) : ℂ),
      ((-P.px : ℂ) + Complex.I * (P.py : ℂ));
     ((-P.px : ℂ) - Complex.I * (P.py : ℂ)),
      ((P.energy + P.pz : ℝ) : ℂ)]

theorem coSolderingMap_det (P : PauliParavector) :
    Matrix.det (coSolderingMap P) = (P.minkowskiNormSq : ℂ) := by
  simp [coSolderingMap, PauliParavector.minkowskiNormSq,
    Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem soldering_mul_cosoldering (P : PauliParavector) :
    P.pauliMatrix * coSolderingMap P =
      (P.minkowskiNormSq : ℂ) • (1 : PauliBlock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PauliParavector.pauliMatrix, coSolderingMap,
      PauliParavector.minkowskiNormSq, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

theorem cosoldering_mul_soldering (P : PauliParavector) :
    coSolderingMap P * P.pauliMatrix =
      (P.minkowskiNormSq : ℂ) • (1 : PauliBlock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PauliParavector.pauliMatrix, coSolderingMap,
      PauliParavector.minkowskiNormSq, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

def chiralWeylOperator (A B : PauliBlock) : Module.End ℂ DiracSpinor where
  toFun ψ := (A *ᵥ ψ.2, B *ᵥ ψ.1)
  map_add' x y := by
    apply Prod.ext
    · dsimp; rw [mulVec_add]
    · dsimp; rw [mulVec_add]
  map_smul' c x := by
    apply Prod.ext
    · dsimp; rw [mulVec_smul]
    · dsimp; rw [mulVec_smul]

theorem chiralWeylOperator_sq_apply (A B : PauliBlock) (ψ : DiracSpinor) :
    chiralWeylOperator A B (chiralWeylOperator A B ψ) =
      ((A * B) *ᵥ ψ.1, (B * A) *ᵥ ψ.2) := by
  apply Prod.ext
  · dsimp [chiralWeylOperator]; rw [mulVec_mulVec]
  · dsimp [chiralWeylOperator]; rw [mulVec_mulVec]

theorem soldered_chiralWeylOperator_sq_apply
    (P : PauliParavector) (ψ : DiracSpinor) :
    chiralWeylOperator P.pauliMatrix (coSolderingMap P)
        (chiralWeylOperator P.pauliMatrix (coSolderingMap P) ψ) =
      (P.minkowskiNormSq : ℂ) • ψ := by
  rw [chiralWeylOperator_sq_apply, soldering_mul_cosoldering,
    cosoldering_mul_soldering]
  rcases ψ with ⟨ψL, ψR⟩
  ext i <;> simp [Matrix.smul_mulVec]



/-- The Pauli chirality grading and its Peirce/circular generators. -/
def chirality : PauliBlock := !![(1 : ℂ), 0; 0, -1]
def chiralPlus : PauliBlock := !![(1 : ℂ), 0; 0, 0]
def chiralMinus : PauliBlock := !![(0 : ℂ), 0; 0, 1]
def circularPlus : PauliBlock := !![(0 : ℂ), 1; 0, 0]
def circularMinus : PauliBlock := !![(0 : ℂ), 0; 1, 0]

theorem coSolderingMap_isHermitian (P : PauliParavector) :
    (coSolderingMap P).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coSolderingMap, Matrix.conjTranspose_apply, Complex.conj_I] <;> ring

theorem chirality_sq : chirality * chirality = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [chirality, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralPlus_sq : chiralPlus * chiralPlus = chiralPlus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiralMinus_sq : chiralMinus * chiralMinus = chiralMinus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [chiralMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem chiral_projectors_complete : chiralPlus + chiralMinus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chiralPlus, chiralMinus]

theorem chiral_projectors_orthogonal :
    chiralPlus * chiralMinus = 0 ∧ chiralMinus * chiralPlus = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, chiralMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem circularPlus_sq_zero : circularPlus * circularPlus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [circularPlus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem circularMinus_sq_zero : circularMinus * circularMinus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [circularMinus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem circular_car :
    circularPlus * circularMinus + circularMinus * circularPlus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [circularPlus, circularMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem circular_peirce_transport :
    chiralPlus * circularPlus * chiralMinus = circularPlus ∧
    chiralMinus * circularMinus * chiralPlus = circularMinus := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [chiralPlus, chiralMinus, circularPlus, circularMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem chirality_circular_commutators :
    chirality * circularPlus - circularPlus * chirality = (2 : ℂ) • circularPlus ∧
    chirality * circularMinus - circularMinus * chirality = (-2 : ℂ) • circularMinus := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [chirality, circularPlus, circularMinus, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num


namespace QuaternionicOperators

open InfoGeometry.Canonical.BiQuaternionKahlerFinite

abbrev Carrier := R4
def I : Module.End ℝ Carrier := I4c.mulVecLin
def J : Module.End ℝ Carrier := J4c.mulVecLin
def K : Module.End ℝ Carrier := K4c.mulVecLin

@[simp] theorem I_sq : I.comp I = -(LinearMap.id : Module.End ℝ Carrier) := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Canonical.BiQuaternionKahlerFinite.I4c.mulVec
      (InfoGeometry.Canonical.BiQuaternionKahlerFinite.I4c.mulVec x) = -x
  rw [mulVec_mulVec, InfoGeometry.Canonical.BiQuaternionKahlerFinite.I4c_sq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem J_sq : J.comp J = -(LinearMap.id : Module.End ℝ Carrier) := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Canonical.BiQuaternionKahlerFinite.J4c.mulVec
      (InfoGeometry.Canonical.BiQuaternionKahlerFinite.J4c.mulVec x) = -x
  rw [mulVec_mulVec, InfoGeometry.Canonical.BiQuaternionKahlerFinite.J4c_sq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem K_sq : K.comp K = -(LinearMap.id : Module.End ℝ Carrier) := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Canonical.BiQuaternionKahlerFinite.K4c.mulVec
      (InfoGeometry.Canonical.BiQuaternionKahlerFinite.K4c.mulVec x) = -x
  rw [mulVec_mulVec, InfoGeometry.Canonical.BiQuaternionKahlerFinite.K4c_sq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem J_comp_I : J.comp I = -K := by
  apply LinearMap.ext
  intro x
  change InfoGeometry.Canonical.BiQuaternionKahlerFinite.J4c.mulVec
      (InfoGeometry.Canonical.BiQuaternionKahlerFinite.I4c.mulVec x) =
    -(InfoGeometry.Canonical.BiQuaternionKahlerFinite.K4c.mulVec x)
  rw [mulVec_mulVec, InfoGeometry.Canonical.BiQuaternionKahlerFinite.J4c_mul_I4c]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]


theorem I_comp_J : I.comp J = K := by
  apply LinearMap.ext
  intro x
  change I4c.mulVec (J4c.mulVec x) = K4c.mulVec x
  calc
    I4c.mulVec (J4c.mulVec x) = (I4c * J4c).mulVec x := by
      rw [mulVec_mulVec]
    _ = K4c.mulVec x := by rw [I4c_mul_J4c]

theorem commute_third_quaternionic_axis
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    {I J K N : Module.End R V}
    (hK : I * J = K) (hNI : N * I = I * N) (hNJ : N * J = J * N) :
    N * K = K * N := by
  calc
    N * K = N * (I * J) := by rw [hK]
    _ = (N * I) * J := by rw [mul_assoc]
    _ = (I * N) * J := by rw [hNI]
    _ = I * (N * J) := by rw [← mul_assoc]
    _ = I * (J * N) := by rw [hNJ]
    _ = K * N := by rw [← mul_assoc, hK]

theorem commute_every_quaternionic_axis_of_two
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    (a b c : R) {I J K N : Module.End R V}
    (hK : I * J = K) (hNI : N * I = I * N) (hNJ : N * J = J * N) :
    N * (a • I + b • J + c • K) =
      (a • I + b • J + c • K) * N := by
  have hNK := commute_third_quaternionic_axis hK hNI hNJ
  calc
    N * (a • I + b • J + c • K) =
        a • (N * I) + b • (N * J) + c • (N * K) := by
      simp [mul_add]
    _ = a • (I * N) + b • (J * N) + c • (K * N) := by rw [hNI, hNJ, hNK]
    _ = (a • I + b • J + c • K) * N := by simp [add_mul]

end QuaternionicOperators
end InfoGeometry.Bridge.QuaternionicPauliDiracSoldering
