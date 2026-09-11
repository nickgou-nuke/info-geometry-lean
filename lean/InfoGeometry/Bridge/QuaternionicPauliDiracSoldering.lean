import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Canonical.BiQuaternionKahlerFinite

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
      Matrix.one_apply, Fin.sum_univ_two] <;> ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

theorem cosoldering_mul_soldering (P : PauliParavector) :
    coSolderingMap P * P.pauliMatrix =
      (P.minkowskiNormSq : ℂ) • (1 : PauliBlock) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PauliParavector.pauliMatrix, coSolderingMap,
      PauliParavector.minkowskiNormSq, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_two] <;> ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

def chiralWeylOperator (A B : PauliBlock) : Module.End ℂ DiracSpinor where
  toFun ψ := (A *ᵥ ψ.2, B *ᵥ ψ.1)
  map_add' := by intro x y; ext <;> simp [Matrix.mulVec_add]
  map_smul' := by intro c x; ext <;> simp [Matrix.mulVec_smul]

theorem chiralWeylOperator_sq_apply (A B : PauliBlock) (ψ : DiracSpinor) :
    chiralWeylOperator A B (chiralWeylOperator A B ψ) =
      ((A * B) *ᵥ ψ.1, (B * A) *ᵥ ψ.2) := by
  rcases ψ with ⟨ψL, ψR⟩
  apply Prod.ext <;> simp [chiralWeylOperator, Matrix.mulVec_mulVec]

theorem soldered_chiralWeylOperator_sq_apply
    (P : PauliParavector) (ψ : DiracSpinor) :
    chiralWeylOperator P.pauliMatrix (coSolderingMap P)
        (chiralWeylOperator P.pauliMatrix (coSolderingMap P) ψ) =
      (P.minkowskiNormSq : ℂ) • ψ := by
  rw [chiralWeylOperator_sq_apply, soldering_mul_cosoldering,
    cosoldering_mul_soldering]
  rcases ψ with ⟨ψL, ψR⟩
  ext i <;> simp [Matrix.smul_mulVec]

namespace QuaternionicOperators

open InfoGeometry.Canonical.BiQuaternionKahlerFinite

abbrev Carrier := R4
def I : Module.End ℝ Carrier := I4c.mulVecLin
def J : Module.End ℝ Carrier := J4c.mulVecLin
def K : Module.End ℝ Carrier := K4c.mulVecLin

theorem I_comp_J : I.comp J = K := by
  apply LinearMap.ext
  intro x
  change I4c.mulVec (J4c.mulVec x) = K4c.mulVec x
  calc
    I4c.mulVec (J4c.mulVec x) = (I4c * J4c).mulVec x := by
      rw [Matrix.mulVec_mulVec]
    _ = K4c.mulVec x := by rw [I4c_mul_J4c]

theorem commute_third_quaternionic_axis
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
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
      simp [mul_add, mul_smul_comm]
    _ = a • (I * N) + b • (J * N) + c • (K * N) := by rw [hNI, hNJ, hNK]
    _ = (a • I + b • J + c • K) * N := by simp [add_mul, smul_mul_assoc]

end QuaternionicOperators
end InfoGeometry.Bridge.QuaternionicPauliDiracSoldering
