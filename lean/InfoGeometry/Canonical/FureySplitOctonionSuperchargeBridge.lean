/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge

/-!
# Chiral CAR supercharges on the split-octonion coordinate carrier

The finite polynomial–Fock carrier already transports to polynomial
wavefunctions tensored with the native Zorn state module. This file carries
the CAR creation/annihilation pair into the corresponding two-sheet chiral
block operators and proves their anticommutator there. The polynomial CCR
operators act on the same carrier and commute with these blocks.

The Zorn product itself is not substituted for operator composition: Zorn
elements act by the existing left-regular representation on the state factor.
-/

noncomputable section

namespace InfoGeometry.Canonical.FureySplitOctonionSuperchargeBridge

open InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge
open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation
open InfoGeometry.Twistor.RealSupertwistor
open scoped TensorProduct

local notation "Zorn" => InfoGeometry.Canonical.ZornMatrix ℝ
local notation "Wave" => WavePolynomial (Fin 3)
local notation "ZornCarrier" => WavePolynomial (Fin 3) ⊗[ℝ] Zorn
local notation "ZEnd" => Module.End ℝ ZornCarrier
local notation "ZBlock" => Matrix (Fin 2) (Fin 2) ZEnd
local notation "ZStateEnd" => Module.End ℝ Zorn

/-- Matrix units witness noncommutativity of the actual chiral block carrier. -/
def zBlockE01 : ZBlock := fun i j => if i = 0 ∧ j = 1 then 1 else 0

def zBlockE10 : ZBlock := fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem zBlock_noncommutative_witness : zBlockE01 * zBlockE10 ≠ zBlockE10 * zBlockE01 := by
  letI : Nontrivial (WavePolynomial (Fin 3) ⊗[ℝ] Zorn) := commonCarrierZorn_nontrivial
  intro h
  have h00 := congrArg (fun M : ZBlock => M 0 0) h
  have hOne : (1 : ZEnd) = 0 := by
    simpa [zBlockE01, zBlockE10, Matrix.mul_apply, Fin.sum_univ_two] using h00
  exact one_ne_zero hOne

/-! ### Zorn-realized three-mode interaction mass

The CAR operators above are left-regular operators of the split-octonion
Zorn algebra, lifted to the polynomial–Zorn state carrier. Their Majorana
sum is therefore an operator on the actual shared carrier, not a scalar
occupation model. -/

/-- The self-adjoint-generator candidate formed from one split-Zorn CAR pair. -/
def zornMajoranaMode (i : Fin 3) : ZEnd :=
  zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) +
  zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)

/-- The three-mode interaction mass on the polynomial–split-Zorn carrier. -/
def zornThreeModeMajorana : ZEnd :=
  ∑ i : Fin 3, zornMajoranaMode i

/-- A single represented split-Zorn CAR mode squares to the identity. -/
theorem zornMajoranaMode_square (i : Fin 3) :
    zornMajoranaMode i * zornMajoranaMode i = 1 := by
  let c := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i)
  let a := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)
  have hc : c * c = 0 := by
    simpa [c] using splitOctonionCommonCarrier_create_sq i
  have ha : a * a = 0 := by
    simpa [a] using splitOctonionCommonCarrier_annihilate_sq i
  have hca : a * c + c * a = 1 := by
    simpa [a, c] using splitOctonionCommonCarrier_CAR i i
  change (c + a) * (c + a) = 1
  calc
    (c + a) * (c + a) = c * c + (c * a + a * c) + a * a := by
      noncomm_ring
    _ = 1 := by rw [hc, ha]; simpa [add_comm] using hca

/-- Distinct split-Zorn Majorana modes anticommute as operators on the common
carrier. This is the cross-mode CAR relation transported through the actual
left-regular Zorn action. -/
theorem zornMajoranaMode_anticommutator_of_ne {i j : Fin 3} (hij : i ≠ j) :
    zornMajoranaMode i * zornMajoranaMode j +
      zornMajoranaMode j * zornMajoranaMode i = 0 := by
  let ci := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i)
  let ai := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)
  let cj := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j)
  let aj := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j)
  have hcc : ci * cj + cj * ci = 0 := by
    rw [zornFermionLift_mul, zornFermionLift_mul]
    change (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j).lTensor
          (WavePolynomial (Fin 3)) +
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i).lTensor
          (WavePolynomial (Fin 3)) = 0
    rw [← LinearMap.lTensor_add]
    simpa [zornFermionLift] using
      congrArg (fun T : Module.End ℝ Zorn => T.lTensor (WavePolynomial (Fin 3)))
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.regular_upper_CAR i j)
  have haa : ai * aj + aj * ai = 0 := by
    rw [zornFermionLift_mul, zornFermionLift_mul]
    change (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j).lTensor
          (WavePolynomial (Fin 3)) +
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i).lTensor
          (WavePolynomial (Fin 3)) = 0
    rw [← LinearMap.lTensor_add]
    simpa [zornFermionLift] using
      congrArg (fun T : Module.End ℝ Zorn => T.lTensor (WavePolynomial (Fin 3)))
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.regular_lower_CAR i j)
  have hca : ai * cj + cj * ai = 0 := by
    simpa [ai, cj, hij] using splitOctonionCommonCarrier_CAR i j
  have hac : aj * ci + ci * aj = 0 := by
    simpa [aj, ci, Ne.symm hij] using splitOctonionCommonCarrier_CAR j i
  have hac' : ci * aj + aj * ci = 0 := by simpa [add_comm] using hac
  change (ci + ai) * (cj + aj) + (cj + aj) * (ci + ai) = 0
  calc
    (ci + ai) * (cj + aj) + (cj + aj) * (ci + ai) =
        (ci * cj + cj * ci) + (ai * cj + cj * ai) +
          (ci * aj + aj * ci) + (ai * aj + aj * ai) := by noncomm_ring
    _ = 0 := by rw [hcc, hca, hac', haa]; simp

private theorem square_sum_of_anticommuting_involutions
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (s : Finset (Fin 3)) (T : Fin 3 → Module.End ℝ M)
    (hsq : ∀ i, T i * T i = 1)
    (hanti : ∀ i j, i ≠ j → T i * T j + T j * T i = 0) :
    (∑ i ∈ s, T i) * (∑ i ∈ s, T i) =
      (↑s.card : ℝ) • (1 : Module.End ℝ M) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hcross : T a * (∑ i ∈ s, T i) + (∑ i ∈ s, T i) * T a = 0 := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro b hb
        exact hanti a b (by
          intro hab
          subst b
          exact ha hb)
      calc
        (T a + ∑ i ∈ s, T i) * (T a + ∑ i ∈ s, T i) =
            T a * T a +
              (T a * (∑ i ∈ s, T i) + (∑ i ∈ s, T i) * T a) +
              (∑ i ∈ s, T i) * (∑ i ∈ s, T i) := by noncomm_ring
        _ = T a * T a + (∑ i ∈ s, T i) * (∑ i ∈ s, T i) := by
              rw [hcross]
              simp
        _ = (↑s.card + 1 : ℝ) • (1 : Module.End ℝ M) := by
              rw [hsq a, ih]
              simp only [add_smul, one_smul]
              abel
        _ = (↑(insert a s).card : ℝ) • (1 : Module.End ℝ M) := by
              congr 1
              simp [ha]

/-- The three Zorn CAR generators form a finite Clifford mass: the square of
their full noncommutative operator sum is the three-mode CAR value. -/
theorem zornThreeModeMajorana_square :
    zornThreeModeMajorana * zornThreeModeMajorana =
      (3 : ℝ) • (1 : ZEnd) := by
  have hsq : ∀ i : Fin 3, zornMajoranaMode i * zornMajoranaMode i = 1 :=
    zornMajoranaMode_square
  have hanti : ∀ i j : Fin 3, i ≠ j →
      zornMajoranaMode i * zornMajoranaMode j +
        zornMajoranaMode j * zornMajoranaMode i = 0 := by
    intro i j hij
    exact zornMajoranaMode_anticommutator_of_ne hij
  simpa [zornThreeModeMajorana, Finset.card_univ] using
    square_sum_of_anticommuting_involutions Finset.univ zornMajoranaMode hsq hanti

/-- The three-mode mass already has an operator on the Zorn state module;
this is the operator before its lift to polynomial–Zorn states. -/
def zornThreeModeMajoranaState : Module.End ℝ Zorn :=
  ∑ i : Fin 3,
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
      InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)

/-- The three-mode Majorana sum has its finite CAR square already on the
native split-Zorn state module, before adjoining the polynomial factor. -/
theorem zornThreeModeMajoranaState_square :
    zornThreeModeMajoranaState * zornThreeModeMajoranaState =
      (3 : ℝ) • (1 : ZStateEnd) := by
  have hsq : ∀ i : Fin 3,
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) *
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) = 1 := by
    intro i
    have hcc := InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.regular_upper_CAR i i
    have haa := InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.regular_lower_CAR i i
    have hca := InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.regular_mixed_CAR i i
    have hca' : InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i +
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i = 1 := by
      simpa using hca
    have ht : (2 : ℝ) ≠ 0 := by norm_num
    have hcc2 : (2 : ℝ) •
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) = 0 := by
      simpa [two_smul] using hcc
    have haa2 : (2 : ℝ) •
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) = 0 := by
      simpa [two_smul] using haa
    have hcc' : InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i = 0 :=
      (smul_eq_zero.mp hcc2).resolve_left ht
    have haa' : InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i = 0 :=
      (smul_eq_zero.mp haa2).resolve_left ht
    calc
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) *
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) =
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
            (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
                InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i +
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
                InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) +
            InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i := by
                noncomm_ring
      _ = 1 := by rw [hcc', haa', hca']; simp
  have hanti : ∀ i j : Fin 3, i ≠ j →
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) *
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j +
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j) +
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j +
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j) *
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) = 0 := by
    intro i j hij
    have hcc := InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.regular_upper_CAR i j
    have haa := InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.regular_lower_CAR i j
    have hca := InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.regular_mixed_CAR i j
    have hac := InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.regular_mixed_CAR j i
    have hca' : InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j +
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j *
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i = 0 := by
      simpa [hij] using hca
    have hac' : InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i +
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j = 0 := by
      simpa [Ne.symm hij] using hac
    have hac'' : InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j +
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j *
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i = 0 := by
      simpa [add_comm] using hac'
    calc
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) *
          (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j +
            InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j) +
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j +
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j) *
          (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
            InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) =
          (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j +
            InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) +
          (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j +
            InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) +
          (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j +
            InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create j *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) +
          (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j +
            InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j *
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) := by
                noncomm_ring
      _ = 0 := by rw [hcc, hca', hac'', haa]; simp
  simpa [zornThreeModeMajoranaState, Finset.card_univ] using
    square_sum_of_anticommuting_involutions Finset.univ
      (fun i : Fin 3 =>
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) hsq hanti

private theorem polynomialFactor_identity_lift :
    (1 : Module.End ℝ ZornCarrier) =
      (1 : Module.End ℝ Wave).rTensor Zorn := by
  change (LinearMap.id : ZornCarrier →ₗ[ℝ] ZornCarrier) =
    (LinearMap.id : Wave →ₗ[ℝ] Wave).rTensor Zorn
  rw [LinearMap.rTensor_id]

/-- The unified CCR–CAR algebra representation sends the pure CAR mass tensor
to the three-mode Majorana operator on the common polynomial–Zorn carrier. -/
theorem splitOctonionCARCCRRepresentation_majorana_mass :
    splitOctonionCARCCRRepresentation
        ((1 : Module.End ℝ Wave) ⊗ₜ[ℝ] zornThreeModeMajoranaState) =
      zornThreeModeMajorana := by
  calc
    splitOctonionCARCCRRepresentation
        ((1 : Module.End ℝ Wave) ⊗ₜ[ℝ] zornThreeModeMajoranaState) =
        ((1 : Module.End ℝ Wave).rTensor Zorn) *
          (zornThreeModeMajoranaState.lTensor Wave) := by
            rw [splitOctonionCARCCRRepresentation_tmul]
    _ = zornThreeModeMajorana := by
      rw [← polynomialFactor_identity_lift, one_mul]
      change (Module.End.lTensorAlgHom ℝ Zorn Wave)
          zornThreeModeMajoranaState = _
      simp only [map_sum, map_add, zornThreeModeMajoranaState,
        zornThreeModeMajorana, zornMajoranaMode, zornFermionLift]
      apply Finset.sum_congr rfl
      intro i hi
      rfl

/-- Every polynomial operator on the first factor commutes with the represented
three-mode mass. In particular, all polynomial CCR generators commute with
the split-Zorn Majorana interaction on this same carrier. -/
theorem polynomial_operator_commutes_with_zorn_majorana_mass
    (A : Module.End ℝ Wave) :
    (A.rTensor Zorn) * zornThreeModeMajorana =
      zornThreeModeMajorana * (A.rTensor Zorn) := by
  rw [← splitOctonionCARCCRRepresentation_majorana_mass]
  rw [splitOctonionCARCCRRepresentation_tmul]
  rw [← polynomialFactor_identity_lift, one_mul]
  change (A.rTensor Zorn).comp (zornThreeModeMajoranaState.lTensor Wave) =
    (zornThreeModeMajoranaState.lTensor Wave).comp (A.rTensor Zorn)
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- Positive chiral supercharge on the polynomial–Zorn carrier, with the
existing left-regular creation operator in its upper-right block. -/
def zornChiralQPlus (i : Fin 3) : ZBlock :=
  !![0, zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i); 0, 0]

/-- Negative chiral supercharge on the polynomial–Zorn carrier, with the
existing left-regular annihilation operator in its lower-left block. -/
def zornChiralQMinus (i : Fin 3) : ZBlock :=
  !![0, 0; zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i), 0]

/-- The chiral supercharge anticommutator closes on the two ordered CAR
partner products in the diagonal blocks. The products remain operator-valued
and retain their order. -/
theorem zorn_chiral_supercharge_anticommutator (i j : Fin 3) :
    zornChiralQPlus i * zornChiralQMinus j +
      zornChiralQMinus j * zornChiralQPlus i =
        !![zornFermionLift
             (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i *
               InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j), 0;
           0, zornFermionLift
             (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate j *
               InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i)] := by
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c
  · simp [zornChiralQPlus, zornChiralQMinus, Matrix.mul_apply,
      zornFermionLift_mul]
  · simp [zornChiralQPlus, zornChiralQMinus, Matrix.mul_apply,
      zornFermionLift_mul]
  · simp [zornChiralQPlus, zornChiralQMinus, Matrix.mul_apply,
      zornFermionLift_mul]
  · simp [zornChiralQPlus, zornChiralQMinus, Matrix.mul_apply,
      zornFermionLift_mul]

/-- On a matching mode, the two diagonal products in the chiral-supercharge
anticommutator are complementary operator projections on the shared
polynomial–Zorn carrier. No scalar occupation-number reduction is made. -/
theorem zorn_chiral_CAR_partner_products_are_complementary_projections (i : Fin 3) :
    let c := zornFermionLift
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i)
    let a := zornFermionLift
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)
    let p := c * a
    let q := a * c
    p * p = p ∧ q * q = q ∧ p * q = 0 ∧ q * p = 0 ∧ p + q = 1 := by
  let c := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i)
  let a := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)
  let p := c * a
  let q := a * c
  have hc : c * c = 0 := by
    simpa [c] using splitOctonionCommonCarrier_create_sq i
  have ha : a * a = 0 := by
    simpa [a] using splitOctonionCommonCarrier_annihilate_sq i
  have hCAR : a * c + c * a = 1 := by
    simpa [a, c] using splitOctonionCommonCarrier_CAR i i
  have hAC : a * c = 1 - c * a := by
    calc
      a * c = (a * c + c * a) - c * a := by abel
      _ = 1 - c * a := by rw [hCAR]
  have hCA : c * a = 1 - a * c := by
    calc
      c * a = (a * c + c * a) - a * c := by abel
      _ = 1 - a * c := by rw [hCAR]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (c * a) * (c * a) = c * a
    calc
      (c * a) * (c * a) = (c * a) * (c * a) + (c * c) * (a * a) := by
        rw [hc]
        simp
      _ = c * (a * c + c * a) * a := by noncomm_ring
      _ = c * a := by rw [hCAR]; simp
  · change (a * c) * (a * c) = a * c
    calc
      (a * c) * (a * c) = (a * a) * (c * c) + (a * c) * (a * c) := by
        rw [ha]
        simp
      _ = a * (a * c + c * a) * c := by noncomm_ring
      _ = a * c := by rw [hCAR]; simp
  · change (c * a) * (a * c) = 0
    calc
      (c * a) * (a * c) = c * (a * a) * c := by noncomm_ring
      _ = 0 := by
        calc c * a * a * c = c * (a * a) * c := by simp only [mul_assoc]
          _ = 0 := by rw [ha]; simp
  · change (a * c) * (c * a) = 0
    calc
      (a * c) * (c * a) = a * (c * c) * a := by noncomm_ring
      _ = 0 := by
        calc a * c * c * a = a * (c * c) * a := by simp only [mul_assoc]
          _ = 0 := by rw [hc]; simp
  · change c * a + a * c = 1
    simpa [add_comm] using hCAR

/-- The finite CAR relation appears as the trace of the two diagonal chiral
partner operators. The anticommutator itself is the ordered particle/hole
block diagonal given above, not the identity matrix. -/
theorem zorn_chiral_supercharge_trace_is_identity (i : Fin 3) :
    Matrix.trace
      (zornChiralQPlus i * zornChiralQMinus i +
        zornChiralQMinus i * zornChiralQPlus i) = 1 := by
  rw [zorn_chiral_supercharge_anticommutator]
  simp only [Matrix.trace, Fin.sum_univ_two]
  rw [← zornFermionLift_mul, ← zornFermionLift_mul]
  simpa [add_comm] using splitOctonionCommonCarrier_CAR i i

/-- The polynomial–Zorn state vector obtained by adjoining a polynomial
wavefunction to the native split-octonion CAR vacuum. -/
def polynomialZornVacuumState : WavePolynomial (Fin 3) →ₗ[ℝ] ZornCarrier where
  toFun p := p ⊗ₜ[ℝ]
    (InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ))
  map_add' p q := by rw [TensorProduct.add_tmul]
  map_smul' r p := by exact (TensorProduct.smul_tmul' r p
    (InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ))).symm

/-- The tensor lift of the actual three-mode Zorn vacuum projector. -/
def polynomialZornVacuumProjection : ZEnd :=
  zornFermionLift
    InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.vacuumProjector

/-- The lifted CAR vacuum projector is idempotent on the full shared
polynomial–Zorn carrier. -/
theorem polynomialZornVacuumProjection_idempotent :
    polynomialZornVacuumProjection * polynomialZornVacuumProjection =
      polynomialZornVacuumProjection := by
  change zornFermionLift vacuumProjector * zornFermionLift vacuumProjector =
    zornFermionLift vacuumProjector
  rw [zornFermionLift_mul, vacuumProjector_idempotent]

/-- The range of the lifted CAR vacuum projector is exactly the polynomial
wavefunction module tensored with the actual rank-one split-Zorn vacuum line.
This identifies the state sector as an operator range on the common carrier. -/
theorem polynomialZornVacuumProjection_range :
    LinearMap.range polynomialZornVacuumProjection =
      LinearMap.range polynomialZornVacuumState := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine TensorProduct.inductionOn x (fun p ψ => ?_) (fun x y hx hy => ?_)
    · refine ⟨ψ.b • p, ?_⟩
      simp [polynomialZornVacuumProjection, zornFermionLift,
        polynomialZornVacuumState,
        InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.vacuumProjector_apply]
    · simpa only [map_add] using add_mem hx hy
  · rintro y ⟨p, rfl⟩
    refine ⟨polynomialZornVacuumState p, ?_⟩
    simp [polynomialZornVacuumProjection, zornFermionLift,
      polynomialZornVacuumState,
      InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.vacuumProjector_apply,
      InfoGeometry.Canonical.ZornMatrix.zornMinus]

/-- Polynomial creation and annihilation commute with both chiral CAR blocks
after the exterior state coordinates are transported to split-octonion Zorn
coordinates. This is the CCR/CAR tensor-factor separation on one carrier. -/
theorem polynomial_CCR_commutes_with_zorn_chiral_supercharges
    (b : Operator (Fin 3)) (i : Fin 3) :
    !![transportCommonCarrierEnd
         (InfoGeometry.Twistor.RealSupertwistor.bosonLift
           (Fin 3) (Fin 3 → ℝ) b), 0;
       0, transportCommonCarrierEnd
         (InfoGeometry.Twistor.RealSupertwistor.bosonLift
           (Fin 3) (Fin 3 → ℝ) b)] *
        zornChiralQPlus i =
      zornChiralQPlus i *
        !![transportCommonCarrierEnd
            (InfoGeometry.Twistor.RealSupertwistor.bosonLift
              (Fin 3) (Fin 3 → ℝ) b), 0;
          0, transportCommonCarrierEnd
            (InfoGeometry.Twistor.RealSupertwistor.bosonLift
              (Fin 3) (Fin 3 → ℝ) b)] ∧
    !![transportCommonCarrierEnd
         (InfoGeometry.Twistor.RealSupertwistor.bosonLift
           (Fin 3) (Fin 3 → ℝ) b), 0;
       0, transportCommonCarrierEnd
         (InfoGeometry.Twistor.RealSupertwistor.bosonLift
           (Fin 3) (Fin 3 → ℝ) b)] *
        zornChiralQMinus i =
      zornChiralQMinus i *
        !![transportCommonCarrierEnd
            (InfoGeometry.Twistor.RealSupertwistor.bosonLift
              (Fin 3) (Fin 3 → ℝ) b), 0;
          0, transportCommonCarrierEnd
            (InfoGeometry.Twistor.RealSupertwistor.bosonLift
              (Fin 3) (Fin 3 → ℝ) b)] := by
  constructor <;> apply Matrix.ext <;> intro r c <;> fin_cases r <;> fin_cases c
  · simp [zornChiralQPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · simpa [zornChiralQPlus, Matrix.mul_apply, Fin.sum_univ_two] using
      transported_polynomial_operator_commutes_with_splitZorn_operator b
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i)
  · simp [zornChiralQPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [zornChiralQPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [zornChiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [zornChiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · simpa [zornChiralQMinus, Matrix.mul_apply, Fin.sum_univ_two] using
      transported_polynomial_operator_commutes_with_splitZorn_operator b
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)
  · simp [zornChiralQMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The polynomial CCR action commutes with the full three-mode interaction
mass, not only with each individual chiral supercharge. -/
theorem polynomial_CCR_commutes_with_zorn_three_mode_mass
    (b : Operator (Fin 3)) :
    transportCommonCarrierEnd
        (InfoGeometry.Twistor.RealSupertwistor.bosonLift
          (Fin 3) (Fin 3 → ℝ) b) * zornThreeModeMajorana =
      zornThreeModeMajorana * transportCommonCarrierEnd
        (InfoGeometry.Twistor.RealSupertwistor.bosonLift
          (Fin 3) (Fin 3 → ℝ) b) := by
  rw [transported_bosonLift_eq_rTensor]
  exact polynomial_operator_commutes_with_zorn_majorana_mass b

end InfoGeometry.Canonical.FureySplitOctonionSuperchargeBridge

end
