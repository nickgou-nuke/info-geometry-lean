/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
import InfoGeometry.Clifford.ExteriorZornCARIntertwiner
import InfoGeometry.Physics.BdGChiralBlockMatrix

/-!
# Finite-mode CAR–CCR supertwistor carrier in split-octonion Fock coordinates

`Furey` in this module name records the motivating repository lane. The results below
formalize finite-mode carrier transport, not a particle model or gauge representation.

The polynomial/exterior carrier carries exact polynomial CCR and a three-mode
CAR action. Its mode count and CAR factor are finite, while the polynomial
wavefunction factor has unbounded degree and is not a finite-dimensional
truncation of the CCR. Finite-dimensional CCR approximants instead retain a
boundary commutator defect, as proved by `FiniteTwistorCCRGeneratingFunction`;
`CounterexampleAlternatives.finite_matrix_ccr_impossible` rules out exact
characteristic-zero CCR in finite matrix algebras. The exterior factor is
linearly equivalent to the native split-octonion Zorn state carrier, with
creation and contraction intertwined by left-regular split-octonion
operators. Tensoring this equivalence with the identity on polynomial
wavefunctions transports the CAR operators on the whole carrier. This is a
state-space equivalence; it does not identify the nonassociative Zorn product
with exterior multiplication.
-/

noncomputable section

namespace InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge

open scoped TensorProduct
open InfoGeometry.Twistor.RealSupertwistor
open InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
open InfoGeometry.Clifford.ExteriorZornCARIntertwiner
open InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation
open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

local notation "Zorn" => InfoGeometry.Canonical.ZornMatrix ℝ
local notation "Wave" => WavePolynomial (Fin 3)
local notation "Fock" => SuperWave (Fin 3) V3
local notation "JointZorn" => Wave ⊗[ℝ] Zorn

/-- Re-express the three-mode exterior factor as the native Zorn state space,
without changing the polynomial wavefunction factor. -/
def commonCarrierZornEquiv : Fock ≃ₗ[ℝ] JointZorn :=
  TensorProduct.congr (LinearEquiv.refl ℝ Wave) exteriorZornCARLinearEquiv

@[simp] theorem commonCarrierZornEquiv_tmul (p : Wave) (ψ : Exterior3) :
    commonCarrierZornEquiv (p ⊗ₜ[ℝ] ψ) = p ⊗ₜ[ℝ] fockToZorn ψ := by
  change p ⊗ₜ[ℝ] fockToZorn ψ = p ⊗ₜ[ℝ] fockToZorn ψ
  rfl

/-- Left-regular Zorn operators act on the second tensor factor of the
re-expressed finite carrier. -/
def zornFermionLift (T : Module.End ℝ Zorn) : Module.End ℝ JointZorn :=
  T.lTensor Wave

/-- The polynomial–Zorn carrier is nontrivial. Flatness of the polynomial
module preserves the embedded scalar line in the Zorn factor. -/
theorem commonCarrierZorn_nontrivial : Nontrivial JointZorn := by
  let pole := InfoGeometry.Canonical.ZornMatrix.zornMinus (R := ℝ)
  have hpole : pole ≠ (0 : Zorn) := by
    intro h
    have hb := congrArg (fun z : Zorn => z.b) h
    norm_num [pole, InfoGeometry.Canonical.ZornMatrix.zornMinus] at hb
  let scalarLine : ℝ →ₗ[ℝ] Zorn :=
    { toFun := fun r => r • pole
      map_add' := by intro r s; simp [add_smul]
      map_smul' := by intro r s; simp [mul_smul] }
  have hscalarLine : Function.Injective scalarLine := by
    intro r s hrs
    have hzero : (r - s) • pole = 0 := by
      have hscaled : r • pole = s • pole := hrs
      change r • pole = s • pole at hscaled
      rw [sub_smul, hscaled, sub_self]
    rcases smul_eq_zero.mp hzero with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact (hpole hzero).elim
  exact TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
    ℝ Wave Zorn scalarLine hscalarLine

/-- Transport an endomorphism of the common exterior carrier through the
state-space equivalence. -/
def transportCommonCarrierEnd (T : Module.End ℝ Fock) :
    Module.End ℝ JointZorn :=
  (commonCarrierZornEquiv.conjAlgEquiv ℝ) T

/-- The bosonic polynomial operator algebra and the associative algebra of
split-Zorn CAR operators act together through one algebra representation on
the already-owned polynomial–Zorn carrier. The underlying Zorn algebra is
only a state carrier here; multiplication in the represented algebra is
composition of endomorphisms. -/
noncomputable def splitOctonionCARCCRRepresentation :
    (Module.End ℝ Wave ⊗[ℝ] Module.End ℝ Zorn) →ₐ[ℝ]
      Module.End ℝ JointZorn :=
  Algebra.TensorProduct.lift
    (Module.End.rTensorAlgHom ℝ Wave Zorn)
    (Module.End.lTensorAlgHom ℝ Zorn Wave)
    (by
      intro b T
      change (b.rTensor Zorn).comp (T.lTensor Wave) =
        (T.lTensor Wave).comp (b.rTensor Zorn)
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])

/-- On elementary tensors, the unified representation is the product of the
wavefunction-side CCR action and state-side Zorn CAR action. -/
@[simp] theorem splitOctonionCARCCRRepresentation_tmul
    (b : Module.End ℝ Wave) (T : Module.End ℝ Zorn) :
    splitOctonionCARCCRRepresentation (b ⊗ₜ[ℝ] T) =
      (b.rTensor Zorn) * (T.lTensor Wave) := by
  exact Algebra.TensorProduct.lift_tmul
    (Module.End.rTensorAlgHom ℝ Wave Zorn)
    (Module.End.lTensorAlgHom ℝ Zorn Wave) _ b T

/-- Bosonic endomorphisms on the polynomial–exterior carrier transport to the
right tensor-factor action on the polynomial–Zorn carrier. -/
theorem transported_bosonLift_eq_rTensor (A : Operator (Fin 3)) :
    transportCommonCarrierEnd (bosonLift (Fin 3) V3 A) = A.rTensor Zorn := by
  apply LinearMap.ext
  intro x
  change commonCarrierZornEquiv
      (bosonLift (Fin 3) V3 A (commonCarrierZornEquiv.symm x)) =
    A.rTensor Zorn x
  refine TensorProduct.inductionOn x (fun p ψ => ?_) (fun x y hx hy => ?_)
  · have hsymm : commonCarrierZornEquiv.symm (p ⊗ₜ[ℝ] ψ) =
        p ⊗ₜ[ℝ] exteriorZornCARLinearEquiv.symm ψ := by
      change p ⊗ₜ[ℝ] exteriorZornCARLinearEquiv.symm ψ = _
      rfl
    rw [hsymm]
    simp only [bosonLift_tmul, commonCarrierZornEquiv_tmul,
      LinearMap.rTensor_tmul]
    change A p ⊗ₜ[ℝ]
      exteriorZornCARLinearEquiv (exteriorZornCARLinearEquiv.symm ψ) = _
    rw [exteriorZornCARLinearEquiv.apply_symm_apply]
  · simp only [map_add, hx, hy]

/-- Polynomial operators remain on the wavefunction factor after the
exterior-to-Zorn state transport.  Consequently they commute with every
operator acting on the native split-Zorn state factor. -/
theorem transported_polynomial_operator_commutes_with_splitZorn_operator
    (A : Operator (Fin 3)) (T : Module.End ℝ Zorn) :
    transportCommonCarrierEnd (bosonLift (Fin 3) V3 A) * zornFermionLift T =
      zornFermionLift T * transportCommonCarrierEnd (bosonLift (Fin 3) V3 A) := by
  rw [transported_bosonLift_eq_rTensor]
  change (A.rTensor Zorn).comp (T.lTensor Wave) =
    (T.lTensor Wave).comp (A.rTensor Zorn)
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- Exterior creation on the finite-mode CAR–CCR carrier becomes the left-regular
split-octonion creation operator after transport. -/
theorem fermionCreate_transports_to_splitOctonion_leftRegular
    (i : Fin 3) :
    transportCommonCarrierEnd (FiniteCARCCRCommonCarrier.fermionCreate 3 i) =
      zornFermionLift (creationMap (Pi.single i 1)) := by
  apply LinearMap.ext
  intro x
  change commonCarrierZornEquiv
      (FiniteCARCCRCommonCarrier.fermionCreate 3 i
        (commonCarrierZornEquiv.symm x)) = _
  conv_rhs => rw [← commonCarrierZornEquiv.apply_symm_apply x]
  refine TensorProduct.inductionOn (commonCarrierZornEquiv.symm x)
    (fun p ψ => ?_) (fun x y hx hy => ?_)
  · change p ⊗ₜ[ℝ]
        fockToZorn (exteriorWedge3 (Pi.single i 1) ψ) =
      zornFermionLift (creationMap (Pi.single i 1))
        (p ⊗ₜ[ℝ] fockToZorn ψ)
    rw [fockToZorn_wedge]
    change p ⊗ₜ[ℝ] creationMap (Pi.single i 1) (fockToZorn ψ) = _
    rfl
  · calc
      commonCarrierZornEquiv
          (FiniteCARCCRCommonCarrier.fermionCreate 3 i (x + y)) =
        commonCarrierZornEquiv
          (FiniteCARCCRCommonCarrier.fermionCreate 3 i x) +
          commonCarrierZornEquiv
            (FiniteCARCCRCommonCarrier.fermionCreate 3 i y) := by
              simp only [map_add]
      _ = zornFermionLift (creationMap (Pi.single i 1))
            (commonCarrierZornEquiv x) +
          zornFermionLift (creationMap (Pi.single i 1))
            (commonCarrierZornEquiv y) := by rw [hx, hy]
      _ = zornFermionLift (creationMap (Pi.single i 1))
            (commonCarrierZornEquiv (x + y)) := by simp only [map_add]

/-- Coordinate contraction likewise becomes the native Zorn annihilation
operator on this common carrier. -/
theorem fermionAnnihilate_transports_to_splitOctonion_leftRegular
    (i : Fin 3) :
    transportCommonCarrierEnd
        (InfoGeometry.Twistor.RealSupertwistor.fermionAnnihilate
          (Fin 3) V3 (LinearMap.proj i)) =
      zornFermionLift (annihilate i) := by
  apply LinearMap.ext
  intro x
  change commonCarrierZornEquiv
      (InfoGeometry.Twistor.RealSupertwistor.fermionAnnihilate
        (Fin 3) V3 (LinearMap.proj i) (commonCarrierZornEquiv.symm x)) = _
  conv_rhs => rw [← commonCarrierZornEquiv.apply_symm_apply x]
  refine TensorProduct.inductionOn (commonCarrierZornEquiv.symm x)
    (fun p ψ => ?_) (fun x y hx hy => ?_)
  · change p ⊗ₜ[ℝ]
        fockToZorn (exteriorContract3 (LinearMap.proj i) ψ) =
      zornFermionLift (annihilate i) (p ⊗ₜ[ℝ] fockToZorn ψ)
    rw [fockToZorn_contract]
    change p ⊗ₜ[ℝ] annihilate i (fockToZorn ψ) = _
    rfl
  · calc
      commonCarrierZornEquiv
          (InfoGeometry.Twistor.RealSupertwistor.fermionAnnihilate
            (Fin 3) V3 (LinearMap.proj i) (x + y)) =
        commonCarrierZornEquiv
          (InfoGeometry.Twistor.RealSupertwistor.fermionAnnihilate
            (Fin 3) V3 (LinearMap.proj i) x) +
          commonCarrierZornEquiv
            (InfoGeometry.Twistor.RealSupertwistor.fermionAnnihilate
              (Fin 3) V3 (LinearMap.proj i) y) := by
                simp only [map_add]
      _ = zornFermionLift (annihilate i) (commonCarrierZornEquiv x) +
          zornFermionLift (annihilate i) (commonCarrierZornEquiv y) := by
            rw [hx, hy]
      _ = zornFermionLift (annihilate i)
            (commonCarrierZornEquiv (x + y)) := by simp only [map_add]

/-- The finite-mode CAR relation on the common carrier remains exact after its
state coordinates are read in the split-octonion Fock model. -/
theorem splitOctonionCommonCarrier_CAR (i j : Fin 3) :
    zornFermionLift (annihilate i) * zornFermionLift (create j) +
      zornFermionLift (create j) * zornFermionLift (annihilate i) =
        (if i = j then 1 else 0 : ℝ) • (1 : Module.End ℝ JointZorn) := by
  have h := congrArg transportCommonCarrierEnd
    (fermionAnnihilate_create_CAR 3 i j)
  have h' :
      (commonCarrierZornEquiv.conjAlgEquiv ℝ)
          (InfoGeometry.Twistor.RealSupertwistor.fermionAnnihilate
            (Fin 3) (Fin 3 → ℝ) (LinearMap.proj i)) *
        (commonCarrierZornEquiv.conjAlgEquiv ℝ)
          (FiniteCARCCRCommonCarrier.fermionCreate 3 j) +
      (commonCarrierZornEquiv.conjAlgEquiv ℝ)
          (FiniteCARCCRCommonCarrier.fermionCreate 3 j) *
        (commonCarrierZornEquiv.conjAlgEquiv ℝ)
          (InfoGeometry.Twistor.RealSupertwistor.fermionAnnihilate
            (Fin 3) (Fin 3 → ℝ) (LinearMap.proj i)) =
        (if i = j then 1 else 0 : ℝ) • (1 : Module.End ℝ JointZorn) := by
    simpa only [transportCommonCarrierEnd, map_add, map_mul, map_smul, map_one]
      using h
  have hA := fermionAnnihilate_transports_to_splitOctonion_leftRegular i
  have hC := fermionCreate_transports_to_splitOctonion_leftRegular j
  change (commonCarrierZornEquiv.conjAlgEquiv ℝ)
      (InfoGeometry.Twistor.RealSupertwistor.fermionAnnihilate
        (Fin 3) (Fin 3 → ℝ) (LinearMap.proj i)) = _ at hA
  change (commonCarrierZornEquiv.conjAlgEquiv ℝ)
      (FiniteCARCCRCommonCarrier.fermionCreate 3 j) = _ at hC
  rw [hA, hC] at h'
  have hCreate := congrArg zornFermionLift (creationMap_basis j)
  rw [← hCreate]
  exact h'

/-- The left-tensor lift preserves composition: its operators act on the
Zorn state factor in the same order as the underlying left-regular operators. -/
theorem zornFermionLift_mul (S T : Module.End ℝ Zorn) :
    zornFermionLift S * zornFermionLift T = zornFermionLift (S * T) := by
  apply LinearMap.ext
  intro x
  refine TensorProduct.inductionOn x (fun p ψ => ?_) (fun x y hx hy => ?_)
  · simp [zornFermionLift, LinearMap.lTensor_tmul, Module.End.mul_apply]
  · simp only [map_add, hx, hy]

/-- The transported split-Zorn annihilation operator remains square-zero on
the whole polynomial–Fock carrier. This is the lower-CAR nilpotence transported
through the existing left-tensor representation. -/
theorem splitOctonionCommonCarrier_annihilate_sq (i : Fin 3) :
    zornFermionLift (Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) *
      zornFermionLift (Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) = 0 := by
  have hLower := regular_lower_CAR i i
  have htwice :
      (2 : ℝ) • (Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
        Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) = 0 := by
    simpa only [two_smul] using hLower
  have hsq :
      Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
        Algebra.Zorn.RegularCARVacuumSeparation.annihilate i = 0 := by
    rcases smul_eq_zero.mp htwice with hscalar | hoperator
    · norm_num at hscalar
    · exact hoperator
  calc
    zornFermionLift (Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) *
        zornFermionLift (Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) =
        zornFermionLift (Algebra.Zorn.RegularCARVacuumSeparation.annihilate i *
          Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) := zornFermionLift_mul _ _
    _ = 0 := by rw [hsq]; simp [zornFermionLift]

/-- A creation operator on the transported split-Zorn common carrier remains
square-zero. This is the CAR nilpotence transported through the tensor action. -/
theorem splitOctonionCommonCarrier_create_sq (i : Fin 3) :
    zornFermionLift (create i) * zornFermionLift (create i) = 0 := by
  rw [zornFermionLift_mul, ← creationMap_basis i, creationMap_sq]
  simp [zornFermionLift]

/-- The represented split-Zorn creation and annihilation operators genuinely
fail to commute on the polynomial–Fock common carrier. CAR, square-zero creation, and
nontriviality of the actual tensor carrier force this defect. -/
theorem splitOctonionCommonCarrier_create_annihilate_noncommute (i : Fin 3) :
    zornFermionLift (create i) * zornFermionLift (annihilate i) ≠
      zornFermionLift (annihilate i) * zornFermionLift (create i) := by
  let c := zornFermionLift (create i)
  let a := zornFermionLift (annihilate i)
  have hc : c * c = 0 := splitOctonionCommonCarrier_create_sq i
  have hcar : a * c + c * a = 1 := by
    simpa [c, a] using splitOctonionCommonCarrier_CAR i i
  intro hcomm
  have htwice : c * a + c * a = 1 := by
    calc
      c * a + c * a = a * c + c * a := by rw [hcomm]
      _ = 1 := hcar
  have hcaZero : c * (c * a) = 0 := by
    calc
      c * (c * a) = (c * c) * a := by rw [← mul_assoc]
      _ = 0 := by rw [hc, zero_mul]
  have hcZero : c = 0 := by
    have hmul := congrArg (fun z : Module.End ℝ JointZorn => c * z) htwice
    have h : 0 = c := by simpa [mul_add, hcaZero] using hmul
    exact h.symm
  letI : Nontrivial JointZorn := commonCarrierZorn_nontrivial
  have hzero : (0 : Module.End ℝ JointZorn) = 1 := by
    simpa [hcZero] using hcar
  exact zero_ne_one hzero

/-- The split-Zorn common-carrier CAR pair has a nonzero operator-valued BdG
interaction anomaly, and Andreev particle-hole reflection cancels it exactly. -/
theorem splitOctonionCommonCarrier_bdg_andreev_anomaly (i : Fin 3) :
    InfoGeometry.Physics.massiveBdGCommutatorAnomaly
        (zornFermionLift (create i)) (zornFermionLift (annihilate i)) ≠ 0 ∧
    InfoGeometry.Physics.andreevSwap *
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          (zornFermionLift (create i)) (zornFermionLift (annihilate i)) *
        InfoGeometry.Physics.andreevSwap =
      -InfoGeometry.Physics.massiveBdGCommutatorAnomaly
        (zornFermionLift (create i)) (zornFermionLift (annihilate i)) ∧
    InfoGeometry.Physics.massiveBdGCommutatorAnomaly
        (zornFermionLift (create i)) (zornFermionLift (annihilate i)) +
      InfoGeometry.Physics.andreevSwap *
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          (zornFermionLift (create i)) (zornFermionLift (annihilate i)) *
        InfoGeometry.Physics.andreevSwap = 0 := by
  have hnc := splitOctonionCommonCarrier_create_annihilate_noncommute i
  have h := InfoGeometry.Physics.andreev_reflect_mass_commutator_anomaly
    (zornFermionLift (create i)) (zornFermionLift (annihilate i))
  refine ⟨?_, h, ?_⟩
  · intro hzero
    exact hnc ((InfoGeometry.Physics.massiveBdGCommutatorAnomaly_eq_zero_iff_commute
      (zornFermionLift (create i)) (zornFermionLift (annihilate i))).mp hzero)
  · rw [h]
    exact add_neg_cancel
      (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
        (zornFermionLift (create i)) (zornFermionLift (annihilate i)))

/-- The polynomial CCR remains exact after the exterior factor is expressed in
split-octonion Zorn coordinates. This preserves the ordered bosonic
commutator on the transported common carrier. -/
theorem splitOctonionCommonCarrier_CCR (i j : Fin 3) :
    transportCommonCarrierEnd (bosonAnnihilate 3 i) *
        transportCommonCarrierEnd (bosonCreate 3 j) -
      transportCommonCarrierEnd (bosonCreate 3 j) *
        transportCommonCarrierEnd (bosonAnnihilate 3 i) =
      (if i = j then 1 else 0 : ℝ) • (1 : Module.End ℝ JointZorn) := by
  let f : Operator (Fin 3) →+* Module.End ℝ JointZorn :=
    ((commonCarrierZornEquiv.conjAlgEquiv ℝ).toRingHom).comp
      (bosonLift (Fin 3) V3).toRingHom
  change f (InfoGeometry.Twistor.RealPolynomialCCR.annihilate i) *
      f (InfoGeometry.Twistor.RealPolynomialCCR.create j) -
    f (InfoGeometry.Twistor.RealPolynomialCCR.create j) *
      f (InfoGeometry.Twistor.RealPolynomialCCR.annihilate i) = _
  calc
    f (InfoGeometry.Twistor.RealPolynomialCCR.annihilate i) *
        f (InfoGeometry.Twistor.RealPolynomialCCR.create j) -
      f (InfoGeometry.Twistor.RealPolynomialCCR.create j) *
        f (InfoGeometry.Twistor.RealPolynomialCCR.annihilate i) =
        f (InfoGeometry.Twistor.RealPolynomialCCR.annihilate i *
          InfoGeometry.Twistor.RealPolynomialCCR.create j -
          InfoGeometry.Twistor.RealPolynomialCCR.create j *
          InfoGeometry.Twistor.RealPolynomialCCR.annihilate i) := by
      rw [← f.map_mul, ← f.map_mul]
      exact (map_sub f _ _).symm
    _ = (if i = j then 1 else 0 : ℝ) • (1 : Module.End ℝ JointZorn) := by
      rw [InfoGeometry.Twistor.RealPolynomialCCR.annihilate_create_commutator]
      simp [f]

end InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge

end
