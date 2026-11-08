/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
import InfoGeometry.Canonical.Cl55AllModeMassCoercivity
import InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
import InfoGeometry.Clifford.RealFockHilbertCompletion
import InfoGeometry.OperatorAlgebra.Cl55CARBdGInteractionBridge
import InfoGeometry.Algebra.SupergradedBracket
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Polynomial CCR with the Cl(5,5) CAR action on the algebraic Fock colimit

The polynomial CCR acts on the first tensor factor and the existing
Cl(5,5)-Fock direct-limit representation acts on the second. This module
places both actions on one algebraic carrier and proves their distinct
commutation laws there. It makes no completion or analytic-limit claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.CARCCRColimitSupercarrier

open scoped TensorProduct
open InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.OperatorAlgebra.Cl55CARBdGInteractionBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
open InfoGeometry.Twistor.RealSupertwistor
open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Physics
open InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge

/-- The polynomial factor tensored with the algebraic direct limit of the
finite Cl(5,5) Fock stages. -/
abbrev Carrier := WavePolynomial (Fin 5) ⊗[ℝ] FockInfinity

/-- The algebraic Fock colimit is nontrivial: the native stage map embeds
the unit of the fifth finite Clifford stage. -/
theorem fockInfinity_nontrivial : Nontrivial FockInfinity := by
  let pole : FockInfinity := fockToInfinity 5 (1 : FockStage 5)
  have hpole : pole ≠ 0 := by
    intro hzero
    have hmap : fockToInfinity 5 (1 : FockStage 5) = 0 := by
      simpa [pole] using hzero
    have hzero' : fockToInfinity 5 (0 : FockStage 5) = 0 := by
      change DirectLimit.Module.of ℝ ℕ FockStage
        (fun m n h => fockStageMap m n h) 5 0 = 0
      exact map_zero _
    have hmap' : fockToInfinity 5 (1 : FockStage 5) = fockToInfinity 5 0 := by
      exact hmap.trans hzero'.symm
    exact one_ne_zero ((fockToInfinity_injective 5) hmap')
  exact ⟨⟨pole, 0, hpole⟩⟩

/-- The polynomial–Fock tensor carrier is nontrivial, by the embedded scalar
line in its actual Fock-colimit factor. -/
theorem commonCarrier_nontrivial : Nontrivial Carrier := by
  letI : Nontrivial FockInfinity := fockInfinity_nontrivial
  let pole : FockInfinity := fockToInfinity 5 (1 : FockStage 5)
  have hpole : pole ≠ 0 := by
    intro hzero
    have hmap : fockToInfinity 5 (1 : FockStage 5) = 0 := by
      simpa [pole] using hzero
    have hzero' : fockToInfinity 5 (0 : FockStage 5) = 0 := by
      change DirectLimit.Module.of ℝ ℕ FockStage
        (fun m n h => fockStageMap m n h) 5 0 = 0
      exact map_zero _
    have hmap' : fockToInfinity 5 (1 : FockStage 5) = fockToInfinity 5 0 := by
      exact hmap.trans hzero'.symm
    exact one_ne_zero ((fockToInfinity_injective 5) hmap')
  let scalarLine : ℝ →ₗ[ℝ] FockInfinity :=
    { toFun := fun r => r • pole
      map_add' := by intro r s; simp [add_smul]
      map_smul' := by intro r s; simp [mul_smul] }
  have hscalarLine : Function.Injective scalarLine := by
    intro r s hrs
    have hzero : (r - s) • pole = 0 := by
      change r • pole = s • pole at hrs
      rw [sub_smul, hrs, sub_self]
    rcases smul_eq_zero.mp hzero with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact (hpole hzero).elim
  exact TensorProduct.nontrivial_of_linearMap_injective_of_flat_left
    ℝ (WavePolynomial (Fin 5)) FockInfinity scalarLine hscalarLine

/-- The polynomial CCR creation action on the shared polynomial–colimit
carrier. -/
def bosonCreation (i : Fin 5) : Module.End ℝ Carrier :=
  Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity (create i)

/-- The polynomial CCR annihilation action on the shared polynomial–colimit
carrier. -/
def bosonAnnihilation (i : Fin 5) : Module.End ℝ Carrier :=
  Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity (annihilate i)

/-- Lift the actual Cl(5,5) Fock-colimit representation to the second tensor
factor of the common carrier. -/
def cl55ColimitSupercarrierRep : Cl55 →+* Module.End ℝ Carrier :=
  (Module.End.lTensorAlgHom ℝ FockInfinity (WavePolynomial (Fin 5))).toRingHom.comp
    cl55FockInfinityRepresentation

/-- The Clifford grade involution on the Fock-colimit tensor factor, acting
identically on the polynomial CCR factor. -/
def colimitFockParity : Module.End ℝ Carrier :=
  fockInfinityInvolute.lTensor (WavePolynomial (Fin 5))

/-- The polynomial CCR operator algebra acts on the first tensor factor. -/
noncomputable def bosonFactorRepresentation :
    Module.End ℝ (WavePolynomial (Fin 5)) →ₐ[ℝ] Module.End ℝ Carrier :=
  Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity

/-- The full algebra of Fock-colimit endomorphisms acts on the second tensor
factor. Restricting this representation along the existing Cl(5,5) action
recovers `cl55ColimitSupercarrierRep`. -/
noncomputable def fockFactorRepresentation :
    Module.End ℝ FockInfinity →ₐ[ℝ] Module.End ℝ Carrier :=
  Module.End.lTensorAlgHom ℝ FockInfinity (WavePolynomial (Fin 5))

/-- The two factor actions commute, so their algebraic tensor product acts on
the shared polynomial–Fock colimit carrier. This is the universal operator
representation combining the CCR factor with the represented CAR factor. -/
noncomputable def carCcrTensorRepresentation :
    (Module.End ℝ (WavePolynomial (Fin 5)) ⊗[ℝ]
      Module.End ℝ FockInfinity) →ₐ[ℝ] Module.End ℝ Carrier :=
  Algebra.TensorProduct.lift bosonFactorRepresentation fockFactorRepresentation
    (by
      intro b f
      change (b.rTensor FockInfinity).comp
          (f.lTensor (WavePolynomial (Fin 5))) =
        (f.lTensor (WavePolynomial (Fin 5))).comp
          (b.rTensor FockInfinity)
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])

/-- On a pure tensor of operators, the combined representation is the
composition of the two commuting factor actions. -/
@[simp] theorem carCcrTensorRepresentation_tmul
    (b : Module.End ℝ (WavePolynomial (Fin 5)))
    (f : Module.End ℝ FockInfinity) :
    carCcrTensorRepresentation (b ⊗ₜ[ℝ] f) =
      bosonFactorRepresentation b * fockFactorRepresentation f := by
  exact Algebra.TensorProduct.lift_tmul
    bosonFactorRepresentation fockFactorRepresentation _ b f

/-- The native Clifford/Fock-colimit representation is the second-factor
restriction of the combined CAR–CCR tensor representation. -/
@[simp] theorem carCcrTensorRepresentation_cl55
    (b : Module.End ℝ (WavePolynomial (Fin 5))) (x : Cl55) :
    carCcrTensorRepresentation
        (b ⊗ₜ[ℝ] cl55FockInfinityRepresentation x) =
      Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b *
        cl55ColimitSupercarrierRep x := by
  rw [carCcrTensorRepresentation_tmul]
  rfl

/-- The tensor-lifted Fock parity is an involution on the common carrier. -/
theorem colimitFockParity_involutive (v : Carrier) :
    colimitFockParity (colimitFockParity v) = v := by
  have hcomp : colimitFockParity.comp colimitFockParity =
      (LinearMap.id : Carrier →ₗ[ℝ] Carrier) := by
    change (fockInfinityInvolute.lTensor (WavePolynomial (Fin 5))).comp
        (fockInfinityInvolute.lTensor (WavePolynomial (Fin 5))) = _
    rw [← LinearMap.lTensor_comp]
    change (fockInfinityInvolute.comp fockInfinityInvolute).lTensor
        (WavePolynomial (Fin 5)) = _
    have hparity : fockInfinityInvolute.comp fockInfinityInvolute =
        (LinearMap.id : FockInfinity →ₗ[ℝ] FockInfinity) := by
      apply LinearMap.ext
      intro ψ
      exact fockInfinityInvolute_involutive ψ
    rw [hparity, LinearMap.lTensor_id]
  exact congrArg (fun f : Carrier →ₗ[ℝ] Carrier => f v) hcomp

/-- The finite `Cl(5,5)` chart map preserves Clifford grade involution. -/
theorem cl55ToSplitCl55_preserves_involute (x : Cl55) :
    cl55ToSplitCl55 (CliffordAlgebra.involute x) =
      CliffordAlgebra.involute (cl55ToSplitCl55 x) := by
  have hmaps :
      cl55ToSplitCl55.toAlgHom.comp
          (CliffordAlgebra.involute (Q := Q55)) =
        (CliffordAlgebra.involute (Q := Qsplit 5)).comp
          cl55ToSplitCl55.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change cl55ToSplitCl55
        (CliffordAlgebra.involute (CliffordAlgebra.ι Q55 v)) =
      CliffordAlgebra.involute (cl55ToSplitCl55 (CliffordAlgebra.ι Q55 v))
    rw [CliffordAlgebra.involute_ι,
      cl55ToSplitCl55_map_ι, map_neg,
      cl55ToSplitCl55_map_ι, CliffordAlgebra.involute_ι]
  exact congrArg (fun f : Cl55 →ₐ[ℝ] SplitCl55Alg => f x) hmaps

/-- The Fock-colimit parity intertwines the native Clifford action with its
grade involution, and this identity lifts to the shared polynomial–Fock
carrier. -/
theorem colimitFockParity_intertwines_Cl55_grade (x : Cl55) :
    colimitFockParity * cl55ColimitSupercarrierRep x =
      cl55ColimitSupercarrierRep (CliffordAlgebra.involute x) *
        colimitFockParity := by
  have hFock :
      fockInfinityInvolute.comp (cl55FockInfinityRepresentation x) =
        (cl55FockInfinityRepresentation (CliffordAlgebra.involute x)).comp
          fockInfinityInvolute := by
    apply LinearMap.ext
    intro ψ
    change fockInfinityInvolute
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m n h => splitCliffordMap m n h) 5
            (cl55ToSplitCl55 x)) ψ) =
      splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 5
          (cl55ToSplitCl55 (CliffordAlgebra.involute x)))
        (fockInfinityInvolute ψ)
    rw [splitCliffordFockAction_grade_equivariant,
      splitCliffordInfinityInvolute_ofStage,
      ← cl55ToSplitCl55_preserves_involute]
  change (fockInfinityInvolute.lTensor (WavePolynomial (Fin 5))).comp
      ((cl55FockInfinityRepresentation x).lTensor (WavePolynomial (Fin 5))) =
    ((cl55FockInfinityRepresentation (CliffordAlgebra.involute x)).lTensor
      (WavePolynomial (Fin 5))).comp
      (fockInfinityInvolute.lTensor (WavePolynomial (Fin 5)))
  rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hFock]

/-- The represented CAR creation and annihilation operators are odd for the
colimit Fock parity on the common carrier. -/
theorem colimit_CAR_generators_are_odd (i : Fin 5) :
    colimitFockParity * cl55ColimitSupercarrierRep (creation55 i) =
        -(cl55ColimitSupercarrierRep (creation55 i) * colimitFockParity) ∧
    colimitFockParity * cl55ColimitSupercarrierRep (annihilation55 i) =
        -(cl55ColimitSupercarrierRep (annihilation55 i) * colimitFockParity) := by
  have hCreate := colimitFockParity_intertwines_Cl55_grade (creation55 i)
  have hAnnihilate := colimitFockParity_intertwines_Cl55_grade (annihilation55 i)
  simp only [creation55_involute, annihilation55_involute, map_neg] at hCreate hAnnihilate
  have hNegMul (f g : Module.End ℝ Carrier) : -f * g = -(f * g) := by
    ext v
    simp
  exact ⟨hCreate.trans (hNegMul _ _), hAnnihilate.trans (hNegMul _ _)⟩

/-- The boson factor retains its polynomial CCR on the tensor product with
the Clifford Fock colimit. -/
theorem boson_creation_annihilation_CCR (i j : Fin 5) :
    bosonAnnihilation i * bosonCreation j -
        bosonCreation j * bosonAnnihilation i =
      (if i = j then 1 else 0 : ℝ) • (1 : Module.End ℝ Carrier) := by
  have h := congrArg
    (Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity)
    (annihilate_create_commutator i j)
  simpa [bosonAnnihilation, bosonCreation] using h

/-- The Cl(5,5) CAR relation remains valid after its Fock-colimit action is
lifted to the same polynomial–colimit carrier. -/
theorem cl55_colimit_creation_annihilation_CAR (i j : Fin 5) :
    cl55ColimitSupercarrierRep (annihilation55 i) *
        cl55ColimitSupercarrierRep (creation55 j) +
      cl55ColimitSupercarrierRep (creation55 j) *
        cl55ColimitSupercarrierRep (annihilation55 i) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have h := congrArg cl55ColimitSupercarrierRep
      (annihilation55_creation55_anticommutator i)
    simpa using h
  · have h := congrArg cl55ColimitSupercarrierRep
      (annihilation55_creation55_anticommutator_eq i j)
    simpa [hij] using h

/-- A same-mode Cl(5,5) creation/annihilation pair does not commute. This
follows from the CAR relation and the square-zero laws, without any matrix
coordinate realization. -/
theorem cl55_creation_annihilation_do_not_commute :
    ∀ i : Fin 5, ¬ Commute (creation55 i) (annihilation55 i) := by
  intro i
  intro h
  have hcomm : creation55 i * annihilation55 i =
      annihilation55 i * creation55 i := h.eq
  let x : Cl55 := creation55 i * annihilation55 i
  have hCAR := annihilation55_creation55_anticommutator i
  have hTwice : x + x = 1 := by
    simpa [x, hcomm, add_comm] using hCAR
  have hSquare : x * x = 0 := by
    dsimp [x]
    calc
      (creation55 i * annihilation55 i) * (creation55 i * annihilation55 i) =
          creation55 i * (annihilation55 i * creation55 i) * annihilation55 i := by
            simp only [mul_assoc]
      _ = creation55 i * (creation55 i * annihilation55 i) * annihilation55 i := by
            rw [← hcomm]
      _ = (creation55 i * creation55 i) * (annihilation55 i * annihilation55 i) := by
            simp only [mul_assoc]
      _ = 0 := by rw [creation55_sq, annihilation55_sq, zero_mul]
  have hMul := congrArg (fun z : Cl55 => z * x) hTwice
  rw [add_mul, hSquare, zero_add, one_mul] at hMul
  have hx : x = 0 := hMul.symm
  have hOne : (1 : Cl55) = 0 := by simpa [x, hx] using hTwice.symm
  exact (one_ne_zero : (1 : Cl55) ≠ 0) hOne

/-- CCR creation acts on the polynomial factor while the colimit CAR
creation acts on the Fock factor; the two endomorphisms commute. -/
theorem boson_creation_commutes_with_colimit_CAR (i j : Fin 5) :
    bosonCreation i * cl55ColimitSupercarrierRep (creation55 j) =
      cl55ColimitSupercarrierRep (creation55 j) * bosonCreation i := by
  change ((create i).rTensor FockInfinity).comp
      ((cl55FockInfinityRepresentation (creation55 j)).lTensor
        (WavePolynomial (Fin 5))) =
    ((cl55FockInfinityRepresentation (creation55 j)).lTensor
        (WavePolynomial (Fin 5))).comp
      ((create i).rTensor FockInfinity)
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- CCR annihilation acts on the polynomial factor while the colimit CAR
annihilation acts on the Fock factor; the two endomorphisms commute. -/
theorem boson_annihilation_commutes_with_colimit_CAR (i j : Fin 5) :
    bosonAnnihilation i * cl55ColimitSupercarrierRep (annihilation55 j) =
      cl55ColimitSupercarrierRep (annihilation55 j) * bosonAnnihilation i := by
  change ((annihilate i).rTensor FockInfinity).comp
      ((cl55FockInfinityRepresentation (annihilation55 j)).lTensor
        (WavePolynomial (Fin 5))) =
    ((cl55FockInfinityRepresentation (annihilation55 j)).lTensor
        (WavePolynomial (Fin 5))).comp
      ((annihilate i).rTensor FockInfinity)
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- Particle–hole reflection of the native CAR BdG commutator anomaly is
preserved by the same Fock-colimit representation lifted to the polynomial
CCR carrier. -/
theorem colimit_supercarrier_andreev_reflects_CAR_anomaly (i : Fin 5) :
    Matrix.map
        (andreevSwap *
          massiveBdGCommutatorAnomaly (creation55 i) (annihilation55 i) *
          andreevSwap)
        cl55ColimitSupercarrierRep =
      Matrix.map
        (-massiveBdGCommutatorAnomaly (creation55 i) (annihilation55 i))
        cl55ColimitSupercarrierRep := by
  exact congrArg
    (fun M => Matrix.map M cl55ColimitSupercarrierRep)
    (andreev_reflect_mass_commutator_anomaly
      (creation55 i) (annihilation55 i))

/-- On the common CCR–CAR colimit carrier, the hole-reflected BdG
commutator anomaly cancels the particle contribution exactly. -/
theorem colimit_supercarrier_andreev_anomaly_cancellation (i : Fin 5) :
    andreevSwap *
        massiveBdGCommutatorAnomaly
          (cl55ColimitSupercarrierRep (creation55 i))
          (cl55ColimitSupercarrierRep (annihilation55 i)) * andreevSwap +
      massiveBdGCommutatorAnomaly
        (cl55ColimitSupercarrierRep (creation55 i))
        (cl55ColimitSupercarrierRep (annihilation55 i)) = 0 := by
  rw [andreev_reflect_mass_commutator_anomaly]
  exact neg_add_cancel
    (massiveBdGCommutatorAnomaly
      (cl55ColimitSupercarrierRep (creation55 i))
      (cl55ColimitSupercarrierRep (annihilation55 i)))

/-- The total five-mode CAR creation operator in the native `Cl(5,5)` algebra. -/
def cl55FiveModeCreation : Cl55 := ∑ i : Fin 5, creation55 i

/-- The total five-mode CAR annihilation operator in the native `Cl(5,5)` algebra. -/
def cl55FiveModeAnnihilation : Cl55 := ∑ i : Fin 5, annihilation55 i

private theorem sum_square_zero_of_anticommuting
    {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (T : ι → R)
    (hsq : ∀ i ∈ s, T i * T i = 0)
    (hanti : ∀ i j, i ∈ s → j ∈ s → i ≠ j → T i * T j + T j * T i = 0) :
    (∑ i ∈ s, T i) * (∑ i ∈ s, T i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hcross : T a * (∑ i ∈ s, T i) + (∑ i ∈ s, T i) * T a = 0 := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro b hb
        have h := hanti a b (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb)
          (by intro heq; subst b; exact ha hb)
        exact h
      calc
        (T a + (∑ i ∈ s, T i)) * (T a + (∑ i ∈ s, T i)) =
            T a * T a +
              (T a * (∑ i ∈ s, T i) + (∑ i ∈ s, T i) * T a) +
              (∑ i ∈ s, T i) * (∑ i ∈ s, T i) := by noncomm_ring
        _ = 0 := by
          rw [hsq a (Finset.mem_insert_self a s), hcross]
          simp only [zero_add, add_zero]
          exact ih (fun i hi => hsq i (Finset.mem_insert_of_mem hi))
            (fun i j hi hj hij => hanti i j
              (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij)

private theorem cl55FiveModeCreation_square :
    cl55FiveModeCreation * cl55FiveModeCreation = 0 := by
  have hsq : ∀ i ∈ (Finset.univ : Finset (Fin 5)), creation55 i * creation55 i = 0 :=
    fun i _ => creation55_sq i
  have hanti : ∀ i j, i ∈ (Finset.univ : Finset (Fin 5)) →
      j ∈ (Finset.univ : Finset (Fin 5)) → i ≠ j →
      creation55 i * creation55 j + creation55 j * creation55 i = 0 := by
    intro i j _ _ hij
    exact creation55_anticommutator i j
  simpa [cl55FiveModeCreation] using
    sum_square_zero_of_anticommuting Finset.univ creation55 hsq hanti

private theorem cl55FiveModeAnnihilation_square :
    cl55FiveModeAnnihilation * cl55FiveModeAnnihilation = 0 := by
  have hsq : ∀ i ∈ (Finset.univ : Finset (Fin 5)), annihilation55 i * annihilation55 i = 0 :=
    fun i _ => annihilation55_sq i
  have hanti : ∀ i j, i ∈ (Finset.univ : Finset (Fin 5)) →
      j ∈ (Finset.univ : Finset (Fin 5)) → i ≠ j →
      annihilation55 i * annihilation55 j + annihilation55 j * annihilation55 i = 0 := by
    intro i j _ _ hij
    exact annihilation55_anticommutator i j
  simpa [cl55FiveModeAnnihilation] using
    sum_square_zero_of_anticommuting Finset.univ annihilation55 hsq hanti

/-- The finite mass generator is the sum of the native creation and
annihilation modes. -/
theorem nativeFiveModeMajorana_eq_creation_add_annihilation :
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana =
      cl55FiveModeCreation + cl55FiveModeAnnihilation := by
  simp only [InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana,
    cl55FiveModeCreation, cl55FiveModeAnnihilation, Finset.sum_add_distrib]

/-- The native five-mode creation and annihilation sums satisfy the full
Cl(5,5) CAR anticommutator before choosing a Fock representation. -/
theorem cl55FiveModeCreation_annihilation_CAR :
    cl55FiveModeCreation * cl55FiveModeAnnihilation +
      cl55FiveModeAnnihilation * cl55FiveModeCreation = (5 : Cl55) := by
  have hmass := InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana_square
  rw [nativeFiveModeMajorana_eq_creation_add_annihilation] at hmass
  have hNat : (5 : ℝ) • (1 : Cl55) = (5 : Cl55) := by
    norm_num [Algebra.smul_def, map_ofNat]
  rw [hNat] at hmass
  calc
    _ = (cl55FiveModeCreation + cl55FiveModeAnnihilation) *
        (cl55FiveModeCreation + cl55FiveModeAnnihilation) := by
          noncomm_ring [cl55FiveModeCreation_square, cl55FiveModeAnnihilation_square]
    _ = 5 := hmass

/-- The actual finite Fock-stage representation of the native Cl(5,5)
operators, before adjoining the independent polynomial CCR factor. -/
def cl55FiniteFockRep : Cl55 →+* Module.End ℝ (FockStage 5) :=
  (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.towerSpinorRep 5).toRingHom.comp
    (cl55ToSplitCl55.toRingHom)

def finiteFockFiveModeCreation : Module.End ℝ (FockStage 5) :=
  cl55FiniteFockRep cl55FiveModeCreation

def finiteFockFiveModeAnnihilation : Module.End ℝ (FockStage 5) :=
  cl55FiniteFockRep cl55FiveModeAnnihilation

/-- The native mass operator represented on the finite Fock stage. -/
def finiteFockFiveModeMass : Module.End ℝ (FockStage 5) :=
  cl55FiniteFockRep
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana

/-- On the finite Fock carrier, the calibrated mass is the sum of the
represented creation and annihilation interaction operators. -/
theorem finiteFock_fiveModeMass_eq_interaction_sum :
    finiteFockFiveModeMass =
      finiteFockFiveModeCreation + finiteFockFiveModeAnnihilation := by
  simpa only [finiteFockFiveModeMass, finiteFockFiveModeCreation,
    finiteFockFiveModeAnnihilation, map_add] using
    congrArg cl55FiniteFockRep nativeFiveModeMajorana_eq_creation_add_annihilation

/-- The finite Fock-stage mass square is the exact five-mode CAR value. -/
theorem finiteFock_fiveModeMass_square :
    finiteFockFiveModeMass * finiteFockFiveModeMass =
      (5 : Module.End ℝ (FockStage 5)) := by
  have hNat : (5 : ℝ) • (1 : Cl55) = (5 : Cl55) := by
    norm_num [Algebra.smul_def, map_ofNat]
  have h := congrArg cl55FiniteFockRep
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana_square
  rw [hNat] at h
  simpa only [finiteFockFiveModeMass, map_mul, map_ofNat] using h

/-- The finite Fock-stage mass preserves the repository's degree-six
operator cyclotomic Higgs value `21`. -/
theorem finiteFock_fiveModeMass_cyclotomic_higgs :
    InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix
        (finiteFockFiveModeMass * finiteFockFiveModeMass) =
      (21 : Module.End ℝ (FockStage 5)) := by
  let rho := cl55FiniteFockRep
  have hNat : (21 : ℝ) • (1 : Cl55) = (21 : Cl55) := by
    norm_num [Algebra.smul_def, map_ofNat]
  have hRho := congrArg rho
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana_cyclotomic_higgs
  rw [hNat] at hRho
  simp only [rho, map_ofNat,
    InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix,
    map_mul, map_sub, map_add, map_one] at hRho
  simpa only [finiteFockFiveModeMass,
    InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix,
    map_mul, map_sub, map_add, map_one, map_ofNat] using hRho

/-- On the finite Fock stage, the represented five-mode particle and hole
operators are square-zero and retain the exact summed CAR value. -/
theorem finiteFock_fiveMode_CAR :
    finiteFockFiveModeCreation * finiteFockFiveModeCreation = 0 ∧
    finiteFockFiveModeAnnihilation * finiteFockFiveModeAnnihilation = 0 ∧
    finiteFockFiveModeCreation * finiteFockFiveModeAnnihilation +
      finiteFockFiveModeAnnihilation * finiteFockFiveModeCreation =
        (5 : Module.End ℝ (FockStage 5)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [finiteFockFiveModeCreation, map_mul, map_zero] using
      congrArg cl55FiniteFockRep cl55FiveModeCreation_square
  · simpa only [finiteFockFiveModeAnnihilation, map_mul, map_zero] using
      congrArg cl55FiniteFockRep cl55FiveModeAnnihilation_square
  · simpa only [finiteFockFiveModeCreation, finiteFockFiveModeAnnihilation,
      map_add, map_mul, map_ofNat] using
      congrArg cl55FiniteFockRep cl55FiveModeCreation_annihilation_CAR

/-- The finite Fock-stage BdG interaction retains the summed CAR relation,
and Andreev reflection cancels its commutator cross-term in the square. -/
theorem finiteFock_fiveMode_BdG_andreev_cancellation :
    let D := finiteFockFiveModeCreation
    let M := finiteFockFiveModeAnnihilation
    let H := massiveBdGHamiltonian D M
    D * D = 0 ∧
    M * M = 0 ∧
    D * M + M * D = (5 : Module.End ℝ (FockStage 5)) ∧
    H * H + andreevSwap * (H * H) * andreevSwap =
      !![D * D + M * M + (M * M + D * D), 0;
         0, M * M + D * D + (D * D + M * M)] := by
  dsimp
  rcases finiteFock_fiveMode_CAR with ⟨hD, hM, hCAR⟩
  let D := finiteFockFiveModeCreation
  let M := finiteFockFiveModeAnnihilation
  let H := massiveBdGHamiltonian D M
  refine ⟨hD, hM, hCAR, ?_⟩
  exact massiveBdGHamiltonian_andreev_anomaly_cancellation D M

/-- On the shared polynomial–Fock colimit, the sum of all five represented
creation modes is square-zero. The proof transports the native CAR relations
through the actual `Cl(5,5)` representation. -/
theorem colimit_supercarrier_fiveMode_creation_sq :
    cl55ColimitSupercarrierRep cl55FiveModeCreation *
      cl55ColimitSupercarrierRep cl55FiveModeCreation = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg cl55ColimitSupercarrierRep cl55FiveModeCreation_square

/-- On the shared polynomial–Fock colimit, the sum of all five represented
annihilation modes is square-zero. -/
theorem colimit_supercarrier_fiveMode_annihilation_sq :
    cl55ColimitSupercarrierRep cl55FiveModeAnnihilation *
      cl55ColimitSupercarrierRep cl55FiveModeAnnihilation = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg cl55ColimitSupercarrierRep cl55FiveModeAnnihilation_square

/-- The five-mode creation and annihilation sums on the common carrier satisfy
the full summed CAR relation, with its nonzero central term `5`. -/
theorem colimit_supercarrier_fiveMode_CAR_anticommutator :
    cl55ColimitSupercarrierRep cl55FiveModeCreation *
        cl55ColimitSupercarrierRep cl55FiveModeAnnihilation +
      cl55ColimitSupercarrierRep cl55FiveModeAnnihilation *
        cl55ColimitSupercarrierRep cl55FiveModeCreation =
      (5 : Module.End ℝ Carrier) := by
  have h := congrArg cl55ColimitSupercarrierRep cl55FiveModeCreation_annihilation_CAR
  simpa only [map_add, map_mul, map_ofNat] using h

/-- The summed five-mode BdG interaction on the shared CCR–Fock colimit has
the exact CAR mass relation, and the hole-reflected square cancels its
off-diagonal anomaly. The diagonal products retain their noncommutative order. -/
theorem colimit_supercarrier_fiveMode_mass_and_andreev_cancellation :
    let D := cl55ColimitSupercarrierRep cl55FiveModeCreation
    let M := cl55ColimitSupercarrierRep cl55FiveModeAnnihilation
    let H := massiveBdGHamiltonian D M
    D * D = 0 ∧
    M * M = 0 ∧
    D * M + M * D = (5 : Module.End ℝ Carrier) ∧
    D * M - M * D ≠ 0 ∧
    (H * H) 0 1 ≠ 0 ∧
    H * H + andreevSwap * (H * H) * andreevSwap =
      !![D * D + M * M + (M * M + D * D), 0;
         0, M * M + D * D + (D * D + M * M)] := by
  dsimp
  let D := cl55ColimitSupercarrierRep cl55FiveModeCreation
  let M := cl55ColimitSupercarrierRep cl55FiveModeAnnihilation
  let H := massiveBdGHamiltonian D M
  letI : Nontrivial Carrier := commonCarrier_nontrivial
  have hD : D * D = 0 := by
    dsimp [D]
    exact colimit_supercarrier_fiveMode_creation_sq
  have hM : M * M = 0 := by
    dsimp [M]
    exact colimit_supercarrier_fiveMode_annihilation_sq
  have hCAR : D * M + M * D = (5 : Module.End ℝ Carrier) := by
    dsimp [D, M]
    exact colimit_supercarrier_fiveMode_CAR_anticommutator
  have hAnomaly : D * M - M * D ≠ 0 := by
    intro hcomm
    have hcomm' : D * M = M * D := sub_eq_zero.mp hcomm
    have htwice : D * M + D * M = (5 : Module.End ℝ Carrier) := by
      calc
        D * M + D * M = D * M + M * D := by rw [hcomm']
        _ = (5 : Module.End ℝ Carrier) := hCAR
    have hleft : D * (D * M + D * M) = 0 := by
      calc
        D * (D * M + D * M) = (D * D) * M + (D * D) * M := by
          simp only [mul_add, ← mul_assoc]
        _ = 0 := by rw [hD]; simp
    have hright : D * (5 : Module.End ℝ Carrier) =
        D * (D * M + D * M) := congrArg (fun z : Module.End ℝ Carrier => D * z) htwice.symm
    have hfiveD : (5 : ℝ) • D = 0 := by
      have h := hright.trans hleft
      have hscalar : D * (5 : Module.End ℝ Carrier) = (5 : ℝ) • D := by
        apply LinearMap.ext
        intro v
        simp [Algebra.smul_def]
        exact (Nat.cast_smul_eq_nsmul ℝ 5 (D v)).symm
      exact hscalar.symm ▸ h
    have hDzero : D = 0 := (smul_eq_zero.mp hfiveD).resolve_left (by norm_num)
    have hfiveZero : (5 : Module.End ℝ Carrier) = 0 := by
      calc
        (5 : Module.End ℝ Carrier) = D * M + M * D := hCAR.symm
        _ = 0 := by rw [hDzero]; simp
    have hfiveNe : (5 : Module.End ℝ Carrier) ≠ 0 := by
      have hrepr : (5 : Module.End ℝ Carrier) = (5 : ℝ) • (1 : Module.End ℝ Carrier) := by
        norm_num [Algebra.smul_def, map_ofNat]
      rw [hrepr]
      exact smul_ne_zero (by norm_num) one_ne_zero
    exact hfiveNe hfiveZero
  have hEntry : (H * H) 0 1 = D * M - M * D := by
    have hsquare := massiveBdGHamiltonian_sq_with_commutator D M
    have hentry := congrArg
      (fun X : InfoGeometry.Physics.BdGBlock (Module.End ℝ Carrier) => X 0 1) hsquare
    simpa [H, massiveBdGHamiltonian] using hentry
  refine ⟨hD, hM, hCAR, hAnomaly, ?_, ?_⟩
  · rw [hEntry]
    exact hAnomaly
  · exact massiveBdGHamiltonian_andreev_anomaly_cancellation D M

/-- The particle part of the three-color CAR mass, before representing it on
the common CCR–Fock carrier. -/
def cl55ThreeColorCreation : Cl55 :=
  ∑ i : Fin 3, creation55 (Fin.castAdd 2 i)

/-- The hole part of the three-color CAR mass, before representing it on the
common CCR–Fock carrier. -/
def cl55ThreeColorAnnihilation : Cl55 :=
  ∑ i : Fin 3, annihilation55 (Fin.castAdd 2 i)

/-- The finite color mass is the particle–hole sum of its three CAR modes. -/
theorem nativeThreeColorMass_eq_creation_add_annihilation :
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana =
      cl55ThreeColorCreation + cl55ThreeColorAnnihilation := by
  simp [InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana,
    cl55ThreeColorCreation, cl55ThreeColorAnnihilation, Finset.sum_add_distrib]

private theorem cl55ThreeColorCreation_square :
    cl55ThreeColorCreation * cl55ThreeColorCreation = 0 := by
  have hsq : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      creation55 (Fin.castAdd 2 i) * creation55 (Fin.castAdd 2 i) = 0 :=
    fun i _ => creation55_sq (Fin.castAdd 2 i)
  have hanti : ∀ i j, i ∈ (Finset.univ : Finset (Fin 3)) →
      j ∈ (Finset.univ : Finset (Fin 3)) → i ≠ j →
      creation55 (Fin.castAdd 2 i) * creation55 (Fin.castAdd 2 j) +
        creation55 (Fin.castAdd 2 j) * creation55 (Fin.castAdd 2 i) = 0 := by
    intro i j _ _ hij
    exact creation55_anticommutator (Fin.castAdd 2 i) (Fin.castAdd 2 j)
  simpa [cl55ThreeColorCreation] using
    sum_square_zero_of_anticommuting Finset.univ
      (fun i : Fin 3 => creation55 (Fin.castAdd 2 i)) hsq hanti

private theorem cl55ThreeColorAnnihilation_square :
    cl55ThreeColorAnnihilation * cl55ThreeColorAnnihilation = 0 := by
  have hsq : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      annihilation55 (Fin.castAdd 2 i) * annihilation55 (Fin.castAdd 2 i) = 0 :=
    fun i _ => annihilation55_sq (Fin.castAdd 2 i)
  have hanti : ∀ i j, i ∈ (Finset.univ : Finset (Fin 3)) →
      j ∈ (Finset.univ : Finset (Fin 3)) → i ≠ j →
      annihilation55 (Fin.castAdd 2 i) * annihilation55 (Fin.castAdd 2 j) +
        annihilation55 (Fin.castAdd 2 j) * annihilation55 (Fin.castAdd 2 i) = 0 := by
    intro i j _ _ hij
    exact annihilation55_anticommutator (Fin.castAdd 2 i) (Fin.castAdd 2 j)
  simpa [cl55ThreeColorAnnihilation] using
    sum_square_zero_of_anticommuting Finset.univ
      (fun i : Fin 3 => annihilation55 (Fin.castAdd 2 i)) hsq hanti

/-- The three-color particle and hole sums retain their exact CAR relation in
the finite Clifford algebra. The scalar on the right is the count of the
three embedded color modes. -/
theorem nativeThreeColor_creation_annihilation_CAR :
    cl55ThreeColorCreation * cl55ThreeColorAnnihilation +
      cl55ThreeColorAnnihilation * cl55ThreeColorCreation = (3 : Cl55) := by
  have hmass :=
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeColor_and_complement_mass_squares.1
  rw [nativeThreeColorMass_eq_creation_add_annihilation] at hmass
  have hthree : (3 : ℝ) • (1 : Cl55) = (3 : Cl55) := by
    norm_num [Algebra.smul_def, map_ofNat]
  rw [hthree] at hmass
  calc
    cl55ThreeColorCreation * cl55ThreeColorAnnihilation +
        cl55ThreeColorAnnihilation * cl55ThreeColorCreation =
      (cl55ThreeColorCreation + cl55ThreeColorAnnihilation) ^ 2 := by
        simp only [pow_two]
        noncomm_ring [cl55ThreeColorCreation_square, cl55ThreeColorAnnihilation_square]
    _ = 3 := by simpa [pow_two] using hmass

/-- The three-color particle and hole operators, represented on the same
polynomial–Fock colimit carrier as the CCR generators. -/
def colimitThreeColorCreation : Module.End ℝ Carrier :=
  cl55ColimitSupercarrierRep cl55ThreeColorCreation

def colimitThreeColorAnnihilation : Module.End ℝ Carrier :=
  cl55ColimitSupercarrierRep cl55ThreeColorAnnihilation

/-- The color particle–hole CAR relation survives on the shared CCR–CAR
carrier, with its nonzero rank-three central term. -/
theorem colimit_supercarrier_threeColor_CAR :
    colimitThreeColorCreation * colimitThreeColorCreation = 0 ∧
    colimitThreeColorAnnihilation * colimitThreeColorAnnihilation = 0 ∧
    colimitThreeColorCreation * colimitThreeColorAnnihilation +
      colimitThreeColorAnnihilation * colimitThreeColorCreation =
        (3 : Module.End ℝ Carrier) := by
  have hcreate := congrArg cl55ColimitSupercarrierRep cl55ThreeColorCreation_square
  have hannihilate := congrArg cl55ColimitSupercarrierRep cl55ThreeColorAnnihilation_square
  have hCAR := congrArg cl55ColimitSupercarrierRep
    nativeThreeColor_creation_annihilation_CAR
  exact ⟨by simpa only [colimitThreeColorCreation, map_mul, map_zero] using hcreate,
    by simpa only [colimitThreeColorAnnihilation, map_mul, map_zero] using hannihilate,
    by simpa only [colimitThreeColorCreation, colimitThreeColorAnnihilation,
      map_add, map_mul, map_ofNat] using hCAR⟩

/-- The native rank-three Cl(5,5) mass retains its exact CAR square on the
shared polynomial–Fock colimit carrier. -/
theorem colimit_supercarrier_threeColorMass_square :
    cl55ColimitSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana *
      cl55ColimitSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana =
      (3 : Module.End ℝ Carrier) := by
  have hNat : (3 : ℝ) • (1 : Cl55) = (3 : Cl55) := by
    norm_num [Algebra.smul_def, map_ofNat]
  have h := congrArg cl55ColimitSupercarrierRep
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeColor_and_complement_mass_squares.1
  rw [hNat] at h
  simpa only [map_mul, map_ofNat] using h

/-- The sixth cyclotomic polynomial of the represented rank-three mass
square has value seven on the shared CCR–CAR carrier. This is the polynomial
readout of the same operator identity, not a spectral-coordinate surrogate. -/
theorem colimit_supercarrier_threeColorMass_cyclotomic_higgs :
    InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix
        (cl55ColimitSupercarrierRep
            InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana *
          cl55ColimitSupercarrierRep
            InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana) =
      (7 : Module.End ℝ Carrier) := by
  rw [colimit_supercarrier_threeColorMass_square]
  norm_num [InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix,
    Algebra.smul_def]

/-- Each polynomial CCR generator commutes with the represented three-color
Majorana mass. Thus the bosonic and color-particle–hole interactions coexist
as commuting actions on the same inductive-colimit carrier. -/
theorem CCR_generators_commute_with_threeColor_mass (i : Fin 5) :
    bosonCreation i * cl55ColimitSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana =
      cl55ColimitSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana *
          bosonCreation i ∧
    bosonAnnihilation i * cl55ColimitSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana =
      cl55ColimitSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana *
          bosonAnnihilation i := by
  constructor
  · change ((create i).rTensor FockInfinity).comp
        ((cl55FockInfinityRepresentation
          InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana).lTensor
          (WavePolynomial (Fin 5))) =
      ((cl55FockInfinityRepresentation
          InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana).lTensor
          (WavePolynomial (Fin 5))).comp ((create i).rTensor FockInfinity)
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  · change ((annihilate i).rTensor FockInfinity).comp
        ((cl55FockInfinityRepresentation
          InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana).lTensor
          (WavePolynomial (Fin 5))) =
      ((cl55FockInfinityRepresentation
          InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana).lTensor
          (WavePolynomial (Fin 5))).comp ((annihilate i).rTensor FockInfinity)
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- Andreev reflection cancels the three-color particle–hole commutator on
the same carrier where the polynomial CCR acts. The unreﬂected off-diagonal
BdG entry remains nonzero, certified from the rank-three CAR term. -/
theorem colimit_supercarrier_threeColor_mass_and_andreev_cancellation :
    let D := colimitThreeColorCreation
    let M := colimitThreeColorAnnihilation
    let H := massiveBdGHamiltonian D M
    D * D = 0 ∧
    M * M = 0 ∧
    D * M + M * D = (3 : Module.End ℝ Carrier) ∧
    D * M - M * D ≠ 0 ∧
    (H * H) 0 1 = D * M - M * D ∧
    H * H + andreevSwap * (H * H) * andreevSwap =
      !![D * D + M * M + (M * M + D * D), 0;
         0, M * M + D * D + (D * D + M * M)] := by
  dsimp
  let D := colimitThreeColorCreation
  let M := colimitThreeColorAnnihilation
  let H := massiveBdGHamiltonian D M
  letI : Nontrivial Carrier := commonCarrier_nontrivial
  rcases colimit_supercarrier_threeColor_CAR with ⟨hD, hM, hCAR⟩
  have hAnomaly : D * M - M * D ≠ 0 := by
    intro hcomm
    have hcomm' : D * M = M * D := sub_eq_zero.mp hcomm
    have hdouble : D * M + D * M = (3 : Module.End ℝ Carrier) := by
      calc
        D * M + D * M = D * M + M * D := by rw [hcomm']
        _ = (3 : Module.End ℝ Carrier) := hCAR
    have hleft : D * (D * M + D * M) = 0 := by
      calc
        D * (D * M + D * M) = (D * D) * M + (D * D) * M := by
          simp only [mul_add, ← mul_assoc]
        _ = 0 := by rw [hD]; simp
    have hzero : D * (3 : Module.End ℝ Carrier) = 0 := by
      calc
        D * (3 : Module.End ℝ Carrier) = D * (D * M + D * M) :=
          congrArg (fun z : Module.End ℝ Carrier => D * z) hdouble.symm
        _ = 0 := hleft
    have hDzero : D = 0 := by
      have hscalar : (3 : ℝ) • D = 0 := by
        have h := hzero
        have hmul : D * (3 : Module.End ℝ Carrier) = (3 : ℝ) • D := by
          apply LinearMap.ext
          intro v
          simp [Algebra.smul_def]
          exact (Nat.cast_smul_eq_nsmul ℝ 3 (D v)).symm
        exact hmul.symm.trans h
      exact (smul_eq_zero.mp hscalar).resolve_left (by norm_num)
    have hthreeZero : (3 : Module.End ℝ Carrier) = 0 := by
      calc
        (3 : Module.End ℝ Carrier) = D * M + M * D := hCAR.symm
        _ = 0 := by rw [hDzero]; simp
    have hthreeNe : (3 : Module.End ℝ Carrier) ≠ 0 := by
      have hrepr : (3 : Module.End ℝ Carrier) = (3 : ℝ) • (1 : Module.End ℝ Carrier) := by
        norm_num [Algebra.smul_def, map_ofNat]
      rw [hrepr]
      exact smul_ne_zero (by norm_num) one_ne_zero
    exact hthreeNe hthreeZero
  have hEntry : (H * H) 0 1 = D * M - M * D := by
    have hsquare := massiveBdGHamiltonian_sq_with_commutator D M
    have hentry := congrArg
      (fun X : InfoGeometry.Physics.BdGBlock (Module.End ℝ Carrier) => X 0 1) hsquare
    simpa [H, massiveBdGHamiltonian] using hentry
  exact ⟨hD, hM, hCAR, hAnomaly, hEntry,
    massiveBdGHamiltonian_andreev_anomaly_cancellation D M⟩

/-! ### Finite Fock stage to the common CCR–CAR colimit carrier

The representation above is the colimit action.  The following map makes its
finite-stage origin explicit on the same polynomial tensor factor. -/

/-- The finite five-mode Fock stage with the same polynomial CCR factor. -/
abbrev FiniteStageCarrier :=
  WavePolynomial (Fin 5) ⊗[ℝ] FockStage 5

/-- The finite-stage Cl(5,5) action on the polynomial–Fock tensor carrier. -/
def cl55FiniteStageSupercarrierRep :
    Cl55 →+* Module.End ℝ FiniteStageCarrier :=
  (Module.End.lTensorAlgHom ℝ (FockStage 5) (WavePolynomial (Fin 5))).toRingHom.comp
    ((InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.towerSpinorRep 5).toRingHom.comp
      (cl55ToSplitCl55.toRingHom))

/-- The native five-mode mass on the actual finite five-mode Fock carrier. -/
def finiteStageFiveModeMass : Module.End ℝ FiniteStageCarrier :=
  cl55FiniteStageSupercarrierRep
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana

/-- The finite Fock representation preserves the exact five-mode CAR mass
square before passage to the algebraic colimit. -/
theorem finiteStage_fiveModeMass_square :
    finiteStageFiveModeMass * finiteStageFiveModeMass =
      (5 : Module.End ℝ FiniteStageCarrier) := by
  have hNat : (5 : ℝ) • (1 : Cl55) = (5 : Cl55) := by
    norm_num [Algebra.smul_def, map_ofNat]
  have h := congrArg cl55FiniteStageSupercarrierRep
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana_square
  rw [hNat] at h
  simpa only [finiteStageFiveModeMass, map_mul, map_ofNat] using h

/-- The finite-stage carrier embeds into the common polynomial–Fock colimit
carrier by the identity on wave polynomials and the owned Fock-stage map. -/
def finiteStageToColimit : FiniteStageCarrier →ₗ[ℝ] Carrier :=
  TensorProduct.map (LinearMap.id : WavePolynomial (Fin 5) →ₗ[ℝ] WavePolynomial (Fin 5))
    (DirectLimit.Module.of ℝ ℕ FockStage
      (fun m n h => fockStageMap m n h) 5)

/-- The finite Cl(5,5) action intertwines with the actual colimit action under
the finite-stage embedding, on every tensor state. -/
theorem cl55_finite_stage_action_intertwines_colimit (x : Cl55)
    (v : FiniteStageCarrier) :
    finiteStageToColimit (cl55FiniteStageSupercarrierRep x v) =
      cl55ColimitSupercarrierRep x (finiteStageToColimit v) := by
  let rho5 : Module.End ℝ (FockStage 5) :=
    InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.towerSpinorRep 5
      (cl55ToSplitCl55 x)
  let rhoInf : Module.End ℝ FockInfinity := cl55FockInfinityRepresentation x
  have hintertwine :
      (DirectLimit.Module.of ℝ ℕ FockStage
        (fun m n h => fockStageMap m n h) 5).comp rho5 =
        rhoInf.comp (DirectLimit.Module.of ℝ ℕ FockStage
          (fun m n h => fockStageMap m n h) 5) := by
    apply LinearMap.ext
    intro ψ
    exact (cl55FockInfinityRepresentation_on_stage x ψ).symm
  change (TensorProduct.map (LinearMap.id : WavePolynomial (Fin 5) →ₗ[ℝ]
      WavePolynomial (Fin 5))
      (DirectLimit.Module.of ℝ ℕ FockStage
        (fun m n h => fockStageMap m n h) 5))
      (rho5.lTensor (WavePolynomial (Fin 5)) v) =
    rhoInf.lTensor (WavePolynomial (Fin 5))
      ((TensorProduct.map (LinearMap.id : WavePolynomial (Fin 5) →ₗ[ℝ]
        WavePolynomial (Fin 5))
        (DirectLimit.Module.of ℝ ℕ FockStage
          (fun m n h => fockStageMap m n h) 5)) v)
  rw [LinearMap.map_lTensor, LinearMap.lTensor_map, hintertwine]

/-- Squaring the finite five-mode mass commutes with the finite-stage inclusion
into the Fock colimit. This identifies the finite CAR energy value on every
embedded state, rather than only identifying the two generator actions. -/
theorem finite_stage_fiveModeMass_square_transports (v : FiniteStageCarrier) :
    finiteStageToColimit ((finiteStageFiveModeMass * finiteStageFiveModeMass) v) =
      (5 : Module.End ℝ Carrier) (finiteStageToColimit v) := by
  let mass := InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana
  let rhoFinite := cl55FiniteStageSupercarrierRep mass
  let rhoLimit := cl55ColimitSupercarrierRep mass
  have haction (w : FiniteStageCarrier) :
      finiteStageToColimit (rhoFinite w) = rhoLimit (finiteStageToColimit w) :=
    cl55_finite_stage_action_intertwines_colimit mass w
  calc
    finiteStageToColimit ((finiteStageFiveModeMass * finiteStageFiveModeMass) v) =
        rhoLimit (rhoLimit (finiteStageToColimit v)) := by
      change finiteStageToColimit (rhoFinite (rhoFinite v)) = _
      rw [haction, haction]
    _ = (5 : Module.End ℝ Carrier) (finiteStageToColimit v) := by
      have hNat : (5 : ℝ) • (1 : Cl55) = (5 : Cl55) := by
        norm_num [Algebra.smul_def, map_ofNat]
      have hRho := congrArg cl55FockInfinityRepresentation
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana_square
      rw [hNat] at hRho
      simp only [map_mul, map_ofNat] at hRho
      have hRho' : cl55FockInfinityRepresentation mass *
          cl55FockInfinityRepresentation mass =
          (5 : Module.End ℝ FockInfinity) := hRho
      let lift := Module.End.lTensorAlgHom ℝ FockInfinity (WavePolynomial (Fin 5))
      have hLift := congrArg lift hRho'
      have hmassLift : rhoLimit * rhoLimit = (5 : Module.End ℝ Carrier) := by
        change lift (cl55FockInfinityRepresentation mass) *
          lift (cl55FockInfinityRepresentation mass) =
          (5 : Module.End ℝ Carrier)
        simpa only [lift, map_mul, map_ofNat] using hLift
      have hvalue := congrArg
        (fun T : Module.End ℝ Carrier => T (finiteStageToColimit v)) hmassLift
      simpa using hvalue

/-- The three-color mass has square three on the finite five-mode Fock stage.
This is the rank-three CAR value transported through the existing finite
Cl(5,5) representation on the polynomial tensor carrier. -/
theorem finiteStage_threeColorMass_square :
    cl55FiniteStageSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana *
      cl55FiniteStageSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana =
      (3 : Module.End ℝ FiniteStageCarrier) := by
  have hNat : (3 : ℝ) • (1 : Cl55) = (3 : Cl55) := by
    norm_num [Algebra.smul_def, map_ofNat]
  have h := congrArg cl55FiniteStageSupercarrierRep
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeColor_and_complement_mass_squares.1
  rw [hNat] at h
  simpa only [map_mul, map_ofNat] using h

/-- The finite three-color CAR mass-square identity is preserved by the
actual finite-stage-to-colimit embedding, pointwise on every tensor state. -/
theorem finite_stage_threeColorMass_square_transports (v : FiniteStageCarrier) :
    finiteStageToColimit
        ((cl55FiniteStageSupercarrierRep
          InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana *
          cl55FiniteStageSupercarrierRep
            InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana) v) =
      (3 : Module.End ℝ Carrier) (finiteStageToColimit v) := by
  let mass := InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeThreeColorModeMajorana
  let rhoFinite := cl55FiniteStageSupercarrierRep mass
  let rhoLimit := cl55ColimitSupercarrierRep mass
  have haction (w : FiniteStageCarrier) :
      finiteStageToColimit (rhoFinite w) = rhoLimit (finiteStageToColimit w) :=
    cl55_finite_stage_action_intertwines_colimit mass w
  calc
    finiteStageToColimit ((rhoFinite * rhoFinite) v) =
        rhoLimit (rhoLimit (finiteStageToColimit v)) := by
      change finiteStageToColimit (rhoFinite (rhoFinite v)) = _
      rw [haction, haction]
    _ = (3 : Module.End ℝ Carrier) (finiteStageToColimit v) := by
      have hNat : (3 : ℝ) • (1 : Cl55) = (3 : Cl55) := by
        norm_num [Algebra.smul_def, map_ofNat]
      have hRho := congrArg cl55FockInfinityRepresentation
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeColor_and_complement_mass_squares.1
      rw [hNat] at hRho
      simp only [map_mul, map_ofNat] at hRho
      have hRho' : cl55FockInfinityRepresentation mass *
          cl55FockInfinityRepresentation mass = (3 : Module.End ℝ FockInfinity) := hRho
      let lift := Module.End.lTensorAlgHom ℝ FockInfinity (WavePolynomial (Fin 5))
      have hLift := congrArg lift hRho'
      have hmassLift : rhoLimit * rhoLimit = (3 : Module.End ℝ Carrier) := by
        change lift (cl55FockInfinityRepresentation mass) *
          lift (cl55FockInfinityRepresentation mass) = (3 : Module.End ℝ Carrier)
        simpa only [lift, map_mul, map_ofNat] using hLift
      have hvalue := congrArg
        (fun T : Module.End ℝ Carrier => T (finiteStageToColimit v)) hmassLift
      simpa using hvalue

/-- Both polynomial CCR generators are compatible with the finite-stage
embedding, so their exact polynomial commutator survives on the Fock colimit
carrier. -/
theorem finite_stage_CCR_intertwines_colimit (i : Fin 5) (v : FiniteStageCarrier) :
    finiteStageToColimit
        (((Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) (FockStage 5))
          (create i)) v) =
      bosonCreation i (finiteStageToColimit v) ∧
    finiteStageToColimit
        (((Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) (FockStage 5))
          (annihilate i)) v) =
      bosonAnnihilation i (finiteStageToColimit v) := by
  constructor
  · change (TensorProduct.map (LinearMap.id : WavePolynomial (Fin 5) →ₗ[ℝ]
        WavePolynomial (Fin 5))
        (DirectLimit.Module.of ℝ ℕ FockStage
          (fun m n h => fockStageMap m n h) 5))
        ((create i).rTensor (FockStage 5) v) =
      (create i).rTensor FockInfinity
        ((TensorProduct.map (LinearMap.id : WavePolynomial (Fin 5) →ₗ[ℝ]
          WavePolynomial (Fin 5))
          (DirectLimit.Module.of ℝ ℕ FockStage
            (fun m n h => fockStageMap m n h) 5)) v)
    rw [LinearMap.map_rTensor, LinearMap.rTensor_map]
    simp
  · change (TensorProduct.map (LinearMap.id : WavePolynomial (Fin 5) →ₗ[ℝ]
        WavePolynomial (Fin 5))
        (DirectLimit.Module.of ℝ ℕ FockStage
          (fun m n h => fockStageMap m n h) 5))
        ((annihilate i).rTensor (FockStage 5) v) =
      (annihilate i).rTensor FockInfinity
        ((TensorProduct.map (LinearMap.id : WavePolynomial (Fin 5) →ₗ[ℝ]
          WavePolynomial (Fin 5))
          (DirectLimit.Module.of ℝ ℕ FockStage
            (fun m n h => fockStageMap m n h) 5)) v)
    rw [LinearMap.map_rTensor, LinearMap.rTensor_map]
    simp

/-- Any polynomial-factor endomorphism commutes with the represented
Cl(5,5) action on the Fock-colimit factor. This extends the generator-level
CCR/CAR commutation to every Clifford interaction operator. -/
theorem polynomial_operator_commutes_with_colimit_Cl55
    (b : Module.End ℝ (WavePolynomial (Fin 5))) (x : Cl55) :
    Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b *
        cl55ColimitSupercarrierRep x =
      cl55ColimitSupercarrierRep x *
        Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b := by
  change (b.rTensor FockInfinity).comp
      ((cl55FockInfinityRepresentation x).lTensor (WavePolynomial (Fin 5))) =
    ((cl55FockInfinityRepresentation x).lTensor (WavePolynomial (Fin 5))).comp
      (b.rTensor FockInfinity)
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- The polynomial CCR action commutes with every represented Clifford
superbracket. This carries the cross-factor compatibility from CAR generators
to the even commutator and odd anticommutator products that generate the
Cl(5,5) superalgebra. -/
theorem polynomial_operator_commutes_with_colimit_superBracket
    (b : Module.End ℝ (WavePolynomial (Fin 5))) (p q : Bool) (x y : Cl55) :
    Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b *
        InfoGeometry.Algebra.SupergradedBracket.superBracket p q
          (cl55ColimitSupercarrierRep x) (cl55ColimitSupercarrierRep y) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket p q
          (cl55ColimitSupercarrierRep x) (cl55ColimitSupercarrierRep y) *
        Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b := by
  have hmap : cl55ColimitSupercarrierRep
      (InfoGeometry.Algebra.SupergradedBracket.superBracket p q x y) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket p q
        (cl55ColimitSupercarrierRep x) (cl55ColimitSupercarrierRep y) := by
    cases p <;> cases q <;>
      simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
        InfoGeometry.Algebra.SupergradedBracket.commutator,
        InfoGeometry.Algebra.SupergradedBracket.anticommutator]
  rw [← hmap]
  exact polynomial_operator_commutes_with_colimit_Cl55 b
    (InfoGeometry.Algebra.SupergradedBracket.superBracket p q x y)

/-- The CCR operator acts identically on the particle and hole blocks and
commutes with the full mass-coupled BdG operator on the shared carrier. The
proof uses the coefficient commutation theorem above for both Cl(5,5) entries. -/
theorem polynomial_operator_commutes_with_colimit_massiveBdG
    (b : Module.End ℝ (WavePolynomial (Fin 5))) (D M : Cl55) :
    Matrix.diagonal (fun _ : Fin 2 =>
        Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b) *
        InfoGeometry.Physics.massiveBdGHamiltonian
          (cl55ColimitSupercarrierRep D) (cl55ColimitSupercarrierRep M) =
      InfoGeometry.Physics.massiveBdGHamiltonian
          (cl55ColimitSupercarrierRep D) (cl55ColimitSupercarrierRep M) *
        Matrix.diagonal (fun _ : Fin 2 =>
          Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b) := by
  have hD := polynomial_operator_commutes_with_colimit_Cl55 b D
  have hM := polynomial_operator_commutes_with_colimit_Cl55 b M
  have hmulNegRight (f g : Module.End ℝ Carrier) : f * -g = -(f * g) := by
    ext v
    simp
  have hnegMulLeft (f g : Module.End ℝ Carrier) : -f * g = -(f * g) := by
    ext v
    simp
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
      InfoGeometry.Physics.massiveBdGHamiltonian, Matrix.of_apply]
    exact hD
  · simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
      InfoGeometry.Physics.massiveBdGHamiltonian, Matrix.of_apply]
    exact hM
  · simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
      InfoGeometry.Physics.massiveBdGHamiltonian, Matrix.of_apply]
    exact hM
  · simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
      InfoGeometry.Physics.massiveBdGHamiltonian, Matrix.of_apply]
    let Bop := Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b
    change Bop *
        (-cl55ColimitSupercarrierRep D) =
      (-cl55ColimitSupercarrierRep D) * Bop
    calc
      _ = -(Bop * cl55ColimitSupercarrierRep D) := by
        exact hmulNegRight Bop (cl55ColimitSupercarrierRep D)
      _ = -(cl55ColimitSupercarrierRep D * Bop) := congrArg Neg.neg hD
      _ = _ := (hnegMulLeft (cl55ColimitSupercarrierRep D) Bop).symm

/-- The lifted CCR algebra also commutes with the existing degree-four
cyclotomic Higgs polynomial of the full mass-coupled BdG operator. The proof
transports commutation through operator powers; it does not diagonalize the
BdG matrix or replace the operator polynomial by scalar data. -/
theorem polynomial_operator_commutes_with_colimit_massiveBdG_higgs
    (b : Module.End ℝ (WavePolynomial (Fin 5))) (D M : Cl55) :
    Matrix.diagonal (fun _ : Fin 2 =>
        Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b) *
        InfoGeometry.Physics.operatorCyclotomicHiggs
          (InfoGeometry.Physics.massiveBdGHamiltonian
            (cl55ColimitSupercarrierRep D) (cl55ColimitSupercarrierRep M)) =
      InfoGeometry.Physics.operatorCyclotomicHiggs
          (InfoGeometry.Physics.massiveBdGHamiltonian
            (cl55ColimitSupercarrierRep D) (cl55ColimitSupercarrierRep M)) *
        Matrix.diagonal (fun _ : Fin 2 =>
          Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b) := by
  let T : InfoGeometry.Physics.BdGBlock (Module.End ℝ Carrier) :=
    Matrix.diagonal fun _ : Fin 2 =>
      Module.End.rTensorAlgHom ℝ (WavePolynomial (Fin 5)) FockInfinity b
  let H : InfoGeometry.Physics.BdGBlock (Module.End ℝ Carrier) :=
    InfoGeometry.Physics.massiveBdGHamiltonian
      (cl55ColimitSupercarrierRep D) (cl55ColimitSupercarrierRep M)
  have hcomm : T * H = H * T :=
    polynomial_operator_commutes_with_colimit_massiveBdG b D M
  change T * (H ^ 4 - H ^ 2 + 1) =
    (H ^ 4 - H ^ 2 + 1) * T
  have hT_H : Commute T H := hcomm
  have hT_H4 : Commute T (H ^ 4) := hT_H.pow_right 4
  have hT_H2 : Commute T (H ^ 2) := hT_H.pow_right 2
  have hT_diff : Commute T (H ^ 4 - H ^ 2) :=
    Commute.sub_right (a := T) hT_H4 hT_H2
  exact Commute.add_right hT_diff (Commute.one_right T)

/-! ### Five-mode mass transport to the shared CCR–CAR colimit

The finite five-mode mass and its cyclotomic value are owned by
`Cl55AllModeMassCoercivity`.  These results carry those exact native Clifford
operators through the existing Fock-colimit representation on the same
polynomial–Fock carrier used by the CCR action. -/

/-- The five-mode Clifford mass, represented on the shared CCR–Fock colimit,
has the finite CAR square `5`.  This uses the existing native mass theorem
and the actual colimit ring representation. -/
theorem colimit_supercarrier_fiveModeMass_square :
    cl55ColimitSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana *
      cl55ColimitSupercarrierRep
        InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana =
      (5 : Module.End ℝ Carrier) := by
  let rho := cl55FockInfinityRepresentation
  let lift := Module.End.lTensorAlgHom ℝ FockInfinity (WavePolynomial (Fin 5))
  have hNat : (5 : ℝ) • (1 : Cl55) = (5 : Cl55) := by
    norm_num [Algebra.smul_def, map_ofNat]
  have hRho := congrArg rho
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana_square
  rw [hNat] at hRho
  simp only [rho, map_ofNat, map_mul] at hRho
  have hRho' : rho
      InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana *
      rho InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana =
      (5 : Module.End ℝ FockInfinity) := hRho
  have h := congrArg lift hRho'
  change lift (rho
      InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana) *
      lift (rho InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana) =
      (5 : Module.End ℝ Carrier)
  simpa only [lift, map_mul, map_ofNat] using h

/-- The sixth cyclotomic Higgs polynomial of the represented five-mode mass
has value `21` on the shared CCR–Fock colimit.  Thus the finite CAR mass
calibration and the CCR action coexist on this carrier without changing the
operator polynomial or passing through scalar eigenvalue data. -/
theorem colimit_supercarrier_fiveModeMass_cyclotomic_higgs :
    InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix
        (cl55ColimitSupercarrierRep
            InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana *
          cl55ColimitSupercarrierRep
            InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana) =
      (21 : Module.End ℝ Carrier) := by
  let rho := cl55FockInfinityRepresentation
  let lift := Module.End.lTensorAlgHom ℝ FockInfinity (WavePolynomial (Fin 5))
  have hNat : (21 : ℝ) • (1 : Cl55) = (21 : Cl55) := by
    norm_num [Algebra.smul_def, map_ofNat]
  have hRho := congrArg rho
    InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana_cyclotomic_higgs
  rw [hNat] at hRho
  simp only [rho, map_ofNat, InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix,
    map_mul, map_sub, map_add, map_one] at hRho
  have hRho' : InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix
      (rho InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana *
        rho InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana) =
      (21 : Module.End ℝ FockInfinity) := hRho
  have h := congrArg lift hRho'
  change InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix
      (lift (rho InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana) *
        lift (rho InfoGeometry.Canonical.Cl55AllModeMassCoercivity.nativeFiveModeMajorana)) =
      (21 : Module.End ℝ Carrier)
  simpa only [lift, InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix,
    map_mul, map_sub, map_add, map_one, map_ofNat] using h

end InfoGeometry.Canonical.CARCCRColimitSupercarrier
