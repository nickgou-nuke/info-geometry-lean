/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence
import InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
import InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-!
# Finite occupation Fock CAR in the complex algebraic matrix direct limit

This candidate transports the repository's real finite occupation Fock
operator tower into the existing complex algebraic Cuntz matrix carrier.
It does not identify that algebraic carrier with a C*-completion, nor does it
identify the occupation model with the separate exterior-algebra Fock owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11AttentionMatrixCARBridge

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.JordanWignerCantorRepresentation

/-- The real finite Clifford carrier used by the occupation tower. -/
abbrev OccupationClStage (n : ℕ) :=
  InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.ClStage n

/-- The coherent real-to-complex finite-stage map followed by the canonical
injection into the existing complex algebraic matrix direct limit. -/
noncomputable def clStageToComplexCarrier (n : ℕ) :
    OccupationClStage n →+* Carrier :=
  (stageInjection n).toRingHom.comp (coherentComplexifyClStage n).toRingHom

/-- The finite-stage maps are compatible with the real Clifford tensor bonds. -/
theorem clStageToComplexCarrier_compatible (n : ℕ) (A : OccupationClStage n) :
    clStageToComplexCarrier (n + 1) (stageBond n A) =
      clStageToComplexCarrier n A := by
  change stageInjection (n + 1)
      (coherentComplexifyClStage (n + 1) (stageEmbed n A)) =
    stageInjection n (coherentComplexifyClStage n A)
  rw [coherentComplexifyClStage_naturality]
  have hstep : concreteMap (Nat.le_succ n) = concreteStep n := by
    change map concreteData (Nat.le.step (le_refl n)) = concreteStep n
    rw [map_succ concreteData (le_refl n)]
    simp [concreteData]
  rw [← hstep]
  exact stageInjection_concrete_transition (Nat.le_succ n)
    (coherentComplexifyClStage n A)

/-- The real `Cl(1,1)` algebraic direct limit maps to the existing complex
matrix algebraic direct limit through its coherent finite-stage
complexification. -/
noncomputable def clLimitToComplexCarrier : ClLimit →+* Carrier :=
  directLimitLift stageBond clStageToComplexCarrier
    (clStageToComplexCarrier_compatible)

@[simp] theorem clLimitToComplexCarrier_stage (n : ℕ) (A : OccupationClStage n) :
    clLimitToComplexCarrier (ofStage n A) =
      stageInjection n (coherentComplexifyClStage n A) := by
  rfl

/-- Transport the preceding map to the repository's real occupation Fock
operator direct limit using its existing global algebra equivalence. -/
noncomputable def fockOperatorLimitToComplexCarrier : FockOpLimit →+* Carrier :=
  clLimitToComplexCarrier.comp clLimitFockOpAlgEquiv.symm.toRingHom

/-- Stage readback for the image of a finite occupation Fock operator. -/
theorem fockOperatorLimitToComplexCarrier_stage (n : ℕ) (T : FockOpStage n) :
    fockOperatorLimitToComplexCarrier (realCantorOfStage n T) =
      stageInjection n
        (coherentComplexifyClStage n ((clToFockOp n).symm T)) := by
  change clLimitToComplexCarrier
      (clLimitFockOpEquiv.symm (realCantorOfStage n T)) = _
  rw [clLimitFockOpEquiv_symm_ofStage]
  simp [InfoGeometry.Canonical.JordanWignerCantorColimit.MatOfStage,
    clLimitToComplexCarrier_stage]

/-- The canonical image of a finite-stage Jordan--Wigner creation operator in
the complex algebraic matrix direct-limit carrier. -/
noncomputable def complexCarrierCreation (n : ℕ) (i : Fin n) : Carrier :=
  fockOperatorLimitToComplexCarrier
    (realCantorOfStage n (fockCreation n i))

/-- The canonical image of a finite-stage Jordan--Wigner annihilation
operator in the complex algebraic matrix direct-limit carrier. -/
noncomputable def complexCarrierAnnihilation (n : ℕ) (i : Fin n) : Carrier :=
  fockOperatorLimitToComplexCarrier
    (realCantorOfStage n (fockAnnihilation n i))

@[simp] theorem complexCarrierCreation_stage (n : ℕ) (i : Fin n) :
    complexCarrierCreation n i =
      stageInjection n (coherentComplexifyClStage n (jwCreation n i)) := by
  rw [complexCarrierCreation, fockOperatorLimitToComplexCarrier_stage]
  change stageInjection n (coherentComplexifyClStage n
    ((clToFockOp n).symm (clToFockOp n (jwCreation n i)))) = _
  rw [(clToFockOp n).symm_apply_apply]

@[simp] theorem complexCarrierAnnihilation_stage (n : ℕ) (i : Fin n) :
    complexCarrierAnnihilation n i =
      stageInjection n (coherentComplexifyClStage n (jwAnnihilation n i)) := by
  rw [complexCarrierAnnihilation, fockOperatorLimitToComplexCarrier_stage]
  change stageInjection n (coherentComplexifyClStage n
    ((clToFockOp n).symm (clToFockOp n (jwAnnihilation n i)))) = _
  rw [(clToFockOp n).symm_apply_apply]

/-- The complex-carrier creation family is compatible with the named adjacent
finite-stage Jordan--Wigner generators. -/
theorem complexCarrierCreation_succ (n : ℕ) (i : Fin n) :
    complexCarrierCreation (n + 1) i.castSucc = complexCarrierCreation n i := by
  rw [complexCarrierCreation_stage, complexCarrierCreation_stage]
  change clStageToComplexCarrier (n + 1) (jwCreation (n + 1) i.castSucc) = _
  rw [← matStageEmbed_jwCreation]
  change clStageToComplexCarrier (n + 1) (stageBond n (jwCreation n i)) = _
  exact clStageToComplexCarrier_compatible n (jwCreation n i)

/-- The complex-carrier annihilation family is compatible with the named
adjacent finite-stage Jordan--Wigner generators. -/
theorem complexCarrierAnnihilation_succ (n : ℕ) (i : Fin n) :
    complexCarrierAnnihilation (n + 1) i.castSucc = complexCarrierAnnihilation n i := by
  rw [complexCarrierAnnihilation_stage, complexCarrierAnnihilation_stage]
  change clStageToComplexCarrier (n + 1) (jwAnnihilation (n + 1) i.castSucc) = _
  rw [← matStageEmbed_jwAnnihilation]
  change clStageToComplexCarrier (n + 1) (stageBond n (jwAnnihilation n i)) = _
  exact clStageToComplexCarrier_compatible n (jwAnnihilation n i)

/-! The last-site square-zero declarations are owned by
`Cl11JordanWignerCARBridge`. These inductions transport them to every indexed
finite-stage operator using the existing named-generator successor equations. -/

private theorem jwCreation_sq_zero_all (n : ℕ) : ∀ i : Fin n,
    jwCreation n i * jwCreation n i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      cases i using Fin.lastCases with
      | cast j =>
        rw [← matStageEmbed_jwCreation]
        change stageEmbed n (jwCreation n j) * stageEmbed n (jwCreation n j) = 0
        calc
          stageEmbed n (jwCreation n j) * stageEmbed n (jwCreation n j) =
              stageEmbed n (jwCreation n j * jwCreation n j) :=
            (map_mul (stageEmbed n) (jwCreation n j) (jwCreation n j)).symm
          _ = stageEmbed n 0 := by rw [ih j]
          _ = 0 := map_zero (stageEmbed n)
      | last =>
        simpa [Fin.last] using
          InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwCreation_last_sq n

private theorem jwAnnihilation_sq_zero_all (n : ℕ) : ∀ i : Fin n,
    jwAnnihilation n i * jwAnnihilation n i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      cases i using Fin.lastCases with
      | cast j =>
        rw [← matStageEmbed_jwAnnihilation]
        change stageEmbed n (jwAnnihilation n j) * stageEmbed n (jwAnnihilation n j) = 0
        calc
          stageEmbed n (jwAnnihilation n j) * stageEmbed n (jwAnnihilation n j) =
              stageEmbed n (jwAnnihilation n j * jwAnnihilation n j) :=
            (map_mul (stageEmbed n) (jwAnnihilation n j) (jwAnnihilation n j)).symm
          _ = stageEmbed n 0 := by rw [ih j]
          _ = 0 := map_zero (stageEmbed n)
      | last =>
        simpa [Fin.last] using
          InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwAnnihilation_last_sq n

/-- Each indexed finite occupation creation generator remains nilpotent in the
complex algebraic direct-limit carrier. -/
theorem complexCarrierCreation_sq_zero (n : ℕ) (i : Fin n) :
    complexCarrierCreation n i * complexCarrierCreation n i = 0 := by
  simp only [complexCarrierCreation_stage]
  change clStageToComplexCarrier n (jwCreation n i) *
      clStageToComplexCarrier n (jwCreation n i) = 0
  calc
    _ = clStageToComplexCarrier n (jwCreation n i * jwCreation n i) := by
      rw [map_mul]
    _ = 0 := by rw [jwCreation_sq_zero_all n i, map_zero]

/-- Each indexed finite occupation annihilation generator remains nilpotent in
the complex algebraic direct-limit carrier. -/
theorem complexCarrierAnnihilation_sq_zero (n : ℕ) (i : Fin n) :
    complexCarrierAnnihilation n i * complexCarrierAnnihilation n i = 0 := by
  simp only [complexCarrierAnnihilation_stage]
  change clStageToComplexCarrier n (jwAnnihilation n i) *
      clStageToComplexCarrier n (jwAnnihilation n i) = 0
  calc
    _ = clStageToComplexCarrier n (jwAnnihilation n i * jwAnnihilation n i) := by
      rw [map_mul]
    _ = 0 := by rw [jwAnnihilation_sq_zero_all n i, map_zero]

/-- The mixed CAR anticommutator of the transported operators is the Kronecker
delta in the complex full-matrix direct-limit carrier. -/
theorem complexCarrier_mixed_car (n : ℕ) (i j : Fin n) :
    complexCarrierAnnihilation n i * complexCarrierCreation n j +
      complexCarrierCreation n j * complexCarrierAnnihilation n i =
        if i = j then 1 else 0 := by
  simp only [complexCarrierAnnihilation_stage, complexCarrierCreation_stage]
  change (clStageToComplexCarrier n (jwAnnihilation n i) *
      clStageToComplexCarrier n (jwCreation n j) +
    clStageToComplexCarrier n (jwCreation n j) *
      clStageToComplexCarrier n (jwAnnihilation n i)) = _
  rw [← map_mul, ← map_mul, ← map_add,
    InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwAnnihilation_creation_anticommutator]
  split_ifs with h
  · exact map_one (clStageToComplexCarrier n)
  · exact map_zero (clStageToComplexCarrier n)

/-- Distinct finite occupation modes retain the creation-creation CAR
anticommutator after passage to the complex algebraic carrier. -/
theorem complexCarrier_creation_cross_site_car (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) :
    complexCarrierCreation n i * complexCarrierCreation n j +
      complexCarrierCreation n j * complexCarrierCreation n i = 0 := by
  rw [complexCarrierCreation_stage, complexCarrierCreation_stage]
  change clStageToComplexCarrier n (jwCreation n i) *
      clStageToComplexCarrier n (jwCreation n j) +
    clStageToComplexCarrier n (jwCreation n j) *
      clStageToComplexCarrier n (jwCreation n i) = 0
  calc
    _ = clStageToComplexCarrier n
        (jwCreation n i * jwCreation n j + jwCreation n j * jwCreation n i) := by
          rw [map_add, map_mul, map_mul]
    _ = 0 := by
      rw [InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute
        n i j hij]
      exact map_zero (clStageToComplexCarrier n)

/-- Distinct finite occupation modes retain the annihilation-annihilation CAR
anticommutator after passage to the complex algebraic carrier. -/
theorem complexCarrier_annihilation_cross_site_car (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) :
    complexCarrierAnnihilation n i * complexCarrierAnnihilation n j +
      complexCarrierAnnihilation n j * complexCarrierAnnihilation n i = 0 := by
  rw [complexCarrierAnnihilation_stage, complexCarrierAnnihilation_stage]
  change clStageToComplexCarrier n (jwAnnihilation n i) *
      clStageToComplexCarrier n (jwAnnihilation n j) +
    clStageToComplexCarrier n (jwAnnihilation n j) *
      clStageToComplexCarrier n (jwAnnihilation n i) = 0
  calc
    _ = clStageToComplexCarrier n
        (jwAnnihilation n i * jwAnnihilation n j +
          jwAnnihilation n j * jwAnnihilation n i) := by
          rw [map_add, map_mul, map_mul]
    _ = 0 := by
      rw [InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.annihilation_cross_site_anticommute
        n i j hij]
      exact map_zero (clStageToComplexCarrier n)

/-- The complete creation-creation CAR anticommutator, including the
same-mode square-zero case. -/
theorem complexCarrier_creation_anticommute (n : ℕ) (i j : Fin n) :
    complexCarrierCreation n i * complexCarrierCreation n j +
      complexCarrierCreation n j * complexCarrierCreation n i = 0 := by
  by_cases hij : i = j
  · subst j
    rw [complexCarrierCreation_sq_zero]
    simp
  · exact complexCarrier_creation_cross_site_car n i j hij

/-- The complete annihilation-annihilation CAR anticommutator, including the
same-mode square-zero case. -/
theorem complexCarrier_annihilation_anticommute (n : ℕ) (i j : Fin n) :
    complexCarrierAnnihilation n i * complexCarrierAnnihilation n j +
      complexCarrierAnnihilation n j * complexCarrierAnnihilation n i = 0 := by
  by_cases hij : i = j
  · subst j
    rw [complexCarrierAnnihilation_sq_zero]
    simp
  · exact complexCarrier_annihilation_cross_site_car n i j hij

end InfoGeometry.Canonical.Cl11AttentionMatrixCARBridge
