import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.KKTClosureSymmetry

Repo-native closure-symmetry surface for the Drazin–Penrose–dilation KKT lane.

This file packages the conjugation-invariance notion for the core generators
`(Γ_S, Γ_G, Q_D, H_D, Z_D)` and proves subgroup closure of these symmetries.
-/

namespace InfoGeometry.Canonical.KKTClosure

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Spectral grading generator on the projected Drazin lane. -/
@[rep_depth krein]
noncomputable abbrev GammaS (CIK : CertifiedInverseKernel E) : EndH :=
  CIK.toInformationCartanTriple.GammaS

/-- Geometric grading generator on the projected Drazin lane. -/
@[rep_depth krein]
noncomputable abbrev GammaG (CIK : CertifiedInverseKernel E) : EndH :=
  CIK.GammaG

/-- Net odd generator `Q_D = χ_R - χ_L`. -/
@[rep_depth krein]
noncomputable abbrev QD (CIK : CertifiedInverseKernel E) : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.supercharge CIK

/-- Even generator `H_D = Q_D²`. -/
@[rep_depth krein]
noncomputable abbrev HD (CIK : CertifiedInverseKernel E) : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.superHamiltonian CIK

/-- Canonical defect-central channel in the internal split `Q_D² = H + Z`. -/
@[rep_depth krein]
noncomputable abbrev ZD (CIK : CertifiedInverseKernel E) : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral CIK

/-- Conjugation action by a unit on the operator lane. -/
@[rep_depth operator]
noncomputable def conjugateUnit (U : EndHˣ) (A : EndH) : EndH :=
  (U : EndH) * A * (↑(U⁻¹) : EndH)

@[rep_depth operator, simp]
theorem conjugateUnit_one (A : EndH) :
    conjugateUnit (E := E) (1 : EndHˣ) A = A := by
  simp [conjugateUnit]

@[rep_depth operator, simp]
theorem conjugateUnit_mul (U V : EndHˣ) (A : EndH) :
    conjugateUnit (E := E) (U * V) A
      = conjugateUnit (E := E) U (conjugateUnit (E := E) V A) := by
  simp [conjugateUnit, mul_assoc]

@[rep_depth operator]
theorem conjugateUnit_inv_eq_of_eq
    (U : EndHˣ) (A : EndH)
    (h : conjugateUnit (E := E) U A = A) :
    conjugateUnit (E := E) (U⁻¹) A = A := by
  have h' :
      (↑(U⁻¹) : EndH) * (conjugateUnit (E := E) U A) * (U : EndH)
        = (↑(U⁻¹) : EndH) * A * (U : EndH) := by
    exact congrArg (fun X => (↑(U⁻¹) : EndH) * X * (U : EndH)) h
  have h'' : A = (↑(U⁻¹) : EndH) * A * (U : EndH) := by
    simpa [conjugateUnit, mul_assoc] using h'
  calc
    conjugateUnit (E := E) (U⁻¹) A
        = (↑(U⁻¹) : EndH) * A * (U : EndH) := by
            simp [conjugateUnit, mul_assoc]
    _ = A := by simpa using h''.symm

/-- Conjugation by a unit transports commutators on the operator lane. -/
@[rep_depth operator]
theorem conjugateUnit_commutator (U : EndHˣ) (X Y : EndH) :
    conjugateUnit (E := E) U (DrazinSupercharge.commutator X Y)
      = DrazinSupercharge.commutator
          (conjugateUnit (E := E) U X) (conjugateUnit (E := E) U Y) := by
  ext v
  simp [conjugateUnit, DrazinSupercharge.commutator, mul_assoc, mul_sub, sub_mul]

/-- Conjugation by a unit transports anticommutators on the operator lane. -/
@[rep_depth operator]
theorem conjugateUnit_anticommutator (U : EndHˣ) (X Y : EndH) :
    conjugateUnit (E := E) U (DrazinSupercharge.anticommutator X Y)
      = DrazinSupercharge.anticommutator
          (conjugateUnit (E := E) U X) (conjugateUnit (E := E) U Y) := by
  ext v
  simp [conjugateUnit, DrazinSupercharge.anticommutator, mul_assoc, mul_add, add_mul]

/--
Generator-preservation predicate for KKT closure symmetries:
conjugation invariance of `(Γ_S, Γ_G, Q_D, H_D, Z_D)`.
-/
@[rep_depth transport]
def PreservesKKTGenerators
    (CIK : CertifiedInverseKernel E) (U : EndHˣ) : Prop :=
  conjugateUnit (E := E) U (GammaS CIK) = GammaS CIK
    ∧ conjugateUnit (E := E) U (GammaG CIK) = GammaG CIK
    ∧ conjugateUnit (E := E) U (QD CIK) = QD CIK
    ∧ conjugateUnit (E := E) U (HD CIK) = HD CIK
    ∧ conjugateUnit (E := E) U (ZD CIK) = ZD CIK

/--
Repo-native closure symmetry object for the DPD/KKT lane.
-/
@[rep_depth transport]
structure KKTClosureSymmetry (CIK : CertifiedInverseKernel E) where
  U : EndHˣ
  preserves : PreservesKKTGenerators (E := E) CIK U

/--
Subgroup of unit conjugations preserving `(Γ_S, Γ_G, Q_D, H_D, Z_D)`.
-/
@[rep_depth transport]
def kktClosureSymmetrySubgroup
    (CIK : CertifiedInverseKernel E) : Subgroup EndHˣ where
  carrier := {U | PreservesKKTGenerators (E := E) CIK U}
  one_mem' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [conjugateUnit]
  mul_mem' := by
    intro U V hU hV
    rcases hU with ⟨hUS, hUG, hUQ, hUH, hUZ⟩
    rcases hV with ⟨hVS, hVG, hVQ, hVH, hVZ⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc
        conjugateUnit (E := E) (U * V) (GammaS CIK)
            = conjugateUnit (E := E) U (conjugateUnit (E := E) V (GammaS CIK)) := by
                simp [conjugateUnit_mul]
        _ = conjugateUnit (E := E) U (GammaS CIK) := by rw [hVS]
        _ = GammaS CIK := hUS
    · calc
        conjugateUnit (E := E) (U * V) (GammaG CIK)
            = conjugateUnit (E := E) U (conjugateUnit (E := E) V (GammaG CIK)) := by
                simp [conjugateUnit_mul]
        _ = conjugateUnit (E := E) U (GammaG CIK) := by rw [hVG]
        _ = GammaG CIK := hUG
    · calc
        conjugateUnit (E := E) (U * V) (QD CIK)
            = conjugateUnit (E := E) U (conjugateUnit (E := E) V (QD CIK)) := by
                simp [conjugateUnit_mul]
        _ = conjugateUnit (E := E) U (QD CIK) := by rw [hVQ]
        _ = QD CIK := hUQ
    · calc
        conjugateUnit (E := E) (U * V) (HD CIK)
            = conjugateUnit (E := E) U (conjugateUnit (E := E) V (HD CIK)) := by
                simp [conjugateUnit_mul]
        _ = conjugateUnit (E := E) U (HD CIK) := by rw [hVH]
        _ = HD CIK := hUH
    · calc
        conjugateUnit (E := E) (U * V) (ZD CIK)
            = conjugateUnit (E := E) U (conjugateUnit (E := E) V (ZD CIK)) := by
                simp [conjugateUnit_mul]
        _ = conjugateUnit (E := E) U (ZD CIK) := by rw [hVZ]
        _ = ZD CIK := hUZ
  inv_mem' := by
    intro U hU
    rcases hU with ⟨hUS, hUG, hUQ, hUH, hUZ⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact conjugateUnit_inv_eq_of_eq (E := E) U (GammaS CIK) hUS
    · exact conjugateUnit_inv_eq_of_eq (E := E) U (GammaG CIK) hUG
    · exact conjugateUnit_inv_eq_of_eq (E := E) U (QD CIK) hUQ
    · exact conjugateUnit_inv_eq_of_eq (E := E) U (HD CIK) hUH
    · exact conjugateUnit_inv_eq_of_eq (E := E) U (ZD CIK) hUZ

/--
Any `KKTClosureSymmetry` element lies in the closure-symmetry subgroup.
-/
@[rep_depth transport]
theorem KKTClosureSymmetry.mem_subgroup
    (CIK : CertifiedInverseKernel E)
    (S : KKTClosureSymmetry (E := E) CIK) :
    S.U ∈ kktClosureSymmetrySubgroup (E := E) CIK := by
  exact S.preserves

/--
`[even, odd]` closure witness on the generator packet:
if a unit preserves `(Γ_S, Γ_G, Q_D, H_D, Z_D)`, then it preserves
the commutator lane `[Γ_S, Q_D]`.
-/
@[rep_depth transport]
theorem commutator_GammaS_QD_conjugation_invariant_of_preserves
    (CIK : CertifiedInverseKernel E) (U : EndHˣ)
    (hU : PreservesKKTGenerators (E := E) CIK U) :
    conjugateUnit (E := E) U (DrazinSupercharge.commutator (GammaS CIK) (QD CIK))
      = DrazinSupercharge.commutator (GammaS CIK) (QD CIK) := by
  rcases hU with ⟨hS, _, hQ, _, _⟩
  calc
    conjugateUnit (E := E) U (DrazinSupercharge.commutator (GammaS CIK) (QD CIK))
        = DrazinSupercharge.commutator (conjugateUnit (E := E) U (GammaS CIK))
            (conjugateUnit (E := E) U (QD CIK)) := by
              simpa using conjugateUnit_commutator (E := E) U (GammaS CIK) (QD CIK)
    _ = DrazinSupercharge.commutator (GammaS CIK) (QD CIK) := by simpa [hS, hQ]

/--
`[even, odd]` closure witness on the generator packet:
if a unit preserves `(Γ_S, Γ_G, Q_D, H_D, Z_D)`, then it preserves
the commutator lane `[Γ_G, Q_D]`.
-/
@[rep_depth transport]
theorem commutator_GammaG_QD_conjugation_invariant_of_preserves
    (CIK : CertifiedInverseKernel E) (U : EndHˣ)
    (hU : PreservesKKTGenerators (E := E) CIK U) :
    conjugateUnit (E := E) U (DrazinSupercharge.commutator (GammaG CIK) (QD CIK))
      = DrazinSupercharge.commutator (GammaG CIK) (QD CIK) := by
  rcases hU with ⟨_, hG, hQ, _, _⟩
  calc
    conjugateUnit (E := E) U (DrazinSupercharge.commutator (GammaG CIK) (QD CIK))
        = DrazinSupercharge.commutator (conjugateUnit (E := E) U (GammaG CIK))
            (conjugateUnit (E := E) U (QD CIK)) := by
              simpa using conjugateUnit_commutator (E := E) U (GammaG CIK) (QD CIK)
    _ = DrazinSupercharge.commutator (GammaG CIK) (QD CIK) := by simpa [hG, hQ]

/--
`{odd, odd}` closure witness:
the anticommutator of the odd generator with itself lands in the even lane.
-/
@[rep_depth transport]
theorem anticommutator_QD_QD_eq_two_smul_HD (CIK : CertifiedInverseKernel E) :
    DrazinSupercharge.anticommutator (QD CIK) (QD CIK) = (2 : ℝ) • HD CIK := by
  change QD CIK * QD CIK + QD CIK * QD CIK = (2 : ℝ) • (QD CIK * QD CIK)
  simpa [two_smul]

/--
`{odd, odd}` closure witness in split form:
`{Q_D,Q_D}` lands in `even ⊕ center` through the canonical split
`H_D = H_kin + Z_D`.
-/
@[rep_depth transport]
theorem anticommutator_QD_QD_eq_two_smul_kinetic_plus_central
    (CIK : CertifiedInverseKernel E) :
    DrazinSupercharge.anticommutator (QD CIK) (QD CIK)
      = (2 : ℝ) •
          (DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart (CIK := CIK) + ZD CIK) := by
  have hSplit :
      HD CIK
        = DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart (CIK := CIK) + ZD CIK := by
    simpa [HD, ZD] using
      DrazinSupercharge.CertifiedInverseKernel.superHamiltonian_eq_canonicalKinetic_plus_canonicalDefectCentral
        (CIK := CIK)
  calc
    DrazinSupercharge.anticommutator (QD CIK) (QD CIK) = (2 : ℝ) • HD CIK :=
      anticommutator_QD_QD_eq_two_smul_HD (E := E) CIK
    _ = (2 : ℝ) •
          (DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart (CIK := CIK) + ZD CIK) := by
          rw [hSplit]

/-- Central channel witness: `Z_D` is central on the full Drazin lane. -/
@[rep_depth transport]
theorem ZD_isDrazinLaneCentral (CIK : CertifiedInverseKernel E) :
    DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentral CIK (ZD CIK) := by
  simpa [ZD] using
    DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral_isDrazinLaneCentral (CIK := CIK)

/--
`{odd, odd}` closure is conjugation-invariant under any KKT closure symmetry.
-/
@[rep_depth transport]
theorem anticommutator_QD_QD_conjugation_invariant_of_preserves
    (CIK : CertifiedInverseKernel E) (U : EndHˣ)
    (hU : PreservesKKTGenerators (E := E) CIK U) :
    conjugateUnit (E := E) U (DrazinSupercharge.anticommutator (QD CIK) (QD CIK))
      = DrazinSupercharge.anticommutator (QD CIK) (QD CIK) := by
  rcases hU with ⟨_, _, hQ, _, _⟩
  calc
    conjugateUnit (E := E) U (DrazinSupercharge.anticommutator (QD CIK) (QD CIK))
        = DrazinSupercharge.anticommutator (conjugateUnit (E := E) U (QD CIK))
            (conjugateUnit (E := E) U (QD CIK)) := by
              simpa using conjugateUnit_anticommutator (E := E) U (QD CIK) (QD CIK)
    _ = DrazinSupercharge.anticommutator (QD CIK) (QD CIK) := by simpa [hQ]

end Core

end InfoGeometry.Canonical.KKTClosure
