import InfoGeometry.Quantum.Fock
import InfoGeometry.Canonical.RicciMongeAmpere

/-!
# Research.BogoliubovFockSuper

Bogoliubov/Fock superalgebra lift over the doubled state space:

- Bogoliubov-mixed creation/annihilation operators
- `ℤ₂` super-bracket on Fock endomorphisms
- grand-canonical generator with chemical potential
- bridge from transported Einstein residual to Fock deformation scale
-/

namespace InfoGeometry.Canonical.BogoliubovFockSuper

open InfoGeometry.Quantum
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Krein

section FockSuper

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Endomorphisms of the doubled/Fock state space. -/
abbrev FockEnd (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/-- Canonical naming alias for Fock endomorphisms. -/
abbrev FockEndomorphism (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  FockEnd E

/-- Real Bogoliubov mixing parameters with split normalization. -/
structure BogoliubovParams where
  u : ℝ
  v : ℝ
  normalization : u ^ 2 - v ^ 2 = 1

/-- Canonical naming alias for Bogoliubov mixing parameters. -/
abbrev BogoliubovMixingParams := BogoliubovParams

/--
Bogoliubov annihilation operator:
`a_B = u a + v a†`.
-/
noncomputable def bogoliubovAnnihilation
    (B : BogoliubovParams) : FockEnd E :=
  B.u • annihilationOp (E := E) + B.v • creationOp (E := E)

/--
Bogoliubov creation operator:
`a†_B = u a† + v a`.
-/
noncomputable def bogoliubovCreation
    (B : BogoliubovParams) : FockEnd E :=
  B.u • creationOp (E := E) + B.v • annihilationOp (E := E)

/-- Number operator induced by Bogoliubov ladder modes. -/
noncomputable def numberOperator
    (B : BogoliubovParams) : FockEnd E :=
  (bogoliubovCreation (E := E) B).comp (bogoliubovAnnihilation (E := E) B)

/-- Canonical naming alias for the Bogoliubov number operator. -/
noncomputable abbrev bogoliubovNumberOperator
    (B : BogoliubovMixingParams) : FockEndomorphism E :=
  numberOperator (E := E) B

/-- Grand-canonical generator `H - μ N_B`. -/
noncomputable def grandCanonicalGenerator
    (B : BogoliubovParams) (H : FockEnd E) (μ : ℝ) : FockEnd E :=
  H - μ • numberOperator (E := E) B

/-- Canonical naming alias for the grand-canonical Fock generator. -/
noncomputable abbrev grandCanonicalFockGenerator
    (B : BogoliubovMixingParams) (H : FockEndomorphism E) (μ : ℝ) :
    FockEndomorphism E :=
  grandCanonicalGenerator (E := E) B H μ

/-- One Euler step of grand-canonical Fock evolution. -/
noncomputable def grandCanonicalEulerStep
    (η : ℝ) (B : BogoliubovParams) (H : FockEnd E) (μ : ℝ)
    (ψ : DoubledSpace E) : DoubledSpace E :=
  ψ + η • grandCanonicalGenerator (E := E) B H μ ψ

/-- Canonical naming alias for one Euler step of grand-canonical Fock evolution. -/
noncomputable abbrev grandCanonicalFockEulerStep
    (η : ℝ) (B : BogoliubovMixingParams) (H : FockEndomorphism E) (μ : ℝ)
    (ψ : DoubledSpace E) : DoubledSpace E :=
  grandCanonicalEulerStep (E := E) η B H μ ψ

/-- Theorem `bogoliubovAnnihilation_kills_vacuumVector`. -/
theorem bogoliubovAnnihilation_kills_vacuumVector
    (B : BogoliubovParams) :
    bogoliubovAnnihilation (E := E) B 0 = 0 := by
  simp [bogoliubovAnnihilation]

/-- Theorem `bogoliubovCreation_kills_vacuumVector`. -/
theorem bogoliubovCreation_kills_vacuumVector
    (B : BogoliubovParams) :
    bogoliubovCreation (E := E) B 0 = 0 := by
  simp [bogoliubovCreation]

/-- `ℤ₂` grading parity labels for superalgebra brackets. -/
inductive SuperParity where
  | even
  | odd
deriving DecidableEq, Repr

/-- Super sign `(-1)^{|p||q|}` specialized to `{even, odd}`. -/
def paritySign : SuperParity → SuperParity → ℝ
  | .odd, .odd => -1
  | _, _ => 1

/-- Graded super-commutator on Fock endomorphisms. -/
noncomputable def superBracket
    (p q : SuperParity) (A B : FockEnd E) : FockEnd E :=
  A.comp B - paritySign p q • (B.comp A)

/-- Canonical naming alias for graded bracket on Fock endomorphisms. -/
noncomputable abbrev fockSuperBracket
    (p q : SuperParity) (A B : FockEndomorphism E) : FockEndomorphism E :=
  superBracket (E := E) p q A B

/-- Lemma `superBracket_add_left`. -/
lemma superBracket_add_left
    (p q : SuperParity) (A₁ A₂ B : FockEnd E) :
    superBracket (E := E) p q (A₁ + A₂) B
      = superBracket (E := E) p q A₁ B + superBracket (E := E) p q A₂ B := by
  unfold superBracket
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add]

/-- Lemma `superBracket_add_right`. -/
lemma superBracket_add_right
    (p q : SuperParity) (A B₁ B₂ : FockEnd E) :
    superBracket (E := E) p q A (B₁ + B₂)
      = superBracket (E := E) p q A B₁ + superBracket (E := E) p q A B₂ := by
  unfold superBracket
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add]

/-- Lemma `superBracket_smul_left`. -/
lemma superBracket_smul_left
    (p q : SuperParity) (r : ℝ) (A B : FockEnd E) :
    superBracket (E := E) p q (r • A) B
      = r • superBracket (E := E) p q A B := by
  unfold superBracket
  simp [sub_eq_add_neg, smul_smul, mul_comm]

/-- Lemma `superBracket_smul_right`. -/
lemma superBracket_smul_right
    (p q : SuperParity) (r : ℝ) (A B : FockEnd E) :
    superBracket (E := E) p q A (r • B)
      = r • superBracket (E := E) p q A B := by
  unfold superBracket
  simp [sub_eq_add_neg, smul_smul, mul_comm]

@[simp] lemma superBracket_even_left
    (q : SuperParity) (A B : FockEnd E) :
    superBracket (E := E) SuperParity.even q A B
      = A.comp B - B.comp A := by
  simp [superBracket, paritySign]

@[simp] lemma superBracket_odd_odd
    (A B : FockEnd E) :
    superBracket (E := E) SuperParity.odd SuperParity.odd A B
      = A.comp B + B.comp A := by
  apply ContinuousLinearMap.ext
  intro x
  rcases x with ⟨x₁, x₂⟩
  simp [superBracket, paritySign]

/-- Even-even super bracket (commutator channel). -/
noncomputable abbrev commutator (A B : FockEnd E) : FockEnd E :=
  superBracket (E := E) SuperParity.even SuperParity.even A B

/-- Odd-odd super bracket (anticommutator channel). -/
noncomputable abbrev anticommutator (A B : FockEnd E) : FockEnd E :=
  superBracket (E := E) SuperParity.odd SuperParity.odd A B

/-- Canonical naming alias for even-even channel on Fock endomorphisms. -/
noncomputable abbrev fockCommutator (A B : FockEndomorphism E) : FockEndomorphism E :=
  commutator (E := E) A B

/-- Canonical naming alias for odd-odd channel on Fock endomorphisms. -/
noncomputable abbrev fockAnticommutator (A B : FockEndomorphism E) : FockEndomorphism E :=
  anticommutator (E := E) A B

/--
Exact odd-odd self bracket for the annihilation projector:
`{a, a} = 2a` in the doubled-projector model.
-/
theorem anticommutator_annihilation_self :
    anticommutator (E := E) (annihilationOp (E := E)) (annihilationOp (E := E))
      = (2 : ℝ) • annihilationOp (E := E) := by
  unfold anticommutator
  rw [superBracket_odd_odd]
  calc
    (annihilationOp (E := E)).comp (annihilationOp (E := E))
        + (annihilationOp (E := E)).comp (annihilationOp (E := E))
      = annihilationOp (E := E) + annihilationOp (E := E) := by
          simp [annihilation_eq_minus_projector, gradeMinusProj_idempotent]
    _ = (2 : ℝ) • annihilationOp (E := E) := by
          ext w
          simp [two_smul]

/--
Exact odd-odd self bracket for the creation projector:
`{a†, a†} = 2a†` in the doubled-projector model.
-/
theorem anticommutator_creation_self :
    anticommutator (E := E) (creationOp (E := E)) (creationOp (E := E))
      = (2 : ℝ) • creationOp (E := E) := by
  unfold anticommutator
  rw [superBracket_odd_odd]
  calc
    (creationOp (E := E)).comp (creationOp (E := E))
        + (creationOp (E := E)).comp (creationOp (E := E))
      = creationOp (E := E) + creationOp (E := E) := by
          simp [creation_eq_plus_projector, gradePlusProj_idempotent]
    _ = (2 : ℝ) • creationOp (E := E) := by
          ext w
          simp [two_smul]

/--
Exact mixed odd-odd bracket for grade projectors:
`{a, a†} = 0`.
-/
theorem anticommutator_annihilation_creation :
    anticommutator (E := E) (annihilationOp (E := E)) (creationOp (E := E)) = 0 := by
  unfold anticommutator
  rw [superBracket_odd_odd]
  simp [annihilation_eq_minus_projector, creation_eq_plus_projector,
    gradeMinusProj_comp_gradePlusProj, gradePlusProj_comp_gradeMinusProj]

/--
Exact even-even self bracket for the annihilation projector:
`[a, a] = 0`.
-/
theorem commutator_annihilation_self :
    commutator (E := E) (annihilationOp (E := E)) (annihilationOp (E := E)) = 0 := by
  unfold commutator
  rw [superBracket_even_left]
  simp

/--
Exact even-even self bracket for the creation projector:
`[a†, a†] = 0`.
-/
theorem commutator_creation_self :
    commutator (E := E) (creationOp (E := E)) (creationOp (E := E)) = 0 := by
  unfold commutator
  rw [superBracket_even_left]
  simp

/--
Exact mixed even-even bracket for grade projectors:
`[a, a†] = 0`.
-/
theorem commutator_annihilation_creation :
    commutator (E := E) (annihilationOp (E := E)) (creationOp (E := E)) = 0 := by
  unfold commutator
  rw [superBracket_even_left]
  simp [annihilation_eq_minus_projector, creation_eq_plus_projector,
    gradeMinusProj_comp_gradePlusProj, gradePlusProj_comp_gradeMinusProj]

/-- Lemma `anticommutator_symm`. -/
lemma anticommutator_symm (A B : FockEnd E) :
    anticommutator (E := E) A B = anticommutator (E := E) B A := by
  simp [anticommutator, superBracket_odd_odd, add_comm]

/-- Lemma `fockAnticommutator_symm`. -/
lemma fockAnticommutator_symm (A B : FockEndomorphism E) :
    fockAnticommutator (E := E) A B = fockAnticommutator (E := E) B A :=
  anticommutator_symm (E := E) A B

/-- Lemma `commutator_swap`. -/
lemma commutator_swap (A B : FockEnd E) :
    commutator (E := E) A B = - commutator (E := E) B A := by
  unfold commutator
  simp [superBracket_even_left, sub_eq_add_neg]

/-- Lemma `fockCommutator_swap`. -/
lemma fockCommutator_swap (A B : FockEndomorphism E) :
    fockCommutator (E := E) A B = - fockCommutator (E := E) B A :=
  commutator_swap (E := E) A B

/--
Bogoliubov covariance (mode expansion form) for the graded super bracket.
This is the core transport law before imposing CAR/CCR closure.
-/
theorem superBracket_bogoliubov_covariance
    (p q : SuperParity) (B : BogoliubovParams) :
    superBracket (E := E) p q
        (bogoliubovAnnihilation (E := E) B)
        (bogoliubovCreation (E := E) B)
      =
      (superBracket (E := E) p q (B.u • annihilationOp (E := E)) (B.u • creationOp (E := E))
        + superBracket (E := E) p q (B.u • annihilationOp (E := E)) (B.v • annihilationOp (E := E)))
      + (superBracket (E := E) p q (B.v • creationOp (E := E)) (B.u • creationOp (E := E))
        + superBracket (E := E) p q (B.v • creationOp (E := E)) (B.v • annihilationOp (E := E))) := by
  simp [bogoliubovAnnihilation, bogoliubovCreation,
    superBracket_add_left, superBracket_add_right]
  ac_rfl

/--
Constructive odd-odd Bogoliubov bracket in the doubled-projector model:
`{a_B, a†_B} = 2uv · Id`.
-/
theorem anticommutator_bogoliubov_projector_model
    (B : BogoliubovParams) :
    anticommutator (E := E)
        (bogoliubovAnnihilation (E := E) B)
        (bogoliubovCreation (E := E) B)
      =
      (B.u * (B.v * 2) : ℝ) • ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  have hCov :=
    superBracket_bogoliubov_covariance (E := E) (p := SuperParity.odd) (q := SuperParity.odd) B
  have hmm :
      (annihilationOp (E := E)).comp (annihilationOp (E := E)) = annihilationOp (E := E) := by
    simp [annihilation_eq_minus_projector, gradeMinusProj_idempotent]
  have hpp :
      (creationOp (E := E)).comp (creationOp (E := E)) = creationOp (E := E) := by
    simp [creation_eq_plus_projector, gradePlusProj_idempotent]
  have hmp :
      (annihilationOp (E := E)).comp (creationOp (E := E)) = 0 := by
    simp [annihilation_eq_minus_projector, creation_eq_plus_projector, gradeMinusProj_comp_gradePlusProj]
  have hpm :
      (creationOp (E := E)).comp (annihilationOp (E := E)) = 0 := by
    simp [annihilation_eq_minus_projector, creation_eq_plus_projector, gradePlusProj_comp_gradeMinusProj]
  have hExpand :
      anticommutator (E := E)
          (bogoliubovAnnihilation (E := E) B)
          (bogoliubovCreation (E := E) B)
        =
        (B.u * B.u) • (0 : FockEnd E) +
          ((B.u * B.v) • annihilationOp (E := E) + (B.u * B.v) • annihilationOp (E := E)) +
          ((B.u * B.v) • creationOp (E := E) + (B.u * B.v) • creationOp (E := E) +
            (B.v * B.v) • (0 : FockEnd E)) := by
    have huv : B.v * B.u = B.u * B.v := by ring
    unfold anticommutator
    rw [hCov]
    simp [superBracket_smul_left, superBracket_smul_right,
      superBracket_odd_odd, hmm, hpp, hmp, hpm, smul_smul, mul_comm]
  rw [hExpand]
  calc
    (B.u * B.u) • (0 : FockEnd E) +
      ((B.u * B.v) • annihilationOp (E := E) + (B.u * B.v) • annihilationOp (E := E)) +
      ((B.u * B.v) • creationOp (E := E) + (B.u * B.v) • creationOp (E := E) +
        (B.v * B.v) • (0 : FockEnd E))
        = ((B.u * B.v + B.u * B.v) : ℝ) •
          (annihilationOp (E := E) + creationOp (E := E)) := by
            have hzeroU : (B.u * B.u) • (0 : FockEnd E) = 0 := by
              ext w
              simp
            have hzeroV : (B.v * B.v) • (0 : FockEnd E) = 0 := by
              ext w
              simp
            rw [hzeroU, hzeroV]
            simp [add_smul, smul_add, add_assoc, add_comm]
    _ = ((B.u * B.v + B.u * B.v) : ℝ) • ContinuousLinearMap.id ℝ (DoubledSpace E) := by
            have hsum :
                annihilationOp (E := E) + creationOp (E := E)
                  = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
              simpa [add_comm] using creation_add_annihilation (E := E)
            rw [hsum]
    _ = (B.u * (B.v * 2) : ℝ) • ContinuousLinearMap.id ℝ (DoubledSpace E) := by
            have hcoef : (B.u * B.v + B.u * B.v : ℝ) = B.u * (B.v * 2) := by ring
            rw [hcoef]

/--
Constructive even-even Bogoliubov bracket in the doubled-projector model:
`[a_B, a†_B] = 0`.
-/
theorem commutator_bogoliubov_projector_model
    (B : BogoliubovParams) :
    commutator (E := E)
        (bogoliubovAnnihilation (E := E) B)
        (bogoliubovCreation (E := E) B)
      = 0 := by
  have hCov :=
    superBracket_bogoliubov_covariance (E := E) (p := SuperParity.even) (q := SuperParity.even) B
  have hmp :
      (annihilationOp (E := E)).comp (creationOp (E := E)) = 0 := by
    simp [annihilation_eq_minus_projector, creation_eq_plus_projector, gradeMinusProj_comp_gradePlusProj]
  have hpm :
      (creationOp (E := E)).comp (annihilationOp (E := E)) = 0 := by
    simp [annihilation_eq_minus_projector, creation_eq_plus_projector, gradePlusProj_comp_gradeMinusProj]
  unfold commutator
  rw [hCov]
  simp [superBracket_smul_left, superBracket_smul_right, superBracket_even_left,
    hmp, hpm]

end FockSuper

section EinsteinBridge

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Einstein-transported residual viewed as a chemical-potential shift. -/
noncomputable def inducedChemicalPotential
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V) : ℝ :=
  transportedEinsteinResidual (R := R) (K := K) (x := x)
    (scalar := scalar) (Λ := Λ) V Γ

/-- Canonical naming alias for Einstein-induced chemical potential. -/
noncomputable abbrev einsteinInducedChemicalPotential
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V) : ℝ :=
  inducedChemicalPotential R K x scalar Λ V Γ

/-- Lemma `inducedChemicalPotential_eq_zero_of_vacuumTransported`. -/
lemma inducedChemicalPotential_eq_zero_of_vacuumTransported
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ) :
    inducedChemicalPotential R K x scalar Λ V Γ = 0 :=
  hVacSplit

/-- Einstein-residual deformation as a scalar multiple of identity on Fock space. -/
noncomputable def einsteinFockDeformation
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V) :
    FockEnd E :=
  inducedChemicalPotential R K x scalar Λ V Γ • ContinuousLinearMap.id ℝ (DoubledSpace E)

/-- Canonical naming alias for Einstein-induced Fock deformation operator. -/
noncomputable abbrev einsteinFockDeformationOperator
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V) :
    FockEndomorphism E :=
  einsteinFockDeformation R K x scalar Λ V Γ

/-- Lemma `einsteinFockDeformation_eq_zero_of_vacuumTransported`. -/
lemma einsteinFockDeformation_eq_zero_of_vacuumTransported
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ) :
    einsteinFockDeformation R K x scalar Λ V Γ = 0 := by
  have hμ : inducedChemicalPotential R K x scalar Λ V Γ = 0 := hVacSplit
  have hdef : einsteinFockDeformation R K x scalar Λ V Γ = inducedChemicalPotential R K x scalar Λ V Γ • ContinuousLinearMap.id ℝ (DoubledSpace E) := rfl
  rw [hdef, hμ]
  ext v; simp

/-- Lemma `grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported`. -/
lemma grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported
    (B : BogoliubovParams) (H : FockEnd E)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ) :
    grandCanonicalGenerator (E := E) B H
        (inducedChemicalPotential R K x scalar Λ V Γ) = H := by
  have hμ : inducedChemicalPotential R K x scalar Λ V Γ = 0 := hVacSplit
  have hgcg : grandCanonicalGenerator (E := E) B H (inducedChemicalPotential R K x scalar Λ V Γ) = H - inducedChemicalPotential R K x scalar Λ V Γ • numberOperator B := rfl
  rw [hgcg, hμ]
  ext v; simp

/-- Lemma `grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported`. -/
lemma grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
    (B : BogoliubovMixingParams) (H : FockEndomorphism E)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ) :
    grandCanonicalFockGenerator (E := E) B H
        (einsteinInducedChemicalPotential R K x scalar Λ V Γ) = H := by
  simpa [grandCanonicalFockGenerator, einsteinInducedChemicalPotential] using
    grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported
      (E := E) (B := B) (H := H) (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ) hVacSplit

end EinsteinBridge

attribute [deprecated FockEndomorphism (since := "2026-02-26")] FockEnd
attribute [deprecated BogoliubovMixingParams (since := "2026-02-26")] BogoliubovParams
attribute [deprecated bogoliubovNumberOperator (since := "2026-02-26")] numberOperator
attribute [deprecated grandCanonicalFockGenerator (since := "2026-02-26")] grandCanonicalGenerator
attribute [deprecated grandCanonicalFockEulerStep (since := "2026-02-26")] grandCanonicalEulerStep
attribute [deprecated fockSuperBracket (since := "2026-02-26")] superBracket
attribute [deprecated fockCommutator (since := "2026-02-26")] commutator
attribute [deprecated fockAnticommutator (since := "2026-02-26")] anticommutator
attribute [deprecated einsteinInducedChemicalPotential (since := "2026-02-26")]
  inducedChemicalPotential
attribute [deprecated einsteinFockDeformationOperator (since := "2026-02-26")]
  einsteinFockDeformation
attribute [deprecated grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported
  (since := "2026-02-26")]
  grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported

end InfoGeometry.Canonical.BogoliubovFockSuper
