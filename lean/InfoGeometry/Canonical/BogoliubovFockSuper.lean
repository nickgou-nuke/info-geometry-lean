import InfoGeometry.Quantum.Fock
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Canonical.RicciMongeAmpere

/-!
# Research.BogoliubovFockSuper

Bogoliubov/Fock superalgebra lift over the doubled state space:

- projector-super mixing on doubled-space creation/annihilation projectors
- `ℤ₂` super-bracket on Fock endomorphisms
- grand-canonical generator with chemical potential
- scalar bridge from transported Einstein residual to a Fock deformation scale

The file is intentionally split into two theorem surfaces:

- `FockSuper`: the projector-super branch, where doubled-space projectors are
  treated as odd generators but are not claimed to satisfy CAR.
- `CliffordCAR`: the genuine CAR branch, imported from the split-`Cl(1,1)`
  Clifford null-mode construction.
-/

namespace InfoGeometry.Canonical.BogoliubovFockSuper

open InfoGeometry.Quantum
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Krein

/-! ## Projector-Super Branch -/

section FockSuper

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Endomorphisms of the doubled/Fock state space. -/
abbrev FockEnd (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/-- Canonical naming alias for Fock endomorphisms. -/
abbrev FockEndomorphism (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  FockEnd E

/--
Neutral hyperbolic mixing parameters for the projector-super branch.

The constraint `u^2 - v^2 = 1` matches the hyperbolic parameterization used by
`ofAngle`, but the projector-super theorems in this section do not, by
themselves, imply fermionic CAR preservation.
-/
structure HyperbolicMixingParams where
  u : ℝ
  v : ℝ
  normalization : u ^ 2 - v ^ 2 = 1

namespace HyperbolicMixingParams

/-- Hyperbolic-angle constructor `u = cosh θ`, `v = sinh θ`. -/
noncomputable def ofAngle (θ : ℝ) : HyperbolicMixingParams where
  u := Real.cosh θ
  v := Real.sinh θ
  normalization := by
    simpa [pow_two] using Real.cosh_sq_sub_sinh_sq θ

end HyperbolicMixingParams

/-- Backward-compatible alias for the older projector-branch parameter name. -/
abbrev BogoliubovParams := HyperbolicMixingParams

/-- Backward-compatible alias for the older mixing-parameter surface. -/
abbrev BogoliubovMixingParams := HyperbolicMixingParams

/--
Bogoliubov annihilation operator:
`a_B = u a + v a†`.
-/
noncomputable def bogoliubovAnnihilation
    (B : HyperbolicMixingParams) : FockEnd E :=
  B.u • annihilationOp (E := E) + B.v • creationOp (E := E)

/--
Bogoliubov creation operator:
`a†_B = u a† + v a`.
-/
noncomputable def bogoliubovCreation
    (B : HyperbolicMixingParams) : FockEnd E :=
  B.u • creationOp (E := E) + B.v • annihilationOp (E := E)

/-- Number operator induced by Bogoliubov ladder modes. -/
noncomputable def numberOperator
    (B : HyperbolicMixingParams) : FockEnd E :=
  (bogoliubovCreation (E := E) B).comp (bogoliubovAnnihilation (E := E) B)

/-- Canonical naming alias for the Bogoliubov number operator. -/
noncomputable abbrev bogoliubovNumberOperator
    (B : BogoliubovMixingParams) : FockEndomorphism E :=
  numberOperator (E := E) B

/-- Grand-canonical generator `H - μ N_B`. -/
noncomputable def grandCanonicalGenerator
    (B : HyperbolicMixingParams) (H : FockEnd E) (μ : ℝ) : FockEnd E :=
  H - μ • numberOperator (E := E) B

/-- Canonical naming alias for the grand-canonical Fock generator. -/
noncomputable abbrev grandCanonicalFockGenerator
    (B : BogoliubovMixingParams) (H : FockEndomorphism E) (μ : ℝ) :
    FockEndomorphism E :=
  grandCanonicalGenerator (E := E) B H μ

/-- One Euler step of grand-canonical Fock evolution. -/
noncomputable def grandCanonicalEulerStep
    (η : ℝ) (B : HyperbolicMixingParams) (H : FockEnd E) (μ : ℝ)
    (ψ : DoubledSpace E) : DoubledSpace E :=
  ψ + η • grandCanonicalGenerator (E := E) B H μ ψ

/-- Canonical naming alias for one Euler step of grand-canonical Fock evolution. -/
noncomputable abbrev grandCanonicalFockEulerStep
    (η : ℝ) (B : BogoliubovMixingParams) (H : FockEndomorphism E) (μ : ℝ)
    (ψ : DoubledSpace E) : DoubledSpace E :=
  grandCanonicalEulerStep (E := E) η B H μ ψ

/-- Every Bogoliubov-mixed annihilation operator sends `0` to `0`. -/
theorem bogoliubovAnnihilation_map_zero
    (B : HyperbolicMixingParams) :
    bogoliubovAnnihilation (E := E) B 0 = 0 := by
  simp [bogoliubovAnnihilation]

/-- Every Bogoliubov-mixed creation operator sends `0` to `0`. -/
theorem bogoliubovCreation_map_zero
    (B : HyperbolicMixingParams) :
    bogoliubovCreation (E := E) B 0 = 0 := by
  simp [bogoliubovCreation]

@[deprecated bogoliubovAnnihilation_map_zero (since := "2026-03-21")]
theorem bogoliubovAnnihilation_kills_vacuumVector
    (B : HyperbolicMixingParams) :
    bogoliubovAnnihilation (E := E) B 0 = 0 :=
  bogoliubovAnnihilation_map_zero (E := E) B

@[deprecated bogoliubovCreation_map_zero (since := "2026-03-21")]
theorem bogoliubovCreation_kills_vacuumVector
    (B : HyperbolicMixingParams) :
    bogoliubovCreation (E := E) B 0 = 0 :=
  bogoliubovCreation_map_zero (E := E) B

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

/--
Standard CAR package for an odd-operator pair.

This is intentionally separated from the current doubled-projector model:
for projector-derived odd generators, these identities generally fail.
-/
def IsCARPair (a adag : FockEnd E) : Prop :=
  anticommutator (E := E) a a = 0 ∧
    anticommutator (E := E) adag adag = 0 ∧
    anticommutator (E := E) a adag = ContinuousLinearMap.id ℝ (DoubledSpace E)

/--
Constructive closure package actually realized by the doubled-projector model.
-/
def IsProjectorSuperPair (a adag : FockEnd E) : Prop :=
  anticommutator (E := E) a a = (2 : ℝ) • a ∧
    anticommutator (E := E) adag adag = (2 : ℝ) • adag ∧
    anticommutator (E := E) a adag = 0 ∧
    commutator (E := E) a adag = 0

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
          apply ContinuousLinearMap.ext
          intro w
          apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [two_smul]

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
          apply ContinuousLinearMap.ext
          intro w
          apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [two_smul]

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

/--
The canonical doubled-space odd pair is a projector-super pair.
-/
theorem projectorSuperPair_base :
    IsProjectorSuperPair (E := E) (annihilationOp (E := E)) (creationOp (E := E)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact anticommutator_annihilation_self (E := E)
  · exact anticommutator_creation_self (E := E)
  · exact anticommutator_annihilation_creation (E := E)
  · exact commutator_annihilation_creation (E := E)

/--
Honesty theorem: the canonical doubled-projector odd pair is not a standard CAR
pair on nontrivial doubled space.
-/
theorem not_isCARPair_base [Nontrivial E] :
    ¬ IsCARPair (E := E) (annihilationOp (E := E)) (creationOp (E := E) ) := by
  intro hCAR
  rcases hCAR with ⟨_, _, hMixedId⟩
  have hMixedZero :
      anticommutator (E := E) (annihilationOp (E := E)) (creationOp (E := E)) = 0 :=
    anticommutator_annihilation_creation (E := E)
  have hIdZero : (ContinuousLinearMap.id ℝ (DoubledSpace E)) = 0 := by
    calc
      ContinuousLinearMap.id ℝ (DoubledSpace E)
          = anticommutator (E := E) (annihilationOp (E := E)) (creationOp (E := E)) := by
              rw [hMixedId.symm]
      _ = 0 := hMixedZero
  rcases exists_ne (0 : DoubledSpace E) with ⟨x, hx⟩
  have : x = (0 : DoubledSpace E) := by
    have hEval := DFunLike.congr_fun hIdZero x
    simpa using hEval
  exact hx this

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
    (p q : SuperParity) (B : HyperbolicMixingParams) :
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
    (B : HyperbolicMixingParams) :
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
              apply ContinuousLinearMap.ext
              intro w
              apply InfoGeometry.Krein.DoubledSpace.ext <;> simp
            have hzeroV : (B.v * B.v) • (0 : FockEnd E) = 0 := by
              apply ContinuousLinearMap.ext
              intro w
              apply InfoGeometry.Krein.DoubledSpace.ext <;> simp
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
    (B : HyperbolicMixingParams) :
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

/--
Constructive closure theorem for Bogoliubov-mixed odd generators in the
doubled-projector model.
-/
theorem bogoliubov_projector_superalgebra
    (B : HyperbolicMixingParams) :
    anticommutator (E := E)
        (bogoliubovAnnihilation (E := E) B)
        (bogoliubovCreation (E := E) B)
      = (B.u * (B.v * 2) : ℝ) • ContinuousLinearMap.id ℝ (DoubledSpace E)
    ∧
    commutator (E := E)
        (bogoliubovAnnihilation (E := E) B)
        (bogoliubovCreation (E := E) B) = 0 := by
  refine ⟨?_, ?_⟩
  · exact anticommutator_bogoliubov_projector_model (E := E) B
  · exact commutator_bogoliubov_projector_model (E := E) B

/--
For the hyperbolic-angle parameterization, the projector anomaly coefficient
collapses to `sinh (2θ)`.
-/
theorem anticommutator_ofAngle_projector_model
    (θ : ℝ) :
    anticommutator (E := E)
        (bogoliubovAnnihilation (E := E) (HyperbolicMixingParams.ofAngle θ))
        (bogoliubovCreation (E := E) (HyperbolicMixingParams.ofAngle θ))
      = (Real.sinh (2 * θ)) • ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  rw [anticommutator_bogoliubov_projector_model]
  congr 1
  calc
    (HyperbolicMixingParams.ofAngle θ).u * ((HyperbolicMixingParams.ofAngle θ).v * 2)
        = 2 * Real.sinh θ * Real.cosh θ := by
            simp [HyperbolicMixingParams.ofAngle]
            ring
    _ = Real.sinh (2 * θ) := by
          rw [Real.sinh_two_mul]

end FockSuper

/-! ## Genuine Clifford/CAR Branch -/

section CliffordCAR

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Constructive derivation of CAR from the split-Clifford real Majorana layer.

This is the canonical reformulation of the old ladder-primitive target:
CAR is proved for transported real Majorana fields, while ladder operators are
derived later from polarization choices.
-/
theorem car_realization_of_clifford
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := DoubledSpace E))
    (T : InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform (S := DoubledSpace E) M) :
    InfoGeometry.Quantum.RealMajorana.MajoranaCARWitness
      (S := DoubledSpace E)
      (fun u v => inner ℝ u v)
      (InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.transportGamma (T := T)) := by
  exact
    InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.car_realization_of_clifford
      (T := T)

/--
Any derived polarization split carries the constructive projector-super algebra.
This is the ladder-level target associated to a chosen polarization, not a CAR pair.
-/
theorem projectorSuperPair_of_polarizationSplit
    (A : InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit
      (S := DoubledSpace E)) :
    IsProjectorSuperPair (E := E) A.Pminus A.Pplus := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold anticommutator
    rw [superBracket_odd_odd]
    calc
      A.Pminus.comp A.Pminus + A.Pminus.comp A.Pminus = A.Pminus + A.Pminus := by
        rw [A.minus_idem]
      _ = (2 : ℝ) • A.Pminus := by
        apply ContinuousLinearMap.ext
        intro w
        apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [two_smul]
  · unfold anticommutator
    rw [superBracket_odd_odd]
    calc
      A.Pplus.comp A.Pplus + A.Pplus.comp A.Pplus = A.Pplus + A.Pplus := by
        rw [A.plus_idem]
      _ = (2 : ℝ) • A.Pplus := by
        apply ContinuousLinearMap.ext
        intro w
        apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [two_smul]
  · unfold anticommutator
    rw [superBracket_odd_odd]
    simp [A.cross_minus_plus, A.cross_plus_minus]
  · unfold commutator
    rw [superBracket_even_left]
    simp [A.cross_minus_plus, A.cross_plus_minus]

/--
A `K`-compatible polarization yields a ladder-level projector-super pair by
its canonical split presentation.
-/
theorem projectorSuperPair_of_ladderOfPolarization
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := DoubledSpace E))
    (P : InfoGeometry.Quantum.RealMajorana.KPolarization (S := DoubledSpace E) M) :
    IsProjectorSuperPair (E := E)
      (InfoGeometry.Quantum.RealMajorana.KPolarization.splitOfPolarization (M := M) P).Pminus
      (InfoGeometry.Quantum.RealMajorana.KPolarization.splitOfPolarization (M := M) P).Pplus := by
  exact
    projectorSuperPair_of_polarizationSplit (E := E)
      (A := InfoGeometry.Quantum.RealMajorana.KPolarization.splitOfPolarization (M := M) P)

/--
The canonical chirality polarization of a real Majorana datum induces the
projector-super pair used as the ladder-level surface in the canonical file.
-/
theorem projectorSuperPair_of_chiralityPolarization
    (M : InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum (S := DoubledSpace E)) :
    IsProjectorSuperPair (E := E)
      (InfoGeometry.Quantum.RealMajorana.KPolarization.splitOfPolarization
        (M := M) M.chiralityPolarization).Pminus
      (InfoGeometry.Quantum.RealMajorana.KPolarization.splitOfPolarization
        (M := M) M.chiralityPolarization).Pplus := by
  exact projectorSuperPair_of_ladderOfPolarization (E := E) M M.chiralityPolarization

/--
Adapter from the algebraic real-Majorana CAR witness to the continuous Fock-side
CAR pair witness on doubled space.
-/
theorem isCARPair_of_linear_CARWitness
    (a adag : FockEnd E)
    (hLinearCAR :
      InfoGeometry.Quantum.RealMajoranaCategory.CARWitness
        (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E)
        a.toLinearMap adag.toLinearMap) :
    IsCARPair (E := E) a adag := by
  rcases hLinearCAR with ⟨haa, hdd, had⟩
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    have h := LinearMap.congr_fun haa x
    simpa [anticommutator,
      InfoGeometry.Quantum.RealMajoranaCategory.anticommutator,
      ContinuousLinearMap.comp_apply] using h
  · apply ContinuousLinearMap.ext
    intro x
    have h := LinearMap.congr_fun hdd x
    simpa [anticommutator,
      InfoGeometry.Quantum.RealMajoranaCategory.anticommutator,
      ContinuousLinearMap.comp_apply] using h
  · apply ContinuousLinearMap.ext
    intro x
    have h := LinearMap.congr_fun had x
    simpa [anticommutator,
      InfoGeometry.Quantum.RealMajoranaCategory.anticommutator,
      ContinuousLinearMap.comp_apply] using h

/-- Continuous doubled-space CAR annihilation operator from the concrete `Cl(1,1)` null mode `u_-`. -/
noncomputable def cliffordConcreteAnnihilation : FockEnd E :=
  InfoGeometry.Krein.cl11RepLin (E := E)
    (InfoGeometry.Quantum.RealMajoranaCategory.cl11_uMinus (E := E))

/-- Continuous doubled-space CAR creation operator from the concrete `Cl(1,1)` null mode `u_+`. -/
noncomputable def cliffordConcreteCreation : FockEnd E :=
  InfoGeometry.Krein.cl11RepLin (E := E)
    (InfoGeometry.Quantum.RealMajoranaCategory.cl11_uPlus (E := E))

@[simp] theorem cliffordConcreteAnnihilation_toLinearMap :
    (cliffordConcreteAnnihilation (E := E)).toLinearMap
      = (InfoGeometry.Quantum.RealMajoranaCategory.ladderOfRealization
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11CanonicalPolarizedMajorana (E := E))
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11SplitCliffordDatum E)
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11_concrete_ladder_realization (E := E))).annihil := by
  apply LinearMap.ext
  intro w
  have hw : InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w) = w := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  have hhalf (z : E) : ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z) = z := by
    have hscalar : (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) = 1 := by norm_num
    simpa [hscalar]
  rw [← hw]
  calc
    (cliffordConcreteAnnihilation (E := E)).toLinearMap
        (InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w))
        = InfoGeometry.Krein.to_doubled (0 : E) ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • (WithLp.fst w)) := by
            simpa [cliffordConcreteAnnihilation,
              InfoGeometry.Quantum.RealMajoranaCategory.cl11_uMinus,
              sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (InfoGeometry.Krein.cl11RepLin_apply_to_doubled
                  (E := E) ((1 / 2 : ℝ)) ((1 / 2 : ℝ)) (WithLp.fst w) (WithLp.snd w))
    _ = InfoGeometry.Krein.to_doubled (0 : E) (WithLp.fst w) := by
          simpa [hhalf]
    _ = (InfoGeometry.Quantum.RealMajoranaCategory.ladderOfRealization
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11CanonicalPolarizedMajorana (E := E))
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11SplitCliffordDatum E)
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11_concrete_ladder_realization (E := E))).annihil
            (InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w)) := by
          symm
          simpa [InfoGeometry.Quantum.RealMajoranaCategory.ladderOfRealization,
            InfoGeometry.Quantum.RealMajoranaCategory.SplitCliffordDatum.majoranaField]
            using InfoGeometry.Quantum.RealMajoranaCategory.cl11_majoranaField_uMinus_apply_to_doubled
              (E := E) (x := WithLp.fst w) (y := WithLp.snd w)

@[simp] theorem cliffordConcreteCreation_toLinearMap :
    (cliffordConcreteCreation (E := E)).toLinearMap
      = (InfoGeometry.Quantum.RealMajoranaCategory.ladderOfRealization
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11CanonicalPolarizedMajorana (E := E))
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11SplitCliffordDatum E)
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11_concrete_ladder_realization (E := E))).create := by
  apply LinearMap.ext
  intro w
  have hw : InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w) = w := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  have hhalf (z : E) : ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z) = z := by
    have hscalar : (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) = 1 := by norm_num
    simpa [hscalar]
  rw [← hw]
  calc
    (cliffordConcreteCreation (E := E)).toLinearMap
        (InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w))
        = InfoGeometry.Krein.to_doubled ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • (WithLp.snd w)) (0 : E) := by
            simpa [cliffordConcreteCreation,
              InfoGeometry.Quantum.RealMajoranaCategory.cl11_uPlus,
              sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (InfoGeometry.Krein.cl11RepLin_apply_to_doubled
                  (E := E) ((1 / 2 : ℝ)) (-(1 / 2 : ℝ)) (WithLp.fst w) (WithLp.snd w))
    _ = InfoGeometry.Krein.to_doubled (WithLp.snd w) (0 : E) := by
          simpa [hhalf]
    _ = (InfoGeometry.Quantum.RealMajoranaCategory.ladderOfRealization
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11CanonicalPolarizedMajorana (E := E))
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11SplitCliffordDatum E)
          (InfoGeometry.Quantum.RealMajoranaCategory.cl11_concrete_ladder_realization (E := E))).create
            (InfoGeometry.Krein.to_doubled (WithLp.fst w) (WithLp.snd w)) := by
          symm
          simpa [InfoGeometry.Quantum.RealMajoranaCategory.ladderOfRealization,
            InfoGeometry.Quantum.RealMajoranaCategory.SplitCliffordDatum.majoranaField]
            using InfoGeometry.Quantum.RealMajoranaCategory.cl11_majoranaField_uPlus_apply_to_doubled
              (E := E) (x := WithLp.fst w) (y := WithLp.snd w)

@[simp] lemma cliffordConcreteAnnihilation_apply_to_doubled (x y : E) :
    cliffordConcreteAnnihilation (E := E) (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.to_doubled (0 : E) x := by
  have hhalf (z : E) : ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z) = z := by
    have hscalar : (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) = 1 := by norm_num
    simpa [hscalar]
  calc
    cliffordConcreteAnnihilation (E := E) (InfoGeometry.Krein.to_doubled x y)
        = InfoGeometry.Krein.to_doubled (0 : E) ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • x) := by
            simpa [cliffordConcreteAnnihilation,
              InfoGeometry.Quantum.RealMajoranaCategory.cl11_uMinus,
              sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (InfoGeometry.Krein.cl11RepLin_apply_to_doubled
                  (E := E) ((1 / 2 : ℝ)) ((1 / 2 : ℝ)) x y)
    _ = InfoGeometry.Krein.to_doubled (0 : E) x := by
          simpa [hhalf]

@[simp] lemma cliffordConcreteCreation_apply_to_doubled (x y : E) :
    cliffordConcreteCreation (E := E) (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.to_doubled y (0 : E) := by
  have hhalf (z : E) : ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z) = z := by
    have hscalar : (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) = 1 := by norm_num
    simpa [hscalar]
  calc
    cliffordConcreteCreation (E := E) (InfoGeometry.Krein.to_doubled x y)
        = InfoGeometry.Krein.to_doubled ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • y) (0 : E) := by
            simpa [cliffordConcreteCreation,
              InfoGeometry.Quantum.RealMajoranaCategory.cl11_uPlus,
              sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (InfoGeometry.Krein.cl11RepLin_apply_to_doubled
                  (E := E) ((1 / 2 : ℝ)) (-(1 / 2 : ℝ)) x y)
    _ = InfoGeometry.Krein.to_doubled y (0 : E) := by
          simpa [hhalf]

/--
The concrete split-`Cl(1,1)` null-mode ladder pair is a genuine CAR pair in the
continuous doubled-space/Fock interface.
-/
theorem cliffordConcreteIsCARPair :
    IsCARPair (E := E)
      (cliffordConcreteAnnihilation (E := E))
      (cliffordConcreteCreation (E := E)) := by
  apply isCARPair_of_linear_CARWitness (E := E)
  simpa using (InfoGeometry.Quantum.RealMajoranaCategory.car_realization_of_clifford_concrete (E := E))

end CliffordCAR

/-! ## Scalar Einstein/Fock Deformation Bridge -/

section EinsteinBridge

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Einstein-transported residual viewed as a scalar deformation scale, used here
as a chemical-potential proxy.
-/
noncomputable def inducedChemicalPotential
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V) : ℝ :=
  transportedEinsteinResidual (R := R) (K := K) (x := x)
    (scalar := scalar) (Λ := Λ) V Γ

/-- Canonical naming alias for the Einstein-induced scalar deformation scale. -/
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

/--
Scalar identity deformation on Fock space induced by the Einstein residual
proxy.
-/
noncomputable def einsteinFockDeformation
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V) :
    FockEnd E :=
  inducedChemicalPotential R K x scalar Λ V Γ • ContinuousLinearMap.id ℝ (DoubledSpace E)

/-- Canonical naming alias for the Einstein-induced scalar Fock deformation. -/
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
  apply ContinuousLinearMap.ext
  intro v
  apply InfoGeometry.Krein.DoubledSpace.ext <;> simp

/-- Lemma `grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported`. -/
lemma grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported
    (B : HyperbolicMixingParams) (H : FockEnd E)
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
  apply ContinuousLinearMap.ext
  intro v
  apply InfoGeometry.Krein.DoubledSpace.ext <;> simp

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
attribute [deprecated HyperbolicMixingParams (since := "2026-03-21")] BogoliubovParams
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
