import Mathlib
import InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
import InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope

/-!
# Grade-preserving representation on a common two-mode CAR--phonon carrier

This file supplies the missing common representation map for the concrete
nuclear five-grading. The finite fermionic sector is the existing two-mode
Jordan--Wigner carrier `Fin 4`; each coefficient is a native Zorn module
vector, and the outer countable coordinate is the algebraic phonon occupation.

A real `4 × 4` matrix acts on the fermionic coordinate by the ordinary module
matrix action and pointwise on every phonon level. This gives a linear and
multiplicative representation into an associative endomorphism ring, hence a
Lie representation for commutators. The five adjoint grades are preserved.
The phonon shifts commute with the represented fermionic algebra, while native
Zorn derivations act coefficientwise and commute with both sectors.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation

open Matrix
open InfoGeometry.Algebra
open InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearTwoModeFiveGradeSubmodules
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR
local notation "M4R" =>
  InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R

local notation "a1" => InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1
local notation "a2" => InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2
local notation "a1Dag" => InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag
local notation "a2Dag" => InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag
local notation "pairCreation" =>
  InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
local notation "pairAnnihilation" =>
  InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation

abbrev Coefficient := NativeZorn
abbrev FermionVector := Fin 4 → Coefficient
abbrev FermionEnd := Module.End ℝ FermionVector
abbrev Carrier := ℕ → FermionVector
abbrev Operator := Module.End ℝ Carrier

/-- A finite scalar sum acts termwise on the coefficient module. -/
theorem finite_scalar_sum_smul (a : Fin 4 → ℝ) (x : Coefficient) :
    (∑ j, a j) • x = ∑ j, a j • x := by
  simpa using (Finset.sum_smul (s := Finset.univ) (f := a) (x := x))

/-- Scalar multiplication on the coefficient module respects scalar products. -/
theorem coefficient_mul_smul (a b : ℝ) (x : Coefficient) :
    (a * b) • x = a • (b • x) := by
  exact mul_smul a b x

/-- Matrix composition acts on coefficient vectors by exchanging the two
finite summation indices. -/
theorem finite_matrix_action_comp (M N : M4R) (v : FermionVector) (i : Fin 4) :
    (∑ j, (∑ k, M i k * N k j) • v j) =
      ∑ k, M i k • (∑ j, N k j • v j) := by
  simp only [finite_scalar_sum_smul, coefficient_mul_smul,
    Finset.smul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

/-- Ordinary matrix action on a four-component module vector. -/
def fermionAction (M : M4R) : FermionEnd where
  toFun v i := ∑ j, M i j • v j
  map_add' v w := by
    funext i
    calc
      (∑ j, M i j • (v j + w j)) =
          ∑ j, (M i j • v j + M i j • w j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact ZornVectorMatrix.smul_add (M i j) (v j) (w j)
      _ = (∑ j, M i j • v j) + ∑ j, M i j • w j :=
        Finset.sum_add_distrib
  map_smul' c v := by
    funext i
    change (∑ j, M i j • (c • v j)) =
      c • (∑ j, M i j • v j)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_smul, smul_smul, mul_comm]

@[simp] theorem fermionAction_apply
    (M : M4R) (v : FermionVector) (i : Fin 4) :
    fermionAction M v i = ∑ j, M i j • v j := rfl

/-- The identity matrix acts identically. -/
theorem fermionAction_one :
    fermionAction (1 : M4R) = 1 := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;>
    simp [fermionAction, Fin.sum_univ_four,
      InfoGeometry.Algebra.ZornVectorMatrix.one_smul,
      InfoGeometry.Algebra.ZornVectorMatrix.zero_smul,
      InfoGeometry.Algebra.ZornVectorMatrix.zero_add,
      InfoGeometry.Algebra.ZornVectorMatrix.add_zero]

/-- Matrix multiplication is represented by composition. -/
theorem fermionAction_mul (M N : M4R) :
    fermionAction (M * N) = fermionAction M * fermionAction N := by
  apply LinearMap.ext
  intro v
  funext i
  change (∑ j, (∑ k, M i k * N k j) • v j) =
    ∑ k, M i k • (∑ j, N k j • v j)
  exact finite_matrix_action_comp M N v i

/-- Pointwise extension through the phonon occupation coordinate. -/
def occupationLift (T : FermionEnd) : Operator where
  toFun ψ n := T (ψ n)
  map_add' ψ φ := by
    funext n
    exact T.map_add (ψ n) (φ n)
  map_smul' c ψ := by
    funext n
    exact T.map_smul c (ψ n)

@[simp] theorem occupationLift_apply
    (T : FermionEnd) (ψ : Carrier) (n : ℕ) :
    occupationLift T ψ n = T (ψ n) := rfl

/-- Pointwise extension preserves composition. -/
theorem occupationLift_mul (S T : FermionEnd) :
    occupationLift (S * T) = occupationLift S * occupationLift T := by
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

/-- Concrete operator representation of the two-mode matrix algebra. -/
def representation (M : M4R) : Operator :=
  occupationLift (fermionAction M)

@[simp] theorem representation_apply
    (M : M4R) (ψ : Carrier) (n : ℕ) (i : Fin 4) :
    representation M ψ n i = ∑ j, M i j • ψ n j := rfl

/-- Additivity of the representation. -/
theorem representation_add (M N : M4R) :
    representation (M + N) = representation M + representation N := by
  apply LinearMap.ext
  intro ψ
  funext n i
  change (∑ j, (M i j + N i j) • ψ n j) =
    (∑ j, M i j • ψ n j) + ∑ j, N i j • ψ n j
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact ZornVectorMatrix.add_smul (M i j) (N i j) (ψ n j)

/-- Scalar compatibility. -/
theorem representation_smul (c : ℝ) (M : M4R) :
    representation (c • M) = c • representation M := by
  apply LinearMap.ext
  intro ψ
  funext n i
  change (∑ j, (c * M i j) • ψ n j) =
    c • (∑ j, M i j • ψ n j)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact coefficient_mul_smul c (M i j) (ψ n j)

/-- Zero preservation. -/
theorem representation_zero :
    representation (0 : M4R) = 0 := by
  apply LinearMap.ext
  intro ψ
  funext n i
  change (∑ j, (0 : ℝ) • ψ n j) = 0
  simp only [zero_smul, Finset.sum_const_zero]

/-- Unit preservation. -/
theorem representation_one :
    representation (1 : M4R) = 1 := by
  unfold representation
  rw [fermionAction_one]
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

/-- Multiplicativity. -/
theorem representation_mul (M N : M4R) :
    representation (M * N) = representation M * representation N := by
  unfold representation
  rw [fermionAction_mul, occupationLift_mul]

/-- The representation as a native linear map. -/
def representationLinear : M4R →ₗ[ℝ] Operator where
  toFun := representation
  map_add' := representation_add
  map_smul' := representation_smul

@[simp] theorem representationLinear_apply (M : M4R) :
    representationLinear M = representation M := rfl

/-- The matrix commutator is transported to the operator commutator. -/
theorem representation_commutator (M N : M4R) :
    representation (comm M N) =
      representation M * representation N -
        representation N * representation M := by
  change representation (M * N - N * M) = _
  calc
    representation (M * N - N * M) =
        representation (M * N) - representation (N * M) :=
      representationLinear.map_sub (M * N) (N * M)
    _ = representation M * representation N -
          representation N * representation M := by
      rw [representation_mul, representation_mul]

/-- Grade readout on represented operators. -/
def RepresentedHasGrade (k : ℤ) (T : Operator) : Prop :=
  representation gradingOperator * T -
      T * representation gradingOperator = (k : ℝ) • T

/-- The common representation preserves every adjoint grade. -/
theorem representation_preserves_grade
    {k : ℤ} {X : M4R} (hX : HasGrade k X) :
    RepresentedHasGrade k (representation X) := by
  unfold RepresentedHasGrade
  rw [← representation_commutator, hX, representation_smul]

/-- The named five lanes act on the common carrier with the same weights. -/
theorem represented_named_five_grade_packet :
    RepresentedHasGrade 2 (representation pairCreation) ∧
      RepresentedHasGrade 1 (representation a1Dag) ∧
      RepresentedHasGrade 1 (representation a2Dag) ∧
      RepresentedHasGrade (-1) (representation a1) ∧
      RepresentedHasGrade (-1) (representation a2) ∧
      RepresentedHasGrade (-2) (representation pairAnnihilation) := by
  exact ⟨representation_preserves_grade pairCreation_grade,
    representation_preserves_grade a1Dag_grade,
    representation_preserves_grade a2Dag_grade,
    representation_preserves_grade a1_grade,
    representation_preserves_grade a2_grade,
    representation_preserves_grade pairAnnihilation_grade⟩

/-- The represented first-mode CAR relation. -/
theorem represented_mode1_CAR :
    representation a1 * representation a1Dag +
      representation a1Dag * representation a1 = 1 := by
  rw [← representation_mul, ← representation_mul,
    ← representation_add, mode1_car_identity, representation_one]

/-- The represented second-mode CAR relation. -/
theorem represented_mode2_CAR :
    representation a2 * representation a2Dag +
      representation a2Dag * representation a2 = 1 := by
  rw [← representation_mul, ← representation_mul,
    ← representation_add, mode2_car_identity, representation_one]

/-- Cross-mode represented CAR. -/
theorem represented_cross_CAR :
    representation a1 * representation a2Dag +
      representation a2Dag * representation a1 = 0 := by
  rw [← representation_mul, ← representation_mul,
    ← representation_add, cross_mixed_anticommute,
    representation_zero]

/-! ## Phonon shifts on the common carrier -/

/-- Phonon creation shift on the outer occupation coordinate. -/
def phononCreation : Operator where
  toFun ψ n :=
    match n with
    | 0 => 0
    | k + 1 => ψ k
  map_add' ψ φ := by
    funext n
    cases n <;> simp [Pi.add_apply]
  map_smul' c ψ := by
    funext n
    cases n <;> simp [Pi.smul_apply]

/-- Unnormalised phonon annihilation shift. -/
def phononAnnihilation : Operator where
  toFun ψ n := ((n + 1 : ℕ) : ℝ) • ψ (n + 1)
  map_add' ψ φ := by
    funext n
    simp [smul_add]
  map_smul' c ψ := by
    funext n
    simp only [Pi.smul_apply, smul_smul]
    change (((n + 1 : ℕ) : ℝ) * c) • ψ (n + 1) =
      (c * ((n + 1 : ℕ) : ℝ)) • ψ (n + 1)
    rw [mul_comm]

/-- Exact CCR. -/
theorem phonon_CCR :
    phononAnnihilation * phononCreation -
      phononCreation * phononAnnihilation = 1 := by
  apply LinearMap.ext
  intro ψ
  funext n
  cases n with
  | zero =>
      simp [phononAnnihilation, phononCreation, Module.End.mul_apply]
  | succ n =>
      change (((n + 2 : ℕ) : ℝ) • ψ (n + 1)) -
          (((n + 1 : ℕ) : ℝ) • ψ (n + 1)) = ψ (n + 1)
      rw [← sub_smul]
      have hscalar :
          (((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = 1 := by
        norm_num
      rw [hscalar, one_smul]

/-- Every represented fermionic matrix commutes with phonon creation. -/
theorem representation_commutes_phononCreation (M : M4R) :
    representation M * phononCreation =
      phononCreation * representation M := by
  apply LinearMap.ext
  intro ψ
  funext n i
  cases n with
  | zero =>
      simp [representation, occupationLift, fermionAction,
        phononCreation, ZornVectorMatrix.smul_zero]
      exact nsmul_zero (M := Coefficient) 4
  | succ n =>
      simp [representation, occupationLift, fermionAction, phononCreation]

/-- Every represented fermionic matrix commutes with phonon annihilation. -/
theorem representation_commutes_phononAnnihilation (M : M4R) :
    representation M * phononAnnihilation =
      phononAnnihilation * representation M := by
  apply LinearMap.ext
  intro ψ
  funext n i
  simp only [Module.End.mul_apply, representation_apply,
    phononAnnihilation, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    M i j • (((n + 1 : ℕ) : ℝ) • ψ (n + 1) j) =
        (M i j * ((n + 1 : ℕ) : ℝ)) • ψ (n + 1) j :=
      (coefficient_mul_smul (M i j) ((n + 1 : ℕ) : ℝ) (ψ (n + 1) j)).symm
    _ = (((n + 1 : ℕ) : ℝ) * M i j) • ψ (n + 1) j := by rw [mul_comm]
    _ = ((n + 1 : ℕ) : ℝ) • (M i j • ψ (n + 1) j) :=
      coefficient_mul_smul _ _ _

/-! ## Native Zorn derivations on coefficients -/

/-- Coefficientwise lift of a native Zorn endomorphism. -/
def coefficientLift (D : NativeZornEnd) : Operator where
  toFun ψ n i := D (ψ n i)
  map_add' ψ φ := by
    funext n i
    exact D.map_add _ _
  map_smul' c ψ := by
    funext n i
    exact D.map_smul c _

/-- Coefficient lifts preserve composition. -/
theorem coefficientLift_mul (D E : NativeZornEnd) :
    coefficientLift (D * E) = coefficientLift D * coefficientLift E := by
  apply LinearMap.ext
  intro ψ
  funext n i
  rfl

/-- They preserve the derivation Lie bracket. -/
theorem coefficientLift_commutator (D E : NativeZornEnd) :
    coefficientLift (D * E - E * D) =
      coefficientLift D * coefficientLift E -
        coefficientLift E * coefficientLift D := by
  apply LinearMap.ext
  intro ψ
  funext n i
  rfl

/-- Coefficient endomorphisms commute with the represented fermionic algebra. -/
theorem coefficientLift_commutes_representation
    (D : NativeZornEnd) (M : M4R) :
    coefficientLift D * representation M =
      representation M * coefficientLift D := by
  apply LinearMap.ext
  intro ψ
  funext n i
  simp only [Module.End.mul_apply, coefficientLift, LinearMap.coe_mk,
    AddHom.coe_mk, representation_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact D.map_smul (M i j) (ψ n j)

/-- Coefficient endomorphisms commute with both phonon shifts. -/
theorem coefficientLift_commutes_phonons (D : NativeZornEnd) :
    coefficientLift D * phononCreation =
        phononCreation * coefficientLift D ∧
      coefficientLift D * phononAnnihilation =
        phononAnnihilation * coefficientLift D := by
  constructor
  · apply LinearMap.ext
    intro ψ
    funext n i
    cases n with
    | zero =>
        change D (0 : Coefficient) = 0
        exact D.map_zero
    | succ n =>
        simp [coefficientLift, phononCreation, Module.End.mul_apply]
  · apply LinearMap.ext
    intro ψ
    funext n i
    change D (((n + 1 : ℕ) : ℝ) • ψ (n + 1) i) =
      ((n + 1 : ℕ) : ℝ) • D (ψ (n + 1) i)
    exact D.map_smul _ _

/-- Concrete grade-preserving common representation closure. -/
theorem five_grade_common_representation_packet
    (D E : NativeZornDerLie) :
    RepresentedHasGrade 2 (representation pairCreation) ∧
      RepresentedHasGrade (-2) (representation pairAnnihilation) ∧
      representation a1 * representation a1Dag +
          representation a1Dag * representation a1 = 1 ∧
      phononAnnihilation * phononCreation -
          phononCreation * phononAnnihilation = 1 ∧
      representation pairCreation * phononCreation =
          phononCreation * representation pairCreation ∧
      coefficientLift ((⁅D, E⁆ : NativeZornDerLie) : NativeZornEnd) =
        coefficientLift (D : NativeZornEnd) *
            coefficientLift (E : NativeZornEnd) -
          coefficientLift (E : NativeZornEnd) *
            coefficientLift (D : NativeZornEnd) := by
  refine ⟨representation_preserves_grade pairCreation_grade,
    representation_preserves_grade pairAnnihilation_grade,
    represented_mode1_CAR,
    phonon_CCR,
    representation_commutes_phononCreation pairCreation,
    ?_⟩
  change coefficientLift
      ((D : NativeZornEnd) * (E : NativeZornEnd) -
        (E : NativeZornEnd) * (D : NativeZornEnd)) = _
  exact coefficientLift_commutator (D : NativeZornEnd) (E : NativeZornEnd)

end InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
