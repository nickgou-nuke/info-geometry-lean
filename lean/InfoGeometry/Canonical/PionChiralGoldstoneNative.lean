import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Core.SymmetricLieSpaces
import InfoGeometry.Physics.ChiralCausalCone
import InfoGeometry.Canonical.TomitaKreinNilpotentAtom

/-!
# Native chiral Lie/CAR closure

This is the theorem-safe replacement for the former proof-only pion packet.
It uses the existing generic symmetric-Lie owner for Cartan eigenspaces and
the existing finite chiral `σ⁺/σ⁻/σ³` owner for the concrete matrix model.

No Pin group, TKK, Casimir, Zorn, or Goldstone-physics identification is
asserted here. The proved content is the algebraic symmetric-pair closure
and the finite `sl₂`/CAR relations.
-/

noncomputable section

namespace InfoGeometry.Canonical.PionChiralGoldstoneNative

open InfoGeometry.Core.Generic
open InfoGeometry.Physics.ChiralCausalCone

section SymmetricPair

variable {R L : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [Invertible (2 : R)]

namespace SymmetricLieAlgebra

variable (S : SymmetricLieAlgebra R L)

/-- The three symmetric-pair bracket rules, packaged without a new carrier. -/
theorem symmetric_pair_bracket_closure :
    (∀ {x y : L}, x ∈ S.𝔨 → y ∈ S.𝔨 → ⁅x, y⁆ ∈ S.𝔨) ∧
    (∀ {x y : L}, x ∈ S.𝔨 → y ∈ S.𝔭 → ⁅x, y⁆ ∈ S.𝔭) ∧
    (∀ {x y : L}, x ∈ S.𝔭 → y ∈ S.𝔭 → ⁅x, y⁆ ∈ S.𝔨) := by
  exact ⟨fun hx hy => S.bracket_k_k hx hy,
    fun hx hy => S.bracket_k_p hx hy,
    fun hx hy => S.bracket_p_p hx hy⟩

/-- The two Cartan eigenspaces are complementary submodules. -/
theorem cartan_eigenspaces_complementary :
    IsCompl S.𝔨 S.𝔭 :=
  S.isCompl_𝔨_𝔭

end SymmetricLieAlgebra

end SymmetricPair

section ChiralMatrices

abbrev M2C := InfoGeometry.Physics.ChiralCausalCone.M2C

/-! These are aliases, not a second matrix realization. -/
abbrev piPlus : M2C := σPlus
abbrev piMinus : M2C := σMinus
abbrev piZero : M2C := (1 / 2 : ℂ) • σ3c

@[simp] theorem piPlus_sq : piPlus * piPlus = 0 := σPlus_sq

@[simp] theorem piMinus_sq : piMinus * piMinus = 0 := σMinus_sq

theorem piPlus_piMinus_CAR :
    piPlus * piMinus + piMinus * piPlus = (1 : M2C) := by
  simpa [piPlus, piMinus] using anti_σPlus_σMinus

theorem piPlus_piMinus_lie :
    ⁅piPlus, piMinus⁆ = (2 : ℂ) • piZero := by
  rw [LieRing.of_associative_ring_bracket]
  simpa [piPlus, piMinus, piZero] using comm_σPlus_σMinus

theorem piZero_piPlus_lie :
    ⁅piZero, piPlus⁆ = piPlus := by
  rw [piZero, piPlus]
  rw [smul_lie]
  simpa [smul_smul] using congrArg (fun X : M2C => (1 / 2 : ℂ) • X)
    comm_σ3_σPlus

theorem piZero_piMinus_lie :
    ⁅piZero, piMinus⁆ = -piMinus := by
  rw [piZero, piMinus]
  rw [smul_lie]
  simpa [smul_smul] using congrArg (fun X : M2C => (1 / 2 : ℂ) • X)
    comm_σ3_σMinus

def pionLieSubalgebra : LieSubalgebra ℂ M2C :=
  LieSubalgebra.lieSpan ℂ M2C {piPlus, piMinus, piZero}

theorem piPlus_mem_pionLieSubalgebra :
    piPlus ∈ pionLieSubalgebra := by
  apply LieSubalgebra.subset_lieSpan
  simp [pionLieSubalgebra]

theorem piMinus_mem_pionLieSubalgebra :
    piMinus ∈ pionLieSubalgebra := by
  apply LieSubalgebra.subset_lieSpan
  simp [pionLieSubalgebra]

theorem piZero_mem_pionLieSubalgebra :
    piZero ∈ pionLieSubalgebra := by
  apply LieSubalgebra.subset_lieSpan
  simp [pionLieSubalgebra]

theorem pionLieSubalgebra_closed :
    ⁅piPlus, piMinus⁆ ∈ pionLieSubalgebra ∧
    ⁅piZero, piPlus⁆ ∈ pionLieSubalgebra ∧
    ⁅piZero, piMinus⁆ ∈ pionLieSubalgebra := by
  exact ⟨LieSubalgebra.lie_mem _ piPlus_mem_pionLieSubalgebra
      piMinus_mem_pionLieSubalgebra,
    LieSubalgebra.lie_mem _ piZero_mem_pionLieSubalgebra
      piPlus_mem_pionLieSubalgebra,
    LieSubalgebra.lie_mem _ piZero_mem_pionLieSubalgebra
      piMinus_mem_pionLieSubalgebra⟩

theorem piZero_from_piPlus_piMinus :
    piZero = (1 / 2 : ℂ) • ⁅piPlus, piMinus⁆ := by
  change (1 / 2 : ℂ) • σ3c =
    (1 / 2 : ℂ) • ⁅σPlus, σMinus⁆
  rw [LieRing.of_associative_ring_bracket, comm_σPlus_σMinus]

/-! ## Readback to the existing real `Cl(1,1)` atom -/

theorem piPlus_from_real_CPTAtom :
    piPlus = (1 / 2 : ℂ) •
      (complexifyCl11 InfoGeometry.Physics.CPTAtom.eps -
        complexifyCl11 InfoGeometry.Physics.CPTAtom.J) :=
  σPlus_from_cl11

theorem piMinus_from_real_CPTAtom :
    piMinus = (1 / 2 : ℂ) •
      (complexifyCl11 InfoGeometry.Physics.CPTAtom.eps +
        complexifyCl11 InfoGeometry.Physics.CPTAtom.J) :=
  σMinus_from_cl11

theorem piZero_from_real_CPTAtom :
    piZero = (1 / 2 : ℂ) •
      complexifyCl11 InfoGeometry.Physics.CPTAtom.CPT := by
  rw [piZero, complexifyCl11_CPT]

theorem real_CPT_chiral_basis :
    piPlus = (1 / 2 : ℂ) •
        (complexifyCl11 InfoGeometry.Physics.CPTAtom.eps -
          complexifyCl11 InfoGeometry.Physics.CPTAtom.J) ∧
    piMinus = (1 / 2 : ℂ) •
        (complexifyCl11 InfoGeometry.Physics.CPTAtom.eps +
          complexifyCl11 InfoGeometry.Physics.CPTAtom.J) ∧
    piZero = (1 / 2 : ℂ) •
      complexifyCl11 InfoGeometry.Physics.CPTAtom.CPT := by
  exact ⟨piPlus_from_real_CPTAtom, piMinus_from_real_CPTAtom,
    piZero_from_real_CPTAtom⟩

theorem native_chiral_closure :
    piPlus * piPlus = 0 ∧
    piMinus * piMinus = 0 ∧
    piPlus * piMinus + piMinus * piPlus = (1 : M2C) ∧
    ⁅piPlus, piMinus⁆ = (2 : ℂ) • piZero ∧
    ⁅piZero, piPlus⁆ = piPlus ∧
    ⁅piZero, piMinus⁆ = -piMinus := by
  exact ⟨piPlus_sq, piMinus_sq, piPlus_piMinus_CAR,
    piPlus_piMinus_lie, piZero_piPlus_lie, piZero_piMinus_lie⟩

end ChiralMatrices

/-! ## Real Hestenes--Krein owner

The matrix block above is retained only as a finite readout.  The primary
real nilpotent pair is the already-owned doubled CAR pair; no new carrier is
introduced here.
-/

section RealHestenesKrein

open InfoGeometry.Krein
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev hestenesPionPlus : DoubledSpace E →L[ℝ] DoubledSpace E :=
  concreteCARCreation (E := E)

abbrev hestenesPionMinus : DoubledSpace E →L[ℝ] DoubledSpace E :=
  concreteCARAnnihilation (E := E)

abbrev hestenesPionZero : DoubledSpace E →L[ℝ] DoubledSpace E :=
  (1 / 2 : ℝ) • spectral_epsilon (E := E)

/-! The formula presentation in `DoubledSpace` is the same operator as the
repository-owned concrete CAR presentation. -/

theorem hestenesPionPlus_eq_doubledSpace_formula :
    hestenesPionPlus (E := E) =
      InfoGeometry.Krein.hestenesPionPlus (E := E) := by
  exact (InfoGeometry.Canonical.TomitaKreinNilpotentAtom
    .hestenesPionPlus_eq_concreteCARCreation (E := E)).symm

theorem hestenesPionMinus_eq_doubledSpace_formula :
    hestenesPionMinus (E := E) =
      InfoGeometry.Krein.hestenesPionMinus (E := E) := by
  exact (InfoGeometry.Canonical.TomitaKreinNilpotentAtom
    .hestenesPionMinus_eq_concreteCARAnnihilation (E := E)).symm

@[simp] theorem hestenesPionPlus_sq :
    (hestenesPionPlus (E := E)).comp
        (hestenesPionPlus (E := E)) = 0 := by
  exact concrete_creation_square_zero (E := E)

@[simp] theorem hestenesPionMinus_sq :
    (hestenesPionMinus (E := E)).comp
        (hestenesPionMinus (E := E)) = 0 := by
  exact concrete_annihilation_square_zero (E := E)

theorem hestenesPion_plus_minus_car :
    CARBracket (E := E)
        (hestenesPionMinus (E := E))
        (hestenesPionPlus (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  exact concrete_car_minus_plus (E := E)

theorem hestenesPion_plus_minus_lie :
    CCRBracket (E := E)
        (hestenesPionPlus (E := E))
        (hestenesPionMinus (E := E)) =
      (2 : ℝ) • hestenesPionZero (E := E) := by
  rw [hestenesPionZero]
  simpa [hestenesPionPlus, hestenesPionMinus, smul_smul] using
    concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon
      (E := E)

theorem hestenesPion_real_closure :
    (hestenesPionPlus (E := E)).comp
        (hestenesPionPlus (E := E)) = 0 ∧
    (hestenesPionMinus (E := E)).comp
        (hestenesPionMinus (E := E)) = 0 ∧
    CARBracket (E := E)
        (hestenesPionMinus (E := E))
        (hestenesPionPlus (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) ∧
    CCRBracket (E := E)
        (hestenesPionPlus (E := E))
        (hestenesPionMinus (E := E)) =
      (2 : ℝ) • hestenesPionZero (E := E) := by
  exact ⟨hestenesPionPlus_sq (E := E),
    hestenesPionMinus_sq (E := E),
    hestenesPion_plus_minus_car (E := E),
    hestenesPion_plus_minus_lie (E := E)⟩

end RealHestenesKrein

end InfoGeometry.Canonical.PionChiralGoldstoneNative

end
