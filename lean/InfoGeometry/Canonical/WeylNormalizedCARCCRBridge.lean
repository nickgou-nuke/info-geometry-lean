import InfoGeometry.Canonical.DrazinHodgeChiralBridge
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.WeylNormalizedCARCCRBridge

Weyl normalization for the calibrated Drazin/Hodge chiral arrows.

The Drazin/Hodge bridge supplies the two projector arrows `D⁺ = u⁻(D)` and
`D⁻ = u⁺(D)`.  This file records the final algebraic normalization step:
if the unnormalized CAR/CCR relation has metric core `ν • 1`, and the Weyl
scale satisfies `λ²ν = 1`, then the normalized arrows satisfy the unit
CAR/CCR relation.

This is a calibration layer.  It does not construct a Fock representation,
does not prove analytic field equations, and does not assert a Type-III
modular-flow theorem.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance weylNormalizedCARCCRNormedRing : NormedRing EndH :=
  inferInstance
noncomputable local instance weylNormalizedCARCCRNormedAlgebra : NormedAlgebra ℝ EndH :=
  inferInstance
local instance weylNormalizedCARCCRTopologicalRing : IsTopologicalRing EndH :=
  inferInstance
local instance weylNormalizedCARCCRSMulCommClass : SMulCommClass ℝ EndH EndH :=
  inferInstance
local instance weylNormalizedCARCCRIsScalarTower : IsScalarTower ℝ EndH EndH :=
  inferInstance

/--
Weyl-normalized CAR/CCR calibration over the Drazin/Hodge chiral arrows.

`ν` is the raw metric/core scale of the unnormalized arrow algebra.  The Weyl
condition `λ²ν = 1` is explicit property data.
-/
@[rep_depth operator]
structure WeylNormalizedCARCCRBridge where
  /-- The calibrated Drazin/Hodge chiral bridge. -/
  hodgeBridge : DrazinHodgeChiralBridge (E := E)

  /-- Weyl scale applied to the two chiral arrows. -/
  lambda : ℝ

  /-- Raw metric/core scale in the unnormalized CAR/CCR relation. -/
  nu : ℝ

  /-- Unit Weyl normalization condition. -/
  lambda_sq_mul_nu_eq_one : lambda ^ 2 * nu = 1

namespace WeylNormalizedCARCCRBridge

variable (B : WeylNormalizedCARCCRBridge (E := E))

/-- Weyl-normalized `D⁺ = u⁻(D)` arrow. -/
@[rep_depth operator]
noncomputable def normalizedDiracPlus : EndH :=
  B.lambda • B.hodgeBridge.diracPlus

/-- Weyl-normalized `D⁻ = u⁺(D)` arrow. -/
@[rep_depth operator]
noncomputable def normalizedDiracMinus : EndH :=
  B.lambda • B.hodgeBridge.diracMinus

/-- Readback: normalized plus arrow is the Weyl-scaled `u⁻` channel. -/
@[rep_depth operator]
theorem normalizedDiracPlus_eq_lambda_smul_uMinus :
    B.normalizedDiracPlus = B.lambda • B.hodgeBridge.drazinSplit.uMinus B.hodgeBridge.Dirac := by
  unfold normalizedDiracPlus
  rw [DrazinHodgeChiralBridge.diracPlus_eq_uMinus (B := B.hodgeBridge)]

/-- Readback: normalized minus arrow is the Weyl-scaled `u⁺` channel. -/
@[rep_depth operator]
theorem normalizedDiracMinus_eq_lambda_smul_uPlus :
    B.normalizedDiracMinus = B.lambda • B.hodgeBridge.drazinSplit.uPlus B.hodgeBridge.Dirac := by
  unfold normalizedDiracMinus
  rw [DrazinHodgeChiralBridge.diracMinus_eq_uPlus (B := B.hodgeBridge)]

/--
Raw CAR relation for the unnormalized Drazin/Hodge arrows.

This is a predicate, not a theorem: the bridge only normalizes a supplied raw
relation.
-/
@[rep_depth operator]
def RawCAR : Prop :=
  B.hodgeBridge.diracPlus * B.hodgeBridge.diracMinus
      + B.hodgeBridge.diracMinus * B.hodgeBridge.diracPlus =
    B.nu • (1 : EndH)

/--
Raw CCR relation for the unnormalized Drazin/Hodge arrows.

This is a predicate, not a theorem: the bridge only normalizes a supplied raw
relation.
-/
@[rep_depth operator]
def RawCCR : Prop :=
  B.hodgeBridge.diracMinus * B.hodgeBridge.diracPlus
      - B.hodgeBridge.diracPlus * B.hodgeBridge.diracMinus =
    B.nu • (1 : EndH)

/--
Weyl-normalized CAR readback.

If the unnormalized anticommutator is `ν • 1` and `λ²ν = 1`, the normalized
arrows have unit anticommutator.
-/
@[rep_depth operator]
theorem normalizedCAR_of_raw (hRaw : B.RawCAR) :
    B.normalizedDiracPlus * B.normalizedDiracMinus
        + B.normalizedDiracMinus * B.normalizedDiracPlus =
      (1 : EndH) := by
  unfold RawCAR at hRaw
  unfold normalizedDiracPlus normalizedDiracMinus
  calc
    (B.lambda • B.hodgeBridge.diracPlus) * (B.lambda • B.hodgeBridge.diracMinus)
          + (B.lambda • B.hodgeBridge.diracMinus) * (B.lambda • B.hodgeBridge.diracPlus)
        =
      (B.lambda * B.lambda) •
        (B.hodgeBridge.diracPlus * B.hodgeBridge.diracMinus
          + B.hodgeBridge.diracMinus * B.hodgeBridge.diracPlus) := by
          simp [smul_add, smul_smul]
    _ = (B.lambda * B.lambda) • (B.nu • (1 : EndH)) := by
          rw [hRaw]
    _ = ((B.lambda * B.lambda) * B.nu) • (1 : EndH) := by
          rw [smul_smul]
    _ = (1 : EndH) := by
          have hUnit : (B.lambda * B.lambda) * B.nu = 1 := by
            simpa [pow_two] using B.lambda_sq_mul_nu_eq_one
          rw [hUnit]
          simp

/--
Weyl-normalized CCR readback.

If the unnormalized commutator is `ν • 1` and `λ²ν = 1`, the normalized arrows
have unit commutator in the chosen arrow order.
-/
@[rep_depth operator]
theorem normalizedCCR_of_raw (hRaw : B.RawCCR) :
    B.normalizedDiracMinus * B.normalizedDiracPlus
        - B.normalizedDiracPlus * B.normalizedDiracMinus =
      (1 : EndH) := by
  unfold RawCCR at hRaw
  unfold normalizedDiracPlus normalizedDiracMinus
  calc
    (B.lambda • B.hodgeBridge.diracMinus) * (B.lambda • B.hodgeBridge.diracPlus)
          - (B.lambda • B.hodgeBridge.diracPlus) * (B.lambda • B.hodgeBridge.diracMinus)
        =
      (B.lambda * B.lambda) •
        (B.hodgeBridge.diracMinus * B.hodgeBridge.diracPlus
          - B.hodgeBridge.diracPlus * B.hodgeBridge.diracMinus) := by
          simp [smul_sub, smul_smul]
    _ = (B.lambda * B.lambda) • (B.nu • (1 : EndH)) := by
          rw [hRaw]
    _ = ((B.lambda * B.lambda) * B.nu) • (1 : EndH) := by
          rw [smul_smul]
    _ = (1 : EndH) := by
          have hUnit : (B.lambda * B.lambda) * B.nu = 1 := by
            simpa [pow_two] using B.lambda_sq_mul_nu_eq_one
          rw [hUnit]
          simp

/-- Same-arrow nilpotence survives Weyl normalization for the `D⁺` channel. -/
@[rep_depth operator]
theorem normalizedDiracPlus_mul_normalizedDiracPlus_eq_zero :
    B.normalizedDiracPlus * B.normalizedDiracPlus = 0 := by
  unfold normalizedDiracPlus
  calc
    (B.lambda • B.hodgeBridge.diracPlus) * (B.lambda • B.hodgeBridge.diracPlus)
        = (B.lambda * B.lambda) •
            (B.hodgeBridge.diracPlus * B.hodgeBridge.diracPlus) := by
            simp [smul_smul]
    _ = (B.lambda * B.lambda) • (0 : EndH) := by
          rw [DrazinHodgeChiralBridge.diracPlus_mul_diracPlus_eq_zero
            (B := B.hodgeBridge)]
    _ = 0 := by
          simp

/-- Same-arrow nilpotence survives Weyl normalization for the `D⁻` channel. -/
@[rep_depth operator]
theorem normalizedDiracMinus_mul_normalizedDiracMinus_eq_zero :
    B.normalizedDiracMinus * B.normalizedDiracMinus = 0 := by
  unfold normalizedDiracMinus
  calc
    (B.lambda • B.hodgeBridge.diracMinus) * (B.lambda • B.hodgeBridge.diracMinus)
        = (B.lambda * B.lambda) •
            (B.hodgeBridge.diracMinus * B.hodgeBridge.diracMinus) := by
            simp [smul_smul]
    _ = (B.lambda * B.lambda) • (0 : EndH) := by
          rw [DrazinHodgeChiralBridge.diracMinus_mul_diracMinus_eq_zero
            (B := B.hodgeBridge)]
    _ = 0 := by
          simp

end WeylNormalizedCARCCRBridge

end Core

section FockCore

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- CCR pair predicate on the existing supergraded Fock lane. -/
@[rep_depth krein]
def IsCCRPair (A B : FockEndomorphism E) : Prop :=
  fockCommutator (E := E) A B = ContinuousLinearMap.id ℝ (DoubledSpace E)

/--
Scaled CAR pair on the existing Fock lane.

The raw pair has CAR core `ν • 1`; the normalized pair is obtained by Weyl
scaling with `λ`, and the theorem below proves the normalized pair is a genuine
`IsCARPair` when `λ²ν = 1`.
-/
@[rep_depth krein]
structure ScaledCARPair
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  annihilation : FockEndomorphism E
  creation : FockEndomorphism E
  lambda : ℝ
  nu : ℝ
  lambda_sq_mul_nu_eq_one : lambda ^ 2 * nu = 1
  raw_annihilation_nil :
    fockAnticommutator (E := E) annihilation annihilation = 0
  raw_creation_nil :
    fockAnticommutator (E := E) creation creation = 0
  raw_mixed :
    fockAnticommutator (E := E) annihilation creation =
      nu • ContinuousLinearMap.id ℝ (DoubledSpace E)

namespace ScaledCARPair

variable (P : ScaledCARPair E)

/-- Weyl-normalized annihilation operator. -/
@[rep_depth krein]
noncomputable def normalizedAnnihilation : FockEndomorphism E :=
  P.lambda • P.annihilation

/-- Weyl-normalized creation operator. -/
@[rep_depth krein]
noncomputable def normalizedCreation : FockEndomorphism E :=
  P.lambda • P.creation

/-- Scaling both Fock arguments extracts a quadratic Weyl factor from the anticommutator. -/
@[rep_depth krein]
theorem fockAnticommutator_smul_smul
    (r : ℝ) (A B : FockEndomorphism E) :
    fockAnticommutator (E := E) (r • A) (r • B) =
      (r * r) • fockAnticommutator (E := E) A B := by
  change
    fockSuperBracket (E := E) SuperParity.odd SuperParity.odd (r • A) (r • B) =
      (r * r) • fockSuperBracket (E := E) SuperParity.odd SuperParity.odd A B
  unfold fockSuperBracket
  rw [superBracket_smul_left, superBracket_smul_right]
  simp [smul_smul]

/-- The Weyl-normalized pair satisfies the genuine Fock CAR package. -/
@[rep_depth krein]
theorem normalized_isCARPair :
    IsCARPair (E := E) P.normalizedAnnihilation P.normalizedCreation := by
  refine ⟨?_, ?_, ?_⟩
  · unfold normalizedAnnihilation
    change fockAnticommutator (E := E) (P.lambda • P.annihilation)
        (P.lambda • P.annihilation) = 0
    rw [fockAnticommutator_smul_smul (E := E)]
    rw [P.raw_annihilation_nil]
    apply ContinuousLinearMap.ext
    intro x
    simp
  · unfold normalizedCreation
    change fockAnticommutator (E := E) (P.lambda • P.creation)
        (P.lambda • P.creation) = 0
    rw [fockAnticommutator_smul_smul (E := E)]
    rw [P.raw_creation_nil]
    apply ContinuousLinearMap.ext
    intro x
    simp
  · unfold normalizedAnnihilation normalizedCreation
    change fockAnticommutator (E := E) (P.lambda • P.annihilation)
        (P.lambda • P.creation) = ContinuousLinearMap.id ℝ (DoubledSpace E)
    rw [fockAnticommutator_smul_smul (E := E)]
    rw [P.raw_mixed]
    rw [smul_smul]
    have hUnit : (P.lambda * P.lambda) * P.nu = 1 := by
      simpa [pow_two] using P.lambda_sq_mul_nu_eq_one
    rw [hUnit]
    simp

end ScaledCARPair

/-! ## Concrete split-`Cl(1,1)` CAR property -/

/--
Canonical polarized Majorana object underlying the concrete split-`Cl(1,1)`
Fock CAR property.
-/
@[rep_depth krein]
noncomputable abbrev concreteCl11CanonicalPolarizedMajorana :
    InfoGeometry.Quantum.RealMajoranaCategory.PolarizedMajorana :=
  InfoGeometry.Quantum.RealMajoranaCategory.cl11CanonicalPolarizedMajorana (E := E)

/--
The concrete split-`Cl(1,1)` Fock CAR pair is sourced from the canonical
polarized Majorana realization, not from an ad hoc ladder API.
-/
@[rep_depth krein]
theorem concreteCl11FockCAR_from_canonicalPolarizedMajorana :
    IsCARPair (E := E)
      (cliffordConcreteAnnihilation (E := E))
      (cliffordConcreteCreation (E := E)) :=
  cliffordConcreteIsCARPair (E := E)

/--
Concrete split-`Cl(1,1)` Weyl-normalized CAR property.

This packages the repo-owned concrete Fock CAR pair as a `ScaledCARPair` with
unit Weyl gauge `λ = 1` and raw core `ν = 1`.  It is the safest direct property
for downstream normalized CAR readouts.
-/
@[rep_depth krein]
noncomputable def concreteCl11ScaledCARPair :
    ScaledCARPair E where
  annihilation :=
    cliffordConcreteAnnihilation (E := E)
  creation :=
    cliffordConcreteCreation (E := E)
  lambda := 1
  nu := 1
  lambda_sq_mul_nu_eq_one := by
    norm_num
  raw_annihilation_nil := by
    exact (concreteCl11FockCAR_from_canonicalPolarizedMajorana (E := E)).1
  raw_creation_nil := by
    exact (concreteCl11FockCAR_from_canonicalPolarizedMajorana (E := E)).2.1
  raw_mixed := by
    simpa using (concreteCl11FockCAR_from_canonicalPolarizedMajorana (E := E)).2.2

/--
The concrete split-`Cl(1,1)` scaled pair normalizes to a genuine Fock CAR pair.
-/
@[rep_depth krein]
theorem concreteCl11ScaledCARPair_normalized_isCARPair :
    IsCARPair (E := E)
      (concreteCl11ScaledCARPair (E := E)).normalizedAnnihilation
      (concreteCl11ScaledCARPair (E := E)).normalizedCreation :=
  (concreteCl11ScaledCARPair (E := E)).normalized_isCARPair

/--
Scaled CCR pair on the existing Fock lane.

The raw commutator has CCR core `ν • 1`; Weyl scaling with `λ²ν = 1` produces
the unit CCR relation.
-/
@[rep_depth krein]
structure ScaledCCRPair
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  annihilation : FockEndomorphism E
  creation : FockEndomorphism E
  lambda : ℝ
  nu : ℝ
  lambda_sq_mul_nu_eq_one : lambda ^ 2 * nu = 1
  raw_commutator :
    fockCommutator (E := E) annihilation creation =
      nu • ContinuousLinearMap.id ℝ (DoubledSpace E)

namespace ScaledCCRPair

variable (P : ScaledCCRPair E)

/-- Weyl-normalized annihilation operator. -/
@[rep_depth krein]
noncomputable def normalizedAnnihilation : FockEndomorphism E :=
  P.lambda • P.annihilation

/-- Weyl-normalized creation operator. -/
@[rep_depth krein]
noncomputable def normalizedCreation : FockEndomorphism E :=
  P.lambda • P.creation

/-- Scaling both Fock arguments extracts a quadratic Weyl factor from the commutator. -/
@[rep_depth krein]
theorem fockCommutator_smul_smul
    (r : ℝ) (A B : FockEndomorphism E) :
    fockCommutator (E := E) (r • A) (r • B) =
      (r * r) • fockCommutator (E := E) A B := by
  change
    fockSuperBracket (E := E) SuperParity.even SuperParity.even (r • A) (r • B) =
      (r * r) • fockSuperBracket (E := E) SuperParity.even SuperParity.even A B
  unfold fockSuperBracket
  rw [superBracket_smul_left, superBracket_smul_right]
  simp [smul_smul]

/-- The Weyl-normalized pair satisfies the unit Fock CCR predicate. -/
@[rep_depth krein]
theorem normalized_isCCRPair :
    IsCCRPair (E := E) P.normalizedAnnihilation P.normalizedCreation := by
  unfold IsCCRPair normalizedAnnihilation normalizedCreation
  rw [fockCommutator_smul_smul (E := E)]
  rw [P.raw_commutator]
  rw [smul_smul]
  have hUnit : (P.lambda * P.lambda) * P.nu = 1 := by
    simpa [pow_two] using P.lambda_sq_mul_nu_eq_one
  rw [hUnit]
  simp

end ScaledCCRPair

/-! ## Drazin/Hodge arrow adapters into the Fock CAR/CCR owner -/

section DrazinHodgeFockAdapters

local notation "EndH" => E →L[ℝ] E

/--
Adapter from calibrated Drazin/Hodge arrows to the Fock `ScaledCARPair` owner.

The representation map and raw Fock CAR identities are explicit property data.
This prevents the invalid promotion of arbitrary projector arrows to genuine
Fock CAR operators.
-/
@[rep_depth krein]
structure DrazinHodgeFockCARAdapter where
  /-- Calibrated Drazin/Hodge arrow source. -/
  hodgeBridge : DrazinHodgeChiralBridge (E := E)

  /-- Representation/readout of bounded operators as Fock endomorphisms. -/
  toFock : EndH → FockEndomorphism E

  /-- Weyl scale used by the existing `ScaledCARPair` owner. -/
  lambda : ℝ

  /-- Raw CAR metric/core scale. -/
  nu : ℝ

  /-- Unit Weyl normalization condition. -/
  lambda_sq_mul_nu_eq_one : lambda ^ 2 * nu = 1

  /-- The represented `D⁺ = u⁻(D)` channel is Fock-CAR nilpotent. -/
  raw_diracPlus_nil :
    fockAnticommutator (E := E)
      (toFock hodgeBridge.diracPlus) (toFock hodgeBridge.diracPlus) = 0

  /-- The represented `D⁻ = u⁺(D)` channel is Fock-CAR nilpotent. -/
  raw_diracMinus_nil :
    fockAnticommutator (E := E)
      (toFock hodgeBridge.diracMinus) (toFock hodgeBridge.diracMinus) = 0

  /-- The represented mixed arrow anticommutator has raw metric/core `ν`. -/
  raw_mixed :
    fockAnticommutator (E := E)
      (toFock hodgeBridge.diracPlus) (toFock hodgeBridge.diracMinus) =
        nu • ContinuousLinearMap.id ℝ (DoubledSpace E)

namespace DrazinHodgeFockCARAdapter

variable (A : DrazinHodgeFockCARAdapter (E := E))

/-- The represented Drazin/Hodge arrows as an existing `ScaledCARPair`. -/
@[rep_depth krein]
noncomputable def scaledCARPair : ScaledCARPair E where
  annihilation := A.toFock A.hodgeBridge.diracPlus
  creation := A.toFock A.hodgeBridge.diracMinus
  lambda := A.lambda
  nu := A.nu
  lambda_sq_mul_nu_eq_one := A.lambda_sq_mul_nu_eq_one
  raw_annihilation_nil := A.raw_diracPlus_nil
  raw_creation_nil := A.raw_diracMinus_nil
  raw_mixed := A.raw_mixed

/-- Readback: the adapter annihilation operator is the represented `D⁺ = u⁻(D)` arrow. -/
@[rep_depth krein]
theorem scaledCARPair_annihilation_eq_toFock_diracPlus :
    (A.scaledCARPair).annihilation = A.toFock A.hodgeBridge.diracPlus :=
  rfl

/-- Readback: the adapter creation operator is the represented `D⁻ = u⁺(D)` arrow. -/
@[rep_depth krein]
theorem scaledCARPair_creation_eq_toFock_diracMinus :
    (A.scaledCARPair).creation = A.toFock A.hodgeBridge.diracMinus :=
  rfl

/-- The represented, Weyl-normalized Drazin/Hodge arrows satisfy genuine Fock CAR. -/
@[rep_depth krein]
theorem normalized_isCARPair :
    IsCARPair (E := E)
      (A.scaledCARPair.normalizedAnnihilation)
      (A.scaledCARPair.normalizedCreation) :=
  A.scaledCARPair.normalized_isCARPair

end DrazinHodgeFockCARAdapter

/--
Adapter from calibrated Drazin/Hodge arrows to the Fock `ScaledCCRPair` owner.

As with the CAR adapter, this is property-gated: the represented commutator law
must be supplied by the backend model.
-/
@[rep_depth krein]
structure DrazinHodgeFockCCRAdapter where
  /-- Calibrated Drazin/Hodge arrow source. -/
  hodgeBridge : DrazinHodgeChiralBridge (E := E)

  /-- Representation/readout of bounded operators as Fock endomorphisms. -/
  toFock : EndH → FockEndomorphism E

  /-- Weyl scale used by the existing `ScaledCCRPair` owner. -/
  lambda : ℝ

  /-- Raw CCR metric/core scale. -/
  nu : ℝ

  /-- Unit Weyl normalization condition. -/
  lambda_sq_mul_nu_eq_one : lambda ^ 2 * nu = 1

  /-- The represented arrow commutator has raw metric/core `ν`. -/
  raw_commutator :
    fockCommutator (E := E)
      (toFock hodgeBridge.diracMinus) (toFock hodgeBridge.diracPlus) =
        nu • ContinuousLinearMap.id ℝ (DoubledSpace E)

namespace DrazinHodgeFockCCRAdapter

variable (A : DrazinHodgeFockCCRAdapter (E := E))

/-- The represented Drazin/Hodge arrows as an existing `ScaledCCRPair`. -/
@[rep_depth krein]
noncomputable def scaledCCRPair : ScaledCCRPair E where
  annihilation := A.toFock A.hodgeBridge.diracMinus
  creation := A.toFock A.hodgeBridge.diracPlus
  lambda := A.lambda
  nu := A.nu
  lambda_sq_mul_nu_eq_one := A.lambda_sq_mul_nu_eq_one
  raw_commutator := A.raw_commutator

/-- Readback: the CCR annihilation channel is the represented `D⁻ = u⁺(D)` arrow. -/
@[rep_depth krein]
theorem scaledCCRPair_annihilation_eq_toFock_diracMinus :
    (A.scaledCCRPair).annihilation = A.toFock A.hodgeBridge.diracMinus :=
  rfl

/-- Readback: the CCR creation channel is the represented `D⁺ = u⁻(D)` arrow. -/
@[rep_depth krein]
theorem scaledCCRPair_creation_eq_toFock_diracPlus :
    (A.scaledCCRPair).creation = A.toFock A.hodgeBridge.diracPlus :=
  rfl

/-- The represented, Weyl-normalized Drazin/Hodge arrows satisfy unit Fock CCR. -/
@[rep_depth krein]
theorem normalized_isCCRPair :
    IsCCRPair (E := E)
      (A.scaledCCRPair.normalizedAnnihilation)
      (A.scaledCCRPair.normalizedCreation) :=
  A.scaledCCRPair.normalized_isCCRPair

end DrazinHodgeFockCCRAdapter

end DrazinHodgeFockAdapters

end FockCore

end InfoGeometry.Canonical
