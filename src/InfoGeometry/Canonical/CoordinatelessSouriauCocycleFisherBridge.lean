import InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.CoordinatelessSouriauCocycleFisherBridge

2-cocycle/non-equivariant moment bridge for coordinateless Souriau-Fisher data.

The literature statement "2-cocycles locally modify the Souriau-Fisher metric
on coadjoint orbits" is not used as a proof.  This file isolates the exact
formal data required to make that statement true in Lean:

- an operator-valued Souriau moment;
- an explicit central/non-equivariant correction to that moment;
- an explicit Fisher correction bilinear form;
- symmetry/positivity obligations for the corrected metric.

Theorems here are therefore bridge theorems: they prove reduction, symmetry,
and nonnegativity only from supplied cocycle-correction hypotheses.
-/

namespace InfoGeometry.Canonical.CoordinatelessSouriauCocycleFisherBridge

open InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge
open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.GrandCanonical
open InfoGeometry.Volume.ConnesCocycle

universe u v

section OperatorCocycle

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "Obs" => AlgebraEnd H

/--
Operator-valued 2-cocycle correction for a Souriau moment map.

The symmetry carrier is a Mathlib `LieRing`.  Closure is the
Chevalley--Eilenberg cyclic identity for an operator-valued 2-cocycle with
trivial coefficient action.
-/
@[rep_depth operator]
structure SouriauMomentTwoCocycle (Symmetry : Type v) [LieRing Symmetry] where
  cocycle : Symmetry → Symmetry → Obs
  centralCorrection : Symmetry → Obs
  antisymmetric : ∀ X Y : Symmetry, cocycle X Y = -cocycle Y X
  closed :
    ∀ X Y Z : Symmetry,
      cocycle ⁅X, Y⁆ Z + cocycle ⁅Y, Z⁆ X + cocycle ⁅Z, X⁆ Y = 0
  moment_defect :
    ∀ X Y : Symmetry, centralCorrection X * centralCorrection Y
      - centralCorrection Y * centralCorrection X = cocycle X Y

/--
Moment map corrected by the central/non-equivariant cocycle lane.
-/
@[rep_depth operator]
noncomputable def correctedMomentOperator
    {Symmetry : Type v}
    [LieRing Symmetry]
    (J : OperatorSouriauMoment (H := H) Symmetry)
    (κ : SouriauMomentTwoCocycle (H := H) Symmetry)
    (X : Symmetry) : Obs :=
  J.momentOperator X + κ.centralCorrection X

/-- If the central correction vanishes on a generator, the corrected moment reduces to Souriau's moment. -/
@[rep_depth operator]
theorem correctedMomentOperator_eq_moment_of_zero_correction
    {Symmetry : Type v}
    [LieRing Symmetry]
    (J : OperatorSouriauMoment (H := H) Symmetry)
    (κ : SouriauMomentTwoCocycle (H := H) Symmetry)
    (X : Symmetry)
    (hzero : κ.centralCorrection X = 0) :
    correctedMomentOperator (H := H) J κ X = J.momentOperator X := by
  simp [correctedMomentOperator, hzero]

/--
The non-equivariance defect is exactly the supplied operator 2-cocycle.
-/
@[rep_depth operator]
theorem centralCorrection_commutator_eq_cocycle
    {Symmetry : Type v}
    [LieRing Symmetry]
    (κ : SouriauMomentTwoCocycle (H := H) Symmetry)
    (X Y : Symmetry) :
    κ.centralCorrection X * κ.centralCorrection Y
      - κ.centralCorrection Y * κ.centralCorrection X = κ.cocycle X Y :=
  κ.moment_defect X Y

/-- The 2-cocycle antisymmetry witness. -/
@[rep_depth operator]
theorem cocycle_antisymmetric
    {Symmetry : Type v}
    [LieRing Symmetry]
    (κ : SouriauMomentTwoCocycle (H := H) Symmetry)
    (X Y : Symmetry) :
    κ.cocycle X Y = -κ.cocycle Y X :=
  κ.antisymmetric X Y

/-- The operator-valued Chevalley--Eilenberg 2-cocycle identity. -/
@[rep_depth operator]
theorem cocycle_closed
    {Symmetry : Type v}
    [LieRing Symmetry]
    (κ : SouriauMomentTwoCocycle (H := H) Symmetry)
    (X Y Z : Symmetry) :
    κ.cocycle ⁅X, Y⁆ Z + κ.cocycle ⁅Y, Z⁆ X + κ.cocycle ⁅Z, X⁆ Y = 0 :=
  κ.closed X Y Z

end OperatorCocycle

section FisherCorrection

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Tangent : Type v}
variable (ω : AlgebraicState (H := H))

/--
Cocycle correction packet for a coordinateless quantum Fisher metric.

The corrected metric is `base + correction`; the correction is where a
non-equivariant Souriau moment or central extension enters the Fisher geometry.
-/
@[rep_depth operator]
structure CocycleFisherCorrection where
  base : QuantumFisherSLDMetric (H := H) Tangent ω
  correction : Tangent → Tangent → ℝ
  correction_symmetric : ∀ X Y : Tangent, correction X Y = correction Y X
  correction_nonnegative_on_diagonal : ∀ X : Tangent, 0 ≤ correction X X

namespace CocycleFisherCorrection

variable {ω}
variable (C : CocycleFisherCorrection (H := H) (Tangent := Tangent) ω)

/-- Fisher metric modified by the cocycle/non-equivariant moment correction. -/
@[rep_depth operator]
def correctedMetric (X Y : Tangent) : ℝ :=
  C.base.metric X Y + C.correction X Y

/-- The corrected metric is the base SLD metric plus the cocycle correction. -/
@[rep_depth operator]
theorem correctedMetric_eq_base_add_correction (X Y : Tangent) :
    C.correctedMetric X Y = C.base.metric X Y + C.correction X Y := rfl

/-- If the cocycle correction vanishes at `(X,Y)`, the corrected metric reduces to the base metric. -/
@[rep_depth operator]
theorem correctedMetric_eq_base_of_correction_zero
    (X Y : Tangent) (hzero : C.correction X Y = 0) :
    C.correctedMetric X Y = C.base.metric X Y := by
  simp [correctedMetric, hzero]

/-- Symmetry of the cocycle-corrected Souriau-Fisher metric. -/
@[rep_depth operator]
theorem correctedMetric_symm (X Y : Tangent) :
    C.correctedMetric X Y = C.correctedMetric Y X := by
  unfold correctedMetric
  rw [C.base.metric_symm X Y, C.correction_symmetric X Y]

/--
Diagonal nonnegativity of the corrected metric under base Fisher nonnegativity
and cocycle-correction nonnegativity.
-/
@[rep_depth operator]
theorem correctedMetric_diagonal_nonnegative
    (hbase : ∀ X : Tangent, 0 ≤ C.base.metric X X)
    (X : Tangent) :
    0 ≤ C.correctedMetric X X :=
  add_nonneg (hbase X) (C.correction_nonnegative_on_diagonal X)

end CocycleFisherCorrection

end FisherCorrection

section FiniteSouriauShadow

variable {α : Type u}

/--
Finite two-channel Souriau-Fisher correction.

This is only a finite shadow of the coordinateless operator bridge.  It is
useful for comparing with the existing `ResponseMatrix2` owner lane.
-/
@[rep_depth thermo]
structure FiniteSouriauFisherCocycleCorrection [Fintype α] [Nonempty α] where
  M : SouriauMomentMap α
  T : GeometricTemperature
  correction : ResponseMatrix2
  correction_symmetric : ResponseMatrix2.Symmetric correction
  correction_positiveSemidefinite : ResponseMatrix2.PositiveSemidefinite correction

namespace FiniteSouriauFisherCocycleCorrection

variable [Fintype α] [Nonempty α]
variable (C : FiniteSouriauFisherCocycleCorrection (α := α))

/-- Base finite Souriau-Fisher response packet. -/
@[rep_depth thermo]
noncomputable def baseResponse : ResponseMatrix2 :=
  souriauFisherResponseMatrix C.M C.T

/-- Corrected finite response packet, componentwise. -/
@[rep_depth thermo]
noncomputable def correctedResponse : ResponseMatrix2 where
  betaBeta := C.baseResponse.betaBeta + C.correction.betaBeta
  betaMu := C.baseResponse.betaMu + C.correction.betaMu
  muBeta := C.baseResponse.muBeta + C.correction.muBeta
  muMu := C.baseResponse.muMu + C.correction.muMu

/-- The corrected `ββ` response is base plus cocycle correction. -/
@[rep_depth thermo]
theorem correctedResponse_betaBeta :
    C.correctedResponse.betaBeta = C.baseResponse.betaBeta + C.correction.betaBeta := rfl

/-- If the correction vanishes componentwise, the corrected finite response is the base response. -/
@[rep_depth thermo]
theorem correctedResponse_eq_base_of_correction_zero
    (hββ : C.correction.betaBeta = 0)
    (hβμ : C.correction.betaMu = 0)
    (hμβ : C.correction.muBeta = 0)
    (hμμ : C.correction.muMu = 0) :
    C.correctedResponse = C.baseResponse := by
  cases hbase : C.baseResponse
  cases hcorr : C.correction
  simp [hcorr] at hββ hβμ hμβ hμμ
  simp [correctedResponse, hbase, hcorr, hββ, hβμ, hμβ, hμμ]

/-- Symmetry of the finite corrected response packet. -/
@[rep_depth thermo]
theorem correctedResponse_symmetric :
    ResponseMatrix2.Symmetric C.correctedResponse := by
  have hbase : ResponseMatrix2.Symmetric C.baseResponse :=
    souriauFisherResponseMatrix_symmetric C.M C.T
  have hcorr : ResponseMatrix2.Symmetric C.correction :=
    C.correction_symmetric
  have hbase' :
      (souriauFisherResponseMatrix C.M C.T).betaMu =
        (souriauFisherResponseMatrix C.M C.T).muBeta := by
    simpa [baseResponse, ResponseMatrix2.Symmetric] using hbase
  unfold ResponseMatrix2.Symmetric at hcorr ⊢
  simp [correctedResponse, baseResponse, hbase', hcorr]

end FiniteSouriauFisherCocycleCorrection

end FiniteSouriauShadow

end InfoGeometry.Canonical.CoordinatelessSouriauCocycleFisherBridge
