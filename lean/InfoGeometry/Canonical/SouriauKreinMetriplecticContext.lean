import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Canonical.Operators
import InfoGeometry.Canonical.OperatorialCramerRao
import InfoGeometry.Canonical.OperatorFenchelRegularCone
import InfoGeometry.Canonical.WeightedWeylNormalizationBridge
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Thermodynamics.SouriauKillingFlow
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SouriauKreinMetriplecticContext

Operatorial Souriau/Onsager context on the doubled Krein carrier.

This file deliberately avoids finite response matrices.  It packages only the
already-owned operatorial lane:

- perturbation channels are doubled-space endomorphisms `EndH := H₂ →L[ℝ] H₂`;
- the metric response is the symmetric operatorial Hessian read by a
  `PotentialDatum` probe;
- the diagonal response is the probed double transport commutator;
- the skew response is the probed bracket derivation;
- the J-reflected phase channel flips sign by the existing Onsager-Casimir
  theorem;
- density/Weyl weight enters as a generator-side `w • K` commutator correction.

It does not assert positivity of the indefinite Krein response, nor a full
coadjoint-orbit metriplectic flow.  Those require separate operatorial
hypotheses.
-/

namespace InfoGeometry.Canonical.SouriauKreinMetriplectic

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.DensityWeightIntertwinerBridge
open InfoGeometry.Canonical.OnsagerCasimirJ
open InfoGeometry.Canonical.OperatorialCramerRao
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.OperatorFenchelRegularCone
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.WeightedWeylNormalizationBridge
open InfoGeometry.Krein

section Core

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Explicit operatorial context joining the Souriau/Onsager response lane to the
weighted Weyl generator lane on the same doubled Krein carrier.
-/
@[rep_depth transport]
structure OperatorialMetriplecticContext where
  P : PotentialDatum (E := E)
  reference : H₂
  comparison : H₂
  ψ : H₂
  A : EndH
  X : EndH
  Y : EndH
  weight : ℝ
  X_jInvariant : IsJInvariant X
  Y_jInvariant : IsJInvariant Y

namespace OperatorialMetriplecticContext

variable (C : OperatorialMetriplecticContext (E := E))

/-- Symmetric Onsager/Souriau response read by the operatorial potential probe. -/
@[rep_depth transport]
noncomputable def metricResponse : ℝ :=
  responseCoefficient (E := E) C.P C.X C.Y C.A

/-- Same metric response with perturbation channels swapped. -/
@[rep_depth transport]
noncomputable def swappedMetricResponse : ℝ :=
  responseCoefficient (E := E) C.P C.Y C.X C.A

/-- Skew curvature/bracket response read by the operatorial potential probe. -/
@[rep_depth transport]
noncomputable def curvatureResponse : ℝ :=
  curvatureCoefficient (E := E) C.P C.X C.Y C.A

/-- Same skew response with perturbation channels swapped. -/
@[rep_depth transport]
noncomputable def swappedCurvatureResponse : ℝ :=
  curvatureCoefficient (E := E) C.P C.Y C.X C.A

/-- Diagonal metric response, the operatorial Hessian channel. -/
@[rep_depth transport]
noncomputable def diagonalMetricResponse : ℝ :=
  responseCoefficient (E := E) C.P C.X C.X C.A

/-- The second diagonal metric response for the `Y` perturbation channel. -/
@[rep_depth transport]
noncomputable def yDiagonalMetricResponse : ℝ :=
  responseCoefficient (E := E) C.P C.Y C.Y C.A

/-- The mixed operatorial metric response in the `(X,Y)` order. -/
@[rep_depth transport]
noncomputable def mixedMetricResponseXY : ℝ :=
  responseCoefficient (E := E) C.P C.X C.Y C.A

/-- The mixed operatorial metric response in the `(Y,X)` order. -/
@[rep_depth transport]
noncomputable def mixedMetricResponseYX : ℝ :=
  responseCoefficient (E := E) C.P C.Y C.X C.A

/-- Linear operatorial Onsager flux in the `X` channel. -/
@[rep_depth transport]
noncomputable def operatorialXFlux (xForce yForce : ℝ) : ℝ :=
  C.diagonalMetricResponse * xForce + C.mixedMetricResponseXY * yForce

/-- Linear operatorial Onsager flux in the `Y` channel. -/
@[rep_depth transport]
noncomputable def operatorialYFlux (xForce yForce : ℝ) : ℝ :=
  C.mixedMetricResponseYX * xForce + C.yDiagonalMetricResponse * yForce

/--
Two-channel operatorial entropy production on the doubled Krein carrier.

This is not a finite-state response matrix: the coefficients are read from the
operatorial Hessian form on `EndH := DoubledSpace E →L[ℝ] DoubledSpace E`.
-/
@[rep_depth transport]
noncomputable def operatorialEntropyProduction (xForce yForce : ℝ) : ℝ :=
  xForce * C.operatorialXFlux xForce yForce
    + yForce * C.operatorialYFlux xForce yForce

/-- Operatorial weighted Weyl dynamics at the context weight. -/
@[rep_depth transport]
noncomputable def weightedDynamics : EndH :=
  densityWeightLiftedDynamics C.P C.ψ C.A C.weight

/-- Operatorial zero-weight dynamics. -/
@[rep_depth transport]
noncomputable def zeroWeightDynamics : EndH :=
  densityWeightLiftedDynamics C.P C.ψ C.A 0

/-- Weighted phase-axis commutator correction. -/
@[rep_depth transport]
noncomputable def weightedPhaseAxisCommutator : EndH :=
  C.weight • transportCommutator (E := E) (densityWeightPhaseAxis (E := E)) C.A

/--
Coordinate-free Weyl-covariant thermodynamic derivation.

This is the repo-native operational replacement for a coordinate derivative:
the generator is the Souriau temperature vector corrected by the Weyl density
weight, and the derivative of an observable is its Lie/commutator derivation.
-/
@[rep_depth transport]
noncomputable def weylCovariantThermodynamicDerivation : EndH :=
  observableLieDerivation (E := E)
    (densityWeightLiftedTransportGenerator C.P C.ψ C.weight) C.A

/-- Zero-weight thermodynamic Lie derivation. -/
@[rep_depth transport]
noncomputable def zeroWeightThermodynamicDerivation : EndH :=
  observableLieDerivation (E := E)
    (densityWeightLiftedTransportGenerator C.P C.ψ 0) C.A

/-- Weyl phase-axis Lie-derivation correction before multiplying by the weight. -/
@[rep_depth transport]
noncomputable def phaseAxisThermodynamicDerivation : EndH :=
  observableLieDerivation (E := E) (densityWeightPhaseAxis (E := E)) C.A

/-- The phase/J-Casimir response before J-reflection. -/
@[rep_depth transport]
noncomputable def phaseCorrelation : ℝ :=
  InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation (E := E)
    C.reference C.comparison (channelPhaseAxis C.X) C.Y

/-- The same phase response after modular J-reflection of both states. -/
@[rep_depth transport]
noncomputable def jReflectedPhaseCorrelation : ℝ :=
  InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation (E := E)
    (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E) C.reference)
    (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E) C.comparison)
    (channelPhaseAxis C.X) C.Y

/-- Operatorial Onsager reciprocity: the metric response is symmetric. -/
@[rep_depth transport]
theorem metricResponse_swap :
    C.metricResponse = C.swappedMetricResponse := by
  simpa [metricResponse, swappedMetricResponse] using
    responseCoefficient_swap (E := E) C.P C.X C.Y C.A

/-- Mixed-response symmetry in the explicit two-channel operatorial packet. -/
@[rep_depth transport]
theorem mixedMetricResponse_symm :
    C.mixedMetricResponseXY = C.mixedMetricResponseYX := by
  simpa [mixedMetricResponseXY, mixedMetricResponseYX] using
    responseCoefficient_swap (E := E) C.P C.X C.Y C.A

/-- Operatorial entropy production as the symmetric quadratic response form. -/
@[rep_depth transport]
theorem operatorialEntropyProduction_eq_quadratic
    (xForce yForce : ℝ) :
    C.operatorialEntropyProduction xForce yForce =
      C.diagonalMetricResponse * xForce ^ (2 : ℕ)
        + 2 * C.mixedMetricResponseXY * xForce * yForce
          + C.yDiagonalMetricResponse * yForce ^ (2 : ℕ) := by
  unfold operatorialEntropyProduction operatorialXFlux operatorialYFlux
  rw [← C.mixedMetricResponse_symm]
  ring

/--
Positive-semidefinite operatorial response context for the two perturbation
channels `X,Y`.

The Krein metric is indefinite, so this file does not assert positivity
globally.  Positivity enters only through these explicit scalar response
hypotheses on the probed operatorial Hessian packet.
-/
@[rep_depth transport]
def OperatorialMetricResponsePSD : Prop :=
  0 ≤ C.diagonalMetricResponse ∧
    0 ≤ C.yDiagonalMetricResponse ∧
      0 ≤ C.diagonalMetricResponse * C.yDiagonalMetricResponse
        - C.mixedMetricResponseXY * C.mixedMetricResponseYX

/--
Constructive square-response operatorial packet.

This is a dimension-agnostic replacement for directly assuming scalar PSD when
the concrete operator model supplies orthogonal Onsager channels: both diagonal
responses are real squares and the mixed response vanishes.  No finite response
matrix or diagonal count-state model is used.
-/
@[rep_depth transport]
structure SquareOperatorialResponseContext where
  xAmplitude : ℝ
  yAmplitude : ℝ
  diagonalMetricResponse_eq_square :
    C.diagonalMetricResponse = xAmplitude ^ (2 : ℕ)
  yDiagonalMetricResponse_eq_square :
    C.yDiagonalMetricResponse = yAmplitude ^ (2 : ℕ)
  mixedMetricResponseXY_eq_zero :
    C.mixedMetricResponseXY = 0

namespace SquareOperatorialResponseContext

variable {C}

/-- The `X` diagonal response is nonnegative because it is a square. -/
@[rep_depth transport]
theorem diagonalMetricResponse_nonnegative
    (S : SquareOperatorialResponseContext C) :
    0 ≤ C.diagonalMetricResponse := by
  rw [SquareOperatorialResponseContext.diagonalMetricResponse_eq_square S]
  exact sq_nonneg S.xAmplitude

/-- The `Y` diagonal response is nonnegative because it is a square. -/
@[rep_depth transport]
theorem yDiagonalMetricResponse_nonnegative
    (S : SquareOperatorialResponseContext C) :
    0 ≤ C.yDiagonalMetricResponse := by
  rw [SquareOperatorialResponseContext.yDiagonalMetricResponse_eq_square S]
  exact sq_nonneg S.yAmplitude

/-- Orthogonal square-response channels construct the scalar PSD packet. -/
@[rep_depth transport]
theorem operatorialMetricResponsePSD
    (S : SquareOperatorialResponseContext C) :
    C.OperatorialMetricResponsePSD := by
  refine
    ⟨diagonalMetricResponse_nonnegative S,
      yDiagonalMetricResponse_nonnegative S, ?_⟩
  have hyx : C.mixedMetricResponseYX = 0 := by
    rw [C.mixedMetricResponse_symm.symm]
    exact S.mixedMetricResponseXY_eq_zero
  rw [S.diagonalMetricResponse_eq_square,
    S.yDiagonalMetricResponse_eq_square,
    S.mixedMetricResponseXY_eq_zero,
    hyx]
  simp
  exact mul_nonneg (sq_nonneg S.xAmplitude) (sq_nonneg S.yAmplitude)

end SquareOperatorialResponseContext

/--
One-channel regular-cone positivity for the `X` operatorial Hessian response.

This is the dimension-agnostic owner surface for the first constructive
operatorial Hessian closure: only the probed double-transport Hessian in the
`X` channel must live in the regular Drazin/Krein cone.  No finite matrix, no
two-channel determinant bound, and no scalar PSD packet is assumed.
-/
@[rep_depth transport]
structure RegularConeXResponseContext where
  c : CertifiedModularReduction (E := H₂)
  Hxx : EndH
  Hxx_mem : Hxx ∈ regularPositiveConeOmegaD c
  probe_nonneg_on_regular :
    ∀ H : EndH, H ∈ regularPositiveConeOmegaD c → 0 ≤ C.P.probe H
  diagonalMetricResponse_eq_probe_Hxx :
    C.diagonalMetricResponse = C.P.probe Hxx

namespace RegularConeXResponseContext

variable {C}

/-- The `X` diagonal response is nonnegative by regular-cone positivity. -/
@[rep_depth transport]
theorem diagonalMetricResponse_nonneg
    (R : RegularConeXResponseContext C) :
    0 ≤ C.diagonalMetricResponse := by
  rw [RegularConeXResponseContext.diagonalMetricResponse_eq_probe_Hxx R]
  exact RegularConeXResponseContext.probe_nonneg_on_regular R
    (RegularConeXResponseContext.Hxx R)
    (RegularConeXResponseContext.Hxx_mem R)

end RegularConeXResponseContext

/--
Noncommutative-operator positivity context for the two-channel response packet.

The positive objects live in the regular Drazin/Krein operator cone `Ω_D`; the
probe is required to be positive on that cone.  This avoids finite-state or
diagonal-count positivity and keeps the closure in the operator algebra
`EndH`.
-/
@[rep_depth transport]
structure RegularConeOperatorialResponseContext where
  c : CertifiedModularReduction (E := H₂)
  Hxx : EndH
  Hyy : EndH
  Hxx_mem : Hxx ∈ regularPositiveConeOmegaD c
  Hyy_mem : Hyy ∈ regularPositiveConeOmegaD c
  probe_nonneg_on_regular :
    ∀ H : EndH, H ∈ regularPositiveConeOmegaD c → 0 ≤ C.P.probe H
  diagonalMetricResponse_eq_probe_Hxx :
    C.diagonalMetricResponse = C.P.probe Hxx
  yDiagonalMetricResponse_eq_probe_Hyy :
    C.yDiagonalMetricResponse = C.P.probe Hyy
  mixed_determinant_nonneg :
    0 ≤ C.diagonalMetricResponse * C.yDiagonalMetricResponse
      - C.mixedMetricResponseXY * C.mixedMetricResponseYX

namespace RegularConeOperatorialResponseContext

variable {C}

/-- The `X` diagonal response is nonnegative by regular-cone positivity. -/
@[rep_depth transport]
theorem diagonalMetricResponse_nonneg
    (R : RegularConeOperatorialResponseContext C) :
    0 ≤ C.diagonalMetricResponse := by
  rw [RegularConeOperatorialResponseContext.diagonalMetricResponse_eq_probe_Hxx R]
  exact RegularConeOperatorialResponseContext.probe_nonneg_on_regular R
    (RegularConeOperatorialResponseContext.Hxx R)
    (RegularConeOperatorialResponseContext.Hxx_mem R)

/-- The `Y` diagonal response is nonnegative by regular-cone positivity. -/
@[rep_depth transport]
theorem yDiagonalMetricResponse_nonneg
    (R : RegularConeOperatorialResponseContext C) :
    0 ≤ C.yDiagonalMetricResponse := by
  rw [RegularConeOperatorialResponseContext.yDiagonalMetricResponse_eq_probe_Hyy R]
  exact RegularConeOperatorialResponseContext.probe_nonneg_on_regular R
    (RegularConeOperatorialResponseContext.Hyy R)
    (RegularConeOperatorialResponseContext.Hyy_mem R)

/-- A regular-cone operator context supplies the scalar PSD packet required downstream. -/
@[rep_depth transport]
theorem operatorialMetricResponsePSD
    (R : RegularConeOperatorialResponseContext C) :
    C.OperatorialMetricResponsePSD :=
  ⟨diagonalMetricResponse_nonneg R,
    yDiagonalMetricResponse_nonneg R,
    RegularConeOperatorialResponseContext.mixed_determinant_nonneg R⟩

end RegularConeOperatorialResponseContext

/--
Operatorial Cramer-Rao realization of the two-channel response packet.

This replaces the explicit determinant hypothesis by identifying the probed
Souriau/Onsager responses with the owned comparison-state channel metric.  The
mixed determinant then follows from the repo-native noncommutative
Cauchy-Schwarz theorem
`comparisonStateGeneratorMetric_sq_le`, without a finite response matrix.
-/
@[rep_depth transport]
structure CramerRaoOperatorialResponseContext where
  diagonalMetricResponse_eq_comparisonMetric :
    C.diagonalMetricResponse =
      comparisonStateGeneratorMetric (E := E) C.comparison C.X C.X
  yDiagonalMetricResponse_eq_comparisonMetric :
    C.yDiagonalMetricResponse =
      comparisonStateGeneratorMetric (E := E) C.comparison C.Y C.Y
  mixedMetricResponseXY_eq_comparisonMetric :
    C.mixedMetricResponseXY =
      comparisonStateGeneratorMetric (E := E) C.comparison C.X C.Y

namespace CramerRaoOperatorialResponseContext

variable {C}

/-- The `X` diagonal response is nonnegative by the channel-metric norm square. -/
@[rep_depth transport]
theorem diagonalMetricResponse_nonneg
    (R : CramerRaoOperatorialResponseContext C) :
    0 ≤ C.diagonalMetricResponse := by
  rw [CramerRaoOperatorialResponseContext.diagonalMetricResponse_eq_comparisonMetric R]
  exact comparisonStateGeneratorMetric_self_nonneg (E := E) C.comparison C.X

/-- The `Y` diagonal response is nonnegative by the channel-metric norm square. -/
@[rep_depth transport]
theorem yDiagonalMetricResponse_nonneg
    (R : CramerRaoOperatorialResponseContext C) :
    0 ≤ C.yDiagonalMetricResponse := by
  rw [CramerRaoOperatorialResponseContext.yDiagonalMetricResponse_eq_comparisonMetric R]
  exact comparisonStateGeneratorMetric_self_nonneg (E := E) C.comparison C.Y

/--
The mixed determinant is constructive: it is exactly Cauchy-Schwarz for the
comparison-state channel metric on the infinite doubled Krein carrier.
-/
@[rep_depth transport]
theorem mixed_determinant_nonneg
    (R : CramerRaoOperatorialResponseContext C) :
    0 ≤ C.diagonalMetricResponse * C.yDiagonalMetricResponse
      - C.mixedMetricResponseXY * C.mixedMetricResponseYX := by
  have hCS :=
    comparisonStateGeneratorMetric_sq_le (E := E) C.comparison C.X C.Y
  have hyx : C.mixedMetricResponseYX = C.mixedMetricResponseXY :=
    C.mixedMetricResponse_symm.symm
  rw [hyx]
  rw [CramerRaoOperatorialResponseContext.diagonalMetricResponse_eq_comparisonMetric R,
    CramerRaoOperatorialResponseContext.yDiagonalMetricResponse_eq_comparisonMetric R,
    CramerRaoOperatorialResponseContext.mixedMetricResponseXY_eq_comparisonMetric R]
  exact sub_nonneg.mpr (by simpa [pow_two] using hCS)

/-- The Cramer-Rao realization constructs the downstream scalar PSD packet. -/
@[rep_depth transport]
theorem operatorialMetricResponsePSD
    (R : CramerRaoOperatorialResponseContext C) :
    C.OperatorialMetricResponsePSD :=
  ⟨diagonalMetricResponse_nonneg R,
    yDiagonalMetricResponse_nonneg R,
    mixed_determinant_nonneg R⟩

end CramerRaoOperatorialResponseContext

/--
Operatorial Krein/Onsager second-law gate: a symmetric positive-semidefinite
two-channel Hessian packet has nonnegative entropy production.
-/
@[rep_depth transport]
theorem operatorialEntropyProduction_nonneg_of_metricResponsePSD
    (hPSD : C.OperatorialMetricResponsePSD)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialEntropyProduction xForce yForce := by
  rcases hPSD with ⟨hXX, hYY, hdet⟩
  have hdetSym :
      0 ≤ C.diagonalMetricResponse * C.yDiagonalMetricResponse
        - C.mixedMetricResponseXY ^ (2 : ℕ) := by
    have hyx : C.mixedMetricResponseYX = C.mixedMetricResponseXY :=
      C.mixedMetricResponse_symm.symm
    rw [hyx] at hdet
    simpa [pow_two] using hdet
  by_cases hXX_zero : C.diagonalMetricResponse = 0
  · have hxy_sq_nonpos : C.mixedMetricResponseXY ^ (2 : ℕ) ≤ 0 := by
      nlinarith
    have hxy_sq_zero : C.mixedMetricResponseXY ^ (2 : ℕ) = 0 :=
      le_antisymm hxy_sq_nonpos (sq_nonneg C.mixedMetricResponseXY)
    have hxy_zero : C.mixedMetricResponseXY = 0 :=
      sq_eq_zero_iff.mp hxy_sq_zero
    rw [operatorialEntropyProduction_eq_quadratic,
      hXX_zero, hxy_zero]
    nlinarith [sq_nonneg yForce, hYY]
  · have hXX_pos : 0 < C.diagonalMetricResponse :=
      lt_of_le_of_ne hXX (Ne.symm hXX_zero)
    have hnum_nonneg :
        0 ≤ (C.diagonalMetricResponse * xForce
              + C.mixedMetricResponseXY * yForce) ^ (2 : ℕ)
          +
            (C.diagonalMetricResponse * C.yDiagonalMetricResponse
              - C.mixedMetricResponseXY ^ (2 : ℕ))
              * yForce ^ (2 : ℕ) :=
      add_nonneg (sq_nonneg _)
        (mul_nonneg hdetSym (sq_nonneg yForce))
    have hquad :
        C.operatorialEntropyProduction xForce yForce =
          ((C.diagonalMetricResponse * xForce
              + C.mixedMetricResponseXY * yForce) ^ (2 : ℕ)
            +
              (C.diagonalMetricResponse * C.yDiagonalMetricResponse
                - C.mixedMetricResponseXY ^ (2 : ℕ))
                * yForce ^ (2 : ℕ))
            / C.diagonalMetricResponse := by
      rw [operatorialEntropyProduction_eq_quadratic]
      field_simp [hXX_zero]
      ring
    rw [hquad]
    exact div_nonneg hnum_nonneg hXX

/--
NCG/Krein second-law gate: regular-cone operator positivity plus the mixed
determinant bound gives nonnegative operatorial entropy production.
-/
@[rep_depth transport]
theorem operatorialEntropyProduction_nonneg_of_regularCone
    (R : RegularConeOperatorialResponseContext C)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialEntropyProduction xForce yForce :=
  C.operatorialEntropyProduction_nonneg_of_metricResponsePSD
    (RegularConeOperatorialResponseContext.operatorialMetricResponsePSD R)
    xForce yForce

/--
Square-response operatorial second-law gate.  This proves nonnegative entropy
production from square diagonal responses and orthogonal mixed response, rather
than assuming a PSD packet directly.
-/
@[rep_depth transport]
theorem operatorialEntropyProduction_nonneg_of_squareResponse
    (S : SquareOperatorialResponseContext C)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialEntropyProduction xForce yForce :=
  C.operatorialEntropyProduction_nonneg_of_metricResponsePSD
    (SquareOperatorialResponseContext.operatorialMetricResponsePSD S)
    xForce yForce

/--
Cramer-Rao operatorial second-law gate.  The two-channel determinant required
by the quadratic form is derived from the comparison-state channel
Cauchy-Schwarz theorem, not assumed as a scalar PSD hypothesis.
-/
@[rep_depth transport]
theorem operatorialEntropyProduction_nonneg_of_cramerRaoResponse
    (R : CramerRaoOperatorialResponseContext C)
    (xForce yForce : ℝ) :
    0 ≤ C.operatorialEntropyProduction xForce yForce :=
  C.operatorialEntropyProduction_nonneg_of_metricResponsePSD
    (CramerRaoOperatorialResponseContext.operatorialMetricResponsePSD R)
    xForce yForce

/--
One-channel operatorial entropy production is nonnegative when the diagonal
Souriau/Onsager response is realized by the owned Cramer-Rao channel metric.

This discharges the old `probe_hessian_nonneg` style wrapper for this concrete
operatorial context: the proof descends through the comparison-state
Cramer-Rao norm square on the infinite doubled carrier.
-/
@[rep_depth transport]
theorem canonicalEntropyProduction_nonneg_of_cramerRaoResponse
    (R : CramerRaoOperatorialResponseContext C) :
    0 ≤ InfoGeometry.Canonical.Operators.entropyProduction (E := E) C.P C.X C.A := by
  have hDiag : 0 ≤ C.diagonalMetricResponse :=
    CramerRaoOperatorialResponseContext.diagonalMetricResponse_nonneg R
  rw [diagonalMetricResponse, responseCoefficient, operatorMetricHessianForm_diag] at hDiag
  simpa [InfoGeometry.Canonical.Operators.entropyProduction,
    InfoGeometry.Canonical.Operators.operatorFisherDiagonal] using hDiag

/--
One-channel operatorial second-law gate from the regular Drazin/Krein cone.

This is the direct operatorial-trunk version of the Souriau--Fisher--Onsager
docstring source: the diagonal Fisher/Onsager shadow is the probed
operatorial Hessian, and nonnegativity is produced by regular-cone positivity
rather than by a finite response matrix.
-/
@[rep_depth transport]
theorem canonicalEntropyProduction_nonneg_of_regularCone
    (R : RegularConeXResponseContext C) :
    0 ≤ InfoGeometry.Canonical.Operators.entropyProduction (E := E) C.P C.X C.A := by
  have hDiag : 0 ≤ C.diagonalMetricResponse :=
    RegularConeXResponseContext.diagonalMetricResponse_nonneg R
  rw [diagonalMetricResponse, responseCoefficient, operatorMetricHessianForm_diag] at hDiag
  simpa [InfoGeometry.Canonical.Operators.entropyProduction,
    InfoGeometry.Canonical.Operators.operatorFisherDiagonal] using hDiag

/--
Supergraded even/odd Onsager block packet on the operatorial carrier.

The `X` channel is read as the even/bosonic direction and the `Y` channel as
the odd/fermionic direction.  This is not a finite block matrix: the entries
are the operatorial response coefficients of arbitrary doubled-Krein
endomorphism channels.  Positivity is inherited from the Cramer-Rao
comparison-state Cauchy-Schwarz theorem.
-/
@[rep_depth transport]
theorem supergradedEvenOddOnsagerBlock_packet_of_cramerRaoResponse
    (R : CramerRaoOperatorialResponseContext C)
    (evenForce oddForce : ℝ) :
    C.mixedMetricResponseXY = C.mixedMetricResponseYX
      ∧ C.diagonalMetricResponse =
          comparisonStateGeneratorMetric (E := E) C.comparison C.X C.X
      ∧ C.yDiagonalMetricResponse =
          comparisonStateGeneratorMetric (E := E) C.comparison C.Y C.Y
      ∧ C.mixedMetricResponseXY =
          comparisonStateGeneratorMetric (E := E) C.comparison C.X C.Y
      ∧ C.operatorialEntropyProduction evenForce oddForce =
          C.diagonalMetricResponse * evenForce ^ (2 : ℕ)
            + 2 * C.mixedMetricResponseXY * evenForce * oddForce
              + C.yDiagonalMetricResponse * oddForce ^ (2 : ℕ)
      ∧ 0 ≤ C.operatorialEntropyProduction evenForce oddForce := by
  exact
    ⟨C.mixedMetricResponse_symm,
      R.diagonalMetricResponse_eq_comparisonMetric,
      R.yDiagonalMetricResponse_eq_comparisonMetric,
      R.mixedMetricResponseXY_eq_comparisonMetric,
      C.operatorialEntropyProduction_eq_quadratic evenForce oddForce,
      C.operatorialEntropyProduction_nonneg_of_cramerRaoResponse
        R evenForce oddForce⟩

/--
One-channel operatorial second-law gate on the doubled Krein carrier.

For a pure `X` force, the entropy production reduces to the diagonal Hessian
readout times `xForce^2`.  If that diagonal Hessian is a regular-cone positive
operator read by a positive probe, nonnegativity is constructive and does not
require a finite response matrix or a two-channel determinant hypothesis.
-/
@[rep_depth transport]
theorem operatorialEntropyProduction_xChannel_nonneg_of_regularCone
    (R : RegularConeXResponseContext C)
    (xForce : ℝ) :
    0 ≤ C.operatorialEntropyProduction xForce 0 := by
  rw [operatorialEntropyProduction_eq_quadratic]
  have hdiag : 0 ≤ C.diagonalMetricResponse :=
    RegularConeXResponseContext.diagonalMetricResponse_nonneg R
  have hx2 : 0 ≤ xForce ^ (2 : ℕ) := sq_nonneg xForce
  nlinarith

/-- The metric response is the symmetrized readout of the two ordered Lie Hessians. -/
@[rep_depth transport]
theorem metricResponse_eq_half_probe_observableLieHessian_add_swap :
    C.metricResponse =
      (2 : ℝ)⁻¹ *
        (C.P.probe (observableLieHessian (E := E) C.X C.Y C.A)
          + C.P.probe (observableLieHessian (E := E) C.Y C.X C.A)) := by
  simpa [metricResponse] using
    InfoGeometry.Canonical.OnsagerReciprocity.operatorMetricHessianForm_eq_half_probe_observableLieHessian_add_swap
      (E := E) C.P C.A C.X C.Y

/-- The diagonal metric response is the probed double transport commutator. -/
@[rep_depth transport]
theorem diagonalMetricResponse_eq_probe_double_transportCommutator :
    C.diagonalMetricResponse =
      C.P.probe
        (transportCommutator (E := E) C.X
          (transportCommutator (E := E) C.X C.A)) := by
  simpa [diagonalMetricResponse] using
    InfoGeometry.Canonical.OnsagerReciprocity.responseCoefficient_diag_eq_probe_double_transportCommutator
      (E := E) C.P C.X C.A

/-- The skew response changes sign under channel swap. -/
@[rep_depth transport]
theorem curvatureResponse_swap_neg :
    C.swappedCurvatureResponse = -C.curvatureResponse := by
  simpa [curvatureResponse, swappedCurvatureResponse] using
    curvatureCoefficient_swap_neg (E := E) C.P C.X C.Y C.A

/-- The skew response is the probe of the bracket-derivation channel. -/
@[rep_depth transport]
theorem curvatureResponse_eq_probe_bracketDerivation :
    C.curvatureResponse =
      C.P.probe
        (observableLieDerivation (E := E) ⁅C.X, C.Y⁆ C.A) := by
  simpa [curvatureResponse] using
    curvatureCoefficient_eq_probe_bracketDerivation (E := E) C.P C.X C.Y C.A

/--
J/Casimir sign rule: modular J-reflection flips the phase channel while
preserving the metric lane assumptions carried by `IsJInvariant`.
-/
@[rep_depth transport]
theorem jReflectedPhaseCorrelation_eq_neg :
    C.jReflectedPhaseCorrelation = -C.phaseCorrelation := by
  simpa [jReflectedPhaseCorrelation, phaseCorrelation] using
    InfoGeometry.Thermodynamics.hodge_star_executes_legendre_transform
      (E := E) C.reference C.comparison C.X C.Y C.X_jInvariant C.Y_jInvariant

/--
Weighted Weyl correction stays operatorial: the weighted dynamics is the
zero-weight dynamics plus the explicit phase-axis commutator correction.
-/
@[rep_depth transport]
theorem weightedDynamics_eq_zeroWeight_add_phaseAxisCommutator :
    C.weightedDynamics =
      C.zeroWeightDynamics + C.weightedPhaseAxisCommutator := by
  simpa [weightedDynamics, zeroWeightDynamics, weightedPhaseAxisCommutator] using
    densityWeightLiftedDynamics_eq_zeroWeight_add_weighted_phaseAxis_commutator
      (E := E) C.P C.ψ C.A C.weight

/--
The weighted Weyl dynamics is exactly the coordinate-free Lie derivation for
the density-weighted Souriau generator.
-/
@[rep_depth transport]
theorem weightedDynamics_eq_weylCovariantThermodynamicDerivation :
    C.weightedDynamics = C.weylCovariantThermodynamicDerivation := by
  simp [weightedDynamics, weylCovariantThermodynamicDerivation,
    densityWeightLiftedDynamics, observableLieDerivation_apply]

/--
Operational Weyl formula:

`D_w A = D_0 A + w [K_Weyl, A]`.

This is the coordinate-free replacement for a Weyl-covariant partial
derivative.  The proof is the existing weighted-generator split plus the
commutator/Lie-derivation identity.
-/
@[rep_depth transport]
theorem weylCovariantThermodynamicDerivation_eq_zeroWeight_add_phaseAxis :
    C.weylCovariantThermodynamicDerivation =
      C.zeroWeightThermodynamicDerivation
        + C.weight • C.phaseAxisThermodynamicDerivation := by
  rw [← C.weightedDynamics_eq_weylCovariantThermodynamicDerivation]
  rw [C.weightedDynamics_eq_zeroWeight_add_phaseAxisCommutator]
  simp [zeroWeightDynamics, weightedPhaseAxisCommutator,
    zeroWeightThermodynamicDerivation, phaseAxisThermodynamicDerivation,
    densityWeightLiftedDynamics, observableLieDerivation_apply]

/--
Coordinate-free two-operator Onsager packet.

This packages the operatorial two-channel response in derivation language:

* the metric lane is the symmetrized probe of the nested Lie derivation;
* the skew lane is the probe of the bracket derivation;
* the Weyl-covariant thermodynamic derivation splits into zero-weight and
  phase-axis derivations.

No coordinate derivative is used here.  The operators live on the doubled
Krein carrier `EndH`.
-/
@[rep_depth transport]
theorem operatorialTwoOperatorOnsagerDerivation_packet
    (xForce yForce : ℝ) :
    C.metricResponse =
      (2 : ℝ)⁻¹ *
        (C.P.probe (observableLieHessian (E := E) C.X C.Y C.A)
          + C.P.probe (observableLieHessian (E := E) C.Y C.X C.A))
      ∧ C.curvatureResponse =
        C.P.probe
          (observableLieDerivation (E := E) ⁅C.X, C.Y⁆ C.A)
      ∧ C.weylCovariantThermodynamicDerivation =
          C.zeroWeightThermodynamicDerivation
            + C.weight • C.phaseAxisThermodynamicDerivation
      ∧ C.operatorialEntropyProduction xForce yForce =
          C.diagonalMetricResponse * xForce ^ (2 : ℕ)
            + 2 * C.mixedMetricResponseXY * xForce * yForce
              + C.yDiagonalMetricResponse * yForce ^ (2 : ℕ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact C.metricResponse_eq_half_probe_observableLieHessian_add_swap
  · exact C.curvatureResponse_eq_probe_bracketDerivation
  · exact C.weylCovariantThermodynamicDerivation_eq_zeroWeight_add_phaseAxis
  · exact C.operatorialEntropyProduction_eq_quadratic xForce yForce

/--
Dilation/Goldstone-charge packet on the doubled real Krein carrier.

The theorem name is Goldstone-facing, but the formal content is deliberately
repo-native: density weight is the Weyl phase/dilation axis, the Weyl
thermodynamic derivation splits into zero-weight plus phase-axis derivation,
and the real doubled primitive supercharges close by the existing CAR/CCR
owners.  No scalar charge or finite surrogate is introduced here.
-/
@[rep_depth transport]
theorem operatorialDilationGoldstoneCharge_packet :
    densityWeightPhaseAxis (E := E) = dilationOperator (E := E)
      ∧ densityWeightLiftedTransportGenerator (E := E) C.P C.ψ C.weight =
          InfoGeometry.Canonical.ThermodynamicGenerator.souriauTemperatureVector
            (E := E) C.P C.ψ
            + C.weight • dilationOperator (E := E)
      ∧ C.weylCovariantThermodynamicDerivation =
          C.zeroWeightThermodynamicDerivation
            + C.weight • C.phaseAxisThermodynamicDerivation
      ∧ SuperchargeCARCCRBridge.cptSuperchargeOp (E := E) =
          dilationOperator (E := E)
      ∧ SuperchargeCARCCRBridge.CARBracket (E := E)
          (SuperchargeCARCCRBridge.paritySuperchargeOp (E := E))
          (SuperchargeCARCCRBridge.modularSuperchargeOp (E := E))
        = 0
      ∧ SuperchargeCARCCRBridge.CCRBracket (E := E)
          (SuperchargeCARCCRBridge.paritySuperchargeOp (E := E))
          (SuperchargeCARCCRBridge.modularSuperchargeOp (E := E))
        = (2 : ℝ) • SuperchargeCARCCRBridge.cptSuperchargeOp (E := E) := by
  exact
    ⟨densityWeightPhaseAxis_eq_dilationOperator (E := E),
      densityWeightLiftedTransportGenerator_eq_souriau_add_weighted_dilation
        (E := E) C.P C.ψ C.weight,
      C.weylCovariantThermodynamicDerivation_eq_zeroWeight_add_phaseAxis,
      SuperchargeCARCCRBridge.cptSuperchargeOp_eq_dilationOperator (E := E),
      SuperchargeCARCCRBridge.parity_modular_supercharge_car_zero (E := E),
      SuperchargeCARCCRBridge.parity_modular_supercharge_ccrBracket_eq_two_cpt (E := E)⟩

attribute [terminal] operatorialDilationGoldstoneCharge_packet

/--
Supergraded operatorial Fisher/Onsager block packet on the real doubled carrier.

The two response channels `X` and `Y` are the abstract even/odd block labels of
the operatorial Hessian.  Positivity is not assumed as a bare PSD hypothesis:
it is constructed from a square-response witness.  Fermionic/odd closure is
kept in the existing CAR owner and included as a separate proof component.

This is dimension-agnostic: the carrier `E` is arbitrary, and all dynamics live
in `EndH := DoubledSpace E →L[ℝ] DoubledSpace E`.
-/
@[rep_depth transport]
theorem supergradedFisherOnsagerBlock_squareResponse_CAR_packet
    (S : SquareOperatorialResponseContext C)
    (evenForce oddForce : ℝ) :
    C.metricResponse =
        (2 : ℝ)⁻¹ *
          (C.P.probe (observableLieHessian (E := E) C.X C.Y C.A)
            + C.P.probe (observableLieHessian (E := E) C.Y C.X C.A))
      ∧ C.diagonalMetricResponse =
        C.P.probe
          (transportCommutator (E := E) C.X
            (transportCommutator (E := E) C.X C.A))
      ∧ C.weylCovariantThermodynamicDerivation =
        C.zeroWeightThermodynamicDerivation
          + C.weight • C.phaseAxisThermodynamicDerivation
      ∧ C.operatorialEntropyProduction evenForce oddForce =
        C.diagonalMetricResponse * evenForce ^ (2 : ℕ)
          + 2 * C.mixedMetricResponseXY * evenForce * oddForce
            + C.yDiagonalMetricResponse * oddForce ^ (2 : ℕ)
      ∧ C.diagonalMetricResponse = S.xAmplitude ^ (2 : ℕ)
      ∧ C.yDiagonalMetricResponse = S.yAmplitude ^ (2 : ℕ)
      ∧ C.mixedMetricResponseXY = 0
      ∧ 0 ≤ C.operatorialEntropyProduction evenForce oddForce
      ∧ SuperchargeCARCCRBridge.CARBracket (E := E)
          (SuperchargeCARCCRBridge.paritySuperchargeOp (E := E))
          (SuperchargeCARCCRBridge.modularSuperchargeOp (E := E))
        = 0
      ∧ SuperchargeCARCCRBridge.CCRBracket (E := E)
          (SuperchargeCARCCRBridge.paritySuperchargeOp (E := E))
          (SuperchargeCARCCRBridge.modularSuperchargeOp (E := E))
        = (2 : ℝ) • SuperchargeCARCCRBridge.cptSuperchargeOp (E := E) := by
  rcases SuperchargeCARCCRBridge.harmonic_oscillator_spine (E := E) with
    ⟨hCAR, hCCR, _⟩
  exact
    ⟨C.metricResponse_eq_half_probe_observableLieHessian_add_swap,
      C.diagonalMetricResponse_eq_probe_double_transportCommutator,
      C.weylCovariantThermodynamicDerivation_eq_zeroWeight_add_phaseAxis,
      C.operatorialEntropyProduction_eq_quadratic evenForce oddForce,
      S.diagonalMetricResponse_eq_square,
      S.yDiagonalMetricResponse_eq_square,
      S.mixedMetricResponseXY_eq_zero,
      C.operatorialEntropyProduction_nonneg_of_squareResponse S evenForce oddForce,
      hCAR,
      hCCR⟩

/--
Supergraded operatorial Fisher/Onsager block packet from the regular
Drazin/Krein cone lane.

This removes the old bare positivity route on the two-channel operatorial block:
nonnegativity now descends from explicit regular-cone witnesses for both
operatorial Hessian channels together with the mixed-determinant witness already
carried by `RegularConeOperatorialResponseContext`.
-/
@[rep_depth transport]
theorem supergradedFisherOnsagerBlock_regularCone_CAR_packet
    (R : RegularConeOperatorialResponseContext C)
    (evenForce oddForce : ℝ) :
    C.metricResponse =
        (2 : ℝ)⁻¹ *
          (C.P.probe (observableLieHessian (E := E) C.X C.Y C.A)
            + C.P.probe (observableLieHessian (E := E) C.Y C.X C.A))
      ∧ C.diagonalMetricResponse = C.P.probe R.Hxx
      ∧ C.yDiagonalMetricResponse = C.P.probe R.Hyy
      ∧ C.weylCovariantThermodynamicDerivation =
        C.zeroWeightThermodynamicDerivation
          + C.weight • C.phaseAxisThermodynamicDerivation
      ∧ C.operatorialEntropyProduction evenForce oddForce =
        C.diagonalMetricResponse * evenForce ^ (2 : ℕ)
          + 2 * C.mixedMetricResponseXY * evenForce * oddForce
            + C.yDiagonalMetricResponse * oddForce ^ (2 : ℕ)
      ∧ 0 ≤ C.operatorialEntropyProduction evenForce oddForce
      ∧ SuperchargeCARCCRBridge.CARBracket (E := E)
          (SuperchargeCARCCRBridge.paritySuperchargeOp (E := E))
          (SuperchargeCARCCRBridge.modularSuperchargeOp (E := E))
        = 0
      ∧ SuperchargeCARCCRBridge.CCRBracket (E := E)
          (SuperchargeCARCCRBridge.paritySuperchargeOp (E := E))
          (SuperchargeCARCCRBridge.modularSuperchargeOp (E := E))
        = (2 : ℝ) • SuperchargeCARCCRBridge.cptSuperchargeOp (E := E) := by
  rcases SuperchargeCARCCRBridge.harmonic_oscillator_spine (E := E) with
    ⟨hCAR, hCCR, _⟩
  exact
    ⟨C.metricResponse_eq_half_probe_observableLieHessian_add_swap,
      R.diagonalMetricResponse_eq_probe_Hxx,
      R.yDiagonalMetricResponse_eq_probe_Hyy,
      C.weylCovariantThermodynamicDerivation_eq_zeroWeight_add_phaseAxis,
      C.operatorialEntropyProduction_eq_quadratic evenForce oddForce,
      C.operatorialEntropyProduction_nonneg_of_regularCone R evenForce oddForce,
      hCAR,
      hCCR⟩

/--
Supergraded operatorial Fisher/Onsager block packet from the Cramer-Rao owner lane.

This is the companion to the square-response packet above, but it no longer
requires orthogonal mixed response or explicit square-amplitude witnesses.  The
positivity component is discharged by the comparison-state Cauchy-Schwarz
owner theorem through `CramerRaoOperatorialResponseContext`.
-/
@[rep_depth transport]
theorem supergradedFisherOnsagerBlock_cramerRaoResponse_CAR_packet
    (R : CramerRaoOperatorialResponseContext C)
    (evenForce oddForce : ℝ) :
    C.metricResponse =
        (2 : ℝ)⁻¹ *
          (C.P.probe (observableLieHessian (E := E) C.X C.Y C.A)
            + C.P.probe (observableLieHessian (E := E) C.Y C.X C.A))
      ∧ C.diagonalMetricResponse =
        comparisonStateGeneratorMetric (E := E) C.comparison C.X C.X
      ∧ C.yDiagonalMetricResponse =
        comparisonStateGeneratorMetric (E := E) C.comparison C.Y C.Y
      ∧ C.mixedMetricResponseXY =
        comparisonStateGeneratorMetric (E := E) C.comparison C.X C.Y
      ∧ C.weylCovariantThermodynamicDerivation =
        C.zeroWeightThermodynamicDerivation
          + C.weight • C.phaseAxisThermodynamicDerivation
      ∧ C.operatorialEntropyProduction evenForce oddForce =
        C.diagonalMetricResponse * evenForce ^ (2 : ℕ)
          + 2 * C.mixedMetricResponseXY * evenForce * oddForce
            + C.yDiagonalMetricResponse * oddForce ^ (2 : ℕ)
      ∧ 0 ≤ C.operatorialEntropyProduction evenForce oddForce
      ∧ SuperchargeCARCCRBridge.CARBracket (E := E)
          (SuperchargeCARCCRBridge.paritySuperchargeOp (E := E))
          (SuperchargeCARCCRBridge.modularSuperchargeOp (E := E))
        = 0
      ∧ SuperchargeCARCCRBridge.CCRBracket (E := E)
          (SuperchargeCARCCRBridge.paritySuperchargeOp (E := E))
          (SuperchargeCARCCRBridge.modularSuperchargeOp (E := E))
        = (2 : ℝ) • SuperchargeCARCCRBridge.cptSuperchargeOp (E := E) := by
  rcases SuperchargeCARCCRBridge.harmonic_oscillator_spine (E := E) with
    ⟨hCAR, hCCR, _⟩
  exact
    ⟨C.metricResponse_eq_half_probe_observableLieHessian_add_swap,
      R.diagonalMetricResponse_eq_comparisonMetric,
      R.yDiagonalMetricResponse_eq_comparisonMetric,
      R.mixedMetricResponseXY_eq_comparisonMetric,
      C.weylCovariantThermodynamicDerivation_eq_zeroWeight_add_phaseAxis,
      C.operatorialEntropyProduction_eq_quadratic evenForce oddForce,
      C.operatorialEntropyProduction_nonneg_of_cramerRaoResponse R evenForce oddForce,
      hCAR,
      hCCR⟩

attribute [terminal] supergradedFisherOnsagerBlock_squareResponse_CAR_packet
attribute [terminal] supergradedFisherOnsagerBlock_cramerRaoResponse_CAR_packet

end OperatorialMetriplecticContext

end Core

end InfoGeometry.Canonical.SouriauKreinMetriplectic
