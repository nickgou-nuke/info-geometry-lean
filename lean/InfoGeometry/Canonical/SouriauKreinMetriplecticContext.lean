import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Canonical.OperatorFenchelRegularCone
import InfoGeometry.Canonical.WeightedWeylNormalizationBridge
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

/-- The metric response is the symmetrized readout of the two ordered Lie Hessians. -/
@[rep_depth transport]
theorem metricResponse_eq_half_probe_observableLieHessian_add_swap :
    C.metricResponse =
      (2 : ℝ)⁻¹ *
        (C.P.probe (observableLieHessian (E := E) C.X C.Y C.A)
          + C.P.probe (observableLieHessian (E := E) C.Y C.X C.A)) := by
  simpa [metricResponse] using
    operatorMetricHessianForm_eq_half_probe_observableLieHessian_add_swap
      (E := E) C.P C.A C.X C.Y

/-- The diagonal metric response is the probed double transport commutator. -/
@[rep_depth transport]
theorem diagonalMetricResponse_eq_probe_double_transportCommutator :
    C.diagonalMetricResponse =
      C.P.probe
        (transportCommutator (E := E) C.X
          (transportCommutator (E := E) C.X C.A)) := by
  simpa [diagonalMetricResponse] using
    responseCoefficient_diag_eq_probe_double_transportCommutator
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

end OperatorialMetriplecticContext

end Core

end InfoGeometry.Canonical.SouriauKreinMetriplectic
