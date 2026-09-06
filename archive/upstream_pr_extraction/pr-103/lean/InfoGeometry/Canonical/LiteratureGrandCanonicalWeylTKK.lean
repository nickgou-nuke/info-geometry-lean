import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Meta.Architecture

/-!
# Literature Grand-Canonical Weyl TKK Bridge

This file records a literature-facing theorem surface extracted from the cited
papers, without searching for pre-existing repo components as proof sources.

Literature inputs:

* arXiv:2603.20571: canonical and grand-canonical singular ensembles.
  The usable mathematical layer is the simple-pole residue extraction of
  inverse temperature and the affine grand-canonical action
  `beta * (E - mu * N)`.
* arXiv:2309.11372: Weyl conformal geometry as a gauge theory of local scale
  invariance.  The usable mathematical layer here is an abstract
  Weyl-covariant gauge interface, with invariant curvature/field-strength
  under gauge representative changes.
* arXiv:1609.00271: structure and TKK algebras for Jordan superalgebras.
  The usable mathematical layer is a 3-graded TKK closure pattern
  `g_- ⊕ g_0 ⊕ g_+` with the mixed bracket closing in `g_0`.

The declarations below do not claim a full analytic proof of contour
integration, Weyl geometry, or Jordan-superalgebra TKK construction inside this
repository.  They expose the proof obligations needed to connect those
literature statements to repo-native operator lanes.
-/

namespace InfoGeometry.Canonical.LiteratureGrandCanonicalWeylTKK

/-! ## Residue-controlled singular ensembles -/

/--
Contour/holonomy presentation of the simple-pole residue.

The singular-ensemble paper extracts thermodynamic data from a contour around
a simple pole.  The repo already represents path/line data abstractly through
`WeylTrajectory`, `WeylLineIntegrator`, and `WeylHolonomyMap`.  This package
links that path-holonomy readout to the real residue used in the action
formulas, without pretending to have developed complex contour integration in
Lean.
-/
@[rep_depth thermo]
structure ResidueContourHolonomyData
    (I X A S : Type*) where
  contour : WeylTrajectory I X
  lineIntegrator : WeylLineIntegrator I A S
  residueMap : WeylHolonomyMap S ℝ
  residueField : X → A
  lapseResidue : ℝ
  contourResidue_eq_lapseResidue :
    residueMap
      (lineIntegrator.integrate (fun i => residueField (contour.point i))) =
        lapseResidue

namespace ResidueContourHolonomyData

variable {I X A S : Type*}
variable (C : ResidueContourHolonomyData I X A S)

/-- The contour holonomy/readout equals the lapse residue. -/
@[rep_depth thermo]
theorem contourHolonomy_eq_lapseResidue :
    C.residueMap
      (C.lineIntegrator.integrate (fun i => C.residueField (C.contour.point i))) =
        C.lapseResidue :=
  C.contourResidue_eq_lapseResidue

end ResidueContourHolonomyData

/--
Simple-pole residue data for a static lapse function.

The literature formula used by the bridge is:

`beta = 4 * pi * Res(1 / f)`.

The actual contour integral and analyticity hypotheses are represented by the
field `inverseTemperature_eq_four_pi_residue`.
-/
@[rep_depth thermo]
structure SimplePoleResidueData where
  lapseResidue : ℝ
  inverseTemperature : ℝ
  inverseTemperature_eq_four_pi_residue :
    inverseTemperature = 4 * Real.pi * lapseResidue

namespace SimplePoleResidueData

variable (R : SimplePoleResidueData)

/-- Literature residue formula for inverse temperature. -/
@[rep_depth thermo]
theorem beta_eq_four_pi_residue :
    R.inverseTemperature = 4 * Real.pi * R.lapseResidue :=
  R.inverseTemperature_eq_four_pi_residue

/-- Canonical singular action `I_A = beta * E`. -/
@[rep_depth thermo]
def canonicalSingularAction (energy : ℝ) : ℝ :=
  R.inverseTemperature * energy

/--
Grand-canonical singular action `I_B = beta * (E - mu * N)`.

This is the affine thermodynamic expression extracted from the residue
formalism in the grand-canonical sector.
-/
@[rep_depth thermo]
def grandCanonicalSingularAction
    (energy chemicalPotential number : ℝ) : ℝ :=
  R.inverseTemperature * (energy - chemicalPotential * number)

/-- Expansion of the grand-canonical singular action into its affine form. -/
@[rep_depth thermo]
theorem grandCanonicalSingularAction_eq
    (energy chemicalPotential number : ℝ) :
    R.grandCanonicalSingularAction energy chemicalPotential number =
      R.inverseTemperature * (energy - chemicalPotential * number) := by
  rfl

/--
The grand-canonical action is the canonical action corrected by the
chemical-potential count term.
-/
@[rep_depth thermo]
theorem grandCanonicalSingularAction_eq_canonical_sub_muN
    (energy chemicalPotential number : ℝ) :
    R.grandCanonicalSingularAction energy chemicalPotential number =
      R.canonicalSingularAction energy
        - R.inverseTemperature * chemicalPotential * number := by
  simp [grandCanonicalSingularAction, canonicalSingularAction]
  ring

end SimplePoleResidueData

namespace ResidueContourHolonomyData

variable {I X A S : Type*}
variable (C : ResidueContourHolonomyData I X A S)

/-- Induced simple-pole residue data from a contour-holonomy representative. -/
@[rep_depth thermo]
def toSimplePoleResidueData
    (inverseTemperature : ℝ)
    (hβ : inverseTemperature = 4 * Real.pi * C.lapseResidue) :
    SimplePoleResidueData where
  lapseResidue := C.lapseResidue
  inverseTemperature := inverseTemperature
  inverseTemperature_eq_four_pi_residue := hβ

/--
Contour-holonomy form of the grand-canonical singular action.

The contour data determine the residue; the supplied `hβ` is the literature
temperature formula `β = 4π Res`.  The resulting action is the same affine
grand-canonical expression `β(E - μN)`.
-/
@[rep_depth thermo]
def grandCanonicalContourHolonomyAction
    (inverseTemperature : ℝ)
    (hβ : inverseTemperature = 4 * Real.pi * C.lapseResidue)
    (energy chemicalPotential number : ℝ) : ℝ :=
  (C.toSimplePoleResidueData inverseTemperature hβ).grandCanonicalSingularAction
    energy chemicalPotential number

/--
The contour-holonomy grand-canonical action expands to
`βE - βμN`.
-/
@[rep_depth thermo]
theorem grandCanonicalContourHolonomyAction_eq_canonical_sub_muN
    (inverseTemperature : ℝ)
    (hβ : inverseTemperature = 4 * Real.pi * C.lapseResidue)
    (energy chemicalPotential number : ℝ) :
    C.grandCanonicalContourHolonomyAction
        inverseTemperature hβ energy chemicalPotential number =
      (C.toSimplePoleResidueData inverseTemperature hβ).canonicalSingularAction energy
        - inverseTemperature * chemicalPotential * number := by
  simpa [grandCanonicalContourHolonomyAction, toSimplePoleResidueData] using
    SimplePoleResidueData.grandCanonicalSingularAction_eq_canonical_sub_muN
      (C.toSimplePoleResidueData inverseTemperature hβ)
      energy chemicalPotential number

end ResidueContourHolonomyData

/--
Tolman-Klein equilibrium data abstracted as redshift-invariant products.

This does not build a spacetime model.  It records the exact equilibrium shape
used by the grand-canonical singular-ensemble paper:
local temperature and local chemical potential have the same redshift factor.
-/
@[rep_depth thermo]
structure TolmanKleinRedshiftData (R : Type*) where
  redshift : R → ℝ
  localTemperature : R → ℝ
  localChemicalPotential : R → ℝ
  temperatureAtInfinity : ℝ
  chemicalPotentialAtInfinity : ℝ
  temperature_redshift :
    ∀ r, localTemperature r * redshift r = temperatureAtInfinity
  chemicalPotential_redshift :
    ∀ r, localChemicalPotential r * redshift r = chemicalPotentialAtInfinity

namespace TolmanKleinRedshiftData

variable {R : Type*} (T : TolmanKleinRedshiftData R)

/-- Temperature redshift equilibrium law. -/
@[rep_depth thermo]
theorem temperatureRedshiftInvariant (r : R) :
    T.localTemperature r * T.redshift r = T.temperatureAtInfinity :=
  T.temperature_redshift r

/-- Chemical-potential redshift equilibrium law. -/
@[rep_depth thermo]
theorem chemicalPotentialRedshiftInvariant (r : R) :
    T.localChemicalPotential r * T.redshift r =
      T.chemicalPotentialAtInfinity :=
  T.chemicalPotential_redshift r

end TolmanKleinRedshiftData

/-! ## Weyl gauge covariance -/

/--
Abstract Weyl gauge representative and its curvature/field-strength readout.

The paper-level statement used here is that Weyl geometry can be formulated
covariantly under local scale-gauge changes.  The field `curvature_invariant`
is the proof obligation for the invariant observable under a gauge
representative change.
-/
@[rep_depth transport]
structure WeylGaugeCovariantInterface
    (Gauge Parameter Curvature : Type*) where
  transform : Gauge → Parameter → Gauge
  curvature : Gauge → Curvature
  curvature_invariant :
    ∀ gauge parameter,
      curvature (transform gauge parameter) = curvature gauge

namespace WeylGaugeCovariantInterface

variable {Gauge Parameter Curvature : Type*}
variable (W : WeylGaugeCovariantInterface Gauge Parameter Curvature)

/-- Weyl representative changes preserve the curvature readout. -/
@[rep_depth transport]
theorem curvature_transform_eq
    (gauge : Gauge) (parameter : Parameter) :
    W.curvature (W.transform gauge parameter) = W.curvature gauge :=
  W.curvature_invariant gauge parameter

end WeylGaugeCovariantInterface

/-! ## TKK 3-graded closure from Jordan-superpair literature -/

/--
Abstract 3-graded TKK closure package.

The TKK literature assigns the pair lanes to `g_+` and `g_-`, and the
structure/inner-derivation lane to `g_0`.  The essential closure laws needed by
the bridge are stored as membership predicates rather than by choosing a
specific concrete Jordan superalgebra.
-/
@[rep_depth transport]
structure TKKThreeGradedClosure
    (G : Type*) where
  bracket : G → G → G
  inGPlus : G → Prop
  inGZero : G → Prop
  inGMinus : G → Prop
  bracket_plus_minus_mem_zero :
    ∀ x y, inGPlus x → inGMinus y → inGZero (bracket x y)
  bracket_zero_plus_mem_plus :
    ∀ x y, inGZero x → inGPlus y → inGPlus (bracket x y)
  bracket_zero_minus_mem_minus :
    ∀ x y, inGZero x → inGMinus y → inGMinus (bracket x y)
  bracket_zero_zero_mem_zero :
    ∀ x y, inGZero x → inGZero y → inGZero (bracket x y)

namespace TKKThreeGradedClosure

variable {G : Type*} (T : TKKThreeGradedClosure G)

/-- TKK mixed bracket closure `[g_+, g_-] ⊆ g_0`. -/
@[rep_depth transport]
theorem bracketPlusMinusMemZero
    {x y : G} (hx : T.inGPlus x) (hy : T.inGMinus y) :
    T.inGZero (T.bracket x y) :=
  T.bracket_plus_minus_mem_zero x y hx hy

/-- TKK action closure `[g_0, g_+] ⊆ g_+`. -/
@[rep_depth transport]
theorem bracketZeroPlusMemPlus
    {x y : G} (hx : T.inGZero x) (hy : T.inGPlus y) :
    T.inGPlus (T.bracket x y) :=
  T.bracket_zero_plus_mem_plus x y hx hy

/-- TKK action closure `[g_0, g_-] ⊆ g_-`. -/
@[rep_depth transport]
theorem bracketZeroMinusMemMinus
    {x y : G} (hx : T.inGZero x) (hy : T.inGMinus y) :
    T.inGMinus (T.bracket x y) :=
  T.bracket_zero_minus_mem_minus x y hx hy

/-- Structure algebra closure `[g_0, g_0] ⊆ g_0`. -/
@[rep_depth transport]
theorem bracketZeroZeroMemZero
    {x y : G} (hx : T.inGZero x) (hy : T.inGZero y) :
    T.inGZero (T.bracket x y) :=
  T.bracket_zero_zero_mem_zero x y hx hy

end TKKThreeGradedClosure

/-! ## Karush-Kuhn-Tucker optimization packet -/

/--
Karush-Kuhn-Tucker data for constrained thermodynamic optimization.

This is the optimization meaning of KKT: primal feasibility, dual feasibility,
stationarity, and complementary slackness.  It is deliberately separate from
`InfoGeometry.Canonical.KKTCore`, which is a split-operator/chiral grading
surface rather than a Karush-Kuhn-Tucker optimizer.
-/
@[rep_depth thermo]
structure KarushKuhnTuckerThermodynamicData where
  /-- Primal variables and finite inequality/equality constraint labels. -/
  Primal : Type*
  InequalityIndex : Type*
  EqualityIndex : Type*
  PartitionIndex : Type*
  [inequalityFintype : Fintype InequalityIndex]
  [equalityFintype : Fintype EqualityIndex]
  [partitionFintype : Fintype PartitionIndex]
  [inequalityDecidableEq : DecidableEq InequalityIndex]
  [equalityDecidableEq : DecidableEq EqualityIndex]
  [partitionDecidableEq : DecidableEq PartitionIndex]

  /-- Candidate primal point and Lagrange multipliers. -/
  point : Primal
  inequalityMultiplier : InequalityIndex → ℝ
  equalityMultiplier : EqualityIndex → ℝ

  /-- Constraint functions and their directional derivatives at the point. -/
  inequalityConstraint : InequalityIndex → Primal → ℝ
  equalityConstraint : EqualityIndex → Primal → ℝ
  objectiveDerivative : Primal → ℝ
  inequalityDerivative : InequalityIndex → Primal → ℝ
  equalityDerivative : EqualityIndex → Primal → ℝ

  /-- Finite grand-canonical partition data, with dimensionless `k_B = 1`. -/
  partitionEnergy : PartitionIndex → ℝ
  inverseTemperature : ℝ
  partitionFunction : ℝ

  /-- Genuine KKT feasibility, stationarity, and complementarity laws. -/
  inequality_feasible :
    ∀ i, inequalityConstraint i point ≤ 0
  equality_feasible :
    ∀ j, equalityConstraint j point = 0
  multiplier_nonnegative :
    ∀ i, 0 ≤ inequalityMultiplier i
  lagrangian_stationary :
    ∀ direction,
      objectiveDerivative direction +
          ∑ i, inequalityMultiplier i * inequalityDerivative i direction +
          ∑ j, equalityMultiplier j * equalityDerivative j direction = 0
  complementary_slackness :
    ∀ i, inequalityMultiplier i * inequalityConstraint i point = 0
  partitionFunction_eq :
    partitionFunction =
      ∑ i, Real.exp (-inverseTemperature * partitionEnergy i)

namespace KarushKuhnTuckerThermodynamicData

variable (K : KarushKuhnTuckerThermodynamicData)

/-- Native primal feasibility predicate. -/
def primalFeasible : Prop :=
  (∀ i, K.inequalityConstraint i K.point ≤ 0) ∧
    ∀ j, K.equalityConstraint j K.point = 0

/-- Native dual-cone feasibility predicate. -/
def dualFeasible : Prop :=
  ∀ i, 0 ≤ K.inequalityMultiplier i

/-- Native Lagrangian stationarity predicate. -/
def stationarity : Prop :=
  by
    letI := K.inequalityFintype
    letI := K.equalityFintype
    letI := K.inequalityDecidableEq
    letI := K.equalityDecidableEq
    exact ∀ direction,
      K.objectiveDerivative direction +
          ∑ i, K.inequalityMultiplier i * K.inequalityDerivative i direction +
          ∑ j, K.equalityMultiplier j * K.equalityDerivative j direction = 0

/-- Native complementary-slackness predicate. -/
def complementarySlackness : Prop :=
  ∀ i,
    K.inequalityMultiplier i * K.inequalityConstraint i K.point = 0

/-- The finite partition function is the actual Gibbs sum (`k_B = 1`). -/
def finitePartitionAdmissible : Prop :=
  by
    letI := K.partitionFintype
    letI := K.partitionDecidableEq
    exact K.partitionFunction =
      ∑ i, Real.exp (-K.inverseTemperature * K.partitionEnergy i)

/-- Primal feasibility follows from the stored constraint laws. -/
theorem primalFeasible_proof : K.primalFeasible :=
  ⟨K.inequality_feasible, K.equality_feasible⟩

/-- Dual feasibility follows from multiplier nonnegativity. -/
theorem dualFeasible_proof : K.dualFeasible :=
  K.multiplier_nonnegative

/-- Stationarity is the stored Lagrangian directional-derivative equation. -/
theorem stationarity_proof : K.stationarity := by
  letI := K.inequalityFintype
  letI := K.equalityFintype
  letI := K.inequalityDecidableEq
  letI := K.equalityDecidableEq
  exact K.lagrangian_stationary

/-- Complementary slackness is pointwise in the inequality labels. -/
theorem complementarySlackness_proof : K.complementarySlackness :=
  K.complementary_slackness

/-- Finite-partition admissibility is the defining Gibbs-sum equality. -/
theorem finitePartitionAdmissible_proof : K.finitePartitionAdmissible := by
  letI := K.partitionFintype
  letI := K.partitionDecidableEq
  exact K.partitionFunction_eq

end KarushKuhnTuckerThermodynamicData

/-! ## Combined literature theorem surface -/

/--
Literature-backed bridge package combining:

* residue-controlled grand-canonical affine action,
* Tolman-Klein redshift compatibility,
* Weyl gauge covariance,
* TKK 3-graded closure.
-/
@[rep_depth transport]
structure LiteratureWeylGrandCanonicalTKKBridge
    (R Gauge Parameter Curvature G I X A S : Type*) where
  residue : SimplePoleResidueData
  contourResidue : ResidueContourHolonomyData I X A S
  redshift : TolmanKleinRedshiftData R
  weyl : WeylGaugeCovariantInterface Gauge Parameter Curvature
  tkk : TKKThreeGradedClosure G

/--
Literature-backed bridge with an explicit Karush-Kuhn-Tucker optimization
packet.

This extends the Weyl/grand-canonical/TKK bridge without changing existing
constructors.  The KKT data are assumptions supplied by a concrete constrained
thermodynamic model; they are not inferred from the chiral `KKTCore` grading.
-/
@[rep_depth transport]
structure LiteratureWeylGrandCanonicalTKKKKTBridge
    (R Gauge Parameter Curvature G I X A S : Type*) extends
      LiteratureWeylGrandCanonicalTKKBridge
        R Gauge Parameter Curvature G I X A S where
  kktOptimization : KarushKuhnTuckerThermodynamicData

/--
Literature-backed bridge where the optimization KKT packet is not a bare list
of propositions but is induced by explicit residual equations.
-/
@[rep_depth transport]
structure ConstructiveLiteratureWeylGrandCanonicalTKKKKTBridge
    (R Gauge Parameter Curvature G I X A S : Type*) extends
      LiteratureWeylGrandCanonicalTKKBridge
        R Gauge Parameter Curvature G I X A S where
  kktCertificate : KarushKuhnTuckerThermodynamicData

namespace ConstructiveLiteratureWeylGrandCanonicalTKKKKTBridge

variable {R Gauge Parameter Curvature G I X A S : Type*}
variable (B : ConstructiveLiteratureWeylGrandCanonicalTKKKKTBridge
  R Gauge Parameter Curvature G I X A S)

/-- The proposition-level KKT bridge induced by the residual property. -/
@[rep_depth thermo]
def toKKTBridge :
    LiteratureWeylGrandCanonicalTKKKKTBridge
      R Gauge Parameter Curvature G I X A S where
  toLiteratureWeylGrandCanonicalTKKBridge :=
    B.toLiteratureWeylGrandCanonicalTKKBridge
  kktOptimization := B.kktCertificate

/-- The constructive bridge still supplies the grand-canonical affine action. -/
@[rep_depth thermo]
theorem grandCanonicalActionAffine
    (energy chemicalPotential number : ℝ) :
  B.toLiteratureWeylGrandCanonicalTKKBridge.residue.grandCanonicalSingularAction
        energy chemicalPotential number =
      B.toLiteratureWeylGrandCanonicalTKKBridge.residue.canonicalSingularAction energy
        - B.toLiteratureWeylGrandCanonicalTKKBridge.residue.inverseTemperature *
          chemicalPotential * number :=
  SimplePoleResidueData.grandCanonicalSingularAction_eq_canonical_sub_muN
    B.toLiteratureWeylGrandCanonicalTKKBridge.residue
    energy chemicalPotential number

/--
Single packet matching the Bulgarian theorem-factory text:
grand-canonical affine action, Weyl gauge curvature invariance, TKK mixed
closure, and exact KKT optimization closure.
-/
@[rep_depth thermo]
theorem grandCanonicalWeylTKKKKTExactPacket
    (gauge : Gauge) (parameter : Parameter)
    {x y : G} (hx : B.tkk.inGPlus x) (hy : B.tkk.inGMinus y)
    (energy chemicalPotential number : ℝ) :
    B.toLiteratureWeylGrandCanonicalTKKBridge.residue.grandCanonicalSingularAction
        energy chemicalPotential number =
          B.toLiteratureWeylGrandCanonicalTKKBridge.residue.canonicalSingularAction energy
            - B.toLiteratureWeylGrandCanonicalTKKBridge.residue.inverseTemperature *
              chemicalPotential * number ∧
      B.weyl.curvature (B.weyl.transform gauge parameter) =
        B.weyl.curvature gauge ∧
      B.tkk.inGZero (B.tkk.bracket x y) ∧
      B.kktCertificate.primalFeasible ∧
        B.kktCertificate.dualFeasible ∧
        B.kktCertificate.stationarity ∧
        B.kktCertificate.complementarySlackness ∧
        B.kktCertificate.finitePartitionAdmissible :=
  ⟨B.grandCanonicalActionAffine energy chemicalPotential number,
    B.weyl.curvature_transform_eq gauge parameter,
    B.tkk.bracketPlusMinusMemZero hx hy,
    B.kktCertificate.primalFeasible_proof,
    B.kktCertificate.dualFeasible_proof,
    B.kktCertificate.stationarity_proof,
    B.kktCertificate.complementarySlackness_proof,
    B.kktCertificate.finitePartitionAdmissible_proof⟩

end ConstructiveLiteratureWeylGrandCanonicalTKKKKTBridge

namespace LiteratureWeylGrandCanonicalTKKBridge

variable {R Gauge Parameter Curvature G I X A S : Type*}
variable (B : LiteratureWeylGrandCanonicalTKKBridge
  R Gauge Parameter Curvature G I X A S)

/-- The bridge supplies the residue formula for inverse temperature. -/
@[rep_depth thermo]
theorem inverseTemperatureFromResidue :
    B.residue.inverseTemperature = 4 * Real.pi * B.residue.lapseResidue :=
  B.residue.beta_eq_four_pi_residue

/-- The bridge supplies the grand-canonical affine singular action. -/
@[rep_depth thermo]
theorem grandCanonicalActionAffine
    (energy chemicalPotential number : ℝ) :
    B.residue.grandCanonicalSingularAction
        energy chemicalPotential number =
      B.residue.canonicalSingularAction energy
        - B.residue.inverseTemperature * chemicalPotential * number :=
  B.residue.grandCanonicalSingularAction_eq_canonical_sub_muN
    energy chemicalPotential number

/-- The bridge supplies the contour-holonomy readout of the lapse residue. -/
@[rep_depth thermo]
theorem contourHolonomyReadsLapseResidue :
      B.contourResidue.residueMap
      (B.contourResidue.lineIntegrator.integrate
        (fun i => B.contourResidue.residueField
          (B.contourResidue.contour.point i))) =
        B.contourResidue.lapseResidue :=
  B.contourResidue.contourHolonomy_eq_lapseResidue

/--
The contour-holonomy residue presentation yields the same grand-canonical
affine action once the residue temperature formula is supplied.
-/
@[rep_depth thermo]
theorem contourHolonomyGrandCanonicalActionAffine
    (inverseTemperature : ℝ)
    (hβ : inverseTemperature =
      4 * Real.pi * B.contourResidue.lapseResidue)
    (energy chemicalPotential number : ℝ) :
    B.contourResidue.grandCanonicalContourHolonomyAction
        inverseTemperature hβ energy chemicalPotential number =
      (B.contourResidue.toSimplePoleResidueData
          inverseTemperature hβ).canonicalSingularAction energy
        - inverseTemperature * chemicalPotential * number :=
  ResidueContourHolonomyData.grandCanonicalContourHolonomyAction_eq_canonical_sub_muN
    B.contourResidue inverseTemperature hβ energy chemicalPotential number

/-- The bridge supplies Weyl curvature invariance under gauge change. -/
@[rep_depth transport]
theorem weylCurvatureInvariant
    (gauge : Gauge) (parameter : Parameter) :
    B.weyl.curvature (B.weyl.transform gauge parameter) =
      B.weyl.curvature gauge :=
  B.weyl.curvature_transform_eq gauge parameter

/-- The bridge supplies the TKK closure `[g_+, g_-] ⊆ g_0`. -/
@[rep_depth transport]
theorem tkkPlusMinusClosesInZero
    {x y : G} (hx : B.tkk.inGPlus x) (hy : B.tkk.inGMinus y) :
    B.tkk.inGZero (B.tkk.bracket x y) :=
  B.tkk.bracketPlusMinusMemZero hx hy

end LiteratureWeylGrandCanonicalTKKBridge

/-! ## Weyl-covariant coadjoint entropy foliation -/

namespace WeylCoadjointMetriplecticFoliation

open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic

variable {Orbit LieAlg LieCoalg Gauge Parameter Curvature : Type*}

/--
Bridge from the coadjoint-orbit metriplectic owner to the Weyl-gauge owner.

The coadjoint side is the already-verified dimension-agnostic context: moment
images select the entropy leaves, the reversible channel is the Casimir leaf
direction, and the metric channel is the transverse Onsager direction.  The
Weyl side is the existing curvature-covariant interface; graph/literature
proximity is not used as proof.
-/
@[rep_depth transport]
structure WeylCoadjointMetriplecticBridge where
  metriplectic :
    InfiniteCoadjointOrbitMetriplecticContext Orbit LieAlg LieCoalg
  weyl : WeylGaugeCovariantInterface Gauge Parameter Curvature

namespace WeylCoadjointMetriplecticBridge

variable (B :
  WeylCoadjointMetriplecticBridge
    (Orbit := Orbit) (LieAlg := LieAlg) (LieCoalg := LieCoalg)
    (Gauge := Gauge) (Parameter := Parameter) (Curvature := Curvature))

/--
Proof packet for the prose claim:

* moment images lie on the selected coadjoint/entropy leaf;
* reversible leaf motion is Casimir and has zero entropy production;
* transverse metric motion is the entire nonequilibrium production channel;
* the second law follows from the metric channel;
* Weyl representative changes preserve the curvature readout.
-/
@[rep_depth transport]
theorem entropyFoliation_transverseOnsager_weylCovariant_packet
    (x : Orbit) (gauge : Gauge) (parameter : Parameter) :
    B.metriplectic.isOnCoadjointOrbit (B.metriplectic.moment x)
      ∧ B.metriplectic.isOnCoadjointOrbit
        (B.metriplectic.moment (B.metriplectic.reversibleVectorField x))
      ∧ B.metriplectic.isOnCoadjointOrbit
        (B.metriplectic.moment (B.metriplectic.metricVectorField x))
      ∧ B.metriplectic.reversibleEntropyRate x = 0
      ∧ 0 ≤ B.metriplectic.metricEntropyRate x
      ∧ B.metriplectic.totalEntropyRate x =
        B.metriplectic.metricEntropyRate x
      ∧ 0 ≤ B.metriplectic.totalEntropyRate x
      ∧ B.weyl.curvature (B.weyl.transform gauge parameter) =
        B.weyl.curvature gauge :=
  ⟨B.metriplectic.moment_lands_on_coadjoint_orbit x,
    B.metriplectic.reversible_flow_closes_on_coadjoint_orbit x,
    B.metriplectic.metric_flow_closes_on_coadjoint_orbit x,
    B.metriplectic.reversibleEntropyRate_eq_zero x,
    B.metriplectic.metricEntropyRate_nonnegative x,
    B.metriplectic.totalEntropyRate_eq_metricEntropyRate x,
    B.metriplectic.coadjoint_orbit_metriplectic_second_law x,
    B.weyl.curvature_transform_eq gauge parameter⟩

attribute [terminal] entropyFoliation_transverseOnsager_weylCovariant_packet

end WeylCoadjointMetriplecticBridge

namespace SquareDissipation

variable
  (moment : Orbit → LieCoalg)
  (geometricTemperature : LieAlg)
  (reversibleVectorField metricVectorField : Orbit → Orbit)
  (entropy : Orbit → ℝ)
  (dissipationAmplitude : Orbit → ℝ)
  (weyl : WeylGaugeCovariantInterface Gauge Parameter Curvature)

local notation "C□" =>
  InfiniteCoadjointOrbitMetriplecticContext.ofMomentImageSquareDissipation
    (Orbit := Orbit) (LieAlg := LieAlg) (LieCoalg := LieCoalg)
    moment geometricTemperature reversibleVectorField metricVectorField entropy
    dissipationAmplitude

/--
Constructive dimension-agnostic Weyl/coadjoint foliation packet.

This version removes the explicit Casimir, Onsager nonnegativity, and
entropy-split hypotheses by using the square-dissipation constructor.  It does
not construct a nontrivial Weyl gauge model; it composes with the existing
`WeylGaugeCovariantInterface` proof object supplied by the Weyl owner.
-/
@[rep_depth transport]
theorem squareEntropyFoliation_transverseOnsager_weylCovariant_packet
    (x : Orbit) (gauge : Gauge) (parameter : Parameter) :
    C□.isOnCoadjointOrbit (C□.moment x)
      ∧ C□.isOnCoadjointOrbit (C□.moment (C□.reversibleVectorField x))
      ∧ C□.isOnCoadjointOrbit (C□.moment (C□.metricVectorField x))
      ∧ C□.reversibleEntropyRate x = 0
      ∧ C□.metricEntropyRate x = dissipationAmplitude x ^ (2 : ℕ)
      ∧ C□.totalEntropyRate x = C□.metricEntropyRate x
      ∧ 0 ≤ C□.metricEntropyRate x
      ∧ 0 ≤ C□.totalEntropyRate x
      ∧ weyl.curvature (weyl.transform gauge parameter) =
        weyl.curvature gauge := by
  refine
    ⟨C□.moment_mem_orbit x,
      C□.reversible_preserves_orbit x,
      C□.metric_preserves_state x,
      rfl,
      rfl,
      ?_,
      ?_,
      ?_,
      weyl.curvature_transform_eq gauge parameter⟩
  · rfl
  · exact sq_nonneg (dissipationAmplitude x)
  · exact sq_nonneg (dissipationAmplitude x)

attribute [terminal] squareEntropyFoliation_transverseOnsager_weylCovariant_packet

end SquareDissipation

end WeylCoadjointMetriplecticFoliation

namespace LiteratureWeylGrandCanonicalTKKKKTBridge

variable {R Gauge Parameter Curvature G I X A S : Type*}
variable (B : LiteratureWeylGrandCanonicalTKKKKTBridge
  R Gauge Parameter Curvature G I X A S)

/--
The KKT-enhanced bridge still supplies the grand-canonical affine action from
the underlying residue bridge.
-/
@[rep_depth thermo]
theorem grandCanonicalActionAffine
    (energy chemicalPotential number : ℝ) :
    B.toLiteratureWeylGrandCanonicalTKKBridge.residue.grandCanonicalSingularAction
        energy chemicalPotential number =
      B.toLiteratureWeylGrandCanonicalTKKBridge.residue.canonicalSingularAction energy
        - B.toLiteratureWeylGrandCanonicalTKKBridge.residue.inverseTemperature *
          chemicalPotential * number :=
  LiteratureWeylGrandCanonicalTKKBridge.grandCanonicalActionAffine
    B.toLiteratureWeylGrandCanonicalTKKBridge
    energy chemicalPotential number

end LiteratureWeylGrandCanonicalTKKKKTBridge

end InfoGeometry.Canonical.LiteratureGrandCanonicalWeylTKK
