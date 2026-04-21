import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Canonical.WeylTransport
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
    residueMap.toHolonomy
      (lineIntegrator.integrate (fun i => residueField (contour.point i))) =
        lapseResidue

namespace ResidueContourHolonomyData

variable {I X A S : Type*}
variable (C : ResidueContourHolonomyData I X A S)

/-- The contour holonomy/readout equals the lapse residue. -/
@[rep_depth thermo]
theorem contourHolonomy_eq_lapseResidue :
    C.residueMap.toHolonomy
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
  primalFeasible : Prop
  dualFeasible : Prop
  stationarity : Prop
  complementarySlackness : Prop
  finitePartitionAdmissible : Prop

namespace KarushKuhnTuckerThermodynamicData

variable (K : KarushKuhnTuckerThermodynamicData)

/-- The thermodynamic KKT packet exposes exactly its explicit hypotheses. -/
@[rep_depth thermo]
theorem packet
    (hPrimal : K.primalFeasible)
    (hDual : K.dualFeasible)
    (hStationarity : K.stationarity)
    (hSlack : K.complementarySlackness)
    (hFinite : K.finitePartitionAdmissible) :
    K.primalFeasible ∧ K.dualFeasible ∧ K.stationarity ∧
      K.complementarySlackness ∧ K.finitePartitionAdmissible :=
  ⟨hPrimal, hDual, hStationarity, hSlack, hFinite⟩

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

namespace LiteratureWeylGrandCanonicalTKKBridge

variable {R Gauge Parameter Curvature G I X A S : Type*}
variable (B : LiteratureWeylGrandCanonicalTKKBridge
  R Gauge Parameter Curvature G I X A S)

/-- The bridge supplies the residue formula for inverse temperature. -/
@[rep_depth transport]
theorem inverseTemperatureFromResidue :
    B.residue.inverseTemperature = 4 * Real.pi * B.residue.lapseResidue :=
  B.residue.beta_eq_four_pi_residue

/-- The bridge supplies the grand-canonical affine singular action. -/
@[rep_depth transport]
theorem grandCanonicalActionAffine
    (energy chemicalPotential number : ℝ) :
    B.residue.grandCanonicalSingularAction
        energy chemicalPotential number =
      B.residue.canonicalSingularAction energy
        - B.residue.inverseTemperature * chemicalPotential * number :=
  B.residue.grandCanonicalSingularAction_eq_canonical_sub_muN
    energy chemicalPotential number

/-- The bridge supplies the contour-holonomy readout of the lapse residue. -/
@[rep_depth transport]
theorem contourHolonomyReadsLapseResidue :
    B.contourResidue.residueMap.toHolonomy
      (B.contourResidue.lineIntegrator.integrate
        (fun i => B.contourResidue.residueField
          (B.contourResidue.contour.point i))) =
        B.contourResidue.lapseResidue :=
  B.contourResidue.contourHolonomy_eq_lapseResidue

/--
The contour-holonomy residue presentation yields the same grand-canonical
affine action once the residue temperature formula is supplied.
-/
@[rep_depth transport]
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

namespace LiteratureWeylGrandCanonicalTKKKKTBridge

variable {R Gauge Parameter Curvature G I X A S : Type*}
variable (B : LiteratureWeylGrandCanonicalTKKKKTBridge
  R Gauge Parameter Curvature G I X A S)

/-- The extended bridge exposes the explicit thermodynamic KKT packet. -/
@[rep_depth transport]
theorem kktOptimizationPacket
    (hPrimal : B.kktOptimization.primalFeasible)
    (hDual : B.kktOptimization.dualFeasible)
    (hStationarity : B.kktOptimization.stationarity)
    (hSlack : B.kktOptimization.complementarySlackness)
    (hFinite : B.kktOptimization.finitePartitionAdmissible) :
    B.kktOptimization.primalFeasible ∧
      B.kktOptimization.dualFeasible ∧
      B.kktOptimization.stationarity ∧
      B.kktOptimization.complementarySlackness ∧
      B.kktOptimization.finitePartitionAdmissible :=
  B.kktOptimization.packet hPrimal hDual hStationarity hSlack hFinite

/--
The KKT-enhanced bridge still supplies the grand-canonical affine action from
the underlying residue bridge.
-/
@[rep_depth transport]
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
