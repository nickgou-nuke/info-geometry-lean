import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.RiemannApolloniusVectorFields
import InfoGeometry.Thermodynamics.SouriauApolloniusEntropyFoliation
import InfoGeometry.Volume.ModularSurprisalDerivationBridge
import InfoGeometry.NCG.DerivationDifferential
import InfoGeometry.NCG.NoncommutativeCyclicCocycle
import InfoGeometry.Volume.TracePairingModularInvariance
import InfoGeometry.Lie.SplitOctonionProjectiveRapidityMonodromyBridge
import InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow
import InfoGeometry.Physics.PenroseQuantizedTwistorSplitOctonion
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Apollonius information potential and operator charge

This owner records the theorem-safe part of the source/sink picture.  The
Apollonius imbalance is the difference of squared distances to the two
midpoint foci.  Its zero set is the unit-ratio locus, while its sign records
the two sides.  The logarithmic ratio is only used away from the two foci.

No statement about the location of zeta zeros is made here.
-/

noncomputable section

open Filter
open scoped Topology

namespace InfoGeometry.Arithmetic.ApolloniusInformationChargeBridge

open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Arithmetic.RiemannApolloniusVectorFields
open InfoGeometry.Thermodynamics.SouriauApolloniusFoliation
open InfoGeometry.Lie.SplitOctonionProjectiveRapidityMonodromyBridge
open InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow
open InfoGeometry.Physics.PenroseTwistor

abbrev Point := ℝ × ℝ

/-- The signed Apollonius information imbalance. -/
def apolloniusInformationPotential (p : Point) : ℝ :=
  ((p.1 - 3 / 2) ^ 2 + p.2 ^ 2) - ((p.1 + 1 / 2) ^ 2 + p.2 ^ 2)

/-- The unit-ratio (neutral source/sink) locus. -/
def unitRatioLocus (p : Point) : Prop :=
  apolloniusInformationPotential p = 0

/-- The genuine metric logarithmic ratio from the source/sink formulation.
    Its non-focal domain is carried by the hypotheses of the readback theorem
    below; the signed polynomial potential remains the convenient global
    coordinate surrogate used by the existing Apollonius owners. -/
noncomputable def metricApolloniusPotential {X : Type*} [MetricSpace X]
    (x p q : X) : ℝ :=
  Real.log (dist x p / dist x q)

theorem metricApolloniusPotential_eq_zero_iff
    {X : Type*} [MetricSpace X] {x p q : X}
    (hxp : x ≠ p) (hxq : x ≠ q) :
    metricApolloniusPotential x p q = 0 ↔ dist x p = dist x q := by
  unfold metricApolloniusPotential
  have hxp' : (0 : ℝ) < dist x p := dist_pos.mpr hxp
  have hxq' : (0 : ℝ) < dist x q := dist_pos.mpr hxq
  have hpos : 0 < dist x p / dist x q := div_pos hxp' hxq'
  constructor
  · intro h
    have hone : dist x p / dist x q = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero hpos h
    exact (div_eq_one_iff_eq (ne_of_gt hxq')).mp hone
  · intro h
    rw [h, div_self (ne_of_gt hxq'), Real.log_one]

theorem metricApolloniusPotential_lt_zero_iff
    {X : Type*} [MetricSpace X] {x p q : X}
    (hxp : x ≠ p) (hxq : x ≠ q) :
    metricApolloniusPotential x p q < 0 ↔ dist x p < dist x q := by
  unfold metricApolloniusPotential
  have hpos : 0 < dist x p / dist x q :=
    div_pos (dist_pos.mpr hxp) (dist_pos.mpr hxq)
  rw [Real.log_neg_iff hpos]
  exact (div_lt_one (dist_pos.mpr hxq) :
    dist x p / dist x q < 1 ↔ dist x p < dist x q)

theorem metricApolloniusPotential_pos_iff
    {X : Type*} [MetricSpace X] {x p q : X}
    (hxp : x ≠ p) (hxq : x ≠ q) :
    0 < metricApolloniusPotential x p q ↔ dist x q < dist x p := by
  unfold metricApolloniusPotential
  have hpos : 0 < dist x p / dist x q :=
    div_pos (dist_pos.mpr hxp) (dist_pos.mpr hxq)
  rw [Real.log_pos_iff hpos.le]
  exact (one_lt_div (dist_pos.mpr hxq) :
    1 < dist x p / dist x q ↔ dist x q < dist x p)

theorem metricApolloniusPotential_swap
    {X : Type*} [MetricSpace X] {x p q : X}
    (hxp : x ≠ p) (hxq : x ≠ q) :
    metricApolloniusPotential x q p = -metricApolloniusPotential x p q := by
  unfold metricApolloniusPotential
  have hxp' : dist x p ≠ 0 := ne_of_gt (dist_pos.mpr hxp)
  have hxq' : dist x q ≠ 0 := ne_of_gt (dist_pos.mpr hxq)
  rw [div_eq_mul_inv, div_eq_mul_inv,
    Real.log_mul hxq' (inv_ne_zero hxp'), Real.log_inv,
    Real.log_mul hxp' (inv_ne_zero hxq'), Real.log_inv]
  ring

/-! A signed transverse coordinate is the negative logarithmic distance ratio.
The name records the intended coordinate interpretation, while its theorems
remain purely metric and make no claim about a Lorentzian representation. -/

noncomputable def transverseRapidity {X : Type*} [MetricSpace X]
    (x p q : X) : ℝ :=
  -metricApolloniusPotential x p q

theorem transverseRapidity_eq_zero_iff
    {X : Type*} [MetricSpace X] {x p q : X}
    (hxp : x ≠ p) (hxq : x ≠ q) :
    transverseRapidity x p q = 0 ↔ dist x p = dist x q := by
  simpa [transverseRapidity] using
    (metricApolloniusPotential_eq_zero_iff hxp hxq)

theorem transverseRapidity_pos_iff
    {X : Type*} [MetricSpace X] {x p q : X}
    (hxp : x ≠ p) (hxq : x ≠ q) :
    0 < transverseRapidity x p q ↔ dist x p < dist x q := by
  simpa [transverseRapidity] using
    (metricApolloniusPotential_lt_zero_iff hxp hxq)

theorem transverseRapidity_neg_iff
    {X : Type*} [MetricSpace X] {x p q : X}
    (hxp : x ≠ p) (hxq : x ≠ q) :
    transverseRapidity x p q < 0 ↔ dist x q < dist x p := by
  simpa [transverseRapidity] using
    (metricApolloniusPotential_pos_iff hxp hxq)

theorem transverseRapidity_swap
    {X : Type*} [MetricSpace X] {x p q : X}
    (hxp : x ≠ p) (hxq : x ≠ q) :
    transverseRapidity x q p = -transverseRapidity x p q := by
  unfold transverseRapidity
  have h := metricApolloniusPotential_swap hxp hxq
  linarith

theorem metricApolloniusPotential_eq_twice_projectiveRapidity
    {X : Type*} [MetricSpace X] {x p q : X}
    (hxp : x ≠ p) (hxq : x ≠ q) :
    metricApolloniusPotential x p q =
      2 * rapidity (dist x p) (dist x q) := by
  unfold metricApolloniusPotential rapidity projZ
  rw [Real.log_div (ne_of_gt (dist_pos.mpr hxp))
    (ne_of_gt (dist_pos.mpr hxq))]
  ring

theorem apolloniusInformationPotential_formula (p : Point) :
    apolloniusInformationPotential p = -4 * p.1 + 2 := by
  unfold apolloniusInformationPotential
  ring

/-- Exact centered-coordinate readout of the Souriau affine temperature. -/
theorem apolloniusInformationPotential_eq_souriauBeta (s : ℂ) :
    apolloniusInformationPotential (s.re, s.im) =
      souriauApolloniusBeta s.re := by
  rw [apolloniusInformationPotential_formula]
  rfl

/-! The canonical affine chart has the normalized transverse coordinate
`σ - 1/2`.  It is the affine readout of the signed Apollonius imbalance,
not an additional Lorentzian structure. -/

def affineTransverseCoordinate (p : Point) : ℝ :=
  -(1 / 4 : ℝ) * apolloniusInformationPotential p

theorem affineTransverseCoordinate_formula (p : Point) :
    affineTransverseCoordinate p = p.1 - 1 / 2 := by
  rw [affineTransverseCoordinate, apolloniusInformationPotential_formula]
  ring

theorem affineTransverseCoordinate_eq_zero_iff (p : Point) :
    affineTransverseCoordinate p = 0 ↔ p.1 = 1 / 2 := by
  rw [affineTransverseCoordinate_formula]
  constructor <;> intro h <;> linarith

theorem affineTransverseCoordinate_pos_iff (p : Point) :
    0 < affineTransverseCoordinate p ↔ 1 / 2 < p.1 := by
  rw [affineTransverseCoordinate_formula]
  constructor <;> intro h <;> linarith

theorem affineTransverseCoordinate_neg_iff (p : Point) :
    affineTransverseCoordinate p < 0 ↔ p.1 < 1 / 2 := by
  rw [affineTransverseCoordinate_formula]
  constructor <;> intro h <;> linarith

theorem unitRatioLocus_iff_criticalLine (p : Point) :
    unitRatioLocus p ↔ p.1 = 1 / 2 := by
  unfold unitRatioLocus
  rw [apolloniusInformationPotential_formula]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-! The affine Apollonius equator is the same locus as the Cayley unit-circle
    readout.  The Cayley transform itself remains owned by the canonical
    conformal-geometry file. -/
theorem unitRatioLocus_iff_cayley_unitCircle (p : Point) :
    unitRatioLocus p ↔
      OnLeeYangCircle
        (cayleyToFugacity ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
  rw [unitRatioLocus_iff_criticalLine]
  have h := criticalLine_iff_cayley_unitCircle
      ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
  change p.1 = (1 / 2 : ℝ) ↔ _
  convert h using 1
  simp [OnCriticalLine]

def cayleyStereographicSphere (s : ℂ) : SpherePoint :=
  stereographicSphere (cayleyToFugacity s)

/-- The Cayley--stereographic composite has values on the unit sphere.

This is a carrier-level compactification statement only: it does not add a
topology or identify the compactification with a quotient of the punctured
plane. -/
theorem cayleyStereographicSphere_unit_sphere (s : ℂ) :
    let p := cayleyStereographicSphere s
    p.X ^ 2 + p.Y ^ 2 + p.Z ^ 2 = 1 := by
  exact stereographic_unit_sphere (cayleyToFugacity s)

theorem cayleyStereographicSphere_critical_equator
    {s : ℂ} (hs : OnCriticalLine s) :
    (cayleyStereographicSphere s).Z = 0 := by
  unfold cayleyStereographicSphere stereographicSphere
  have hcircle := cayleyToFugacity_mem_unitCircle_of_criticalLine s hs
  have hnorm : (cayleyToFugacity s).re ^ 2 +
      (cayleyToFugacity s).im ^ 2 = 1 := by
    have hcircle' := hcircle
    simp only [OnLeeYangCircle, Complex.normSq_apply] at hcircle'
    nlinarith

  rw [hnorm]
  norm_num

theorem cayleyStereographicSphere_equator_critical
    {s : ℂ} (hs : (cayleyStereographicSphere s).Z = 0) :
    OnCriticalLine s := by
  unfold cayleyStereographicSphere stereographicSphere at hs
  have hden : 1 + (cayleyToFugacity s).re ^ 2 +
      (cayleyToFugacity s).im ^ 2 ≠ 0 := by
    have hpos : 0 < 1 + (cayleyToFugacity s).re ^ 2 +
        (cayleyToFugacity s).im ^ 2 := by positivity
    linarith
  have hnorm : (cayleyToFugacity s).re ^ 2 +
      (cayleyToFugacity s).im ^ 2 = 1 := by
    field_simp [hden] at hs
    nlinarith
  apply (criticalLine_iff_cayley_unitCircle s).2
  simp only [OnLeeYangCircle, Complex.normSq_apply]
  nlinarith

/-- The source/sink side is the sign of the information potential. -/
theorem source_side_iff (p : Point) :
    apolloniusInformationPotential p < 0 ↔ 1 / 2 < p.1 := by
  rw [apolloniusInformationPotential_formula]
  constructor <;> intro h <;> linarith

theorem sink_side_iff (p : Point) :
    0 < apolloniusInformationPotential p ↔ p.1 < 1 / 2 := by
  rw [apolloniusInformationPotential_formula]
  constructor <;> intro h <;> linarith

theorem potential_zero_iff_unit_ratio (p : Point) :
    unitRatioLocus p ↔
      ((p.1 - 3 / 2) ^ 2 + p.2 ^ 2) =
        ((p.1 + 1 / 2) ^ 2 + p.2 ^ 2) := by
  unfold unitRatioLocus
  rw [apolloniusInformationPotential]
  constructor <;> intro h
  · linarith
  · exact sub_eq_zero.mpr h

/-! The three-way geometric readout.  The names `source` and `sink` are
    conventional labels for the two sides; no dynamical orientation is
    inferred from them. -/

theorem apollonius_source_sink_equator_packet (p : Point) :
    (apolloniusInformationPotential p < 0 ↔ 1 / 2 < p.1) ∧
    (unitRatioLocus p ↔ p.1 = 1 / 2) ∧
    (0 < apolloniusInformationPotential p ↔ p.1 < 1 / 2) := by
  exact ⟨source_side_iff p, unitRatioLocus_iff_criticalLine p, sink_side_iff p⟩

/-! The finite electrostatic-style readout on the neutral leaf.  The
    orthogonality is Euclidean and the field directions are the already
    defined coordinate fields; no global flow or attractor statement is
    encoded. -/
theorem apollonius_equator_vector_packet (t : ℝ) :
    unitRatioLocus (1 / 2, t) ∧
    (rotationalField (1 / 2) t).1 = 0 ∧
    (dilationCoordinateField (1 / 2) t).2 = 0 ∧
    (rotationalField (1 / 2) t).2 = 1 / 4 + t ^ 2 := by
  exact ⟨(unitRatioLocus_iff_criticalLine (1 / 2, t)).mpr rfl,
    rotationalField_criticalLine_transverse_zero t,
    dilationCoordinateField_criticalLine_longitudinal_zero t,
    rotationalField_criticalLine_longitudinal t⟩

/-! ## Noncommutative transport -/

section Operator

variable {A : Type*} [Ring A]

/-- Information transport generated by a noncommutative surprisal operator. -/
def surprisalTransport (K : A) : A → A := fun a => K * a - a * K

/- The Apollonius operator transport is the native noncommutative-calculus
   inner derivation, not merely an extensionally similar function. -/
theorem surprisalTransport_eq_innerDerivation (K : A) :
    surprisalTransport K =
      InfoGeometry.NCG.DerivationDifferential.innerDerivation K := by
  funext a
  rfl

theorem surprisalTransport_leibniz (K a b : A) :
    surprisalTransport K (a * b) =
      surprisalTransport K a * b + a * surprisalTransport K b := by
  dsimp [surprisalTransport]
  noncomm_ring

/-- The Apollonius transport is also the canonical inner derivation used by
the cyclic-cohomology lane.  This is an interoperability theorem between
the two existing owners; it introduces no second derivation structure. -/
theorem surprisalTransport_eq_cyclicInnerAlgebraDerivation
    {R : Type*} [CommRing R] [Algebra R A] (K : A) :
    surprisalTransport K =
      (fun a => InfoGeometry.NCG.innerAlgebraDerivation (R := R) K a) := by
  funext a
  rfl

end Operator

section TraceCharge

open InfoGeometry.Physics
open InfoGeometry.Volume.TracePairingModularInvariance

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace-pairing charge of an operator transported by its own
    noncommutative surprisal flow vanishes. -/
theorem surprisal_trace_charge_conserved (K X : TraceOperatorSpace n) :
    tracePairingNative K (commutatorActionNative K X) = 0 := by
  exact generator_trace_pairing_orthogonal K X

/-- Trace pairing is infinitesimally invariant under the inner derivation.
    This is the operator-valued conservation law; no scalar commutativity is
    assumed. -/
theorem surprisal_trace_charge_invariant
    (K X Y : TraceOperatorSpace n) :
    tracePairingNative (commutatorActionNative K X) Y +
        tracePairingNative X (commutatorActionNative K Y) = 0 := by
  exact infinitesimal_trace_pairing_ad_invariant K X Y

/- The charge `Tr(K X)` is stationary to first order along the modular
   commutator flow of `X`.  This is the concrete second-commutator readout of
   the preceding ad-invariance theorem; it introduces no scalar or diagonal
   replacement for the operator algebra. -/
theorem surprisal_trace_charge_modular_flow_stationary
    (K X : TraceOperatorSpace n) :
    tracePairingNative K
        (commutatorActionNative K (commutatorActionNative K X)) = 0 := by
  have h := infinitesimal_trace_pairing_ad_invariant K K
    (commutatorActionNative K X)
  have hKK : commutatorActionNative K K = 0 := by
    simp [commutatorActionNative, leftActionNative, rightActionNative]
  rw [hKK] at h
  have hzero : tracePairingNative 0 (commutatorActionNative K X) = 0 := by
    simp [tracePairingNative]
  linarith

end TraceCharge

/-! The source/sink data are kept separate from the potential.  This makes
the non-focal domain explicit without pretending that a metric space carries
a canonical vector field or integration theory. -/

structure ApolloniusPotentialData (X : Type*) [MetricSpace X] where
  source : X
  sink : X
  source_ne_sink : source ≠ sink

namespace ApolloniusPotentialData

variable {X : Type*} [MetricSpace X] (A : ApolloniusPotentialData X)

def potential (x : X) : ℝ :=
  metricApolloniusPotential x A.source A.sink

def equator (x : X) : Prop :=
  A.potential x = 0

def sourceSide (x : X) : Prop :=
  A.potential x < 0

def sinkSide (x : X) : Prop :=
  0 < A.potential x

def swap : ApolloniusPotentialData X where
  source := A.sink
  sink := A.source
  source_ne_sink := Ne.symm A.source_ne_sink

theorem potential_swap
    {x : X} (hxs : x ≠ A.source) (hxt : x ≠ A.sink) :
    (A.swap).potential x = -A.potential x := by
  change metricApolloniusPotential x A.sink A.source =
    -metricApolloniusPotential x A.source A.sink
  exact metricApolloniusPotential_swap hxs hxt

theorem equator_swap :
    ∀ {x : X}, (A.swap).equator x ↔ A.equator x := by
  intro x
  by_cases hxs : x = A.source
  · subst x
    simp [equator, potential, metricApolloniusPotential, swap]
  by_cases hxt : x = A.sink
  · subst x
    simp [equator, potential, metricApolloniusPotential, swap]
  change (A.swap).potential x = 0 ↔ A.potential x = 0
  rw [potential_swap A hxs hxt]
  simp

theorem potential_eq_zero_iff
    {x : X} (hxs : x ≠ A.source) (hxt : x ≠ A.sink) :
    A.potential x = 0 ↔ dist x A.source = dist x A.sink := by
  exact metricApolloniusPotential_eq_zero_iff hxs hxt

theorem potential_lt_zero_iff
    {x : X} (hxs : x ≠ A.source) (hxt : x ≠ A.sink) :
    A.sourceSide x ↔ dist x A.source < dist x A.sink := by
  exact metricApolloniusPotential_lt_zero_iff hxs hxt

theorem potential_pos_iff
    {x : X} (hxs : x ≠ A.source) (hxt : x ≠ A.sink) :
    A.sinkSide x ↔ dist x A.sink < dist x A.source := by
  exact metricApolloniusPotential_pos_iff hxs hxt

end ApolloniusPotentialData

/-! A genuine restoring rapidity flow is distinct from the affine translation
`dissipativeFlow` in the zeta chart.  The following is the canonical linear
normal flow with equilibrium at the Apollonius equator `u = 0`. -/

def rapidityRelaxation (γ t u : ℝ) : ℝ :=
  Real.exp (-γ * t) * u

theorem affineTransverseCoordinate_flowMap (γ t : ℝ) (p : Point) :
    (flowMap γ 0 t (affineTransverseCoordinate p, p.2)).1 =
      rapidityRelaxation γ t (affineTransverseCoordinate p) := by
  rfl

@[simp] theorem rapidityRelaxation_zero (γ t : ℝ) :
    rapidityRelaxation γ t 0 = 0 := by
  simp [rapidityRelaxation]

theorem rapidityRelaxation_add (γ s t u : ℝ) :
    rapidityRelaxation γ (s + t) u =
      rapidityRelaxation γ s (rapidityRelaxation γ t u) := by
  unfold rapidityRelaxation
  rw [show -γ * (s + t) = (-γ * s) + (-γ * t) by ring, Real.exp_add]
  ring

theorem rapidityRelaxation_preserves_sign {γ t u : ℝ} :
    0 < rapidityRelaxation γ t u ↔ 0 < u := by
  simp [rapidityRelaxation, Real.exp_pos]

theorem rapidityRelaxation_hasDerivAt (γ u t : ℝ) :
    HasDerivAt (fun s : ℝ => rapidityRelaxation γ s u)
      (-γ * rapidityRelaxation γ t u) t := by
  unfold rapidityRelaxation
  have hinner : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t := by
    convert (hasDerivAt_const t (-γ)).mul (hasDerivAt_id t) using 1
    ring
  have hexp := (Real.hasDerivAt_exp (-γ * t)).comp t hinner
  convert hexp.const_mul u using 1
  · funext s
    dsimp
    ring
  · ring

theorem rapidityRelaxation_solves_linear_ode (γ u t : ℝ) :
    deriv (fun s : ℝ => rapidityRelaxation γ s u) t =
      -γ * rapidityRelaxation γ t u := by
  exact (rapidityRelaxation_hasDerivAt γ u t).deriv

theorem rapidityRelaxation_tendsto_zero {γ u : ℝ} (hγ : 0 < γ) :
    Tendsto (fun t : ℝ => rapidityRelaxation γ t u) atTop (𝓝 0) := by
  unfold rapidityRelaxation
  have h_exp : Tendsto (fun t : ℝ => Real.exp (-γ * t)) atTop (𝓝 0) := by
    have hlinear : Tendsto (fun t : ℝ => γ * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hγ Filter.tendsto_id
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
    simpa only [Function.comp_apply, neg_mul] using hexp
  simpa [mul_zero] using h_exp.mul_const u

/-! ## Unified geometric corridor

The following packet is the canonical connection point for the geometric
lanes: the affine neutral leaf, its Cayley unit-circle readout, and the
compact sphere equator are the same condition.  The rapidity flow is recorded
separately as the native normal evolution, so no identification of affine
time with a projective angle is introduced. -/

theorem apollonius_cayley_sphere_corridor (t : ℝ) :
    unitRatioLocus (1 / 2, t) ∧
    OnLeeYangCircle
      (cayleyToFugacity (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) ∧
    (cayleyStereographicSphere
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).Z = 0 := by
  have hunit : unitRatioLocus (1 / 2, t) :=
    (unitRatioLocus_iff_criticalLine (1 / 2, t)).mpr rfl
  have hcrit : OnCriticalLine
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    simp [OnCriticalLine]
  exact ⟨hunit,
    cayleyToFugacity_mem_unitCircle_of_criticalLine _ hcrit,
    cayleyStereographicSphere_critical_equator hcrit⟩

/-! The dipole coefficient is the difference of the two logarithmic pole
forms.  This is the algebraic identity needed before any period theorem; it
does not itself assert a contour integral or a zero-counting result. -/
theorem dipole_logarithmic_coefficient_partial_fraction
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    1 / (s - 1) - 1 / s = 1 / (s * (s - 1)) := by
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

theorem dipole_logarithmic_coefficient_reflection
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    1 / ((1 - s) - 1) - 1 / (1 - s) =
      1 / (s - 1) - 1 / s := by
  have h1s : 1 - s ≠ 0 := by
    intro h
    exact hs1 ((sub_eq_zero.mp h).symm)
  have hs1' : (1 - s) - 1 ≠ 0 := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [sub_eq_zero.mp h]
      _ = 0 := by ring
  field_simp [hs0, hs1, h1s, hs1', sub_ne_zero.mpr hs1]
  ring

end InfoGeometry.Arithmetic.ApolloniusInformationChargeBridge
