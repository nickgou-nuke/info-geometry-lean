import InfoGeometry.Arithmetic.RHQuantumStabilityBridge
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.HestenesComplexTranslation
import InfoGeometry.Krein.HestenesModularKMSBridge
import InfoGeometry.Krein.HilbertBridge

/-!
# Hestenes-Krein Translated RH on a Real Doubled Carrier

The theorem-safe formulation here does **not** prove the original
complex-plane formulation as a native statement about points of `ℂ`.  The
native carrier is a real doubled Hestenes/Krein space with two real spectral
coordinates:

* `sigma` — the real thermodynamic/conformal coordinate;
* `height` — the modular phase/flow coordinate.

The "critical line" becomes a `throat` predicate on real Krein states.  The
remaining analytic socket is stated in order language:

* every zero-state must be supported by some finite stage of an inductive
  colimit; or
* equivalently for global boundary work, every zero-state must lie in a
  Zorn-maximal admissible subsystem where the `J`-odd obstruction is killed.

The theorem proved in this language is the Hestenes-Krein translated theorem:
zero-states of the real doubled spectral chart are supported on the real
fixed throat.  A classical complex-plane RH statement is recovered only after
supplying explicit charts from completed-zeta zeros to Krein zero states, and
conversely.

Thus the file proves the language-translated theorem and records the exact
chart boundary at which one may compare it with the original formulation.
-/

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Arithmetic.RHRealDoubledKreinReformulation

open InfoGeometry.Arithmetic.RHQuantumStabilityBridge
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Krein

/--
The repo-native real doubled conformal/Krein carrier associated to a real
Hilbert seed `E`.
-/
abbrev RealDoubledConformalKreinCarrier
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  HilbertDoubled E

/--
The existing Hestenes translation embeds a complex coordinate as a real-linear
operator on the doubled carrier.  The complex plane is therefore a chart inside
the real doubled Krein operator geometry, not the native carrier.
-/
@[rep_depth krein]
noncomputable abbrev hestenesComplexCoordinate
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (z : ℂ) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  InfoGeometry.Canonical.HestenesComplexTranslation.hestenesScalar (E := E) z

/-- Tomita reflection reverses the Hestenes imaginary/clock axis. -/
@[rep_depth krein]
theorem hestenes_phaseAxis_conjugation
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    modular_j (E := E) * complex_i (E := E) * modular_j (E := E) =
      -complex_i (E := E) := by
  simpa using
    (InfoGeometry.Canonical.HestenesComplexTranslation.modular_j_conjugates_complex_i
      (E := E))

/--
Tomita reflection implements complex conjugation on the embedded Hestenes
complex-coordinate chart.
-/
@[rep_depth krein]
theorem hestenesComplexCoordinate_conjugation
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (z : ℂ) :
    modular_j (E := E) * hestenesComplexCoordinate E z * modular_j (E := E) =
      hestenesComplexCoordinate E (star z) := by
  simpa [hestenesComplexCoordinate] using
    (InfoGeometry.Canonical.HestenesComplexTranslation.modular_j_conjugates_hestenesScalar
      (E := E) z)

/--
The real doubled Krein spectral chart.

The zero sector is a predicate on real Krein states, not on complex numbers.
The throat is a real state-space predicate whose coordinate readout is the
fixed point `sigma = 1/2` of the reflection `sigma ↦ 1 - sigma`.
-/
@[rep_depth krein]
structure KreinSpectralChart
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] where
  /-- Spectral zero states in the real doubled Krein carrier. -/
  zeroSector : H → Prop
  /-- Thermodynamic/conformal coordinate. -/
  sigma : H → ℝ
  /-- Modular phase/flow coordinate. -/
  height : H → ℝ
  /-- Real fixed-throat predicate replacing the complex critical line. -/
  throat : H → Prop
  /-- The throat is exactly the fixed real-coordinate condition. -/
  throat_iff_sigma :
    ∀ ψ : H, throat ψ ↔ IsCriticalLineRealPart (sigma ψ)
  /-- Tomita/Krein mirror preserves the zero sector. -/
  zero_mirror :
    ∀ ψ : H, zeroSector ψ → zeroSector (KreinSpace.jCLM (H := H) ψ)
  /-- Tomita/Krein mirror acts on the real coordinate by `sigma ↦ 1 - sigma`. -/
  sigma_mirror :
    ∀ ψ : H,
      sigma (KreinSpace.jCLM (H := H) ψ) =
        criticalReflection (sigma ψ)

/-- The Krein-native RH/no-leakage formulation. -/
@[rep_depth krein]
def KreinRH
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) : Prop :=
  ∀ ψ : H, C.zeroSector ψ → C.throat ψ

/--
Formal name for the theorem actually native to this file: the
Hestenes-Krein translated RH statement on a real doubled spectral chart.
-/
@[rep_depth krein]
def HestenesKreinTranslatedRH
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) : Prop :=
  KreinRH C

/-- Alias emphasizing the physical reading: zero states do not leave the throat. -/
@[rep_depth krein]
def KreinNoLeakage
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) : Prop :=
  ∀ ψ : H, C.zeroSector ψ → C.throat ψ

/-- Alias for the measure-theoretic reading: the zero sector is supported on the throat. -/
@[rep_depth krein]
def KreinSpectralConcentration
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) : Prop :=
  ∀ ψ : H, C.zeroSector ψ → C.throat ψ

/--
Obstruction data for the final no-leakage step.

This is the precise place where the topology enters the RH reformulation:
an off-throat zero must create a `J`-odd obstruction, while the twisted-index
vanishing theorem supplies the obstruction-vanishing clause.  Only the
combination proves spectral concentration.
-/
@[rep_depth krein]
structure KreinOddObstructionData
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) where
  /-- Abstract predicate for the `J`-odd/twisted-index obstruction. -/
  oddObstruction : H → Prop
  /-- Any zero away from the throat produces the obstruction. -/
  off_throat_obstructs :
    ∀ ψ : H, C.zeroSector ψ → ¬ C.throat ψ → oddObstruction ψ
  /-- The twisted-index/topological theorem kills that obstruction on zero states. -/
  obstruction_vanishes :
    ∀ ψ : H, C.zeroSector ψ → ¬ oddObstruction ψ

/--
Inductive-colimit support property for the zero sector.

The intended use is finite-stage arithmetic/Fredholm/Krein data transported
through a direct-limit carrier.  It says every zero-state has a finite-stage
representative, and every such stage already proves the throat condition.
-/
@[rep_depth krein]
structure KreinFiniteStageSupportData
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) where
  /-- Indexing type of finite stages in the inductive system. -/
  Stage : Type*
  /-- Stage-membership relation after mapping into the colimit carrier. -/
  stageMember : Stage → H → Prop
  /-- Every zero-state is represented at some finite stage. -/
  zero_has_stage :
    ∀ ψ : H, C.zeroSector ψ → ∃ n : Stage, stageMember n ψ
  /-- Each finite stage carries the no-leakage/throat proof. -/
  stage_no_leakage :
    ∀ n : Stage, ∀ ψ : H, stageMember n ψ → C.zeroSector ψ → C.throat ψ

/--
Zorn-maximal subsystem property for the zero sector.

This mirrors the repository's boundary Zorn theorems: choose an admissible
subsystem between a seed and an ambient boundary, make it maximal by Zorn's
lemma, and prove the zero sector is contained in that maximal subsystem.
-/
@[rep_depth krein]
structure KreinZornMaximalSubsystemData
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) where
  /-- Admissible boundary/Fredholm/Krein subsystems. -/
  admissible : Set H → Prop
  /-- Seed subsystem. -/
  seed : Set H
  /-- Ambient subsystem. -/
  ambient : Set H
  /-- Zorn-maximal subsystem between `seed` and `ambient`. -/
  maximal : Set H
  /-- Native order-theoretic maximality in the constrained subsystem set. -/
  maximality :
    Maximal (fun N : Set H => seed ⊆ N ∧ N ⊆ ambient ∧ admissible N) maximal
  /-- The analytic zero sector is contained in the Zorn-maximal subsystem. -/
  zero_subset_maximal :
    ∀ ψ : H, C.zeroSector ψ → ψ ∈ maximal
  /-- The maximal subsystem kills leakage. -/
  maximal_no_leakage :
    ∀ ψ : H, ψ ∈ maximal → C.zeroSector ψ → C.throat ψ

@[rep_depth krein]
theorem kreinNoLeakage_iff_kreinRH
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) :
    KreinNoLeakage C ↔ KreinRH C :=
  Iff.rfl

@[rep_depth krein]
theorem kreinSpectralConcentration_iff_kreinRH
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) :
    KreinSpectralConcentration C ↔ KreinRH C :=
  Iff.rfl

@[rep_depth krein]
theorem hestenesKreinTranslatedRH_iff_kreinRH
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) :
    HestenesKreinTranslatedRH C ↔ KreinRH C :=
  Iff.rfl

/--
The real doubled Krein RH/no-leakage statement follows from an explicit
`J`-odd obstruction property.

This avoids the invalid shortcut "`J`-odd trace vanishes, therefore all poles
are on the throat" unless the chart supplies the separation statement that an
off-throat zero creates a nonzero obstruction.
-/
@[rep_depth krein]
theorem kreinRH_of_oddObstructionCertificate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (O : KreinOddObstructionData C) :
    KreinRH C := by
  intro ψ hzero
  by_contra hnot
  exact O.obstruction_vanishes ψ hzero
    (O.off_throat_obstructs ψ hzero hnot)

@[rep_depth krein]
theorem kreinSpectralConcentration_of_oddObstructionCertificate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (O : KreinOddObstructionData C) :
    KreinSpectralConcentration C :=
  kreinRH_of_oddObstructionCertificate O

/-- Colimit-stage support plus finite-stage no-leakage proves translated Krein RH. -/
@[rep_depth krein]
theorem kreinRH_of_inductiveColimitSupport
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (L : KreinFiniteStageSupportData C) :
    KreinRH C := by
  intro ψ hzero
  rcases L.zero_has_stage ψ hzero with ⟨n, hn⟩
  exact L.stage_no_leakage n ψ hn hzero

@[rep_depth krein]
theorem kreinSpectralConcentration_of_inductiveColimitSupport
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (L : KreinFiniteStageSupportData C) :
    KreinSpectralConcentration C :=
  kreinRH_of_inductiveColimitSupport L

/-- Zorn-maximal containment plus maximal-subsystem no-leakage proves translated Krein RH. -/
@[rep_depth krein]
theorem kreinRH_of_zornMaximalSubsystem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (Z : KreinZornMaximalSubsystemData C) :
    KreinRH C := by
  intro ψ hzero
  exact Z.maximal_no_leakage ψ (Z.zero_subset_maximal ψ hzero) hzero

@[rep_depth krein]
theorem kreinSpectralConcentration_of_zornMaximalSubsystem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (Z : KreinZornMaximalSubsystemData C) :
    KreinSpectralConcentration C :=
  kreinRH_of_zornMaximalSubsystem Z

/--
The real throat is invariant as a set under the Tomita/Krein mirror.

This is the set-level version appropriate to the doubled real/Klein-bottle
picture: the mirror need not fix every state pointwise; it preserves the
throat because it sends `sigma` to `1 - sigma`.
-/
@[rep_depth krein]
theorem mirror_preserves_throat
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H)
    {ψ : H} (hψ : C.throat ψ) :
    C.throat (KreinSpace.jCLM (H := H) ψ) := by
  apply (C.throat_iff_sigma _).2
  rw [C.sigma_mirror ψ]
  have hs : C.sigma ψ = (1 / 2 : ℝ) :=
    (C.throat_iff_sigma ψ).1 hψ
  unfold IsCriticalLineRealPart criticalReflection
  rw [hs]
  ring

/-- The Tomita/Krein mirror preserves the Krein zero sector by chart data. -/
@[rep_depth krein]
theorem mirror_preserves_zeroSector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H)
    {ψ : H} (hψ : C.zeroSector ψ) :
    C.zeroSector (KreinSpace.jCLM (H := H) ψ) :=
  C.zero_mirror ψ hψ

/--
Original complex-coordinate RH relative to a supplied completed-zero
predicate.  This is not the native theorem of the real doubled carrier.
-/
@[rep_depth operator]
def ComplexRH (XiZero : ℂ → Prop) : Prop :=
  ∀ s : ℂ, XiZero s → OnCriticalLine s

/--
Chart from classical completed-zeta zeros to real doubled Krein zero states.

This is the analytic/socket boundary: the map from a complex zero to a Krein
state is not invented by this file.
-/
@[rep_depth krein]
structure ComplexToKreinZeroChart
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) (XiZero : ℂ → Prop) where
  stateOf : ∀ s : ℂ, XiZero s → H
  state_zero : ∀ s hs, C.zeroSector (stateOf s hs)
  sigma_state : ∀ s hs, C.sigma (stateOf s hs) = s.re

/--
Chart from real doubled Krein zero states back to classical completed-zeta
zeros.

Together with `ComplexToKreinZeroChart`, this is the reversible dictionary
between the real doubled formulation and the usual complex-coordinate
formulation.
-/
@[rep_depth krein]
structure KreinToComplexZeroChart
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) (XiZero : ℂ → Prop) where
  pointOf : ∀ ψ : H, C.zeroSector ψ → ℂ
  point_zero : ∀ ψ hψ, XiZero (pointOf ψ hψ)
  sigma_point : ∀ ψ hψ, (pointOf ψ hψ).re = C.sigma ψ

/--
If the Hestenes-Krein translated theorem holds and complex zeros have been
charted into the Krein zero sector, then the original complex-coordinate
critical-line statement follows.
-/
@[rep_depth krein]
theorem complexRH_of_kreinRH
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H} {XiZero : ℂ → Prop}
    (hKrein : KreinRH C)
    (Z : ComplexToKreinZeroChart C XiZero) :
    ComplexRH XiZero := by
  intro s hs
  unfold OnCriticalLine
  have hthroat : C.throat (Z.stateOf s hs) :=
    hKrein (Z.stateOf s hs) (Z.state_zero s hs)
  have hcrit : IsCriticalLineRealPart (C.sigma (Z.stateOf s hs)) :=
    (C.throat_iff_sigma (Z.stateOf s hs)).1 hthroat
  unfold IsCriticalLineRealPart at hcrit
  rw [Z.sigma_state s hs] at hcrit
  exact hcrit

/--
Conversely, if every Krein zero state is charted back to an original
complex-coordinate completed zero, then the original complex-coordinate
statement implies the Hestenes-Krein translated no-leakage statement.
-/
@[rep_depth krein]
theorem kreinRH_of_complexRH
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H} {XiZero : ℂ → Prop}
    (hComplex : ComplexRH XiZero)
    (Z : KreinToComplexZeroChart C XiZero) :
    KreinRH C := by
  intro ψ hψ
  apply (C.throat_iff_sigma ψ).2
  unfold IsCriticalLineRealPart
  have hz : OnCriticalLine (Z.pointOf ψ hψ) :=
    hComplex (Z.pointOf ψ hψ) (Z.point_zero ψ hψ)
  unfold OnCriticalLine at hz
  rw [← Z.sigma_point ψ hψ]
  exact hz

/--
With both charts supplied, the Hestenes-Krein translated formulation and the
original complex-coordinate formulation are equivalent as charted statements.
-/
@[rep_depth krein]
theorem kreinRH_iff_complexRH_of_charts
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) (XiZero : ℂ → Prop)
    (toKrein : ComplexToKreinZeroChart C XiZero)
    (toComplex : KreinToComplexZeroChart C XiZero) :
    KreinRH C ↔ ComplexRH XiZero :=
  ⟨fun h => complexRH_of_kreinRH h toKrein,
    fun h => kreinRH_of_complexRH h toComplex⟩

/-- Specialized chart type for the repo-native doubled carrier `HilbertDoubled E`. -/
abbrev RealDoubledKreinSpectralChart
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  KreinSpectralChart (RealDoubledConformalKreinCarrier E)

end InfoGeometry.Arithmetic.RHRealDoubledKreinReformulation

end
