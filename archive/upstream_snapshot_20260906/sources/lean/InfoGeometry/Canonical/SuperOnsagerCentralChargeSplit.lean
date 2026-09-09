import InfoGeometry.Canonical.SuperchargeCentralChargeClosure
import InfoGeometry.Canonical.SouriauMetriplecticContext
import InfoGeometry.Canonical.ObserverDefect
import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SuperOnsagerCentralChargeSplit

Theorem-facing scaffold for the super-Onsager `P/Z` split.

This file is intentionally modest. It does **not** claim that the full physical
statement

`{Q,Q} = P + Z`

has already been derived as an owner theorem on the current repo carrier. It
only provides a Lean-facing interface for reconciling the existing surfaces:

- the transported supercharge/central-charge closure lane,
- the Souriau metriplectic split between metric and Casimir directions,
- the observer-defect compression lane.

The intended reading is:

- `transportPart` models the even closure that contributes to transport,
- `centralPart` models the even closure that remains protected/defect-like,
- entropy production is carried by the transport lane,
- the central lane is entropy-inert / null / Casimir-like.
-/

namespace InfoGeometry.Canonical.SuperOnsagerCentralChargeSplit

open InfoGeometry.Canonical

universe u

/--
Minimal theorem-facing data for the decomposition of odd closure into a
transport-generating even lane and a central/protected lane.

`Odd` is the odd supercharge carrier and `Even` is the even carrier in which the
closure lands.  The map `oddClosure` is the abstract odd-odd closure channel.
The fields `transportPart` and `centralPart` are the two projections whose sum
reconstructs the closure.
-/
@[rep_depth transport]
structure SplitData (Odd Even : Type u) [Add Even] where
  oddClosure : Odd → Odd → Even
  transportPart : Odd → Odd → Even
  centralPart : Odd → Odd → Even
  oddClosure_eq_transport_add_central :
    ∀ q₁ q₂, oddClosure q₁ q₂ = transportPart q₁ q₂ + centralPart q₁ q₂

namespace SplitData

variable {Odd Even : Type u} [Add Even]
variable (S : SplitData Odd Even)

@[rep_depth transport]
theorem oddClosure_eq_transport_add_central_apply (q₁ q₂ : Odd) :
    S.oddClosure q₁ q₂ = S.transportPart q₁ q₂ + S.centralPart q₁ q₂ :=
  S.oddClosure_eq_transport_add_central q₁ q₂

end SplitData

/--
Entropy-channel interface for a `P/Z` split.

`entropyProduction` is a scalar entropy-production shadow.  The fields express
how the total entropy channel decomposes into a transport contribution and a
central contribution, together with the intended protection law on the central
lane.
-/
@[rep_depth thermo]
structure EntropySplit where
  entropyProduction : ℝ
  transportEntropy : ℝ
  centralEntropy : ℝ
  entropyProduction_eq_transport_plus_central :
    entropyProduction = transportEntropy + centralEntropy
  central_entropy_inert : centralEntropy = 0

namespace EntropySplit

variable (E : EntropySplit)

@[rep_depth thermo]
theorem entropyProduction_eq_transport (h : E.centralEntropy = 0 := E.central_entropy_inert) :
    E.entropyProduction = E.transportEntropy := by
  rw [E.entropyProduction_eq_transport_plus_central, h]
  simp

end EntropySplit

/--
Protected-lane proposition: the central part is read as defect-supported.

This is left as an external predicate because the exact carrier of the defect
lane varies across the repo (observer compression, Drazin defect support,
operatorial central shadow, etc.).
-/
@[rep_depth transport]
def IsDefectSupported {Even Defect : Type u}
    (embed : Even → Defect) (isSupported : Defect → Prop)
    (z : Even) : Prop :=
  isSupported (embed z)

/--
Theorem-facing packet for the super-Onsager `P/Z` split.

This packet does not claim the physical theorem has been fully discharged.  It
packages the intended roles of the two lanes in a form that downstream files can
state explicitly without collapsing transport and central residue into one
ontology.
-/
@[rep_depth transport]
structure SuperOnsagerSplit (Odd Even : Type u) [Add Even] where
  data : SplitData Odd Even
  entropy : EntropySplit
  transport_generates_entropy : entropy.transportEntropy = entropy.entropyProduction
  central_is_entropy_inert : entropy.centralEntropy = 0

namespace SuperOnsagerSplit

variable {Odd Even : Type u} [Add Even]
variable (S : SuperOnsagerSplit Odd Even)

@[rep_depth transport]
def oddClosure : Odd → Odd → Even := S.data.oddClosure

@[rep_depth transport]
def transportPart : Odd → Odd → Even := S.data.transportPart

@[rep_depth transport]
def centralPart : Odd → Odd → Even := S.data.centralPart

@[rep_depth transport]
theorem oddClosure_eq_transport_add_central (q₁ q₂ : Odd) :
    S.oddClosure q₁ q₂ = S.transportPart q₁ q₂ + S.centralPart q₁ q₂ :=
  S.data.oddClosure_eq_transport_add_central q₁ q₂

@[rep_depth thermo]
theorem centralEntropy_eq_zero :
    S.entropy.centralEntropy = 0 :=
  S.central_is_entropy_inert

@[rep_depth thermo]
theorem entropyProduction_eq_transportEntropy :
    S.entropy.entropyProduction = S.entropy.transportEntropy := by
  exact S.entropy.entropyProduction_eq_transport S.central_is_entropy_inert

/--
Compressed theorem-facing summary of the `P/Z` split.
-/
@[rep_depth transport]
theorem package (q₁ q₂ : Odd) :
    S.oddClosure q₁ q₂ = S.transportPart q₁ q₂ + S.centralPart q₁ q₂
      ∧ S.entropy.centralEntropy = 0
      ∧ S.entropy.entropyProduction = S.entropy.transportEntropy := by
  exact ⟨S.oddClosure_eq_transport_add_central q₁ q₂,
    S.centralEntropy_eq_zero,
    S.entropyProduction_eq_transportEntropy⟩

end SuperOnsagerSplit

/--
Abstract BPS-style degeneracy proposition for the protected central lane.

This is intentionally only a proposition-valued interface.  The current repo has
several honest ways a protected lane can appear (Casimir vanishing,
metric-nullity, defect compression, transport-invariant index), and we should
not force them into a fake single proof before the owner theorem exists.
-/
@[rep_depth transport]
def ProtectedDegeneracy {Central MetricWitness : Type u}
    (witness : Central → MetricWitness) (isDegenerate : MetricWitness → Prop) : Prop :=
  ∀ z, isDegenerate (witness z)

/--
A tiny constructor for the common intended case: zero central entropy means the
transport lane carries the full entropy-production shadow.
-/
@[rep_depth thermo]
def mkEntropySplit (transportEntropy : ℝ) : EntropySplit where
  entropyProduction := transportEntropy
  transportEntropy := transportEntropy
  centralEntropy := 0
  entropyProduction_eq_transport_plus_central := by simp
  central_entropy_inert := rfl

@[rep_depth thermo]
theorem mkEntropySplit_transport_generates_entropy (x : ℝ) :
    (mkEntropySplit x).transportEntropy = (mkEntropySplit x).entropyProduction := rfl

/--
Operatorial specialization of the `P/Z` split: the even carrier is taken to be
an actual endomorphism algebra `Module.End ℝ H`.
-/
@[rep_depth transport]
structure OperatorialSplitData (Odd H : Type u)
    [AddCommMonoid H] [Module ℝ H] where
  toSplitData : SplitData Odd (Module.End ℝ H)

namespace OperatorialSplitData

variable {Odd H : Type u}
variable [AddCommMonoid H] [Module ℝ H]
variable (S : OperatorialSplitData Odd H)

@[rep_depth transport]
def oddClosure : Odd → Odd → Module.End ℝ H := S.toSplitData.oddClosure

@[rep_depth transport]
def transportPart : Odd → Odd → Module.End ℝ H := S.toSplitData.transportPart

@[rep_depth transport]
def centralPart : Odd → Odd → Module.End ℝ H := S.toSplitData.centralPart

@[rep_depth transport]
theorem oddClosure_apply_eq_transport_add_central
    (q₁ q₂ : Odd) (ψ : H) :
    S.oddClosure q₁ q₂ ψ = S.transportPart q₁ q₂ ψ + S.centralPart q₁ q₂ ψ := by
  exact congrArg (fun T : Module.End ℝ H => T ψ)
    (S.toSplitData.oddClosure_eq_transport_add_central q₁ q₂)

end OperatorialSplitData

section RepoAdapters

open InfoGeometry.Canonical.SouriauMetriplectic
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.ObserverDefect
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein

/--
Repo-native entropy adapter: a metriplectic context induces the intended `P/Z`
entropy split by assigning the full entropy-production shadow to the metric
transport lane and zero to the protected central lane.
-/
@[rep_depth thermo]
noncomputable def EntropySplit.ofMetriplecticContext
    {α : Type _} [Fintype α] [Nonempty α]
    (C : SouriauMetriplectic.MetriplecticContext (α := α)) : EntropySplit :=
  mkEntropySplit (C.metricEntropyProduction)

/--
On the finite Souriau metriplectic lane, total entropy production is exactly the
transport entropy of the induced `P/Z` split.
-/
@[rep_depth thermo]
theorem EntropySplit.ofMetriplecticContext_total_eq_transport
    {α : Type _} [Fintype α] [Nonempty α]
    (C : SouriauMetriplectic.MetriplecticContext (α := α)) :
    C.totalEntropyProduction = (EntropySplit.ofMetriplecticContext C).transportEntropy := by
  rw [SouriauMetriplectic.MetriplecticContext.totalEntropyProduction_eq_metric]
  simp [EntropySplit.ofMetriplecticContext, mkEntropySplit]

/--
The induced central lane on a finite metriplectic context is entropy-inert.
-/
@[rep_depth thermo]
theorem EntropySplit.ofMetriplecticContext_central_eq_zero
    {α : Type _} [Fintype α] [Nonempty α]
    (C : SouriauMetriplectic.MetriplecticContext (α := α)) :
    (EntropySplit.ofMetriplecticContext C).centralEntropy = 0 := by
  rfl

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E

/--
Repo-native central-charge protection law: nonvanishing of the operatorial
central charge persists across every Bogoliubov transport slice.
-/
@[rep_depth transport]
theorem operatorialCentralCharge_nonvanishing_transport_protected
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    {s t : ℝ}
    (hs :
      quasilatticeAnalyticalIndex V X s
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s)
        ≠ 0) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      ≠ 0 :=
  quasilatticeSlice_ne_zero_transport_protected
    (A := A) (B := B) (E := E) V X hX hEven hs

/--
Repo-native defect adapter: after defect compression, only the observer
projector-deviation commutator remains.
-/
@[rep_depth transport]
theorem observerDefectResidual_eq_deviation_only
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    observerDefectResidual CIK obs
      =
    CIK.spectralComplementaryProjector *
      DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
      CIK.spectralComplementaryProjector := by
  exact observerDefectResidual_eq_projectorCompression_commutator_deviation
    (CIK := CIK) (obs := obs)

/--
Repo-native central-defect principle.

This packages the three currently honest lanes behind the `P/Z` interpretation:

1. the finite metriplectic total entropy is entirely carried by the transport lane;
2. nonzero operatorial central charge is transport-protected across Bogoliubov slices;
3. after observer defect compression, only the deviation commutator remains.
-/
@[rep_depth transport]
theorem central_defect_principle
    {α : Type _} [Fintype α] [Nonempty α]
    (C : SouriauMetriplectic.MetriplecticContext (α := α))
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    {s t : ℝ}
    (hs :
      quasilatticeAnalyticalIndex V X s
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s)
        ≠ 0)
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    C.totalEntropyProduction = (EntropySplit.ofMetriplecticContext C).transportEntropy
      ∧ (EntropySplit.ofMetriplecticContext C).centralEntropy = 0
      ∧ quasilatticeAnalyticalIndex V X t
          (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
          ≠ 0
      ∧ observerDefectResidual CIK obs
          = CIK.spectralComplementaryProjector *
              DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
              CIK.spectralComplementaryProjector := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact EntropySplit.ofMetriplecticContext_total_eq_transport C
  · exact EntropySplit.ofMetriplecticContext_central_eq_zero C
  · exact operatorialCentralCharge_nonvanishing_transport_protected
      (A := A) (B := B) (E := E) V X hX hEven hs
  · exact observerDefectResidual_eq_deviation_only (E := E) CIK obs

end RepoAdapters

end InfoGeometry.Canonical.SuperOnsagerCentralChargeSplit
