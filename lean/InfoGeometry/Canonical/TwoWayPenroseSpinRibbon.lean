import Mathlib.Analysis.Complex.Exponential
import InfoGeometry.Canonical.DiscretePenroseSpinNet
import InfoGeometry.Canonical.FiniteAmbitwistorPairing
import InfoGeometry.Quantum.TraceFormula

/-!
# Two-way discrete spin ribbons and phase-conjugate cancellation

This module reuses the repository's ordered Penrose `SpinNet` and finite
ambitwistor pairing.  A ribbon is an ordered, bipartite incidence datum with
an SU(2)-style doubled spin label.  The wave result below is conditional
algebra: a phase and its complex conjugate cancel in a dyad.  It does not
assert a graph propagation equation or a physical time-reversal law.
-/

namespace InfoGeometry.Canonical.TwoWayPenroseSpinRibbon

open InfoGeometry.Canonical.DiscretePenroseSpinNet

universe u

section Ribbon

variable {α : Type u} [PartialOrder α]
variable {𝕜 T D : Type u} [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]
variable {S : SpinNet α 𝕜 T D} {black white : α → Prop}

/-- Ribbon data over the event set. `twiceJ` and `twiceM` encode twice the
usual half-integral labels. Admissibility conditions are stated separately. -/
structure Ribbon where
  source : α
  target : α
  twiceJ : ℕ
  twiceM : ℤ

/-- Conditions making ribbon data a directed bipartite spin ribbon over `S`.
The spin labels use the standard doubled-spin bound and parity condition. -/
def IsAdmissibleRibbon (S : SpinNet α 𝕜 T D) (black white : α → Prop)
    (e : Ribbon (α := α)) : Prop :=
  black e.source ∧ white e.target ∧ e.source ≤ e.target ∧
    e.twiceM.natAbs ≤ e.twiceJ ∧
    e.twiceJ % 2 = e.twiceM.natAbs % 2 ∧
    S.twistorIncidence.Incidence (S.dualAt e.source) (S.twistorAt e.target)

/-- The oriented forward strand of a ribbon. -/
def forwardStrand (e : Ribbon (α := α)) : α × α :=
  (e.source, e.target)

/-- The same ribbon traversed in the reverse direction. -/
def backwardStrand (e : Ribbon (α := α)) : α × α :=
  (e.target, e.source)

omit [PartialOrder α] in
@[simp] theorem backwardStrand_swap (e : Ribbon (α := α)) :
    backwardStrand e = (forwardStrand e).swap := rfl

/-- The ordered endpoints carry the incidence already supplied by `SpinNet`. -/
theorem ribbon_incidence (e : Ribbon (α := α)) (h : e.source ≤ e.target) :
    S.twistorIncidence.Incidence (S.dualAt e.source) (S.twistorAt e.target) :=
  DiscretePenroseSpinNet.incidence_of_le S h

end Ribbon

section TwistorPairing

open InfoGeometry.Canonical.FiniteAmbitwistorPairing

/-- A ribbon's finite ambitwistor label is null when its existing dual/twistor
pairing vanishes. This is a definition of the condition, not a claim that all
spin-net incidences are null pairs. -/
def ribbonNullCondition (W : DualTwistor4) (Z : Twistor4) : Prop :=
  IsNullPair W Z

theorem ribbonNullCondition_iff (W : DualTwistor4) (Z : Twistor4) :
    ribbonNullCondition W Z ↔ pairing W Z = 0 := Iff.rfl

end TwistorPairing

section PhaseCancellation

/-- The product of a unit complex amplitude and its conjugate is one. -/
theorem phase_conjugate_mul_eq_one (z : ℂ) (hz : star z * z = 1) :
    z * star z = 1 := by
  calc
    z * star z = star z * z := mul_comm _ _
    _ = 1 := hz

/-- A ket-bra dyad with a unit forward amplitude and conjugate backward
amplitude is unchanged. This is an algebraic phase cancellation theorem; it
does not assert that a physical system supplies such amplitudes. -/
theorem phase_conjugate_dyad_cancel (ket bra z : ℂ)
    (hz : star z * z = 1) :
    (z * ket) * (star z * bra) = ket * bra := by
  calc
    (z * ket) * (star z * bra) = (z * star z) * (ket * bra) := by ring
    _ = ket * bra := by rw [phase_conjugate_mul_eq_one z hz, one_mul]

/-- The corresponding cancellation law in a possibly noncommutative operator
ring.  The backward amplitude must commute with the ket factor, as happens for
a central scalar phase.  No commutativity of the ambient ring is assumed. -/
theorem operator_phase_dyad_cancel {A : Type*} [Ring A]
    (forward backward ket bra : A)
    (h_inverse : forward * backward = 1)
    (h_backward_central_on_ket : backward * ket = ket * backward) :
    (forward * ket) * (backward * bra) = ket * bra := by
  calc
    (forward * ket) * (backward * bra) =
        forward * (ket * backward) * bra := by noncomm_ring
    _ = forward * (backward * ket) * bra := by
      rw [← h_backward_central_on_ket]
    _ = (forward * backward) * (ket * bra) := by noncomm_ring
    _ = ket * bra := by rw [h_inverse, one_mul]

/-- Opposite harmonic frequencies cancel exactly. This reuses the repository's
`spectralTracePhase` owner rather than introducing a second phase convention. -/
theorem opposite_frequency_phase_mul (γ t : ℝ) :
    InfoGeometry.Quantum.TraceFormula.spectralTracePhase γ t *
        InfoGeometry.Quantum.TraceFormula.spectralTracePhase (-γ) t = 1 := by
  unfold InfoGeometry.Quantum.TraceFormula.spectralTracePhase
  rw [← Complex.exp_add]
  have harg : Complex.I * ((γ * t : ℝ) : ℂ) +
      Complex.I * (((-γ) * t : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [harg, Complex.exp_zero]

/-- Forward phase accumulated along a finite set of edge labels. -/
noncomputable def forwardPathPhase {ι : Type*} (edges : Finset ι)
    (γ : ι → ℝ) (t : ℝ) : ℂ :=
  edges.prod fun e =>
    InfoGeometry.Quantum.TraceFormula.spectralTracePhase (γ e) t

/-- Backward, opposite-frequency phase accumulated over the same finite edge
set. -/
noncomputable def backwardPathPhase {ι : Type*} (edges : Finset ι)
    (γ : ι → ℝ) (t : ℝ) : ℂ :=
  edges.prod fun e =>
    InfoGeometry.Quantum.TraceFormula.spectralTracePhase (-γ e) t

/-- Edgewise opposite frequencies cancel after multiplication along any finite
path index set. This is a finite-product consequence of
`opposite_frequency_phase_mul`. -/
theorem path_phase_cancellation {ι : Type*} (edges : Finset ι)
    (γ : ι → ℝ) (t : ℝ) :
    forwardPathPhase edges γ t * backwardPathPhase edges γ t = 1 := by
  unfold forwardPathPhase backwardPathPhase
  rw [← Finset.prod_mul_distrib]
  simp [opposite_frequency_phase_mul]

/-- The dyad formed from opposite-frequency harmonic modes is independent of
the phase parameter `t`. This is a scalar identity; no lattice evolution law
is assumed. -/
noncomputable def harmonicDyad (ket bra : ℂ) (γ t : ℝ) : ℂ :=
  (InfoGeometry.Quantum.TraceFormula.spectralTracePhase γ t * ket) *
    (InfoGeometry.Quantum.TraceFormula.spectralTracePhase (-γ) t * bra)

theorem harmonicDyad_eq_ket_mul_bra (ket bra : ℂ) (γ t : ℝ) :
    harmonicDyad ket bra γ t = ket * bra := by
  unfold harmonicDyad
  calc
    (InfoGeometry.Quantum.TraceFormula.spectralTracePhase γ t * ket) *
        (InfoGeometry.Quantum.TraceFormula.spectralTracePhase (-γ) t * bra) =
        (InfoGeometry.Quantum.TraceFormula.spectralTracePhase γ t *
          InfoGeometry.Quantum.TraceFormula.spectralTracePhase (-γ) t) *
          (ket * bra) := by ring
    _ = ket * bra := by rw [opposite_frequency_phase_mul, one_mul]

theorem harmonicDyad_time_independent (ket bra : ℂ) (γ t₁ t₂ : ℝ) :
    harmonicDyad ket bra γ t₁ = harmonicDyad ket bra γ t₂ := by
  rw [harmonicDyad_eq_ket_mul_bra, harmonicDyad_eq_ket_mul_bra]

end PhaseCancellation

end InfoGeometry.Canonical.TwoWayPenroseSpinRibbon
