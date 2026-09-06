import Mathlib

/-!
# InfoGeometry.Arithmetic.FiniteRiemannPrimeState

Finite Riemann/prime-state owner surface.

This module keeps the Latorre--Sierra style quantum-register state separate
from the bosonic/fermionic primon Fock gas:

* a finite state is a normalized weighted superposition over a finite support;
* the finite probability weights sum to `1`;
* Hardy--Littlewood entanglement, BRST, modular-invariance, CFT, and critical
  line claims are represented only by witness gates.

No infinite Hilbert-space state, analytic continuation theorem, BRST anomaly
cancellation theorem, Riemann Hypothesis statement, or CFT/bosonization theorem
is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.FiniteRiemannPrimeState

/-! ## 1. Finite Riemann-state normalization -/

/--
Finite squared norm of a weighted register state.

For a truncated Riemann state one later reads `w n` as a finite stand-in for
`|n^{-s}|`.
-/
def finiteRiemannNormSq
    {α : Type*}
    (A : Finset α)
    (w : α → ℝ) : ℝ :=
  ∑ a ∈ A, w a ^ 2

/--
Finite normalized probability attached to a weighted register state.

This is a probability readout, not a signed/Krein supertrace.
-/
def finiteRiemannProbability
    {α : Type*}
    (A : Finset α)
    (w : α → ℝ)
    (a : α) : ℝ :=
  w a ^ 2 / finiteRiemannNormSq A w

/--
The finite normalized probabilities sum to `1` when the finite norm is nonzero.
-/
theorem finiteRiemannProbability_sum_eq_one
    {α : Type*}
    (A : Finset α)
    (w : α → ℝ)
    (h : finiteRiemannNormSq A w ≠ 0) :
    ∑ a ∈ A, finiteRiemannProbability A w a = 1 := by
  unfold finiteRiemannProbability finiteRiemannNormSq
  rw [← Finset.sum_div]
  exact div_self h

/--
Finite prime-state packet.

The support can be all integers in a cutoff, or only primes in a cutoff.
Primality of the support is a predicate field, not built into the normalization
theorem.
-/
structure FiniteRiemannStatePacket where
  support : Finset ℕ
  weight : ℕ → ℝ
  normSq_nonzero : finiteRiemannNormSq support weight ≠ 0
  support_is_prime_lane : Prop

namespace FiniteRiemannStatePacket

variable (P : FiniteRiemannStatePacket)

/-- Finite squared norm of the packet. -/
def normSq : ℝ :=
  finiteRiemannNormSq P.support P.weight

/-- Finite probability weight of one register basis element. -/
def probability (n : ℕ) : ℝ :=
  finiteRiemannProbability P.support P.weight n

/-- The finite packet probabilities sum to `1`. -/
theorem probability_sum_eq_one :
    ∑ n ∈ P.support, P.probability n = 1 := by
  exact finiteRiemannProbability_sum_eq_one P.support P.weight P.normSq_nonzero

end FiniteRiemannStatePacket

/-! ## 2. Interpretation gates for entanglement and conformal structure -/

/--
Hardy--Littlewood entanglement witness gate.

This records a model-supplied relation between an entanglement readout and an
arithmetic correlation readout.  It is not derived from finite normalization.
-/
structure HardyLittlewoodEntanglementGate
    (EntanglementReadout CorrelationReadout : Type*) where
  entanglement : EntanglementReadout
  correlation : CorrelationReadout
  compare : EntanglementReadout → CorrelationReadout → Prop
  comparison_law : compare entanglement correlation

namespace HardyLittlewoodEntanglementGate

/-- Re-export of the supplied entanglement/correlation comparison. -/
theorem valid
    {EntanglementReadout CorrelationReadout : Type*}
    (G : HardyLittlewoodEntanglementGate EntanglementReadout CorrelationReadout) :
    G.compare G.entanglement G.correlation :=
  G.comparison_law

end HardyLittlewoodEntanglementGate

/--
BRST critical-line gate.

BRST nilpotence, anomaly cancellation, and any critical-line consequence are
model-dependent claims.  This structure records them as supplied witnesses
instead of proving RH-level consequences from the finite prime-state packet.
-/
structure BRSTCriticalLineGate
    (BRSTCharge StateSpace : Type*) where
  Q : BRSTCharge
  stateSpace : StateSpace
  nilpotence_law : Prop
  anomaly_cancellation_law : Prop
  critical_line_law : Prop
  certificate :
    nilpotence_law ∧ anomaly_cancellation_law ∧ critical_line_law

namespace BRSTCriticalLineGate

/-- The supplied BRST nilpotence law. -/
theorem nilpotent
    {BRSTCharge StateSpace : Type*}
    (G : BRSTCriticalLineGate BRSTCharge StateSpace) :
    G.nilpotence_law :=
  G.certificate.1

/-- The supplied BRST anomaly-cancellation law. -/
theorem anomaly_cancelled
    {BRSTCharge StateSpace : Type*}
    (G : BRSTCriticalLineGate BRSTCharge StateSpace) :
    G.anomaly_cancellation_law :=
  G.certificate.2.1

/-- The supplied critical-line law. -/
theorem critical_line
    {BRSTCharge StateSpace : Type*}
    (G : BRSTCriticalLineGate BRSTCharge StateSpace) :
    G.critical_line_law :=
  G.certificate.2.2

end BRSTCriticalLineGate

/--
Modular-invariance witness gate for a finite or completed Riemann-state model.

Finite normalization alone does not imply modular invariance.
-/
structure RiemannStateModularInvarianceGate
    (State Transform : Type*) where
  state : State
  transform : Transform
  modular_invariance_law : Prop
  certificate : modular_invariance_law

namespace RiemannStateModularInvarianceGate

/-- Re-export of the supplied modular-invariance law. -/
theorem valid
    {State Transform : Type*}
    (G : RiemannStateModularInvarianceGate State Transform) :
    G.modular_invariance_law :=
  G.certificate

end RiemannStateModularInvarianceGate

end InfoGeometry.Arithmetic.FiniteRiemannPrimeState

