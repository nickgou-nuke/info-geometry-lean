import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.TomitaDissipativeBreak

Minimal formal corridor separating:

* reversible Tomita-style invariant flow (group-like stationarity), and
* dissipative semigroup-style monotone flow (arrow of time).
-/

namespace InfoGeometry.Canonical.TomitaDissipativeBreak

/-- Minimal metriplectic packet over real-valued observables. -/
structure MetriplecticSystem (A : Type*) where
  bracketP : A → A → ℝ
  bracketM : A → A → ℝ
  bracketP_self_zero : ∀ x : A, bracketP x x = 0
  bracketM_symm : ∀ x y : A, bracketM x y = bracketM y x
  H : A
  S : A
  bracketM_H_right_zero : ∀ x : A, bracketM x H = 0
  bracketP_S_right_zero : ∀ x : A, bracketP x S = 0
  bracketP_S_left_zero : ∀ x : A, bracketP S x = 0

/-- Unified Leibniz-type metriplectic bracket. -/
def MetriplecticSystem.leibniz {A : Type*} (sys : MetriplecticSystem A) (x y : A) : ℝ :=
  sys.bracketP x y + sys.bracketM x y

/--
First-law channel: the Hamiltonian is conserved by the unified bracket.
-/
theorem MetriplecticSystem.dH_eq_zero
    {A : Type*} (sys : MetriplecticSystem A) :
    sys.leibniz sys.H sys.H = 0 := by
  unfold MetriplecticSystem.leibniz
  rw [sys.bracketP_self_zero, sys.bracketM_H_right_zero]
  ring

/--
Second-law readout: entropy production along Hamiltonian-driven evolution is
exactly the metric channel because entropy is Poisson-Casimir.
-/
theorem MetriplecticSystem.dS_eq_metric_channel
    {A : Type*} (sys : MetriplecticSystem A) :
    sys.leibniz sys.S sys.H = sys.bracketM sys.S sys.H := by
  unfold MetriplecticSystem.leibniz
  rw [sys.bracketP_S_left_zero]
  ring

/--
If the metric entropy channel is nonnegative, entropy production is nonnegative.
-/
theorem MetriplecticSystem.dS_nonneg_of_metric_channel_nonneg
    {A : Type*} (sys : MetriplecticSystem A)
    (hNonneg : 0 ≤ sys.bracketM sys.S sys.H) :
    0 ≤ sys.leibniz sys.S sys.H := by
  rw [sys.dS_eq_metric_channel]
  exact hNonneg

/--
If both conservative and dissipative self-channels on entropy vanish, then
entropy is stationary under the unified bracket against itself.
-/
theorem MetriplecticSystem.dS_self_eq_zero_of_self_channels
    {A : Type*} (sys : MetriplecticSystem A)
    (hP : sys.bracketP sys.S sys.S = 0)
    (hM : sys.bracketM sys.S sys.S = 0) :
    sys.leibniz sys.S sys.S = 0 := by
  unfold MetriplecticSystem.leibniz
  rw [hP, hM]
  ring

/-- Minimal supergraded metriplectic packet with explicit sign factor. -/
structure SupergradedMetriplecticSystem (A : Type*) where
  degreeF : A → ℤ
  degreeD : A → ℤ
  signFactor : ℤ → ℤ → ℤ → ℤ → ℝ
  bracketP : A → A → ℝ
  bracketM : A → A → ℝ
  bracketP_graded_skew :
    ∀ x y : A,
      bracketP x y
        = - (signFactor (degreeF x) (degreeD x) (degreeF y) (degreeD y)) * bracketP y x
  bracketM_graded_symm :
    ∀ x y : A,
      bracketM x y
        = (signFactor (degreeF x) (degreeD x) (degreeF y) (degreeD y)) * bracketM y x
  bracketP_self_zero : ∀ x : A, bracketP x x = 0
  H : A
  S : A
  bracketM_H_right_zero : ∀ x : A, bracketM x H = 0
  bracketP_S_left_zero : ∀ x : A, bracketP S x = 0

/-- Unified graded Leibniz-type bracket. -/
def SupergradedMetriplecticSystem.leibniz
    {A : Type*} (sys : SupergradedMetriplecticSystem A) (x y : A) : ℝ :=
  sys.bracketP x y + sys.bracketM x y

/-- Graded first-law channel at the minimal theorem surface. -/
theorem SupergradedMetriplecticSystem.dH_eq_zero
    {A : Type*} (sys : SupergradedMetriplecticSystem A) :
    sys.leibniz sys.H sys.H = 0 := by
  unfold SupergradedMetriplecticSystem.leibniz
  rw [sys.bracketP_self_zero, sys.bracketM_H_right_zero]
  ring

/-- Graded entropy channel reduces to the metric block via graded Casimir. -/
theorem SupergradedMetriplecticSystem.dS_eq_metric_channel
    {A : Type*} (sys : SupergradedMetriplecticSystem A) :
    sys.leibniz sys.S sys.H = sys.bracketM sys.S sys.H := by
  unfold SupergradedMetriplecticSystem.leibniz
  rw [sys.bracketP_S_left_zero]
  ring

/-- Nonnegativity transfer for the graded entropy-production channel. -/
theorem SupergradedMetriplecticSystem.dS_nonneg_of_metric_channel_nonneg
    {A : Type*} (sys : SupergradedMetriplecticSystem A)
    (hNonneg : 0 ≤ sys.bracketM sys.S sys.H) :
    0 ≤ sys.leibniz sys.S sys.H := by
  rw [sys.dS_eq_metric_channel]
  exact hNonneg

/-- Parabolic (`Ω² = 0`) dual-number style operator packet. -/
structure ParabolicOperator where
  scalar : ℝ
  nilpotent : ℝ

namespace ParabolicOperator

/-- Chiral transmission channels for the photonic readout model. -/
inductive ChiralChannel
  | E_plus
  | E_minus
  | Parabolic
  deriving DecidableEq, Repr

/-- Unit element in the parabolic algebra. -/
def one : ParabolicOperator := ⟨1, 0⟩

/-- Nilpotent generator `Ω` with `Ω² = 0`. -/
def omega : ParabolicOperator := ⟨0, 1⟩

/--
Multiplication in the square-zero parabolic algebra:
`(a + bΩ)(c + dΩ) = ac + (ad + bc)Ω`, with `Ω² = 0`.
-/
def mul (A B : ParabolicOperator) : ParabolicOperator :=
  ⟨A.scalar * B.scalar, A.scalar * B.nilpotent + A.nilpotent * B.scalar⟩

/--
Exact parabolic exponential:
`exp(a + bΩ) = exp(a) * (1 + bΩ)`.
-/
noncomputable def exp (V : ParabolicOperator) : ParabolicOperator :=
  let e := Real.exp V.scalar
  ⟨e, e * V.nilpotent⟩

/-- Additive carrier for the dual-number coordinates. -/
def add (A B : ParabolicOperator) : ParabolicOperator :=
  ⟨A.scalar + B.scalar, A.nilpotent + B.nilpotent⟩

/-- Chiral-parabolic plus channel `(1 + Ω)/2`. -/
noncomputable def pPlus : ParabolicOperator := ⟨(1 : ℝ) / 2, (1 : ℝ) / 2⟩

/-- Chiral-parabolic minus channel `(1 - Ω)/2`. -/
noncomputable def pMinus : ParabolicOperator := ⟨(1 : ℝ) / 2, -(1 : ℝ) / 2⟩

/-- The parabolic generator is square-zero. -/
theorem omega_square_zero : mul omega omega = ⟨0, 0⟩ := by
  unfold omega mul
  norm_num

/--
Parabolic chiral channel square law:
`P₊² = ((1 + 2Ω)/4)` in dual-number coordinates.
-/
theorem pPlus_square_formula :
    mul pPlus pPlus = ⟨(1 : ℝ) / 4, (1 : ℝ) / 2⟩ := by
  unfold pPlus mul
  norm_num

/--
Parabolic chiral channel square law:
`P₋² = ((1 - 2Ω)/4)` in dual-number coordinates.
-/
theorem pMinus_square_formula :
    mul pMinus pMinus = ⟨(1 : ℝ) / 4, -((1 : ℝ) / 2)⟩ := by
  unfold pMinus mul
  norm_num

/-- In the parabolic case, `P₊` is not idempotent. -/
theorem pPlus_not_idempotent : mul pPlus pPlus ≠ pPlus := by
  intro h
  have hs : ((mul pPlus pPlus).scalar) = pPlus.scalar := congrArg ParabolicOperator.scalar h
  norm_num [pPlus, mul] at hs

/-- In the parabolic case, `P₋` is not idempotent. -/
theorem pMinus_not_idempotent : mul pMinus pMinus ≠ pMinus := by
  intro h
  have hs : ((mul pMinus pMinus).scalar) = pMinus.scalar := congrArg ParabolicOperator.scalar h
  norm_num [pMinus, mul] at hs

/--
Proof-directed channel classifier for the parabolic dual-number model.
Supplying a square-zero property classifies the carrier as `Parabolic`.
-/
def channelOfNilpotent (V : ParabolicOperator) (_h : mul V V = ⟨0, 0⟩) : ChiralChannel :=
  ChiralChannel.Parabolic

/-- The canonical nilpotent generator is classified as `Parabolic`. -/
theorem channelOfNilpotent_omega_eq_parabolic :
    channelOfNilpotent omega omega_square_zero = ChiralChannel.Parabolic := rfl

/--
Parabolic contraction theorem (concrete packet):
if `V² = 0`, then the channel classifier collapses to `Parabolic`.
-/
theorem chiral_collapse_to_parabolic
    (V : ParabolicOperator) (h_nilpotent : mul V V = ⟨0, 0⟩) :
    channelOfNilpotent V h_nilpotent = ChiralChannel.Parabolic := rfl

/--
Owner-side algebraic fact in the parabolic corridor:
if `V² = 0` in the dual-number product, then the scalar part of `V` is zero.
-/
theorem scalar_eq_zero_of_square_zero
    (V : ParabolicOperator) (h_nilpotent : mul V V = ⟨0, 0⟩) :
    V.scalar = 0 := by
  have hs : (mul V V).scalar = (0 : ℝ) := by
    exact congrArg ParabolicOperator.scalar h_nilpotent
  have hs' : V.scalar * V.scalar = 0 := by
    simpa [mul] using hs
  exact mul_self_eq_zero.mp hs'

/--
Exact square-zero characterization in the parabolic dual-number algebra:
`V² = 0` iff the scalar component vanishes.
-/
theorem square_zero_iff_scalar_zero (V : ParabolicOperator) :
    mul V V = ⟨0, 0⟩ ↔ V.scalar = 0 := by
  constructor
  · exact scalar_eq_zero_of_square_zero V
  · intro h0
    cases V with
    | mk a b =>
      dsimp at h0
      subst h0
      unfold mul
      simp

/--
Concrete photonic contraction packet:
an operator carrier together with a square-zero property.
-/
structure PhotonicParabolicPacket where
  Ω : ParabolicOperator
  h_nilpotent : mul Ω Ω = ⟨0, 0⟩

/-- The induced active transmission channel for the packet. -/
def PhotonicParabolicPacket.currentChannel (P : PhotonicParabolicPacket) : ChiralChannel :=
  channelOfNilpotent P.Ω P.h_nilpotent

/--
Channel-collapse theorem for the concrete packet:
square-zero contraction forces the `Parabolic` channel.
-/
theorem PhotonicParabolicPacket.currentChannel_eq_parabolic
    (P : PhotonicParabolicPacket) :
    P.currentChannel = ChiralChannel.Parabolic := by
  unfold PhotonicParabolicPacket.currentChannel
  rfl

/--
Nilpotent-parabolic exponential homomorphism:
`exp(A + B) = exp(A) * exp(B)`.
-/
theorem exp_homomorphism (A B : ParabolicOperator) :
    exp (add A B) = mul (exp A) (exp B) := by
  cases A with
  | mk a b =>
    cases B with
    | mk c d =>
      unfold exp add mul
      simp [Real.exp_add, mul_add]
      ring

end ParabolicOperator

/-- Reversible modular packet: the potential is invariant along the flow. -/
structure TomitaEquilibrium (StateSpace : Type*) where
  modularPotential : StateSpace → ℝ
  flow : ℝ → StateSpace → StateSpace
  flow_invariant : ∀ (t : ℝ) (ρ : StateSpace),
    modularPotential (flow t ρ) = modularPotential ρ

/--
Along a pure Tomita-invariant trajectory, the potential is constant in time,
hence has derivative `0` at every time.
-/
theorem tomita_static_hasDerivAt
    {S : Type*} (env : TomitaEquilibrium S) (ρ : S) (t : ℝ) :
    HasDerivAt (fun time => env.modularPotential (env.flow time ρ)) 0 t := by
  have hconst :
      (fun time => env.modularPotential (env.flow time ρ))
        = (fun _ => env.modularPotential ρ) := by
    funext time
    exact env.flow_invariant time ρ
  rw [hconst]
  simpa using (hasDerivAt_const (x := t) (c := env.modularPotential ρ))

/--
Pure Tomita invariance forbids strict forward decay of the modular potential
at any time: values at `t` and `0` are equal.
-/
theorem tomita_no_strict_decay
    {S : Type*} (env : TomitaEquilibrium S) (ρ : S) (t : ℝ) :
    ¬ env.modularPotential (env.flow t ρ) < env.modularPotential (env.flow 0 ρ) := by
  have hEq0 : env.modularPotential (env.flow 0 ρ) = env.modularPotential ρ :=
    env.flow_invariant 0 ρ
  have hEqt : env.modularPotential (env.flow t ρ) = env.modularPotential ρ :=
    env.flow_invariant t ρ
  intro hlt
  rw [hEqt, hEq0] at hlt
  exact lt_irrefl _ hlt

/--
Tomita invariance identifies all time slices along a trajectory at the level
of modular potential.
-/
theorem tomita_potential_eq_at_times
    {S : Type*} (env : TomitaEquilibrium S) (ρ : S) (t₁ t₂ : ℝ) :
    env.modularPotential (env.flow t₁ ρ) = env.modularPotential (env.flow t₂ ρ) := by
  calc
    env.modularPotential (env.flow t₁ ρ) = env.modularPotential ρ := env.flow_invariant t₁ ρ
    _ = env.modularPotential (env.flow t₂ ρ) := (env.flow_invariant t₂ ρ).symm

/--
Any forward-order comparison in a Tomita-equilibrium trajectory is saturated:
for `t₁ ≤ t₂`, the endpoint potentials are equal.
-/
theorem tomita_forward_order_saturates
    {S : Type*} (env : TomitaEquilibrium S) (ρ : S)
    {t₁ t₂ : ℝ} (_ht : t₁ ≤ t₂) :
    env.modularPotential (env.flow t₂ ρ) = env.modularPotential (env.flow t₁ ρ) := by
  simpa [eq_comm] using tomita_potential_eq_at_times env ρ t₁ t₂

/-- Dissipative packet: Lyapunov potential is monotone nonincreasing in time. -/
structure DissipativeFlow (StateSpace : Type*) where
  potential : StateSpace → ℝ
  flow : ℝ → StateSpace → StateSpace
  monotone_forward :
    ∀ (ρ : StateSpace) {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
      potential (flow t₂ ρ) ≤ potential (flow t₁ ρ)

/--
Every Tomita-equilibrium packet canonically induces a dissipative packet:
forward monotonicity is witnessed by equality of time slices.
-/
def dissipativeFlowOfTomita
    {S : Type*} (env : TomitaEquilibrium S) : DissipativeFlow S where
  potential := env.modularPotential
  flow := env.flow
  monotone_forward := by
    intro ρ t₁ t₂ ht
    simp [tomita_forward_order_saturates (env := env) (ρ := ρ) (t₁ := t₁) (t₂ := t₂) ht]

/-- Forward-time contraction to the `t = 0` reference slice. -/
theorem dissipative_potential_le_initial
    {S : Type*} (env : DissipativeFlow S) (ρ : S) {t : ℝ} (ht : 0 ≤ t) :
    env.potential (env.flow t ρ) ≤ env.potential (env.flow 0 ρ) := by
  simpa using env.monotone_forward ρ ht

/--
In a dissipative forward-monotone flow, potential cannot increase as time
advances.
-/
theorem dissipative_no_forward_increase
    {S : Type*} (env : DissipativeFlow S) (ρ : S) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    ¬ env.potential (env.flow t₁ ρ) < env.potential (env.flow t₂ ρ) := by
  have hle : env.potential (env.flow t₂ ρ) ≤ env.potential (env.flow t₁ ρ) :=
    env.monotone_forward ρ ht
  exact not_lt_of_ge hle

/--
If a flow is monotone both forward and backward in time, then the potential is
constant along trajectories.
-/
theorem potential_constant_of_two_sided_monotone
    {S : Type*}
    (env : DissipativeFlow S)
    (hBackward :
      ∀ (ρ : S) {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
        env.potential (env.flow t₁ ρ) ≤ env.potential (env.flow t₂ ρ))
    (ρ : S) (t : ℝ) :
    env.potential (env.flow t ρ) = env.potential (env.flow 0 ρ) := by
  have h1 : env.potential (env.flow t ρ) ≤ env.potential (env.flow 0 ρ) := by
    by_cases h0t : 0 ≤ t
    · simpa using env.monotone_forward ρ h0t
    · have ht0 : t ≤ 0 := le_of_not_ge h0t
      simpa using hBackward ρ ht0
  have h2 : env.potential (env.flow 0 ρ) ≤ env.potential (env.flow t ρ) := by
    by_cases h0t : 0 ≤ t
    · simpa using hBackward ρ h0t
    · have ht0 : t ≤ 0 := le_of_not_ge h0t
      simpa using env.monotone_forward ρ ht0
  exact le_antisymm h1 h2

/--
Two-sided monotonicity reconstructs a Tomita-style invariant packet:
the same flow/potential can be viewed as equilibrium because each trajectory
has constant potential.
-/
def tomitaEquilibriumOfTwoSidedMonotone
    {S : Type*}
    (env : DissipativeFlow S)
    (hFlowZero : ∀ ρ : S, env.flow 0 ρ = ρ)
    (hBackward :
      ∀ (ρ : S) {t₁ t₂ : ℝ}, t₁ ≤ t₂ →
        env.potential (env.flow t₁ ρ) ≤ env.potential (env.flow t₂ ρ)) :
    TomitaEquilibrium S where
  modularPotential := env.potential
  flow := env.flow
  flow_invariant := by
    intro t ρ
    calc
      env.potential (env.flow t ρ) = env.potential (env.flow 0 ρ) := by
        simpa using potential_constant_of_two_sided_monotone env hBackward ρ t
      _ = env.potential ρ := by rw [hFlowZero ρ]

end InfoGeometry.Canonical.TomitaDissipativeBreak
