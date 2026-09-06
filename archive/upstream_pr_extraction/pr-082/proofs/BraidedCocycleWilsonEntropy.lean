import proofs.InfiniteLightConeConfColimit

/-!
# Braided edge cocycles, Wilson cycles, and entropy production

Finite theorem-honest scaffold for the user's dictionary:

* edges as oriented one-cochains/cocycles,
* `aᵢⱼ` ratios as edge transports,
* `log aᵢⱼ` as entropy affinities,
* Wilson cycle/circulation as the obstruction to detailed balance,
* braid moves as finite permutations of oriented edges,
* spin-network labels as finite edge decorations.

No analytic logarithm, path integral, Wilson-loop physics, or Markov process is
asserted here.  Those are external targets.  The kernel only proves finite graph
identities on the triangle underlying the arity-three light-cone model.
-/

namespace BraidedCocycleWilsonEntropy

open LightConeConf3DeRhamCooperad

/-- The six oriented edges of the three-point graph. -/
inductive OrientedEdge3 where
  | e12 | e21 | e13 | e31 | e23 | e32
  deriving DecidableEq, Fintype, Repr

/-- Reverse an oriented edge. -/
def reverse : OrientedEdge3 → OrientedEdge3
  | OrientedEdge3.e12 => OrientedEdge3.e21
  | OrientedEdge3.e21 => OrientedEdge3.e12
  | OrientedEdge3.e13 => OrientedEdge3.e31
  | OrientedEdge3.e31 => OrientedEdge3.e13
  | OrientedEdge3.e23 => OrientedEdge3.e32
  | OrientedEdge3.e32 => OrientedEdge3.e23

@[simp] theorem reverse_reverse : ∀ e : OrientedEdge3, reverse (reverse e) = e := by
  intro e
  cases e <;> rfl

/-- Forget orientation and recover the underlying arity-three edge. -/
def forgetOrientation : OrientedEdge3 → Edge3
  | OrientedEdge3.e12 | OrientedEdge3.e21 => Edge3.e12
  | OrientedEdge3.e13 | OrientedEdge3.e31 => Edge3.e13
  | OrientedEdge3.e23 | OrientedEdge3.e32 => Edge3.e23

@[simp] theorem forget_reverse (e : OrientedEdge3) :
    forgetOrientation (reverse e) = forgetOrientation e := by
  cases e <;> rfl

/-- A finite logarithmic edge affinity/cochain.  Think formally of
`Lᵢⱼ = log aᵢⱼ`; no analytic logarithm is used. -/
abbrev LogAffinity := OrientedEdge3 → ℤ

/-- Antisymmetry is the formal shadow of `log aⱼᵢ = - log aᵢⱼ`. -/
def Antisymmetric (L : LogAffinity) : Prop :=
  ∀ e, L (reverse e) = - L e

/-- Wilson/entropy circulation around the oriented triangle `1→2→3→1`. -/
def triangleWilson (L : LogAffinity) : ℤ :=
  L OrientedEdge3.e12 + L OrientedEdge3.e23 + L OrientedEdge3.e31

/-- Flat cocycle condition on the triangle: the Wilson circulation vanishes. -/
def TriangleCocycle (L : LogAffinity) : Prop :=
  triangleWilson L = 0

/-- Detailed balance is represented by vanishing cycle affinity on the triangle. -/
def DetailedBalance (L : LogAffinity) : Prop :=
  triangleWilson L = 0

/-- Broken detailed balance is nonzero Wilson/entropy circulation. -/
def BrokenDetailedBalance (L : LogAffinity) : Prop :=
  triangleWilson L ≠ 0

/-- In this finite triangle model, the cocycle condition is exactly detailed
balance.  The nonzero Wilson class is the obstruction. -/
theorem triangleCocycle_iff_detailedBalance (L : LogAffinity) :
    TriangleCocycle L ↔ DetailedBalance L := Iff.rfl

/-- Broken detailed balance is exactly failure of the triangle cocycle condition. -/
theorem brokenDetailedBalance_iff_not_cocycle (L : LogAffinity) :
    BrokenDetailedBalance L ↔ ¬ TriangleCocycle L := by
  rfl

/-- A concrete entropy-producing edge affinity: every edge on the cycle
`1→2→3→1` has weight `1`, and the reverse edges have weight `-1`. -/
def entropyCycle : LogAffinity
  | OrientedEdge3.e12 => 1
  | OrientedEdge3.e23 => 1
  | OrientedEdge3.e31 => 1
  | OrientedEdge3.e21 => -1
  | OrientedEdge3.e32 => -1
  | OrientedEdge3.e13 => -1

@[simp] theorem entropyCycle_antisymmetric :
    Antisymmetric entropyCycle := by
  intro e
  cases e <;> rfl

@[simp] theorem entropyCycle_wilson :
    triangleWilson entropyCycle = 3 := rfl

/-- The entropy cycle has broken detailed balance. -/
theorem entropyCycle_breaks_detailedBalance :
    BrokenDetailedBalance entropyCycle := by
  simp [BrokenDetailedBalance]

/-- A flat/potential affinity: all log-ratios vanish. -/
def flatAffinity : LogAffinity := fun _ => 0

@[simp] theorem flatAffinity_wilson : triangleWilson flatAffinity = 0 := rfl

/-- The flat affinity satisfies detailed balance. -/
theorem flatAffinity_detailedBalance : DetailedBalance flatAffinity := rfl

/-- Braid generator swapping vertices `1` and `2`, acting on oriented edges. -/
def braidSwap12 : OrientedEdge3 → OrientedEdge3
  | OrientedEdge3.e12 => OrientedEdge3.e21
  | OrientedEdge3.e21 => OrientedEdge3.e12
  | OrientedEdge3.e13 => OrientedEdge3.e23
  | OrientedEdge3.e31 => OrientedEdge3.e32
  | OrientedEdge3.e23 => OrientedEdge3.e13
  | OrientedEdge3.e32 => OrientedEdge3.e31

@[simp] theorem braidSwap12_involutive (e : OrientedEdge3) :
    braidSwap12 (braidSwap12 e) = e := by
  cases e <;> rfl

/-- Pull back an affinity along the braid. -/
def braidPullback12 (L : LogAffinity) : LogAffinity := fun e => L (braidSwap12 e)

@[simp] theorem braidPullback12_involutive (L : LogAffinity) :
    braidPullback12 (braidPullback12 L) = L := by
  funext e
  cases e <;> rfl

/-- Braid defect: how much the entropy circulation changes under the braid. -/
def braidEntropyDefect12 (L : LogAffinity) : ℤ :=
  triangleWilson (braidPullback12 L) - triangleWilson L

/-- A braid-invariant entropy circulation has zero braid defect. -/
theorem braidEntropyDefect12_zero_of_invariant
    (L : LogAffinity) (h : triangleWilson (braidPullback12 L) = triangleWilson L) :
    braidEntropyDefect12 L = 0 := by
  simp [braidEntropyDefect12, h]

/-- Finite spin-network decoration: assign a spin/color label to every unoriented
edge. -/
def SpinNetLabel (k : ℕ) := Edge3 → Fin k

/-- Conditional bridge from finite Wilson obstruction to the external
Wilson/spin-network/entropy reading. -/
theorem wilson_entropy_spin_network_synthesis :
    BrokenDetailedBalance entropyCycle ∧
    triangleWilson entropyCycle = 3 := by
  constructor
  · exact entropyCycle_breaks_detailedBalance
  · exact entropyCycle_wilson

end BraidedCocycleWilsonEntropy
