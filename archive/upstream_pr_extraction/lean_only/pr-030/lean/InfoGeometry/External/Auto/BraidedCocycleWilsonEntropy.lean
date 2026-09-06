import InfoGeometry.External.Auto.QuadraticConfiguration3

/-!
# Oriented triangle affinities and braid pullback

This module proves finite combinatorics for integer-valued cochains on the six
oriented edges of a triangle: reversal, antisymmetry, triangle circulation,
vertex-swap pullback, and circulation defects.
-/

namespace BraidedCocycleWilsonEntropy

open QuadraticConfiguration3

/-- The six oriented edges of the three-point graph. -/
inductive OrientedEdge3 where
  | e12 | e21 | e13 | e31 | e23 | e32
  deriving DecidableEq, Fintype, Repr

/-- Reverse an oriented edge. -/
def reverse : OrientedEdge3 → OrientedEdge3
  | .e12 => .e21
  | .e21 => .e12
  | .e13 => .e31
  | .e31 => .e13
  | .e23 => .e32
  | .e32 => .e23

@[simp] theorem reverse_reverse (e : OrientedEdge3) :
    reverse (reverse e) = e := by
  cases e <;> rfl

/-- Forget orientation and recover the underlying edge. -/
def forgetOrientation : OrientedEdge3 → Edge3
  | .e12 | .e21 => .e12
  | .e13 | .e31 => .e13
  | .e23 | .e32 => .e23

@[simp] theorem forget_reverse (e : OrientedEdge3) :
    forgetOrientation (reverse e) = forgetOrientation e := by
  cases e <;> rfl

/-- An integer-valued cochain on oriented edges. -/
abbrev EdgeAffinity := OrientedEdge3 → ℤ

/-- Antisymmetry under reversal. -/
def Antisymmetric (L : EdgeAffinity) : Prop :=
  ∀ e, L (reverse e) = -L e

/-- Circulation around `1 → 2 → 3 → 1`. -/
def triangleCirculation (L : EdgeAffinity) : ℤ :=
  L .e12 + L .e23 + L .e31

/-- Vanishing triangle circulation. -/
def TriangleCocycle (L : EdgeAffinity) : Prop :=
  triangleCirculation L = 0

/-- Nonvanishing triangle circulation. -/
def NonzeroCirculation (L : EdgeAffinity) : Prop :=
  triangleCirculation L ≠ 0

/-- A unit antisymmetric cochain around the chosen orientation. -/
def unitCycleAffinity : EdgeAffinity
  | .e12 | .e23 | .e31 => 1
  | .e21 | .e32 | .e13 => -1

@[simp] theorem unitCycleAffinity_antisymmetric :
    Antisymmetric unitCycleAffinity := by
  intro e
  cases e <;> rfl

@[simp] theorem unitCycleAffinity_circulation :
    triangleCirculation unitCycleAffinity = 3 := rfl

theorem unitCycleAffinity_nonzero : NonzeroCirculation unitCycleAffinity := by
  norm_num [NonzeroCirculation]

/-- The zero cochain. -/
def zeroAffinity : EdgeAffinity := fun _ => 0

@[simp] theorem zeroAffinity_circulation :
    triangleCirculation zeroAffinity = 0 := rfl

theorem zeroAffinity_is_cocycle : TriangleCocycle zeroAffinity := rfl

/-- Swap vertices `1` and `2` on oriented edges. -/
def braidSwap12 : OrientedEdge3 → OrientedEdge3
  | .e12 => .e21
  | .e21 => .e12
  | .e13 => .e23
  | .e31 => .e32
  | .e23 => .e13
  | .e32 => .e31

@[simp] theorem braidSwap12_involutive (e : OrientedEdge3) :
    braidSwap12 (braidSwap12 e) = e := by
  cases e <;> rfl

/-- Pull back an affinity along the vertex swap. -/
def braidPullback12 (L : EdgeAffinity) : EdgeAffinity :=
  fun e => L (braidSwap12 e)

@[simp] theorem braidPullback12_involutive (L : EdgeAffinity) :
    braidPullback12 (braidPullback12 L) = L := by
  funext e
  cases e <;> rfl

/-- Change in circulation under the vertex swap. -/
def braidCirculationDefect12 (L : EdgeAffinity) : ℤ :=
  triangleCirculation (braidPullback12 L) - triangleCirculation L

theorem braidCirculationDefect12_zero_of_invariant
    (L : EdgeAffinity)
    (h : triangleCirculation (braidPullback12 L) = triangleCirculation L) :
    braidCirculationDefect12 L = 0 := by
  simp [braidCirculationDefect12, h]

/-- A finite decoration of the three unoriented edges. -/
def EdgeLabeling (k : ℕ) := Edge3 → Fin k

/-- Consolidated finite circulation statement. -/
theorem finite_oriented_triangle_summary :
    Antisymmetric unitCycleAffinity ∧
    triangleCirculation unitCycleAffinity = 3 ∧
    NonzeroCirculation unitCycleAffinity ∧
    TriangleCocycle zeroAffinity :=
  ⟨unitCycleAffinity_antisymmetric, unitCycleAffinity_circulation,
    unitCycleAffinity_nonzero, zeroAffinity_is_cocycle⟩

end BraidedCocycleWilsonEntropy
