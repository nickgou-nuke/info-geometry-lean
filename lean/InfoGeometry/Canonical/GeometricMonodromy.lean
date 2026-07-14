import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Algebra.Basic

/-!
# Geometric monodromy for an internal real bivector phase

This file records the theorem-honest finite algebraic core of the
Hestenes--Krein monodromy story.  It does **not** claim to replace complex
analysis, prove a geometric Stokes theorem, or construct a full QFT.  It proves
only the kernel-checkable fact used by that interpretation: a spinorial
half-angle transport built from an internal real algebra element has the
expected `2π ↦ -1`, `4π ↦ 1` double-cover readout.

#### BUCKET 1: CLOSED FINITE THEOREMS
* `bivectorExp_pi`, `bivectorExp_two_pi`, `spinorial_monodromy_around_pole`,
  and `spinorial_double_loop_identity` are closed algebra/trigonometry
  theorems for any real algebra.
* `state_boundaryPair_zero`, `monodromyBoundaryCurrent_state_zero`, and
  `monodromyBoundaryCurrent_eq_boundaryPair` are closed algebraic cancellation
  readouts for a real-linear state and the `2π` spinorial monodromy.
* `spinorial_winding_transport_nat` and its even/odd corollaries record the
  finite winding-parity readout of the half-angle transport.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
No geometric Stokes theorem, de Rham pole integral, GNS annihilation theorem,
or analytic-continuation replacement theorem is claimed here.
-/

noncomputable section

namespace GeometricMonodromy

variable {AInf : Type*} [Ring AInf] [Algebra ℝ AInf]

/--
Native real-algebra Euler expression for a chosen internal bivector-like element
`J`.  The formula itself is purely algebraic; multiplication laws for a genuine
rotation one-parameter subgroup require additional hypotheses such as `J * J = -1`.
-/
def bivectorExp (J : AInf) (θ : ℝ) : AInf :=
  (Real.cos θ) • (1 : AInf) + (Real.sin θ) • J

/-- Spinorial transport uses the half-angle representation. -/
def spinorTransport (J : AInf) (θ : ℝ) : AInf :=
  bivectorExp J (θ / 2)

/-- At angle `π`, the internal Euler expression is the parity operator `-1`. -/
theorem bivectorExp_pi (J : AInf) :
    bivectorExp J Real.pi = -(1 : AInf) := by
  unfold bivectorExp
  rw [Real.cos_pi, Real.sin_pi]
  simp

/-- At angle `2π`, the internal Euler expression returns to `+1`. -/
theorem bivectorExp_two_pi (J : AInf) :
    bivectorExp J (2 * Real.pi) = (1 : AInf) := by
  unfold bivectorExp
  rw [Real.cos_two_pi, Real.sin_two_pi]
  simp

/--
A full `2π` spatial loop gives the spinorial parity flip.  This is the precise
Lean statement behind the slogan that the spin representation is a double cover.
-/
theorem spinorial_monodromy_around_pole (J : AInf) :
    spinorTransport J (2 * Real.pi) = -(1 : AInf) := by
  unfold spinorTransport
  have hhalf : (2 * Real.pi) / 2 = Real.pi := by ring
  rw [hhalf]
  exact bivectorExp_pi J

/-- Two full turns, i.e. `4π`, return a spinor to itself. -/
theorem spinorial_double_loop_identity (J : AInf) :
    spinorTransport J (4 * Real.pi) = (1 : AInf) := by
  unfold spinorTransport
  have hhalf : (4 * Real.pi) / 2 = 2 * Real.pi := by ring
  rw [hhalf]
  exact bivectorExp_two_pi J

/-- The finite winding-number readout: `n` full spatial loops produce `(-1)^n`. -/
theorem spinorial_winding_transport_nat (J : AInf) (n : ℕ) :
    spinorTransport J (2 * Real.pi * (n : ℝ)) = ((-1 : ℝ) ^ n) • (1 : AInf) := by
  unfold spinorTransport bivectorExp
  have hhalf : (2 * Real.pi * (n : ℝ)) / 2 = (n : ℝ) * Real.pi := by ring
  rw [hhalf, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  simp

/-- An even number of full windings returns the spinorial phase to `+1`. -/
theorem spinorial_even_winding_transport (J : AInf) (k : ℕ) :
    spinorTransport J (2 * Real.pi * (((2 * k : ℕ) : ℝ))) = (1 : AInf) := by
  rw [spinorial_winding_transport_nat]
  have hpow : ((-1 : ℝ) ^ (2 * k)) = 1 := by
    rw [show 2 * k = 2 * k by rfl, pow_mul]
    simp
  simp [hpow]

/-- An odd number of full windings gives the spinorial parity flip `-1`. -/
theorem spinorial_odd_winding_transport (J : AInf) (k : ℕ) :
    spinorTransport J (2 * Real.pi * (((2 * k + 1 : ℕ) : ℝ))) = -(1 : AInf) := by
  rw [spinorial_winding_transport_nat]
  have hpow : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by
    rw [pow_succ]
    have heven : ((-1 : ℝ) ^ (2 * k)) = 1 := by
      rw [show 2 * k = 2 * k by rfl, pow_mul]
      simp
    rw [heven]
    norm_num
  simp [hpow]

/-! ## Boundary cancellation readout -/

/-- The algebraic boundary pair of an element and its opposite. -/
def boundaryPair (X : AInf) : AInf :=
  X + (-X)

/-- A linear state kills the algebraic boundary pair. -/
theorem state_boundaryPair_zero (ω : AInf →ₗ[ℝ] ℝ) (X : AInf) :
    ω (boundaryPair X) = 0 := by
  unfold boundaryPair
  simp

/-- The monodromy-weighted boundary current. -/
def monodromyBoundaryCurrent (J X : AInf) : AInf :=
  X + spinorTransport J (2 * Real.pi) * X

/--
The monodromy-weighted boundary current collapses to zero under any linear
state.  The only geometric input is the `2π` spinorial monodromy theorem.
-/
theorem monodromyBoundaryCurrent_state_zero
    (ω : AInf →ₗ[ℝ] ℝ) (J X : AInf) :
    ω (monodromyBoundaryCurrent J X) = 0 := by
  unfold monodromyBoundaryCurrent
  rw [spinorial_monodromy_around_pole]
  simp

/-- The monodromy current itself is algebraically the boundary pair after `2π`. -/
theorem monodromyBoundaryCurrent_eq_boundaryPair (J X : AInf) :
    monodromyBoundaryCurrent J X = boundaryPair X := by
  unfold monodromyBoundaryCurrent boundaryPair
  rw [spinorial_monodromy_around_pole]
  simp

/-- The monodromy-weighted boundary current is itself zero after `2π`. -/
theorem monodromyBoundaryCurrent_eq_zero (J X : AInf) :
    monodromyBoundaryCurrent J X = 0 := by
  rw [monodromyBoundaryCurrent_eq_boundaryPair]
  simp [boundaryPair]

/-- A recursive winding readout: each extra loop flips the sign. -/
def windingReadout : ℕ → AInf
  | 0 => (1 : AInf)
  | n + 1 => - windingReadout n

omit [Algebra ℝ AInf] in
@[simp] theorem windingReadout_zero : windingReadout (AInf := AInf) 0 = 1 := rfl

omit [Algebra ℝ AInf] in
@[simp] theorem windingReadout_succ (n : ℕ) :
    windingReadout (AInf := AInf) (n + 1) = - windingReadout (AInf := AInf) n := rfl

omit [Algebra ℝ AInf] in
/-- Two successive windings cancel. -/
theorem windingReadout_add_two (n : ℕ) :
    windingReadout (AInf := AInf) (n + 2) = windingReadout (AInf := AInf) n := by
  simp [windingReadout]

omit [Algebra ℝ AInf] in
/-- A winding pair is additive cancellation. -/
theorem windingReadout_pair_zero (n : ℕ) :
    windingReadout (AInf := AInf) (n + 1) + windingReadout (AInf := AInf) n = 0 := by
  simp [windingReadout, add_comm]

/-- The n-fold product of full-loop spinorial transport operators. -/
def spinorialWindingTransport (J : AInf) : ℕ → AInf
  | 0 => 1
  | n + 1 => spinorTransport J (2 * Real.pi) * spinorialWindingTransport J n

@[simp] theorem spinorialWindingTransport_zero (J : AInf) :
    spinorialWindingTransport J 0 = (1 : AInf) :=
  rfl

@[simp] theorem spinorialWindingTransport_succ (J : AInf) (n : ℕ) :
    spinorialWindingTransport J (n + 1) =
      spinorTransport J (2 * Real.pi) * spinorialWindingTransport J n :=
  rfl

/-- The n-fold full-loop spinorial transport equals the recursive winding sign. -/
theorem spinorialWindingTransport_eq_windingReadout (J : AInf) (n : ℕ) :
    spinorialWindingTransport J n = windingReadout (AInf := AInf) n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [spinorialWindingTransport_succ, spinorial_monodromy_around_pole, ih,
        windingReadout_succ]
      simp

omit [Algebra ℝ AInf] in
/-- An even number of full windings gives `+1`. -/
theorem windingReadout_even (m : ℕ) :
    windingReadout (AInf := AInf) (2 * m) = (1 : AInf) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hidx : 2 * (m + 1) = 2 * m + 2 := Nat.mul_succ 2 m
      calc
        windingReadout (AInf := AInf) (2 * (m + 1))
            = windingReadout (AInf := AInf) (2 * m + 2) := by rw [hidx]
        _ = windingReadout (AInf := AInf) (2 * m) := by
                rw [windingReadout_add_two]
        _ = (1 : AInf) := ih

omit [Algebra ℝ AInf] in
/-- An odd number of full windings gives `-1`. -/
theorem windingReadout_odd (m : ℕ) :
    windingReadout (AInf := AInf) (2 * m + 1) = -(1 : AInf) := by
  calc
        windingReadout (AInf := AInf) (2 * m + 1)
        = - windingReadout (AInf := AInf) (2 * m) := by
            simp
    _ = -(1 : AInf) := by rw [windingReadout_even]

/-- The actual n-fold transport is `+1` for an even number of full windings. -/
theorem spinorialWindingTransport_even (J : AInf) (m : ℕ) :
    spinorialWindingTransport J (2 * m) = (1 : AInf) := by
  rw [spinorialWindingTransport_eq_windingReadout, windingReadout_even]

/-- The actual n-fold transport is `-1` for an odd number of full windings. -/
theorem spinorialWindingTransport_odd (J : AInf) (m : ℕ) :
    spinorialWindingTransport J (2 * m + 1) = -(1 : AInf) := by
  rw [spinorialWindingTransport_eq_windingReadout, windingReadout_odd]

end GeometricMonodromy
