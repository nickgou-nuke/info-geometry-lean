import Mathlib.Tactic
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.PositiveHomogeneousBarrier

/-!
# Real Hestenes--Krein readout of the positive homogeneous barrier

The positive two-lane barrier remains the canonical scalar owner.  This file
only supplies its finite real split-projector readout: the two lanes are the
`Pplus` and `Pminus` sectors of the hyperbolic matrix `E`, with `E^2 = 1`.
No scalar-complex structure, analytic continuation, or self-concordance claim
is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.PositiveHomogeneousHestenesKreinBridge

open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.PositiveHomogeneousBarrier

/-! ## Split Hestenes/Krein lane readout -/

/-- The positive homogeneous pair placed in the two complementary split lanes. -/
def splitLaneOperator (x : PositiveHomogeneousCone) : Mat2 :=
  x.1.1 • Pplus + x.1.2 • Pminus

@[simp] theorem splitLaneOperator_pos_lane
    (x : PositiveHomogeneousCone) :
    splitLaneOperator x 0 0 = x.1.1 := by
  norm_num [splitLaneOperator, Pplus, Pminus, E]
  ring

@[simp] theorem splitLaneOperator_neg_lane
    (x : PositiveHomogeneousCone) :
    splitLaneOperator x 1 1 = x.1.2 := by
  norm_num [splitLaneOperator, Pplus, Pminus, E]

@[simp] theorem splitLaneOperator_offdiag_zero
    (x : PositiveHomogeneousCone) (i j : Fin 2) (hij : i ≠ j) :
    splitLaneOperator x i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [splitLaneOperator, Pplus, Pminus, E]

/-- Scalar barrier read from the two real split lanes. -/
def splitBarrierReadout (X : Mat2) : ℝ :=
  -Real.log (X 0 0) - Real.log (X 1 1)

theorem splitBarrierReadout_splitLaneOperator
    (x : PositiveHomogeneousCone) :
    splitBarrierReadout (splitLaneOperator x) = barrier x := by
  simp [splitBarrierReadout, barrier]

/-! ## Hestenes/Krein symmetry laws -/

theorem splitBarrierReadout_cartanFlow
    (t : ℝ) (x : PositiveHomogeneousCone) :
    splitBarrierReadout (splitLaneOperator (cartanFlow t x)) =
      splitBarrierReadout (splitLaneOperator x) := by
  rw [splitBarrierReadout_splitLaneOperator,
    splitBarrierReadout_splitLaneOperator]
  exact barrier_cartanFlow_invariant t x

theorem splitBarrierReadout_reciprocalScale
    (lambda : ℝ) (x : PositiveHomogeneousCone) (hlambda : 0 < lambda) :
    splitBarrierReadout (splitLaneOperator (reciprocalScale lambda x hlambda)) =
      splitBarrierReadout (splitLaneOperator x) := by
  rw [splitBarrierReadout_splitLaneOperator,
    splitBarrierReadout_splitLaneOperator]
  exact barrier_reciprocalScale_invariant lambda x hlambda

theorem splitBarrierReadout_swap
    (x : PositiveHomogeneousCone) :
    splitBarrierReadout (splitLaneOperator (homogeneousSwap x)) =
      splitBarrierReadout (splitLaneOperator x) := by
  rw [splitBarrierReadout_splitLaneOperator,
    splitBarrierReadout_splitLaneOperator]
  exact barrier_homogeneousSwap_invariant x

/-! ## The split involution and Cartan conjugacy -/

theorem splitLaneOperator_swap_diagonal
    (x : PositiveHomogeneousCone) :
    splitLaneOperator (homogeneousSwap x) 0 0 = x.1.2 ∧
      splitLaneOperator (homogeneousSwap x) 1 1 = x.1.1 := by
  simp

theorem splitBarrierReadout_cartan_swap_conjugacy
    (t : ℝ) (x : PositiveHomogeneousCone) :
    splitBarrierReadout
        (splitLaneOperator (homogeneousSwap (cartanFlow t (homogeneousSwap x)))) =
      splitBarrierReadout (splitLaneOperator (cartanFlow (-t) x)) := by
  rw [homogeneousSwap_cartanFlow_conjugacy]

/-! ## A finite stage-independent barrier packet -/

/--
A finite-stage barrier family is the precise data needed to descend a scalar
readout through a filtered carrier.  The compatibility field is explicit:
the colimit theorem below uses no representation of an actual infinity.
-/
structure FilteredBarrierReadout where
  Stage : ℕ → Type
  state : ∀ n, Stage n → PositiveHomogeneousCone
  bond : ∀ n, Stage n → Stage (n + 1)
  state_bond : ∀ n x,
    state (n + 1) (bond n x) = state n x

namespace FilteredBarrierReadout

variable (F : FilteredBarrierReadout)

def bondIterate (F : FilteredBarrierReadout) :
    ∀ (n m : ℕ), F.Stage n → F.Stage (n + m)
  | n, 0, x => x
  | n, m + 1, x => F.bond (n + m) (bondIterate F n m x)

theorem state_bondIterate (F : FilteredBarrierReadout) :
    ∀ (n m : ℕ) (x : F.Stage n),
    F.state (n + m) (F.bondIterate n m x) = F.state n x
  | n, 0, x => rfl
  | n, m + 1, x => by
      simpa [bondIterate, Nat.add_assoc] using
        (F.state_bond (n + m) (bondIterate F n m x)).trans
          (state_bondIterate F n m x)

theorem barrier_bondIterate (F : FilteredBarrierReadout) (n m : ℕ) (x : F.Stage n) :
    barrier (F.state (n + m) (bondIterate F n m x)) =
      barrier (F.state n x) := by
  rw [F.state_bondIterate]

theorem splitBarrierReadout_bondIterate
    (F : FilteredBarrierReadout) (n m : ℕ) (x : F.Stage n) :
    splitBarrierReadout (splitLaneOperator (F.state (n + m) (bondIterate F n m x))) =
      splitBarrierReadout (splitLaneOperator (F.state n x)) := by
  rw [splitBarrierReadout_splitLaneOperator,
    splitBarrierReadout_splitLaneOperator]
  exact barrier_bondIterate F n m x

end FilteredBarrierReadout

end InfoGeometry.Canonical.PositiveHomogeneousHestenesKreinBridge

end
