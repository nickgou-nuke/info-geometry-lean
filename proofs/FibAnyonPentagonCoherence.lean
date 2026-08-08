import Mathlib
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Presentable.Finite

open CategoryTheory
open CategoryTheory.Limits
open SSet
open Opposite

universe u

-- Part 1: Filtered Colimits of ∞-Categories (Rozenblyum's Lemma)
variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable (F : J ⥤ SSet.{u}) (c : SSet.{u})

/-- A compact object in the ∞-category setting is exactly a finitely presentable object.
    For such objects, the mapping space functor `Maps(c, -)` commutes with filtered colimits. -/
noncomputable def rozenblyum_mapping_space_commutes_colimit
    [IsFinitelyPresentable c] [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op c))] :
    (c ⟶ colimit F) ≅ colimit (F ⋙ coyoneda.obj (op c)) := by
  haveI : PreservesFilteredColimits (coyoneda.obj (op c)) :=
    isFinitelyPresentable_iff_preservesFilteredColimits.mp ‹IsFinitelyPresentable c›
  haveI : PreservesColimitsOfShape J (coyoneda.obj (op c)) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  exact preservesColimitIso (coyoneda.obj (op c)) F


-- Part 2: Fibonacci Anyons and the algebraic Pentagon Identity (Mac Lane coherence)
noncomputable def tau_gr : ℝ := (Real.sqrt 5 - 1) / 2
noncomputable def s_gr : ℝ := Real.sqrt tau_gr

lemma tau_nonneg : 0 ≤ tau_gr := by
  dsimp [tau_gr]
  have h : (1 : ℝ) ≤ Real.sqrt 5 := by
    calc
      (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
  nlinarith

lemma s_sq_eq_tau : s_gr ^ 2 = tau_gr :=
  Real.sq_sqrt tau_nonneg

lemma pentagon_condition : tau_gr ^ 2 + s_gr ^ 2 = 1 := by
  rw [s_sq_eq_tau]
  dsimp [tau_gr]
  have h5sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (show 0 ≤ (5 : ℝ) from by norm_num)
  nlinarith

/-- Label set for Fibonacci simple objects: `I` (identity) and `tau` (non-Abelian anyon). -/
inductive FibLabel
  | I
  | tau
  deriving DecidableEq, Fintype, Repr

/-- The multiplicity-free F-symbols for the Fibonacci category.
    When all four outer labels are `tau`, we get the 2x2 F-matrix.
    In all other cases, the symbol defaults to the Kronecker delta. -/
noncomputable def FibF (a b c d e f : FibLabel) : ℝ :=
  if a = FibLabel.tau && b = FibLabel.tau && c = FibLabel.tau && d = FibLabel.tau then
    match e, f with
    | FibLabel.I, FibLabel.I => tau_gr
    | FibLabel.I, FibLabel.tau => s_gr
    | FibLabel.tau, FibLabel.I => s_gr
    | FibLabel.tau, FibLabel.tau => -tau_gr
  else
    if e = f then 1 else 0

/-- Left-hand side of the Pentagon Identity, summing over the intermediate label `j`. -/
def pentagon_lhs (a b c d e f g h i : FibLabel) : ℝ :=
  (FibF c d e h FibLabel.I g) * (FibF a b FibLabel.I f i g) * (FibF a i e f h FibLabel.I) +
  (FibF c d e h FibLabel.tau g) * (FibF a b FibLabel.tau f i g) * (FibF a i e f h FibLabel.tau)

/-- Right-hand side of the Pentagon Identity. -/
def pentagon_rhs (a b c d e f g h i : FibLabel) : ℝ :=
  (FibF a b c i h g) * (FibF a h e f i g)

lemma tau_sq_add_s_sq : tau_gr * tau_gr + s_gr * s_gr = 1 := by
  calc
    tau_gr * tau_gr + s_gr * s_gr = tau_gr ^ 2 + s_gr ^ 2 := by ring
    _ = 1 := pentagon_condition

lemma s_sq_add_tau_sq : s_gr * s_gr + tau_gr * tau_gr = 1 := by
  rw [add_comm, tau_sq_add_s_sq]

/-- The algebraic Mac Lane Pentagon Identity for the Fibonacci Anyon F-symbols.
    This identity holds for all 512 possible labeling configurations. -/
theorem fib_pentagon_identity (a b c d e f g h i : FibLabel) :
    pentagon_lhs a b c d e f g h i = pentagon_rhs a b c d e f g h i := by
  rcases a <;> rcases b <;> rcases c <;> rcases d <;> rcases e <;> rcases f <;> rcases g <;> rcases h <;> rcases i <;> {
    dsimp [pentagon_lhs, pentagon_rhs, FibF]
    try rw [tau_sq_add_s_sq]
    try rw [s_sq_add_tau_sq]
    try ring
  }
