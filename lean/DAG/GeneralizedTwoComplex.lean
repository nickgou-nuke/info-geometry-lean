import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Matrix.Basic
import DAG.TwoComplex
import DAG.MatrixRepresentation

/-!
# DAG.GeneralizedTwoComplex

A TwoComplex parameterized by a coefficient ring `R` with star,
supporting abstract node/edge/face types and a native Hodge dual.

All six carrier types (proof architecture, Kitaev chain, LLM
softmax, Fisher information, Fibonacci anyons, V4 anomaly) are
instances of this single structure.
-/

open Matrix

namespace DAG

/-! ## The generalized structure -/

/--
A generalized TwoComplex over a coefficient ring `R` with star.

Types `nodes`, `edges`, `faces` are abstract — they can be
`Fin n` for computation, `ℕ` for infinite limits, or any
index set for categorical constructions.
-/
structure GeneralizedTwoComplex
    (R : Type u) [Semiring R] [StarRing R]
    (nodes edges faces : Type v)
    [Fintype nodes] [Fintype edges] [Fintype faces]
    [DecidableEq nodes] [DecidableEq edges] [DecidableEq faces] where
  /-- Boundary operator on edges: d1(e, v) = ±1 depending on orientation. -/
  d1 : edges → nodes → R
  /-- Boundary operator on faces: d2(f, e) = coefficient of edge e in face f. -/
  d2 : faces → edges → R
  /-- The Hodge star on 0-cochains. -/
  star0 : (nodes → R) → nodes → R
  /-- The Hodge star on 1-cochains. -/
  star1 : (edges → R) → edges → R
  /-- The Hodge star on 2-cochains. -/
  star2 : (faces → R) → faces → R
  /-- Hodge star is an involution on 0-chains: star0(star0(f)) = f. -/
  star0_involution : ∀ (f : nodes → R) (v : nodes), star0 (star0 f) v = f v
  /-- Hodge star is an involution on 1-chains. -/
  star1_involution : ∀ (f : edges → R) (e : edges), star1 (star1 f) e = f e
  /-- Boundary-squared-zero: d2 ∘ d1 = 0. -/
  boundary_squared_zero : ∀ (f : faces) (v : nodes),
    (Finset.sum Finset.univ (λ e : edges => d2 f e * d1 e v)) = 0

theorem GeneralizedTwoComplex.boundary_squared_zero_apply
    {R : Type u} [Semiring R] [StarRing R]
    {nodes edges faces : Type v}
    [Fintype nodes] [Fintype edges] [Fintype faces]
    [DecidableEq nodes] [DecidableEq edges] [DecidableEq faces]
    (C : GeneralizedTwoComplex R nodes edges faces)
    (f : faces) (v : nodes) :
    Finset.sum Finset.univ (fun e : edges => C.d2 f e * C.d1 e v) = 0 :=
  C.boundary_squared_zero f v

theorem GeneralizedTwoComplex.boundary_squared_zero_fun
    {R : Type u} [Semiring R] [StarRing R]
    {nodes edges faces : Type v}
    [Fintype nodes] [Fintype edges] [Fintype faces]
    [DecidableEq nodes] [DecidableEq edges] [DecidableEq faces]
    (C : GeneralizedTwoComplex R nodes edges faces) :
    (fun f v => Finset.sum Finset.univ
      (fun e : edges => C.d2 f e * C.d1 e v)) =
      (fun _ _ => 0) := by
  funext f v
  exact C.boundary_squared_zero f v

theorem GeneralizedTwoComplex.star0_involution_apply
    {R : Type u} [Semiring R] [StarRing R]
    {nodes edges faces : Type v}
    [Fintype nodes] [Fintype edges] [Fintype faces]
    [DecidableEq nodes] [DecidableEq edges] [DecidableEq faces]
    (C : GeneralizedTwoComplex R nodes edges faces)
    (f : nodes → R) (v : nodes) :
    C.star0 (C.star0 f) v = f v :=
  C.star0_involution f v

theorem GeneralizedTwoComplex.star1_involution_apply
    {R : Type u} [Semiring R] [StarRing R]
    {nodes edges faces : Type v}
    [Fintype nodes] [Fintype edges] [Fintype faces]
    [DecidableEq nodes] [DecidableEq edges] [DecidableEq faces]
    (C : GeneralizedTwoComplex R nodes edges faces)
    (f : edges → R) (e : edges) :
    C.star1 (C.star1 f) e = f e :=
  C.star1_involution f e

theorem GeneralizedTwoComplex.star0_involution_fun
    {R : Type u} [Semiring R] [StarRing R]
    {nodes edges faces : Type v}
    [Fintype nodes] [Fintype edges] [Fintype faces]
    [DecidableEq nodes] [DecidableEq edges] [DecidableEq faces]
    (C : GeneralizedTwoComplex R nodes edges faces)
    (f : nodes → R) :
    C.star0 (C.star0 f) = f := by
  funext v
  exact C.star0_involution f v

theorem GeneralizedTwoComplex.star1_involution_fun
    {R : Type u} [Semiring R] [StarRing R]
    {nodes edges faces : Type v}
    [Fintype nodes] [Fintype edges] [Fintype faces]
    [DecidableEq nodes] [DecidableEq edges] [DecidableEq faces]
    (C : GeneralizedTwoComplex R nodes edges faces)
    (f : edges → R) :
    C.star1 (C.star1 f) = f := by
  funext e
  exact C.star1_involution f e

end DAG
