/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GraphChartTransition
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic

/-!
# Null operators and signed graph inversion

The inverse chart is a chart on actual submodules, not a totalized scalar
reciprocal. Signed exchange has square -I on vectors and acts involutively
on submodules. Nonzero square-zero operators leave the graph chart, while
the ambient linear equivalence remains nonsingular. Clifford nullity is
used only through the native quadratic relation.
-/

namespace InfoGeometry.OperatorAlgebra.ProjectiveNullInversion

open InfoGeometry.SuperGrassmannian.GraphChartTransition

section Graphs
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- The signed homogeneous interchange of the two operator-graph coordinates. -/
def signedSwap : (V × V) ≃ₗ[R] (V × V) where
  toFun z := (-z.2, z.1)
  invFun z := (z.2, -z.1)
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by simp [add_comm]
  map_smul' c z := by simp

@[simp] theorem signedSwap_apply (z : V × V) : signedSwap (R := R) z = (-z.2, z.1) := rfl

theorem signedSwap_square (z : V × V) :
    signedSwap (R := R) (signedSwap z) = -z := rfl

/-- The vector sign is retained; only passage to submodules forgets it. -/
theorem signedSwap_map_twice (S : Submodule R (V × V)) :
    (S.map signedSwap.toLinearMap).map signedSwap.toLinearMap = S := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    change -y ∈ S
    exact S.neg_mem hy
  · intro hz
    refine ⟨signedSwap (-z), ⟨-z, S.neg_mem hz, rfl⟩, ?_⟩
    change -(-z) = z
    exact neg_neg z

/-- The ordered operator inverse, on its exact invertible chart. -/
theorem signedSwap_graph_inverse (u : V ≃ₗ[R] V) :
    u.toLinearMap.graph.map signedSwap.toLinearMap = (-u.symm.toLinearMap).graph := by
  apply (map_graph_eq_iff _ _ _).mpr
  constructor
  · intro x
    change x = -u.symm (-u x)
    simp
  · intro y
    refine ⟨u.symm (-y), ?_⟩
    change -(u (u.symm (-y))) = y
    simp

/-- Signed inversion has exactly the same domain obstruction as ordinary swap. -/
theorem signedSwap_graph_chart_iff (f : Module.End R V) :
    (∃ g : Module.End R V, f.graph.map signedSwap.toLinearMap = g.graph) ↔
      Function.Bijective f := by
  rw [exists_map_graph_iff _ signedSwap.injective]
  change Function.Bijective (fun x => -f x) ↔ Function.Bijective f
  constructor
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y h
      exact hi (congrArg Neg.neg h)
    · intro y
      obtain ⟨x, hx⟩ := hs (-y)
      exact ⟨x, neg_injective hx⟩
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y h
      exact hi (neg_injective h)
    · intro y
      obtain ⟨x, hx⟩ := hs (-y)
      exact ⟨x, by rw [hx, neg_neg]⟩

/-- A genuine nonzero nilpotent channel is an inverse-chart boundary. -/
theorem square_zero_exits_graph_chart (f : Module.End R V)
    (hf : f ≠ 0) (hsq : f * f = 0) (g : Module.End R V) :
    f.graph.map signedSwap.toLinearMap ≠ g.graph := by
  intro h
  have hi := ((signedSwap_graph_chart_iff f).mp ⟨g, h⟩).1
  apply hf
  ext x
  have hx : f (f x) = f 0 := by
    have hh := LinearMap.congr_fun hsq x
    simpa using hh
  exact hi hx

/-- The zero graph maps to the vertical submodule, without an inverse at zero. -/
theorem zero_graph_to_vertical :
    (0 : Module.End R V).graph.map signedSwap.toLinearMap =
      LinearMap.ker (LinearMap.fst R V V) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x.2 = (0 : Module.End R V) x.1 at hx
    change -x.2 = 0
    simp [hx]
  · intro hz
    change z.1 = 0 at hz
    refine ⟨(z.2, 0), rfl, ?_⟩
    exact Prod.ext (by simpa using hz.symm) rfl

end Graphs

section Clifford
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The faithful left regular action of the native Clifford generator. -/
def cliffordLeft (Q : QuadraticForm R V) (v : V) : Module.End R (CliffordAlgebra Q) where
  toFun a := CliffordAlgebra.ι Q v * a
  map_add' a b := mul_add _ _ _
  map_smul' c a := by simp [mul_smul_comm]

theorem cliffordLeft_square (Q : QuadraticForm R V) (v : V) :
    cliffordLeft Q v * cliffordLeft Q v = (Q v) • (1 : Module.End R (CliffordAlgebra Q)) := by
  ext a
  change CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q v * a) = (Q v) • a
  rw [← mul_assoc, CliffordAlgebra.ι_sq_scalar, Algebra.smul_def]

theorem cliffordLeft_ne_zero (Q : QuadraticForm R V) (v : V)
    (hv : CliffordAlgebra.ι Q v ≠ 0) : cliffordLeft Q v ≠ 0 := by
  intro h
  have hh := LinearMap.congr_fun h 1
  exact hv (by simpa [cliffordLeft] using hh)

/-- The null cone maps into the square-zero cone of an operator algebra. -/
theorem clifford_null_graph_boundary (Q : QuadraticForm R V) (v : V)
    (hQ : Q v = 0) (hv : CliffordAlgebra.ι Q v ≠ 0)
    (g : Module.End R (CliffordAlgebra Q)) :
    (cliffordLeft Q v).graph.map signedSwap.toLinearMap ≠ g.graph := by
  apply square_zero_exits_graph_chart _ (cliffordLeft_ne_zero Q v hv)
  rw [cliffordLeft_square, hQ, zero_smul]

end Clifford

end InfoGeometry.OperatorAlgebra.ProjectiveNullInversion
