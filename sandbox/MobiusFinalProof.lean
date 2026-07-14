import InfoGeometry.Topology.MobiusGeometry
import sandbox.MobiusHelpers

namespace InfoGeometry
open Classical

lemma eval_comp_inv_left (M1 M2 : MobiusTransform) (z : RiemannSphere) :
    (comp (inv M1) M2).eval z = (inv M1).eval (M2.eval z) := by
  apply eval_comp

theorem strictly_three_transitive
    (z1 z2 z3 : RiemannSphere) (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h13 : z1 ≠ z3)
    (w1 w2 w3 : RiemannSphere) (g12 : w1 ≠ w2) (g23 : w2 ≠ w3) (g13 : w1 ≠ w3) :
    ∃ M : MobiusTransform,
      M.eval z1 = w1 ∧ M.eval z2 = w2 ∧ M.eval z3 = w3 ∧
      ∀ M' : MobiusTransform, M'.eval z1 = w1 ∧ M'.eval z2 = w2 ∧ M'.eval z3 = w3 →
        M.equiv M' := by
  obtain ⟨M1, h1z1, h1z2, h1z3⟩ := maps_to_01inf z1 z2 z3 h12 h23 h13
  obtain ⟨M2, h2w1, h2w2, h2w3⟩ := maps_to_01inf w1 w2 w3 g12 g23 g13
  let M := comp (inv M2) M1
  have hmz1 : M.eval z1 = w1 := by
    calc M.eval z1 = (inv M2).eval (M1.eval z1) := eval_comp (inv M2) M1 z1
      _ = (inv M2).eval (some 0) := by rw [h1z1]
      _ = w1 := by
        have h_inv : (inv M2).eval (M2.eval w1) = w1 := eval_inv M2 w1
        rw [h2w1] at h_inv
        exact h_inv
  have hmz2 : M.eval z2 = w2 := by
    calc M.eval z2 = (inv M2).eval (M1.eval z2) := eval_comp (inv M2) M1 z2
      _ = (inv M2).eval (some 1) := by rw [h1z2]
      _ = w2 := by
        have h_inv : (inv M2).eval (M2.eval w2) = w2 := eval_inv M2 w2
        rw [h2w2] at h_inv
        exact h_inv
  have hmz3 : M.eval z3 = w3 := by
    calc M.eval z3 = (inv M2).eval (M1.eval z3) := eval_comp (inv M2) M1 z3
      _ = (inv M2).eval none := by rw [h1z3]
      _ = w3 := by
        have h_inv : (inv M2).eval (M2.eval w3) = w3 := eval_inv M2 w3
        rw [h2w3] at h_inv
        exact h_inv
  refine ⟨M, hmz1, hmz2, hmz3, ?_⟩
  intro M' hM'
  intro z
  let M_test := comp M2 (comp M' (inv M1))
  have ht0 : M_test.eval (some 0) = some 0 := by
    calc M_test.eval (some 0) = M2.eval ((comp M' (inv M1)).eval (some 0)) := eval_comp M2 (comp M' (inv M1)) (some 0)
      _ = M2.eval (M'.eval ((inv M1).eval (some 0))) := by rw [eval_comp M' (inv M1) (some 0)]
      _ = M2.eval (M'.eval z1) := by
        have h_inv : (inv M1).eval (M1.eval z1) = z1 := eval_inv M1 z1
        rw [h1z1] at h_inv
        rw [h_inv]
      _ = M2.eval w1 := by rw [hM'.1]
      _ = some 0 := h2w1
  have ht1 : M_test.eval (some 1) = some 1 := by
    calc M_test.eval (some 1) = M2.eval ((comp M' (inv M1)).eval (some 1)) := eval_comp M2 (comp M' (inv M1)) (some 1)
      _ = M2.eval (M'.eval ((inv M1).eval (some 1))) := by rw [eval_comp M' (inv M1) (some 1)]
      _ = M2.eval (M'.eval z2) := by
        have h_inv : (inv M1).eval (M1.eval z2) = z2 := eval_inv M1 z2
        rw [h1z2] at h_inv
        rw [h_inv]
      _ = M2.eval w2 := by rw [hM'.2.1]
      _ = some 1 := h2w2
  have htinf : M_test.eval none = none := by
    calc M_test.eval none = M2.eval ((comp M' (inv M1)).eval none) := eval_comp M2 (comp M' (inv M1)) none
      _ = M2.eval (M'.eval ((inv M1).eval none)) := by rw [eval_comp M' (inv M1) none]
      _ = M2.eval (M'.eval z3) := by
        have h_inv : (inv M1).eval (M1.eval z3) = z3 := eval_inv M1 z3
        rw [h1z3] at h_inv
        rw [h_inv]
      _ = M2.eval w3 := by rw [hM'.2.2]
      _ = none := h2w3
  have h_id := mobius_unique_01inf M_test ht0 ht1 htinf
  -- We know M_test.eval z = z
  -- M_test = comp M2 (comp M' (inv M1))
  -- So M2(M'(inv M1(z))) = z
  -- M'(inv M1(z)) = inv M2 (z)
  -- M'(y) = inv M2 (M1(y)) = M(y)
  -- Let's prove M.eval z = M'.eval z
  have h_M_eq_M' : ∀ y, M.eval y = M'.eval y := by
    intro y
    have h_z_eq : M_test.eval (M1.eval y) = M1.eval y := h_id (M1.eval y)
    have h_z_expand : M_test.eval (M1.eval y) = M2.eval (M'.eval y) := by
      calc M_test.eval (M1.eval y) = M2.eval ((comp M' (inv M1)).eval (M1.eval y)) := eval_comp M2 (comp M' (inv M1)) (M1.eval y)
        _ = M2.eval (M'.eval ((inv M1).eval (M1.eval y))) := by rw [eval_comp M' (inv M1) (M1.eval y)]
        _ = M2.eval (M'.eval y) := by rw [eval_inv M1 y]
    rw [h_z_expand] at h_z_eq
    calc M.eval y = (comp (inv M2) M1).eval y := rfl
      _ = (inv M2).eval (M1.eval y) := eval_comp (inv M2) M1 y
      _ = (inv M2).eval (M2.eval (M'.eval y)) := by rw [← h_z_eq]
      _ = M'.eval y := eval_inv M2 (M'.eval y)
  exact h_M_eq_M' z
