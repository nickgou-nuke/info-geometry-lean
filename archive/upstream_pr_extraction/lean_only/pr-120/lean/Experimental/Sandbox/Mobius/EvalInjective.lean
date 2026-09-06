import Experimental.Sandbox.Mobius.CP1ActionRiemannInjective

namespace Experimental.Sandbox.Mobius

lemma mobius_eval_injective (M : InfoGeometry.MobiusTransform) :
    Function.Injective M.eval := by
  intro z w h
  calc
    z = (InfoGeometry.inv M).eval (M.eval z) := by
      exact (InfoGeometry.eval_inv_left M z).symm
    _ = (InfoGeometry.inv M).eval (M.eval w) := by rw [h]
    _ = w := InfoGeometry.eval_inv_left M w

lemma mobius_eval_eq_iff (M : InfoGeometry.MobiusTransform) (z w : InfoGeometry.RiemannSphere) :
    M.eval z = M.eval w ↔ z = w := by
  constructor
  · intro h
    exact mobius_eval_injective M h
  · intro h
    rw [h]

lemma mobius_eval_ne_of_ne (M : InfoGeometry.MobiusTransform)
    {z w : InfoGeometry.RiemannSphere} (h : z ≠ w) :
    M.eval z ≠ M.eval w := by
  intro heq
  exact h ((mobius_eval_eq_iff M z w).mp heq)

lemma ne_of_mobius_eval_ne (M : InfoGeometry.MobiusTransform)
    {z w : InfoGeometry.RiemannSphere} (h : M.eval z ≠ M.eval w) :
    z ≠ w := by
  intro hzw
  exact h (by rw [hzw])

end Experimental.Sandbox.Mobius
