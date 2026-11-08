import InfoGeometry.Quantum.DualFlatKreinGraph
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Real cotangent lift on the doubled primal/dual carrier

This is the finite carrier action underlying a Möbius representation.  It is
an external linear action; it does not identify the action with raw Zorn
multiplication.
-/

namespace InfoGeometry.Quantum.MobiusRealCotangentLift

open InfoGeometry.Quantum.DualFlatKreinGraph

def lift {n : ℕ} (g : Vector n ≃ₗ[ℝ] Vector n) (x : Carrier n) : Carrier n :=
  (g x.1, x.2.comp g.symm.toLinearMap)

theorem lift_primal {n : ℕ} (g : Vector n ≃ₗ[ℝ] Vector n) (v : Vector n) :
    lift g (primal v) = primal (g v) := by
  rfl

theorem lift_dual {n : ℕ} (g : Vector n ≃ₗ[ℝ] Vector n) (α : Covector n) :
    lift g (dual α) = dual (α.comp g.symm.toLinearMap) := by
  apply Prod.ext
  · simp [lift, dual]
  · rfl

theorem lift_preserves_neutral {n : ℕ} (g : Vector n ≃ₗ[ℝ] Vector n)
    (x y : Carrier n) :
    neutralPair (lift g x) (lift g y) = neutralPair x y := by
  unfold lift neutralPair
  simp only [Prod.fst, Prod.snd, LinearMap.comp_apply]
  have hx : x.2 (g.symm.toLinearMap (g y.1)) = x.2 y.1 :=
    congrArg x.2 (g.symm_apply_apply y.1)
  have hy : y.2 (g.symm.toLinearMap (g x.1)) = y.2 x.1 :=
    congrArg y.2 (g.symm_apply_apply x.1)
  rw [hx, hy]

theorem lift_preserves_symplectic {n : ℕ} (g : Vector n ≃ₗ[ℝ] Vector n)
    (x y : Carrier n) :
    symplecticPair (lift g x) (lift g y) = symplecticPair x y := by
  unfold lift symplecticPair
  simp only [Prod.fst, Prod.snd, LinearMap.comp_apply]
  have hx : x.2 (g.symm.toLinearMap (g y.1)) = x.2 y.1 :=
    congrArg x.2 (g.symm_apply_apply y.1)
  have hy : y.2 (g.symm.toLinearMap (g x.1)) = y.2 x.1 :=
    congrArg y.2 (g.symm_apply_apply x.1)
  rw [hx, hy]

theorem lift_preserves_grading {n : ℕ} (g : Vector n ≃ₗ[ℝ] Vector n)
    (x : Carrier n) :
    grading (lift g x) = lift g (grading x) := by
  ext <;> rfl

theorem lift_identity {n : ℕ} (x : Carrier n) :
    lift (LinearEquiv.refl ℝ (Vector n)) x = x := by
  ext <;> simp [lift]

theorem lift_comp {n : ℕ} (g h : Vector n ≃ₗ[ℝ] Vector n) (x : Carrier n) :
    lift (g.trans h) x = lift h (lift g x) := by
  ext <;> simp [lift, LinearMap.comp_apply]

/-- The cotangent lift is an invertible real carrier action. -/
def liftEquiv {n : ℕ} (g : Vector n ≃ₗ[ℝ] Vector n) : Carrier n ≃ Carrier n where
  toFun := lift g
  invFun := lift g.symm
  left_inv := by
    intro x
    rw [← lift_comp]
    simpa using lift_identity x
  right_inv := by
    intro x
    rw [← lift_comp]
    simpa using lift_identity x

@[simp] theorem liftEquiv_apply {n : ℕ} (g : Vector n ≃ₗ[ℝ] Vector n)
    (x : Carrier n) : liftEquiv g x = lift g x := rfl

end InfoGeometry.Quantum.MobiusRealCotangentLift
