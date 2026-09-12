import InfoGeometry.Convex.FenchelConjugate
import InfoGeometry.Convex.Legendre
import InfoGeometry.Physics.WillertonIsbellAmariDuality

namespace InfoGeometry.Convex

noncomputable section

def finiteEuclideanFunctional {D : ℕ} (x : EuclideanSpace ℝ (Fin D)) :
    DualSpace (EuclideanSpace ℝ (Fin D)) :=
  innerSL ℝ x

theorem finiteEuclideanFunctional_apply {D : ℕ}
    (x y : EuclideanSpace ℝ (Fin D)) :
    finiteEuclideanFunctional x y = inner ℝ x y := by
  exact innerSL_apply_apply ℝ x y

theorem euclidean_inner_eq_sum {D : ℕ}
    (x y : EuclideanSpace ℝ (Fin D)) :
    inner ℝ x y = ∑ i : Fin D, x i * y i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp [RCLike.inner_apply]
  ring

theorem euclidean_equiv_inner_eq_pairing {D : ℕ}
    (x y : Fin D → ℝ) :
    inner ℝ ((EuclideanSpace.equiv (Fin D) ℝ).symm x)
      ((EuclideanSpace.equiv (Fin D) ℝ).symm y) =
      ∑ i : Fin D, x i * y i := by
  rw [euclidean_inner_eq_sum]
  rfl

theorem finiteEuclideanFunctional_eq_pairing {D : ℕ}
    (x y : Fin D → ℝ) :
    finiteEuclideanFunctional ((EuclideanSpace.equiv (Fin D) ℝ).symm x)
      ((EuclideanSpace.equiv (Fin D) ℝ).symm y) =
      InfoGeometry.Physics.WillertonIsbellAmari.pairing x y := by
  rw [finiteEuclideanFunctional_apply, euclidean_equiv_inner_eq_pairing]
  rfl

theorem convexFunctional_affineSet_eq_fenchelSet
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (Φ : ConvexFunctional V) (y : V) :
    Φ.affineSet y = fenchelSet Φ.F (innerSL ℝ y) := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    simp [dualPair, innerSL_apply_apply, real_inner_comm]
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    simp [dualPair, innerSL_apply_apply, real_inner_comm]

theorem convexFunctional_legendre_eq_fenchelConj
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (Φ : ConvexFunctional V) (y : V) :
    Φ.legendre y = fenchelConj Φ.F (innerSL ℝ y) := by
  unfold ConvexFunctional.legendre fenchelConj
  rw [convexFunctional_affineSet_eq_fenchelSet]

end
end InfoGeometry.Convex
