import InfoGeometry.Clifford.Cl55ExteriorBivectorDerivation
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

/-!
# Lie compatibility of the exterior-algebra derivation lift

The lift of a linear action on degree-one generators is a derivation on the
whole exterior algebra.  This file proves the further representation law:
the commutator of two lifted derivations is the lift of the commutator of the
generator actions.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55ExteriorBivectorLieAction

open ExteriorAlgebra
open InfoGeometry.Clifford.Cl55ExteriorBivectorDerivation

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private theorem liftExteriorDerivation_one_eq_zero (f : V →ₗ[R] V) :
    liftExteriorDerivation f (1 : ExteriorAlgebra R V) = 0 := by
  have h := liftExteriorDerivation_leibniz f (1 : ExteriorAlgebra R V) 1
  have h' : liftExteriorDerivation f 1 + 0 =
      liftExteriorDerivation f 1 + liftExteriorDerivation f 1 := by
    simpa using h
  exact (add_left_cancel h').symm

/-- The exterior-algebra lift preserves commutators of linear generator
actions.  This proves bracket compatibility for the induced degree-zero
derivations. -/
theorem liftExteriorDerivation_commutator
    (f g : V →ₗ[R] V) (x : ExteriorAlgebra R V) :
    liftExteriorDerivation f (liftExteriorDerivation g x) -
        liftExteriorDerivation g (liftExteriorDerivation f x) =
      liftExteriorDerivation (f.comp g - g.comp f) x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
      simp [Algebra.algebraMap_eq_smul_one, liftExteriorDerivation_one_eq_zero]
  | ι v =>
      simp [liftExteriorDerivation_ι, LinearMap.sub_apply,
        LinearMap.comp_apply]
  | mul a b ha hb =>
      have hfg :
          liftExteriorDerivation f (liftExteriorDerivation g (a * b)) =
            (liftExteriorDerivation f (liftExteriorDerivation g a) * b +
              liftExteriorDerivation g a * liftExteriorDerivation f b) +
            (liftExteriorDerivation f a * liftExteriorDerivation g b +
              a * liftExteriorDerivation f (liftExteriorDerivation g b)) := by
        rw [liftExteriorDerivation_leibniz g a b, map_add,
          liftExteriorDerivation_leibniz f (liftExteriorDerivation g a) b,
          liftExteriorDerivation_leibniz f a (liftExteriorDerivation g b)]
      have hgf :
          liftExteriorDerivation g (liftExteriorDerivation f (a * b)) =
            (liftExteriorDerivation g (liftExteriorDerivation f a) * b +
              liftExteriorDerivation f a * liftExteriorDerivation g b) +
            (liftExteriorDerivation g a * liftExteriorDerivation f b +
              a * liftExteriorDerivation g (liftExteriorDerivation f b)) := by
        rw [liftExteriorDerivation_leibniz f a b, map_add,
          liftExteriorDerivation_leibniz g (liftExteriorDerivation f a) b,
          liftExteriorDerivation_leibniz g a (liftExteriorDerivation f b)]
      rw [hfg, hgf, liftExteriorDerivation_leibniz (f.comp g - g.comp f) a b,
        ← ha, ← hb]
      noncomm_ring
  | add a b ha hb =>
      simp only [map_add, ha, hb]

open InfoGeometry.Clifford.BivectorVectorRepresentation
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.CliffordLieAlgebra

local notation "Exterior55" => ExteriorAlgebra ℝ V55

/-- Every element of the native `SpinBivector55` Lie span acts by the
Clifford commutator on the image of the vector generators. -/
theorem spinBivector_commutator_preserves_vector_image
    (X : SpinBivector55) (w : V55) :
    ∃ w' : V55, ⁅(X : Cl55), ι55 w⁆ = ι55 w' := by
  have hmem : ∀ (x : Cl55), x ∈ soLieAlgebra Q55 →
      ∀ w : V55, ∃ w' : V55, ⁅x, ι55 w⁆ = ι55 w' := by
    intro x hx
    change x ∈ LieSubalgebra.lieSpan ℝ Cl55
      (Set.range (fun p : V55 × V55 => ⁅ι55 p.1, ι55 p.2⁆)) at hx
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx =>
        rcases hx with ⟨⟨u, v⟩, rfl⟩
        intro w
        have h₁ := bivector_vector_action_eq u v w
        have h₂ := bivector_vector_action_eq v u w
        have hT : bivectorVectorTransform v u w =
            -bivectorVectorTransform u v w := by
          dsimp [bivectorVectorTransform]
          abel
        rw [hT] at h₂
        refine ⟨2 • bivectorVectorTransform u v w, ?_⟩
        have hdiff : ⁅ι55 u * ι55 v - ι55 v * ι55 u, ι55 w⁆ =
            ⁅ι55 u * ι55 v, ι55 w⁆ - ⁅ι55 v * ι55 u, ι55 w⁆ := by
          simp only [Ring.lie_def]
          noncomm_ring
        change ⁅ι55 u * ι55 v - ι55 v * ι55 u, ι55 w⁆ =
          ι55 (2 • bivectorVectorTransform u v w)
        rw [hdiff, h₁, h₂]
        simp only [map_neg, sub_neg_eq_add, two_smul, map_smul]
    | zero =>
        intro w
        exact ⟨0, by simp⟩
    | add x y hx hy ihx ihy =>
        intro w
        obtain ⟨xw, hxw⟩ := ihx w
        obtain ⟨yw, hyv⟩ := ihy w
        refine ⟨xw + yw, ?_⟩
        change ⁅x + y, ι55 w⁆ = ι55 (xw + yw)
        rw [add_lie, hxw, hyv, map_add]
    | smul r x hx ih =>
        intro w
        obtain ⟨xw, hxw⟩ := ih w
        refine ⟨r • xw, ?_⟩
        change ⁅r • x, ι55 w⁆ = ι55 (r • xw)
        rw [smul_lie, hxw, map_smul]
    | lie x y hx hy ihx ihy =>
        intro w
        obtain ⟨yw, hyw⟩ := ihy w
        obtain ⟨xw, hxw⟩ := ihx w
        obtain ⟨xyw, hxyw⟩ := ihx yw
        obtain ⟨yxw, hyxw⟩ := ihy xw
        refine ⟨xyw - yxw, ?_⟩
        change ⁅⁅x, y⁆, ι55 w⁆ = ι55 (xyw - yxw)
        rw [lie_lie, hyw, hxw, hxyw, hyxw, map_sub]
  exact hmem (X : Cl55) X.property w

/-- The commutator action of a `SpinBivector55` element restricts to a linear
endomorphism of the embedded vector subspace of the Clifford algebra. -/
noncomputable def spinBivectorAdjointOnVectorImage (X : SpinBivector55) :
    LinearMap.range ι55 →ₗ[ℝ] LinearMap.range ι55 where
  toFun z :=
    ⟨⁅(X : Cl55), z.1⁆, by
      rcases z.2 with ⟨w, hw⟩
      rw [← hw]
      obtain ⟨w', hw'⟩ := spinBivector_commutator_preserves_vector_image X w
      exact ⟨w', hw'⟩⟩
  map_add' z₁ z₂ := by
    apply Subtype.ext
    exact add_lie (X : Cl55) z₁.1 z₂.1
  map_smul' r z := by
    apply Subtype.ext
    exact lie_smul (X : Cl55) r z.1

/-- The induced linear action of the full native `SpinBivector55` Lie
algebra on `V55`, transported back from the embedded vector subspace. -/
noncomputable def spinBivectorVectorAction (X : SpinBivector55) :
    V55 →ₗ[ℝ] V55 :=
  ι55RangeEquiv.symm.toLinearMap.comp
    ((spinBivectorAdjointOnVectorImage X).comp ι55RangeEquiv.toLinearMap)

/-- The induced vector action is characterized by the Clifford commutator. -/
theorem ι55_spinBivectorVectorAction (X : SpinBivector55) (w : V55) :
    ι55 (spinBivectorVectorAction X w) = ⁅(X : Cl55), ι55 w⁆ := by
  change (ι55RangeEquiv
      (ι55RangeEquiv.symm
        (spinBivectorAdjointOnVectorImage X (ι55RangeEquiv w)))).1 = _
  rw [ι55RangeEquiv.apply_symm_apply]
  change (spinBivectorAdjointOnVectorImage X (ι55RangeEquiv w)).1 = _
  simp [spinBivectorAdjointOnVectorImage, ι55RangeEquiv_apply]

/-- The induced action of `SpinBivector55` on `V55` is a Lie algebra
representation. -/
theorem spinBivectorVectorAction_commutator
    (X Y : SpinBivector55) (w : V55) :
    spinBivectorVectorAction ⁅X, Y⁆ w =
      spinBivectorVectorAction X (spinBivectorVectorAction Y w) -
        spinBivectorVectorAction Y (spinBivectorVectorAction X w) := by
  apply ι55_injective
  calc
    ι55 (spinBivectorVectorAction ⁅X, Y⁆ w) =
        ⁅⁅(X : Cl55), (Y : Cl55)⁆, ι55 w⁆ :=
      ι55_spinBivectorVectorAction ⁅X, Y⁆ w
    _ = ⁅(X : Cl55), ⁅(Y : Cl55), ι55 w⁆⁆ -
        ⁅(Y : Cl55), ⁅(X : Cl55), ι55 w⁆⁆ := by rw [lie_lie]
    _ = ι55 (spinBivectorVectorAction X (spinBivectorVectorAction Y w) -
          spinBivectorVectorAction Y (spinBivectorVectorAction X w)) := by
      rw [map_sub, ι55_spinBivectorVectorAction,
        ι55_spinBivectorVectorAction, ι55_spinBivectorVectorAction]

/-- Linear-map form of the vector-action bracket law. -/
theorem spinBivectorVectorAction_map_lie (X Y : SpinBivector55) :
    spinBivectorVectorAction ⁅X, Y⁆ =
      (spinBivectorVectorAction X).comp (spinBivectorVectorAction Y) -
        (spinBivectorVectorAction Y).comp (spinBivectorVectorAction X) := by
  ext w
  exact spinBivectorVectorAction_commutator X Y w

/-- The full Lie-algebra action induced on the exterior algebra. -/
noncomputable def spinBivectorExteriorAction (X : SpinBivector55) :
    Exterior55 →ₗ[ℝ] Exterior55 :=
  liftExteriorDerivation (spinBivectorVectorAction X)

/-- The exterior-algebra lift is a Lie algebra representation of the native
`SpinBivector55` carrier. -/
theorem spinBivectorExteriorAction_commutator
    (X Y : SpinBivector55) (z : Exterior55) :
    spinBivectorExteriorAction ⁅X, Y⁆ z =
      spinBivectorExteriorAction X (spinBivectorExteriorAction Y z) -
        spinBivectorExteriorAction Y (spinBivectorExteriorAction X z) := by
  change liftExteriorDerivation (spinBivectorVectorAction ⁅X, Y⁆) z = _
  rw [spinBivectorVectorAction_map_lie]
  exact (liftExteriorDerivation_commutator
    (spinBivectorVectorAction X) (spinBivectorVectorAction Y) z).symm

/-- The commutator of two lifted `Cl(5,5)` bivector actions is the lift of
the commutator of their actions on vectors. -/
theorem bivectorExteriorDerivation_commutator
    (u₁ v₁ u₂ v₂ : V55) (x : Exterior55) :
    bivectorExteriorDerivation u₁ v₁ (bivectorExteriorDerivation u₂ v₂ x) -
        bivectorExteriorDerivation u₂ v₂ (bivectorExteriorDerivation u₁ v₁ x) =
      liftExteriorDerivation
        ((bivectorVectorTransformLinear u₁ v₁).comp
            (bivectorVectorTransformLinear u₂ v₂) -
          (bivectorVectorTransformLinear u₂ v₂).comp
            (bivectorVectorTransformLinear u₁ v₁)) x := by
  exact liftExteriorDerivation_commutator
    (bivectorVectorTransformLinear u₁ v₁)
    (bivectorVectorTransformLinear u₂ v₂) x

/-- On degree-one generators, the exterior-algebra commutator agrees with
the Clifford commutator action already proved on `V55`. -/
theorem bivectorExteriorDerivation_commutator_ι
    (u₁ v₁ u₂ v₂ w : V55) :
    bivectorExteriorDerivation u₁ v₁
        (bivectorExteriorDerivation u₂ v₂ (ExteriorAlgebra.ι ℝ w)) -
      bivectorExteriorDerivation u₂ v₂
        (bivectorExteriorDerivation u₁ v₁ (ExteriorAlgebra.ι ℝ w)) =
      ExteriorAlgebra.ι ℝ
        (bivectorVectorTransform u₁ v₁ (bivectorVectorTransform u₂ v₂ w) -
          bivectorVectorTransform u₂ v₂ (bivectorVectorTransform u₁ v₁ w)) := by
  rw [bivectorExteriorDerivation_ι, bivectorExteriorDerivation_ι,
    bivectorExteriorDerivation_ι, bivectorExteriorDerivation_ι, map_sub]

/-- The lifted commutator on a generator is exactly the adjoint Clifford
action of the commutator of the two generating bivectors. -/
theorem bivectorExteriorDerivation_commutator_eq_clifford
    (u₁ v₁ u₂ v₂ w : V55) :
    bivectorExteriorDerivation u₁ v₁
        (bivectorExteriorDerivation u₂ v₂ (ExteriorAlgebra.ι ℝ w)) -
      bivectorExteriorDerivation u₂ v₂
        (bivectorExteriorDerivation u₁ v₁ (ExteriorAlgebra.ι ℝ w)) =
      ⁅⁅ι55 u₁ * ι55 v₁, ι55 u₂ * ι55 v₂⁆, ι55 w⁆ := by
  rw [bivectorExteriorDerivation_commutator_ι]
  exact (bivector_bracket_vector_action u₁ v₁ u₂ v₂ w).symm

end InfoGeometry.Clifford.Cl55ExteriorBivectorLieAction
