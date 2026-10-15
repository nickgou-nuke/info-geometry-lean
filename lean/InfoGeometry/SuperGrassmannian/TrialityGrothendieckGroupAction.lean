import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic.FinCases
import InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive

/-!
# The permutation action on the additive Grothendieck completion of a triple product

For the explicit product ring `A × A × A`, coordinate permutations induce ring
equivalences, and the universal additive Grothendieck completion carries the
resulting `S₃ = Equiv.Perm (Fin 3)` action. The target is stated as
`Multiplicative (AddAut _)` because Mathlib gives `AddAut` its composition group
in additive notation. This is an additive-monoid group completion, not the
projective-module algebraic `K₀` group.
-/

namespace InfoGeometry.SuperGrassmannian.TrialityGrothendieckGroupAction

open InfoGeometry.Algebra
open InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive
open InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive.TrialityRing

noncomputable section

variable (A : Type*) [Ring A]

private def tripleCoordinates : TrialityRing A ≃+* (Fin 3 → A) where
  toFun x := Fin.cases x.1 (Fin.cases x.2.1 (fun _ => x.2.2))
  invFun f := (f 0, f 1, f 2)
  left_inv := by
    intro x
    rcases x with ⟨a, b, c⟩
    rfl
  right_inv := by
    intro f
    funext i
    fin_cases i <;> rfl
  map_mul' := by
    intro x y
    funext i
    fin_cases i <;> rfl
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> rfl

private def coordinateReindex (σ : Equiv.Perm (Fin 3)) :
    (Fin 3 → A) ≃+* (Fin 3 → A) where
  toFun f i := f (σ.symm i)
  invFun f i := f (σ i)
  left_inv := by
    intro f
    funext i
    simp
  right_inv := by
    intro f
    funext i
    simp
  map_mul' := by
    intro f g
    funext i
    rfl
  map_add' := by
    intro f g
    funext i
    rfl

/-- The genuine ring automorphism that reindexes the three product factors by `σ`. -/
def ringReindex (σ : Equiv.Perm (Fin 3)) : TrialityRing A ≃+* TrialityRing A :=
  (tripleCoordinates A).trans ((coordinateReindex A σ).trans (tripleCoordinates A).symm)

@[simp] theorem ringReindex_apply_coord (σ : Equiv.Perm (Fin 3))
    (x : TrialityRing A) (i : Fin 3) :
    tripleCoordinates A (ringReindex A σ x) i =
      tripleCoordinates A x (σ.symm i) := by
  simp [ringReindex, RingEquiv.trans_apply, coordinateReindex]

/-- Reindexing first by `τ` and then by `σ` is the permutation product `σ * τ`. -/
theorem ringReindex_mul (σ τ : Equiv.Perm (Fin 3)) :
    ∀ x, ringReindex A (σ * τ) x = ringReindex A σ (ringReindex A τ x) := by
  intro x
  apply (tripleCoordinates A).injective
  funext i
  simp [ringReindex_apply_coord, Equiv.Perm.mul_def, Equiv.trans_apply,
    Equiv.Perm.symm_mul]

/-- Identity reindexing is the identity ring equivalence. -/
theorem ringReindex_one : ringReindex A (1 : Equiv.Perm (Fin 3)) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  apply (tripleCoordinates A).injective
  funext i
  simp [ringReindex_apply_coord, Equiv.Perm.one_symm]

private abbrev MotiveGroup (A : Type*) [Ring A] :=
  Grothendieck (TrialityRing A)

private def inducedHom {A : Type*} [Ring A] (σ : Equiv.Perm (Fin 3)) :
    MotiveGroup A →+ MotiveGroup A :=
  grothendieckFunctor (ringReindex A σ).toAddMonoidHom

private theorem inducedHom_mul {A : Type*} [Ring A] (σ τ : Equiv.Perm (Fin 3)) :
    (inducedHom (A := A) σ).comp (inducedHom (A := A) τ) =
      inducedHom (A := A) (σ * τ) := by
  apply grothendieck_hom_ext
  intro x
  simp only [inducedHom, grothendieckFunctor_map, AddMonoidHom.coe_comp,
    Function.comp_apply]
  exact congrArg (grothendieckMap (TrialityRing A))
    (ringReindex_mul A σ τ x).symm

private theorem inducedHom_one {A : Type*} [Ring A] :
    inducedHom (A := A) (1 : Equiv.Perm (Fin 3)) =
    AddMonoidHom.id (MotiveGroup A) := by
  change grothendieckFunctor (ringReindex A 1).toAddMonoidHom = _
  rw [ringReindex_one, RingEquiv.toAddMonoidHom_refl, grothendieckFunctor_id]

private def inducedMulEquiv {A : Type*} [Ring A] (σ : Equiv.Perm (Fin 3)) :
    Multiplicative (MotiveGroup A) ≃* Multiplicative (MotiveGroup A) where
  toFun x := Multiplicative.ofAdd (inducedHom (A := A) σ x.toAdd)
  invFun x := Multiplicative.ofAdd (inducedHom (A := A) σ⁻¹ x.toAdd)
  left_inv := by
    intro x
    have h := inducedHom_mul (A := A) σ⁻¹ σ
    have hp : σ⁻¹ * σ = 1 := by simp
    rw [hp, inducedHom_one (A := A)] at h
    have hx := congrArg (fun f : MotiveGroup A →+ MotiveGroup A => f x.toAdd) h
    apply Multiplicative.toAdd.injective
    simpa [AddMonoidHom.comp_apply] using hx
  right_inv := by
    intro x
    have h := inducedHom_mul (A := A) σ σ⁻¹
    have hp : σ * σ⁻¹ = 1 := by simp
    rw [hp, inducedHom_one (A := A)] at h
    have hx := congrArg (fun f : MotiveGroup A →+ MotiveGroup A => f x.toAdd) h
    apply Multiplicative.toAdd.injective
    simpa [AddMonoidHom.comp_apply] using hx
  map_mul' x y := by
    change Multiplicative.ofAdd
        (inducedHom (A := A) σ (x.toAdd + y.toAdd)) =
      Multiplicative.ofAdd
        (inducedHom (A := A) σ x.toAdd + inducedHom (A := A) σ y.toAdd)
    congr 1
    exact (inducedHom (A := A) σ).map_add _ _

/-- The full permutation group acts by multiplicative automorphisms on the
multiplicative type associated to the additive Grothendieck completion. -/
private def grothendieckActionAut :
    Equiv.Perm (Fin 3) →* MulAut (Multiplicative (MotiveGroup A)) where
  toFun σ := inducedMulEquiv (A := A) σ
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Multiplicative.toAdd.injective
    change inducedHom (A := A) 1 x.toAdd = x.toAdd
    rw [inducedHom_one (A := A)]
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    apply Multiplicative.toAdd.injective
    change inducedHom (A := A) (σ * τ) x.toAdd =
      inducedHom (A := A) σ (inducedHom (A := A) τ x.toAdd)
    have h := congrArg (fun f : MotiveGroup A →+ MotiveGroup A => f x.toAdd)
      (inducedHom_mul (A := A) σ τ)
    -- `MulAut` multiplies by ordinary function composition (`f * g = f ∘ g`).
    -- Evaluate the already-proved composition law at the underlying additive
    -- element; its reverse is precisely the pointwise equality required here.
    simpa only [AddMonoidHom.comp_apply] using h.symm

/-- The full permutation group acts by additive automorphisms on the additive
Grothendieck completion of `A × A × A`. -/
def grothendieckAction :
    Equiv.Perm (Fin 3) →* Multiplicative (AddAut (MotiveGroup A)) :=
  (MulAutMultiplicative (MotiveGroup A)).toMonoidHom.comp
    (grothendieckActionAut A)

@[simp] theorem grothendieckAction_apply (σ : Equiv.Perm (Fin 3))
    (x : MotiveGroup A) :
    ((grothendieckAction A σ :
      Multiplicative (AddAut (MotiveGroup A))).toAdd) x =
      inducedHom (A := A) σ x := by
  change (AddEquiv.toMultiplicative.symm
      (inducedMulEquiv (A := A) σ)) x = inducedHom (A := A) σ x
  rfl

end

end InfoGeometry.SuperGrassmannian.TrialityGrothendieckGroupAction
