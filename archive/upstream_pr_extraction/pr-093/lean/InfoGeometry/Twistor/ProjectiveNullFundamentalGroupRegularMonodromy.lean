import InfoGeometry.Twistor.ProjectiveNullConfigurationFundamentalGroup
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# The regular linear monodromy of a based fundamental group

Every based fundamental group acts faithfully by left translation on its free
coefficient module.  This gives a canonical GL-valued monodromy which retains
the full based loop class, rather than factoring through the finite deck
permutation quotient.

This is a based regular representation.  It does not construct a fundamental
groupoid local system, identify braid generators, or supply a Yang--Baxter or
anyon representation.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularMonodromy

/-- The free `R`-module on a group. -/
abbrev GroupRegularModule (R G : Type*) [Semiring R] [Group G] := G →₀ R

/-- Left multiplication by `g`, linearly extended to the free module on `G`. -/
def groupRegularBasisLinearEquiv
    (R G : Type*) [Semiring R] [Group G] (g : G) :
    GroupRegularModule R G ≃ₗ[R] GroupRegularModule R G :=
  Finsupp.domLCongr (Equiv.mulLeft g)

@[simp] theorem groupRegularBasisLinearEquiv_single
    (R G : Type*) [Semiring R] [Group G] (g h : G) (r : R) :
    groupRegularBasisLinearEquiv R G g (Finsupp.single h r) =
      Finsupp.single (g * h) r := by
  exact Finsupp.domLCongr_single (Equiv.mulLeft g) h r

theorem groupRegularBasisLinearEquiv_mul
    (R G : Type*) [Semiring R] [Group G] (g h : G) :
    groupRegularBasisLinearEquiv R G (g * h) =
      groupRegularBasisLinearEquiv R G g *
        groupRegularBasisLinearEquiv R G h := by
  apply LinearEquiv.ext
  intro x
  refine Finsupp.induction x ?_ ?_
  · rfl
  · intro a b f ha hb ih
    have hsingle :
        groupRegularBasisLinearEquiv R G (g * h) (Finsupp.single a b) =
          (groupRegularBasisLinearEquiv R G g *
            groupRegularBasisLinearEquiv R G h) (Finsupp.single a b) := by
      rw [groupRegularBasisLinearEquiv_single]
      change Finsupp.single ((g * h) * a) b =
        groupRegularBasisLinearEquiv R G g
          (groupRegularBasisLinearEquiv R G h (Finsupp.single a b))
      rw [groupRegularBasisLinearEquiv_single,
        groupRegularBasisLinearEquiv_single, mul_assoc]
    rw [map_add, map_add, hsingle, ih]

/-- The left-regular general-linear representation of a group. -/
def groupRegularLinearRepresentation
    (R G : Type*) [Semiring R] [Group G] :
    G →* LinearMap.GeneralLinearGroup R (GroupRegularModule R G) where
  toFun g := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (groupRegularBasisLinearEquiv R G g)
  map_one' := by
    have hone : groupRegularBasisLinearEquiv R G 1 = 1 := by
      apply LinearEquiv.ext
      intro x
      refine Finsupp.induction x rfl ?_
      intro a b f ha hb ih
      rw [map_add, groupRegularBasisLinearEquiv_single, ih, one_mul]
      rfl
    apply Units.ext
    exact congrArg LinearEquiv.toLinearMap hone
  map_mul' g h := by
    apply Units.ext
    exact congrArg LinearEquiv.toLinearMap
      (groupRegularBasisLinearEquiv_mul R G g h)

@[simp] theorem groupRegularLinearRepresentation_single
    (R G : Type*) [Semiring R] [Group G] (g h : G) (r : R) :
    (groupRegularLinearRepresentation R G g :
        GroupRegularModule R G →ₗ[R] GroupRegularModule R G)
        (Finsupp.single h r) = Finsupp.single (g * h) r := by
  exact groupRegularBasisLinearEquiv_single R G g h r

/-- Over a nontrivial coefficient semiring, the regular representation is
faithful. -/
theorem groupRegularLinearRepresentation_injective
    (R G : Type*) [Semiring R] [Nontrivial R] [Group G] :
    Function.Injective (groupRegularLinearRepresentation R G) := by
  intro g h hgh
  have happ := congrArg
    (fun u : LinearMap.GeneralLinearGroup R (GroupRegularModule R G) =>
      (u : GroupRegularModule R G →ₗ[R] GroupRegularModule R G)
        (Finsupp.single 1 (1 : R))) hgh
  simp only [groupRegularLinearRepresentation_single, mul_one] at happ
  exact Finsupp.single_left_injective one_ne_zero happ

/-- The canonical based monodromy on the free module of actual fundamental
group elements. -/
def fundamentalGroupRegularMonodromy
    (R X : Type*) [Semiring R] [TopologicalSpace X] (x : X) :
    FundamentalGroup X x →*
      LinearMap.GeneralLinearGroup R
        (GroupRegularModule R (FundamentalGroup X x)) :=
  groupRegularLinearRepresentation R (FundamentalGroup X x)

@[simp] theorem fundamentalGroupRegularMonodromy_single
    (R X : Type*) [Semiring R] [TopologicalSpace X] (x : X)
    (gamma delta : FundamentalGroup X x) (r : R) :
    (fundamentalGroupRegularMonodromy R X x gamma :
        GroupRegularModule R (FundamentalGroup X x) →ₗ[R]
          GroupRegularModule R (FundamentalGroup X x))
        (Finsupp.single delta r) =
      Finsupp.single (gamma * delta) r := by
  exact groupRegularLinearRepresentation_single R _ gamma delta r

theorem fundamentalGroupRegularMonodromy_injective
    (R X : Type*) [Semiring R] [Nontrivial R] [TopologicalSpace X] (x : X) :
    Function.Injective (fundamentalGroupRegularMonodromy R X x) :=
  groupRegularLinearRepresentation_injective R (FundamentalGroup X x)

/-! ## Functorial and representation readouts of the regular module -/

/-- A group homomorphism induces the linear map of free regular modules which
sends each basis label to its image.  Colliding labels are added by the native
`Finsupp.mapDomain` construction. -/
def groupHomRegularLinearMap
    (R G H : Type*) [Semiring R] [Group G] [Group H] (phi : G →* H) :
    GroupRegularModule R G →ₗ[R] GroupRegularModule R H :=
  Finsupp.lmapDomain R R phi

@[simp] theorem groupHomRegularLinearMap_single
    (R G H : Type*) [Semiring R] [Group G] [Group H]
    (phi : G →* H) (g : G) (r : R) :
    groupHomRegularLinearMap R G H phi (Finsupp.single g r) =
      Finsupp.single (phi g) r := by
  rw [groupHomRegularLinearMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- The free-module map induced by a group homomorphism intertwines the two
left-regular actions. -/
theorem groupHomRegularLinearMap_intertwines
    (R G H : Type*) [Semiring R] [Group G] [Group H]
    (phi : G →* H) (g : G) (x : GroupRegularModule R G) :
    groupHomRegularLinearMap R G H phi
        ((groupRegularLinearRepresentation R G g :
          GroupRegularModule R G →ₗ[R] GroupRegularModule R G) x) =
      (groupRegularLinearRepresentation R H (phi g) :
        GroupRegularModule R H →ₗ[R] GroupRegularModule R H)
        (groupHomRegularLinearMap R G H phi x) := by
  refine Finsupp.induction x ?_ ?_
  · simp
  · intro h r f hh hr ih
    have hsingle :
        groupHomRegularLinearMap R G H phi
            ((groupRegularLinearRepresentation R G g :
              GroupRegularModule R G →ₗ[R] GroupRegularModule R G)
              (Finsupp.single h r)) =
          (groupRegularLinearRepresentation R H (phi g) :
            GroupRegularModule R H →ₗ[R] GroupRegularModule R H)
            (groupHomRegularLinearMap R G H phi (Finsupp.single h r)) := by
      rw [groupRegularLinearRepresentation_single,
        groupHomRegularLinearMap_single,
        groupHomRegularLinearMap_single,
        groupRegularLinearRepresentation_single, map_mul]
    rw [map_add, map_add, map_add, hsingle, ih]
    exact (map_add _ _ _).symm

/-- Evaluation of the free regular module along the orbit of a vector in a
linear representation. -/
def representationOrbitLinearMap
    (R G M : Type*) [Semiring R] [Group G]
    [AddCommMonoid M] [Module R M]
    (rho : G →* LinearMap.GeneralLinearGroup R M) (v : M) :
    GroupRegularModule R G →ₗ[R] M :=
  Finsupp.linearCombination R fun g => (rho g : M →ₗ[R] M) v

@[simp] theorem representationOrbitLinearMap_single
    (R G M : Type*) [Semiring R] [Group G]
    [AddCommMonoid M] [Module R M]
    (rho : G →* LinearMap.GeneralLinearGroup R M)
    (v : M) (g : G) (r : R) :
    representationOrbitLinearMap R G M rho v (Finsupp.single g r) =
      r • (rho g : M →ₗ[R] M) v := by
  exact Finsupp.linearCombination_single (R := R) r g

/-- Orbit evaluation intertwines the regular action with the supplied linear
representation. -/
theorem representationOrbitLinearMap_intertwines
    (R G M : Type*) [Semiring R] [Group G]
    [AddCommMonoid M] [Module R M]
    (rho : G →* LinearMap.GeneralLinearGroup R M)
    (v : M) (g : G) (x : GroupRegularModule R G) :
    representationOrbitLinearMap R G M rho v
        ((groupRegularLinearRepresentation R G g :
          GroupRegularModule R G →ₗ[R] GroupRegularModule R G) x) =
      (rho g : M →ₗ[R] M)
        (representationOrbitLinearMap R G M rho v x) := by
  refine Finsupp.induction x ?_ ?_
  · simp
  · intro h r f hh hr ih
    have hsingle :
        representationOrbitLinearMap R G M rho v
            ((groupRegularLinearRepresentation R G g :
              GroupRegularModule R G →ₗ[R] GroupRegularModule R G)
              (Finsupp.single h r)) =
          (rho g : M →ₗ[R] M)
            (representationOrbitLinearMap R G M rho v
              (Finsupp.single h r)) := by
      rw [groupRegularLinearRepresentation_single,
        representationOrbitLinearMap_single,
        representationOrbitLinearMap_single, map_smul, map_mul]
      rfl
    rw [map_add, map_add, map_add, hsingle, ih]
    exact (map_add _ _ _).symm

/-! ## Exact descent to the range of a group homomorphism -/

/-- A representation descends from `G` to the actual range of `phi : G → H`
whenever it kills the kernel of `phi`. -/
noncomputable def representationOnHomRange
    (G H A : Type*) [Group G] [Group H] [Group A]
    (phi : G →* H) (rho : G →* A) (hker : phi.ker ≤ rho.ker) :
    phi.range →* A :=
  (QuotientGroup.lift phi.ker rho (by
    intro g hg
    exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hker hg)))).comp
      (QuotientGroup.quotientKerEquivRange phi).symm.toMonoidHom

@[simp] theorem representationOnHomRange_rangeRestrict
    (G H A : Type*) [Group G] [Group H] [Group A]
    (phi : G →* H) (rho : G →* A) (hker : phi.ker ≤ rho.ker)
    (g : G) :
    representationOnHomRange G H A phi rho hker (phi.rangeRestrict g) =
      rho g := by
  rw [representationOnHomRange, MonoidHom.comp_apply]
  change QuotientGroup.lift phi.ker rho _
    ((QuotientGroup.quotientKerEquivRange phi).symm
      (phi.rangeRestrict g)) = _
  rw [show (QuotientGroup.quotientKerEquivRange phi).symm
      (phi.rangeRestrict g) = QuotientGroup.mk g by
    apply (QuotientGroup.quotientKerEquivRange phi).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl]
  apply QuotientGroup.lift_mk

/-- Killing the kernel is exactly the criterion for a representation to
factor through the actual range of a group homomorphism. -/
theorem exists_representationOnHomRange_iff
    (G H A : Type*) [Group G] [Group H] [Group A]
    (phi : G →* H) (rho : G →* A) :
    (∃ rhoRange : phi.range →* A,
      rhoRange.comp phi.rangeRestrict = rho) ↔
      phi.ker ≤ rho.ker := by
  constructor
  · rintro ⟨rhoRange, hrange⟩ g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have happ := DFunLike.congr_fun hrange g
    rw [MonoidHom.comp_apply] at happ
    rw [← happ]
    have hr : phi.rangeRestrict g = 1 := by
      apply Subtype.ext
      exact hg
    rw [hr, map_one]
  · intro hker
    refine ⟨representationOnHomRange G H A phi rho hker, ?_⟩
    apply MonoidHom.ext
    intro g
    exact representationOnHomRange_rangeRestrict G H A phi rho hker g

end InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularMonodromy
