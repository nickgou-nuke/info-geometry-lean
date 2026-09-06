import InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy
import InfoGeometry.Twistor.ProjectiveNullConfigurationPermutationLinearMonodromy

/-!
# The covering local system of unordered projective-null configurations

Path lifting for the finite ordered-to-unordered configuration covering gives
an equivalence between the fibers over the endpoints of every fundamental-
groupoid morphism.  Linearizing those fiber equivalences with
`Finsupp.domLCongr` produces a concrete `ModuleCat`-valued local system.

At a chosen ordered base configuration, its linear monodromy sends each fiber
basis vector to the basis vector at the lifted endpoint.  Under the existing
identification of the fiber with `S_n`, this is exactly left multiplication by
the already proved permutation monodromy.

This is a genuine covering local system.  It is not asserted to be a conformal-
block bundle, an Artin or spherical-braid representation, or an anyon theory.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationCoveringLocalSystem

open CategoryTheory
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationFiberEquiv
open InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-! ## Generic covering local system -/

/-- A path-homotopy class in the base of a covering induces an equivalence of
its endpoint fibers. -/
def coveringMonodromyPathEquiv
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (cov : IsCoveringMap f) {x y : X}
    (gamma : Path.Homotopic.Quotient x y) :
    {e : E // f e = x} ≃ {e : E // f e = y} where
  toFun := cov.monodromy gamma
  invFun := cov.monodromy gamma.symm
  left_inv e := by
    rw [← coveringMonodromy_trans_apply cov gamma gamma.symm e,
      Path.Homotopic.Quotient.trans_symm, cov.monodromy_refl]
    rfl
  right_inv e := by
    rw [← coveringMonodromy_trans_apply cov gamma.symm gamma e,
      Path.Homotopic.Quotient.symm_trans, cov.monodromy_refl]
    rfl

@[simp] theorem coveringMonodromyPathEquiv_refl
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (cov : IsCoveringMap f) (x : X) :
    coveringMonodromyPathEquiv cov (Path.Homotopic.Quotient.refl x) =
      Equiv.refl {e : E // f e = x} := by
  apply Equiv.ext
  intro e
  exact congrFun cov.monodromy_refl e

theorem coveringMonodromyPathEquiv_trans
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (cov : IsCoveringMap f) {x y z : X}
    (gamma : Path.Homotopic.Quotient x y)
    (delta : Path.Homotopic.Quotient y z) :
    (coveringMonodromyPathEquiv cov gamma).trans
        (coveringMonodromyPathEquiv cov delta) =
      coveringMonodromyPathEquiv cov (gamma.trans delta) := by
  apply Equiv.ext
  intro e
  exact (coveringMonodromy_trans_apply cov gamma delta e).symm

/-- The free-module local system obtained by linearizing the fibers and path
lifting of a covering map. -/
def coveringFiberLinearLocalSystem
    (R : Type*) [Ring R]
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (cov : IsCoveringMap f) :
    FundamentalGroupoid X ⥤ ModuleCat R where
  obj x := ModuleCat.of R ({e : E // f e = x.as} →₀ R)
  map {x y} gamma := ModuleCat.ofHom
    (Finsupp.domLCongr (R := R) (M := R)
      (coveringMonodromyPathEquiv cov gamma)).toLinearMap
  map_id x := by
    change ModuleCat.ofHom (Finsupp.domLCongr (R := R) (M := R)
      (coveringMonodromyPathEquiv cov
        (Path.Homotopic.Quotient.refl x.as))).toLinearMap =
      𝟙 (ModuleCat.of R ({e : E // f e = x.as} →₀ R))
    rw [coveringMonodromyPathEquiv_refl]
    ext u i
    simp
  map_comp gamma delta := by
    change ModuleCat.ofHom (Finsupp.domLCongr (R := R) (M := R)
      (coveringMonodromyPathEquiv cov (gamma.trans delta))).toLinearMap =
      ModuleCat.ofHom (Finsupp.domLCongr (R := R) (M := R)
        (coveringMonodromyPathEquiv cov gamma)).toLinearMap ≫
      ModuleCat.ofHom (Finsupp.domLCongr (R := R) (M := R)
        (coveringMonodromyPathEquiv cov delta)).toLinearMap
    rw [← coveringMonodromyPathEquiv_trans]
    ext u i
    simp

/-! ## Projective-null configuration specialization -/

variable {R K V : Type*} [Ring R] [Field K] [AddCommGroup V] [Module K V]

/-- The concrete free-module local system of the finite ordered-configuration
covering over unordered projective-null configurations. -/
def unorderedConfigurationCoveringLocalSystem
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n)) :
    ConfigurationLocalSystem R Q n := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact coveringFiberLinearLocalSystem R
    (unorderedProjection_isQuotientCoveringMap Q n hLC hT2).isCoveringMap

/-- The canonical linear identification of the covering-local-system fiber at
an ordered base configuration with the free module on its deck labels
`S_n`. -/
def unorderedConfigurationCoveringFiberLinearEquiv
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n) :
    ({q : Ordered Q n //
        Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} →₀ R) ≃ₗ[R]
      DeckPermutationModule R n :=
  Finsupp.domLCongr (R := R) (M := R) (orderedFiberEquivPerm Q n p).symm

@[simp] theorem unorderedConfigurationCoveringFiberLinearEquiv_single
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n)
    (q : {r : Ordered Q n //
      Quotient.mk' r = (Quotient.mk' p : Unordered Q n)}) (a : R) :
    unorderedConfigurationCoveringFiberLinearEquiv (R := R) Q n p
        (Finsupp.single q a) =
      Finsupp.single ((orderedFiberEquivPerm Q n p).symm q) a := by
  exact Finsupp.domLCongr_single (orderedFiberEquivPerm Q n p).symm q a

/-- Over a field, every covering-local-system fiber has dimension `n!`: its
canonical basis is the deck-label set `S_n`. -/
theorem unorderedConfigurationCoveringFiber_finrank
    {F : Type*} [Field F]
    (Q : QuadraticForm K V) (n : ℕ) (p : Ordered Q n) :
    Module.finrank F
        ({q : Ordered Q n //
          Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} →₀ F) =
      n.factorial := by
  rw [(unorderedConfigurationCoveringFiberLinearEquiv (R := F) Q n p).finrank_eq]
  change Module.finrank F (Equiv.Perm (Fin n) →₀ F) = n.factorial
  rw [Module.finrank_eq_card_basis Finsupp.basisSingleOne]
  simp [Fintype.card_perm]

/-- On the native covering-fiber basis, local-system monodromy is exactly the
lifted-endpoint action. -/
@[simp] theorem unorderedConfigurationCoveringLocalSystem_monodromy_single
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (q : {r : Ordered Q n //
      Quotient.mk' r = (Quotient.mk' p : Unordered Q n)}) (a : R) :
    let L := unorderedConfigurationCoveringLocalSystem (R := R) Q n hLC hT2
    let _inst : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    (localSystemLinearMonodromy Q n L (Quotient.mk' p) gamma :
      Module.End R (L.obj (FundamentalGroupoid.mk (Quotient.mk' p))))
        (Finsupp.single q a) =
      Finsupp.single
        (unorderedConfigurationFiberMonodromy Q n hLC hT2 p gamma q) a := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  change (Finsupp.domLCongr (R := R) (M := R)
    (coveringMonodromyPathEquiv
      (unorderedProjection_isQuotientCoveringMap Q n hLC hT2).isCoveringMap gamma))
      (Finsupp.single q a) = _
  rw [Finsupp.domLCongr_single]
  rfl

/-- Under the canonical `S_n` labeling of the covering fiber, the same local-
system monodromy is left multiplication by permutation monodromy. -/
@[simp] theorem unorderedConfigurationCoveringLocalSystem_monodromy_label_single
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (tau : Equiv.Perm (Fin n)) (a : R) :
    let L := unorderedConfigurationCoveringLocalSystem (R := R) Q n hLC hT2
    let _inst : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    (localSystemLinearMonodromy Q n L (Quotient.mk' p) gamma :
      Module.End R (L.obj (FundamentalGroupoid.mk (Quotient.mk' p))))
        (Finsupp.single (orderedFiberEquivPerm Q n p tau) a) =
      Finsupp.single
        (orderedFiberEquivPerm Q n p
          (unorderedCoveringPermutationMonodromy Q n hLC hT2 p gamma * tau)) a := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  change (Finsupp.domLCongr (R := R) (M := R)
    (coveringMonodromyPathEquiv
      (unorderedProjection_isQuotientCoveringMap Q n hLC hT2).isCoveringMap gamma))
      (Finsupp.single (orderedFiberEquivPerm Q n p tau) a) = _
  rw [Finsupp.domLCongr_single]
  change Finsupp.single
      (unorderedConfigurationFiberMonodromy Q n hLC hT2 p gamma
        (orderedFiberEquivPerm Q n p tau)) a = _
  rw [unorderedConfigurationFiberMonodromy_orderedFiberEquivPerm]

/-- The canonical fiber labeling intertwines the complete covering-local-
system monodromy operator with the already constructed left-regular
permutation monodromy, not merely their individual basis readouts. -/
theorem unorderedConfigurationCoveringFiberLinearEquiv_intertwines_monodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (gamma : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) (Quotient.mk' p))
    (x : {q : Ordered Q n //
      Quotient.mk' q = (Quotient.mk' p : Unordered Q n)} →₀ R) :
    let L := unorderedConfigurationCoveringLocalSystem (R := R) Q n hLC hT2
    let _inst : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    unorderedConfigurationCoveringFiberLinearEquiv (R := R) Q n p
        ((localSystemLinearMonodromy Q n L (Quotient.mk' p) gamma :
          Module.End R (L.obj (FundamentalGroupoid.mk (Quotient.mk' p)))) x) =
      (unorderedCoveringPermutationLinearMonodromy R Q n hLC hT2 p gamma :
        Module.End R (DeckPermutationModule R n))
        (unorderedConfigurationCoveringFiberLinearEquiv (R := R) Q n p x) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  dsimp only
  refine Finsupp.induction x ?_ ?_
  · simp
  · intro q a f hq hf ih
    rw [map_add, map_add, map_add, ih]
    let tau := (orderedFiberEquivPerm Q n p).symm q
    have hq_eq : q = orderedFiberEquivPerm Q n p tau := by
      exact ((orderedFiberEquivPerm Q n p).apply_symm_apply q).symm
    rw [hq_eq]
    rw [unorderedConfigurationCoveringLocalSystem_monodromy_label_single,
      unorderedConfigurationCoveringFiberLinearEquiv_single,
      unorderedConfigurationCoveringFiberLinearEquiv_single]
    simp [tau]

end InfoGeometry.Twistor.ProjectiveNullConfigurationCoveringLocalSystem
