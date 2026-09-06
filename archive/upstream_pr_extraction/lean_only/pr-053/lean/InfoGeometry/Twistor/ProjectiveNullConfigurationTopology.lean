import InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration
import Mathlib.Topology.Maps.Basic

/-!
# Quotient topologies for projective-null configuration carriers

This owner equips the existing algebraic projective-null carriers with their
canonical induced and quotient topologies.  The topology on Mathlib's
projectivization is the quotient topology of the nonzero-vector carrier; the
null boundary and ordered configuration inherit subtype topologies; and the
unordered configuration receives the quotient topology for finite reindexing.

No fundamental-group computation, spherical-braid identification, monodromy,
or anyon interpretation is asserted here.  Continuity of a particular
projective generator is also a separate theorem requiring an appropriate
continuous-linear hypothesis.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationTopology

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration
open InfoGeometry.Twistor.ProjectiveNullArtinBraid
open Topology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- The quotient topology on Mathlib's projectivization of a topological
vector carrier.  No continuity of the scalar action is needed merely to form
this quotient topology. -/
def projectivizationQuotientTopology [TopologicalSpace V] :
    TopologicalSpace (ℙ K V) :=
  TopologicalSpace.coinduced
    (@Quotient.mk' {v : V // v ≠ 0} (projectivizationSetoid K V))
    inferInstance

/-- The induced projective map is continuous for the named quotient
topologies, provided its underlying injective linear map is continuous. -/
theorem projectivization_map_continuous
    [TopologicalSpace V] [TopologicalSpace W]
    (f : V →ₗ[K] W) (hf : Function.Injective f) (hcont : Continuous f) :
    @Continuous (ℙ K V) (ℙ K W)
      (projectivizationQuotientTopology (K := K) (V := V))
      (projectivizationQuotientTopology (K := K) (V := W))
      (Projectivization.map f hf) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (ℙ K W) :=
    projectivizationQuotientTopology (K := K) (V := W)
  let qV : {v : V // v ≠ 0} → ℙ K V :=
    @Quotient.mk' {v : V // v ≠ 0} (projectivizationSetoid K V)
  let qW : {w : W // w ≠ 0} → ℙ K W :=
    @Quotient.mk' {w : W // w ≠ 0} (projectivizationSetoid K W)
  let h : {v : V // v ≠ 0} → {w : W // w ≠ 0} := fun v =>
    ⟨f v, by
      intro hz
      apply v.property
      apply hf
      simpa using hz⟩
  have hh : Continuous h := by
    have hc : Continuous (fun v : {v : V // v ≠ 0} => f v) :=
      hcont.comp continuous_subtype_val
    simpa [h] using hc.subtype_mk (fun v => by
      intro hz
      apply v.property
      apply hf
      simpa using hz)
  have hqW : Continuous qW := by
    exact continuous_coinduced_rng
  rw [continuous_coinduced_dom]
  have heq : (Projectivization.map f hf) ∘ qV = qW ∘ h := by
    funext v
    change Projectivization.map f hf (Projectivization.mk K v v.property) = _
    rw [Projectivization.map_mk]
    rfl
  change Continuous ((Projectivization.map f hf) ∘ qV)
  rw [heq]
  exact hqW.comp hh

/-- The null boundary inherits the subtype topology from projectivization. -/
def nullBoundaryTopology [TopologicalSpace V] (Q : QuadraticForm K V) :
    TopologicalSpace (TwistorSpace Q) :=
  TopologicalSpace.induced Subtype.val projectivizationQuotientTopology

/-- The null-boundary restriction of a continuous projective generator is
continuous for the induced subtype topology. -/
theorem nullProjectiveGenerator_continuous
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (i : ℕ)
    (hcont : Continuous ((ρ i : V → V))) :
    @Continuous (TwistorSpace Q) (TwistorSpace Q)
      (nullBoundaryTopology Q) (nullBoundaryTopology Q)
      (nullProjectiveGenerator Q ρ hQ i) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  have hp : Continuous (projectiveGenerator ρ i) := by
    exact projectivization_map_continuous
      ((ρ i).toLinearMap) (ρ i).injective hcont
  have hdom : Continuous (fun p : TwistorSpace Q => projectiveGenerator ρ i p.1) :=
    hp.comp continuous_subtype_val
  exact hdom.subtype_mk _

/-- A null-boundary projective generator is a homeomorphism when both the
generator and its inverse are continuous on the underlying vector carrier. -/
theorem nullProjectiveGenerator_isHomeomorph
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (i : ℕ)
    (hcont : Continuous ((ρ i : V → V)))
    (hcont_inv : Continuous (((ρ i).symm : V → V))) :
    @IsHomeomorph (TwistorSpace Q) (TwistorSpace Q)
      (nullBoundaryTopology Q) (nullBoundaryTopology Q)
      (nullProjectiveGenerator Q ρ hQ i) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  let ρinv : ℕ → (V ≃ₗ[K] V) := fun _ => (ρ i).symm
  have hQinv : ∀ j v, Q (ρinv j v) = Q v := by
    intro j v
    dsimp [ρinv]
    rw [← hQ i ((ρ i).symm v)]
    simp
  have hleft : Function.LeftInverse
      (nullProjectiveGenerator Q ρinv hQinv 0)
      (nullProjectiveGenerator Q ρ hQ i) := by
    intro p
    apply Subtype.ext
    change projectiveGenerator ρinv 0
      (projectiveGenerator ρ i p.1) = p.1
    dsimp [ρinv]
    rw [projectiveGenerator, projectiveGenerator]
    change (Projectivization.map ((ρ i).symm : V →ₗ[K] V) _
      (Projectivization.map (ρ i : V →ₗ[K] V) _ p.1)) = p.1
    rw [show Projectivization.map ((ρ i).symm : V →ₗ[K] V) _
        (Projectivization.map (ρ i : V →ₗ[K] V) _ p.1) =
        ((Projectivization.map ((ρ i).symm : V →ₗ[K] V) _ ∘
          Projectivization.map (ρ i : V →ₗ[K] V) _) p.1) by rfl]
    rw [← Projectivization.map_comp]
    simp
  have hright : Function.RightInverse
      (nullProjectiveGenerator Q ρinv hQinv 0)
      (nullProjectiveGenerator Q ρ hQ i) := by
    intro p
    apply Subtype.ext
    change projectiveGenerator ρ i
      (projectiveGenerator (fun _ => (ρ i).symm) 0 p.1) = p.1
    rw [projectiveGenerator, projectiveGenerator]
    change (Projectivization.map (ρ i : V →ₗ[K] V) _
      (Projectivization.map ((ρ i).symm : V →ₗ[K] V) _ p.1)) = p.1
    rw [show Projectivization.map (ρ i : V →ₗ[K] V) _
        (Projectivization.map ((ρ i).symm : V →ₗ[K] V) _ p.1) =
        ((Projectivization.map (ρ i : V →ₗ[K] V) _ ∘
          Projectivization.map ((ρ i).symm : V →ₗ[K] V) _) p.1) by rfl]
    rw [← Projectivization.map_comp]
    simp
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨nullProjectiveGenerator_continuous Q ρ hQ i hcont, _, hleft, hright, ?_⟩
  exact nullProjectiveGenerator_continuous Q ρinv hQinv 0 hcont_inv

/-- Ordered distinct null configurations inherit the subtype topology from
the finite function space of null-boundary points. -/
def orderedConfigurationTopology [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) :
    TopologicalSpace (NullOrderedConfiguration Q n) := by
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  exact TopologicalSpace.induced Subtype.val inferInstance

/-- Reindexing an ordered configuration by a finite permutation is continuous.
This is a symmetry of the configuration carrier, not a braid-exchange path. -/
theorem permute_continuous [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    @Continuous (Ordered Q n) (Ordered Q n)
      (orderedConfigurationTopology Q n) (orderedConfigurationTopology Q n)
      (permute Q n σ) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  have hfun : Continuous (fun p : Ordered Q n => fun j => p.1 (σ j)) := by
    apply continuous_pi
    intro j
    exact (continuous_apply (σ j)).comp continuous_subtype_val
  exact hfun.subtype_mk _

/-- Every finite reindexing is a homeomorphism of the ordered distinct-null
configuration carrier.  Together with `permute_eq_self_imp_eq_refl`, this gives the
precise free-by-homeomorphisms statement, without asserting a covering map. -/
theorem permute_isHomeomorph [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    @IsHomeomorph (Ordered Q n) (Ordered Q n)
      (orderedConfigurationTopology Q n) (orderedConfigurationTopology Q n)
      (permute Q n σ) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨permute_continuous Q n σ, permute Q n σ.symm, ?_, ?_,
    permute_continuous Q n σ.symm⟩
  · intro p
    apply Subtype.ext
    funext j
    simp [permute]
  · intro p
    apply Subtype.ext
    funext j
    simp [permute]

/-- The diagonal action on ordered null configurations is continuous. -/
theorem mapOrderedConfiguration_continuous
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator n : ℕ)
    (hcont : Continuous ((ρ generator : V → V))) :
    @Continuous (NullOrderedConfiguration Q n) (NullOrderedConfiguration Q n)
      (orderedConfigurationTopology Q n) (orderedConfigurationTopology Q n)
      (mapOrderedConfiguration Q ρ hQ generator n) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (NullOrderedConfiguration Q n) :=
    orderedConfigurationTopology Q n
  have hp : Continuous (nullProjectiveGenerator Q ρ hQ generator) :=
    nullProjectiveGenerator_continuous Q ρ hQ generator hcont
  have hfun : Continuous (fun p : NullOrderedConfiguration Q n =>
      fun j => nullProjectiveGenerator Q ρ hQ generator (p.1 j)) := by
    apply continuous_pi
    intro j
    exact hp.comp ((continuous_apply j).comp continuous_subtype_val)
  exact hfun.subtype_mk _

/-- The ordered diagonal generator is a homeomorphism when the generator and
its inverse are continuous on the underlying vector carrier. -/
theorem mapOrderedConfiguration_isHomeomorph
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator n : ℕ)
    (hcont : Continuous ((ρ generator : V → V)))
    (hcont_inv : Continuous (((ρ generator).symm : V → V))) :
    @IsHomeomorph (Ordered Q n) (Ordered Q n)
      (orderedConfigurationTopology Q n) (orderedConfigurationTopology Q n)
      (mapOrderedConfiguration Q ρ hQ generator n) := by
  let ρinv : ℕ → (V ≃ₗ[K] V) := fun _ => (ρ generator).symm
  have hQinv : ∀ i v, Q (ρinv i v) = Q v := by
    intro i v
    dsimp [ρinv]
    rw [← hQ generator ((ρ generator).symm v)]
    simp
  have hleft : Function.LeftInverse
      (mapOrderedConfiguration Q ρinv hQinv 0 n)
      (mapOrderedConfiguration Q ρ hQ generator n) := by
    intro p
    apply Subtype.ext
    funext j
    apply Subtype.ext
    simp only [mapOrderedConfiguration_apply, nullProjectiveGenerator]
    dsimp [ρinv]
    rw [projectiveGenerator, projectiveGenerator]
    change (Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _
      (Projectivization.map (ρ generator : V →ₗ[K] V) _ (p.1 j).1)) = (p.1 j).1
    rw [show Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _
        (Projectivization.map (ρ generator : V →ₗ[K] V) _ (p.1 j).1) =
        ((Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _ ∘
          Projectivization.map (ρ generator : V →ₗ[K] V) _) (p.1 j).1) by rfl]
    rw [← Projectivization.map_comp]
    simp
  have hright : Function.RightInverse
      (mapOrderedConfiguration Q ρinv hQinv 0 n)
      (mapOrderedConfiguration Q ρ hQ generator n) := by
    intro p
    apply Subtype.ext
    funext j
    apply Subtype.ext
    simp only [mapOrderedConfiguration_apply, nullProjectiveGenerator]
    dsimp [ρinv]
    rw [projectiveGenerator, projectiveGenerator]
    change (Projectivization.map (ρ generator : V →ₗ[K] V) _
      (Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _ (p.1 j).1)) = (p.1 j).1
    rw [show Projectivization.map (ρ generator : V →ₗ[K] V) _
        (Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _ (p.1 j).1) =
        ((Projectivization.map (ρ generator : V →ₗ[K] V) _ ∘
          Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _) (p.1 j).1) by rfl]
    rw [← Projectivization.map_comp]
    simp
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨mapOrderedConfiguration_continuous Q ρ hQ generator n hcont,
    mapOrderedConfiguration Q ρinv hQinv 0 n, hleft, hright, ?_⟩
  exact mapOrderedConfiguration_continuous Q ρinv hQinv 0 n hcont_inv

/-- The algebraic unordered configuration quotient receives its canonical
quotient topology. -/
def unorderedConfigurationTopology [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) :
    TopologicalSpace (Unordered Q n) :=
  TopologicalSpace.coinduced
    (@Quotient.mk' (Ordered Q n)
      (InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration.reindexSetoid Q n))
    (orderedConfigurationTopology Q n)

/-- The descended diagonal action on unordered configurations is continuous
for the canonical quotient topology. -/
theorem mapUnorderedConfiguration_continuous
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator n : ℕ)
    (hcont : Continuous ((ρ generator : V → V))) :
    @Continuous (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n) (unorderedConfigurationTopology Q n)
      (mapUnorderedConfiguration Q ρ hQ generator n) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  have ho : Continuous (mapOrderedConfiguration Q ρ hQ generator n) :=
    mapOrderedConfiguration_continuous Q ρ hQ generator n hcont
  apply (continuous_coinduced_dom).2
  rw [show (mapUnorderedConfiguration Q ρ hQ generator n) ∘ Quotient.mk' =
      (Quotient.mk' : Ordered Q n → Unordered Q n) ∘
        mapOrderedConfiguration Q ρ hQ generator n by
    funext p
    rfl]
  exact continuous_quotient_mk'.comp ho

/-- The unordered descended diagonal generator is a homeomorphism under the
same explicit continuity hypotheses. -/
theorem mapUnorderedConfiguration_isHomeomorph
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator n : ℕ)
    (hcont : Continuous ((ρ generator : V → V)))
    (hcont_inv : Continuous (((ρ generator).symm : V → V))) :
    @IsHomeomorph (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n) (unorderedConfigurationTopology Q n)
      (mapUnorderedConfiguration Q ρ hQ generator n) := by
  let ρinv : ℕ → (V ≃ₗ[K] V) := fun _ => (ρ generator).symm
  have hQinv : ∀ i v, Q (ρinv i v) = Q v := by
    intro i v
    dsimp [ρinv]
    rw [← hQ generator ((ρ generator).symm v)]
    simp
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  have hleftOrd : Function.LeftInverse
      (mapOrderedConfiguration Q ρinv hQinv 0 n)
      (mapOrderedConfiguration Q ρ hQ generator n) := by
    intro p
    apply Subtype.ext
    funext j
    apply Subtype.ext
    simp only [mapOrderedConfiguration_apply, nullProjectiveGenerator]
    dsimp [ρinv]
    rw [projectiveGenerator, projectiveGenerator]
    change (Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _
      (Projectivization.map (ρ generator : V →ₗ[K] V) _ (p.1 j).1)) = (p.1 j).1
    rw [show Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _
        (Projectivization.map (ρ generator : V →ₗ[K] V) _ (p.1 j).1) =
        ((Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _ ∘
          Projectivization.map (ρ generator : V →ₗ[K] V) _) (p.1 j).1) by rfl]
    rw [← Projectivization.map_comp]
    simp
  have hrightOrd : Function.RightInverse
      (mapOrderedConfiguration Q ρinv hQinv 0 n)
      (mapOrderedConfiguration Q ρ hQ generator n) := by
    intro p
    apply Subtype.ext
    funext j
    apply Subtype.ext
    simp only [mapOrderedConfiguration_apply, nullProjectiveGenerator]
    dsimp [ρinv]
    rw [projectiveGenerator, projectiveGenerator]
    change (Projectivization.map (ρ generator : V →ₗ[K] V) _
      (Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _ (p.1 j).1)) = (p.1 j).1
    rw [show Projectivization.map (ρ generator : V →ₗ[K] V) _
        (Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _ (p.1 j).1) =
        ((Projectivization.map (ρ generator : V →ₗ[K] V) _ ∘
          Projectivization.map ((ρ generator).symm : V →ₗ[K] V) _) (p.1 j).1) by rfl]
    rw [← Projectivization.map_comp]
    simp
  have hleft : Function.LeftInverse
      (mapUnorderedConfiguration Q ρinv hQinv 0 n)
      (mapUnorderedConfiguration Q ρ hQ generator n) := by
    intro p
    refine Quotient.inductionOn p ?_
    intro c
    change Quotient.mk' (mapOrderedConfiguration Q ρinv hQinv 0 n
      (mapOrderedConfiguration Q ρ hQ generator n c)) = Quotient.mk' c
    exact congrArg Quotient.mk' (hleftOrd c)
  have hright : Function.RightInverse
      (mapUnorderedConfiguration Q ρinv hQinv 0 n)
      (mapUnorderedConfiguration Q ρ hQ generator n) := by
    intro p
    refine Quotient.inductionOn p ?_
    intro c
    change Quotient.mk' (mapOrderedConfiguration Q ρ hQ generator n
      (mapOrderedConfiguration Q ρinv hQinv 0 n c)) = Quotient.mk' c
    exact congrArg Quotient.mk' (hrightOrd c)
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨mapUnorderedConfiguration_continuous Q ρ hQ generator n hcont,
    mapUnorderedConfiguration Q ρinv hQinv 0 n, hleft, hright, ?_⟩
  exact mapUnorderedConfiguration_continuous Q ρinv hQinv 0 n hcont_inv

/-- The ordered and unordered diagonal actions form a commuting quotient
square. -/
theorem unorderedProjection_comp_mapOrderedConfiguration
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator n : ℕ) :
    mapUnorderedConfiguration Q ρ hQ generator n ∘
        (@Quotient.mk' (Ordered Q n)
          (InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration.reindexSetoid Q n)) =
      (@Quotient.mk' (Ordered Q n)
        (InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration.reindexSetoid Q n)) ∘
        mapOrderedConfiguration Q ρ hQ generator n := by
  funext p
  rfl

/-- The ordered-to-unordered projection is continuous for the named canonical
topologies. -/
theorem unorderedProjection_continuous [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) :
    @Continuous (Ordered Q n) (Unordered Q n)
      (orderedConfigurationTopology Q n)
      (unorderedConfigurationTopology Q n)
      (@Quotient.mk' (Ordered Q n)
        (InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration.reindexSetoid Q n)) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact continuous_quotient_mk'

/-- The ordered-to-unordered projection is a quotient map for the named
canonical topologies. -/
theorem unorderedProjection_isQuotientMap [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ) :
    @Topology.IsQuotientMap (Ordered Q n) (Unordered Q n)
      (orderedConfigurationTopology Q n)
      (unorderedConfigurationTopology Q n)
      (@Quotient.mk' (Ordered Q n)
        (InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration.reindexSetoid Q n)) := by
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact isQuotientMap_quotient_mk'

end InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
