import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.OperatorAlgebra.GNSMathlibBridge

/-!
# Filtered GNS representations

This file transports Mathlib's native GNS construction along a unital
star-algebra homomorphism.  The state on the source is the contravariant
restriction of the target state.  Consequently the homomorphism preserves the
GNS inner product exactly and induces an isometry on the completed GNS spaces.

No commutativity, simultaneous diagonalization, or coordinate presentation is
assumed.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNS

open CStarStateColimit.Native
open CategoryTheory CategoryTheory.Limits
open scoped InnerProductSpace

universe u

variable {A B C : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- Restriction preserves the full sesquilinear GNS kernel. -/
theorem restricted_star_mul
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a b : A) :
    (ω.restrict f).functional (star a * b) =
      ω.functional (star (f a) * f b) := by
  rw [State.restrict_apply, map_mul, map_star]

/-- In particular, restriction preserves the positive GNS quadratic form. -/
theorem restricted_star_square
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a : A) :
    (ω.restrict f).functional (star a * a) =
      ω.functional (star (f a) * f a) :=
  restricted_star_mul f ω a a

/-- The native GNS-null predicate associated to a positive functional. -/
def IsGNSNull
    (ω : State A)
    (a : A) : Prop :=
  ω.functional (star a * a) = 0

/-- A star homomorphism sends a null vector for the restricted state to a null
vector for the target state. -/
theorem isGNSNull_map
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    {a : A}
    (ha : IsGNSNull (ω.restrict f) a) :
    IsGNSNull ω (f a) := by
  unfold IsGNSNull at ha ⊢
  rw [← restricted_star_square f ω a]
  exact ha

/-- Linear map between Mathlib's pre-GNS spaces induced by a star
homomorphism and contravariant state restriction. -/
def preGNSMap
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    (ω.restrict f).functional.PreGNS →ₗ[ℂ]
      ω.functional.PreGNS :=
  ω.functional.toPreGNS.toLinearMap.comp
    (f.toAlgHom.toLinearMap.comp
      (ω.restrict f).functional.toPreGNS.symm.toLinearMap)

@[simp] theorem preGNSMap_toPreGNS
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a : A) :
    preGNSMap f ω
        ((ω.restrict f).functional.toPreGNS a) =
      ω.functional.toPreGNS (f a) := by
  simp [preGNSMap]

/-- The induced pre-GNS map preserves the inner product on algebra
generators. -/
theorem preGNSMap_inner_toPreGNS
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a b : A) :
    ⟪preGNSMap f ω
          ((ω.restrict f).functional.toPreGNS a),
        preGNSMap f ω
          ((ω.restrict f).functional.toPreGNS b)⟫_ℂ =
      ⟪(ω.restrict f).functional.toPreGNS a,
        (ω.restrict f).functional.toPreGNS b⟫_ℂ := by
  simp [PositiveLinearMap.preGNS_inner_def]
  rw [map_star]

/-- The induced map preserves the complete pre-GNS inner product. -/
theorem preGNSMap_inner
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (x y : (ω.restrict f).functional.PreGNS) :
    ⟪preGNSMap f ω x, preGNSMap f ω y⟫_ℂ =
      ⟪x, y⟫_ℂ := by
  obtain ⟨a, rfl⟩ :=
    (ω.restrict f).functional.toPreGNS.surjective x
  obtain ⟨b, rfl⟩ :=
    (ω.restrict f).functional.toPreGNS.surjective y
  exact preGNSMap_inner_toPreGNS f ω a b

/-- The pre-GNS transport is a native complex-linear isometry. -/
def preGNSLinearIsometry
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    (ω.restrict f).functional.PreGNS →ₗᵢ[ℂ]
      ω.functional.PreGNS :=
  (preGNSMap f ω).isometryOfInner
    (preGNSMap_inner f ω)

@[simp] theorem preGNSLinearIsometry_toPreGNS
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a : A) :
    preGNSLinearIsometry f ω
        ((ω.restrict f).functional.toPreGNS a) =
      ω.functional.toPreGNS (f a) := by
  simp [preGNSLinearIsometry]

/-- The map on completed GNS Hilbert spaces induced by the pre-GNS
isometry. -/
def gnsMap
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    (ω.restrict f).functional.GNS →
      ω.functional.GNS :=
  UniformSpace.Completion.map
    (preGNSLinearIsometry f ω)

/-- Bundled continuous complex-linear form of the completed GNS map. -/
def gnsMapCLM
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    (ω.restrict f).functional.GNS →L[ℂ]
      ω.functional.GNS :=
  (preGNSLinearIsometry f ω).toContinuousLinearMap.completion

@[simp] theorem gnsMapCLM_apply
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (x : (ω.restrict f).functional.GNS) :
    gnsMapCLM f ω x =
      gnsMap f ω x :=
  rfl

/-- The completed GNS map remains an isometry. -/
theorem gnsMap_isometry
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    Isometry (gnsMap f ω) :=
  (preGNSLinearIsometry f ω).isometry.completion_map

/-- The completed map agrees with algebra transport on the dense pre-GNS
subspace. -/
@[simp] theorem gnsMap_toPreGNS
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a : A) :
    gnsMap f ω
        ((ω.restrict f).functional.toPreGNS a :
          (ω.restrict f).functional.GNS) =
      (ω.functional.toPreGNS (f a) :
        ω.functional.GNS) := by
  apply UniformSpace.Completion.map_coe
  exact (preGNSLinearIsometry f ω).isometry.uniformContinuous

/-- On algebra generators, GNS transport respects composition of star
homomorphisms.  This is the dense-subspace form of functoriality and avoids
identifying propositionally equal restricted-state types by an implicit cast. -/
theorem gnsMap_comp_toPreGNS
    (f : A →⋆ₐ[ℂ] B)
    (g : B →⋆ₐ[ℂ] C)
    (ω : State C)
    (a : A) :
    gnsMap g ω
        (gnsMap f (ω.restrict g)
          (((ω.restrict g).restrict f).functional.toPreGNS a :
            ((ω.restrict g).restrict f).functional.GNS)) =
      (ω.functional.toPreGNS (g (f a)) :
        ω.functional.GNS) := by
  rw [gnsMap_toPreGNS, gnsMap_toPreGNS]

/-- The completed GNS transport intertwines the source representation with
the target representation on the canonical dense algebraic subspace. -/
theorem gnsMap_intertwines_toPreGNS
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a b : A) :
    gnsMap f ω
        ((ω.restrict f).functional.gnsStarAlgHom a
          ((ω.restrict f).functional.toPreGNS b :
            (ω.restrict f).functional.GNS)) =
      ω.functional.gnsStarAlgHom (f a)
        (gnsMap f ω
          ((ω.restrict f).functional.toPreGNS b :
            (ω.restrict f).functional.GNS)) := by
  simp [PositiveLinearMap.gnsStarAlgHom,
    PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
    PositiveLinearMap.leftMulMapPreGNS]

/-- The completed GNS transport intertwines the representations on the whole
Hilbert completion.  The proof extends the algebraic identity from the dense
pre-GNS image by continuity. -/
theorem gnsMap_intertwines
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a : A) :
    gnsMap f ω ∘
        (ω.restrict f).functional.gnsStarAlgHom a =
      ω.functional.gnsStarAlgHom (f a) ∘
        gnsMap f ω := by
  apply UniformSpace.Completion.denseRange_coe.equalizer
  · exact
      (gnsMap_isometry f ω).continuous.comp
        ((ω.restrict f).functional.gnsStarAlgHom a).continuous
  · exact
      (ω.functional.gnsStarAlgHom (f a)).continuous.comp
        (gnsMap_isometry f ω).continuous
  · funext x
    obtain ⟨b, rfl⟩ :=
      (ω.restrict f).functional.toPreGNS.surjective x
    exact gnsMap_intertwines_toPreGNS f ω a b

section FilteredSystem

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable
  (sys :
    ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

/-- Equality of native states induces the canonical identification of their
dependent completed GNS spaces. -/
def stateGNSCast
    {D : Type u}
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {ω₁ ω₂ : State D}
    (h : ω₁ = ω₂) :
    ω₁.functional.GNS →
      ω₂.functional.GNS := by
  cases h
  exact id

@[simp] theorem stateGNSCast_toPreGNS
    {D : Type u}
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {ω₁ ω₂ : State D}
    (h : ω₁ = ω₂)
    (a : D) :
    stateGNSCast h
        (ω₁.functional.toPreGNS a :
          ω₁.functional.GNS) =
      (ω₂.functional.toPreGNS a :
        ω₂.functional.GNS) := by
  cases h
  rfl

/-- State equality identifies GNS completions isometrically. -/
theorem stateGNSCast_isometry
    {D : Type u}
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {ω₁ ω₂ : State D}
    (h : ω₁ = ω₂) :
    Isometry (stateGNSCast h) := by
  cases h
  exact isometry_id

/-- Bundled complex-linear isometric form of transport along state
equality. -/
def stateGNSLinearIsometry
    {D : Type u}
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {ω₁ ω₂ : State D}
    (h : ω₁ = ω₂) :
    ω₁.functional.GNS →ₗᵢ[ℂ]
      ω₂.functional.GNS := by
  cases h
  exact LinearIsometry.id

@[simp] theorem stateGNSLinearIsometry_apply
    {D : Type u}
    [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {ω₁ ω₂ : State D}
    (h : ω₁ = ω₂)
    (x : ω₁.functional.GNS) :
    stateGNSLinearIsometry h x =
      stateGNSCast h x := by
  cases h
  rfl

/-- A compatible inverse family of states turns every forward star transition
into a forward isometry of the associated completed GNS spaces. -/
def filteredGNSMap
    {i j : I} (hij : i ≤ j) :
    (ω.state i).functional.GNS →
      (ω.state j).functional.GNS :=
  gnsMap (sys.map hij) (ω.state j) ∘
    stateGNSCast (ω.compatible hij).symm

/-- Bundled continuous complex-linear transition on filtered GNS spaces. -/
def filteredGNSMapCLM
    {i j : I} (hij : i ≤ j) :
    (ω.state i).functional.GNS →L[ℂ]
      (ω.state j).functional.GNS :=
  (gnsMapCLM (sys.map hij) (ω.state j)).comp
    (stateGNSLinearIsometry
      (ω.compatible hij).symm).toContinuousLinearMap

@[simp] theorem filteredGNSMapCLM_apply
    {i j : I} (hij : i ≤ j)
    (x : (ω.state i).functional.GNS) :
    filteredGNSMapCLM Stage sys ω hij x =
      filteredGNSMap Stage sys ω hij x := by
  change
    gnsMapCLM (sys.map hij) (ω.state j)
        (stateGNSLinearIsometry
          (ω.compatible hij).symm x) =
      gnsMap (sys.map hij) (ω.state j)
        (stateGNSCast
          (ω.compatible hij).symm x)
  rw [gnsMapCLM_apply, stateGNSLinearIsometry_apply]

/-- The filtered GNS transition acts on the dense algebraic vectors by the
original noncommutative star-algebra transition. -/
@[simp] theorem filteredGNSMap_toPreGNS
    {i j : I} (hij : i ≤ j)
    (a : Stage i) :
    filteredGNSMap Stage sys ω hij
        ((ω.state i).functional.toPreGNS a :
          (ω.state i).functional.GNS) =
      ((ω.state j).functional.toPreGNS
          (sys.map hij a) :
        (ω.state j).functional.GNS) := by
  unfold filteredGNSMap
  simp only [Function.comp_apply, stateGNSCast_toPreGNS,
    gnsMap_toPreGNS]

/-- Each filtered GNS transition is an isometry. -/
theorem filteredGNSMap_isometry
    {i j : I} (hij : i ≤ j) :
    Isometry (filteredGNSMap Stage sys ω hij) := by
  exact
    (gnsMap_isometry (sys.map hij) (ω.state j)).comp
      (stateGNSCast_isometry (ω.compatible hij).symm)

/-- Filtered GNS transport intertwines the stage representations on the
canonical dense subspace. -/
theorem filteredGNSMap_intertwines_toPreGNS
    {i j : I} (hij : i ≤ j)
    (a b : Stage i) :
    filteredGNSMap Stage sys ω hij
        ((ω.state i).functional.gnsStarAlgHom a
          ((ω.state i).functional.toPreGNS b :
            (ω.state i).functional.GNS)) =
      (ω.state j).functional.gnsStarAlgHom
        (sys.map hij a)
        (filteredGNSMap Stage sys ω hij
          ((ω.state i).functional.toPreGNS b :
            (ω.state i).functional.GNS)) := by
  simp [PositiveLinearMap.gnsStarAlgHom,
    PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
    PositiveLinearMap.leftMulMapPreGNS]

/-- Filtered GNS transport intertwines the stage representations on the whole
completed Hilbert space. -/
theorem filteredGNSMap_intertwines
    {i j : I} (hij : i ≤ j)
    (a : Stage i) :
    filteredGNSMap Stage sys ω hij ∘
        (ω.state i).functional.gnsStarAlgHom a =
      (ω.state j).functional.gnsStarAlgHom
          (sys.map hij a) ∘
        filteredGNSMap Stage sys ω hij := by
  apply UniformSpace.Completion.denseRange_coe.equalizer
  · exact
      (filteredGNSMap_isometry Stage sys ω hij).continuous.comp
        ((ω.state i).functional.gnsStarAlgHom a).continuous
  · exact
      ((ω.state j).functional.gnsStarAlgHom
        (sys.map hij a)).continuous.comp
          (filteredGNSMap_isometry Stage sys ω hij).continuous
  · funext x
    obtain ⟨b, rfl⟩ :=
      (ω.state i).functional.toPreGNS.surjective x
    exact filteredGNSMap_intertwines_toPreGNS
      Stage sys ω hij a b

/-- Identity transitions act identically on the canonical dense GNS
subspace. -/
theorem filteredGNSMap_id_toPreGNS
    (i : I) (a : Stage i) :
    filteredGNSMap Stage sys ω (le_refl i)
        ((ω.state i).functional.toPreGNS a :
          (ω.state i).functional.GNS) =
      ((ω.state i).functional.toPreGNS a :
        (ω.state i).functional.GNS) := by
  rw [filteredGNSMap_toPreGNS]
  rw [sys.map_id]
  rfl

/-- Filtered GNS transitions compose on the canonical dense subspaces
according to the direct-system law. -/
theorem filteredGNSMap_comp_toPreGNS
    {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k)
    (a : Stage i) :
    filteredGNSMap Stage sys ω hjk
        (filteredGNSMap Stage sys ω hij
          ((ω.state i).functional.toPreGNS a :
            (ω.state i).functional.GNS)) =
      filteredGNSMap Stage sys ω (le_trans hij hjk)
        ((ω.state i).functional.toPreGNS a :
          (ω.state i).functional.GNS) := by
  rw [filteredGNSMap_toPreGNS,
    filteredGNSMap_toPreGNS,
    filteredGNSMap_toPreGNS]
  have hmap :=
    congrArg
      (fun F : Stage i →⋆ₐ[ℂ] Stage k => F a)
      (sys.map_comp hij hjk)
  exact congrArg
    (fun x : Stage k =>
      ((ω.state k).functional.toPreGNS x :
        (ω.state k).functional.GNS))
    hmap

/-- The identity law holds on the entire completed GNS space. -/
theorem filteredGNSMap_id
    (i : I) :
    filteredGNSMap Stage sys ω (le_refl i) =
      id := by
  apply UniformSpace.Completion.denseRange_coe.equalizer
  · exact (filteredGNSMap_isometry Stage sys ω (le_refl i)).continuous
  · exact continuous_id
  · funext x
    obtain ⟨a, rfl⟩ :=
      (ω.state i).functional.toPreGNS.surjective x
    exact filteredGNSMap_id_toPreGNS Stage sys ω i a

/-- The direct-system composition law holds on the entire completed GNS
spaces, not only on their algebraic dense subspaces. -/
theorem filteredGNSMap_comp
    {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) :
    filteredGNSMap Stage sys ω hjk ∘
        filteredGNSMap Stage sys ω hij =
      filteredGNSMap Stage sys ω
        (le_trans hij hjk) := by
  apply UniformSpace.Completion.denseRange_coe.equalizer
  · exact
      (filteredGNSMap_isometry Stage sys ω hjk).continuous.comp
        (filteredGNSMap_isometry Stage sys ω hij).continuous
  · exact
      (filteredGNSMap_isometry Stage sys ω
        (le_trans hij hjk)).continuous
  · funext x
    obtain ⟨a, rfl⟩ :=
      (ω.state i).functional.toPreGNS.surjective x
    exact filteredGNSMap_comp_toPreGNS
      Stage sys ω hij hjk a

/-- The completed GNS Hilbert spaces and their transition operators form a
direct inductive system in the existing categorical owner. -/
def gnsDirectInductiveSystem :
    FilteredColimit.DirectInductiveSystem
      ℂ I (fun i => (ω.state i).functional.GNS) where
  f := fun hij =>
    (filteredGNSMapCLM Stage sys ω hij).toLinearMap
  f_id := by
    intro i
    ext x
    change
      filteredGNSMapCLM Stage sys ω (le_refl i) x = x
    rw [filteredGNSMapCLM_apply]
    exact congrFun
      (filteredGNSMap_id Stage sys ω i) x
  f_comp := by
    intro i j k hij hjk
    ext x
    change
      filteredGNSMapCLM Stage sys ω hjk
          (filteredGNSMapCLM Stage sys ω hij x) =
        filteredGNSMapCLM Stage sys ω
          (le_trans hij hjk) x
    rw [filteredGNSMapCLM_apply,
      filteredGNSMapCLM_apply,
      filteredGNSMapCLM_apply]
    exact congrFun
      (filteredGNSMap_comp Stage sys ω hij hjk) x

/-- Universe-polymorphic `ModuleCat` diagram of the completed GNS system.
Unlike the older generic owner, this does not force the scalar ring `ℂ` and
the stage carriers to inhabit the same universe. -/
def gnsModuleDiagram :
    I ⥤ ModuleCat.{u} ℂ where
  obj i :=
    ModuleCat.of ℂ
      ((ω.state i).functional.GNS)
  map f :=
    ModuleCat.ofHom
      ((gnsDirectInductiveSystem Stage sys ω).f
        (leOfHom f))
  map_id i := by
    ext x
    exact LinearMap.congr_fun
      ((gnsDirectInductiveSystem Stage sys ω).f_id i) x
  map_comp f g := by
    ext x
    exact LinearMap.congr_fun
      ((gnsDirectInductiveSystem Stage sys ω).f_comp
        (leOfHom f) (leOfHom g)).symm x

/-- The native `ModuleCat` colimit of the completed GNS direct system. -/
noncomputable abbrev GNSModuleColimit : Type u :=
  (colimit (gnsModuleDiagram Stage sys ω) :
    ModuleCat.{u} ℂ)

/-- Canonical linear inclusion of a stage GNS space into the native
categorical colimit. -/
noncomputable def gnsColimitInclusion
    (i : I) :
    (ω.state i).functional.GNS →ₗ[ℂ]
      GNSModuleColimit Stage sys ω :=
  (colimit.ι
    (gnsModuleDiagram Stage sys ω) i).hom

/-- The categorical GNS inclusions commute with every filtered transition. -/
theorem gnsColimitInclusion_transition
    {i j : I} (hij : i ≤ j)
    (x : (ω.state i).functional.GNS) :
    gnsColimitInclusion Stage sys ω i x =
      gnsColimitInclusion Stage sys ω j
        (filteredGNSMap Stage sys ω hij x) := by
  let F :=
    gnsModuleDiagram Stage sys ω
  have hw := colimit.w F (homOfLE hij)
  have hx := congrArg
    (fun k : F.obj i ⟶ CategoryTheory.Limits.colimit F => k x)
    hw.symm
  have htransition :
      (gnsDirectInductiveSystem Stage sys ω).f hij x =
        filteredGNSMap Stage sys ω hij x := by
    change
      filteredGNSMapCLM Stage sys ω hij x =
        filteredGNSMap Stage sys ω hij x
    exact filteredGNSMapCLM_apply Stage sys ω hij x
  simpa [F, gnsColimitInclusion, gnsModuleDiagram,
    htransition] using hx

/-- Stage representations define the same vector in the GNS colimit after
transporting both the observable and vector to a later stage. -/
theorem gnsColimitInclusion_representation_compat
    {i j : I} (hij : i ≤ j)
    (a : Stage i)
    (x : (ω.state i).functional.GNS) :
    gnsColimitInclusion Stage sys ω i
        ((ω.state i).functional.gnsStarAlgHom a x) =
      gnsColimitInclusion Stage sys ω j
        ((ω.state j).functional.gnsStarAlgHom
          (sys.map hij a)
          (filteredGNSMap Stage sys ω hij x)) := by
  rw [gnsColimitInclusion_transition Stage sys ω hij]
  have hintertwine :=
    congrFun
      (filteredGNSMap_intertwines
        Stage sys ω hij a) x
  exact congrArg
    (gnsColimitInclusion Stage sys ω j)
    hintertwine

end FilteredSystem

end CStarStateColimit.Native.FilteredGNS
