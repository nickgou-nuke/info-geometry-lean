import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Maps.Proper.Basic
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology

/-!
# The Cantor boundary as a native topological inverse limit

The finite-prefix carrier `Fin n → Bool` is organized by restriction along
the opposite natural-number order.  This file identifies the existing
product-topological Cantor boundary with the corresponding `TopCat` limit.
No metric completion or measure-theoretic realization is used: the universal
property is the categorical `IsLimit` property of the prefix cone.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-! The restriction map from a longer finite prefix to a shorter one. -/

def prefixRestriction {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (Fin m.unop → Bool) → (Fin n.unop → Bool) := fun w i =>
  w (Fin.castLE (show n.unop ≤ m.unop from leOfHom f.unop) i)

def prefixDiagram : ℕᵒᵖ ⥤ TopCat where
  obj n := TopCat.of (Fin n.unop → Bool)
  map f := { hom' :=
    { toFun := prefixRestriction f
      continuous_toFun := by
        apply continuous_pi
        intro i
        exact continuous_apply _ } }
  map_id n := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    funext i
    rfl
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    funext i
    apply congrArg w
    apply Fin.ext
    rfl

/-! The cone whose projections are the finite boundary prefixes. -/

def prefixCone : Cone prefixDiagram where
  pt := TopCat.of CantorBoundary
  π :=
    { app := fun n =>
        { hom' :=
            { toFun := boundaryPrefix n.unop
              continuous_toFun := continuous_boundaryPrefix n.unop } }
      naturality := by
        intro X Y f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro x
        funext i
        rfl }

/-! The map induced by an arbitrary compatible cone. -/

def prefixLimitLift (s : Cone prefixDiagram) : s.pt ⟶ prefixCone.pt := by
  let f : s.pt → CantorBoundary :=
    fun x n => s.π.app (Opposite.op (n + 1)) x (Fin.last n)
  have hf : Continuous f := by
    apply continuous_pi
    intro n
    exact (continuous_apply (Fin.last n)).comp
      (s.π.app (Opposite.op (n + 1))).hom.continuous
  exact { hom' := { toFun := f, continuous_toFun := hf } }

/-! The finite-prefix cone satisfies the full topological limit universal
property, not merely a pointwise set-theoretic reconstruction. -/

def prefixConeIsLimit : IsLimit prefixCone := by
  refine IsLimit.mk prefixLimitLift ?_ ?_
  · intro s j
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    funext i
    rcases j with ⟨j⟩
    cases j with
    | zero => exact Fin.elim0 i
    | succ k =>
      let hki : i.val + 1 ≤ k + 1 := Nat.succ_le_of_lt i.isLt
      let f : (Opposite.op (k + 1) : ℕᵒᵖ) ⟶ Opposite.op (i.val + 1) :=
        (homOfLE hki).op
      have hn := congrArg (fun q => (ConcreteCategory.hom q) x)
        (s.π.naturality f)
      have hi := congrFun hn (Fin.last i.val)
      change (s.π.app (Opposite.op (i.val + 1))).hom x (Fin.last i.val) =
        (s.π.app (Opposite.op (k + 1))).hom x
          (Fin.castLE hki (Fin.last i.val)) at hi
      have hcast : Fin.castLE hki (Fin.last i.val) = i := by
        apply Fin.ext
        rfl
      rw [hcast] at hi
      simpa [prefixLimitLift, prefixRestriction] using hi
  · intro s m hm
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    funext n
    have h := congrArg (fun q => (ConcreteCategory.hom q) x)
      (hm (Opposite.op (n + 1)))
    have hlast := congrFun h (Fin.last n)
    change (TopCat.Hom.hom m) x n =
      (TopCat.Hom.hom (prefixLimitLift s)) x n
    simpa [prefixLimitLift] using hlast

/-! The categorical limit object is canonically isomorphic to the existing
Cantor boundary carrier. -/

noncomputable def prefixBoundaryLimitIso :
    prefixCone.pt ≅ limit prefixDiagram :=
  prefixConeIsLimit.conePointUniqueUpToIso (limit.isLimit prefixDiagram)

noncomputable instance prefixLimit_compactSpace :
    CompactSpace (↑(limit prefixDiagram)) where
  isCompact_univ := by
    let H := TopCat.homeoOfIso prefixBoundaryLimitIso
    have h := H.isCompact_image.mpr cantorBoundary_compact
    simpa using h

noncomputable instance prefixLimit_t2Space :
    T2Space (↑(limit prefixDiagram)) := by
  letI : T2Space (↑prefixCone.pt) := by
    change T2Space CantorBoundary
    infer_instance
  exact (TopCat.homeoOfIso prefixBoundaryLimitIso).t2Space

theorem prefixBoundaryLimitIso_hom_comp (n : ℕ) :
    prefixBoundaryLimitIso.hom ≫ (limit.π prefixDiagram (Opposite.op n)) =
      prefixCone.π.app (Opposite.op n) := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp prefixConeIsLimit
    (limit.isLimit prefixDiagram) (Opposite.op n)

theorem prefixBoundaryLimitIso_hom_apply (n : ℕ)
    (x : CantorBoundary) (i : Fin n) :
    (limit.π prefixDiagram (Opposite.op n)).hom
        (prefixBoundaryLimitIso.hom.hom x) i = x i := by
  have h := congrArg (fun q => (ConcreteCategory.hom q) x)
    (prefixBoundaryLimitIso_hom_comp n)
  have hi := congrFun h i
  exact hi

/-! Branch self-similarity transported to the categorical limit object. -/

noncomputable def prependBitHom (b : Bool) :
    prefixCone.pt ⟶ prefixCone.pt :=
  { hom' :=
      { toFun := prependBit b
        continuous_toFun := continuous_prependBit b } }

noncomputable def prefixLimitPrependBit (b : Bool) :
    (limit prefixDiagram) ⟶ limit prefixDiagram :=
  prefixBoundaryLimitIso.inv ≫ prependBitHom b ≫ prefixBoundaryLimitIso.hom

theorem prefixLimitPrependBit_continuous (b : Bool) :
    Continuous (ConcreteCategory.hom (prefixLimitPrependBit b)) :=
  (prefixLimitPrependBit b).hom.continuous

theorem prefixLimitPrependBit_projection (b : Bool) (n : ℕ) :
    prefixLimitPrependBit b ≫ limit.π prefixDiagram (Opposite.op n) =
      prefixBoundaryLimitIso.inv ≫ prependBitHom b ≫
        prefixCone.π.app (Opposite.op n) := by
  dsimp [prefixLimitPrependBit]
  simp only [Category.assoc, prefixBoundaryLimitIso_hom_comp]

theorem prefixLimitPrependBit_isClosedEmbedding (b : Bool) :
    Topology.IsClosedEmbedding (ConcreteCategory.hom (prefixLimitPrependBit b)) := by
  let H := TopCat.homeoOfIso prefixBoundaryLimitIso
  have hcomp := H.isClosedEmbedding.comp (prependBit_isClosedEmbedding b)
  have hcomp' := hcomp.comp H.symm.isClosedEmbedding
  simpa [prefixLimitPrependBit, prependBitHom, H, TopCat.homeoOfIso] using hcomp'

theorem prefixLimitPrependBit_image_closed (b : Bool) :
    IsClosed (Set.range (ConcreteCategory.hom (prefixLimitPrependBit b))) :=
  (prefixLimitPrependBit_isClosedEmbedding b).isClosed_range

/-! The transported branch image is the inverse image of the original
clopen branch under the canonical limit homeomorphism. -/

def prefixLimitBranchSet (b : Bool) :
    Set (↑(limit prefixDiagram)) :=
  (TopCat.homeoOfIso prefixBoundaryLimitIso).symm ⁻¹'
    Set.range (prependBit b)

theorem prefixLimitBranchSet_isClopen (b : Bool) :
    IsClopen (prefixLimitBranchSet b) := by
  exact (prependBit_image_clopen b).preimage
    (TopCat.homeoOfIso prefixBoundaryLimitIso).symm.continuous

theorem prefixLimitPrependBit_range (b : Bool) :
    Set.range (ConcreteCategory.hom (prefixLimitPrependBit b)) =
      prefixLimitBranchSet b := by
  let H := TopCat.homeoOfIso prefixBoundaryLimitIso
  have hconj (z : ↑(limit prefixDiagram)) :
      (ConcreteCategory.hom (prefixLimitPrependBit b)) z =
        H (prependBit b (H.symm z)) := by
    rfl
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change H.symm ((ConcreteCategory.hom (prefixLimitPrependBit b)) x) ∈
      Set.range (prependBit b)
    refine ⟨H.symm x, ?_⟩
    have hx := hconj x
    rw [hx]
    simp [H, TopCat.homeoOfIso]
  · intro hy
    rcases hy with ⟨z, hz⟩
    refine ⟨H z, ?_⟩
    have hz' := hconj (H z)
    simp only [H.symm_apply_apply] at hz'
    rw [hz']
    rw [hz]
    simp [H, TopCat.homeoOfIso]

theorem prefixLimitBranchSet_compl (b : Bool) :
    (prefixLimitBranchSet b)ᶜ = prefixLimitBranchSet (!b) := by
  let H := TopCat.homeoOfIso prefixBoundaryLimitIso
  ext x
  change H.symm x ∈ (Set.range (prependBit b))ᶜ ↔
    H.symm x ∈ Set.range (prependBit (!b))
  rw [prependBit_image_compl]

theorem prefixLimitBranchSet_false_true_disjoint :
    Disjoint (prefixLimitBranchSet false) (prefixLimitBranchSet true) := by
  let H := TopCat.homeoOfIso prefixBoundaryLimitIso
  rw [Set.disjoint_left]
  intro x hxFalse hxTrue
  change H.symm x ∈ Set.range (prependBit false) at hxFalse
  change H.symm x ∈ Set.range (prependBit true) at hxTrue
  exact Set.disjoint_left.mp prependBit_false_true_disjoint hxFalse hxTrue

theorem prefixLimitBranchSet_range_cover (x : ↑(limit prefixDiagram)) :
    x ∈ prefixLimitBranchSet false ∪ prefixLimitBranchSet true := by
  let H := TopCat.homeoOfIso prefixBoundaryLimitIso
  change H.symm x ∈ Set.range (prependBit false) ∪
    Set.range (prependBit true)
  exact prependBit_range_cover (H.symm x)

/-! Finite-cylinder topology transported to the categorical limit object. -/

def prefixLimitCylinderSet (n : ℕ) (w : BitWord n) :
    Set (↑(limit prefixDiagram)) :=
  (TopCat.homeoOfIso prefixBoundaryLimitIso).symm ⁻¹'
    cylinderSet n w

theorem prefixLimitCylinderSet_isClopen (n : ℕ) (w : BitWord n) :
    IsClopen (prefixLimitCylinderSet n w) := by
  exact (cylinderSet_isClopen n w).preimage
    (TopCat.homeoOfIso prefixBoundaryLimitIso).symm.continuous

theorem prefixLimitCylinderSet_isCompact (n : ℕ) (w : BitWord n) :
    IsCompact (prefixLimitCylinderSet n w) := by
  apply (TopCat.homeoOfIso prefixBoundaryLimitIso).symm.isCompact_preimage.mpr
  exact cylinderSet_isCompact n w

theorem prefixLimitCylinderSet_separates {x y : ↑(limit prefixDiagram)}
    (hxy : x ≠ y) :
    ∃ (n : ℕ) (w : BitWord n),
      x ∈ prefixLimitCylinderSet n w ∧
        y ∉ prefixLimitCylinderSet n w := by
  let H := TopCat.homeoOfIso prefixBoundaryLimitIso
  have hxy' : H.symm x ≠ H.symm y := by
    intro h
    apply hxy
    exact H.symm.injective h
  obtain ⟨n, w, hx, hy⟩ := cylinderSet_separates hxy'
  refine ⟨n, w, ?_, ?_⟩
  · exact hx
  · exact hy

theorem isTopologicalBasis_prefixLimitCylinderSet :
    TopologicalSpace.IsTopologicalBasis
      {s : Set (↑(limit prefixDiagram)) |
        ∃ (n : ℕ) (w : BitWord n), s = prefixLimitCylinderSet n w} := by
  let H := TopCat.homeoOfIso prefixBoundaryLimitIso
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro s ⟨n, w, rfl⟩
    exact (prefixLimitCylinderSet_isClopen n w).isOpen
  · intro x u hx hu
    have hx' : H.symm x ∈ H ⁻¹' u := by
      change H (H.symm x) ∈ u
      simpa
    have hu' : IsOpen (H ⁻¹' u) := hu.preimage H.continuous
    obtain ⟨v, ⟨n, w, rfl⟩, hy, hsub⟩ :=
      (isTopologicalBasis_cylinderSet.exists_subset_of_mem_open hx' hu')
    refine ⟨prefixLimitCylinderSet n w, ⟨n, w, rfl⟩, ?_, ?_⟩
    · exact hy
    · intro z hz
      have hz' : H.symm z ∈ cylinderSet n w := hz
      have hzU : H.symm z ∈ H ⁻¹' u := hsub hz'
      change H (H.symm z) ∈ u at hzU
      simpa using hzU

theorem prefixLimit_projection_eq_boundaryPrefix (n : ℕ)
    (x : ↑(limit prefixDiagram)) :
    (limit.π prefixDiagram (Opposite.op n)).hom x =
      boundaryPrefix n ((TopCat.homeoOfIso prefixBoundaryLimitIso).symm x) := by
  funext i
  have h := prefixBoundaryLimitIso_hom_apply n
    ((TopCat.homeoOfIso prefixBoundaryLimitIso).symm x) i
  simpa using h

def extendWord (n : ℕ) (w : BitWord n) : CantorBoundary :=
  fun k => if hk : k < n then w ⟨k, hk⟩ else false

theorem boundaryPrefix_extendWord (n : ℕ) (w : BitWord n) :
    boundaryPrefix n (extendWord n w) = w := by
  funext i
  simp [boundaryPrefix, extendWord]

theorem prefixLimit_projection_surjective (n : ℕ) :
    Function.Surjective
      ((limit.π prefixDiagram (Opposite.op n)).hom :
        (↑(limit prefixDiagram) → (Fin n → Bool))) := by
  intro w
  let H := TopCat.homeoOfIso prefixBoundaryLimitIso
  refine ⟨H (extendWord n w), ?_⟩
  rw [prefixLimit_projection_eq_boundaryPrefix]
  simpa [H] using boundaryPrefix_extendWord n w

theorem prefixLimit_projection_isOpenMap (n : ℕ) :
    IsOpenMap
      ((limit.π prefixDiagram (Opposite.op n)).hom :
        (↑(limit prefixDiagram) → (Fin n → Bool))) := by
  letI : DiscreteTopology (↑(prefixDiagram.obj (Opposite.op n))) := by
    change DiscreteTopology (Fin n → Bool)
    infer_instance
  intro U hU
  exact isOpen_discrete _

theorem prefixLimit_projection_isClosedMap (n : ℕ) :
    IsClosedMap
      ((limit.π prefixDiagram (Opposite.op n)).hom :
        (↑(limit prefixDiagram) → (Fin n → Bool))) := by
  letI : T2Space (↑(prefixDiagram.obj (Opposite.op n))) := by
    change T2Space (Fin n → Bool)
    infer_instance
  exact (limit.π prefixDiagram (Opposite.op n)).hom.continuous.isClosedMap

theorem prefixLimit_projection_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap
      ((limit.π prefixDiagram (Opposite.op n)).hom :
        (↑(limit prefixDiagram) → (Fin n → Bool))) :=
  (prefixLimit_projection_isOpenMap n).isQuotientMap
    (limit.π prefixDiagram (Opposite.op n)).hom.continuous
    (prefixLimit_projection_surjective n)

theorem prefixLimit_projection_isOpen_preimage_iff (n : ℕ)
    (s : Set (Fin n → Bool)) :
    IsOpen (((limit.π prefixDiagram (Opposite.op n)).hom ⁻¹' s)) ↔
      IsOpen s :=
  (prefixLimit_projection_isQuotientMap n).isOpen_preimage

theorem prefixLimit_projection_isClosed_preimage_iff (n : ℕ)
    (s : Set (Fin n → Bool)) :
    IsClosed (((limit.π prefixDiagram (Opposite.op n)).hom ⁻¹' s)) ↔
      IsClosed s :=
  (prefixLimit_projection_isQuotientMap n).isClosed_preimage

theorem prefixLimit_projection_map {m n : ℕᵒᵖ} (f : m ⟶ n)
    (x : ↑(limit prefixDiagram)) :
    prefixRestriction f ((limit.π prefixDiagram m).hom x) =
      (limit.π prefixDiagram n).hom x := by
  change (ConcreteCategory.hom (prefixDiagram.map f))
      ((limit.π prefixDiagram m).hom x) =
    (limit.π prefixDiagram n).hom x
  have h := congrArg (fun q => (ConcreteCategory.hom q) x)
    (limit.w prefixDiagram f)
  exact h

theorem prefixLimitCylinderSet_eq_projection_fiber (n : ℕ) (w : BitWord n) :
    prefixLimitCylinderSet n w =
      {x : ↑(limit prefixDiagram) |
        (limit.π prefixDiagram (Opposite.op n)).hom x = w} := by
  ext x
  change boundaryPrefix n ((TopCat.homeoOfIso prefixBoundaryLimitIso).symm x) = w ↔
    (limit.π prefixDiagram (Opposite.op n)).hom x = w
  rw [prefixLimit_projection_eq_boundaryPrefix]

theorem prefixLimitCylinderSet_disjoint {n : ℕ} {w v : BitWord n}
    (h : w ≠ v) :
    Disjoint (prefixLimitCylinderSet n w) (prefixLimitCylinderSet n v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rw [prefixLimitCylinderSet_eq_projection_fiber] at hx hy
  exact h (hx.symm.trans hy)

theorem prefixLimitCylinderSet_mem_partition (n : ℕ)
    (x : ↑(limit prefixDiagram)) :
    ∃ w : BitWord n, x ∈ prefixLimitCylinderSet n w := by
  refine ⟨(limit.π prefixDiagram (Opposite.op n)).hom x, ?_⟩
  rw [prefixLimitCylinderSet_eq_projection_fiber]
  rfl

theorem prefixLimitCylinderSet_iUnion_eq_univ (n : ℕ) :
    (⋃ w : BitWord n, prefixLimitCylinderSet n w) = Set.univ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    obtain ⟨w, hw⟩ := prefixLimitCylinderSet_mem_partition n x
    exact Set.mem_iUnion.2 ⟨w, hw⟩

theorem prefixLimitCylinderSet_nonempty (n : ℕ) (w : BitWord n) :
    (prefixLimitCylinderSet n w).Nonempty := by
  obtain ⟨x, hx⟩ := prefixLimit_projection_surjective n w
  refine ⟨x, ?_⟩
  rw [prefixLimitCylinderSet_eq_projection_fiber]
  exact hx

theorem prefixLimit_projection_isProperMap (n : ℕ) :
    IsProperMap
      ((limit.π prefixDiagram (Opposite.op n)).hom :
        (↑(limit prefixDiagram) → (Fin n → Bool))) := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨(limit.π prefixDiagram (Opposite.op n)).hom.continuous,
    prefixLimit_projection_isClosedMap n, ?_⟩
  intro w
  change IsCompact {x : ↑(limit prefixDiagram) |
    (limit.π prefixDiagram (Opposite.op n)).hom x = w}
  rw [← prefixLimitCylinderSet_eq_projection_fiber n w]
  exact prefixLimitCylinderSet_isCompact n w

theorem prefixLimitCylinderSet_restriction_subset
    {m n : ℕᵒᵖ} (f : m ⟶ n) (w : Fin m.unop → Bool) :
    prefixLimitCylinderSet m.unop w ⊆
      prefixLimitCylinderSet n.unop (prefixRestriction f w) := by
  intro x hx
  rw [prefixLimitCylinderSet_eq_projection_fiber m.unop w] at hx
  rw [prefixLimitCylinderSet_eq_projection_fiber n.unop (prefixRestriction f w)]
  change (limit.π prefixDiagram n).hom x = prefixRestriction f w
  rw [← prefixLimit_projection_map f x, hx]

theorem prefixLimitCylinderSet_restriction_preimage
    {m n : ℕᵒᵖ} (f : m ⟶ n) (w : Fin n.unop → Bool) :
    {x : ↑(limit prefixDiagram) |
        prefixRestriction f ((limit.π prefixDiagram m).hom x) = w} =
      prefixLimitCylinderSet n.unop w := by
  ext x
  rw [prefixLimitCylinderSet_eq_projection_fiber n.unop w]
  change prefixRestriction f ((limit.π prefixDiagram m).hom x) = w ↔
    (limit.π prefixDiagram n).hom x = w
  rw [prefixLimit_projection_map f x]

theorem prefixLimitBranchSet_eq_projection_fiber (b : Bool) :
    prefixLimitBranchSet b =
      {x : ↑(limit prefixDiagram) |
        (limit.π prefixDiagram (Opposite.op 1)).hom x = (fun _ => b)} := by
  rw [← prefixLimitCylinderSet_eq_projection_fiber 1 (fun _ => b)]
  ext x
  change (TopCat.homeoOfIso prefixBoundaryLimitIso).symm x ∈
      Set.range (prependBit b) ↔
    (TopCat.homeoOfIso prefixBoundaryLimitIso).symm x ∈
      cylinderSet 1 (fun _ => b)
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]
    change boundaryPrefix 1 (prependBit b y) = (fun _ => b)
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
  · intro hz
    change boundaryPrefix 1 ((TopCat.homeoOfIso prefixBoundaryLimitIso).symm x) =
      (fun _ => b) at hz
    have hhead : ((TopCat.homeoOfIso prefixBoundaryLimitIso).symm x) 0 = b := by
      exact congrFun hz ⟨0, Nat.zero_lt_succ 0⟩
    exact ⟨tail ((TopCat.homeoOfIso prefixBoundaryLimitIso).symm x),
      prependBit_tail_of_head hhead⟩

theorem prefixLimitPrependBit_projection_apply (b : Bool) (n : ℕ)
    (x : ↑(limit prefixDiagram)) :
    (limit.π prefixDiagram (Opposite.op (n + 1))).hom
        ((ConcreteCategory.hom (prefixLimitPrependBit b)) x) =
      prependWord n b ((limit.π prefixDiagram (Opposite.op n)).hom x) := by
  rw [prefixLimit_projection_eq_boundaryPrefix]
  have hconj := prefixLimitPrependBit_projection b (n + 1)
  have h := congrArg (fun q => (ConcreteCategory.hom q) x) hconj
  have hpre :
      (TopCat.homeoOfIso prefixBoundaryLimitIso).symm
          ((ConcreteCategory.hom (prefixLimitPrependBit b)) x) =
        prependBit b ((TopCat.homeoOfIso prefixBoundaryLimitIso).symm x) := by
    simp [prefixLimitPrependBit, prependBitHom, TopCat.homeoOfIso]
    rfl
  rw [hpre]
  rw [boundaryPrefix_succ_prependBit]
  rw [prefixLimit_projection_eq_boundaryPrefix]

theorem prependWord_injective (n : ℕ) (b : Bool) :
    Function.Injective (prependWord n b) := by
  intro u v huv
  funext i
  have htail := congrFun huv ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
  simpa [prependWord] using htail

theorem prefixLimitPrependBit_cylinder_preimage (b : Bool) (n : ℕ)
    (w : BitWord n) :
    (fun x : ↑(limit prefixDiagram) =>
        (ConcreteCategory.hom (prefixLimitPrependBit b)) x) ⁻¹'
        prefixLimitCylinderSet (n + 1) (prependWord n b w) =
      prefixLimitCylinderSet n w := by
  ext x
  rw [prefixLimitCylinderSet_eq_projection_fiber,
    prefixLimitCylinderSet_eq_projection_fiber]
  change
    (limit.π prefixDiagram (Opposite.op (n + 1))).hom
        ((ConcreteCategory.hom (prefixLimitPrependBit b)) x) =
        prependWord n b w ↔
      (limit.π prefixDiagram (Opposite.op n)).hom x = w
  rw [prefixLimitPrependBit_projection_apply]
  constructor
  · intro h
    apply (prependWord_injective n b)
    simpa using h
  · intro h
    simpa using congrArg (prependWord n b) h

theorem prefixLimitPrependBit_cylinder_image (b : Bool) (n : ℕ)
    (w : BitWord n) :
    ConcreteCategory.hom (prefixLimitPrependBit b) ''
        prefixLimitCylinderSet n w =
      prefixLimitCylinderSet (n + 1) (prependWord n b w) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [prefixLimitCylinderSet_eq_projection_fiber] at hx ⊢
    change (limit.π prefixDiagram (Opposite.op n)).hom x = w at hx
    change (limit.π prefixDiagram (Opposite.op (n + 1))).hom
        ((ConcreteCategory.hom (prefixLimitPrependBit b)) x) =
      prependWord n b w
    rw [prefixLimitPrependBit_projection_apply]
    simp [hx]
  · intro hy
    let H := TopCat.homeoOfIso prefixBoundaryLimitIso
    have hy' : H.symm y ∈ cylinderSet (n + 1) (prependWord n b w) := by
      exact hy
    rw [← cylinderSet_prependBit_image] at hy'
    obtain ⟨x, hx, hxy⟩ := hy'
    refine ⟨H x, ?_, ?_⟩
    · change H.symm (H x) ∈ cylinderSet n w
      simpa using hx
    · apply H.symm.injective
      simpa [prefixLimitPrependBit, prependBitHom, H, TopCat.homeoOfIso] using hxy

end InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
