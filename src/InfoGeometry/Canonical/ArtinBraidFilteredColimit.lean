import Mathlib.GroupTheory.PresentedGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Tactic

/-!
# Artin braid groups as a filtered categorical colimit

This owner defines the finite Artin presentations

`B_{n+1} = <σ₀,...,σ_{n-1} | σᵢσⱼσᵢ = σⱼσᵢσⱼ for j=i+1,
                               σᵢσⱼ = σⱼσᵢ for |i-j|>1>`

with generators `Fin n`.  Stabilization is induced by the canonical inclusion
`Fin n -> Fin m` for `n <= m`.  These maps form a functor `ℕ ⥤ GrpCat`; its
categorical colimit is the algebraic infinite braid group `B∞` used here.

The construction does not assume injectivity of the stabilization maps.  The
classical injectivity theorem is a separate result and is not needed for the
existence or universal property of the filtered colimit.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArtinBraidFilteredColimit

open CategoryTheory CategoryTheory.Limits
open PresentedGroup

/-- Artin generators for the stage `B_{n+1}`. -/
abbrev ArtinGen (n : ℕ) := Fin n

/-- The adjacent Artin relation word. -/
def adjacentWord {n : ℕ} (i j : ArtinGen n) : FreeGroup (ArtinGen n) :=
  (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i) *
    (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹

/-- The distant-commutation relation word. -/
def distantWord {n : ℕ} (i j : ArtinGen n) : FreeGroup (ArtinGen n) :=
  (FreeGroup.of i * FreeGroup.of j) *
    (FreeGroup.of j * FreeGroup.of i)⁻¹

/-- Adjacent-generator relations at stage `n`. -/
def adjacentRelations (n : ℕ) : Set (FreeGroup (ArtinGen n)) :=
  {w | ∃ i j : ArtinGen n, j.1 = i.1 + 1 ∧ w = adjacentWord i j}

/-- Distant-generator relations at stage `n`.
It is enough to orient the pair by `i+1 < j`; the inverse orientation follows
from the same commutation equation. -/
def distantRelations (n : ℕ) : Set (FreeGroup (ArtinGen n)) :=
  {w | ∃ i j : ArtinGen n, i.1 + 1 < j.1 ∧ w = distantWord i j}

/-- Full Artin relation set at finite stage. -/
def artinRelations (n : ℕ) : Set (FreeGroup (ArtinGen n)) :=
  adjacentRelations n ∪ distantRelations n

/-- The presented finite braid group on `n+1` strands, with `n` Artin
generators.  Thus `ArtinBraid 0` is trivial, `ArtinBraid 1 ≅ ℤ`, and
`ArtinBraid 2` is the usual `B₃` presentation. -/
abbrev ArtinBraid (n : ℕ) := PresentedGroup (artinRelations n)

/-- Canonical inclusion of generator labels along `n ≤ m`. -/
def generatorCast {n m : ℕ} (h : n ≤ m) : ArtinGen n → ArtinGen m :=
  fun i => Fin.castLE h i

@[simp] theorem generatorCast_val {n m : ℕ} (h : n ≤ m) (i : ArtinGen n) :
    (generatorCast h i).1 = i.1 := by
  rfl

@[simp] theorem freeMap_adjacentWord {n m : ℕ} (h : n ≤ m)
    (i j : ArtinGen n) :
    FreeGroup.map (generatorCast h) (adjacentWord i j) =
      adjacentWord (generatorCast h i) (generatorCast h j) := by
  simp [adjacentWord, generatorCast]

@[simp] theorem freeMap_distantWord {n m : ℕ} (h : n ≤ m)
    (i j : ArtinGen n) :
    FreeGroup.map (generatorCast h) (distantWord i j) =
      distantWord (generatorCast h i) (generatorCast h j) := by
  simp [distantWord, generatorCast]

/-- Every defining relation at a finite stage remains a defining relation after
stabilizing the generator labels. -/
theorem artinRelations_mapsTo {n m : ℕ} (h : n ≤ m) :
    Set.MapsTo (FreeGroup.map (generatorCast h))
      (artinRelations n) (artinRelations m) := by
  intro w hw
  rcases hw with hw | hw
  · rcases hw with ⟨i, j, hij, rfl⟩
    left
    refine ⟨generatorCast h i, generatorCast h j, ?_, ?_⟩
    · simpa using hij
    · exact freeMap_adjacentWord h i j
  · rcases hw with ⟨i, j, hij, rfl⟩
    right
    refine ⟨generatorCast h i, generatorCast h j, ?_, ?_⟩
    · simpa using hij
    · exact freeMap_distantWord h i j

/-- Stabilization homomorphism `B_{n+1} -> B_{m+1}` induced by the canonical
inclusion of Artin generators. -/
def artinStageMap {n m : ℕ} (h : n ≤ m) : ArtinBraid n →* ArtinBraid m :=
  PresentedGroup.toGroup (f := fun i =>
    (PresentedGroup.of (generatorCast h i) : ArtinBraid m))
    (by
      intro r hr
      have hmap : FreeGroup.lift (fun i =>
          (PresentedGroup.of (generatorCast h i) : ArtinBraid m)) =
          (PresentedGroup.mk (artinRelations m)).comp
            (FreeGroup.map (generatorCast h)) := by
        symm
        apply MonoidHom.ext
        intro r
        exact FreeGroup.lift_unique
          ((PresentedGroup.mk (artinRelations m)).comp
            (FreeGroup.map (generatorCast h)))
          (by intro i; rfl)
      rw [hmap]
      exact PresentedGroup.one_of_mem (artinRelations_mapsTo h hr))

@[simp] theorem artinStageMap_generator {n m : ℕ} (h : n ≤ m)
    (i : ArtinGen n) :
    artinStageMap h (PresentedGroup.of i : ArtinBraid n) =
      (PresentedGroup.of (generatorCast h i) : ArtinBraid m) := by
  rfl

/-- Stabilization along reflexivity is the identity homomorphism. -/
theorem artinStageMap_id (n : ℕ) :
    artinStageMap (le_refl n) = MonoidHom.id (ArtinBraid n) := by
  apply PresentedGroup.ext
  intro i
  simp [generatorCast]

/-- Stabilizations compose exactly. -/
theorem artinStageMap_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (artinStageMap hjk).comp (artinStageMap hij) =
      artinStageMap (le_trans hij hjk) := by
  apply PresentedGroup.ext
  intro a
  simp [generatorCast]

/-- The finite braid stages form a genuine filtered diagram in `GrpCat`. -/
noncomputable def artinBraidDiagram : ℕ ⥤ GrpCat where
  obj n := GrpCat.of (ArtinBraid n)
  map f := GrpCat.ofHom (artinStageMap (leOfHom f))
  map_id n := by
    apply GrpCat.hom_ext
    exact artinStageMap_id n
  map_comp f g := by
    apply GrpCat.hom_ext
    simpa using (artinStageMap_comp (leOfHom f) (leOfHom g)).symm

/-- The algebraic infinite braid group is the categorical filtered colimit of
the finite Artin braid stages. -/
abbrev BInfinity : Type :=
  GrpCat.FilteredColimits.colimit artinBraidDiagram

/-- Canonical finite-stage inclusion into `B∞`. -/
def toBInfinity (n : ℕ) : ArtinBraid n →* BInfinity :=
  (GrpCat.FilteredColimits.colimitCocone artinBraidDiagram).ι.app n |>.hom

/-- `B∞` carries the native colimit certificate. -/
def bInfinity_isColimit : IsColimit
    (GrpCat.FilteredColimits.colimitCocone artinBraidDiagram) :=
  GrpCat.FilteredColimits.colimitCoconeIsColimit artinBraidDiagram

/-- Canonical stage inclusions are compatible with all finite stabilizations. -/
theorem toBInfinity_transition {n m : ℕ} (h : n ≤ m) (g : ArtinBraid n) :
    toBInfinity m (artinStageMap h g) = toBInfinity n g := by
  have hw := (GrpCat.FilteredColimits.colimitCocone artinBraidDiagram).w
    (homOfLE h)
  exact congrArg (fun f => f.hom g) hw

/-- The stable Artin generator `σ_i` represented at any stage containing it. -/
def sigmaInfinity (i : ℕ) : BInfinity :=
  toBInfinity (i + 1)
    (PresentedGroup.of ⟨i, Nat.lt_succ_self i⟩ : ArtinBraid (i + 1))

/-- The same infinite generator can be represented in every later stage. -/
theorem sigmaInfinity_stage {i n : ℕ} (h : i < n) :
    sigmaInfinity i =
      toBInfinity n (PresentedGroup.of ⟨i, h⟩ : ArtinBraid n) := by
  let hle : i + 1 ≤ n := Nat.succ_le_iff.mpr h
  have ht := toBInfinity_transition hle
    (PresentedGroup.of ⟨i, Nat.lt_succ_self i⟩ : ArtinBraid (i + 1))
  simpa [sigmaInfinity, generatorCast] using ht.symm

/-- Adjacent stable generators satisfy the Artin braid relation in `B∞`. -/
theorem sigmaInfinity_artin (i : ℕ) :
    sigmaInfinity i * sigmaInfinity (i + 1) * sigmaInfinity i =
      sigmaInfinity (i + 1) * sigmaInfinity i * sigmaInfinity (i + 1) := by
  let n := i + 2
  let a : ArtinGen n := ⟨i, by omega⟩
  let b : ArtinGen n := ⟨i + 1, by omega⟩
  have hr : adjacentWord a b ∈ artinRelations n := by
    left
    exact ⟨a, b, rfl, rfl⟩
  have hone : PresentedGroup.mk (artinRelations n) (adjacentWord a b) = 1 :=
    PresentedGroup.one_of_mem hr
  have hstage :
      (PresentedGroup.of a : ArtinBraid n) * PresentedGroup.of b * PresentedGroup.of a =
        PresentedGroup.of b * PresentedGroup.of a * PresentedGroup.of b := by
    change PresentedGroup.mk (artinRelations n)
        (FreeGroup.of a * FreeGroup.of b * FreeGroup.of a) =
      PresentedGroup.mk (artinRelations n)
        (FreeGroup.of b * FreeGroup.of a * FreeGroup.of b)
    exact eq_of_mul_inv_eq_one hone
  have hi : sigmaInfinity i = toBInfinity n (PresentedGroup.of a : ArtinBraid n) := by
    exact sigmaInfinity_stage (by omega)
  have hj : sigmaInfinity (i + 1) =
      toBInfinity n (PresentedGroup.of b : ArtinBraid n) := by
    exact sigmaInfinity_stage (by omega)
  rw [hi, hj]
  simpa using congrArg (toBInfinity n) hstage

/-- Stable generators whose indices are separated by at least one strand
commute in `B∞`. -/
theorem sigmaInfinity_commute {i j : ℕ} (h : i + 1 < j) :
    sigmaInfinity i * sigmaInfinity j = sigmaInfinity j * sigmaInfinity i := by
  let n := j + 1
  let a : ArtinGen n := ⟨i, by omega⟩
  let b : ArtinGen n := ⟨j, by omega⟩
  have hr : distantWord a b ∈ artinRelations n := by
    right
    exact ⟨a, b, h, rfl⟩
  have hone : PresentedGroup.mk (artinRelations n) (distantWord a b) = 1 :=
    PresentedGroup.one_of_mem hr
  have hstage :
      (PresentedGroup.of a : ArtinBraid n) * PresentedGroup.of b =
        PresentedGroup.of b * PresentedGroup.of a := by
    change PresentedGroup.mk (artinRelations n) (FreeGroup.of a * FreeGroup.of b) =
      PresentedGroup.mk (artinRelations n) (FreeGroup.of b * FreeGroup.of a)
    exact eq_of_mul_inv_eq_one hone
  have hi : sigmaInfinity i = toBInfinity n (PresentedGroup.of a : ArtinBraid n) := by
    exact sigmaInfinity_stage (by omega)
  have hj : sigmaInfinity j = toBInfinity n (PresentedGroup.of b : ArtinBraid n) := by
    exact sigmaInfinity_stage (by omega)
  rw [hi, hj]
  simpa using congrArg (toBInfinity n) hstage

/-- The cocone determined by a compatible family of finite-stage group maps. -/
def bInfinityCocone {G : Type} [Group G]
    (f : ∀ n, ArtinBraid n →* G)
    (hcompat : ∀ {n m : ℕ} (h : n ≤ m),
      (f m).comp (artinStageMap h) = f n) :
    Cocone artinBraidDiagram where
  pt := GrpCat.of G
  ι :=
    { app := fun n => GrpCat.ofHom (f n)
      naturality := by
        intro n m h
        apply GrpCat.hom_ext
        exact hcompat (leOfHom h) }

/-- Universal descent from `B∞`: every compatible family of finite-stage group
homomorphisms factors through the categorical colimit. -/
def bInfinityDesc {G : Type} [Group G]
    (f : ∀ n, ArtinBraid n →* G)
    (hcompat : ∀ {n m : ℕ} (h : n ≤ m),
      (f m).comp (artinStageMap h) = f n) : BInfinity →* G :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit artinBraidDiagram).desc
    (bInfinityCocone f hcompat) |>.hom

/-- The universal descent has the prescribed value on every finite stage. -/
theorem bInfinityDesc_stage {G : Type} [Group G]
    (f : ∀ n, ArtinBraid n →* G)
    (hcompat : ∀ {n m : ℕ} (h : n ≤ m),
      (f m).comp (artinStageMap h) = f n)
    (n : ℕ) (g : ArtinBraid n) :
    bInfinityDesc f hcompat (toBInfinity n g) = f n g := by
  have hdesc := (GrpCat.FilteredColimits.colimitCoconeIsColimit
    artinBraidDiagram).fac (bInfinityCocone f hcompat) n
  exact congrArg (fun q => q.hom g) hdesc

end InfoGeometry.Canonical.ArtinBraidFilteredColimit
