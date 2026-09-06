import InfoGeometry.Canonical.FilteredGNSColimitRepresentation

/-!
# Algebraic Tomita cores in a filtered GNS system

For a positive state `ω`, Mathlib's native pre-GNS carrier is linearly
equivalent to the source C-star algebra.  The algebraic Tomita core is
therefore the conjugate-linear operation

`a Ω ↦ a⋆ Ω`

on that dense carrier.  This file constructs the operation rather than
postulating a modular involution, and proves that it is natural under genuine
unital star-algebra homomorphisms and under the filtered GNS transitions.

No bounded extension, closure, polar decomposition, modular operator, or
Tomita--Takesaki theorem is claimed here.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaCore

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open scoped InnerProductSpace

universe u

variable {A B : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Algebraic Tomita operation on Mathlib's native pre-GNS carrier. -/
def tomitaCore
    (ω : State A) :
    ω.functional.PreGNS → ω.functional.PreGNS :=
  fun x =>
    ω.functional.toPreGNS
      (star (ω.functional.ofPreGNS x))

@[simp] theorem tomitaCore_toPreGNS
    (ω : State A) (a : A) :
    tomitaCore ω (ω.functional.toPreGNS a) =
      ω.functional.toPreGNS (star a) := by
  simp [tomitaCore]

/-- The algebraic Tomita core is involutive before completion. -/
@[simp] theorem tomitaCore_involutive
    (ω : State A) (x : ω.functional.PreGNS) :
    tomitaCore ω (tomitaCore ω x) = x := by
  obtain ⟨a, rfl⟩ := ω.functional.toPreGNS.surjective x
  simp

/-- The algebraic Tomita core fixes the additive identity. -/
@[simp] theorem tomitaCore_zero
    (ω : State A) :
    tomitaCore ω 0 = 0 := by
  unfold tomitaCore
  rw [map_zero, star_zero, map_zero]

/-- Additivity of the algebraic Tomita core. -/
theorem tomitaCore_add
    (ω : State A) (x y : ω.functional.PreGNS) :
    tomitaCore ω (x + y) =
      tomitaCore ω x + tomitaCore ω y := by
  obtain ⟨a, rfl⟩ := ω.functional.toPreGNS.surjective x
  obtain ⟨b, rfl⟩ := ω.functional.toPreGNS.surjective y
  calc
    tomitaCore ω
        (ω.functional.toPreGNS a +
          ω.functional.toPreGNS b) =
      tomitaCore ω
        (ω.functional.toPreGNS (a + b)) := by
          rw [map_add]
    _ = ω.functional.toPreGNS (star (a + b)) :=
      tomitaCore_toPreGNS ω (a + b)
    _ = ω.functional.toPreGNS (star a) +
        ω.functional.toPreGNS (star b) := by
      rw [star_add, map_add]

/-- Conjugate homogeneity of the algebraic Tomita core. -/
theorem tomitaCore_smul
    (ω : State A) (c : ℂ) (x : ω.functional.PreGNS) :
    tomitaCore ω (c • x) =
      star c • tomitaCore ω x := by
  obtain ⟨a, rfl⟩ := ω.functional.toPreGNS.surjective x
  calc
    tomitaCore ω
        (c • ω.functional.toPreGNS a) =
      tomitaCore ω
        (ω.functional.toPreGNS (c • a)) := by
          rw [map_smul]
    _ = ω.functional.toPreGNS (star (c • a)) :=
      tomitaCore_toPreGNS ω (c • a)
    _ = star c •
        ω.functional.toPreGNS (star a) := by
      rw [star_smul, map_smul]

/-- Compatibility with additive inverses. -/
@[simp] theorem tomitaCore_neg
    (ω : State A) (x : ω.functional.PreGNS) :
    tomitaCore ω (-x) = -tomitaCore ω x := by
  have h :=
    tomitaCore_add ω x (-x)
  rw [add_neg_cancel, tomitaCore_zero] at h
  apply eq_neg_of_add_eq_zero_left
  simpa [add_comm] using h.symm

/-- Star-homomorphic GNS transport intertwines the two algebraic Tomita
cores. -/
theorem preGNSMap_tomitaCore
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (x : (ω.restrict f).functional.PreGNS) :
    preGNSMap f ω (tomitaCore (ω.restrict f) x) =
      tomitaCore ω (preGNSMap f ω x) := by
  obtain ⟨a, rfl⟩ :=
    (ω.restrict f).functional.toPreGNS.surjective x
  simp only [tomitaCore_toPreGNS, preGNSMap_toPreGNS]
  rw [map_star]

/-- Dense-core form of Tomita naturality after passing to the completed GNS
spaces. -/
theorem gnsMap_tomitaCore_coe
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (x : (ω.restrict f).functional.PreGNS) :
    gnsMap f ω
        ((tomitaCore (ω.restrict f) x :
          (ω.restrict f).functional.PreGNS) :
          (ω.restrict f).functional.GNS) =
      ((tomitaCore ω (preGNSMap f ω x) :
        ω.functional.PreGNS) :
        ω.functional.GNS) := by
  obtain ⟨a, rfl⟩ :=
    (ω.restrict f).functional.toPreGNS.surjective x
  simp only [tomitaCore_toPreGNS, gnsMap_toPreGNS,
    preGNSMap_toPreGNS]
  rw [map_star]

section Filtered

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

/-- Every filtered GNS transition commutes with the algebraic Tomita
operation on canonical dense vectors. -/
theorem filteredGNSMap_tomitaCore_toPreGNS
    {i j : I} (hij : i ≤ j)
    (a : Stage i) :
    filteredGNSMap Stage sys ω hij
        ((tomitaCore (ω.state i)
          ((ω.state i).functional.toPreGNS a) :
            (ω.state i).functional.PreGNS) :
          (ω.state i).functional.GNS) =
      ((tomitaCore (ω.state j)
          ((ω.state j).functional.toPreGNS
            (sys.map hij a)) :
            (ω.state j).functional.PreGNS) :
        (ω.state j).functional.GNS) := by
  simp only [tomitaCore_toPreGNS,
    filteredGNSMap_toPreGNS]
  rw [map_star]

/-- Equivalent explicit star form of filtered Tomita-core naturality. -/
theorem filteredGNSMap_star_toPreGNS
    {i j : I} (hij : i ≤ j)
    (a : Stage i) :
    filteredGNSMap Stage sys ω hij
        ((ω.state i).functional.toPreGNS (star a) :
          (ω.state i).functional.GNS) =
      ((ω.state j).functional.toPreGNS
          (star (sys.map hij a)) :
        (ω.state j).functional.GNS) := by
  rw [filteredGNSMap_toPreGNS, map_star]

end Filtered

end CStarStateColimit.Native.FilteredGNSTomitaCore
