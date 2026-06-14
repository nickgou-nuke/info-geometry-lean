import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Pure braid presented-group boundary

This file installs a mathlib `PresentedGroup` boundary for the pure-braid
source used by the Rohozhkin layer. The relation set is explicit and staged
from the standard pure-braid
presentation families used by Rohozhkin--Staic:

* far commutativity for separated ordered pairs;
* the three-index relation
  `bᵢⱼ bᵢₖ bⱼₖ = bⱼₖ bᵢⱼ bᵢₖ = bᵢₖ bⱼₖ bᵢⱼ`;
* the four-index relation
  `bⱼₗ bₖₗ bᵢₖ bⱼₖ = bₖₗ bᵢₖ bⱼₖ bⱼₗ`.

This is a presented-group boundary. It does not yet prove that Rohozhkin's
Delaunay generator matrices satisfy these relators; that is the next descent
obligation before a closed `PBₙ → GL` theorem.
-/

namespace InfoGeometry.Topology.PureBraid

/--
Generator labels for the pure braid group on `n` strands.
The standard presentation uses labels `bᵢⱼ` for `i < j`.
-/
structure PureBraidGenerator (n : ℕ) where
  i : Fin n
  j : Fin n
  lt : i < j
  deriving DecidableEq

/-- The free-group word corresponding to a pure-braid generator `bᵢⱼ`. -/
def b {n : ℕ} (i j : Fin n) (hij : i < j) : FreeGroup (PureBraidGenerator n) :=
  FreeGroup.of { i := i, j := j, lt := hij }

/-- Relator encoding equality `lhs = rhs` as `lhs * rhs⁻¹ = 1`. -/
def relatorEq {α : Type*} (lhs rhs : FreeGroup α) : FreeGroup α :=
  lhs * rhs⁻¹

/-- Far-commutativity relator for separated ordered pairs `i < j < k < l`. -/
def farCommRelator {n : ℕ} (i j k l : Fin n)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    FreeGroup (PureBraidGenerator n) :=
  let _separated : j < k := hjk
  relatorEq ((b i j hij) * (b k l hkl)) ((b k l hkl) * (b i j hij))

/-- First three-index relator: `bᵢⱼ bᵢₖ bⱼₖ = bⱼₖ bᵢⱼ bᵢₖ`. -/
def tripleRelatorLeft {n : ℕ} (i j k : Fin n)
    (hij : i < j) (hjk : j < k) :
    FreeGroup (PureBraidGenerator n) :=
  have hik : i < k := by exact Nat.lt_trans hij hjk
  relatorEq ((b i j hij) * (b i k hik) * (b j k hjk))
    ((b j k hjk) * (b i j hij) * (b i k hik))

/-- Second three-index relator: `bⱼₖ bᵢⱼ bᵢₖ = bᵢₖ bⱼₖ bᵢⱼ`. -/
def tripleRelatorRight {n : ℕ} (i j k : Fin n)
    (hij : i < j) (hjk : j < k) :
    FreeGroup (PureBraidGenerator n) :=
  have hik : i < k := by exact Nat.lt_trans hij hjk
  relatorEq ((b j k hjk) * (b i j hij) * (b i k hik))
    ((b i k hik) * (b j k hjk) * (b i j hij))

/-- Four-index relator: `bⱼₗ bₖₗ bᵢₖ bⱼₖ = bₖₗ bᵢₖ bⱼₖ bⱼₗ`. -/
def quadrupleRelator {n : ℕ} (i j k l : Fin n)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    FreeGroup (PureBraidGenerator n) :=
  have hik : i < k := by exact Nat.lt_trans hij hjk
  have hjl : j < l := by exact Nat.lt_trans hjk hkl
  relatorEq ((b j l hjl) * (b k l hkl) * (b i k hik) * (b j k hjk))
    ((b k l hkl) * (b i k hik) * (b j k hjk) * (b j l hjl))

/-- Explicit staged relator set for the pure braid presentation boundary. -/
def pureBraidRelations (n : ℕ) : Set (FreeGroup (PureBraidGenerator n)) :=
  { r |
    (∃ (i j k l : Fin n) (hij : i < j) (hjk : j < k) (hkl : k < l),
      r = farCommRelator i j k l hij hjk hkl) ∨
    (∃ (i j k : Fin n) (hij : i < j) (hjk : j < k),
      r = tripleRelatorLeft i j k hij hjk) ∨
    (∃ (i j k : Fin n) (hij : i < j) (hjk : j < k),
      r = tripleRelatorRight i j k hij hjk) ∨
    (∃ (i j k l : Fin n) (hij : i < j) (hjk : j < k) (hkl : k < l),
      r = quadrupleRelator i j k l hij hjk hkl) }

/-- The staged pure braid group as a mathlib presented group. -/
def PB (n : ℕ) : Type :=
  PresentedGroup (pureBraidRelations n)

instance (n : ℕ) : Group (PB n) := by
  dsimp [PB]
  infer_instance

/-- Canonical image of a generator in the presented group. -/
def of {n : ℕ} (g : PureBraidGenerator n) : PB n :=
  PresentedGroup.of g

/-- Boundary obligation for descending a generator assignment through `PB n`. -/
def respectsPureBraidRelations {n : ℕ} {G : Type*} [Group G]
    (f : PureBraidGenerator n → G) : Prop :=
  ∀ r ∈ pureBraidRelations n, FreeGroup.lift f r = 1

/-- Universal map out of the presented pure braid boundary once relators are verified. -/
def lift {n : ℕ} {G : Type*} [Group G] (f : PureBraidGenerator n → G)
    (h : respectsPureBraidRelations f) : PB n →* G :=
  PresentedGroup.toGroup h

@[simp]
theorem lift_of {n : ℕ} {G : Type*} [Group G] (f : PureBraidGenerator n → G)
    (h : respectsPureBraidRelations f) (g : PureBraidGenerator n) :
    lift f h (of g) = f g :=
  PresentedGroup.toGroup.of h

end InfoGeometry.Topology.PureBraid
