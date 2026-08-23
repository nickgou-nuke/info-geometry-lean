import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Parity
import Mathlib.Data.Finset.Card

/-!
# Concrete D4 root lattice and simple Weyl reflections

This owner supplies the missing explicit `D₄` root-lattice layer.  It uses
integer four-vectors, the standard Euclidean dot product, the even-coordinate
lattice

`D₄ = {x ∈ ℤ⁴ | x₀+x₁+x₂+x₃ is even}`,

and the standard simple roots

`α₁=e₁-e₂`, `α₂=e₂-e₃`, `α₃=e₃-e₄`, `α₄=e₃+e₄`.

The file proves the Cartan/Gram matrix, gives an explicit finite enumeration
of the 24 roots, and proves that reflection in any norm-two lattice root
preserves both the Euclidean norm and the `D₄` lattice.  It deliberately does
not identify an abstract Weyl-group presentation with `W(D₄)`; that is a
separate group-level owner.
-/

namespace InfoGeometry.RootSystem.D4RootLattice

open scoped BigOperators

abbrev Vec4Z := Fin 4 → ℤ

/-- Coordinate sum used to define the even `D₄` lattice. -/
def coordSum (x : Vec4Z) : ℤ := x 0 + x 1 + x 2 + x 3

/-- Standard integral Euclidean pairing on `ℤ⁴`. -/
def dot (x y : Vec4Z) : ℤ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

/-- Squared Euclidean norm. -/
def normSq (x : Vec4Z) : ℤ := dot x x

@[simp] theorem dot_comm (x y : Vec4Z) : dot x y = dot y x := by
  simp [dot]
  ring

/-- The concrete `D₄` lattice: integer four-vectors with even coordinate sum. -/
def D4Lattice : AddSubgroup Vec4Z where
  carrier := {x | Even (coordSum x)}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp [coordSum]
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    simp [coordSum] at ha hb ⊢
    omega
  neg_mem' := by
    intro x hx
    rcases hx with ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    simp [coordSum] at ha ⊢
    omega

@[simp] theorem mem_D4Lattice_iff (x : Vec4Z) :
    x ∈ D4Lattice ↔ Even (coordSum x) :=
  Iff.rfl

/-- Standard simple roots, with the branching node at `α₂`. -/
def simpleRoot : Fin 4 → Vec4Z
  | 0 => ![1, -1, 0, 0]
  | 1 => ![0, 1, -1, 0]
  | 2 => ![0, 0, 1, -1]
  | 3 => ![0, 0, 1, 1]

@[simp] theorem simpleRoot_mem_D4Lattice (i : Fin 4) :
    simpleRoot i ∈ D4Lattice := by
  fin_cases i <;> simp [D4Lattice, coordSum, simpleRoot]

@[simp] theorem simpleRoot_normSq (i : Fin 4) :
    normSq (simpleRoot i) = 2 := by
  fin_cases i <;> norm_num [normSq, dot, simpleRoot]

/-- Standard `D₄` Cartan matrix in the chosen simple-root ordering. -/
def cartanMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0;
     -1, 2, -1, -1;
     0, -1, 2, 0;
     0, -1, 0, 2]

/-- The simple-root Gram matrix is exactly the `D₄` Cartan matrix. -/
theorem simpleRoot_gram_eq_cartan :
    (fun i j : Fin 4 => dot (simpleRoot i) (simpleRoot j)) = cartanMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dot, simpleRoot, cartanMatrix]

/-- A `D₄` root is an integral vector of squared norm two. -/
def IsRoot (x : Vec4Z) : Prop := normSq x = 2

@[simp] theorem simpleRoot_isRoot (i : Fin 4) : IsRoot (simpleRoot i) :=
  simpleRoot_normSq i

/-! ## Explicit finite root enumeration -/

/-- Decode `Fin 3` as `-1,0,1`. -/
def signedCoord : Fin 3 → ℤ
  | 0 => -1
  | 1 => 0
  | 2 => 1

/-- The 81 vectors with all coordinates in `{-1,0,1}`. -/
def smallVector (k : Fin 4 → Fin 3) : Vec4Z := fun i => signedCoord (k i)

/-- Indices of the norm-two small vectors. -/
def rootIndices : Finset (Fin 4 → Fin 3) :=
  Finset.univ.filter (fun k => normSq (smallVector k) = 2)

/-- Explicit finite enumeration of the `D₄` roots. -/
def rootFinset : Finset Vec4Z := rootIndices.image smallVector

/-- The explicit enumeration contains exactly 24 vectors. -/
theorem rootFinset_card : rootFinset.card = 24 := by
  native_decide

/-- Every explicitly enumerated root has squared norm two. -/
theorem rootFinset_isRoot {x : Vec4Z} (hx : x ∈ rootFinset) : IsRoot x := by
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  exact (Finset.mem_filter.mp hk).2

/-- Every explicitly enumerated root lies in the even `D₄` lattice. -/
theorem rootFinset_mem_D4Lattice {x : Vec4Z} (hx : x ∈ rootFinset) :
    x ∈ D4Lattice := by
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  have hroot : normSq (smallVector k) = 2 := (Finset.mem_filter.mp hk).2
  have hall : ∀ k : Fin 4 → Fin 3,
      normSq (smallVector k) = 2 → Even (coordSum (smallVector k)) := by
    native_decide
  exact hall k hroot

/-! ## Weyl reflections -/

/-- Reflection in a norm-two root.  Since `α·α=2`, the usual factor
`2(x·α)/(α·α)` reduces integrally to `x·α`. -/
def reflect (α x : Vec4Z) : Vec4Z :=
  fun i => x i - dot x α * α i

/-- Coordinate sum under reflection. -/
theorem coordSum_reflect (α x : Vec4Z) :
    coordSum (reflect α x) = coordSum x - dot x α * coordSum α := by
  simp [coordSum, reflect]
  ring

/-- Reflection in a norm-two vector preserves the Euclidean norm. -/
theorem normSq_reflect_of_norm_two {α x : Vec4Z} (hα : normSq α = 2) :
    normSq (reflect α x) = normSq x := by
  calc
    normSq (reflect α x) =
        normSq x - 2 * (dot x α) ^ 2 + (dot x α) ^ 2 * normSq α := by
      simp [normSq, dot, reflect]
      ring
    _ = normSq x := by rw [hα]; ring

/-- Reflection in a `D₄` lattice root preserves the `D₄` lattice. -/
theorem reflect_mem_D4Lattice
    {α x : Vec4Z} (hα : α ∈ D4Lattice) (hx : x ∈ D4Lattice) :
    reflect α x ∈ D4Lattice := by
  rcases hα with ⟨a, ha⟩
  rcases hx with ⟨b, hb⟩
  refine ⟨b - dot x α * a, ?_⟩
  rw [coordSum_reflect]
  simp only [coordSum] at ha hb ⊢
  omega

/-- Reflection in a norm-two lattice root preserves the root condition. -/
theorem reflect_isRoot
    {α β : Vec4Z} (hα : IsRoot α) (hβ : IsRoot β) :
    IsRoot (reflect α β) := by
  exact (normSq_reflect_of_norm_two hα).trans hβ

/-- Pairing of a reflected vector with its reflecting root changes sign. -/
theorem dot_reflect_self_of_norm_two
    {α x : Vec4Z} (hα : normSq α = 2) :
    dot (reflect α x) α = - dot x α := by
  calc
    dot (reflect α x) α = dot x α - dot x α * normSq α := by
      simp [dot, normSq, reflect]
      ring
    _ = - dot x α := by rw [hα]; ring

/-- Reflection in a norm-two root is an involution. -/
theorem reflect_involutive_of_norm_two
    {α : Vec4Z} (hα : normSq α = 2) :
    Function.Involutive (reflect α) := by
  intro x
  funext i
  simp [reflect, dot_reflect_self_of_norm_two hα]
  ring

/-- The four simple Weyl reflections. -/
def simpleReflection (i : Fin 4) : Vec4Z → Vec4Z := reflect (simpleRoot i)

@[simp] theorem simpleReflection_involutive (i : Fin 4) :
    Function.Involutive (simpleReflection i) :=
  reflect_involutive_of_norm_two (simpleRoot_normSq i)

@[simp] theorem simpleReflection_preserves_D4
    (i : Fin 4) {x : Vec4Z} (hx : x ∈ D4Lattice) :
    simpleReflection i x ∈ D4Lattice :=
  reflect_mem_D4Lattice (simpleRoot_mem_D4Lattice i) hx

@[simp] theorem simpleReflection_preserves_roots
    (i : Fin 4) {β : Vec4Z} (hβ : IsRoot β) :
    IsRoot (simpleReflection i β) :=
  reflect_isRoot (simpleRoot_isRoot i) hβ

/-! ## Fundamental chamber -/

/-- Closed fundamental chamber for the chosen simple roots, on the integral
Cartan carrier. -/
def InFundamentalChamber (x : Vec4Z) : Prop :=
  ∀ i : Fin 4, 0 ≤ dot x (simpleRoot i)

/-- Coordinate inequalities for the chosen fundamental chamber. -/
theorem inFundamentalChamber_iff (x : Vec4Z) :
    InFundamentalChamber x ↔
      x 0 ≥ x 1 ∧ x 1 ≥ x 2 ∧ x 2 ≥ x 3 ∧ x 2 + x 3 ≥ 0 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    simp [dot, simpleRoot] at h0 h1 h2 h3
    omega
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i <;> simp [dot, simpleRoot] <;> omega

end InfoGeometry.RootSystem.D4RootLattice
