import InfoGeometry.Lie.E10SerrePresentation

/-!
# Root-lattice weights of the E₁₀ Serre generators

The causal order recorded here is:

`generator weights → bracket-degree addition → Serre-relation degree data`.

This file formalizes that degree bookkeeping for the actual generator type and
Cartan matrix used by `E10.SerreAlgebra`. It does **not** assert that the
quotient has been decomposed into root spaces: that requires proving that the
Serre ideal is homogeneous, which is a later step.
-/

namespace InfoGeometry.Lie.E10

/-- The integral root lattice on the ten simple roots of the E₁₀ presentation. -/
abbrev RootLattice := Fin 10 → ℤ

/-- The `i`-th simple root, as a coordinate vector in the root lattice. -/
def simpleRoot (i : Fin 10) : RootLattice := fun j => if j = i then 1 else 0

@[simp]
theorem simpleRoot_self (i : Fin 10) : simpleRoot i i = 1 := by
  simp [simpleRoot]

@[simp]
theorem simpleRoot_apply_ne {i j : Fin 10} (h : j ≠ i) : simpleRoot i j = 0 := by
  simp [simpleRoot, h]

/-- The prescribed root-lattice degree of each Serre generator. -/
def generatorDegree : CartanMatrix.Generators (Fin 10) → RootLattice
  | .H _ => 0
  | .E i => simpleRoot i
  | .F i => -simpleRoot i

@[simp]
theorem generatorDegree_H (i : Fin 10) : generatorDegree (.H i) = 0 := rfl

@[simp]
theorem generatorDegree_E (i : Fin 10) : generatorDegree (.E i) = simpleRoot i := rfl

@[simp]
theorem generatorDegree_F (i : Fin 10) : generatorDegree (.F i) = -simpleRoot i := rfl

/-- Bracketing homogeneous terms adds their root-lattice degrees. -/
def bracketDegree (α β : RootLattice) : RootLattice := α + β

@[simp]
theorem bracketDegree_HH (i j : Fin 10) :
    bracketDegree (generatorDegree (.H i)) (generatorDegree (.H j)) = 0 := by
  simp [bracketDegree]

@[simp]
theorem bracketDegree_EF_same (i : Fin 10) :
    bracketDegree (generatorDegree (.E i)) (generatorDegree (.F i)) = 0 := by
  simp [bracketDegree]

@[simp]
theorem bracketDegree_HE (i j : Fin 10) :
    bracketDegree (generatorDegree (.H i)) (generatorDegree (.E j)) = simpleRoot j := by
  simp [bracketDegree]

@[simp]
theorem bracketDegree_HF (i j : Fin 10) :
    bracketDegree (generatorDegree (.H i)) (generatorDegree (.F j)) = -simpleRoot j := by
  simp [bracketDegree]

/-- Degree expected for the positive Serre word
`(ad Eᵢ)^(1 - Aᵢⱼ) Eⱼ`. -/
def positiveSerreDegree (i j : Fin 10) : RootLattice :=
  (1 - cartanMatrix i j) • simpleRoot i + simpleRoot j

/-- Degree expected for the negative Serre word
`(ad Fᵢ)^(1 - Aᵢⱼ) Fⱼ`. -/
def negativeSerreDegree (i j : Fin 10) : RootLattice :=
  -positiveSerreDegree i j

/-- The positive Serre degree is the sum of `1 - Aᵢⱼ` copies of αᵢ and αⱼ. -/
theorem positiveSerreDegree_eq (i j : Fin 10) :
    positiveSerreDegree i j = (1 - cartanMatrix i j) • simpleRoot i + simpleRoot j := rfl

/-- The negative Serre degree is the additive inverse of the positive one. -/
theorem negativeSerreDegree_eq (i j : Fin 10) :
    negativeSerreDegree i j = -((1 - cartanMatrix i j) • simpleRoot i + simpleRoot j) := rfl

end InfoGeometry.Lie.E10
