import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace InfoGeometry.Topology.Delaunay

/-- Abstract parameter space for the rational flip matrices -/
structure FlipLabels (ι : Type*) where
  ζ : ι → ℚ
  nonzero_den : ∀ {i k : ι}, i ≠ k → ζ i - ζ k ≠ 0

variable {ι : Type*} [DecidableEq ι] (labels : FlipLabels ι)

/-- The local 2x2 rational block for a Delaunay flip ik -> jl -/
noncomputable def flipBlock (i k j l : ι) (hik : i ≠ k) : Matrix (Fin 2) (Fin 2) ℚ :=
  let zi := labels.ζ i
  let zk := labels.ζ k
  let zj := labels.ζ j
  let zl := labels.ζ l
  let den := zi - zk
  ![![ (zi - zl) / den, (zi - zj) / den ],
    ![ (zl - zk) / den, (zj - zk) / den ]]

/-- 1. Inverse Flip Identity: applying a flip and its inverse gives the identity block -/
def flipInverseStatement (i k j l : ι) (hik : i ≠ k) (hjl : j ≠ l) : Prop :=
  flipBlock labels i k j l hik * flipBlock labels j l i k hjl = 1

/-- Abstract representation of a disjoint flip context for far-commutativity -/
structure DisjointFlipContext (ι : Type*) where
  F_pts : Finset ι
  G_pts : Finset ι
  disjoint : Disjoint F_pts G_pts

/-- 2. Far-Commutativity Identity -/
structure FarCommutativityStatement (ctx : DisjointFlipContext ι) where
  left : Matrix (Fin 2) (Fin 2) ℚ
  right : Matrix (Fin 2) (Fin 2) ℚ
  commutes : left * right = right * left

/-- 3. Pentagon Identity -/
def pentagonStatement (_i _j _k _l _m : ι)
    (A₁ A₂ A₃ A₄ A₅ : Matrix (Fin 3) (Fin 3) ℚ) : Prop :=
  A₁ * A₂ * A₃ * A₄ * A₅ = 1

end InfoGeometry.Topology.Delaunay
