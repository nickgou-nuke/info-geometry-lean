import InfoGeometry.Algebra.SuperLieRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ConformalSpinorBridge

/-!
# SuperLieRing instance for the conformal spinor bridge

This module equips the canonical finite `𝔬𝔰𝔭(1|2)` coordinate bridge from
`InfoGeometry.Clifford.ConformalSpinorBridge` with the `SuperLieRing` class.

The carrier, basis table, and bracket are imported from the owner file.  The
instance data below supplies explicit coordinate even/odd submodules and proves
the class laws directly by coordinate expansion.
-/

open InfoGeometry.Algebra

noncomputable section

namespace InfoGeometry.Clifford.ConformalSpinorBridge
namespace OSp12

instance : SuperBracket OSp12 where
  bracket := bracket
  add_lie := add_lie
  lie_add := lie_add
  lie_smul := lie_smul

/-- Coordinate even part: the odd coordinates vanish. -/
def evenCoordinatePart : Submodule ℝ OSp12 where
  carrier := {x | x B.G1 = 0 ∧ x B.G2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor <;> simp [Pi.add_apply, hx.1, hx.2, hy.1, hy.2]
  smul_mem' := by
    intro r x hx
    constructor <;> simp [Pi.smul_apply, hx.1, hx.2]

/-- Coordinate odd part: the even coordinates vanish. -/
def oddCoordinatePart : Submodule ℝ OSp12 where
  carrier := {x | x B.H = 0 ∧ x B.Ep = 0 ∧ x B.Em = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    constructor
    · simp [Pi.add_apply, hx.1, hy.1]
    constructor
    · simp [Pi.add_apply, hx.2.1, hy.2.1]
    · simp [Pi.add_apply, hx.2.2, hy.2.2]
  smul_mem' := by
    intro r x hx
    constructor
    · simp [Pi.smul_apply, hx.1]
    constructor
    · simp [Pi.smul_apply, hx.2.1]
    · simp [Pi.smul_apply, hx.2.2]

theorem sup_even_odd_coord :
    evenCoordinatePart ⊔ oddCoordinatePart = (⊤ : Submodule ℝ OSp12) := by
  apply top_unique
  intro x hx
  let e : OSp12 :=
    fun k =>
      match k with
      | B.H => x B.H
      | B.Ep => x B.Ep
      | B.Em => x B.Em
      | B.G1 => 0
      | B.G2 => 0
  let o : OSp12 :=
    fun k =>
      match k with
      | B.H => 0
      | B.Ep => 0
      | B.Em => 0
      | B.G1 => x B.G1
      | B.G2 => x B.G2
  exact Submodule.mem_sup.mpr
    ⟨e, by
        change e B.G1 = 0 ∧ e B.G2 = 0
        simp [e],
      o, by
        change o B.H = 0 ∧ o B.Ep = 0 ∧ o B.Em = 0
        simp [o],
      by
        ext k <;> fin_cases k <;> simp [e, o, Pi.add_apply]⟩

theorem inter_even_odd_coord :
    evenCoordinatePart ⊓ oddCoordinatePart = (⊥ : Submodule ℝ OSp12) := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    ext k <;> fin_cases k
    · exact hx.2.1
    · exact hx.2.2.1
    · exact hx.2.2.2
    · exact hx.1.1
    · exact hx.1.2
  · exact bot_le

theorem even_even_skew_coord (x y : OSp12)
    (hx : x ∈ evenCoordinatePart) (hy : y ∈ evenCoordinatePart) :
    bracket x y = -bracket y x := by
  ext k <;> fin_cases k <;> simp [bracket, hx.1, hx.2, hy.1, hy.2] <;> ring

theorem even_odd_skew_coord (x y : OSp12)
    (hx : x ∈ evenCoordinatePart) (hy : y ∈ oddCoordinatePart) :
    bracket x y = -bracket y x := by
  ext k <;> fin_cases k <;>
    simp [bracket, hx.1, hx.2, hy.1, hy.2.1, hy.2.2] <;> ring

theorem odd_odd_symm_coord (x y : OSp12)
    (hx : x ∈ oddCoordinatePart) (hy : y ∈ oddCoordinatePart) :
    bracket x y = bracket y x := by
  ext k <;> fin_cases k <;>
    simp [bracket, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2] <;> ring

theorem jacobi_even_coord (x y z : OSp12) (hx : x ∈ evenCoordinatePart) :
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z) := by
  ext k <;> fin_cases k <;> simp [bracket, hx.1, hx.2] <;> ring

theorem jacobi_odd_odd_coord (x y z : OSp12)
    (hx : x ∈ oddCoordinatePart) (hy : y ∈ oddCoordinatePart) :
    bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z) := by
  ext k <;> fin_cases k <;>
    simp [bracket, hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2] <;> ring

instance : SuperLieRing OSp12 where
  evenPart := evenCoordinatePart
  oddPart := oddCoordinatePart
  sup_even_odd := sup_even_odd_coord
  even_odd_inter := inter_even_odd_coord
  even_even_skew := even_even_skew_coord
  even_odd_skew := even_odd_skew_coord
  odd_odd_symm := odd_odd_symm_coord
  jacobi_even := jacobi_even_coord
  jacobi_odd_odd := jacobi_odd_odd_coord

end OSp12
end InfoGeometry.Clifford.ConformalSpinorBridge
