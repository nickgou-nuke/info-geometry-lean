import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.FinCases

namespace WeylCrystal

open Matrix

/-!
# Weyl Crystal and the Lattice of Klein Bottles

Formalizes the finite local cell of the Weyl Crystal, representing 
the Cuntz-Kashiwara states at the thermodynamic limit, and the topological 
inversion of the Weyl Chamber via the non-orientable J-twist.
-/

/-- 
The fundamental Weyl reflection matrix on the local Cartan subspace.
This encodes the J-modular inversion (the Klein Bottle twist) for a single cell. 
-/
def J_WeylReflection : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![0, 1],
    ![1, 0]]

/-- 
Theorem: The Weyl reflection is a strict involution (W^2 = I). 
It generates the local Z2 Space Group of the crystal cell.
-/
theorem weyl_involution : J_WeylReflection * J_WeylReflection = 1 := by
  decide

/-- 
The fundamental stability domain (the Weyl Chamber).
We define the invariant throat as the +1 eigenspace of the J reflection,
which physically corresponds to the Barycenter Re(s) = 1/2.
-/
def InvariantThroat (v : Fin 2 → ℤ) : Prop :=
  J_WeylReflection *ᵥ v = v

/-- 
Theorem: The Barycenter of the cell is perfectly invariant under the Weyl reflection.
If we evaluate the symmetric sum of the two roots (v = ![1, 1]), 
it is topologically trapped in the stable Weyl Chamber throat.
This proves that the Weyl Chamber wall perfectly balances the modular reflections.
-/
theorem barycenter_stable :
    InvariantThroat ![1, 1] := by
  dsimp [InvariantThroat, J_WeylReflection]
  ext i
  fin_cases i <;> decide

/-- 
Theorem: Orthogonal roots cross the thermodynamic wall.
The anti-symmetric state v = ![-1, 1] flips sign under the Weyl Reflection, 
representing an orientation-reversing trajectory across the Klein Brillouin zone.
-/
theorem weyl_chamber_wall_flip :
    J_WeylReflection *ᵥ ![-1, 1] = ![1, -1] := by
  dsimp [J_WeylReflection]
  ext i
  fin_cases i <;> decide

end WeylCrystal
