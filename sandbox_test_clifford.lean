import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

universe u v
variable (R : Type u) [CommRing R] [Invertible (2 : R)]
variable (V : Type v) [AddCommGroup V] [Module R V]

def canonicalSplitForm : QuadraticForm R (V × Module.Dual R V) where
  toFun x := x.2 x.1
  toFun_smul a x := by
    dsimp
    rw [LinearMap.smul_apply, LinearMap.map_smul]
    ring

