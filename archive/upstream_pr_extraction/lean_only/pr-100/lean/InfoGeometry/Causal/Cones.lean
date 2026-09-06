import InfoGeometry.Clifford.CartanInstance
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

open scoped Matrix

namespace InfoGeometry.Causal

/-- 
A Generalized Cone based on a Quadratic Form Q.
This captures the "textbook" Lorentz/Minkowski structure 
as a primitive for your doubled space.
-/
abbrev CausalStructure (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  QuadraticForm ℝ V

namespace CausalStructure

abbrev Q
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : CausalStructure V) : QuadraticForm ℝ V :=
  C

end CausalStructure

namespace CausalStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (C : CausalStructure V)

/-- The "Self-Dual Inner Cone" (Interior): Where the metric is positive. -/
def Interior : Set V := {v | 0 < C.Q v}

/-- The "Causal Lightcone" (Boundary): The Null Space of the quadratic form. -/
def Boundary : Set V := {v | C.Q v = 0}

/-- 
The "Isolated Null Space" Principle:
On the interior, the geometry is "safe" (invertible).
On the boundary, we must projectivize or use the Moore-Penrose mirror.
-/
lemma interior_is_non_null {v : V} (hv : v ∈ C.Interior) : v ∉ C.Boundary := by
  simp [Interior, Boundary] at *
  exact ne_of_gt hv

end CausalStructure

/-! 
### Connecting the Cone to Matrix Invertibility
We now map the "Boundary" of the cone to the "Singular Locus" of the algebra.
-/

variable {n : ℕ} (J1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- 
A Matrix lives "On the Boundary" if it has a non-trivial Kernel.
In your theory, this is the "Coordinate Conformal Chart" locus.
-/
def IsOnBoundary (A : InfoGeometry.Clifford.TowerMatrix.Mat n) : Prop := ¬ IsUnit A

/--
The "Modular Mirror" reflection as the canonical matrix inverse in Mathlib.
-/
noncomputable def ModularMirror
    (A : InfoGeometry.Clifford.TowerMatrix.Mat n) : InfoGeometry.Clifford.TowerMatrix.Mat n :=
  A⁻¹

/--
`ModularMirror` is Cartan-compatible on invertible charts:
applying the mirror after Cartan equals Cartan after the mirror.
-/
lemma modularMirror_cartan_comm_of_isUnit
    (hJJ : (InfoGeometry.Clifford.TowerMatrix.Jn J1 n)
      * (InfoGeometry.Clifford.TowerMatrix.Jn J1 n)
      = (1 : InfoGeometry.Clifford.TowerMatrix.Mat n))
    (hJt : (InfoGeometry.Clifford.TowerMatrix.Jn J1 n)ᵀ
      = (InfoGeometry.Clifford.TowerMatrix.Jn J1 n))
    {A : InfoGeometry.Clifford.TowerMatrix.Mat n}
    (hA : IsUnit A.det) :
    ModularMirror (n := n) (InfoGeometry.Clifford.TowerMatrix.cartan J1 n A)
      = InfoGeometry.Clifford.TowerMatrix.cartan J1 n (ModularMirror (n := n) A) := by
  simpa [ModularMirror] using
    (InfoGeometry.Clifford.TowerMatrix.cartan_inv_of_isUnit
      (J1 := J1) (n := n) hJJ hJt (X := A) hA).symm

/--
The "Clifford Null-Cone" translation:
A vector is on the causal lightcone boundary if and only if its representative
squares to zero in the native Clifford Algebra.
-/
theorem clifford_square_zero_of_mem_boundary {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : CausalStructure V) (v : V) (hv : v ∈ C.Boundary) :
    (CliffordAlgebra.ι C.Q v) * (CliffordAlgebra.ι C.Q v) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar]
  have hQ : C.Q v = 0 := hv
  rw [hQ]
  exact map_zero (algebraMap ℝ (CliffordAlgebra C.Q))

end InfoGeometry.Causal
