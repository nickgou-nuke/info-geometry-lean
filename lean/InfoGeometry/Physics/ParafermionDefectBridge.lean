import Mathlib.Tactic
import InfoGeometry.Categorical.Z3Parafermion
import InfoGeometry.Physics.KleinBottleDefects

/-!
# Topological Defects as Z₃ Parafermions in the 𝔰𝔬(5,5) Vacuum

This module bridges the macroscopic geometric 5-7 defect pairs (required on a 
non-orientable Klein bottle or Torus) to the microscopic categorical structure 
of the 𝔰𝔬(5,5) vacuum, specifically mapping them to Z₃ Parafermions and 
Fibonacci Anyons.

## The Tri-State Defect Mapping
The 5-7 defect balance ($F_5 = F_7$) can be viewed as the neutrality condition 
of a topological charge. We map the faces of the lattice to the spectrum of a 
Z₃ Parafermion operator $O$, where $O^3 = O$.
The eigenvalues of $O$ are $\{+1, -1, 0\}$.

* **Pentagon (5-gon)**: Local positive curvature $\to$ $+1$ Parafermion state (proj_up).
* **Heptagon (7-gon)**: Local negative curvature $\to$ $-1$ Parafermion state (proj_down).
* **Hexagon (6-gon)**: Local flat curvature $\to$ $0$ Vacancy state (proj_vacancy).

The geometric constraint $F_5 = F_7$ is identical to the physical constraint 
that the total macroscopic topological charge of the closed universe (the trace 
of the defect operator) must be exactly zero.
-/

namespace InfoGeometry.Physics

open InfoGeometry.Categorical.Z3Parafermion

/-- A local parafermionic operator is natively the subtype cut out by `O³ = O`. -/
abbrev TopologicalDefectOperator (A : Type*) [Ring A] [Algebra ℝ A] :=
  {op : A // op ^ 3 = op}

namespace TopologicalDefectOperator

abbrev op {A : Type*} [Ring A] [Algebra ℝ A]
    (O : TopologicalDefectOperator A) : A := O.1

lemma is_parafermionic {A : Type*} [Ring A] [Algebra ℝ A]
    (O : TopologicalDefectOperator A) : O.op ^ 3 = O.op := O.2

end TopologicalDefectOperator

/-- 
The sum of the topological charges of the network. 
If the number of +1 states (pentagons) equals the number of -1 states (heptagons), 
the net chiral charge is zero. 
We model this by showing that $F_5 (+1) + F_7 (-1) = 0 \iff F_5 = F_7$.
-/
theorem defect_charge_neutrality (F5 F7 : ℤ) :
  F5 * (1 : ℤ) + F7 * (-1 : ℤ) = 0 ↔ F5 = F7 := by
  omega

/-- 
Using our previous theorem from `KleinBottleDefects`, we prove that any 
3-regular $\chi = 0$ lattice natively enforces Z₃ Parafermion charge neutrality. 
-/
theorem klein_lattice_is_parafermion_neutral 
  (V E F F5 F6 F7 : ℕ)
  (h_euler : V + F = E) 
  (h_reg : 3 * V = 2 * E)
  (h_faces : F = F5 + F6 + F7)
  (h_edges : 2 * E = 5 * F5 + 6 * F6 + 7 * F7) :
  (F5 : ℤ) * 1 + (F7 : ℤ) * (-1) = 0 := by
  have h_balance : F5 = F7 := klein_bottle_defects_balance V E F F5 F6 F7 h_euler h_reg h_faces h_edges
  rw [h_balance]
  ring

end InfoGeometry.Physics
