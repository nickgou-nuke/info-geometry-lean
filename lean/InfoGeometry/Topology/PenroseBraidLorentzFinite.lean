import Mathlib.Tactic

/-!
# Finite Penrose--Braid--Clifford packet

This file mirrors the multi-system verifier
`tools/sympy/penrose_braid_lorentz_finite_packet.py`.

It proves only finite algebraic shadows:
* a five-label pentagrid reflection is involutive;
* the adjacent-transposition quotient of the `B₃` braid relation;
* a diagonal Hecke characteristic equation over `ℤ`;
* a concrete split `Cl(1,1)` matrix atom over `ℤ`.

It does **not** assert Penrose tiling classification, quotient-space Klein-bottle
topology, Jones/Kauffman invariants, Lorentz/Spin/Pin/biquaternion representation
theorems, particle physics, spacetime emergence, or infinite braid colimits.
-/

namespace InfoGeometry.Topology.PenroseBraidLorentzFinite

/-- Five pentagrid directions as labels. -/
abbrev FiveLabel := ZMod 5

/-- The finite reflection on pentagrid labels: `j ↦ -j`. -/
def pentagridReflect (j : FiveLabel) : FiveLabel := -j

@[simp]
theorem pentagridReflect_involutive (j : FiveLabel) :
    pentagridReflect (pentagridReflect j) = j := by
  simp [pentagridReflect]

@[simp]
theorem pentagridReflect_zero : pentagridReflect 0 = 0 := by
  simp [pentagridReflect]

/-- Adjacent transposition `(12)` acting on three labels. -/
def tau12 (i : Fin 3) : Fin 3 :=
  if i = 0 then 1 else if i = 1 then 0 else 2

/-- Adjacent transposition `(23)` acting on three labels. -/
def tau23 (i : Fin 3) : Fin 3 :=
  if i = 0 then 0 else if i = 1 then 2 else 1

@[simp]
theorem tau12_tau12 (i : Fin 3) : tau12 (tau12 i) = i := by
  fin_cases i <;> simp [tau12]

@[simp]
theorem tau23_tau23 (i : Fin 3) : tau23 (tau23 i) = i := by
  fin_cases i <;> simp [tau23]

/-- The Coxeter/Symmetric quotient of the Artin `B₃` relation. -/
theorem adjacent_transposition_braid_relation (i : Fin 3) :
    tau12 (tau23 (tau12 i)) = tau23 (tau12 (tau23 i)) := by
  fin_cases i <;> simp [tau12, tau23]

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- Diagonal Hecke representative with eigenvalues `q` and `-1`. -/
def heckeDiag (q : ℤ) : Mat2Z :=
  ![![q, 0], ![0, -1]]

/-- Explicit first factor `H - qI` for the diagonal Hecke representative. -/
def heckeDiagMinus (q : ℤ) : Mat2Z :=
  ![![0, 0], ![0, -1 - q]]

/-- Explicit second factor `H + I` for the diagonal Hecke representative. -/
def heckeDiagPlus (q : ℤ) : Mat2Z :=
  ![![q + 1, 0], ![0, 0]]

/-- Finite Hecke characteristic equation `(H-qI)(H+I)=0` for `diag(q,-1)`. -/
theorem heckeDiag_quadratic (q : ℤ) : heckeDiagMinus q * heckeDiagPlus q = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeDiagMinus, heckeDiagPlus, Matrix.mul_apply]

/-- Split `Cl(1,1)` positive generator, represented as a concrete integer matrix. -/
def cl11Plus : Mat2Z :=
  ![![1, 0], ![0, -1]]

/-- Split `Cl(1,1)` negative generator, represented as a concrete integer matrix. -/
def cl11Minus : Mat2Z :=
  ![![0, 1], ![-1, 0]]

@[simp]
theorem cl11Plus_sq : cl11Plus * cl11Plus = (1 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cl11Plus, Matrix.mul_apply]

@[simp]
theorem cl11Minus_sq : cl11Minus * cl11Minus = -(1 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cl11Minus, Matrix.mul_apply]

@[simp]
theorem cl11_anticomm : cl11Plus * cl11Minus + cl11Minus * cl11Plus = (0 : Mat2Z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cl11Plus, cl11Minus, Matrix.mul_apply]

end InfoGeometry.Topology.PenroseBraidLorentzFinite
