import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Split-octonion symplectic foundation slice

This module is the Lean twin of
`tools/sympy/split_octonion_symplectic_foundation.py`.

It formalizes the smallest Peirce-Witt / hyperbolic commutator packet already
available from the concrete Zorn multiplication layer:

* the diagonal unit `oneZ = ePlus + eMinus`;
* the hyperbolic grading element `H = ePlus - eMinus`;
* `H^2 = oneZ`;
* `[up_i, down_i] = H` and `{up_i, down_i} = oneZ` for each finite vector slot;
* determinant/null readouts for the same finite basis elements.

Honest scope: this is a finite Zorn-coordinate packet.  It does not prove a
Cuntz-algebra representation, wallpaper symmetry forcing theorem,
parafermionic braid coherence theorem, physical helicity classification, or the
global real Lie-group statement `Aut(𝕆_s)=G_{2(2)}`.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- Coordinatewise addition on the concrete Zorn carrier. -/
def addZ (X Y : SplitOct) : SplitOct :=
  ⟨X.a + Y.a, X.b + Y.b, X.x0 + Y.x0, X.x1 + Y.x1, X.x2 + Y.x2,
    X.y0 + Y.y0, X.y1 + Y.y1, X.y2 + Y.y2⟩

/-- Diagonal identity element `ePlus + eMinus`. -/
def oneZ : SplitOct := addZ ePlus eMinus

/-- Hyperbolic Peirce/chiral grading element `H = ePlus - eMinus`. -/
def H : SplitOct := subZ ePlus eMinus

/-- Zorn commutator `[X,Y] = XY - YX`. -/
def commZ (X Y : SplitOct) : SplitOct := subZ (mulZ X Y) (mulZ Y X)

/-- Zorn anticommutator `{X,Y} = XY + YX`. -/
def antiCommZ (X Y : SplitOct) : SplitOct := addZ (mulZ X Y) (mulZ Y X)

@[simp] theorem oneZ_eq : oneZ = ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ := rfl

@[simp] theorem H_eq : H = ⟨1, -1, 0, 0, 0, 0, 0, 0⟩ := rfl

/-- The Peirce idempotents recover the diagonal unit. -/
theorem ePlus_add_eMinus_eq_oneZ : addZ ePlus eMinus = oneZ := rfl

/-- The hyperbolic grading element squares to the diagonal unit. -/
theorem H_sq : mulZ H H = oneZ := rfl

/-- The determinant of the hyperbolic grading element is `-1`. -/
theorem detZ_H : detZ H = -1 := rfl

/-- The determinant of the diagonal unit is `1`. -/
theorem detZ_oneZ : detZ oneZ = 1 := rfl

/-- Canonical symplectic/hyperbolic commutator on each paired Zorn slot. -/
theorem up_down_comm_eq_H (i : Fin 3) : commZ (up i) (down i) = H := by
  fin_cases i <;> rfl

/-- Canonical paired anticommutator on each paired Zorn slot. -/
theorem up_down_anticomm_eq_oneZ (i : Fin 3) : antiCommZ (up i) (down i) = oneZ := by
  fin_cases i <;> rfl

/-- The upper slots are determinant-null. -/
theorem detZ_up_null (i : Fin 3) : detZ (up i) = 0 := by
  fin_cases i <;> rfl

/-- The lower slots are determinant-null. -/
theorem detZ_down_null (i : Fin 3) : detZ (down i) = 0 := by
  fin_cases i <;> rfl

/-- Foundation packet collecting the exact finite Peirce-Witt commutator facts. -/
theorem splitOctonion_symplectic_foundation_packet :
    mulZ H H = oneZ ∧
      detZ H = -1 ∧
      detZ oneZ = 1 ∧
      (∀ i : Fin 3, commZ (up i) (down i) = H) ∧
      (∀ i : Fin 3, antiCommZ (up i) (down i) = oneZ) ∧
      (∀ i : Fin 3, detZ (up i) = 0) ∧
      (∀ i : Fin 3, detZ (down i) = 0) := by
  exact ⟨H_sq, detZ_H, detZ_oneZ, up_down_comm_eq_H,
    up_down_anticomm_eq_oneZ, detZ_up_null, detZ_down_null⟩

end InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation
