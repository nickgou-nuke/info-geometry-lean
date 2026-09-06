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

/-! ## Cleared Jordan triple and Jacobiator readbacks -/

/-- Cleared Jordan triple `2·{X,Y,Z}` over the concrete integer Zorn lane.

The pasted abstract formula uses a factor `1/2`; this owner file works over
`ℤ`, so the theorem-honest readback is the doubled expression
`(XY)Z + (ZY)X`. -/
def doubleJordanTriple (X Y Z : SplitOct) : SplitOct :=
  addZ (mulZ (mulZ X Y) Z) (mulZ (mulZ Z Y) X)

/-- Jacobiator of the concrete Zorn commutator.  This measures the obstruction
to promoting the raw split-octonion commutator to a Lie bracket on the full
eight-coordinate carrier. -/
def jacobiatorZ (X Y Z : SplitOct) : SplitOct :=
  addZ (addZ (commZ X (commZ Y Z)) (commZ Y (commZ Z X))) (commZ Z (commZ X Y))

/-- Axiom-clean concrete readback for the cleared Jordan triple
`(up₀ down₀) up₀ + (up₀ down₀) up₀ = 2·up₀`. -/
theorem doubleJordan_up0_down0_up0_eq :
    doubleJordanTriple up0 down0 up0 = ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ := by
  rfl

/-- Axiom-clean concrete readback for the cleared Jordan triple
`(up₀ down₀) up₁ + (up₁ down₀) up₀ = up₁`. -/
theorem doubleJordan_up0_down0_up1_eq :
    doubleJordanTriple up0 down0 up1 = ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ := by
  rfl

/-- Axiom-clean concrete readback for the cleared Jordan triple
`(up₁ down₁) up₂ + (up₂ down₁) up₁ = up₂`. -/
theorem doubleJordan_up1_down1_up2_eq :
    doubleJordanTriple up1 down1 up2 = ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ := by
  rfl

/-- Concrete upper-sector closure readback for one cleared Jordan triple. -/
theorem doubleJordan_up0_down0_up0_closure :
    (doubleJordanTriple up0 down0 up0).a = 0 ∧
      (doubleJordanTriple up0 down0 up0).b = 0 ∧
      (doubleJordanTriple up0 down0 up0).y0 = 0 ∧
      (doubleJordanTriple up0 down0 up0).y1 = 0 ∧
      (doubleJordanTriple up0 down0 up0).y2 = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete Jacobiator readback for the raw Zorn commutator:
`J(up₀, up₁, down₀) = 6·up₁`. -/
theorem jacobiator_up0_up1_down0 :
    jacobiatorZ up0 up1 down0 = ⟨0, 0, 0, 6, 0, 0, 0, 0⟩ := by
  rfl

/-- The concrete Jacobiator is nonzero, so the raw split-octonion commutator on
the full owner carrier is not a Lie bracket. -/
theorem jacobiator_up0_up1_down0_ne_zero :
    jacobiatorZ up0 up1 down0 ≠ zeroZ := by
  decide

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

theorem mulZ_oneZ (X : SplitOct) :
    mulZ X oneZ = X := by
  cases X
  simp [mulZ, oneZ, addZ, ePlus, eMinus]

theorem oneZ_mulZ (X : SplitOct) :
    mulZ oneZ X = X := by
  cases X
  simp [mulZ, oneZ, addZ, ePlus, eMinus]

theorem commZ_oneZ (X : SplitOct) :
    commZ X oneZ = zeroZ := by
  unfold commZ
  rw [mulZ_oneZ, oneZ_mulZ]
  cases X
  simp [subZ, zeroZ]

theorem antiCommZ_oneZ (X : SplitOct) :
    antiCommZ X oneZ = addZ X X := by
  unfold antiCommZ
  rw [mulZ_oneZ, oneZ_mulZ]

theorem oneZ_commZ (X : SplitOct) :
    commZ oneZ X = zeroZ := by
  unfold commZ
  rw [oneZ_mulZ, mulZ_oneZ]
  cases X
  simp [subZ, zeroZ]

theorem oneZ_antiCommZ (X : SplitOct) :
    antiCommZ oneZ X = addZ X X := by
  unfold antiCommZ
  rw [oneZ_mulZ, mulZ_oneZ]

theorem commZ_self (X : SplitOct) :
    commZ X X = zeroZ := by
  unfold commZ
  cases X
  simp [subZ, zeroZ]

theorem subZ_swap (X Y : SplitOct) :
    subZ X Y = negZ (subZ Y X) := by
  cases X <;> cases Y
  simp [subZ, negZ]

theorem addZ_swap (X Y : SplitOct) :
    addZ X Y = addZ Y X := by
  cases X <;> cases Y
  simp [addZ, add_comm]

theorem commZ_swap (X Y : SplitOct) :
    commZ Y X = negZ (commZ X Y) := by
  unfold commZ
  exact subZ_swap (mulZ Y X) (mulZ X Y)

theorem antiCommZ_swap (X Y : SplitOct) :
    antiCommZ Y X = antiCommZ X Y := by
  unfold antiCommZ
  exact addZ_swap (mulZ Y X) (mulZ X Y)

/-- Canonical symplectic/hyperbolic commutator on each paired Zorn slot. -/
theorem up_down_comm_eq_H (i : Fin 3) : commZ (up i) (down i) = H := by
  fin_cases i <;> rfl

/-- Finite TKK-style anomaly-cancellation readback: the same-slot upper/lower
commutator has no off-diagonal Zorn coordinates.  This is the valid concrete
projection of the proposed `e⁺/e⁻` cancellation statement; it does not assert a
global five-graded Lie algebra or `P_n(5,5)` classification. -/
theorem up_down_comm_offDiagonal_zero (i : Fin 3) :
    (commZ (up i) (down i)).x0 = 0 ∧
      (commZ (up i) (down i)).x1 = 0 ∧
      (commZ (up i) (down i)).x2 = 0 ∧
      (commZ (up i) (down i)).y0 = 0 ∧
      (commZ (up i) (down i)).y1 = 0 ∧
      (commZ (up i) (down i)).y2 = 0 := by
  rw [up_down_comm_eq_H]
  simp [H, subZ, ePlus, eMinus]

/-- The same finite upper/lower commutator has zero trace. -/
theorem up_down_comm_trace_zero (i : Fin 3) : trZ (commZ (up i) (down i)) = 0 := by
  rw [up_down_comm_eq_H]
  rfl

/-- Canonical paired anticommutator on each paired Zorn slot. -/
theorem up_down_anticomm_eq_oneZ (i : Fin 3) : antiCommZ (up i) (down i) = oneZ := by
  fin_cases i <;> rfl

/-- The upper slots are determinant-null. -/
theorem detZ_up_null (i : Fin 3) : detZ (up i) = 0 := by
  fin_cases i <;> rfl

/-- The lower slots are determinant-null. -/
theorem detZ_down_null (i : Fin 3) : detZ (down i) = 0 := by
  fin_cases i <;> rfl

/-! ## Concrete square-to-`-oneZ` element on the split-octonion carrier -/

/--
A concrete element defined by subtracting the first lower basis vector from the
first upper basis vector.

Concretely, `J` is the coordinate vector with `x0 = 1`, `y0 = -1`, and all
other coordinates zero.  The theorems below record its square and determinant.
-/
def J : SplitOct := subZ up0 down0

@[simp] theorem J_eq : J = ⟨0, 0, 1, 0, 0, -1, 0, 0⟩ := rfl

/--
Direct coordinate readback: multiplying `J` by itself gives `negZ oneZ`.
-/
theorem J_sq_neg_oneZ : mulZ J J = negZ oneZ := by
  rfl

/--
Direct coordinate readback: the determinant of `J` is `1`.
-/
theorem detZ_J : detZ J = 1 := by
  rfl

end InfoGeometry.OperatorAlgebra.SplitOctonions.SymplecticFoundation
