import InfoGeometry.Exceptional.FreudenthalSymplecticTKKSocket

/-!
# Total 3-Graded TKK Bracket Candidate on the Symplectic Freudenthal Carrier

This file lifts the componentwise bilinear closure datum `symplecticTKKClosureDatum`
to an explicit total bracket on the 3-graded carrier:

$$\mathfrak{g} = \mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1}$$

where $\mathfrak{g}_{\pm 1} = \text{FreudenthalCharge } J$ and $\mathfrak{g}_0 = \text{SymplecticTKKZero } D$.

## Key Constructions:

1. **Total Carrier (`TKKTotalCarrier`)**:
   Direct sum representation as a product structure `FreudenthalCharge J × SymplecticTKKZero D × FreudenthalCharge J`.

2. **Graded Total Bracket (`tkkTotalBracket`)**:
   - Grade $-1$: $x_0 \cdot y_{-1} - y_0 \cdot x_{-1}$
   - Grade $0$: $[x_0, y_0] + [x_{-1}, y_{+1}] - [y_{-1}, x_{+1}]$
   - Grade $+1$: $x_0 \cdot y_{+1} - y_0 \cdot x_{+1}$

3. **Bracket Structural Laws**:
   - Skew-symmetry: $\llbracket u, v \rrbracket = - \llbracket v, u \rrbracket$.
   - Homogeneous bracket theorems for all gradings.

The file does not claim the Jacobi identity: the required mixed-triple
identity is recorded separately as an explicit obstruction.
All proofs in this file are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open Matrix

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-! ## 1. Zero Vanishing Lemmas for Mixed Bracket -/

@[simp] theorem mixedSymplecticBracket_zero_left (y : FreudenthalCharge J) :
    mixedSymplecticBracket D 0 y = 0 := by
  rw [← mixedSymplecticLinear_apply, map_zero, LinearMap.zero_apply]

@[simp] theorem mixedSymplecticBracket_zero_right (x : FreudenthalCharge J) :
    mixedSymplecticBracket D x 0 = 0 := by
  rw [← mixedSymplecticLinear_apply]
  exact (mixedSymplecticLinearLeft D x).map_zero

/-! ## 2. Total Carrier Structure -/

/-- Total 3-graded TKK carrier $\mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1}$. -/
structure TKKTotalCarrier where
  minus1 : FreudenthalCharge J
  zero : SymplecticTKKZero D
  plus1 : FreudenthalCharge J

namespace TKKTotalCarrier

instance : Add (TKKTotalCarrier D) where
  add u v := ⟨u.minus1 + v.minus1, u.zero + v.zero, u.plus1 + v.plus1⟩

instance : Neg (TKKTotalCarrier D) where
  neg u := ⟨-u.minus1, -u.zero, -u.plus1⟩

instance : Sub (TKKTotalCarrier D) where
  sub u v := ⟨u.minus1 - v.minus1, u.zero - v.zero, u.plus1 - v.plus1⟩

instance : Zero (TKKTotalCarrier D) where
  zero := ⟨0, 0, 0⟩

instance : SMul ℝ (TKKTotalCarrier D) where
  smul r u := ⟨r • u.minus1, r • u.zero, r • u.plus1⟩

@[simp] theorem neg_minus1 (u : TKKTotalCarrier D) : (-u).minus1 = -u.minus1 := rfl
@[simp] theorem neg_zero (u : TKKTotalCarrier D) : (-u).zero = -u.zero := rfl
@[simp] theorem neg_plus1 (u : TKKTotalCarrier D) : (-u).plus1 = -u.plus1 := rfl

@[simp] theorem zero_minus1 : (0 : TKKTotalCarrier D).minus1 = 0 := rfl
@[simp] theorem zero_zero : (0 : TKKTotalCarrier D).zero = 0 := rfl
@[simp] theorem zero_plus1 : (0 : TKKTotalCarrier D).plus1 = 0 := rfl

@[ext]
theorem ext (u v : TKKTotalCarrier D)
    (h_m : u.minus1 = v.minus1)
    (h_0 : u.zero = v.zero)
    (h_p : u.plus1 = v.plus1) : u = v := by
  cases u; cases v; congr

end TKKTotalCarrier

/-! ## 3. The Total Graded Bracket Candidate -/

/-- The total 3-graded TKK Lie bracket on $\mathfrak{g}_{-1} \oplus \mathfrak{g}_0 \oplus \mathfrak{g}_{+1}$. -/
def tkkTotalBracket (u v : TKKTotalCarrier D) : TKKTotalCarrier D where
  minus1 := (u.zero : Module.End ℝ (FreudenthalCharge J)) v.minus1 -
            (v.zero : Module.End ℝ (FreudenthalCharge J)) u.minus1
  zero := ⁅u.zero, v.zero⁆ +
          mixedSymplecticBracket D u.minus1 v.plus1 -
          mixedSymplecticBracket D v.minus1 u.plus1
  plus1 := (u.zero : Module.End ℝ (FreudenthalCharge J)) v.plus1 -
           (v.zero : Module.End ℝ (FreudenthalCharge J)) u.plus1

/-- 🏆 THEOREM: The total TKK bracket is strictly skew-symmetric. -/
theorem tkkTotalBracket_skew (u v : TKKTotalCarrier D) :
    tkkTotalBracket D u v = - tkkTotalBracket D v u := by
  apply TKKTotalCarrier.ext
  · simp only [tkkTotalBracket, TKKTotalCarrier.neg_minus1, neg_sub]
  · simp only [tkkTotalBracket, TKKTotalCarrier.neg_zero]
    have hskew : ⁅u.zero, v.zero⁆ = - ⁅v.zero, u.zero⁆ := (lie_skew u.zero v.zero).symm
    rw [hskew]
    abel
  · simp only [tkkTotalBracket, TKKTotalCarrier.neg_plus1, neg_sub]

@[simp]
theorem tkkTotalBracket_self (u : TKKTotalCarrier D) :
    tkkTotalBracket D u u = 0 := by
  apply TKKTotalCarrier.ext
  · simp [tkkTotalBracket]
  · simp [tkkTotalBracket, lie_self]
  · simp [tkkTotalBracket]

/-! ## 4. Component Injections and Homogeneous Brackets -/

/-- Grade $-1$ canonical injection. -/
def injMinus1 (x : FreudenthalCharge J) : TKKTotalCarrier D := ⟨x, 0, 0⟩

/-- Grade $0$ canonical injection. -/
def injZero (T : SymplecticTKKZero D) : TKKTotalCarrier D := ⟨0, T, 0⟩

/-- Grade $+1$ canonical injection. -/
def injPlus1 (y : FreudenthalCharge J) : TKKTotalCarrier D := ⟨0, 0, y⟩

@[simp] theorem tkk_bracket_minus1_minus1 (x y : FreudenthalCharge J) :
    tkkTotalBracket D (injMinus1 D x) (injMinus1 D y) = 0 := by
  apply TKKTotalCarrier.ext <;> dsimp [tkkTotalBracket, injMinus1] <;> simp

@[simp] theorem tkk_bracket_plus1_plus1 (x y : FreudenthalCharge J) :
    tkkTotalBracket D (injPlus1 D x) (injPlus1 D y) = 0 := by
  apply TKKTotalCarrier.ext <;> dsimp [tkkTotalBracket, injPlus1] <;> simp

@[simp] theorem tkk_bracket_zero_zero (T U : SymplecticTKKZero D) :
    tkkTotalBracket D (injZero D T) (injZero D U) = injZero D ⁅T, U⁆ := by
  apply TKKTotalCarrier.ext <;> dsimp [tkkTotalBracket, injZero] <;> simp

@[simp] theorem tkk_bracket_zero_minus1 (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    tkkTotalBracket D (injZero D T) (injMinus1 D x) = injMinus1 D (T.1 x) := by
  apply TKKTotalCarrier.ext <;> dsimp [tkkTotalBracket, injZero, injMinus1] <;> simp

@[simp] theorem tkk_bracket_zero_plus1 (T : SymplecticTKKZero D) (y : FreudenthalCharge J) :
    tkkTotalBracket D (injZero D T) (injPlus1 D y) = injPlus1 D (T.1 y) := by
  apply TKKTotalCarrier.ext <;> dsimp [tkkTotalBracket, injZero, injPlus1] <;> simp

@[simp] theorem tkk_bracket_minus1_plus1 (x y : FreudenthalCharge J) :
    tkkTotalBracket D (injMinus1 D x) (injPlus1 D y) = injZero D (mixedSymplecticBracket D x y) := by
  apply TKKTotalCarrier.ext <;> dsimp [tkkTotalBracket, injMinus1, injPlus1, injZero] <;> simp

end InfoGeometry.Exceptional.Freudenthal
