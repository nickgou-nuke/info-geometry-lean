import Mathlib.Tactic

/-!
# True split-octonion multiplication layer

This module is the Lean twin of `tools/sympy/split_octonion_multiplication.py`.
It defines an explicit eight-coordinate Zorn split-octonion carrier over `ℤ`
and a concrete nonassociative multiplication table:

```text
(a,x;y,b)(c,u;v,d) =
  (a c + x·v,
   a u + d x - y×v;
   b v + c y + x×u,
   b d + y·u)
```

Theorems below lock the basis table, idempotent diagonal units, nilpotent
upper/lower units, a concrete nonzero associator property, and basis
alternativity checks.  This is a multiplication layer only: it does not assert a
`G₂(2)` automorphism theorem, an `SU(3)` stabilizer theorem, or a particle
classification theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- Eight-coordinate Zorn split-octonion cell over `ℤ`. -/
@[ext]
structure SplitOct where
  a : ℤ
  b : ℤ
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  y0 : ℤ
  y1 : ℤ
  y2 : ℤ
  deriving DecidableEq, Repr

/-- Coordinatewise zero. -/
def zeroZ : SplitOct := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Coordinatewise negation. -/
def negZ (X : SplitOct) : SplitOct :=
  ⟨-X.a, -X.b, -X.x0, -X.x1, -X.x2, -X.y0, -X.y1, -X.y2⟩

/-- Coordinatewise subtraction. -/
def subZ (X Y : SplitOct) : SplitOct :=
  ⟨X.a - Y.a, X.b - Y.b, X.x0 - Y.x0, X.x1 - Y.x1, X.x2 - Y.x2,
    X.y0 - Y.y0, X.y1 - Y.y1, X.y2 - Y.y2⟩

/-- Zorn determinant / split norm. -/
def detZ (X : SplitOct) : ℤ :=
  X.a * X.b - (X.x0 * X.y0 + X.x1 * X.y1 + X.x2 * X.y2)

/-- Coordinate diagonalisation of the native integral split norm.

This proves the `(4,4)` signature identity in coordinates.  It does not
assert an `E₈` lattice identification or a maximal-order theorem.
-/
theorem detZ_split_signature (X : SplitOct) :
    4 * detZ X =
      (X.a + X.b) ^ 2 - (X.a - X.b) ^ 2
        - (X.x0 + X.y0) ^ 2 + (X.x0 - X.y0) ^ 2
        - (X.x1 + X.y1) ^ 2 + (X.x1 - X.y1) ^ 2
        - (X.x2 + X.y2) ^ 2 + (X.x2 - X.y2) ^ 2 := by
  simp [detZ]
  ring

/-- Coordinate expansion of the Zorn determinant. -/
theorem detZ_coordinate_formula (X : SplitOct) :
    detZ X = X.a * X.b -
      (X.x0 * X.y0 + X.x1 * X.y1 + X.x2 * X.y2) := rfl

/-- True Zorn split-octonion multiplication. -/
def mulZ (X Y : SplitOct) : SplitOct :=
  ⟨ X.a * Y.a + (X.x0 * Y.y0 + X.x1 * Y.y1 + X.x2 * Y.y2),
    X.b * Y.b + (X.y0 * Y.x0 + X.y1 * Y.x1 + X.y2 * Y.x2),
    X.a * Y.x0 + Y.b * X.x0 - (X.y1 * Y.y2 - X.y2 * Y.y1),
    X.a * Y.x1 + Y.b * X.x1 - (X.y2 * Y.y0 - X.y0 * Y.y2),
    X.a * Y.x2 + Y.b * X.x2 - (X.y0 * Y.y1 - X.y1 * Y.y0),
    X.b * Y.y0 + Y.a * X.y0 + (X.x1 * Y.x2 - X.x2 * Y.x1),
    X.b * Y.y1 + Y.a * X.y1 + (X.x2 * Y.x0 - X.x0 * Y.x2),
    X.b * Y.y2 + Y.a * X.y2 + (X.x0 * Y.x1 - X.x1 * Y.x0) ⟩

/-- Determinant multiplicativity for the concrete split-octonion product. -/
theorem detZ_mul (X Y : SplitOct) : detZ (mulZ X Y) = detZ X * detZ Y := by
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases Y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      simp [detZ, mulZ]
      ring_nf

/-- Norm notation on this owner file agrees with the Zorn determinant. -/
def normZ (X : SplitOct) : ℤ := detZ X

/-- Norm multiplicativity for the concrete split-octonion product. -/
theorem normZ_mul (X Y : SplitOct) : normZ (mulZ X Y) = normZ X * normZ Y := by
  simpa [normZ] using detZ_mul X Y

instance : Add SplitOct where
  add X Y :=
    ⟨X.a + Y.a, X.b + Y.b, X.x0 + Y.x0, X.x1 + Y.x1, X.x2 + Y.x2,
      X.y0 + Y.y0, X.y1 + Y.y1, X.y2 + Y.y2⟩

instance : Zero SplitOct := ⟨zeroZ⟩
instance : Neg SplitOct := ⟨negZ⟩
instance : Sub SplitOct := ⟨subZ⟩

@[simp] theorem zero_a : (0 : SplitOct).a = 0 := rfl
@[simp] theorem zero_b : (0 : SplitOct).b = 0 := rfl
@[simp] theorem zero_x0 : (0 : SplitOct).x0 = 0 := rfl
@[simp] theorem zero_x1 : (0 : SplitOct).x1 = 0 := rfl
@[simp] theorem zero_x2 : (0 : SplitOct).x2 = 0 := rfl
@[simp] theorem zero_y0 : (0 : SplitOct).y0 = 0 := rfl
@[simp] theorem zero_y1 : (0 : SplitOct).y1 = 0 := rfl
@[simp] theorem zero_y2 : (0 : SplitOct).y2 = 0 := rfl

@[simp] theorem neg_a (X : SplitOct) : (-X).a = -X.a := rfl
@[simp] theorem neg_b (X : SplitOct) : (-X).b = -X.b := rfl
@[simp] theorem neg_x0 (X : SplitOct) : (-X).x0 = -X.x0 := rfl
@[simp] theorem neg_x1 (X : SplitOct) : (-X).x1 = -X.x1 := rfl
@[simp] theorem neg_x2 (X : SplitOct) : (-X).x2 = -X.x2 := rfl
@[simp] theorem neg_y0 (X : SplitOct) : (-X).y0 = -X.y0 := rfl
@[simp] theorem neg_y1 (X : SplitOct) : (-X).y1 = -X.y1 := rfl
@[simp] theorem neg_y2 (X : SplitOct) : (-X).y2 = -X.y2 := rfl

@[simp] theorem add_a (X Y : SplitOct) : (X + Y).a = X.a + Y.a := rfl
@[simp] theorem add_b (X Y : SplitOct) : (X + Y).b = X.b + Y.b := rfl
@[simp] theorem add_x0 (X Y : SplitOct) : (X + Y).x0 = X.x0 + Y.x0 := rfl
@[simp] theorem add_x1 (X Y : SplitOct) : (X + Y).x1 = X.x1 + Y.x1 := rfl
@[simp] theorem add_x2 (X Y : SplitOct) : (X + Y).x2 = X.x2 + Y.x2 := rfl
@[simp] theorem add_y0 (X Y : SplitOct) : (X + Y).y0 = X.y0 + Y.y0 := rfl
@[simp] theorem add_y1 (X Y : SplitOct) : (X + Y).y1 = X.y1 + Y.y1 := rfl
@[simp] theorem add_y2 (X Y : SplitOct) : (X + Y).y2 = X.y2 + Y.y2 := rfl

instance : AddCommGroup SplitOct where
  add := (· + ·)
  add_assoc := by
    intro a b c
    ext <;>
      simp [add_a, add_b, add_x0, add_x1, add_x2, add_y0, add_y1, add_y2]
    <;> ring
  zero := 0
  zero_add := by
    intro a
    ext <;> simp [add_a, add_b, add_x0, add_x1, add_x2, add_y0, add_y1, add_y2]
  add_zero := by
    intro a
    ext <;> simp [add_a, add_b, add_x0, add_x1, add_x2, add_y0, add_y1, add_y2]
  neg := Neg.neg
  neg_add_cancel := by
    intro a
    ext <;> simp [add_a, add_b, add_x0, add_x1, add_x2, add_y0, add_y1, add_y2]
  add_comm := by
    intro a b
    ext <;>
      simp [add_a, add_b, add_x0, add_x1, add_x2, add_y0, add_y1, add_y2]
    <;> ring
  nsmul := nsmulRec
  nsmul_zero := by intro a; rfl
  nsmul_succ := by intro n a; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro a; rfl
  zsmul_succ' := by intro n a; rfl
  zsmul_neg' := by intro n a; rfl

/-- The associative backbone of the split-octonion product. -/
def assocMul (X Y : SplitOct) : SplitOct :=
  ⟨ X.a * Y.a + (X.x0 * Y.y0 + X.x1 * Y.y1 + X.x2 * Y.y2),
    X.b * Y.b + (X.y0 * Y.x0 + X.y1 * Y.x1 + X.y2 * Y.x2),
    X.a * Y.x0 + Y.b * X.x0,
    X.a * Y.x1 + Y.b * X.x1,
    X.a * Y.x2 + Y.b * X.x2,
    X.b * Y.y0 + Y.a * X.y0,
    X.b * Y.y1 + Y.a * X.y1,
    X.b * Y.y2 + Y.a * X.y2 ⟩

/-- The nonassociative teleport anomaly layer. -/
def teleport (X Y : SplitOct) : SplitOct :=
  ⟨0, 0,
    -(X.y1 * Y.y2 - X.y2 * Y.y1),
    -(X.y2 * Y.y0 - X.y0 * Y.y2),
    -(X.y0 * Y.y1 - X.y1 * Y.y0),
    (X.x1 * Y.x2 - X.x2 * Y.x1),
    (X.x2 * Y.x0 - X.x0 * Y.x2),
    (X.x0 * Y.x1 - X.x1 * Y.x0)⟩

/-- The teleport layer lives entirely in the off-diagonal coordinates. -/
theorem teleport_is_purely_off_diagonal (X Y : SplitOct) :
    (teleport X Y).a = 0 ∧ (teleport X Y).b = 0 := by
  constructor <;> rfl

/-- The multiplication splits as backbone plus teleport anomaly. -/
theorem decomposition_lemma (X Y : SplitOct) : mulZ X Y = assocMul X Y + teleport X Y := by
  ext <;> simp [mulZ, assocMul, teleport, sub_eq_add_neg]

/-- The product commutator splits into backbone and teleport contributions. -/
theorem commutator_leak_extraction (X Y : SplitOct) :
    subZ (mulZ X Y) (mulZ Y X) =
      subZ (assocMul X Y) (assocMul Y X) + subZ (teleport X Y) (teleport Y X) := by
  ext <;> simp [subZ, decomposition_lemma] <;> ring_nf

/-- Coordinate associator `(xy)z - x(yz)`. -/
def associator (X Y Z : SplitOct) : SplitOct := subZ (mulZ (mulZ X Y) Z) (mulZ X (mulZ Y Z))

/-- Left-regular action on the true nonassociative `SplitOct` carrier. -/
def leftRegular (X : SplitOct) : SplitOct → SplitOct :=
  fun Y => mulZ X Y

def leftRegularAddHom (X : SplitOct) : SplitOct →+ SplitOct where
  toFun := leftRegular X
  map_zero' := by
    cases X
    ext <;> simp [leftRegular, mulZ]
  map_add' Y Z := by
    cases X; cases Y; cases Z
    ext <;> simp [leftRegular, mulZ, add_a, add_b, add_x0, add_x1, add_x2, add_y0, add_y1, add_y2]
    <;> ring

def leftRegularLinear (X : SplitOct) : SplitOct →ₗ[ℤ] SplitOct :=
  (leftRegularAddHom X).toIntLinearMap

/-- The failure of left-regular multiplication to be multiplicative is the
negative of the explicit associator. -/
theorem leftRegular_mul_defect (X Y Z : SplitOct) :
    subZ (leftRegular X (leftRegular Y Z))
        (leftRegular (mulZ X Y) Z) =
      negZ (associator X Y Z) := by
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    cases Y with
    | mk c d u0 u1 u2 v0 v1 v2 =>
      cases Z with
      | mk e f r0 r1 r2 s0 s1 s2 =>
        ext <;> simp [leftRegular, associator, mulZ, subZ, negZ]

/-- Left-regular multiplication inherits norm composition from `mulZ`. -/
theorem leftRegular_normZ_mul (X Y : SplitOct) :
    normZ (leftRegular X Y) = normZ X * normZ Y := by
  simp [leftRegular, normZ_mul]

theorem leftRegularLinear_range_isotropic (X : SplitOct)
    (hX : normZ X = 0) :
    ∀ Y : SplitOct, Y ∈ LinearMap.range (leftRegularLinear X) → normZ Y = 0 := by
  intro Y hY
  rcases hY with ⟨Z, rfl⟩
  dsimp [leftRegularLinear, leftRegularAddHom, leftRegular]
  rw [normZ_mul, hX, zero_mul]

/-- Right-regular action on the true nonassociative `SplitOct` carrier. -/
def rightRegular (X : SplitOct) : SplitOct → SplitOct :=
  fun Y => mulZ Y X

/-- Right-regular multiplication inherits norm composition from `mulZ`. -/
theorem rightRegular_normZ_mul (X Y : SplitOct) :
    normZ (rightRegular X Y) = normZ Y * normZ X := by
  simp [rightRegular, normZ_mul]

theorem rightRegular_mul_defect (X Y Z : SplitOct) :
    subZ (rightRegular X (rightRegular Y Z))
        (rightRegular (mulZ Y X) Z) =
      associator Z Y X := by
  rfl

/-- First diagonal idempotent. -/
def ePlus : SplitOct := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- Second diagonal idempotent. -/
def eMinus : SplitOct := ⟨0, 1, 0, 0, 0, 0, 0, 0⟩

/-- Upper Zorn vector units. -/
def up0 : SplitOct := ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
def up1 : SplitOct := ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
def up2 : SplitOct := ⟨0, 0, 0, 0, 1, 0, 0, 0⟩

/-- Lower Zorn vector units. -/
def down0 : SplitOct := ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
def down1 : SplitOct := ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
def down2 : SplitOct := ⟨0, 0, 0, 0, 0, 0, 0, 1⟩

/-- Eight named basis constructors for the split-octonion multiplication table. -/
inductive Basis8 where
  | ePlus | eMinus | up0 | up1 | up2 | down0 | down1 | down2
  deriving DecidableEq, Repr, Fintype

/-- The basis element corresponding to an indexed constructor. -/
def basisElem : Basis8 → SplitOct
  | Basis8.ePlus => ePlus
  | Basis8.eMinus => eMinus
  | Basis8.up0 => up0
  | Basis8.up1 => up1
  | Basis8.up2 => up2
  | Basis8.down0 => down0
  | Basis8.down1 => down1
  | Basis8.down2 => down2

/-- Finite multiplication table on the indexed basis. -/
def basisMul : Basis8 → Basis8 → SplitOct
  | Basis8.ePlus, Basis8.ePlus => ePlus
  | Basis8.ePlus, Basis8.eMinus => zeroZ
  | Basis8.ePlus, Basis8.up0 => up0
  | Basis8.ePlus, Basis8.up1 => up1
  | Basis8.ePlus, Basis8.up2 => up2
  | Basis8.ePlus, Basis8.down0 => zeroZ
  | Basis8.ePlus, Basis8.down1 => zeroZ
  | Basis8.ePlus, Basis8.down2 => zeroZ
  | Basis8.eMinus, Basis8.ePlus => zeroZ
  | Basis8.eMinus, Basis8.eMinus => eMinus
  | Basis8.eMinus, Basis8.up0 => zeroZ
  | Basis8.eMinus, Basis8.up1 => zeroZ
  | Basis8.eMinus, Basis8.up2 => zeroZ
  | Basis8.eMinus, Basis8.down0 => down0
  | Basis8.eMinus, Basis8.down1 => down1
  | Basis8.eMinus, Basis8.down2 => down2
  | Basis8.up0, Basis8.ePlus => zeroZ
  | Basis8.up0, Basis8.eMinus => up0
  | Basis8.up0, Basis8.up0 => zeroZ
  | Basis8.up0, Basis8.up1 => down2
  | Basis8.up0, Basis8.up2 => negZ down1
  | Basis8.up0, Basis8.down0 => ePlus
  | Basis8.up0, Basis8.down1 => zeroZ
  | Basis8.up0, Basis8.down2 => zeroZ
  | Basis8.up1, Basis8.ePlus => zeroZ
  | Basis8.up1, Basis8.eMinus => up1
  | Basis8.up1, Basis8.up0 => negZ down2
  | Basis8.up1, Basis8.up1 => zeroZ
  | Basis8.up1, Basis8.up2 => down0
  | Basis8.up1, Basis8.down0 => zeroZ
  | Basis8.up1, Basis8.down1 => ePlus
  | Basis8.up1, Basis8.down2 => zeroZ
  | Basis8.up2, Basis8.ePlus => zeroZ
  | Basis8.up2, Basis8.eMinus => up2
  | Basis8.up2, Basis8.up0 => down1
  | Basis8.up2, Basis8.up1 => negZ down0
  | Basis8.up2, Basis8.up2 => zeroZ
  | Basis8.up2, Basis8.down0 => zeroZ
  | Basis8.up2, Basis8.down1 => zeroZ
  | Basis8.up2, Basis8.down2 => ePlus
  | Basis8.down0, Basis8.ePlus => down0
  | Basis8.down0, Basis8.eMinus => zeroZ
  | Basis8.down0, Basis8.up0 => eMinus
  | Basis8.down0, Basis8.up1 => zeroZ
  | Basis8.down0, Basis8.up2 => zeroZ
  | Basis8.down0, Basis8.down0 => zeroZ
  | Basis8.down0, Basis8.down1 => negZ up2
  | Basis8.down0, Basis8.down2 => up1
  | Basis8.down1, Basis8.ePlus => down1
  | Basis8.down1, Basis8.eMinus => zeroZ
  | Basis8.down1, Basis8.up0 => zeroZ
  | Basis8.down1, Basis8.up1 => eMinus
  | Basis8.down1, Basis8.up2 => zeroZ
  | Basis8.down1, Basis8.down0 => up2
  | Basis8.down1, Basis8.down1 => zeroZ
  | Basis8.down1, Basis8.down2 => negZ up0
  | Basis8.down2, Basis8.ePlus => down2
  | Basis8.down2, Basis8.eMinus => zeroZ
  | Basis8.down2, Basis8.up0 => zeroZ
  | Basis8.down2, Basis8.up1 => zeroZ
  | Basis8.down2, Basis8.up2 => eMinus
  | Basis8.down2, Basis8.down0 => negZ up1
  | Basis8.down2, Basis8.down1 => up0
  | Basis8.down2, Basis8.down2 => zeroZ

@[simp] theorem basisElem_mul (i j : Basis8) : mulZ (basisElem i) (basisElem j) = basisMul i j := by
  cases i <;> cases j <;> decide


/-- Index readout for upper units. -/
def up : Fin 3 → SplitOct
  | 0 => up0
  | 1 => up1
  | 2 => up2

/-- Index readout for lower units. -/
def down : Fin 3 → SplitOct
  | 0 => down0
  | 1 => down1
  | 2 => down2

theorem ePlus_idempotent : mulZ ePlus ePlus = ePlus := by decide
theorem eMinus_idempotent : mulZ eMinus eMinus = eMinus := by decide
theorem ePlus_mul_eMinus : mulZ ePlus eMinus = zeroZ := by decide
theorem eMinus_mul_ePlus : mulZ eMinus ePlus = zeroZ := by decide

theorem ePlus_mul_up (i : Fin 3) : mulZ ePlus (up i) = up i := by
  fin_cases i <;> decide
theorem eMinus_mul_up_zero (i : Fin 3) : mulZ eMinus (up i) = zeroZ := by
  fin_cases i <;> decide
theorem up_mul_eMinus (i : Fin 3) : mulZ (up i) eMinus = up i := by
  fin_cases i <;> decide
theorem up_mul_ePlus_zero (i : Fin 3) : mulZ (up i) ePlus = zeroZ := by
  fin_cases i <;> decide

theorem eMinus_mul_down (i : Fin 3) : mulZ eMinus (down i) = down i := by
  fin_cases i <;> decide
theorem ePlus_mul_down_zero (i : Fin 3) : mulZ ePlus (down i) = zeroZ := by
  fin_cases i <;> decide
theorem down_mul_ePlus (i : Fin 3) : mulZ (down i) ePlus = down i := by
  fin_cases i <;> decide
theorem down_mul_eMinus_zero (i : Fin 3) : mulZ (down i) eMinus = zeroZ := by
  fin_cases i <;> decide

theorem up_sq_zero (i : Fin 3) : mulZ (up i) (up i) = zeroZ := by
  fin_cases i <;> decide
theorem down_sq_zero (i : Fin 3) : mulZ (down i) (down i) = zeroZ := by
  fin_cases i <;> decide
theorem up_mul_down_same (i : Fin 3) : mulZ (up i) (down i) = ePlus := by
  fin_cases i <;> decide
theorem down_mul_up_same (i : Fin 3) : mulZ (down i) (up i) = eMinus := by
  fin_cases i <;> decide

/-- The two Peirce idempotents sum to the Zorn identity `⟨1,1,0,...⟩`. -/
theorem ePlus_add_eMinus : ePlus + eMinus = ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ := by
  ext <;> simp [ePlus, eMinus]

/-- Jordan (anticommutator) combination of matched chiral pairs equals the
    Peirce identity `ePlus + eMinus`. -/
theorem anticommutator_up_down_same (i : Fin 3) :
    mulZ (up i) (down i) + mulZ (down i) (up i) = ePlus + eMinus := by
  fin_cases i <;> decide

/-- Lie (commutator) combination of matched chiral pairs equals the
    Peirce difference `ePlus - eMinus`. -/
theorem commutator_up_down_same (i : Fin 3) :
    mulZ (up i) (down i) - mulZ (down i) (up i) = ePlus - eMinus := by
  fin_cases i <;> decide

theorem up0_mul_up1 : mulZ up0 up1 = down2 := by decide
theorem up1_mul_up2 : mulZ up1 up2 = down0 := by decide
theorem up2_mul_up0 : mulZ up2 up0 = down1 := by decide
theorem up1_mul_up0 : mulZ up1 up0 = negZ down2 := by decide
theorem up2_mul_up1 : mulZ up2 up1 = negZ down0 := by decide
theorem up0_mul_up2 : mulZ up0 up2 = negZ down1 := by decide

theorem down0_mul_down1 : mulZ down0 down1 = negZ up2 := by decide
theorem down1_mul_down2 : mulZ down1 down2 = negZ up0 := by decide
theorem down2_mul_down0 : mulZ down2 down0 = negZ up1 := by decide
theorem down1_mul_down0 : mulZ down1 down0 = up2 := by decide
theorem down2_mul_down1 : mulZ down2 down1 = up0 := by decide
theorem down0_mul_down2 : mulZ down0 down2 = up1 := by decide

/-- Concrete nonassociativity property: `(u₀u₁)v₁ - u₀(u₁v₁) = u₀`. -/
theorem associator_up0_up1_down1 : associator up0 up1 down1 = up0 := by decide

/-- The concrete associator property is nonzero. -/
theorem associator_up0_up1_down1_ne_zero : associator up0 up1 down1 ≠ zeroZ := by decide

/-- The split-octonion multiplication is not associative. -/
theorem splitOctonion_not_associative : ∃ X Y Z : SplitOct, associator X Y Z ≠ zeroZ := by
  exact ⟨up0, up1, down1, associator_up0_up1_down1_ne_zero⟩

/-- There is no global associativity law for the split-octonion product. -/
theorem not_associative_mulZ : ¬ ∀ X Y Z : SplitOct, associator X Y Z = zeroZ := by
  intro h
  exact associator_up0_up1_down1_ne_zero (h up0 up1 down1)

/-- Basis left-alternativity check for upper units against upper units. -/
theorem up_left_alternative_on_up (i j : Fin 3) : associator (up i) (up i) (up j) = zeroZ := by
  fin_cases i <;> fin_cases j <;> decide

/-- Basis right-alternativity check for upper units against upper units. -/
theorem up_right_alternative_on_up (i j : Fin 3) : associator (up j) (up i) (up i) = zeroZ := by
  fin_cases i <;> fin_cases j <;> decide

/-- Basis left-alternativity check for lower units against lower units. -/
theorem down_left_alternative_on_down (i j : Fin 3) : associator (down i) (down i) (down j) = zeroZ := by
  fin_cases i <;> fin_cases j <;> decide

/-- Basis right-alternativity check for lower units against lower units. -/
theorem down_right_alternative_on_down (i j : Fin 3) : associator (down j) (down i) (down i) = zeroZ := by
  fin_cases i <;> fin_cases j <;> decide

/-- Basis left alternativity for all named Zorn basis elements. -/
theorem basis_left_alternative (i j : Basis8) :
    associator (basisElem i) (basisElem i) (basisElem j) = zeroZ := by
  cases i <;> cases j <;> decide

/-- Basis right alternativity for all named Zorn basis elements. -/
theorem basis_right_alternative (i j : Basis8) :
    associator (basisElem j) (basisElem i) (basisElem i) = zeroZ := by
  cases i <;> cases j <;> decide

theorem detZ_ePlus : detZ ePlus = 0 := by decide
theorem detZ_eMinus : detZ eMinus = 0 := by decide
theorem detZ_up (i : Fin 3) : detZ (up i) = 0 := by
  fin_cases i <;> decide
theorem detZ_down (i : Fin 3) : detZ (down i) = 0 := by
  fin_cases i <;> decide

/-- Correct conjugation `conj(a, x; y, b) = (b, -x; -y, a)` giving `Z·conj(Z) = detZ(Z)·1`. -/
def conjZ (X : SplitOct) : SplitOct :=
  ⟨X.b, X.a, -X.x0, -X.x1, -X.x2, -X.y0, -X.y1, -X.y2⟩

/-- Scalar embedding: `r ↦ (r, 0; 0, r)`, the identity element when `r = 1`. -/
def scalarZ (r : ℤ) : SplitOct :=
  ⟨r, r, 0, 0, 0, 0, 0, 0⟩

theorem scalarZ_mul_eq_zero_of_ne_zero
    {r : ℤ} {X : SplitOct} (hX : X ≠ zeroZ)
    (h : mulZ (scalarZ r) X = zeroZ) : r = 0 := by
  by_contra hr
  apply hX
  cases X with
  | mk a b x0 x1 x2 y0 y1 y2 =>
    have ha : r * a = 0 := by have := congrArg SplitOct.a h; simpa [scalarZ, mulZ, zeroZ] using this
    have hb : r * b = 0 := by have := congrArg SplitOct.b h; simpa [scalarZ, mulZ, zeroZ] using this
    have hx0 : r * x0 = 0 := by have := congrArg SplitOct.x0 h; simpa [scalarZ, mulZ, zeroZ] using this
    have hx1 : r * x1 = 0 := by have := congrArg SplitOct.x1 h; simpa [scalarZ, mulZ, zeroZ] using this
    have hx2 : r * x2 = 0 := by have := congrArg SplitOct.x2 h; simpa [scalarZ, mulZ, zeroZ] using this
    have hy0 : r * y0 = 0 := by have := congrArg SplitOct.y0 h; simpa [scalarZ, mulZ, zeroZ] using this
    have hy1 : r * y1 = 0 := by have := congrArg SplitOct.y1 h; simpa [scalarZ, mulZ, zeroZ] using this
    have hy2 : r * y2 = 0 := by have := congrArg SplitOct.y2 h; simpa [scalarZ, mulZ, zeroZ] using this
    ext <;> simp [zeroZ]
    · exact (mul_eq_zero.mp ha).resolve_left hr
    · exact (mul_eq_zero.mp hb).resolve_left hr
    · exact (mul_eq_zero.mp hx0).resolve_left hr
    · exact (mul_eq_zero.mp hx1).resolve_left hr
    · exact (mul_eq_zero.mp hx2).resolve_left hr
    · exact (mul_eq_zero.mp hy0).resolve_left hr
    · exact (mul_eq_zero.mp hy1).resolve_left hr
    · exact (mul_eq_zero.mp hy2).resolve_left hr

/-! ## Trace/determinant truth cross-section -/

/-- Coordinatewise scalar multiplication on the concrete Zorn carrier. -/
def scaleZ (q : ℤ) (X : SplitOct) : SplitOct :=
  ⟨q * X.a, q * X.b, q * X.x0, q * X.x1, q * X.x2,
    q * X.y0, q * X.y1, q * X.y2⟩

/-- Trace coordinate of the concrete Zorn cell. -/
def trZ (X : SplitOct) : ℤ := X.a + X.b

/-- Discriminant of the observable trace/determinant base. -/
def discZ (X : SplitOct) : ℤ := trZ X ^ 2 - 4 * detZ X

/-- The observable thermodynamic base: trace and determinant only. -/
structure ThermodynamicBase where
  trace : ℤ
  det : ℤ
  deriving DecidableEq, Repr

/-- Projection from a concrete Zorn cell to its observable trace/determinant base. -/
def projectToBase (X : SplitOct) : ThermodynamicBase :=
  ⟨trZ X, detZ X⟩

/-! ### Base composition readbacks -/

/-- A concrete state is on the diagonal/bosonic section when all off-diagonal
Zorn coordinates vanish.  This is only a coordinate predicate on `SplitOct`; it
does not assert a principal-bundle or quantum-field interpretation. -/
def IsPureBosonic (X : SplitOct) : Prop :=
  X.x0 = 0 ∧ X.x1 = 0 ∧ X.x2 = 0 ∧ X.y0 = 0 ∧ X.y1 = 0 ∧ X.y2 = 0

/-- Alias for the diagonal/bosonic section predicate. -/
abbrev PureBosonicSection := IsPureBosonic

/-- Exact trace formula for a concrete Zorn product.  The final two parenthesized
terms are the off-diagonal leakage into the trace coordinate. -/
theorem trZ_mulZ_formula (X Y : SplitOct) :
    trZ (mulZ X Y) =
      X.a * Y.a + X.b * Y.b +
        (X.x0 * Y.y0 + X.x1 * Y.y1 + X.x2 * Y.y2) +
        (X.y0 * Y.x0 + X.y1 * Y.x1 + X.y2 * Y.x2) := by
  cases X
  cases Y
  unfold trZ mulZ
  ring

/-- Alias for the explicit trace-leak formula. -/
theorem trZ_mulZ_leak_formula (X Y : SplitOct) :
    trZ (mulZ X Y) =
      X.a * Y.a + X.b * Y.b +
        (X.x0 * Y.y0 + X.x1 * Y.y1 + X.x2 * Y.y2) +
        (X.y0 * Y.x0 + X.y1 * Y.x1 + X.y2 * Y.x2) := by
  simpa using trZ_mulZ_formula X Y

/-- On the diagonal/bosonic section the trace of a product is the sum of the two
naive diagonal products.  This is the correct closed trace law; in general it is
not `trZ X * trZ Y`. -/
theorem trZ_mulZ_pureBosonic_formula (X Y : SplitOct)
    (hX : IsPureBosonic X) (hY : IsPureBosonic Y) :
    trZ (mulZ X Y) = X.a * Y.a + X.b * Y.b := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases Y with ⟨c, d, u0, u1, u2, v0, v1, v2⟩
  rcases hX with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases hY with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [trZ, mulZ]

/-- Alias for the closed trace readback on the bosonic section. -/
theorem trace_closed_on_pureBosonicSection (X Y : SplitOct)
    (hX : PureBosonicSection X) (hY : PureBosonicSection Y) :
    trZ (mulZ X Y) = X.a * Y.a + X.b * Y.b := by
  simpa [PureBosonicSection] using trZ_mulZ_pureBosonic_formula X Y hX hY

/-- Correct base-composition readback on the diagonal/bosonic section: the trace
coordinate is `a_X a_Y + b_X b_Y`, while the determinant coordinate still uses
the global multiplicativity theorem `detZ_mul`. -/
theorem pureBosonic_projectToBase_mul_trace_det (X Y : SplitOct)
    (hX : IsPureBosonic X) (hY : IsPureBosonic Y) :
    (projectToBase (mulZ X Y)).trace = X.a * Y.a + X.b * Y.b ∧
      (projectToBase (mulZ X Y)).det = detZ X * detZ Y := by
  constructor
  · exact trZ_mulZ_pureBosonic_formula X Y hX hY
  · exact detZ_mul X Y

/-- Alias for the closed base readback on the bosonic section. -/
theorem global_base_conservation_on_pureBosonicSection (X Y : SplitOct)
    (hX : PureBosonicSection X) (hY : PureBosonicSection Y) :
    (projectToBase (mulZ X Y)).trace = X.a * Y.a + X.b * Y.b ∧
      (projectToBase (mulZ X Y)).det = detZ X * detZ Y := by
  simpa [PureBosonicSection] using pureBosonic_projectToBase_mul_trace_det X Y hX hY

/-- Centered trace cross-section representative `2X - tr(X)·1`. -/
def centeredCrossSection (X : SplitOct) : SplitOct :=
  subZ (scaleZ 2 X) (scaleZ (trZ X) (scalarZ 1))

/-- The concrete cross/teleport residue: the valid owner-level readback for the
off-diagonal latent-residue part of the Zorn product. -/
def latentDebtTensor (X Y : SplitOct) : SplitOct := teleport X Y

/-- The trace/determinant base projection reads back exactly the observable coordinates. -/
theorem projectToBase_trace_det (X : SplitOct) :
    (projectToBase X).trace = trZ X ∧ (projectToBase X).det = detZ X := by
  constructor <;> rfl

/-- Self-interaction of the teleport residue collapses on the concrete Zorn carrier. -/
theorem latentDebtTensor_self_eq_zeroZ (X : SplitOct) :
    latentDebtTensor X X = zeroZ := by
  cases X
  unfold latentDebtTensor teleport zeroZ
  ring_nf

/-- The centered trace cross-section squares to the discriminant scalar. -/
theorem centeredCrossSection_sq (X : SplitOct) :
    mulZ (centeredCrossSection X) (centeredCrossSection X) = scalarZ (discZ X) := by
  cases X
  ext <;> simp [centeredCrossSection, scaleZ, trZ, discZ, scalarZ, detZ, mulZ, subZ]
    <;> ring_nf

/-- Truth cross-section boundary: on the parabolic horizon `discZ = 0`, the
centered trace cross-section is square-zero. -/
theorem truth_cross_section_stability (X : SplitOct) (h : discZ X = 0) :
    mulZ (centeredCrossSection X) (centeredCrossSection X) = zeroZ := by
  rw [centeredCrossSection_sq, h]
  rfl

/-! ## Determinant-invertible statistical-variety readback -/

/-- Determinant-invertible locus over the trace/determinant base.

This is the valid algebraic projection of the proposed probability-measure
variety: it records the nonsingular determinant chart, but it does not assert a
smooth manifold, probability measure, Hessian calculation, or curvature theorem. -/
structure ZornStatisticalVariety where
  base : ThermodynamicBase
  det_invertible : Invertible base.det

/-- Algebraic inverse-determinant capacity.  This is the determinant part of a
log-barrier readback, not an analytic logarithm over `ℤ`. -/
def zornLogBarrierCapacity (M : ZornStatisticalVariety) : ℤ := by
  letI := M.det_invertible
  exact ⅟ M.base.det

/-- Three coordinate entries of the determinant-capacity tensor on the base.

This is a symbolic/algebraic tensor readback.  It is not promoted as a Fisher
metric from a proved smooth Hessian. -/
abbrev FisherMetricTensor := ℤ × ℤ × ℤ

/-- Coordinate accessors for the native triple representation. -/
abbrev FisherMetricTensor.g_trace_trace (G : FisherMetricTensor) : ℤ := G.1
abbrev FisherMetricTensor.g_trace_det (G : FisherMetricTensor) : ℤ := G.2.1
abbrev FisherMetricTensor.g_det_det (G : FisherMetricTensor) : ℤ := G.2.2

/-- Algebraic determinant-capacity tensor: only the determinant entry survives. -/
def computeFisherMetric (M : ZornStatisticalVariety) : FisherMetricTensor := by
  letI := M.det_invertible
  let invDet := ⅟ M.base.det
  exact (0, 0, invDet * invDet)

/-! ### Algebraic information-geometry readbacks -/

/-- Symbolic determinant-capacity connection coefficient.

This is the truth-cross-section of a proposed Christoffel-symbol formula.  It is
only an algebraic readback over the determinant-invertible integer owner lane;
it does not assert a smooth manifold, Levi-Civita connection, geodesic equation,
or curvature theorem. -/
abbrev CapacityConnectionSymbol := ℤ

/-- Compatibility accessor for the native integer coefficient carrier. -/
abbrev CapacityConnectionSymbol.gamma_det_det_det
    (C : CapacityConnectionSymbol) : ℤ := C

/-- Algebraic inverse-cubic determinant-capacity coefficient. -/
def capacityConnectionZ (M : ZornStatisticalVariety) : CapacityConnectionSymbol := by
  letI := M.det_invertible
  let invDet := ⅟ M.base.det
  exact -(2 * (invDet * invDet * invDet))

/-- Cleared algebraic KL-style jet.

This is twice the symbolic contrast, avoiding division by `2` over the integer
owner lane.  It is not a theorem about analytic KL divergence, Taylor expansion,
or a Fisher-Hessian identification. -/
def twiceAlgebraicKLJet (M : ZornStatisticalVariety) (d_det : ℤ) : ℤ := by
  letI := M.det_invertible
  let invDet := ⅟ M.base.det
  exact 2 * (invDet * d_det) + (invDet * invDet) * (d_det * d_det)

/-- Two symbolic capacity-defect charges.  These are algebraic labels, not a
cohomology theory or a geometric lattice-disclination construction. -/
inductive CapacityDefect where
  | pentagon
  | heptagon
  deriving DecidableEq, Repr

/-- Integer charge readback for the two symbolic capacity defects. -/
def capacityDefectCharge : CapacityDefect → ℤ
  | CapacityDefect.pentagon => 1
  | CapacityDefect.heptagon => -1

/-- Symbolically warp only the determinant-capacity tensor entry by a defect
charge. -/
def defectWarpedCapacityTensor (M : ZornStatisticalVariety)
    (d : CapacityDefect) : FisherMetricTensor :=
  let g := computeFisherMetric M
  (g.g_trace_trace, g.g_trace_det, g.g_det_det + capacityDefectCharge d)

/-! ### Axiom-clean raw algebraic cores

The following raw readbacks avoid the `Invertible`/instance surface and avoid
normalization tactics.  They are definitional integer-coordinate facts, not
smooth information geometry. -/

/-- Raw inverse-cubic capacity coefficient from an explicitly supplied inverse
determinant coordinate. -/
def rawCapacityConnection (invDet : ℤ) : CapacityConnectionSymbol :=
  -2 * (invDet * invDet * invDet)

/-- Axiom-clean definitional readback for the raw inverse-cubic coefficient. -/
theorem rawCapacityConnection_readback (invDet : ℤ) :
    (rawCapacityConnection invDet).gamma_det_det_det =
      -2 * (invDet * invDet * invDet) := by
  rfl

/-- Raw determinant-capacity metric entry from an explicitly supplied inverse
determinant coordinate. -/
def rawCapacityMetricDet (invDet : ℤ) : ℤ := invDet * invDet

/-- Raw cleared algebraic KL-style jet from an explicitly supplied inverse
determinant coordinate. -/
def rawTwiceAlgebraicKLJet (invDet d_det : ℤ) : ℤ :=
  2 * (invDet * d_det) + (invDet * invDet) * (d_det * d_det)

/-- Axiom-clean definitional expansion of the raw cleared KL-style jet. -/
theorem rawTwiceAlgebraicKLJet_expansion (invDet d_det : ℤ) :
    rawTwiceAlgebraicKLJet invDet d_det =
      2 * (invDet * d_det) + (invDet * invDet) * (d_det * d_det) := by
  rfl

/-- Raw symbolic defect tensor entry with an explicit base entry and charge. -/
def rawDefectWarpedMetricDet (g charge : ℤ) : ℤ := g + charge

/-- Axiom-clean readback for the raw pentagon charge. -/
theorem rawDefectCharge_pentagon : capacityDefectCharge CapacityDefect.pentagon = 1 := by
  rfl

/-- Axiom-clean readback for the raw heptagon charge. -/
theorem rawDefectCharge_heptagon : capacityDefectCharge CapacityDefect.heptagon = -1 := by
  rfl

/-- A statistical-variety state is critical when its trace/determinant base lies
on the same parabolic discriminant used by the truth cross-section theorem. -/
def IsCriticalVarietyState (M : ZornStatisticalVariety) : Prop :=
  M.base.trace ^ 2 - 4 * M.base.det = 0

/-- A concrete split-octonion state with invertible determinant induces a point
on the determinant-invertible statistical-variety readback. -/
def statisticalVarietyOfSplitOct (X : SplitOct) [Invertible (detZ X)] :
    ZornStatisticalVariety :=
  { base := projectToBase X
    det_invertible := by
      simpa [projectToBase] using (inferInstance : Invertible (detZ X)) }

/-- The split-octonion statistical-variety point keeps the original trace and determinant. -/
theorem statisticalVarietyOfSplitOct_base_trace_det
    (X : SplitOct) [Invertible (detZ X)] :
    (statisticalVarietyOfSplitOct X).base.trace = trZ X ∧
      (statisticalVarietyOfSplitOct X).base.det = detZ X := by
  exact projectToBase_trace_det X

/-- Conjugation is an involution. -/
theorem conjZ_conjZ (X : SplitOct) : conjZ (conjZ X) = X := by
  cases X; simp [conjZ]

/-- The determinant is invariant under conjugation. -/
theorem detZ_conjZ (X : SplitOct) : detZ (conjZ X) = detZ X := by
  cases X; simp [conjZ, detZ]; ring_nf

/-- **Alternative property:** `Z·conj(Z) = detZ(Z)·1` in the Zorn model. -/
theorem mul_conjZ_eq_scalar_detZ (X : SplitOct) : mulZ X (conjZ X) = scalarZ (detZ X) := by
  cases X; unfold mulZ conjZ scalarZ detZ; ring_nf

/-! ## Conjugation on basis elements -/

theorem conjZ_ePlus : conjZ ePlus = eMinus := by simp [conjZ, ePlus, eMinus]
theorem conjZ_eMinus : conjZ eMinus = ePlus := by simp [conjZ, ePlus, eMinus]
theorem conjZ_zeroZ : conjZ zeroZ = zeroZ := by simp [conjZ, zeroZ]
theorem conjZ_up (i : Fin 3) : conjZ (up i) = negZ (up i) := by
  fin_cases i <;> simp [conjZ, negZ, up, up0, up1, up2]
theorem conjZ_down (i : Fin 3) : conjZ (down i) = negZ (down i) := by
  fin_cases i <;> simp [conjZ, negZ, down, down0, down1, down2]
/-- `conjZ` is an anti-automorphism: `conjZ(mulZ X Y) = mulZ(conjZ Y)(conjZ X)`. -/
theorem conjZ_mulZ (X Y : SplitOct) :
    conjZ (mulZ X Y) = mulZ (conjZ Y) (conjZ X) := by
  ext <;> simp [conjZ, mulZ] <;> ring_nf

/-- Left alternative cancellation. -/
theorem left_alternative_cancellation (X Y : SplitOct) : 
    mulZ (conjZ X) (mulZ X Y) = mulZ (scalarZ (detZ X)) Y := by
  ext <;> simp [mulZ, conjZ, scalarZ, detZ] <;> ring_nf

/-- Right alternative cancellation. -/
theorem right_alternative_cancellation (X Y : SplitOct) : 
    mulZ (mulZ Y X) (conjZ X) = mulZ (scalarZ (detZ X)) Y := by
  ext <;> simp [mulZ, conjZ, scalarZ, detZ] <;> ring_nf

/-- Middle Moufang identity for the split octonions. -/
theorem moufang_identity (X Y Z : SplitOct) : 
    mulZ (mulZ X Y) (mulZ Z X) = mulZ X (mulZ (mulZ Y Z) X) := by
  ext <;> simp [mulZ] <;> ring_nf

end InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
