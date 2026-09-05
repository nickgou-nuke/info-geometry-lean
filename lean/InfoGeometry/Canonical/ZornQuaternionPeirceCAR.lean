import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import Mathlib.Tactic

/-!
# Quaternionic Clifford frames and Peirce contraction identities in the Zorn carrier

This file reconstructs the exact algebra hidden in an informal fusion of
`Pin⁻(3)`, split octonions, projectors, and fermionic ladders.

The distinctions are essential:

* the full real Zorn vector-matrix carrier is nonassociative;
* the paravector slice `zornMk a a x (-x)` is an associative quaternionic
  slice;
* the two diagonal elements are complementary orthogonal idempotents;
* the upper and lower vector blocks are nilpotent Peirce generators;
* their binary mixed anticommutator is the Euclidean contraction times the
  Zorn unit.

The last identity has the shape of a CAR relation, but this file does not call
the full nonassociative Zorn carrier a CAR algebra. A representation of the
associative CAR algebra would require a separate associative operator envelope.
Likewise, the negative Clifford relations below are the algebraic frame used by
`Pin⁻(3)`; no global Pin-group equivalence is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornQuaternionPeirceCAR

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

abbrev Carrier := ZornCoord

/-! ## Scalar and idempotent readouts -/

/-- Scalar Zorn elements are ordinary scalar multiples of the Zorn unit. -/
@[simp] theorem scalarZorn_eq_smul_zornOne (c : ℝ) :
    scalarZorn c = c • zornOne := by
  ext i <;> simp [scalarZorn, zornOne, zornMk]

/-- Left diagonal idempotent. The name is algebraic; no vacuum interpretation
is built into the definition. -/
def leftIdempotent : Carrier := pPlus

/-- Right diagonal idempotent. -/
def rightIdempotent : Carrier := pMinus

@[simp] theorem leftIdempotent_sq :
    zornMul leftIdempotent leftIdempotent = leftIdempotent := by
  ext i <;>
    simp [leftIdempotent, pPlus, zornMul, zornMk, zornA, zornB, zornX, zornY,
      dot3, cross3] <;>
    try { fin_cases i <;> simp }

@[simp] theorem rightIdempotent_sq :
    zornMul rightIdempotent rightIdempotent = rightIdempotent := by
  ext i <;>
    simp [rightIdempotent, pMinus, zornMul, zornMk, zornA, zornB, zornX,
      zornY, dot3, cross3] <;>
    try { fin_cases i <;> simp }

@[simp] theorem leftIdempotent_mul_rightIdempotent :
    zornMul leftIdempotent rightIdempotent = 0 := by
  simpa [leftIdempotent, rightIdempotent] using pPlus_mul_pMinus

@[simp] theorem rightIdempotent_mul_leftIdempotent :
    zornMul rightIdempotent leftIdempotent = 0 := by
  simpa [leftIdempotent, rightIdempotent] using pMinus_mul_pPlus

@[simp] theorem leftIdempotent_add_rightIdempotent :
    leftIdempotent + rightIdempotent = zornOne := by
  simpa [leftIdempotent, rightIdempotent] using pPlus_add_pMinus

/-- The two complementary idempotents are distinct. -/
theorem rightIdempotent_ne_leftIdempotent :
    rightIdempotent ≠ leftIdempotent := by
  intro h
  have hA := congrArg zornA h
  norm_num [rightIdempotent, leftIdempotent, pMinus, pPlus, zornA, zornMk] at hA

/-! ## Nilpotent Peirce generators -/

/-- Upper off-diagonal Peirce generator. -/
def upperRoot (u : Vec3) : Carrier := upperVectorZorn u

/-- Lower off-diagonal Peirce generator. -/
def lowerRoot (u : Vec3) : Carrier := lowerVectorZorn u

@[simp] theorem upperRoot_sq_zero (u : Vec3) :
    zornMul (upperRoot u) (upperRoot u) = 0 := by
  simpa [upperRoot] using upperVectorZorn_square_zero u

@[simp] theorem lowerRoot_sq_zero (u : Vec3) :
    zornMul (lowerRoot u) (lowerRoot u) = 0 := by
  simpa [lowerRoot] using lowerVectorZorn_square_zero u

/-- The upper generator occupies the `left-right` Peirce corner. -/
@[simp] theorem leftIdempotent_mul_upperRoot (u : Vec3) :
    zornMul leftIdempotent (upperRoot u) = upperRoot u := by
  ext i <;>
    simp [leftIdempotent, upperRoot, pPlus, upperVectorZorn, zornMul, zornMk,
      zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> simp }

@[simp] theorem upperRoot_mul_rightIdempotent (u : Vec3) :
    zornMul (upperRoot u) rightIdempotent = upperRoot u := by
  ext i <;>
    simp [rightIdempotent, upperRoot, pMinus, upperVectorZorn, zornMul, zornMk,
      zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> simp }

@[simp] theorem rightIdempotent_mul_upperRoot (u : Vec3) :
    zornMul rightIdempotent (upperRoot u) = 0 := by
  ext i <;>
    simp [rightIdempotent, upperRoot, pMinus, upperVectorZorn, zornMul, zornMk,
      zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> simp }

@[simp] theorem upperRoot_mul_leftIdempotent (u : Vec3) :
    zornMul (upperRoot u) leftIdempotent = 0 := by
  ext i <;>
    simp [leftIdempotent, upperRoot, pPlus, upperVectorZorn, zornMul, zornMk,
      zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> simp }

/-- The lower generator occupies the opposite `right-left` Peirce corner. -/
@[simp] theorem rightIdempotent_mul_lowerRoot (u : Vec3) :
    zornMul rightIdempotent (lowerRoot u) = lowerRoot u := by
  ext i <;>
    simp [rightIdempotent, lowerRoot, pMinus, lowerVectorZorn, zornMul, zornMk,
      zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> simp }

@[simp] theorem lowerRoot_mul_leftIdempotent (u : Vec3) :
    zornMul (lowerRoot u) leftIdempotent = lowerRoot u := by
  ext i <;>
    simp [leftIdempotent, lowerRoot, pPlus, lowerVectorZorn, zornMul, zornMk,
      zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> simp }

@[simp] theorem leftIdempotent_mul_lowerRoot (u : Vec3) :
    zornMul leftIdempotent (lowerRoot u) = 0 := by
  ext i <;>
    simp [leftIdempotent, lowerRoot, pPlus, lowerVectorZorn, zornMul, zornMk,
      zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> simp }

@[simp] theorem lowerRoot_mul_rightIdempotent (u : Vec3) :
    zornMul (lowerRoot u) rightIdempotent = 0 := by
  ext i <;>
    simp [rightIdempotent, lowerRoot, pMinus, lowerVectorZorn, zornMul, zornMk,
      zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> simp }

/-- Upper followed by lower resolves onto the left idempotent. -/
theorem upperRoot_mul_lowerRoot (u v : Vec3) :
    zornMul (upperRoot u) (lowerRoot v) =
      dot3 u v • leftIdempotent := by
  change zornMul (upperVectorZorn u) (lowerVectorZorn v) =
    dot3 u v • leftIdempotent
  rw [upperVectorZorn_mul_lowerVectorZorn]
  ext i <;> simp [leftIdempotent, pPlus, zornMk]

/-- Lower followed by upper resolves onto the right idempotent. -/
theorem lowerRoot_mul_upperRoot (u v : Vec3) :
    zornMul (lowerRoot v) (upperRoot u) =
      dot3 u v • rightIdempotent := by
  change zornMul (lowerVectorZorn v) (upperVectorZorn u) =
    dot3 u v • rightIdempotent
  rw [lowerVectorZorn_mul_upperVectorZorn]
  rw [dot3_comm v u]
  ext i <;> simp [rightIdempotent, pMinus, zornMk]

/-- Binary mixed anticommutator: the two Peirce channels recombine to the
Euclidean contraction times the unit. -/
theorem peirce_CAR (u v : Vec3) :
    zornMul (upperRoot u) (lowerRoot v) +
        zornMul (lowerRoot v) (upperRoot u) =
      dot3 u v • zornOne := by
  change zornMul (upperVectorZorn u) (lowerVectorZorn v) +
      zornMul (lowerVectorZorn v) (upperVectorZorn u) =
    dot3 u v • zornOne
  rw [upperLower_add_lowerUpper_scalar]
  exact scalarZorn_eq_smul_zornOne (dot3 u v)

/-- Equal-sheet upper generators anticommute. -/
theorem upperRoot_anticommutator_zero (u v : Vec3) :
    zornMul (upperRoot u) (upperRoot v) +
      zornMul (upperRoot v) (upperRoot u) = 0 := by
  simpa [upperRoot] using upperVectorZorn_add_mul_reverse_zero u v

/-- Equal-sheet lower generators anticommute. -/
theorem lowerRoot_anticommutator_zero (u v : Vec3) :
    zornMul (lowerRoot u) (lowerRoot v) +
      zornMul (lowerRoot v) (lowerRoot u) = 0 := by
  simpa [lowerRoot] using lowerVectorZorn_add_mul_reverse_zero u v

/-! ## Negative and split Clifford frames -/

/-- Negative-square Clifford generator. This is the quaternionic paravector
`(0,u,-u,0)` in Zorn coordinates. -/
def negativeCliffordGenerator (u : Vec3) : Carrier :=
  paravectorZorn 0 u

/-- Positive-square split generator `(0,u,u,0)`. -/
def splitCliffordGenerator (u : Vec3) : Carrier :=
  zornMk 0 0 u u

/-- The split generator is the sum of the two Peirce roots. -/
theorem splitCliffordGenerator_eq_upper_add_lower (u : Vec3) :
    splitCliffordGenerator u = upperRoot u + lowerRoot u := by
  ext i <;>
    simp [splitCliffordGenerator, upperRoot, lowerRoot, upperVectorZorn,
      lowerVectorZorn, zornMk]

/-- The negative Clifford generator is their difference. -/
theorem negativeCliffordGenerator_eq_upper_sub_lower (u : Vec3) :
    negativeCliffordGenerator u = upperRoot u - lowerRoot u := by
  ext i <;>
    simp [negativeCliffordGenerator, paravectorZorn, upperRoot, lowerRoot,
      upperVectorZorn, lowerVectorZorn, zornMk]

/-- Recovery of the upper nilpotent as a half-sum. -/
theorem upperRoot_eq_half_split_add_negative (u : Vec3) :
    upperRoot u =
      (1 / 2 : ℝ) •
        (splitCliffordGenerator u + negativeCliffordGenerator u) := by
  ext i <;>
    simp [upperRoot, splitCliffordGenerator, negativeCliffordGenerator,
      upperVectorZorn, paravectorZorn, zornMk] <;>
    ring

/-- Recovery of the lower nilpotent as a half-difference. -/
theorem lowerRoot_eq_half_split_sub_negative (u : Vec3) :
    lowerRoot u =
      (1 / 2 : ℝ) •
        (splitCliffordGenerator u - negativeCliffordGenerator u) := by
  ext i <;>
    simp [lowerRoot, splitCliffordGenerator, negativeCliffordGenerator,
      lowerVectorZorn, paravectorZorn, zornMk] <;>
    ring

/-- Negative Clifford square: `gamma(u)^2 = -<u,u> 1`. -/
theorem negativeCliffordGenerator_sq (u : Vec3) :
    zornMul (negativeCliffordGenerator u) (negativeCliffordGenerator u) =
      (-dot3 u u) • zornOne := by
  calc
    zornMul (negativeCliffordGenerator u) (negativeCliffordGenerator u) =
        paravectorZorn (-dot3 u u) 0 := by
      simpa [negativeCliffordGenerator, cross3_self] using
        (zornMul_paravectorZorn (0 : ℝ) 0 u u)
    _ = scalarZorn (-dot3 u u) := by
      symm
      exact scalarZorn_eq_paravectorZorn_zero (-dot3 u u)
    _ = (-dot3 u u) • zornOne := scalarZorn_eq_smul_zornOne _

/-- Split Clifford square: `K(u)^2 = <u,u> 1`. -/
theorem splitCliffordGenerator_sq (u : Vec3) :
    zornMul (splitCliffordGenerator u) (splitCliffordGenerator u) =
      dot3 u u • zornOne := by
  ext i <;>
    simp [splitCliffordGenerator, zornMul, zornOne, zornMk, zornA, zornB,
      zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> ring } <;>
    ring

/-- Polarized negative Clifford relation. -/
theorem negativeCliffordGenerator_anticommutator (u v : Vec3) :
    zornMul (negativeCliffordGenerator u) (negativeCliffordGenerator v) +
        zornMul (negativeCliffordGenerator v) (negativeCliffordGenerator u) =
      (-2 * dot3 u v) • zornOne := by
  ext i <;>
    simp [negativeCliffordGenerator, paravectorZorn, zornMul, zornOne, zornMk,
      zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> ring } <;>
    ring

/-- Polarized split Clifford relation. -/
theorem splitCliffordGenerator_anticommutator (u v : Vec3) :
    zornMul (splitCliffordGenerator u) (splitCliffordGenerator v) +
        zornMul (splitCliffordGenerator v) (splitCliffordGenerator u) =
      (2 * dot3 u v) • zornOne := by
  ext i <;>
    simp [splitCliffordGenerator, zornMul, zornOne, zornMk, zornA, zornB,
      zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> ring } <;>
    ring

/-- The negative and split copies are mutually orthogonal for the polarized
binary Clifford relation. -/
theorem negative_split_anticommutator_zero (u v : Vec3) :
    zornMul (negativeCliffordGenerator u) (splitCliffordGenerator v) +
      zornMul (splitCliffordGenerator v) (negativeCliffordGenerator u) = 0 := by
  ext i <;>
    simp [negativeCliffordGenerator, splitCliffordGenerator, paravectorZorn,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> ring } <;>
    ring

/-! ## The associative quaternionic slice -/

/-- Membership in the paravector/quaternionic slice. -/
def InQuaternionSlice (z : Carrier) : Prop :=
  ∃ a : ℝ, ∃ u : Vec3, z = paravectorZorn a u

/-- The negative Clifford frame lies in the quaternionic slice. -/
theorem negativeCliffordGenerator_mem_quaternionSlice (u : Vec3) :
    InQuaternionSlice (negativeCliffordGenerator u) := by
  exact ⟨0, u, rfl⟩

/-- Closure of the quaternionic slice under the Zorn product. -/
theorem quaternionSlice_mul_closed
    {p q : Carrier} (hp : InQuaternionSlice p) (hq : InQuaternionSlice q) :
    InQuaternionSlice (zornMul p q) := by
  rcases hp with ⟨a, u, rfl⟩
  rcases hq with ⟨b, v, rfl⟩
  exact ⟨a * b - dot3 u v,
    a • v + b • u - cross3 u v,
    zornMul_paravectorZorn a b u v⟩

/-- Direct associativity theorem on the quaternionic paravector slice. -/
theorem paravectorZorn_assoc
    (a b c : ℝ) (u v w : Vec3) :
    zornMul (zornMul (paravectorZorn a u) (paravectorZorn b v))
        (paravectorZorn c w) =
      zornMul (paravectorZorn a u)
        (zornMul (paravectorZorn b v) (paravectorZorn c w)) := by
  ext i <;>
    simp [zornMul, paravectorZorn, zornMk, zornA, zornB, zornX, zornY,
      dot3, cross3] <;>
    try { fin_cases i <;> ring } <;>
    ring

/-- Associativity transported to arbitrary elements known to lie in the
quaternionic slice. -/
theorem zornMul_assoc_of_mem_quaternionSlice
    {p q r : Carrier}
    (hp : InQuaternionSlice p)
    (hq : InQuaternionSlice q)
    (hr : InQuaternionSlice r) :
    zornMul (zornMul p q) r = zornMul p (zornMul q r) := by
  rcases hp with ⟨a, u, rfl⟩
  rcases hq with ⟨b, v, rfl⟩
  rcases hr with ⟨c, w, rfl⟩
  exact paravectorZorn_assoc a b c u v w

/-! ## A convention-correct quaternion table -/

/-- Standard coordinate axes. -/
def e1 : Vec3 := ![(1 : ℝ), 0, 0]
def e2 : Vec3 := ![0, (1 : ℝ), 0]
def e3 : Vec3 := ![0, 0, (1 : ℝ)]

@[simp] theorem dot3_e1_e1 : dot3 e1 e1 = 1 := by norm_num [dot3, e1]
@[simp] theorem dot3_e2_e2 : dot3 e2 e2 = 1 := by norm_num [dot3, e2]
@[simp] theorem dot3_e3_e3 : dot3 e3 e3 = 1 := by norm_num [dot3, e3]

@[simp] theorem cross3_e1_e2 : cross3 e1 e2 = e3 := by
  funext i
  fin_cases i <;> norm_num [cross3, e1, e2, e3]

@[simp] theorem cross3_e2_e3 : cross3 e2 e3 = e1 := by
  funext i
  fin_cases i <;> norm_num [cross3, e1, e2, e3]

@[simp] theorem cross3_e3_e1 : cross3 e3 e1 = e2 := by
  funext i
  fin_cases i <;> norm_num [cross3, e1, e2, e3]

/-- The canonical Zorn convention has
`gamma(e1) gamma(e2) = gamma(-e3)`. The sign in `qK` is therefore required to
obtain the standard quaternion orientation `qI qJ = qK`. -/
def qI : Carrier := negativeCliffordGenerator e1
def qJ : Carrier := negativeCliffordGenerator e2
def qK : Carrier := negativeCliffordGenerator (-e3)
def qNegOne : Carrier := (-1 : ℝ) • zornOne

@[simp] theorem qI_sq : zornMul qI qI = qNegOne := by
  simpa [qI, qNegOne, e1, dot3] using negativeCliffordGenerator_sq e1

@[simp] theorem qJ_sq : zornMul qJ qJ = qNegOne := by
  simpa [qJ, qNegOne, e2, dot3] using negativeCliffordGenerator_sq e2

@[simp] theorem qK_sq : zornMul qK qK = qNegOne := by
  simpa [qK, qNegOne, e3, dot3] using negativeCliffordGenerator_sq (-e3)

@[simp] theorem qI_mul_qJ : zornMul qI qJ = qK := by
  ext i <;>
    simp [qI, qJ, qK, negativeCliffordGenerator, paravectorZorn, e1, e2, e3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> norm_num } <;>
    norm_num

@[simp] theorem qJ_mul_qI : zornMul qJ qI = -qK := by
  ext i <;>
    simp [qI, qJ, qK, negativeCliffordGenerator, paravectorZorn, e1, e2, e3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> norm_num } <;>
    norm_num

@[simp] theorem qJ_mul_qK : zornMul qJ qK = qI := by
  ext i <;>
    simp [qI, qJ, qK, negativeCliffordGenerator, paravectorZorn, e1, e2, e3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> norm_num } <;>
    norm_num

@[simp] theorem qK_mul_qJ : zornMul qK qJ = -qI := by
  ext i <;>
    simp [qI, qJ, qK, negativeCliffordGenerator, paravectorZorn, e1, e2, e3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> norm_num } <;>
    norm_num

@[simp] theorem qK_mul_qI : zornMul qK qI = qJ := by
  ext i <;>
    simp [qI, qJ, qK, negativeCliffordGenerator, paravectorZorn, e1, e2, e3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> norm_num } <;>
    norm_num

@[simp] theorem qI_mul_qK : zornMul qI qK = -qJ := by
  ext i <;>
    simp [qI, qJ, qK, negativeCliffordGenerator, paravectorZorn, e1, e2, e3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> norm_num } <;>
    norm_num

/-- The multiplication packet characteristic of the three imaginary
quaternion units. The preceding slice-associativity theorem is what makes this
a quaternionic sector rather than merely a binary multiplication table. -/
theorem quaternion_table_packet :
    zornMul qI qI = qNegOne ∧
      zornMul qJ qJ = qNegOne ∧
      zornMul qK qK = qNegOne ∧
      zornMul qI qJ = qK ∧
      zornMul qJ qK = qI ∧
      zornMul qK qI = qJ ∧
      zornMul qJ qI = -qK ∧
      zornMul qK qJ = -qI ∧
      zornMul qI qK = -qJ := by
  exact ⟨qI_sq, qJ_sq, qK_sq, qI_mul_qJ, qJ_mul_qK, qK_mul_qI,
    qJ_mul_qI, qK_mul_qJ, qI_mul_qK⟩

/-! ## Explicit global nonassociativity witness -/

/-- One parenthesization of three upper roots lands on the right idempotent. -/
theorem upperRoot_triple_left :
    zornMul (zornMul (upperRoot e1) (upperRoot e2)) (upperRoot e3) =
      rightIdempotent := by
  ext i <;>
    simp [upperRoot, rightIdempotent, upperVectorZorn, pMinus, e1, e2, e3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> norm_num } <;>
    norm_num

/-- The other parenthesization lands on the left idempotent. -/
theorem upperRoot_triple_right :
    zornMul (upperRoot e1) (zornMul (upperRoot e2) (upperRoot e3)) =
      leftIdempotent := by
  ext i <;>
    simp [upperRoot, leftIdempotent, upperVectorZorn, pPlus, e1, e2, e3,
      zornMul, zornMk, zornA, zornB, zornX, zornY, dot3, cross3] <;>
    try { fin_cases i <;> norm_num } <;>
    norm_num

/-- The full Zorn carrier is not associative. This prevents the binary Peirce
CAR identity from being misreported as an associative CAR-algebra structure. -/
theorem zornMul_not_associative_witness :
    zornMul (zornMul (upperRoot e1) (upperRoot e2)) (upperRoot e3) ≠
      zornMul (upperRoot e1) (zornMul (upperRoot e2) (upperRoot e3)) := by
  rw [upperRoot_triple_left, upperRoot_triple_right]
  exact rightIdempotent_ne_leftIdempotent

/-! ## Compact theorem-safe packet -/

/-- The exact algebraic content of the reconstructed stream. -/
theorem zorn_quaternion_peirce_car_packet (u v : Vec3) :
    zornMul leftIdempotent leftIdempotent = leftIdempotent ∧
      zornMul rightIdempotent rightIdempotent = rightIdempotent ∧
      leftIdempotent + rightIdempotent = zornOne ∧
      zornMul (upperRoot u) (upperRoot u) = 0 ∧
      zornMul (lowerRoot v) (lowerRoot v) = 0 ∧
      zornMul (upperRoot u) (lowerRoot v) +
          zornMul (lowerRoot v) (upperRoot u) =
        dot3 u v • zornOne ∧
      zornMul (negativeCliffordGenerator u) (negativeCliffordGenerator v) +
          zornMul (negativeCliffordGenerator v) (negativeCliffordGenerator u) =
        (-2 * dot3 u v) • zornOne ∧
      zornMul (splitCliffordGenerator u) (splitCliffordGenerator v) +
          zornMul (splitCliffordGenerator v) (splitCliffordGenerator u) =
        (2 * dot3 u v) • zornOne := by
  exact ⟨leftIdempotent_sq, rightIdempotent_sq,
    leftIdempotent_add_rightIdempotent, upperRoot_sq_zero u,
    lowerRoot_sq_zero v, peirce_CAR u v,
    negativeCliffordGenerator_anticommutator u v,
    splitCliffordGenerator_anticommutator u v⟩

end InfoGeometry.Canonical.ZornQuaternionPeirceCAR
