import Mathlib.Tactic
import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Composition-algebra triality on the canonical Zorn carrier

This file distinguishes three eight-dimensional carriers:

* the vector copy `8v`;
* the positive semispinor copy `8s`;
* the negative semispinor copy `8c`.

All three are typed wrappers around the canonical complex Zorn composition
algebra.  They are not definitionally interchangeable.  Zorn multiplication
and conjugation give the two chiral Clifford actions

`8v × 8s → 8c` and `8v × 8c → 8s`.

The main quadratic identities prove that composing the two actions is scalar
multiplication by the Zorn norm.  This is the composition-algebra form of the
split Clifford relation underlying Cartan triality.
-/

noncomputable section

open InfoGeometry.Physics.SplitOctonionBraidSU3

namespace CanonicalZornCompositionTriality
/-- Eight canonical complex coordinates of a Zorn element. -/
def zornCoordinates (X : Zorn) : Fin 8 → ℂ :=
  ![X.a, X.u 0, X.u 1, X.u 2, X.v 0, X.v 1, X.v 2, X.b]

theorem zornCoordinates_injective : Function.Injective zornCoordinates := by
  intro X Y h
  apply zorn_ext
  · exact congrFun h 0
  · funext i
    fin_cases i
    · exact congrFun h 1
    · exact congrFun h 2
    · exact congrFun h 3
  · funext i
    fin_cases i
    · exact congrFun h 4
    · exact congrFun h 5
    · exact congrFun h 6
  · exact congrFun h 7

/-! ## Canonical conjugation and quadratic action identities -/

/-- Standard conjugation of a Zorn matrix. -/
def zornConj (X : Zorn) : Zorn where
  a := X.b
  u := fun i => -X.u i
  v := fun i => -X.v i
  b := X.a

@[simp] theorem zornConj_conj (X : Zorn) : zornConj (zornConj X) = X := by
  apply zorn_ext
  · rfl
  · funext i
    simp [zornConj]
  · funext i
    simp [zornConj]
  · rfl

theorem zornNorm_conj (X : Zorn) : zornNorm (zornConj X) = zornNorm X := by
  simp [zornNorm, zornConj, dot3]
  ring

/-- Conjugation satisfies the scalar-trace identity of a composition algebra. -/
theorem zornAdd_conj_eq_trace_smul (X : Zorn) :
    zornAdd X (zornConj X) = zornSmul (X.a + X.b) I_zorn := by
  apply zorn_ext
  all_goals simp [zornAdd, zornConj, zornSmul, I_zorn] <;> ring

/-- The Zorn quadratic identity `X² - tr(X)X + N(X)1 = 0`. -/
theorem zorn_quadratic_identity (X : Zorn) :
    zornAdd
        (zornSub (zornMul X X) (zornSmul (X.a + X.b) X))
        (zornSmul (zornNorm X) I_zorn) = zornZero := by
  apply zorn_ext
  · simp [zornMul, zornSub, zornAdd, zornSmul, zornNorm, I_zorn, zornZero,
      dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornMul, zornSub, zornAdd, zornSmul, zornNorm, I_zorn, zornZero,
        dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornMul, zornSub, zornAdd, zornSmul, zornNorm, I_zorn, zornZero,
        dot3, cross3] <;> ring
  · simp [zornMul, zornSub, zornAdd, zornSmul, zornNorm, I_zorn, zornZero,
      dot3, cross3]
    ring

theorem zornConj_add (X Y : Zorn) :
    zornConj (zornAdd X Y) = zornAdd (zornConj X) (zornConj Y) := by
  apply zorn_ext
  · rfl
  · funext i
    simp [zornConj, zornAdd]
    ring
  · funext i
    simp [zornConj, zornAdd]
    ring
  · rfl

/-- The split-Zorn norm is multiplicative. -/
theorem zornNorm_mul (X Y : Zorn) :
    zornNorm (zornMul X Y) = zornNorm X * zornNorm Y := by
  exact InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm_mul X Y

/-! ### Quadratic sandwiches and the composition cone

The sandwich is written with its parentheses explicitly.  No associativity
of the Zorn product is assumed here; the displayed expression is the
canonical quadratic map used below.
-/

def zornQuadraticSandwich (X Y : Zorn) : Zorn :=
  zornMul X (zornMul Y X)

def zornZeroCone (X : Zorn) : Prop := zornNorm X = 0

theorem zornNorm_quadraticSandwich (X Y : Zorn) :
    zornNorm (zornQuadraticSandwich X Y) =
      zornNorm X ^ 2 * zornNorm Y := by
  unfold zornQuadraticSandwich
  rw [zornNorm_mul, zornNorm_mul]
  ring

theorem zornQuadraticSandwich_mem_zeroCone_of_left
    (X Y : Zorn) (hX : zornZeroCone X) :
    zornZeroCone (zornQuadraticSandwich X Y) := by
  unfold zornZeroCone at hX ⊢
  rw [zornNorm_quadraticSandwich, hX]
  ring

theorem zornQuadraticSandwich_mem_zeroCone_of_right
    (X Y : Zorn) (hY : zornZeroCone Y) :
    zornZeroCone (zornQuadraticSandwich X Y) := by
  unfold zornZeroCone at hY ⊢
  rw [zornNorm_quadraticSandwich, hY]
  ring

theorem zornMul_mem_zeroCone_of_left
    (X Y : Zorn) (hX : zornZeroCone X) :
    zornZeroCone (zornMul X Y) := by
  unfold zornZeroCone at hX ⊢
  rw [zornNorm_mul, hX, zero_mul]

theorem zornMul_mem_zeroCone_of_right
    (X Y : Zorn) (hY : zornZeroCone Y) :
    zornZeroCone (zornMul X Y) := by
  unfold zornZeroCone at hY ⊢
  rw [zornNorm_mul, hY, mul_zero]

/-- Conjugation reverses the Zorn product. -/
theorem zornConj_mul (X Y : Zorn) :
    zornConj (zornMul X Y) = zornMul (zornConj Y) (zornConj X) := by
  apply zorn_ext
  · simp [zornConj, zornMul, dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, cross3] <;> ring
  · simp [zornConj, zornMul, dot3, cross3]
    ring

theorem zornConj_smul (c : ℂ) (X : Zorn) :
    zornConj (zornSmul c X) = zornSmul c (zornConj X) := by
  apply zorn_ext
  · rfl
  · funext i
    simp [zornConj, zornSmul]
  · funext i
    simp [zornConj, zornSmul]
  · rfl

theorem zornConj_mul_self (X : Zorn) :
    zornMul (zornConj X) X = zornSmul (zornNorm X) I_zorn := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, dot3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, cross3] <;> ring
  · simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, dot3]
    ring

theorem zornMul_conj_self (X : Zorn) :
    zornMul X (zornConj X) = zornSmul (zornNorm X) I_zorn := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, dot3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, cross3] <;> ring
  · simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, dot3]
    ring

/-- Left multiplication by `X`, followed by left multiplication by its
conjugate, is the norm scalar. -/
theorem zornConj_left_action (X Y : Zorn) :
    zornMul (zornConj X) (zornMul X Y) = zornSmul (zornNorm X) Y := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3] <;> ring
  · simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3]
    ring

/-- The opposite chiral composition has the same norm scalar. -/
theorem zorn_left_conj_action (X Y : Zorn) :
    zornMul X (zornMul (zornConj X) Y) = zornSmul (zornNorm X) Y := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3] <;> ring
  · simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3]
    ring

/-- Polar form associated with the Zorn composition norm. -/
def zornPolar (X Y : Zorn) : ℂ :=
  zornNorm (zornAdd X Y) - zornNorm X - zornNorm Y

/-- Polarized Clifford relation on the positive chiral carrier. -/
theorem zorn_polarized_conj_left_action (X Y S : Zorn) :
    zornAdd
      (zornMul (zornConj X) (zornMul Y S))
      (zornMul (zornConj Y) (zornMul X S)) =
        zornSmul (zornPolar X Y) S := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
      dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
        dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
        dot3, cross3] <;> ring
  · simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
      dot3, cross3]
    ring

/-- Polarized Clifford relation on the negative chiral carrier. -/
theorem zorn_polarized_left_conj_action (X Y S : Zorn) :
    zornAdd
      (zornMul X (zornMul (zornConj Y) S))
      (zornMul Y (zornMul (zornConj X) S)) =
        zornSmul (zornPolar X Y) S := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
      dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
        dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
        dot3, cross3] <;> ring
  · simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
      dot3, cross3]
    ring

/-- Linear trace of a Zorn matrix. -/
def zornTrace (X : Zorn) : ℂ := X.a + X.b

/-- The trace-zero (pure) subspace of the split Zorn carrier. -/
def zornPure (X : Zorn) : Prop := zornTrace X = 0

/-- A trace-preserving map preserves the pure (trace-zero) subspace. -/
theorem zornPure_map (f : Zorn → Zorn)
    (htrace : ∀ X, zornTrace (f X) = zornTrace X)
    {X : Zorn} (hX : zornPure X) :
    zornPure (f X) := by
  rw [zornPure, htrace, hX]

/-- Scalar projection onto the identity line.  The factor `1/2` normalizes
`zornTrace`, since the identity has trace `2`. -/
def zornScalarPart (X : Zorn) : Zorn :=
  zornSmul (zornTrace X / 2) I_zorn

/-- Trace-zero component of a Zorn element. -/
def zornPurePart (X : Zorn) : Zorn :=
  zornAdd (zornSmul (-(zornTrace X / 2)) I_zorn) X

@[simp] theorem zornPurePart_pure (X : Zorn) :
    zornPure (zornPurePart X) := by
  simp [zornPure, zornPurePart, zornTrace, zornAdd, zornSmul, I_zorn]
  ring

@[simp] theorem zornScalarPart_trace (X : Zorn) :
    zornTrace (zornScalarPart X) = zornTrace X := by
  simp [zornScalarPart, zornTrace, zornSmul, I_zorn]

/-- Every Zorn element is the sum of its scalar and pure components. -/
theorem zornScalarPart_add_purePart (X : Zorn) :
    zornAdd (zornScalarPart X) (zornPurePart X) = X := by
  apply zorn_ext
  · simp [zornScalarPart, zornPurePart, zornTrace, zornAdd, zornSmul, I_zorn]
  · funext i
    simp [zornScalarPart, zornPurePart, zornTrace, zornAdd, zornSmul, I_zorn]
  · funext i
    simp [zornScalarPart, zornPurePart, zornTrace, zornAdd, zornSmul, I_zorn]
  · simp [zornScalarPart, zornPurePart, zornTrace, zornAdd, zornSmul, I_zorn]

/-- The scalar part of a triple Zorn product is cyclic. -/
theorem zornTripleTrace_cyclic (X Y Z : Zorn) :
    zornTrace (zornMul (zornMul X Y) Z) =
      zornTrace (zornMul (zornMul Y Z) X) := by
  simp [zornTrace, zornMul, dot3, cross3]
  ring

/-- The unalternated six-term trace sum splits into the two cyclic orientations,
with multiplicity three for each orientation. -/
theorem zornSymmTripleTrace_sum (X Y Z : Zorn) :
    zornTrace (zornMul (zornMul X Y) Z) +
      zornTrace (zornMul (zornMul Y Z) X) +
      zornTrace (zornMul (zornMul Z X) Y) +
      zornTrace (zornMul (zornMul X Z) Y) +
      zornTrace (zornMul (zornMul Y X) Z) +
      zornTrace (zornMul (zornMul Z Y) X) =
        3 * zornTrace (zornMul (zornMul X Y) Z) +
          3 * zornTrace (zornMul (zornMul X Z) Y) := by
  have hYZX : zornTrace (zornMul (zornMul Y Z) X) =
      zornTrace (zornMul (zornMul X Y) Z) :=
    (zornTripleTrace_cyclic X Y Z).symm
  have hZXY : zornTrace (zornMul (zornMul Z X) Y) =
      zornTrace (zornMul (zornMul X Y) Z) := by
    calc
      zornTrace (zornMul (zornMul Z X) Y) =
          zornTrace (zornMul (zornMul Y Z) X) :=
        (zornTripleTrace_cyclic Y Z X).symm
      _ = zornTrace (zornMul (zornMul X Y) Z) := hYZX
  have hZYX : zornTrace (zornMul (zornMul Z Y) X) =
      zornTrace (zornMul (zornMul X Z) Y) :=
    (zornTripleTrace_cyclic X Z Y).symm
  have hYXZ : zornTrace (zornMul (zornMul Y X) Z) =
      zornTrace (zornMul (zornMul X Z) Y) := by
    calc
      zornTrace (zornMul (zornMul Y X) Z) =
          zornTrace (zornMul (zornMul Z Y) X) :=
        (zornTripleTrace_cyclic Z Y X).symm
      _ = zornTrace (zornMul (zornMul X Z) Y) := hZYX
  rw [hYZX, hZXY, hYXZ, hZYX]
  ring

/-- The split-octonion analogue of the MathOverflow six-term alternating trace form on pure octonions. -/
def zornAlternatingTripleTrace (X Y Z : Zorn) : ℂ :=
  zornTrace (zornMul (zornMul X Y) Z) +
    zornTrace (zornMul (zornMul Y Z) X) +
    zornTrace (zornMul (zornMul Z X) Y) -
    zornTrace (zornMul (zornMul X Z) Y) -
    zornTrace (zornMul (zornMul Y X) Z) -
    zornTrace (zornMul (zornMul Z Y) X)

/-- The six-term trace form is cyclic in the first three slots. -/
theorem zornAlternatingTripleTrace_cyclic (X Y Z : Zorn) :
    zornAlternatingTripleTrace X Y Z = zornAlternatingTripleTrace Y Z X := by
  unfold zornAlternatingTripleTrace
  rw [zornTripleTrace_cyclic X Y Z,
    zornTripleTrace_cyclic Y Z X,
    zornTripleTrace_cyclic Z X Y,
    zornTripleTrace_cyclic X Z Y,
    zornTripleTrace_cyclic Y X Z,
    zornTripleTrace_cyclic Z Y X]
  ring

/-- The six-term trace form is additive in its first slot. -/
theorem zornAlternatingTripleTrace_add_left (X Y Z W : Zorn) :
    zornAlternatingTripleTrace (zornAdd X Y) Z W =
      zornAlternatingTripleTrace X Z W + zornAlternatingTripleTrace Y Z W := by
  unfold zornAlternatingTripleTrace
  simp [zornTrace, zornAdd, zornMul, dot3, cross3]
  ring

/-- The six-term trace form is homogeneous in its first slot. -/
theorem zornAlternatingTripleTrace_smul_left (r : ℂ) (X Y Z : Zorn) :
    zornAlternatingTripleTrace (zornSmul r X) Y Z =
      r * zornAlternatingTripleTrace X Y Z := by
  unfold zornAlternatingTripleTrace
  simp [zornTrace, zornSmul, zornMul, dot3, cross3]
  ring

/-- Additivity in the remaining slots follows from cyclicity. -/
theorem zornAlternatingTripleTrace_add_mid (X Y Z W : Zorn) :
    zornAlternatingTripleTrace X (zornAdd Y Z) W =
      zornAlternatingTripleTrace X Y W + zornAlternatingTripleTrace X Z W := by
  calc
    zornAlternatingTripleTrace X (zornAdd Y Z) W =
        zornAlternatingTripleTrace (zornAdd Y Z) W X :=
      zornAlternatingTripleTrace_cyclic X (zornAdd Y Z) W
    _ = zornAlternatingTripleTrace Y W X + zornAlternatingTripleTrace Z W X :=
      zornAlternatingTripleTrace_add_left Y Z W X
    _ = zornAlternatingTripleTrace X Y W + zornAlternatingTripleTrace X Z W := by
      rw [zornAlternatingTripleTrace_cyclic Y W X,
        zornAlternatingTripleTrace_cyclic W X Y,
        zornAlternatingTripleTrace_cyclic Z W X,
        zornAlternatingTripleTrace_cyclic W X Z]

/-- Additivity in the remaining slots follows from cyclicity. -/
theorem zornAlternatingTripleTrace_add_right (X Y Z W : Zorn) :
    zornAlternatingTripleTrace X Y (zornAdd Z W) =
      zornAlternatingTripleTrace X Y Z + zornAlternatingTripleTrace X Y W := by
  calc
    zornAlternatingTripleTrace X Y (zornAdd Z W) =
        zornAlternatingTripleTrace Y (zornAdd Z W) X :=
      zornAlternatingTripleTrace_cyclic X Y (zornAdd Z W)
    _ = zornAlternatingTripleTrace Y Z X + zornAlternatingTripleTrace Y W X :=
      zornAlternatingTripleTrace_add_mid Y Z W X
    _ = zornAlternatingTripleTrace X Y Z + zornAlternatingTripleTrace X Y W := by
      rw [zornAlternatingTripleTrace_cyclic Y Z X,
        zornAlternatingTripleTrace_cyclic Z X Y,
        zornAlternatingTripleTrace_cyclic Y W X,
        zornAlternatingTripleTrace_cyclic W X Y]

/-- The six-term trace form is alternating in the first two slots. -/
theorem zornAlternatingTripleTrace_swap12 (X Y Z : Zorn) :
    zornAlternatingTripleTrace X Y Z = - zornAlternatingTripleTrace Y X Z := by
  unfold zornAlternatingTripleTrace
  rw [zornTripleTrace_cyclic X Y Z,
    zornTripleTrace_cyclic Y Z X,
    zornTripleTrace_cyclic Z X Y,
    zornTripleTrace_cyclic X Z Y,
    zornTripleTrace_cyclic Y X Z,
    zornTripleTrace_cyclic Z Y X]
  ring

/-- The six-term trace form is alternating in the last two slots. -/
theorem zornAlternatingTripleTrace_swap23 (X Y Z : Zorn) :
    zornAlternatingTripleTrace X Y Z = - zornAlternatingTripleTrace X Z Y := by
  calc
    zornAlternatingTripleTrace X Y Z = zornAlternatingTripleTrace Y Z X := by
      exact zornAlternatingTripleTrace_cyclic X Y Z
    _ = - zornAlternatingTripleTrace Z Y X := by
      exact zornAlternatingTripleTrace_swap12 Y Z X
    _ = - zornAlternatingTripleTrace Y X Z := by
      rw [zornAlternatingTripleTrace_cyclic Z Y X]
    _ = - zornAlternatingTripleTrace X Z Y := by
      rw [zornAlternatingTripleTrace_cyclic Y X Z]

/-- The six-term trace form is alternating in the first and third slots. -/
theorem zornAlternatingTripleTrace_swap13 (X Y Z : Zorn) :
    zornAlternatingTripleTrace X Y Z = - zornAlternatingTripleTrace Z Y X := by
  calc
    zornAlternatingTripleTrace X Y Z = zornAlternatingTripleTrace Y Z X := by
      exact zornAlternatingTripleTrace_cyclic X Y Z
    _ = - zornAlternatingTripleTrace Z Y X := by
      exact zornAlternatingTripleTrace_swap12 Y Z X

/-- The alternating form vanishes when its first two arguments coincide. -/
theorem zornAlternatingTripleTrace_self_left (X Z : Zorn) :
    zornAlternatingTripleTrace X X Z = 0 := by
  have h := zornAlternatingTripleTrace_swap12 X X Z
  linear_combination (1 / 2 : ℂ) * h

/-- The six-term trace form is insensitive to adding a scalar multiple of the identity
in the first slot, so it descends to the pure quotient. -/
theorem zornAlternatingTripleTrace_scalar_left (r : ℂ) (X Y Z : Zorn) :
    zornAlternatingTripleTrace (zornAdd (zornSmul r I_zorn) X) Y Z =
      zornAlternatingTripleTrace X Y Z := by
  unfold zornAlternatingTripleTrace
  simp [zornTrace, zornAdd, zornSmul, zornMul, dot3, cross3, I_zorn]
  ring

/-- Homogeneity in the remaining slots follows from cyclicity. -/
theorem zornAlternatingTripleTrace_smul_mid (r : ℂ) (X Y Z : Zorn) :
    zornAlternatingTripleTrace X (zornSmul r Y) Z =
      r * zornAlternatingTripleTrace X Y Z := by
  calc
    zornAlternatingTripleTrace X (zornSmul r Y) Z =
        zornAlternatingTripleTrace (zornSmul r Y) Z X :=
      zornAlternatingTripleTrace_cyclic X (zornSmul r Y) Z
    _ = r * zornAlternatingTripleTrace Y Z X :=
      zornAlternatingTripleTrace_smul_left r Y Z X
    _ = r * zornAlternatingTripleTrace X Y Z := by
      rw [zornAlternatingTripleTrace_cyclic Y Z X,
        zornAlternatingTripleTrace_cyclic Z X Y]

/-- Homogeneity in the remaining slots follows from cyclicity. -/
theorem zornAlternatingTripleTrace_smul_right (r : ℂ) (X Y Z : Zorn) :
    zornAlternatingTripleTrace X Y (zornSmul r Z) =
      r * zornAlternatingTripleTrace X Y Z := by
  calc
    zornAlternatingTripleTrace X Y (zornSmul r Z) =
        zornAlternatingTripleTrace Y (zornSmul r Z) X :=
      zornAlternatingTripleTrace_cyclic X Y (zornSmul r Z)
    _ = r * zornAlternatingTripleTrace Y Z X :=
      zornAlternatingTripleTrace_smul_mid r Y Z X
    _ = r * zornAlternatingTripleTrace X Y Z := by
      rw [zornAlternatingTripleTrace_cyclic Y Z X,
        zornAlternatingTripleTrace_cyclic Z X Y]

/-- Scalar shifts by the identity do not affect the three-slot trace form in the
middle slot. -/
theorem zornAlternatingTripleTrace_scalar_mid (r : ℂ) (X Y Z : Zorn) :
    zornAlternatingTripleTrace X (zornAdd (zornSmul r I_zorn) Y) Z =
      zornAlternatingTripleTrace X Y Z := by
  calc
    zornAlternatingTripleTrace X (zornAdd (zornSmul r I_zorn) Y) Z =
      - zornAlternatingTripleTrace (zornAdd (zornSmul r I_zorn) Y) X Z := by
        exact zornAlternatingTripleTrace_swap12 X (zornAdd (zornSmul r I_zorn) Y) Z
    _ = - zornAlternatingTripleTrace Y X Z := by
        rw [zornAlternatingTripleTrace_scalar_left r Y X Z]
    _ = zornAlternatingTripleTrace X Y Z := by
        exact (zornAlternatingTripleTrace_swap12 X Y Z).symm

/-- Scalar shifts by the identity do not affect the three-slot trace form in the
rightmost slot. -/
theorem zornAlternatingTripleTrace_scalar_right (r : ℂ) (X Y Z : Zorn) :
    zornAlternatingTripleTrace X Y (zornAdd (zornSmul r I_zorn) Z) =
      zornAlternatingTripleTrace X Y Z := by
  calc
    zornAlternatingTripleTrace X Y (zornAdd (zornSmul r I_zorn) Z) =
      zornAlternatingTripleTrace Y (zornAdd (zornSmul r I_zorn) Z) X := by
        exact zornAlternatingTripleTrace_cyclic X Y (zornAdd (zornSmul r I_zorn) Z)
    _ = - zornAlternatingTripleTrace (zornAdd (zornSmul r I_zorn) Z) Y X := by
        exact zornAlternatingTripleTrace_swap12 Y (zornAdd (zornSmul r I_zorn) Z) X
    _ = - zornAlternatingTripleTrace Z Y X := by
        rw [zornAlternatingTripleTrace_scalar_left r Z Y X]
    _ = zornAlternatingTripleTrace X Y Z := by
        rw [zornAlternatingTripleTrace_cyclic Z Y X, zornAlternatingTripleTrace_swap12 X Y Z]

/-- Any multiplication-preserving, trace-preserving map preserves the
six-term octonionic three-form.  In particular, this is the exact hypothesis
needed to obtain the usual `G₂`/`G₂(2)` invariance statement; no unsupported
identification of a coordinate permutation with an automorphism is made here. -/
theorem zornAlternatingTripleTrace_map
    (f : Zorn → Zorn)
    (hmul : ∀ X Y, f (zornMul X Y) = zornMul (f X) (f Y))
    (htrace : ∀ X, zornTrace (f X) = zornTrace X)
    (X Y Z : Zorn) :
    zornAlternatingTripleTrace (f X) (f Y) (f Z) =
      zornAlternatingTripleTrace X Y Z := by
  have htriple (A B C : Zorn) :
      zornTrace (zornMul (zornMul (f A) (f B)) (f C)) =
        zornTrace (zornMul (zornMul A B) C) := by
    rw [← hmul A B, ← hmul (zornMul A B) C, htrace]
  unfold zornAlternatingTripleTrace
  rw [htriple X Y Z, htriple Y Z X, htriple Z X Y,
    htriple X Z Y, htriple Y X Z, htriple Z Y X]

/-! ## Three distinct eight-dimensional carriers -/

inductive TrialitySector where
  | vector
  | spinorPlus
  | spinorMinus
  deriving DecidableEq, Fintype, Repr

/-- A tagged copy of the canonical Zorn carrier. -/
@[ext] structure ZornCopy (sector : TrialitySector) where
  val : Zorn

abbrev Vector8 := ZornCopy .vector
abbrev SpinorPlus8 := ZornCopy .spinorPlus
abbrev SpinorMinus8 := ZornCopy .spinorMinus

/-- Inverse to the canonical eight-coordinate map. -/
def coordinatesToZorn (v : Fin 8 → ℂ) : Zorn where
  a := v 0
  u := ![v 1, v 2, v 3]
  v := ![v 4, v 5, v 6]
  b := v 7

theorem coordinatesToZorn_zornCoordinates (X : Zorn) :
    coordinatesToZorn (zornCoordinates X) = X := by
  apply zorn_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem zornCoordinates_coordinatesToZorn (v : Fin 8 → ℂ) :
    zornCoordinates (coordinatesToZorn v) = v := by
  funext i
  fin_cases i <;> rfl

/-- Every triality carrier has canonical coordinates in `ℂ⁸`. -/
def copyEquivCoordinates (sector : TrialitySector) :
    ZornCopy sector ≃ (Fin 8 → ℂ) where
  toFun X := zornCoordinates X.val
  invFun v := ⟨coordinatesToZorn v⟩
  left_inv X := by
    ext
    exact coordinatesToZorn_zornCoordinates X.val
  right_inv := zornCoordinates_coordinatesToZorn

instance (sector : TrialitySector) : AddCommGroup (ZornCopy sector) :=
  (copyEquivCoordinates sector).addCommGroup

instance (sector : TrialitySector) : Module ℂ (ZornCopy sector) :=
  (copyEquivCoordinates sector).module ℂ

/-- The transported linear coordinate equivalence. -/
def copyLinearEquivCoordinates (sector : TrialitySector) :
    ZornCopy sector ≃ₗ[ℂ] (Fin 8 → ℂ) where
  toFun := copyEquivCoordinates sector
  invFun := (copyEquivCoordinates sector).symm
  left_inv := (copyEquivCoordinates sector).left_inv
  right_inv := (copyEquivCoordinates sector).right_inv
  map_add' X Y := by
    change zornCoordinates
      (coordinatesToZorn (zornCoordinates X.val + zornCoordinates Y.val)) =
        zornCoordinates X.val + zornCoordinates Y.val
    exact zornCoordinates_coordinatesToZorn _
  map_smul' c X := by
    change zornCoordinates
      (coordinatesToZorn (c • zornCoordinates X.val)) =
        c • zornCoordinates X.val
    exact zornCoordinates_coordinatesToZorn _

/-- Addition on a tagged copy agrees with the explicit Zorn addition. -/
theorem zornCopy_add_val (sector : TrialitySector) (X Y : ZornCopy sector) :
    (X + Y).val = zornAdd X.val Y.val := by
  apply zornCoordinates_injective
  have h := (copyLinearEquivCoordinates sector).map_add X Y
  simpa [copyLinearEquivCoordinates, copyEquivCoordinates, zornCoordinates,
    zornAdd] using h

/-- Scalar multiplication on a tagged copy is transported through the
canonical coordinate equivalence. -/
theorem zornCopy_smul_val (sector : TrialitySector) (c : ℂ) (X : ZornCopy sector) :
    (c • X).val = coordinatesToZorn (c • zornCoordinates X.val) := by
  apply zornCoordinates_injective
  have h := (copyLinearEquivCoordinates sector).map_smul c X
  change zornCoordinates ((c • X).val) = c • zornCoordinates X.val at h
  rw [zornCoordinates_coordinatesToZorn]
  exact h

/-- Each typed triality copy is finite-dimensional because its coordinate
equivalence has the finite function space `Fin 8 → ℂ` as source. -/
noncomputable instance copyModuleFinite (sector : TrialitySector) :
    Module.Finite ℂ (ZornCopy sector) :=
  Module.Finite.equiv (copyLinearEquivCoordinates sector).symm

theorem copy_finrank_eight (sector : TrialitySector) :
    Module.finrank ℂ (ZornCopy sector) = 8 := by
  rw [(copyLinearEquivCoordinates sector).finrank_eq]
  exact Module.finrank_fin_fun ℂ

/-! ## Typed triality cycle and Clifford actions -/

def vectorToSpinorPlus : Vector8 ≃ₗ[ℂ] SpinorPlus8 :=
  (copyLinearEquivCoordinates .vector).trans
    (copyLinearEquivCoordinates .spinorPlus).symm

def spinorPlusToSpinorMinus : SpinorPlus8 ≃ₗ[ℂ] SpinorMinus8 :=
  (copyLinearEquivCoordinates .spinorPlus).trans
    (copyLinearEquivCoordinates .spinorMinus).symm

def spinorMinusToVector : SpinorMinus8 ≃ₗ[ℂ] Vector8 :=
  (copyLinearEquivCoordinates .spinorMinus).trans
    (copyLinearEquivCoordinates .vector).symm

theorem typed_triality_order_three (X : Vector8) :
    spinorMinusToVector
        (spinorPlusToSpinorMinus (vectorToSpinorPlus X)) = X := by
  ext
  exact coordinatesToZorn_zornCoordinates X.val

def vectorNorm (X : Vector8) : ℂ := zornNorm X.val
def spinorPlusNorm (S : SpinorPlus8) : ℂ := zornNorm S.val
def spinorMinusNorm (S : SpinorMinus8) : ℂ := zornNorm S.val

theorem vectorToSpinorPlus_norm (X : Vector8) :
    spinorPlusNorm (vectorToSpinorPlus X) = vectorNorm X := by
  change zornNorm (coordinatesToZorn (zornCoordinates X.val)) = zornNorm X.val
  rw [coordinatesToZorn_zornCoordinates]

theorem spinorPlusToSpinorMinus_norm (S : SpinorPlus8) :
    spinorMinusNorm (spinorPlusToSpinorMinus S) = spinorPlusNorm S := by
  change zornNorm (coordinatesToZorn (zornCoordinates S.val)) = zornNorm S.val
  rw [coordinatesToZorn_zornCoordinates]

theorem spinorMinusToVector_norm (S : SpinorMinus8) :
    vectorNorm (spinorMinusToVector S) = spinorMinusNorm S := by
  change zornNorm (coordinatesToZorn (zornCoordinates S.val)) = zornNorm S.val
  rw [coordinatesToZorn_zornCoordinates]

/-- Vector action from the positive to the negative semispinor carrier. -/
def cliffordPlus (X : Vector8) (S : SpinorPlus8) : SpinorMinus8 :=
  ⟨zornMul X.val S.val⟩

/-- Conjugate vector action from the negative to the positive semispinor carrier. -/
def cliffordMinus (X : Vector8) (S : SpinorMinus8) : SpinorPlus8 :=
  ⟨zornMul (zornConj X.val) S.val⟩

theorem cliffordMinus_plus (X : Vector8) (S : SpinorPlus8) :
    (cliffordMinus X (cliffordPlus X S)).val =
      zornSmul (vectorNorm X) S.val := by
  exact zornConj_left_action X.val S.val

theorem cliffordPlus_minus (X : Vector8) (S : SpinorMinus8) :
    (cliffordPlus X (cliffordMinus X S)).val =
      zornSmul (vectorNorm X) S.val := by
  exact zorn_left_conj_action X.val S.val

theorem clifford_polarized_plus (X Y : Vector8) (S : SpinorPlus8) :
    zornAdd
      (cliffordMinus X (cliffordPlus Y S)).val
      (cliffordMinus Y (cliffordPlus X S)).val =
        zornSmul (zornPolar X.val Y.val) S.val := by
  exact zorn_polarized_conj_left_action X.val Y.val S.val

theorem clifford_polarized_minus (X Y : Vector8) (S : SpinorMinus8) :
    zornAdd
      (cliffordPlus X (cliffordMinus Y S)).val
      (cliffordPlus Y (cliffordMinus X S)).val =
        zornSmul (zornPolar X.val Y.val) S.val := by
  exact zorn_polarized_left_conj_action X.val Y.val S.val

/-- Cartan's composition-algebra trilinear form on the three typed carriers. -/
def trialityForm (V : Vector8) (S : SpinorPlus8) (C : SpinorMinus8) : ℂ :=
  zornTrace (zornMul (zornMul V.val S.val) C.val)

/-- The typed triality cycle preserves the canonical trilinear form. -/
theorem trialityForm_cyclic (V : Vector8) (S : SpinorPlus8)
    (C : SpinorMinus8) :
    trialityForm V S C =
      trialityForm (spinorMinusToVector C)
        (vectorToSpinorPlus V) (spinorPlusToSpinorMinus S) := by
  change zornTrace (zornMul (zornMul V.val S.val) C.val) =
    zornTrace
      (zornMul
        (zornMul (coordinatesToZorn (zornCoordinates C.val))
          (coordinatesToZorn (zornCoordinates V.val)))
        (coordinatesToZorn (zornCoordinates S.val)))
  rw [coordinatesToZorn_zornCoordinates,
    coordinatesToZorn_zornCoordinates,
    coordinatesToZorn_zornCoordinates]
  exact (zornTripleTrace_cyclic C.val V.val S.val).symm

/-- The three typed eight-dimensional carriers and their two chiral Clifford
relations are simultaneously available. -/
theorem canonical_composition_triality_closure
    (X : Vector8) (Splus : SpinorPlus8) (Sminus : SpinorMinus8) :
    Module.finrank ℂ Vector8 = 8 ∧
    Module.finrank ℂ SpinorPlus8 = 8 ∧
    Module.finrank ℂ SpinorMinus8 = 8 ∧
    (cliffordMinus X (cliffordPlus X Splus)).val =
      zornSmul (vectorNorm X) Splus.val ∧
    (cliffordPlus X (cliffordMinus X Sminus)).val =
      zornSmul (vectorNorm X) Sminus.val ∧
    trialityForm X Splus Sminus =
      trialityForm (spinorMinusToVector Sminus)
        (vectorToSpinorPlus X) (spinorPlusToSpinorMinus Splus) := by
  exact ⟨copy_finrank_eight _, copy_finrank_eight _, copy_finrank_eight _,
    cliffordMinus_plus X Splus, cliffordPlus_minus X Sminus,
    trialityForm_cyclic X Splus Sminus⟩


end CanonicalZornCompositionTriality

end noncomputable section
