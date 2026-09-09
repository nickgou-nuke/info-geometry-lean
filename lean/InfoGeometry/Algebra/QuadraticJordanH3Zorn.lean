import Mathlib.Tactic
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.ZornAlternativeLaws

/-!
# H₃(𝕆_s) cubic-data carrier

This file records the additive carrier and the standard cubic-data formulas for
the split-Albert route. It does **not** yet claim the global Jordan identity or
construct the derivation algebra.

The truthful Jordan-algebra and derivation bridge lives elsewhere in the repo
and must be transported from a proven owner surface before it can be reused
here.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Algebra

variable (R : Type*) [CommRing R]

/-- The coordinate carrier for H₃(𝕆_s) over an arbitrary commutative ring R.
It has the coordinate shape of a 3x3 Hermitian matrix over split octonions:
  [ α₁   a   c* ]
  [ a*   α₂  b  ]
  [ c    b*  α₃ ]
-/
structure H3Zorn where
  α₁ : R
  α₂ : R
  α₃ : R
  a : ZornVectorMatrix R
  b : ZornVectorMatrix R
  c : ZornVectorMatrix R

namespace H3Zorn

variable {R : Type*} [CommRing R]

@[ext]
lemma ext_h3 (X Y : H3Zorn R)
    (h1 : X.α₁ = Y.α₁) (h2 : X.α₂ = Y.α₂) (h3 : X.α₃ = Y.α₃)
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hc : X.c = Y.c) : X = Y := by
  cases X; cases Y; congr

noncomputable instance : Add (H3Zorn R) where
  add X Y := ⟨X.α₁ + Y.α₁, X.α₂ + Y.α₂, X.α₃ + Y.α₃,
              ZornVectorMatrix.add X.a Y.a,
              ZornVectorMatrix.add X.b Y.b,
              ZornVectorMatrix.add X.c Y.c⟩

noncomputable instance : Neg (H3Zorn R) where
  neg X := ⟨-X.α₁, -X.α₂, -X.α₃,
            ZornVectorMatrix.neg X.a,
            ZornVectorMatrix.neg X.b,
            ZornVectorMatrix.neg X.c⟩

noncomputable instance : Zero (H3Zorn R) where
  zero := ⟨0, 0, 0,
           ZornVectorMatrix.zero,
           ZornVectorMatrix.zero,
           ZornVectorMatrix.zero⟩

noncomputable instance : Sub (H3Zorn R) where
  sub X Y := X + (-Y)

noncomputable instance : SMul R (H3Zorn R) where
  smul r X := ⟨r * X.α₁, r * X.α₂, r * X.α₃,
               ZornVectorMatrix.smul r X.a,
               ZornVectorMatrix.smul r X.b,
               ZornVectorMatrix.smul r X.c⟩

noncomputable instance : AddCommGroup (H3Zorn R) where
  add_assoc X Y Z := by
    apply ext_h3
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
    · exact ZornVectorMatrix.add_assoc _ _ _
    · exact ZornVectorMatrix.add_assoc _ _ _
    · exact ZornVectorMatrix.add_assoc _ _ _
  zero_add X := by
    apply ext_h3
    · exact zero_add _
    · exact zero_add _
    · exact zero_add _
    · exact ZornVectorMatrix.zero_add _
    · exact ZornVectorMatrix.zero_add _
    · exact ZornVectorMatrix.zero_add _
  add_zero X := by
    apply ext_h3
    · exact add_zero _
    · exact add_zero _
    · exact add_zero _
    · exact ZornVectorMatrix.add_zero _
    · exact ZornVectorMatrix.add_zero _
    · exact ZornVectorMatrix.add_zero _
  nsmul := nsmulRec
  neg_add_cancel X := by
    apply ext_h3
    · exact neg_add_cancel _
    · exact neg_add_cancel _
    · exact neg_add_cancel _
    · exact ZornVectorMatrix.add_left_neg _
    · exact ZornVectorMatrix.add_left_neg _
    · exact ZornVectorMatrix.add_left_neg _
  zsmul := zsmulRec
  add_comm X Y := by
    apply ext_h3
    · exact add_comm _ _
    · exact add_comm _ _
    · exact add_comm _ _
    · exact ZornVectorMatrix.add_comm _ _
    · exact ZornVectorMatrix.add_comm _ _
    · exact ZornVectorMatrix.add_comm _ _

noncomputable instance : Module R (H3Zorn R) where
  one_smul X := by
    apply ext_h3
    · exact one_mul _
    · exact one_mul _
    · exact one_mul _
    · exact ZornVectorMatrix.one_smul _
    · exact ZornVectorMatrix.one_smul _
    · exact ZornVectorMatrix.one_smul _
  mul_smul r s X := by
    apply ext_h3
    · exact mul_assoc _ _ _
    · exact mul_assoc _ _ _
    · exact mul_assoc _ _ _
    · ext i <;> exact mul_assoc _ _ _
    · ext i <;> exact mul_assoc _ _ _
    · ext i <;> exact mul_assoc _ _ _
  smul_zero r := by
    apply ext_h3
    · exact mul_zero _
    · exact mul_zero _
    · exact mul_zero _
    · exact ZornVectorMatrix.smul_zero _
    · exact ZornVectorMatrix.smul_zero _
    · exact ZornVectorMatrix.smul_zero _
  smul_add r X Y := by
    apply ext_h3
    · exact mul_add _ _ _
    · exact mul_add _ _ _
    · exact mul_add _ _ _
    · exact ZornVectorMatrix.smul_add _ _ _
    · exact ZornVectorMatrix.smul_add _ _ _
    · exact ZornVectorMatrix.smul_add _ _ _
  add_smul r s X := by
    apply ext_h3
    · exact add_mul _ _ _
    · exact add_mul _ _ _
    · exact add_mul _ _ _
    · exact ZornVectorMatrix.add_smul _ _ _
    · exact ZornVectorMatrix.add_smul _ _ _
    · exact ZornVectorMatrix.add_smul _ _ _
  zero_smul X := by
    apply ext_h3
    · exact zero_mul _
    · exact zero_mul _
    · exact zero_mul _
    · exact ZornVectorMatrix.zero_smul _
    · exact ZornVectorMatrix.zero_smul _
    · exact ZornVectorMatrix.zero_smul _

/-- The diagonal unit candidate for the split-Albert carrier. -/
noncomputable def one : H3Zorn R :=
  ⟨1, 1, 1, ZornVectorMatrix.zero, ZornVectorMatrix.zero, ZornVectorMatrix.zero⟩

noncomputable instance : One (H3Zorn R) := ⟨one⟩

/-- Coordinate readback for addition on the H3 carrier. -/
theorem add_readback (X Y : H3Zorn R) : X + Y =
    ⟨X.α₁ + Y.α₁, X.α₂ + Y.α₂, X.α₃ + Y.α₃,
      ZornVectorMatrix.add X.a Y.a, ZornVectorMatrix.add X.b Y.b,
      ZornVectorMatrix.add X.c Y.c⟩ := rfl

/-- Coordinate readback for negation on the H3 carrier. -/
theorem neg_readback (X : H3Zorn R) : -X =
    ⟨-X.α₁, -X.α₂, -X.α₃, ZornVectorMatrix.neg X.a,
      ZornVectorMatrix.neg X.b, ZornVectorMatrix.neg X.c⟩ := rfl

/-- Coordinate readback for subtraction on the H3 carrier. -/
theorem sub_readback (X Y : H3Zorn R) : X - Y =
    ⟨X.α₁ - Y.α₁, X.α₂ - Y.α₂, X.α₃ - Y.α₃,
      ZornVectorMatrix.sub X.a Y.a, ZornVectorMatrix.sub X.b Y.b,
      ZornVectorMatrix.sub X.c Y.c⟩ := by
  simp [sub_eq_add_neg, add_readback, neg_readback, ZornVectorMatrix.sub]

/-- Coordinate readback for scalar multiplication on the H3 carrier. -/
theorem smul_readback (r : R) (X : H3Zorn R) : r • X =
    ⟨r * X.α₁, r * X.α₂, r * X.α₃, ZornVectorMatrix.smul r X.a,
      ZornVectorMatrix.smul r X.b, ZornVectorMatrix.smul r X.c⟩ := rfl

/-- Coordinate readback for the diagonal H3 basepoint. -/
theorem one_readback : (1 : H3Zorn R) =
    ⟨1, 1, 1, ZornVectorMatrix.zero, ZornVectorMatrix.zero,
      ZornVectorMatrix.zero⟩ := rfl

/-- Coordinate readback for the additive zero on the H3 carrier. -/
@[simp] theorem zero_readback : (0 : H3Zorn R) =
    ⟨0, 0, 0, ZornVectorMatrix.zero, ZornVectorMatrix.zero,
      ZornVectorMatrix.zero⟩ := rfl

/-- Bilinear trace form on `H₃(𝕆_s)`.

For an off-diagonal coordinate the composition-algebra pairing is
`tr(x * conjugate y)`.  Omitting the conjugation gives the wrong quadratic
form on split octonions.
-/
noncomputable def traceBilin (X Y : H3Zorn R) : R :=
  X.α₁ * Y.α₁ + X.α₂ * Y.α₂ + X.α₃ * Y.α₃ +
  ZornVectorMatrix.trace (ZornVectorMatrix.mul X.a (ZornVectorMatrix.conj Y.a)) +
  ZornVectorMatrix.trace (ZornVectorMatrix.mul X.b (ZornVectorMatrix.conj Y.b)) +
  ZornVectorMatrix.trace (ZornVectorMatrix.mul X.c (ZornVectorMatrix.conj Y.c))

/-- Linear matrix trace of the Hermitian H3 coordinate carrier. -/
noncomputable def linearTrace (X : H3Zorn R) : R :=
  X.α₁ + X.α₂ + X.α₃

/-- Additivity of the linear H3 trace. -/
@[simp] theorem linearTrace_add (X Y : H3Zorn R) :
    linearTrace (X + Y) = linearTrace X + linearTrace Y := by
  rw [add_readback]
  simp [linearTrace]
  ring

/-- Homogeneity of the linear H3 trace. -/
@[simp] theorem linearTrace_smul (r : R) (X : H3Zorn R) :
    linearTrace (r • X) = r * linearTrace X := by
  rw [smul_readback r X]
  simp [linearTrace]
  ring

/-- Pairing with the diagonal unit recovers the linear matrix trace. -/
@[simp] theorem traceBilin_one (X : H3Zorn R) :
    traceBilin X 1 = linearTrace X := by
  change traceBilin X (H3Zorn.one : H3Zorn R) = linearTrace X
  simp [traceBilin, linearTrace, H3Zorn.one, ZornVectorMatrix.conj,
    ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVectorMatrix.trace,
    ZornVec3.dot, ZornVec3.cross]

/-- Pairing with the additive zero vanishes on the left. -/
@[simp] theorem traceBilin_zero_left (X : H3Zorn R) :
    traceBilin (0 : H3Zorn R) X = 0 := by
  simp [traceBilin, zero_readback, ZornVectorMatrix.zero_mul,
    ZornVectorMatrix.trace_zero]

/-- Pairing with the additive zero vanishes on the right. -/
@[simp] theorem traceBilin_zero_right (X : H3Zorn R) :
    traceBilin X (0 : H3Zorn R) = 0 := by
  simp [traceBilin, zero_readback, ZornVectorMatrix.mul_zero,
    ZornVectorMatrix.trace_zero]

/-- The standard cubic norm for the displayed Hermitian layout.

The triality term follows the oriented cycle `a : 1→2`, `b : 2→3`,
`c : 3→1`; its scalar value is `tr((a*b)*c)`.
-/
noncomputable def normCubic (X : H3Zorn R) : R :=
  X.α₁ * X.α₂ * X.α₃
    - X.α₁ * ZornVectorMatrix.norm X.b
    - X.α₂ * ZornVectorMatrix.norm X.c
    - X.α₃ * ZornVectorMatrix.norm X.a
    + ZornVectorMatrix.trace
        (ZornVectorMatrix.mul (ZornVectorMatrix.mul X.a X.b) X.c)

/-- The diagonal basepoint has cubic norm one. -/
@[simp] theorem normCubic_one : normCubic (1 : H3Zorn R) = 1 := by
  change normCubic (H3Zorn.one : H3Zorn R) = 1
  simp [normCubic, H3Zorn.one, ZornVectorMatrix.zero_mul,
    ZornVectorMatrix.trace_zero]

/-- The additive zero has cubic norm zero. -/
@[simp] theorem normCubic_zero : normCubic (0 : H3Zorn R) = 0 := by
  simp [normCubic, zero_readback, ZornVectorMatrix.mul_zero,
    ZornVectorMatrix.trace_zero]

/-- The quadratic adjoint `X#` for the displayed Hermitian layout.

The off-diagonal order and signs are fixed by
`X# = X² - Tr(X) X + S(X) 1`: for example the `(1,2)` coordinate is
`conj(c) * conj(b) - α₃ a`.
-/
noncomputable def adjointQuad (X : H3Zorn R) : H3Zorn R :=
  { α₁ := X.α₂ * X.α₃ - ZornVectorMatrix.norm X.b
    α₂ := X.α₁ * X.α₃ - ZornVectorMatrix.norm X.c
    α₃ := X.α₁ * X.α₂ - ZornVectorMatrix.norm X.a
    a := ZornVectorMatrix.sub
            (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.c) (ZornVectorMatrix.conj X.b))
            (ZornVectorMatrix.smul X.α₃ X.a)
    b := ZornVectorMatrix.sub
            (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.a) (ZornVectorMatrix.conj X.c))
            (ZornVectorMatrix.smul X.α₁ X.b)
    c := ZornVectorMatrix.sub
            (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.b) (ZornVectorMatrix.conj X.a))
            (ZornVectorMatrix.smul X.α₂ X.c) }

/-- The quadratic adjoint is homogeneous of degree two.  The proof keeps each
off-diagonal Zorn entry bundled and uses the composition-algebra operation
laws, rather than expanding vector coordinates. -/
theorem adjointQuad_smul (r : R) (X : H3Zorn R) :
    adjointQuad (r • X) = (r ^ 2) • adjointQuad X := by
  rw [smul_readback r X, smul_readback (r ^ 2) (adjointQuad X)]
  apply ext_h3
  · simp [adjointQuad, ZornVectorMatrix.norm_smul]
    ring
  · simp [adjointQuad, ZornVectorMatrix.norm_smul]
    ring
  · simp [adjointQuad, ZornVectorMatrix.norm_smul]
    ring
  · simp only [adjointQuad, ZornVectorMatrix.conj_smul,
      ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def]
    module
  · simp only [adjointQuad, ZornVectorMatrix.conj_smul,
      ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def]
    module
  · simp only [adjointQuad, ZornVectorMatrix.conj_smul,
      ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul]
    simp only [ZornVectorMatrix.sub_eq_add_neg,
      ← zvm_add_def, ← zvm_neg_def, ← zvm_smul_def]
    module

/-- The diagonal basepoint is fixed by the quadratic adjoint. -/
@[simp] theorem adjointQuad_one : adjointQuad (1 : H3Zorn R) = 1 := by
  change adjointQuad (H3Zorn.one : H3Zorn R) = H3Zorn.one
  apply ext_h3
  · simp [adjointQuad, H3Zorn.one]
  · simp [adjointQuad, H3Zorn.one]
  · simp [adjointQuad, H3Zorn.one]
  · ext i <;>
      simp [adjointQuad, H3Zorn.one, ZornVectorMatrix.sub,
        ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.zero,
        ZornVec3.dot, ZornVec3.cross]
  · ext i <;>
      simp [adjointQuad, H3Zorn.one, ZornVectorMatrix.sub,
        ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.zero,
        ZornVec3.dot, ZornVec3.cross]
  · ext i <;>
      simp [adjointQuad, H3Zorn.one, ZornVectorMatrix.sub,
        ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.smul,
        ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.zero,
        ZornVec3.dot, ZornVec3.cross]

/-- The split-isotropic Zorn idempotent is null for the conjugated H3 trace
pairing.  This distinguishes the composition pairing `tr(a * conj a)` from
the incorrect unconjugated expression `tr(a * a)`.
-/
@[simp] theorem traceBilin_upper_isotropic_self :
    let X : H3Zorn ℝ :=
      { α₁ := 0, α₂ := 0, α₃ := 0
        a := ZornVectorMatrix.E11
        b := ZornVectorMatrix.zero
        c := ZornVectorMatrix.zero }
    traceBilin X X = 0 := by
  norm_num [traceBilin, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
    ZornVectorMatrix.conj, ZornVectorMatrix.E11, ZornVectorMatrix.zero,
    ZornVec3.dot]

/-- Conjugation negates every pure upper Zorn generator. -/
@[simp] theorem conj_U_eq_neg (i : Fin 3) :
    ZornVectorMatrix.conj (ZornVectorMatrix.U i : ZornVectorMatrix ℝ) =
      ZornVectorMatrix.neg (ZornVectorMatrix.U i) := by
  ext j <;>
    simp [ZornVectorMatrix.conj, ZornVectorMatrix.U, ZornVectorMatrix.neg]

/-- A cyclic pair of upper isotropic Zorn entries produces the opposite
idempotent in the first off-diagonal adjoint block.  This checks the
conjugations and the subtraction sign in the quadratic adjoint; because the
two entries coincide, it does not by itself distinguish the factor order.
-/
@[simp] theorem adjointQuad_cyclic_isotropic_a :
    let X : H3Zorn ℝ :=
      { α₁ := 0, α₂ := 0, α₃ := 0
        a := ZornVectorMatrix.zero
        b := ZornVectorMatrix.E11
        c := ZornVectorMatrix.E11 }
    (adjointQuad X).a = ZornVectorMatrix.E22 := by
  ext i <;>
    simp [adjointQuad, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.E11, ZornVectorMatrix.E22,
      ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]

/-- Distinct cyclic upper generators detect the noncommutative factor order in
the first off-diagonal adjoint block:
`conj(U 0) * conj(U 1) = V 2`, whereas reversing the factors gives `-V 2`.
-/
@[simp] theorem adjointQuad_cyclic_order_a :
    let X : H3Zorn ℝ :=
      { α₁ := 0, α₂ := 0, α₃ := 0
        a := ZornVectorMatrix.zero
        b := ZornVectorMatrix.U 1
        c := ZornVectorMatrix.U 0 }
    (adjointQuad X).a = ZornVectorMatrix.V 2 := by
  simp only [adjointQuad]
  rw [conj_U_eq_neg, conj_U_eq_neg, ZornVectorMatrix.neg_mul,
    ZornVectorMatrix.mul_neg]
  ext i <;>
    simp [ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]

/-- The cross product X × Y (polarization of the adjoint). -/
noncomputable def crossProduct (X Y : H3Zorn R) : H3Zorn R :=
  adjointQuad (X + Y) - adjointQuad X - adjointQuad Y

/-- The first off-diagonal block of the adjoint polarization against the
basepoint is the additive inverse of the original block. -/
theorem crossProduct_one_a (X : H3Zorn R) :
    (crossProduct X 1).a = ZornVectorMatrix.neg X.a := by
  simp only [crossProduct, sub_readback, adjointQuad, add_readback, one_readback]
  simp only [ZornVectorMatrix.add_zero, ZornVectorMatrix.conj_zero,
    ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]
  ext i <;>
    simp [ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul] <;> ring

/-- The second off-diagonal block of the adjoint polarization against the
basepoint is the additive inverse of the original block. -/
theorem crossProduct_one_b (X : H3Zorn R) :
    (crossProduct X 1).b = ZornVectorMatrix.neg X.b := by
  simp only [crossProduct, sub_readback, adjointQuad, add_readback, one_readback]
  simp only [ZornVectorMatrix.add_zero, ZornVectorMatrix.conj_zero,
    ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]
  ext i <;>
    simp [ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul] <;> ring

/-- The third off-diagonal block of the adjoint polarization against the
basepoint is the additive inverse of the original block. -/
theorem crossProduct_one_c (X : H3Zorn R) :
    (crossProduct X 1).c = ZornVectorMatrix.neg X.c := by
  simp only [crossProduct, sub_readback, adjointQuad, add_readback, one_readback]
  simp only [ZornVectorMatrix.add_zero, ZornVectorMatrix.conj_zero,
    ZornVectorMatrix.zero_mul, ZornVectorMatrix.smul_zero]
  ext i <;>
    simp [ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul] <;> ring

/-- Polarizing the quadratic adjoint against the diagonal basepoint gives the
standard trace complement `X × 1 = Tr(X) 1 - X` of a cubic Jordan algebra. -/
@[simp] theorem crossProduct_one (X : H3Zorn R) :
    crossProduct X 1 = linearTrace X • (1 : H3Zorn R) - X := by
  apply ext_h3
  · simp [crossProduct, adjointQuad, linearTrace, add_readback, sub_readback,
      smul_readback, one_readback, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVec3.dot]
    ring
  · simp [crossProduct, adjointQuad, linearTrace, add_readback, sub_readback,
      smul_readback, one_readback, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVec3.dot]
    ring
  · simp [crossProduct, adjointQuad, linearTrace, add_readback, sub_readback,
      smul_readback, one_readback, ZornVectorMatrix.norm,
      ZornVectorMatrix.add, ZornVectorMatrix.zero, ZornVec3.dot]
    ring
  · rw [crossProduct_one_a]
    ext i <;> simp [linearTrace, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · rw [crossProduct_one_b]
    ext i <;> simp [linearTrace, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  · rw [crossProduct_one_c]
    ext i <;> simp [linearTrace, sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, ZornVectorMatrix.zero]

/-- Self-polarization of the quadratic adjoint. With
`X × Y = (X + Y)# - X# - Y#`, quadratic homogeneity gives
`X × X = 2 X#`. -/
@[simp] theorem crossProduct_self (X : H3Zorn R) :
    crossProduct X X = (2 : R) • adjointQuad X := by
  rw [crossProduct, show X + X = (2 : R) • X by module,
    adjointQuad_smul]
  module

/-- The quadratic U-operator: U_X(Y).
For cubic Jordan algebras, this is exactly T(X,Y)X - X# × Y. -/
noncomputable def U (X Y : H3Zorn R) : H3Zorn R :=
  traceBilin X Y • X - crossProduct (adjointQuad X) Y

/-- The triple product {X, Y, Z} = T(X, Y, Z) = U_{X,Z}(Y). -/
noncomputable def T (X Y Z : H3Zorn R) : H3Zorn R :=
  U (X + Z) Y - U X Y - U Z Y

/-!
The remaining Jordan-product and derivation-closure claims are intentionally
not asserted here.  The current file only records the candidate cubic data for
the split-Albert route.
-/

end H3Zorn

end InfoGeometry.Algebra
