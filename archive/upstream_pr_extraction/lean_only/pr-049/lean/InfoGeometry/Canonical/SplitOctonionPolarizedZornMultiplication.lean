import InfoGeometry.Canonical.SplitOctonionThreeColorChiralRelations
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra
open SplitOctonionColour

/-!
Explicit Zorn multiplication in the polarized basis

`alpha`, `beta`, `x`, and `y` are the coefficients of
`nPlus`, `nMinus`, `sigmaPlus`, and `sigmaMinus`.  The carrier deliberately
has only a multiplication operation; the ambient product is nonassociative.
-/

structure PolarizedZorn where
  alpha : ℚ
  beta : ℚ
  x : Fin 3 → ℚ
  y : Fin 3 → ℚ

def colourIndex : Fin 3 → SplitOctonionColour
  | 0 => .red
  | 1 => .green
  | 2 => .blue

def polarizedMul (X Y : PolarizedZorn) : PolarizedZorn where
  alpha := X.alpha * Y.alpha + ZornVec3.dot X.x Y.y
  beta := ZornVec3.dot X.y Y.x + X.beta * Y.beta
  x := fun i =>
    X.alpha * Y.x i + Y.beta * X.x i - ZornVec3.cross X.y Y.y i
  y := fun i =>
    Y.alpha * X.y i + X.beta * Y.y i + ZornVec3.cross X.x Y.x i

instance : Mul PolarizedZorn := ⟨polarizedMul⟩

/-- The eight coordinate generators in polarized Peirce--Witt order:
`n₊, n₋, σᵢ₊, σⱼ₊, σₖ₊, σᵢ₋, σⱼ₋, σₖ₋`. -/
def polarizedGenerator : Fin 8 → PolarizedZorn
  | 0 => { alpha := 1, beta := 0, x := 0, y := 0 }
  | 1 => { alpha := 0, beta := 1, x := 0, y := 0 }
  | 2 => { alpha := 0, beta := 0, x := (fun i => if i = 0 then 1 else 0), y := 0 }
  | 3 => { alpha := 0, beta := 0, x := (fun i => if i = 1 then 1 else 0), y := 0 }
  | 4 => { alpha := 0, beta := 0, x := (fun i => if i = 2 then 1 else 0), y := 0 }
  | 5 => { alpha := 0, beta := 0, x := 0, y := (fun i => if i = 0 then 1 else 0) }
  | 6 => { alpha := 0, beta := 0, x := 0, y := (fun i => if i = 1 then 1 else 0) }
  | 7 => { alpha := 0, beta := 0, x := 0, y := (fun i => if i = 2 then 1 else 0) }

def polarizedOne : PolarizedZorn where
  alpha := 1
  beta := 1
  x := 0
  y := 0

abbrev polarizedNPlus : PolarizedZorn := polarizedGenerator 0
abbrev polarizedNMinus : PolarizedZorn := polarizedGenerator 1
abbrev polarizedSigmaRedPlus : PolarizedZorn := polarizedGenerator 2
abbrev polarizedSigmaGreenPlus : PolarizedZorn := polarizedGenerator 3
abbrev polarizedSigmaBluePlus : PolarizedZorn := polarizedGenerator 4
abbrev polarizedSigmaRedMinus : PolarizedZorn := polarizedGenerator 5
abbrev polarizedSigmaGreenMinus : PolarizedZorn := polarizedGenerator 6
abbrev polarizedSigmaBlueMinus : PolarizedZorn := polarizedGenerator 7

/-- Peirce idempotent `n₊` in the polarized Zorn carrier. -/
abbrev polarizedZornNPlus : PolarizedZorn := polarizedNPlus

/-- Peirce idempotent `n₋` in the polarized Zorn carrier. -/
abbrev polarizedZornNMinus : PolarizedZorn := polarizedNMinus

/-- Positive chiral generator `σ_{c,+}` in the polarized Zorn carrier. -/
def polarizedZornSigmaPlus (c : SplitOctonionColour) : PolarizedZorn :=
  match c with
  | .red => polarizedSigmaRedPlus
  | .green => polarizedSigmaGreenPlus
  | .blue => polarizedSigmaBluePlus

/-- Negative chiral generator `σ_{c,-}` in the polarized Zorn carrier. -/
def polarizedZornSigmaMinus (c : SplitOctonionColour) : PolarizedZorn :=
  match c with
  | .red => polarizedSigmaRedMinus
  | .green => polarizedSigmaGreenMinus
  | .blue => polarizedSigmaBlueMinus

def toNative (X : PolarizedZorn) : StandardRationalSplitOctonion
  | .one => (X.alpha + X.beta) / 2
  | .l => (X.alpha - X.beta) / 2
  | .i => (-X.x 0 + X.y 0) / 2
  | .il => (X.x 0 + X.y 0) / 2
  | .j => (-X.x 1 + X.y 1) / 2
  | .jl => (X.x 1 + X.y 1) / 2
  | .k => (-X.x 2 + X.y 2) / 2
  | .kl => (X.x 2 + X.y 2) / 2

/-!
## Explicit soldering matrix

The columns are ordered as
`n₊, n₋, σᵢ₊, σⱼ₊, σₖ₊, σᵢ₋, σⱼ₋, σₖ₋`,
and the rows as
`1, ℓ, i, iℓ, j, jℓ, k, kℓ`.
-/

def chiralCoordinate : PolarizedZorn → Fin 8 → ℚ
  | X, 0 => X.alpha
  | X, 1 => X.beta
  | X, 2 => X.x 0
  | X, 3 => X.x 1
  | X, 4 => X.x 2
  | X, 5 => X.y 0
  | X, 6 => X.y 1
  | X, 7 => X.y 2

def chiralSolderingMatrix : Matrix (Fin 8) (Fin 8) ℚ := fun r =>
  match r with
  | 0 => ![1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0]
  | 1 => ![1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0]
  | 2 => ![0, 0, -1 / 2, 0, 0, 1 / 2, 0, 0]
  | 3 => ![0, 0, 1 / 2, 0, 0, 1 / 2, 0, 0]
  | 4 => ![0, 0, 0, -1 / 2, 0, 0, 1 / 2, 0]
  | 5 => ![0, 0, 0, 1 / 2, 0, 0, 1 / 2, 0]
  | 6 => ![0, 0, 0, 0, -1 / 2, 0, 0, 1 / 2]
  | 7 => ![0, 0, 0, 0, 1 / 2, 0, 0, 1 / 2]

def standardSolderingRow : IntegralSplitBasis → Fin 8
  | .one => 0
  | .l => 1
  | .i => 2
  | .il => 3
  | .j => 4
  | .jl => 5
  | .k => 6
  | .kl => 7

/-!
## The SageMath order

SageMath commonly displays the split-octonion coordinates in the order
`1, i, j, k, l, i*l, j*l, k*l`.  The native carrier uses the equivalent
coordinate type `IntegralSplitBasis`, whose declaration order is
`1, l, i, i*l, j, j*l, k, k*l`.  The following is only a reindexing of the
already existing coordinate basis; it does not introduce a second carrier or
change the multiplication.
-/

def sageBasisIndex : Fin 8 → IntegralSplitBasis
  | 0 => .one
  | 1 => .i
  | 2 => .j
  | 3 => .k
  | 4 => .l
  | 5 => .il
  | 6 => .jl
  | 7 => .kl

def sageBasisIndexEquiv : Fin 8 ≃ IntegralSplitBasis where
  toFun := sageBasisIndex
  invFun := fun b =>
    match b with
    | .one => 0
    | .i => 1
    | .j => 2
    | .k => 3
    | .l => 4
    | .il => 5
    | .jl => 6
    | .kl => 7
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

noncomputable def sageBasis : Module.Basis (Fin 8) ℚ StandardRationalSplitOctonion :=
  (Pi.basisFun ℚ IntegralSplitBasis).reindex sageBasisIndexEquiv.symm

@[simp] theorem sageBasis_apply (i : Fin 8) :
    sageBasis i = rationalBasis (sageBasisIndex i) := by
  rw [sageBasis, Module.Basis.reindex_apply]
  simp [sageBasisIndexEquiv, rationalBasis, sageBasisIndex]

@[simp] theorem sageBasis_zero : sageBasis 0 = rationalBasis .one := by
  rw [sageBasis_apply]
  rfl

@[simp] theorem sageBasis_one : sageBasis 1 = rationalBasis .i := by
  rw [sageBasis_apply]
  rfl

@[simp] theorem sageBasis_two : sageBasis 2 = rationalBasis .j := by
  rw [sageBasis_apply]
  rfl

@[simp] theorem sageBasis_three : sageBasis 3 = rationalBasis .k := by
  rw [sageBasis_apply]
  rfl

@[simp] theorem sageBasis_four : sageBasis 4 = rationalBasis .l := by
  rw [sageBasis_apply]
  rfl

@[simp] theorem sageBasis_five : sageBasis 5 = rationalBasis .il := by
  rw [sageBasis_apply]
  rfl

@[simp] theorem sageBasis_six : sageBasis 6 = rationalBasis .jl := by
  rw [sageBasis_apply]
  rfl

@[simp] theorem sageBasis_seven : sageBasis 7 = rationalBasis .kl := by
  rw [sageBasis_apply]
  rfl

/-!
The matrix below has rows in chiral order and columns in standard order.
It is the transpose of `chiralSolderingMatrix`; the signs follow the native
definitions `σ₊ = (ℓu - u)/2` and `σ₋ = (ℓu + u)/2`.
-/
def chiralBasisChangeMatrix : Matrix (Fin 8) (Fin 8) ℚ := fun r =>
  match r with
  | 0 => ![1 / 2, 1 / 2, 0, 0, 0, 0, 0, 0]
  | 1 => ![0, 0, -1 / 2, 1 / 2, 0, 0, 0, 0]
  | 2 => ![0, 0, 0, 0, -1 / 2, 1 / 2, 0, 0]
  | 3 => ![0, 0, 0, 0, 0, 0, -1 / 2, 1 / 2]
  | 4 => ![1 / 2, -1 / 2, 0, 0, 0, 0, 0, 0]
  | 5 => ![0, 0, 1 / 2, 1 / 2, 0, 0, 0, 0]
  | 6 => ![0, 0, 0, 0, 1 / 2, 1 / 2, 0, 0]
  | 7 => ![0, 0, 0, 0, 0, 0, 1 / 2, 1 / 2]

def chiralBasisChangeMatrixInv : Matrix (Fin 8) (Fin 8) ℚ := fun r =>
  match r with
  | 0 => ![1, 0, 0, 0, 1, 0, 0, 0]
  | 1 => ![1, 0, 0, 0, -1, 0, 0, 0]
  | 2 => ![0, -1, 0, 0, 0, 1, 0, 0]
  | 3 => ![0, 1, 0, 0, 0, 1, 0, 0]
  | 4 => ![0, 0, -1, 0, 0, 0, 1, 0]
  | 5 => ![0, 0, 1, 0, 0, 0, 1, 0]
  | 6 => ![0, 0, 0, -1, 0, 0, 0, 1]
  | 7 => ![0, 0, 0, 1, 0, 0, 0, 1]

theorem chiralBasisChangeMatrixInv_mul :
    chiralBasisChangeMatrixInv * chiralBasisChangeMatrix = 1 := by
  native_decide

theorem chiralBasisChangeMatrix_mul_Inv :
    chiralBasisChangeMatrix * chiralBasisChangeMatrixInv = 1 := by
  native_decide

@[simp] theorem toNative_eq_chiralSolderingMatrix_mul_coordinates
    (X : PolarizedZorn) (b : IntegralSplitBasis) :
    toNative X b =
      ∑ c : Fin 8, chiralSolderingMatrix (standardSolderingRow b) c *
        chiralCoordinate X c := by
  cases b <;>
    simp [toNative, chiralSolderingMatrix, chiralCoordinate,
      standardSolderingRow, Matrix.vecCons, Fin.cons_zero, Fin.cons_succ,
      Fin.sum_univ_succ] <;>
    ring

def fromNative (z : StandardRationalSplitOctonion) : PolarizedZorn where
  alpha := z .one + z .l
  beta := z .one - z .l
  x := fun i => match i with
    | 0 => z .il - z .i
    | 1 => z .jl - z .j
    | 2 => z .kl - z .k
  y := fun i => match i with
    | 0 => z .il + z .i
    | 1 => z .jl + z .j
    | 2 => z .kl + z .k

theorem polarizedZorn_ext {X Y : PolarizedZorn}
    (hα : X.alpha = Y.alpha) (hβ : X.beta = Y.beta)
    (hx : X.x = Y.x) (hy : X.y = Y.y) : X = Y := by
  cases X
  cases Y
  simp_all

@[simp] theorem fromNative_toNative (X : PolarizedZorn) :
    fromNative (toNative X) = X := by
  apply polarizedZorn_ext
  · cases X with | mk alpha beta x y => dsimp [fromNative, toNative]; ring
  · cases X with | mk alpha beta x y => dsimp [fromNative, toNative]; ring
  · cases X with | mk alpha beta x y =>
      funext i; fin_cases i <;> dsimp [fromNative, toNative] <;> ring
  · cases X with | mk alpha beta x y =>
      funext i; fin_cases i <;> dsimp [fromNative, toNative] <;> ring

@[simp] theorem toNative_fromNative (z : StandardRationalSplitOctonion) :
    toNative (fromNative z) = z := by
  funext b
  cases b <;> dsimp [fromNative, toNative] <;> ring

noncomputable def toNativeEquiv :
    PolarizedZorn ≃ StandardRationalSplitOctonion where
  toFun := toNative
  invFun := fromNative
  left_inv := fromNative_toNative
  right_inv := toNative_fromNative

@[simp] theorem toNative_polarizedOne :
    toNative polarizedOne = rationalBasis .one := by
  funext b
  cases b <;> simp [toNative, polarizedOne, rationalBasis]

@[simp] theorem toNative_polarizedNPlus :
    toNative polarizedNPlus = modularNPlus := by
  native_decide

@[simp] theorem toNative_polarizedNMinus :
    toNative polarizedNMinus = modularNMinus := by
  native_decide

@[simp] theorem toNative_polarizedZornNPlus :
    toNative polarizedZornNPlus = modularNPlus :=
  toNative_polarizedNPlus

@[simp] theorem toNative_polarizedZornNMinus :
    toNative polarizedZornNMinus = modularNMinus :=
  toNative_polarizedNMinus

@[simp] theorem toNative_polarizedSigmaRedPlus :
    toNative polarizedSigmaRedPlus = modularSigmaPlus .red := by
  native_decide

@[simp] theorem toNative_polarizedSigmaGreenPlus :
    toNative polarizedSigmaGreenPlus = modularSigmaPlus .green := by
  native_decide

@[simp] theorem toNative_polarizedSigmaBluePlus :
    toNative polarizedSigmaBluePlus = modularSigmaPlus .blue := by
  native_decide

@[simp] theorem toNative_polarizedSigmaRedMinus :
    toNative polarizedSigmaRedMinus = modularSigmaMinus .red := by
  native_decide

@[simp] theorem toNative_polarizedSigmaGreenMinus :
    toNative polarizedSigmaGreenMinus = modularSigmaMinus .green := by
  native_decide

@[simp] theorem toNative_polarizedSigmaBlueMinus :
    toNative polarizedSigmaBlueMinus = modularSigmaMinus .blue := by
  native_decide

@[simp] theorem toNative_polarizedZornSigmaPlus
    (c : SplitOctonionColour) :
    toNative (polarizedZornSigmaPlus c) = modularSigmaPlus c := by
  cases c <;> simp [polarizedZornSigmaPlus]

@[simp] theorem toNative_polarizedZornSigmaMinus
    (c : SplitOctonionColour) :
    toNative (polarizedZornSigmaMinus c) = modularSigmaMinus c := by
  cases c <;> simp [polarizedZornSigmaMinus]

@[simp] theorem toNative_polarizedMul (X Y : PolarizedZorn) :
    toNative (X * Y) =
      splitOctonionMulQ (toNative X) (toNative Y) := by
  change toNative (polarizedMul X Y) =
    splitOctonionMulQ (toNative X) (toNative Y)
  funext b
  cases b <;>
    simp [toNative, polarizedMul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three, splitOctonionMulQ, splitQuaternionOfQ,
      splitQuaternionLPartQ, splitQuaternionConjQ, splitQuaternionAddQ,
      splitQuaternionMulQ, splitOctonionOfQuaternionPairQ] <;>
    ring_nf

structure NativeMulAutomorphism where
  toEquiv : StandardRationalSplitOctonion ≃ StandardRationalSplitOctonion
  map_mul : ∀ X Y,
    toEquiv (splitOctonionMulQ X Y) =
      splitOctonionMulQ (toEquiv X) (toEquiv Y)

noncomputable def transportNativeEquiv
    (g : StandardRationalSplitOctonion ≃ StandardRationalSplitOctonion) :
    PolarizedZorn ≃ PolarizedZorn :=
  toNativeEquiv.trans (g.trans toNativeEquiv.symm)

theorem transportNativeMulAutomorphism_map_mul
    (g : NativeMulAutomorphism) (X Y : PolarizedZorn) :
    transportNativeEquiv g.toEquiv (X * Y) =
      transportNativeEquiv g.toEquiv X *
        transportNativeEquiv g.toEquiv Y := by
  apply toNativeEquiv.injective
  simpa [transportNativeEquiv, toNativeEquiv, Equiv.trans_apply,
    toNative_polarizedMul] using g.map_mul (toNative X) (toNative Y)

structure NativeQuadraticSymmetry
    (q : StandardRationalSplitOctonion → ℚ) where
  toEquiv : StandardRationalSplitOctonion ≃ StandardRationalSplitOctonion
  map_quadratic : ∀ X, q (toEquiv X) = q X

def pulledBackQuadratic
    (q : StandardRationalSplitOctonion → ℚ)
    (X : PolarizedZorn) : ℚ :=
  q (toNative X)

theorem transportNativeQuadraticSymmetry_preserves
    {q : StandardRationalSplitOctonion → ℚ}
    (g : NativeQuadraticSymmetry q) (X : PolarizedZorn) :
    pulledBackQuadratic q (transportNativeEquiv g.toEquiv X) =
      pulledBackQuadratic q X := by
  simpa [pulledBackQuadratic, transportNativeEquiv, toNativeEquiv,
    Equiv.trans_apply] using g.map_quadratic (toNative X)

end InfoGeometry.Canonical
