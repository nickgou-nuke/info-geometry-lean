import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Split Clifford algebras `Cl(n,n)`

This file starts a mathlib-native formalization of real split Clifford algebras.
The important point is that mathlib's `QuadraticForm` is not restricted to
positive definite forms, so indefinite signatures are represented directly.

We model one hyperbolic/split plane by

`Q11(x,y) = x^2 - y^2`.

Then `Qsplit n` is the orthogonal product of `n` copies of `Q11`; its Clifford
algebra is our `Cl(n,n)` model.  Mathlib already proves the structural product
law for Clifford algebras:

`Cl(Q₁.prod Q₂) ≃ₐ evenOdd Q₁ ᵍ⊗ evenOdd Q₂`.

Thus the theorem `clnn_succ_factor` gives the recursive factorization

`Cl(n+1,n+1) ≃ Cl(n,n) ᵍ⊗ Cl(1,1)`.

Iterating this gives the intended slogan `Cl(n,n) = Cl(1,1)^n`; the target is a
nested graded tensor product, because Clifford generators from different
orthogonal blocks anticommute, not commute.
-/

noncomputable section
open scoped TensorProduct
open Matrix Polynomial

namespace SplitClifford

/-- The positive one-dimensional real quadratic form `x ↦ x^2`. -/
abbrev Qpos : QuadraticForm ℝ ℝ := QuadraticMap.sq (R := ℝ)

/-- The negative one-dimensional real quadratic form `x ↦ -x^2`. -/
abbrev Qneg : QuadraticForm ℝ ℝ := - QuadraticMap.sq (R := ℝ)

/-- The split plane of signature `(1,1)`: `Q11(x,y)=x^2-y^2`. -/
abbrev Q11 : QuadraticForm ℝ (ℝ × ℝ) := Qpos.prod Qneg

/-- The real Clifford algebra `Cl(1,1)` in this file's model. -/
abbrev Cl11 := CliffordAlgebra Q11

/-- Positive generator of the split plane. -/
def ePos : Cl11 := CliffordAlgebra.ι Q11 (1, 0)

/-- Negative generator of the split plane. -/
def eNeg : Cl11 := CliffordAlgebra.ι Q11 (0, 1)

@[simp] theorem Qpos_one : Qpos (1 : ℝ) = 1 := by
  norm_num [Qpos, QuadraticMap.sq_apply]

@[simp] theorem Qneg_one : Qneg (1 : ℝ) = -1 := by
  norm_num [Qneg, QuadraticMap.sq_apply]

@[simp] theorem Q11_pos : Q11 (1, 0) = 1 := by
  norm_num [Q11, Qpos, Qneg, QuadraticMap.sq_apply]

@[simp] theorem Q11_neg : Q11 (0, 1) = -1 := by
  norm_num [Q11, Qpos, Qneg, QuadraticMap.sq_apply]

/-- The positive split generator squares to `+1`. -/
@[simp] theorem ePos_sq : ePos * ePos = (1 : Cl11) := by
  rw [ePos, CliffordAlgebra.ι_sq_scalar]
  norm_num [Q11, Qpos, Qneg, QuadraticMap.sq_apply]

/-- The negative split generator squares to `-1`. -/
@[simp] theorem eNeg_sq : eNeg * eNeg = (-1 : Cl11) := by
  rw [eNeg, CliffordAlgebra.ι_sq_scalar]
  norm_num [Q11, Qpos, Qneg, QuadraticMap.sq_apply]

/-- The two coordinate axes in the split plane are orthogonal for `x^2-y^2`. -/
lemma pos_ortho_neg : Q11.IsOrtho (1, 0) (0, 1) := by
  simp [QuadraticMap.isOrtho_def, Q11, Qpos, Qneg, QuadraticMap.sq_apply]

/-- Orthogonal Clifford generators anticommute. -/
@[simp] theorem ePos_mul_eNeg : ePos * eNeg = -(eNeg * ePos) := by
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (Q := Q11) pos_ortho_neg

/-! ## Normalized Clifford--Jordan--Lie split

The Clifford product decomposes into a symmetric/Jordan part and an
antisymmetric/Lie part.  We normalize by `1/2`; this is the convention needed
for structure constants, because the raw commutator/anticommutator carry an
extra factor of two.
-/

/-- Raw anticommutator. -/
def antiComm {A : Type*} [Mul A] [Add A] (a b : A) : A :=
  a * b + b * a

/-- Raw commutator. -/
def comm {A : Type*} [Mul A] [Sub A] (a b : A) : A :=
  a * b - b * a

/-- Normalized Jordan/symmetric product over `ℝ`. -/
def jordanR {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℝ A] (a b : A) : A :=
  ((2 : ℝ)⁻¹) • (a * b + b * a)

/-- Normalized Lie/antisymmetric product over `ℝ`. -/
def lieR {A : Type*} [NonUnitalNonAssocRing A] [Module ℝ A] (a b : A) : A :=
  ((2 : ℝ)⁻¹) • (a * b - b * a)

/-- Normalized Jordan/symmetric product over `ℂ`. -/
def jordanC {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℂ A] (a b : A) : A :=
  ((2 : ℂ)⁻¹) • (a * b + b * a)

/-- Normalized Lie/antisymmetric product over `ℂ`. -/
def lieC {A : Type*} [NonUnitalNonAssocRing A] [Module ℂ A] (a b : A) : A :=
  ((2 : ℂ)⁻¹) • (a * b - b * a)

/-- Weyl/scale-normalized Jordan product.  The parameter `s` is the local gauge
scale; when `s=1` this is `jordanC`. -/
def scaledJordanC {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℂ A]
    (s : ℂ) (a b : A) : A :=
  s⁻¹ • jordanC a b

/-- Weyl/scale-normalized Lie product. -/
def scaledLieC {A : Type*} [NonUnitalNonAssocRing A] [Module ℂ A]
    (s : ℂ) (a b : A) : A :=
  s⁻¹ • lieC a b

/-- Bool parity sign for the graded/super bracket.  It is `-1` exactly when
both inputs are odd. -/
def paritySign (p q : Bool) : ℂ :=
  if p && q then -1 else 1

/-- Graded commutator: `xy - (-1)^{|x||y|} yx`. -/
def superBracket {A : Type*} [Mul A] [Sub A] [SMul ℂ A] (p q : Bool) (a b : A) : A :=
  a * b - paritySign p q • (b * a)

/-- Graded anticommutator: `xy + (-1)^{|x||y|} yx`. -/
def superAntiBracket {A : Type*} [Mul A] [Add A] [SMul ℂ A] (p q : Bool) (a b : A) : A :=
  a * b + paritySign p q • (b * a)

/-- For even/even or even/odd inputs the superbracket is the ordinary
commutator. -/
@[simp] theorem superBracket_even_left {A : Type*} [Mul A] [Sub A] [SMul ℂ A]
    (q : Bool) (a b : A) : superBracket false q a b = a * b - (1 : ℂ) • (b * a) := by
  simp [superBracket, paritySign]

/-- For odd/odd inputs the superbracket is the ordinary anticommutator. -/
@[simp] theorem superBracket_odd_odd {A : Type*} [Mul A] [Sub A] [SMul ℂ A]
    (a b : A) : superBracket true true a b = a * b - (-1 : ℂ) • (b * a) := by
  simp [superBracket, paritySign]

/-- The normalized split recombines to the original product over complex matrix
algebras. -/
theorem jordanC_add_lieC_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : jordanC A B + lieC A B = A * B := by
  ext i j
  simp [jordanC, lieC]
  ring

/-- The normalized split recombines to the original product over real Clifford
algebras. -/
theorem jordanR_add_lieR_clifford (A B : Cl11) : jordanR A B + lieR A B = A * B := by
  simp [jordanR, lieR]
  module

/-- Orthogonal `Cl(1,1)` generators have zero normalized Jordan product. -/
theorem ePos_eNeg_jordan_zero : jordanR ePos eNeg = 0 := by
  simp [jordanR, ePos_mul_eNeg]

/-- For orthogonal `Cl(1,1)` generators, the normalized Lie product is exactly
the Clifford product. -/
theorem ePos_eNeg_lie_eq_mul : lieR ePos eNeg = ePos * eNeg := by
  simp [lieR, ePos_mul_eNeg]
  module

/-- The positive generator's normalized Jordan square is `+1`. -/
theorem ePos_jordan_self : jordanR ePos ePos = (1 : Cl11) := by
  simp [jordanR]
  module

/-- The negative generator's normalized Jordan square is `-1`. -/
theorem eNeg_jordan_self : jordanR eNeg eNeg = (-1 : Cl11) := by
  simp [jordanR]
  module

/-! ## CAR/CCR structures over the normalized split

The CAR algebra is finite-dimensional in one mode and is represented exactly by
creation/annihilation matrices.  Exact CCR cannot be represented by finite
matrices over characteristic zero fields because the trace of a commutator is
zero but the trace of the identity is nonzero.  We therefore provide both an
abstract exact `CCRPair` interface and a finite cutoff model whose commutator
has the expected cutoff defect.
-/

/-- A one-mode CAR pair in an algebra: annihilation `ann`, creation `cre`, both
square-zero, with `{ann,cre}=1`. -/
structure CARPair (A : Type*) [Mul A] [Add A] [OfNat A 0] [OfNat A 1] where
  ann : A
  cre : A
  ann_sq : ann * ann = 0
  cre_sq : cre * cre = 0
  anti : ann * cre + cre * ann = 1

/-- A formal one-mode CCR pair in an algebra: `[ann,cre]=1`. -/
structure CCRPair (A : Type*) [Mul A] [Sub A] [OfNat A 1] where
  ann : A
  cre : A
  commutator : ann * cre - cre * ann = 1

/-- One-mode fermionic annihilation matrix. -/
def carAnn : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1;
     0, 0]

/-- One-mode fermionic creation matrix. -/
def carCre : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0;
     1, 0]

@[simp] theorem carAnn_sq : carAnn * carAnn = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [carAnn, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem carCre_sq : carCre * carCre = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [carCre, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exact one-mode CAR: `{a,a†}=1`. -/
@[simp] theorem car_anticommutator :
    antiComm carAnn carCre = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiComm, carAnn, carCre]

/-- The concrete one-mode CAR algebra seed. -/
def carPair_matrix : CARPair (Matrix (Fin 2) (Fin 2) ℂ) where
  ann := carAnn
  cre := carCre
  ann_sq := carAnn_sq
  cre_sq := carCre_sq
  anti := car_anticommutator

/-- Finite two-level bosonic cutoff uses the same shift matrices, but its
commutator is not the identity; it is a boundary-defected CCR. -/
@[simp] theorem ccr_two_level_commutator_defect :
    comm carAnn carCre = !![(1 : ℂ), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [comm, carAnn, carCre]

/-- The trace obstruction: the two-level cutoff commutator has trace zero. -/
theorem ccr_two_level_commutator_trace_zero :
    Matrix.trace (comm carAnn carCre) = 0 := by
  rw [ccr_two_level_commutator_defect]
  simp [Matrix.trace_fin_two]

/-- But the identity on the same finite space has trace two, so finite matrices
cannot realize exact one-mode CCR here. -/
theorem finite_two_level_not_exact_CCR :
    comm carAnn carCre ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have ht : Matrix.trace (comm carAnn carCre) = Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [h]
  rw [ccr_two_level_commutator_trace_zero] at ht
  norm_num [Matrix.trace_fin_two] at ht

/-- Weyl-form CCR interface: the exponentiated relation packages the symplectic
form as a phase multiplier.  This is the right exact interface for infinite or
formal bosonic systems.  We keep the multiplier abstract to avoid committing to
analytic exponential infrastructure in this algebraic file. -/
structure WeylCCR (V A : Type*) [Add V] [Mul A] [SMul ℂ A] where
  W : V → A
  omega : V → V → ℂ
  phase : V → V → ℂ
  weyl_mul : ∀ f g : V, W f * W g = phase f g • W (f + g)

/-! ## Affine superbrackets, Rindler/Souriau thermodynamic data, and TKK closure

The affine simplex parameter `α` interpolates between the graded commutator and
graded anticommutator.  This records the idea that the excitation/mixing sector
is not a single bracket but a Gibbs/Bogoliubov-weighted affine combination of
Lie and Jordan pieces.
-/

/-- Affine interpolation between superbracket and super-anticommutator. -/
def affineSuperBracket {A : Type*} [Mul A] [Add A] [Sub A] [SMul ℂ A]
    (α : ℂ) (p q : Bool) (a b : A) : A :=
  α • superBracket p q a b + (1 - α) • superAntiBracket p q a b

@[simp] theorem affineSuperBracket_alpha_one {n : Type*} [Fintype n] [DecidableEq n]
    (p q : Bool) (A B : Matrix n n ℂ) :
    affineSuperBracket 1 p q A B = superBracket p q A B := by
  simp [affineSuperBracket]

@[simp] theorem affineSuperBracket_alpha_zero {n : Type*} [Fintype n] [DecidableEq n]
    (p q : Bool) (A B : Matrix n n ℂ) :
    affineSuperBracket 0 p q A B = superAntiBracket p q A B := by
  simp [affineSuperBracket]

/-- The centralizer atom around which the affine geometry is organized. -/
inductive CentralizerAtom where
  | plusI
  | minusI
  deriving DecidableEq, Repr

/-- Matrix realization of `{I,-I}`. -/
def centralizerValue {n : Type*} [Fintype n] [DecidableEq n] :
    CentralizerAtom → Matrix n n ℂ
  | .plusI => 1
  | .minusI => -1

@[simp] theorem centralizer_plus_sq {n : Type*} [Fintype n] [DecidableEq n] :
    (centralizerValue (n := n) .plusI) * centralizerValue .plusI = (1 : Matrix n n ℂ) := by
  simp [centralizerValue]

@[simp] theorem centralizer_minus_sq {n : Type*} [Fintype n] [DecidableEq n] :
    (centralizerValue (n := n) .minusI) * centralizerValue .minusI = (1 : Matrix n n ℂ) := by
  simp [centralizerValue]

/-- A two-vertex affine simplex parameter. -/
structure Simplex2 where
  α : ℝ
  nonneg : 0 ≤ α
  le_one : α ≤ 1

/-- Rindler/Unruh inverse-temperature scale, defined algebraically. -/
def rindlerBeta (accel : ℝ) : ℝ :=
  (2 * Real.pi) / accel

/-- Unruh temperature scale, defined algebraically. -/
def unruhTemperature (accel : ℝ) : ℝ :=
  accel / (2 * Real.pi)

/-- Grand-canonical exponent `-β(E-μq)` before applying an analytic exponential. -/
def grandCanonicalExponent (β μ E q : ℝ) : ℝ :=
  -β * (E - μ * q)

/-- Souriau/Gibbs affine bracket data: thermodynamic weights drive the bracket
mixture and a chemical potential shifts the excitation energy. -/
structure SouriauAffineBracket where
  α : ℝ
  β : ℝ
  μ : ℝ
  energy : ℝ
  charge : ℝ
  exponent_eq : grandCanonicalExponent β μ energy charge = -β * (energy - μ * charge)

/-- Symbolic Bogoliubov/Rindler boost matrix with parameters `c,s`. -/
def bogoliubovMix (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c, s;
     s, c]

/-- The Krein metric preserved by a hyperbolic Bogoliubov boost. -/
def kreinJ : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, -1]

/-- A Bogoliubov boost preserves the Krein/CAR form once normalized by
`c^2-s^2=1`.  This is the algebraic rapidity skeleton without analytic cosh/sinh. -/
theorem bogoliubov_preserves_krein {c s : ℝ} (h : c * c - s * s = 1) :
    (bogoliubovMix c s).transpose * kreinJ * bogoliubovMix c s = kreinJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bogoliubovMix, kreinJ, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]

/-- The projective-affine-conformal closure is represented as an interface:
from a split Clifford carrier, through normalized Jordan/Lie/super brackets, to a
structure group action and TKK-style closure. -/
structure ProjectiveAffineConformalClosure where
  cliffordCarrier : Prop
  jordanLieSplit : Prop
  supergradedAlgebra : Prop
  structureGroupAction : Prop
  tkkClosure : Prop
  closes : cliffordCarrier → jordanLieSplit → supergradedAlgebra → structureGroupAction → tkkClosure

/-! ## Chiral operator, projectors, and split pseudoscalar

In a split Clifford algebra the chiral operator is the normalized top-grade
volume element/pseudoscalar.  For the `Cl(1,1)` atom, the pseudoscalar is
`γ=e₊e₋`; since `e₊²=+1`, `e₋²=-1`, and `e₊e₋=-e₋e₊`, it satisfies `γ²=1`.
Thus the chiral projectors are `(1±γ)/2`.
-/

/-- The `Cl(1,1)` pseudoscalar/chiral operator. -/
def gamma11 : Cl11 :=
  ePos * eNeg

/-- The split `Cl(1,1)` pseudoscalar squares to `+1`. -/
@[simp] theorem gamma11_sq : gamma11 * gamma11 = (1 : Cl11) := by
  have hswap : eNeg * ePos = -(ePos * eNeg) := by
    rw [ePos_mul_eNeg]
    rw [neg_neg]
  calc
    gamma11 * gamma11 = (ePos * eNeg) * (ePos * eNeg) := by rfl
    _ = ePos * (eNeg * ePos) * eNeg := by noncomm_ring
    _ = ePos * (-(ePos * eNeg)) * eNeg := by rw [hswap]
    _ = -((ePos * ePos) * (eNeg * eNeg)) := by noncomm_ring
    _ = (1 : Cl11) := by rw [ePos_sq, eNeg_sq]; norm_num

/-- Positive chiral projector `(1+γ)/2`. -/
def chiralProjPlus11 : Cl11 :=
  ((2 : ℝ)⁻¹) • ((1 : Cl11) + gamma11)

/-- Negative chiral projector `(1-γ)/2`. -/
def chiralProjMinus11 : Cl11 :=
  ((2 : ℝ)⁻¹) • ((1 : Cl11) - gamma11)

/-- Algebraic expansion behind the positive chiral projector. -/
lemma one_add_gamma11_mul_self :
    ((1 : Cl11) + gamma11) * ((1 : Cl11) + gamma11) =
      (2 : ℝ) • ((1 : Cl11) + gamma11) := by
  calc
    ((1 : Cl11) + gamma11) * ((1 : Cl11) + gamma11)
        = (1 : Cl11) + gamma11 + gamma11 + gamma11 * gamma11 := by noncomm_ring
    _ = (2 : ℝ) • ((1 : Cl11) + gamma11) := by
        rw [gamma11_sq]
        simp [two_smul]
        abel

/-- Algebraic expansion behind the negative chiral projector. -/
lemma one_sub_gamma11_mul_self :
    ((1 : Cl11) - gamma11) * ((1 : Cl11) - gamma11) =
      (2 : ℝ) • ((1 : Cl11) - gamma11) := by
  calc
    ((1 : Cl11) - gamma11) * ((1 : Cl11) - gamma11)
        = (1 : Cl11) - gamma11 - gamma11 + gamma11 * gamma11 := by noncomm_ring
    _ = (2 : ℝ) • ((1 : Cl11) - gamma11) := by
        rw [gamma11_sq]
        simp [two_smul]
        abel

/-- The positive chiral projector is idempotent. -/
@[simp] theorem chiralProjPlus11_idempotent :
    chiralProjPlus11 * chiralProjPlus11 = chiralProjPlus11 := by
  rw [chiralProjPlus11]
  calc
    ((2 : ℝ)⁻¹ • ((1 : Cl11) + gamma11)) * ((2 : ℝ)⁻¹ • ((1 : Cl11) + gamma11))
        = ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • (((1 : Cl11) + gamma11) * ((1 : Cl11) + gamma11)) := by
          rw [smul_mul_smul]
    _ = ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • ((2 : ℝ) • ((1 : Cl11) + gamma11)) := by
          rw [one_add_gamma11_mul_self]
    _ = ((2 : ℝ)⁻¹) • ((1 : Cl11) + gamma11) := by
          norm_num [smul_smul]

/-- The negative chiral projector is idempotent. -/
@[simp] theorem chiralProjMinus11_idempotent :
    chiralProjMinus11 * chiralProjMinus11 = chiralProjMinus11 := by
  rw [chiralProjMinus11]
  calc
    ((2 : ℝ)⁻¹ • ((1 : Cl11) - gamma11)) * ((2 : ℝ)⁻¹ • ((1 : Cl11) - gamma11))
        = ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • (((1 : Cl11) - gamma11) * ((1 : Cl11) - gamma11)) := by
          rw [smul_mul_smul]
    _ = ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • ((2 : ℝ) • ((1 : Cl11) - gamma11)) := by
          rw [one_sub_gamma11_mul_self]
    _ = ((2 : ℝ)⁻¹) • ((1 : Cl11) - gamma11) := by
          norm_num [smul_smul]

/-- The two chiral projectors sum to the identity. -/
@[simp] theorem chiralProjPlus11_add_minus :
    chiralProjPlus11 + chiralProjMinus11 = (1 : Cl11) := by
  simp [chiralProjPlus11, chiralProjMinus11]
  module

/-- Algebraic orthogonality expansion for the two chiral sectors. -/
lemma one_add_gamma11_mul_one_sub_gamma11 :
    ((1 : Cl11) + gamma11) * ((1 : Cl11) - gamma11) = 0 := by
  calc
    ((1 : Cl11) + gamma11) * ((1 : Cl11) - gamma11)
        = (1 : Cl11) - gamma11 + gamma11 - gamma11 * gamma11 := by noncomm_ring
    _ = 0 := by rw [gamma11_sq]; abel

/-- The two chiral projectors are orthogonal. -/
@[simp] theorem chiralProjPlus11_mul_minus :
    chiralProjPlus11 * chiralProjMinus11 = (0 : Cl11) := by
  rw [chiralProjPlus11, chiralProjMinus11]
  calc
    ((2 : ℝ)⁻¹ • ((1 : Cl11) + gamma11)) * ((2 : ℝ)⁻¹ • ((1 : Cl11) - gamma11))
        = ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • (((1 : Cl11) + gamma11) * ((1 : Cl11) - gamma11)) := by
          rw [smul_mul_smul]
    _ = 0 := by
          rw [one_add_gamma11_mul_one_sub_gamma11]
          simp

/-- The split tripotent order-parameter/operator with sectors `+1`, `-1`, and `0`. -/
def OP : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, -1, 0;
     0, 0, 0]

/-- The split order-parameter is tripotent: `OP^3 = OP`. -/
@[simp] theorem OP_tripotent : OP ^ 3 = OP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OP, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

/-- Equivalently, the polynomial annihilator is `OP^3 - OP = 0`. -/
theorem OP_cubic_annihilator : OP ^ 3 - OP = 0 := by
  rw [OP_tripotent, sub_self]

/-- The characteristic polynomial of the split tripotent is `(X-1)(X+1)X`. -/
theorem OP_charpoly_factor :
    OP.charpoly = (X - C (1 : ℂ)) * (X - C (-1 : ℂ)) * X := by
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three, OP]

/-- The same characteristic polynomial as the cubic `X^3-X`. -/
theorem OP_charpoly_cubic : OP.charpoly = X ^ 3 - X := by
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three, OP]
  ring

/-- The three visible roots/eigenvalues of the split tripotent. -/
theorem OP_charpoly_root_pos : OP.charpoly.IsRoot (1 : ℂ) := by
  rw [OP_charpoly_cubic]
  norm_num [Polynomial.IsRoot.def]

/-- The negative Clifford sector root/eigenvalue. -/
theorem OP_charpoly_root_neg : OP.charpoly.IsRoot (-1 : ℂ) := by
  rw [OP_charpoly_cubic]
  norm_num

/-- The nilpotent/radical sector root/eigenvalue. -/
theorem OP_charpoly_root_zero : OP.charpoly.IsRoot (0 : ℂ) := by
  rw [OP_charpoly_cubic]
  norm_num [Polynomial.IsRoot.def]

/-- The characteristic roots of the split tripotent are exactly `{-1,0,1}`. -/
theorem OP_charpoly_roots_iff (lam : ℂ) :
    OP.charpoly.IsRoot lam ↔ lam = -1 ∨ lam = 0 ∨ lam = 1 := by
  rw [OP_charpoly_cubic, Polynomial.IsRoot.def]
  simp
  constructor
  · intro h
    have hfac : lam * ((lam - 1) * (lam + 1)) = 0 := by
      calc
        lam * ((lam - 1) * (lam + 1)) = lam ^ 3 - lam := by ring
        _ = 0 := h
    rcases mul_eq_zero.mp hfac with h0 | hrest
    · exact Or.inr (Or.inl h0)
    · rcases mul_eq_zero.mp hrest with h1 | hm1
      · exact Or.inr (Or.inr (sub_eq_zero.mp h1))
      · exact Or.inl ((add_eq_zero_iff_eq_neg.mp hm1).trans (by norm_num))
  · intro h
    rcases h with hm1 | h0 | h1 <;> subst lam <;> norm_num

/-- The underlying module for `n` split planes, recursively as nested products. -/
abbrev SplitSpace : Nat → Type
  | 0 => PUnit
  | n + 1 => SplitSpace n × (ℝ × ℝ)

instance (n : Nat) : AddCommGroup (SplitSpace n) := by
  induction n with
  | zero => infer_instance
  | succ n _ => exact inferInstanceAs (AddCommGroup (SplitSpace n × (ℝ × ℝ)))

instance (n : Nat) : Module ℝ (SplitSpace n) := by
  induction n with
  | zero => infer_instance
  | succ n _ => exact inferInstanceAs (Module ℝ (SplitSpace n × (ℝ × ℝ)))

/-- The split quadratic form of signature `(n,n)`, as an orthogonal sum of `n`
copies of `Q11`. -/
abbrev Qsplit : (n : Nat) → QuadraticForm ℝ (SplitSpace n)
  | 0 => 0
  | n + 1 => (Qsplit n).prod Q11

/-- The real split Clifford algebra `Cl(n,n)` modeled by `Qsplit n`. -/
abbrev Clnn (n : Nat) := CliffordAlgebra (Qsplit n)

/-- `Cl(0,0)` is the Clifford algebra of the zero quadratic form on the unit
module. -/
abbrev Cl00 := Clnn 0

/-- `Cl(2,2)` is `Cl(Q11 ⊕ Q11)`. -/
abbrev Q22 : QuadraticForm ℝ ((ℝ × ℝ) × (ℝ × ℝ)) := Q11.prod Q11

/-- Two split planes split as the graded tensor product of two `Cl(1,1)` factors. -/
def cl22_as_cl11_gTensor_cl11 :
    CliffordAlgebra Q22 ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q11) :=
  CliffordAlgebra.prodEquiv Q11 Q11

/-- The positive generator in the last split block of `Cl(n+1,n+1)`. -/
def lastPos (n : Nat) : Clnn (n + 1) :=
  CliffordAlgebra.ι (Qsplit (n + 1)) (0, (1, 0))

/-- The negative generator in the last split block of `Cl(n+1,n+1)`. -/
def lastNeg (n : Nat) : Clnn (n + 1) :=
  CliffordAlgebra.ι (Qsplit (n + 1)) (0, (0, 1))

@[simp] theorem Qsplit_last_pos (n : Nat) : Qsplit (n + 1) (0, (1, 0)) = 1 := by
  rw [Qsplit, QuadraticMap.prod_apply, QuadraticMap.map_zero]
  simp [Q11, Qpos, Qneg, QuadraticMap.sq_apply]

@[simp] theorem Qsplit_last_neg (n : Nat) : Qsplit (n + 1) (0, (0, 1)) = -1 := by
  rw [Qsplit, QuadraticMap.prod_apply, QuadraticMap.map_zero]
  simp [Q11, Qpos, Qneg, QuadraticMap.sq_apply]

/-- In every `Cl(n+1,n+1)`, the new positive generator squares to `+1`. -/
@[simp] theorem lastPos_sq (n : Nat) : lastPos n * lastPos n = (1 : Clnn (n + 1)) := by
  rw [lastPos, CliffordAlgebra.ι_sq_scalar]
  simp [Qsplit_last_pos]

/-- In every `Cl(n+1,n+1)`, the new negative generator squares to `-1`. -/
@[simp] theorem lastNeg_sq (n : Nat) : lastNeg n * lastNeg n = (-1 : Clnn (n + 1)) := by
  rw [lastNeg, CliffordAlgebra.ι_sq_scalar]
  simp [Qsplit_last_neg]

lemma last_pos_ortho_last_neg (n : Nat) :
    (Qsplit (n + 1)).IsOrtho (0, (1, 0)) (0, (0, 1)) := by
  exact (QuadraticMap.isOrtho_inr_inr_iff (Q₁ := Qsplit n) (Q₂ := Q11)
    (1, 0) (0, 1)).mpr pos_ortho_neg

/-- The two generators in the last split block anticommute. -/
@[simp] theorem lastPos_mul_lastNeg (n : Nat) :
    lastPos n * lastNeg n = -(lastNeg n * lastPos n) := by
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (Q := Qsplit (n + 1))
    (last_pos_ortho_last_neg n)

/-- Embed `Cl(n,n)` into the next split Clifford algebra by adding a final
orthogonal `Cl(1,1)` block. -/
def embedPrev (n : Nat) : Clnn n →ₐ[ℝ] Clnn (n + 1) :=
  CliffordAlgebra.map (QuadraticMap.Isometry.inl (Qsplit n) Q11)

/-- Recursive top-grade split pseudoscalar/volume element.  For `n+1`, take the
previous volume and multiply by the last split plane's two generators.  This is
the algebraic top-degree element for the highest `2n`-form in `Cl(n,n)`. -/
def splitVolume : (n : Nat) → Clnn n
  | 0 => 1
  | n + 1 => embedPrev n (splitVolume n) * lastPos n * lastNeg n

@[simp] theorem splitVolume_zero : splitVolume 0 = (1 : Clnn 0) := rfl

@[simp] theorem splitVolume_succ (n : Nat) :
    splitVolume (n + 1) = embedPrev n (splitVolume n) * lastPos n * lastNeg n := rfl

/-- Recursive product law for split Clifford algebras.

This is the formal version of
`Cl(n+1,n+1) ≃ Cl(n,n) ⊗̂ Cl(1,1)`, where `⊗̂` is the graded tensor product. -/
def clnn_succ_factor (n : Nat) :
    Clnn (n + 1) ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit n) ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q11) :=
  CliffordAlgebra.prodEquiv (Qsplit n) Q11

/-- The first nontrivial recursive factorization is exactly `Cl(1,1)`. -/
def cl11_from_cl00_step :
    Clnn 1 ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit 0) ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q11) :=
  clnn_succ_factor 0

/-- The next recursive factorization: `Cl(2,2) ≃ Cl(1,1) ⊗̂ Cl(1,1)`. -/
def cl22_from_cl11_step :
    Clnn 2 ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit 1) ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q11) :=
  clnn_succ_factor 1

/-- The three-block factorization step: `Cl(3,3) ≃ Cl(2,2) ⊗̂ Cl(1,1)`. -/
def cl33_from_cl22_step :
    Clnn 3 ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit 2) ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q11) :=
  clnn_succ_factor 2

/-! ## `Cl(4,4)`, `Cl(5,5)`, chiral sheets, and modular radial reflection -/

/-- The real split `Cl(4,4)` carrier.  Its irreducible matrix model has real
spinor dimension `16 = 2^4`. -/
abbrev Cl44 := Clnn 4

/-- The real split `Cl(5,5)` carrier. -/
abbrev Cl55 := Clnn 5

/-- Tensoring the `Cl(4,4)` carrier with the `Cl(1,1)` modular/CPT atom gives
`Cl(5,5)`.  This is again a graded tensor product, not an ordinary tensor
product. -/
def cl55_from_cl44_step :
    Cl55 ≃ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit 4) ᵍ⊗[ℝ] CliffordAlgebra.evenOdd Q11) :=
  clnn_succ_factor 4

/-- Real split spinor dimension for `Cl(n,n) ≃ M_{2^n}(ℝ)`. -/
def splitSpinorDim (n : ℕ) : ℕ :=
  2 ^ n

@[simp] theorem splitSpinorDim_four : splitSpinorDim 4 = 16 := by
  norm_num [splitSpinorDim]

@[simp] theorem splitSpinorDim_five : splitSpinorDim 5 = 32 := by
  norm_num [splitSpinorDim]

/-- The `Cl(4,4)` real spinor sheet has dimension `16`. -/
def chiralSheetDim : ℕ := splitSpinorDim 4

/-- The `Cl(5,5)` real spinor carrier has two `16`-dimensional chiral sheets. -/
def doubledChiralDim : ℕ := chiralSheetDim + chiralSheetDim

@[simp] theorem chiralSheetDim_eq_16 : chiralSheetDim = 16 := by
  norm_num [chiralSheetDim, splitSpinorDim]

@[simp] theorem doubledChiralDim_eq_32 : doubledChiralDim = 32 := by
  norm_num [doubledChiralDim, chiralSheetDim, splitSpinorDim]

/-- The two real chiral sheets supplied by the `Cl(1,1)` factor. -/
inductive ChiralSheet where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The trifactor sheet labels carried by the tripotent `OP`: elliptic,
parabolic, and hyperbolic. -/
inductive TrifactorSheet where
  | elliptic
  | parabolic
  | hyperbolic
  deriving DecidableEq, Repr

/-- The determinant/eigenvalue classifier attached to the trifactor sheets. -/
def trifactorValue : TrifactorSheet → ℂ
  | .elliptic => -1
  | .parabolic => 0
  | .hyperbolic => 1

@[simp] theorem trifactor_elliptic_value : trifactorValue .elliptic = (-1 : ℂ) := rfl
@[simp] theorem trifactor_parabolic_value : trifactorValue .parabolic = (0 : ℂ) := rfl
@[simp] theorem trifactor_hyperbolic_value : trifactorValue .hyperbolic = (1 : ℂ) := rfl

/-- Every trifactor sheet value is a root of the tripotent characteristic
polynomial. -/
theorem trifactorValue_is_OP_root (s : TrifactorSheet) : OP.charpoly.IsRoot (trifactorValue s) := by
  cases s
  · exact OP_charpoly_root_neg
  · exact OP_charpoly_root_zero
  · exact OP_charpoly_root_pos

/-- Modular logarithmic radial reflection `J : u ↦ -u`. -/
def modularJ (u : ℝ) : ℝ := -u

@[simp] theorem modularJ_involutive (u : ℝ) : modularJ (modularJ u) = u := by
  simp [modularJ]

@[simp] theorem modularJ_fixed_zero : modularJ 0 = 0 := by
  simp [modularJ]

/-- Radial inversion version of modular reflection: `r ↦ r⁻¹`. -/
def radialJ (r : ℝ) : ℝ := r⁻¹

/-- Away from zero, radial modular reflection exchanges zero/infinity directions
by inversion and is involutive. -/
theorem radialJ_involutive {r : ℝ} (_hr : r ≠ 0) : radialJ (radialJ r) = r := by
  simp [radialJ, inv_inv]

/-- A minimal Bloch-ball state: a real three-vector. -/
abbrev BlochVector := Fin 3 → ℝ

/-- Squared Euclidean radius of a Bloch vector. -/
def blochNormSq (v : BlochVector) : ℝ :=
  ∑ i, v i * v i

/-- Pure states live on the boundary sphere. -/
def IsPureBloch (v : BlochVector) : Prop :=
  blochNormSq v = 1

/-- Strictly mixed states live inside the ball. -/
def IsMixedBloch (v : BlochVector) : Prop :=
  blochNormSq v < 1

/-- The totally mixed/isotropic center. -/
def blochCenter : BlochVector :=
  fun _ => 0

@[simp] theorem blochCenter_normSq : blochNormSq blochCenter = 0 := by
  simp [blochNormSq, blochCenter]

/-- The isotropic center is strictly inside the Bloch ball. -/
theorem blochCenter_mixed : IsMixedBloch blochCenter := by
  norm_num [IsMixedBloch, blochCenter_normSq]

/-- Affine mixing between two Bloch vectors. -/
def blochMix (t : ℝ) (v w : BlochVector) : BlochVector :=
  fun i => t * v i + (1 - t) * w i

@[simp] theorem blochMix_zero_left (v : BlochVector) : blochMix 0 v blochCenter = blochCenter := by
  funext i
  simp [blochMix, blochCenter]

@[simp] theorem blochMix_one_left (v : BlochVector) : blochMix 1 v blochCenter = v := by
  funext i
  simp [blochMix, blochCenter]

end SplitClifford
