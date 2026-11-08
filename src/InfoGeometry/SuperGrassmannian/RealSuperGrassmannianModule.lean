import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Scalar 1|1 Graded Algebra and Diagonal Quotient Identities

Module: `InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule`

This file develops an explicit scalar-entry $1|1$ graded algebra over a commutative
ring. `SuperMatrix R` is a four-entry carrier with scalar multiplication; it is
not a general endomorphism algebra on half-spinor spaces and is not connected
here to the split-Clifford tower by a representation theorem. The results below
are conditional algebraic identities in this scalar model.

1. **Even and Odd Projections & Direct Sum Splitting**:
   - $\operatorname{evenPart}(M) = \begin{pmatrix} A & 0 \\ 0 & D \end{pmatrix}$
   - $\operatorname{oddPart}(M) = \begin{pmatrix} 0 & B \\ C & 0 \end{pmatrix}$
   - $M = \operatorname{evenPart}(M) + \operatorname{oddPart}(M)$
   - $\mathbb{Z}_2$-grading: even × even = even, odd × odd = even, even × odd = odd, odd × even = odd.
2. **Scalar Supertrace**:
   - $\operatorname{str}(M) = A - D$.
   - Annihilation on odd blocks: $\operatorname{str}(\operatorname{oddPart}(M)) = 0$.
   - Here the superbracket identity follows by commutative-ring rearrangement of scalar entries. The separate `RealSuperGrassmannianOperatorBlocks` bridge proves the corresponding trace identity for finite matrix operator blocks.
3. **Diagonal Scalar Projectors**: idempotence and the scalar difference formula for a diagonal pair.
4. **Diagonal Quotient**: `berezinianEven` is the total function $A/D$ on stored entries. Its multiplicativity result is the quotient identity under the stated evenness and nonzero-$D$ hypotheses; this file does not define a general supermatrix Berezinian.
5. **Entrywise Scalar Diagonal Exponential**: `expEven` constructs a diagonal pair of real scalar exponentials, with its quotient identity proved by `Real.exp_sub`.
6. **Scalar Pair Action**: `SuperMatrix R` acts on `SuperVector R = R \times R`; grading preservation/reversal and associativity are proved for this scalar representation.
7. **Finite Operator-Block Results**: `RealSuperGrassmannianOperatorBlocks` bundles the finite matrix-block supertrace law, a noncommuting matrix-unit witness, and the existing determinant-ratio theorem for block-diagonal matrix exponentials.
8. **Certificates**: `ScalarOneOneGradedAlgebraCertificate` bundles exactly the scalar-entry identities. The separate finite operator-block certificate is checked alongside it in the integration suite; no equivalence to the Sato spinor tower or general off-diagonal Berezinian is asserted.
-/

namespace InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule

/-! ### 1. Parity and Koszul Sign -/

/-- Parity degrees for $\mathbb{Z}_2$-graded superalgebra. -/
inductive Parity where
  | even
  | odd
  deriving DecidableEq, Repr

namespace Parity

/-- Addition of parities modulo 2. -/
def add : Parity → Parity → Parity
  | .even, p => p
  | .odd, .even => .odd
  | .odd, .odd => .even

instance : Add Parity := ⟨add⟩

@[simp] theorem even_add (p : Parity) : Parity.even + p = p := rfl
@[simp] theorem odd_add_even : Parity.odd + Parity.even = Parity.odd := rfl
@[simp] theorem odd_add_odd : Parity.odd + Parity.odd = Parity.even := rfl

/-- Koszul sign factor $(-1)^{|x||y|}$. -/
def sign (R : Type*) [Ring R] : Parity → Parity → R
  | .odd, .odd => -1
  | _, _ => 1

end Parity

/-! ### 2. Scalar-Entry Graded 2x2 Array -/

/--
A scalar-entry $1|1$ array over a commutative ring. The entries occupy the
even/odd block positions, but are scalars rather than endomorphisms of spinor
spaces. General finite operator blocks and their trace cyclicity are formalized
in `RealSuperGrassmannianOperatorBlocks` using the NCG block owner.
-/
structure SuperMatrix (R : Type*) where
  A : R
  B : R
  C : R
  D : R
  deriving DecidableEq, Repr

/-- Concrete inhabited model of the scalar carrier over the real field. -/
def realScalarIdentityModel : SuperMatrix ℝ := ⟨1, 0, 0, 1⟩

namespace SuperMatrix

variable {R : Type*} [CommRing R]

@[ext]
theorem ext (X Y : SuperMatrix R)
    (hA : X.A = Y.A) (hB : X.B = Y.B)
    (hC : X.C = Y.C) (hD : X.D = Y.D) : X = Y := by
  cases X; cases Y; subst hA; subst hB; subst hC; subst hD; rfl

instance : Zero (SuperMatrix R) := ⟨⟨0, 0, 0, 0⟩⟩
instance : One (SuperMatrix R) := ⟨⟨1, 0, 0, 1⟩⟩
instance instInhabitedSuperMatrix : Inhabited (SuperMatrix R) := ⟨1⟩
instance : Add (SuperMatrix R) := ⟨λ X Y => ⟨X.A + Y.A, X.B + Y.B, X.C + Y.C, X.D + Y.D⟩⟩
instance : Neg (SuperMatrix R) := ⟨λ X => ⟨-X.A, -X.B, -X.C, -X.D⟩⟩
instance : Sub (SuperMatrix R) := ⟨λ X Y => ⟨X.A - Y.A, X.B - Y.B, X.C - Y.C, X.D - Y.D⟩⟩
instance : Mul (SuperMatrix R) := ⟨λ X Y => ⟨X.A * Y.A + X.B * Y.C,
                                             X.A * Y.B + X.B * Y.D,
                                             X.C * Y.A + X.D * Y.C,
                                             X.C * Y.B + X.D * Y.D⟩⟩
instance : SMul R (SuperMatrix R) := ⟨λ r X => ⟨r * X.A, r * X.B, r * X.C, r * X.D⟩⟩

/-- Matrix power definition via induction. -/
def npow : ℕ → SuperMatrix R → SuperMatrix R
  | 0, _ => 1
  | n + 1, M => M * npow n M

instance : Pow (SuperMatrix R) ℕ := ⟨λ M n => npow n M⟩

@[simp] theorem zero_A : (0 : SuperMatrix R).A = 0 := rfl
@[simp] theorem zero_B : (0 : SuperMatrix R).B = 0 := rfl
@[simp] theorem zero_C : (0 : SuperMatrix R).C = 0 := rfl
@[simp] theorem zero_D : (0 : SuperMatrix R).D = 0 := rfl

@[simp] theorem one_A : (1 : SuperMatrix R).A = 1 := rfl
@[simp] theorem one_B : (1 : SuperMatrix R).B = 0 := rfl
@[simp] theorem one_C : (1 : SuperMatrix R).C = 0 := rfl
@[simp] theorem one_D : (1 : SuperMatrix R).D = 1 := rfl

@[simp] theorem add_A (X Y : SuperMatrix R) : (X + Y).A = X.A + Y.A := rfl
@[simp] theorem add_B (X Y : SuperMatrix R) : (X + Y).B = X.B + Y.B := rfl
@[simp] theorem add_C (X Y : SuperMatrix R) : (X + Y).C = X.C + Y.C := rfl
@[simp] theorem add_D (X Y : SuperMatrix R) : (X + Y).D = X.D + Y.D := rfl

@[simp] theorem sub_A (X Y : SuperMatrix R) : (X - Y).A = X.A - Y.A := rfl
@[simp] theorem sub_B (X Y : SuperMatrix R) : (X - Y).B = X.B - Y.B := rfl
@[simp] theorem sub_C (X Y : SuperMatrix R) : (X - Y).C = X.C - Y.C := rfl
@[simp] theorem sub_D (X Y : SuperMatrix R) : (X - Y).D = X.D - Y.D := rfl

@[simp] theorem neg_A (X : SuperMatrix R) : (-X).A = -X.A := rfl
@[simp] theorem neg_B (X : SuperMatrix R) : (-X).B = -X.B := rfl
@[simp] theorem neg_C (X : SuperMatrix R) : (-X).C = -X.C := rfl
@[simp] theorem neg_D (X : SuperMatrix R) : (-X).D = -X.D := rfl

@[simp] theorem mul_A (X Y : SuperMatrix R) : (X * Y).A = X.A * Y.A + X.B * Y.C := rfl
@[simp] theorem mul_B (X Y : SuperMatrix R) : (X * Y).B = X.A * Y.B + X.B * Y.D := rfl
@[simp] theorem mul_C (X Y : SuperMatrix R) : (X * Y).C = X.C * Y.A + X.D * Y.C := rfl
@[simp] theorem mul_D (X Y : SuperMatrix R) : (X * Y).D = X.C * Y.B + X.D * Y.D := rfl

@[simp] theorem smul_A (r : R) (X : SuperMatrix R) : (r • X).A = r * X.A := rfl
@[simp] theorem smul_B (r : R) (X : SuperMatrix R) : (r • X).B = r * X.B := rfl
@[simp] theorem smul_C (r : R) (X : SuperMatrix R) : (r • X).C = r * X.C := rfl
@[simp] theorem smul_D (r : R) (X : SuperMatrix R) : (r • X).D = r * X.D := rfl

@[simp] theorem pow_zero (M : SuperMatrix R) : M ^ 0 = 1 := rfl
@[simp] theorem pow_succ (M : SuperMatrix R) (n : ℕ) : M ^ (n + 1) = M * (M ^ n) := rfl

theorem pow_two (M : SuperMatrix R) : M ^ 2 = M * M := by
  change M * (M * 1) = M * M
  ext <;> (dsimp; ring)

theorem mul_assoc (X Y Z : SuperMatrix R) : (X * Y) * Z = X * (Y * Z) := by
  ext <;> (dsimp; ring)

theorem one_mul (X : SuperMatrix R) : 1 * X = X := by
  ext <;> (dsimp; ring)

theorem mul_one (X : SuperMatrix R) : X * 1 = X := by
  ext <;> (dsimp; ring)

theorem left_distrib (X Y Z : SuperMatrix R) : X * (Y + Z) = X * Y + X * Z := by
  ext <;> (dsimp; ring)

theorem right_distrib (X Y Z : SuperMatrix R) : (X + Y) * Z = X * Z + Y * Z := by
  ext <;> (dsimp; ring)

/-! ### 3. Graded Projections and Homogeneity -/

/-- Even projection extracting diagonal blocks: !![A, 0; 0, D]. -/
def evenPart (M : SuperMatrix R) : SuperMatrix R :=
  ⟨M.A, 0, 0, M.D⟩

/-- Odd projection extracting off-diagonal blocks: !![0, B; C, 0]. -/
def oddPart (M : SuperMatrix R) : SuperMatrix R :=
  ⟨0, M.B, M.C, 0⟩

/-- Direct sum decomposition: $M = \operatorname{evenPart}(M) + \operatorname{oddPart}(M)$. -/
theorem even_add_odd (M : SuperMatrix R) : evenPart M + oddPart M = M := by
  ext <;> (dsimp [evenPart, oddPart]; ring)

/-- Predicate for even homogeneous supermatrices (block-diagonal). -/
def isEven (M : SuperMatrix R) : Prop :=
  M.B = 0 ∧ M.C = 0

/-- Predicate for odd homogeneous supermatrices (off-diagonal). -/
def isOdd (M : SuperMatrix R) : Prop :=
  M.A = 0 ∧ M.D = 0

/-- General parity homogeneity predicate. -/
def isHomogeneous (p : Parity) (M : SuperMatrix R) : Prop :=
  match p with
  | .even => isEven M
  | .odd => isOdd M

theorem evenPart_is_even (M : SuperMatrix R) : isEven (evenPart M) :=
  ⟨rfl, rfl⟩

theorem oddPart_is_odd (M : SuperMatrix R) : isOdd (oddPart M) :=
  ⟨rfl, rfl⟩

theorem evenPart_even (M : SuperMatrix R) (h : isEven M) : evenPart M = M := by
  ext
  · rfl
  · dsimp [evenPart]; exact h.1.symm
  · dsimp [evenPart]; exact h.2.symm
  · rfl

theorem oddPart_even (M : SuperMatrix R) (h : isEven M) : oddPart M = 0 := by
  ext
  · rfl
  · dsimp [oddPart]; exact h.1
  · dsimp [oddPart]; exact h.2
  · rfl

theorem evenPart_odd (M : SuperMatrix R) (h : isOdd M) : evenPart M = 0 := by
  ext
  · dsimp [evenPart]; exact h.1
  · rfl
  · rfl
  · dsimp [evenPart]; exact h.2

theorem oddPart_odd (M : SuperMatrix R) (h : isOdd M) : oddPart M = M := by
  ext
  · dsimp [oddPart]; exact h.1.symm
  · rfl
  · rfl
  · dsimp [oddPart]; exact h.2.symm

/-- Idempotence of evenPart projection. -/
theorem evenPart_idempotent (M : SuperMatrix R) : evenPart (evenPart M) = evenPart M := by
  ext <;> (dsimp [evenPart]; try rfl)

/-- Idempotence of oddPart projection. -/
theorem oddPart_idempotent (M : SuperMatrix R) : oddPart (oddPart M) = oddPart M := by
  ext <;> (dsimp [oddPart]; try rfl)

/-- Orthogonality of evenPart and oddPart. -/
theorem evenPart_oddPart (M : SuperMatrix R) : evenPart (oddPart M) = 0 := by
  ext <;> (dsimp [evenPart, oddPart]; try rfl)

/-- Orthogonality of oddPart and evenPart. -/
theorem oddPart_evenPart (M : SuperMatrix R) : oddPart (evenPart M) = 0 := by
  ext <;> (dsimp [evenPart, oddPart]; try rfl)

/-- Product of two even supermatrices is even. -/
theorem even_mul_even (M N : SuperMatrix R) (hM : isEven M) (hN : isEven N) :
    isEven (M * N) := by
  rcases hM with ⟨hMB, hMC⟩
  rcases hN with ⟨hNB, hNC⟩
  constructor
  · dsimp; rw [hMB, hNB]; ring
  · dsimp; rw [hMC, hNC]; ring

/-- Product of two odd supermatrices is even ($\mathbb{Z}_2$ grading rule: $1 + 1 \equiv 0$). -/
theorem odd_mul_odd (M N : SuperMatrix R) (hM : isOdd M) (hN : isOdd N) :
    isEven (M * N) := by
  rcases hM with ⟨hMA, hMD⟩
  rcases hN with ⟨hNA, hND⟩
  constructor
  · dsimp; rw [hMA, hND]; ring
  · dsimp; rw [hMD, hNA]; ring

/-- Product of an even and an odd supermatrix is odd. -/
theorem even_mul_odd (M N : SuperMatrix R) (hM : isEven M) (hN : isOdd N) :
    isOdd (M * N) := by
  rcases hM with ⟨hMB, hMC⟩
  rcases hN with ⟨hNA, hND⟩
  constructor
  · dsimp; rw [hMB, hNA]; ring
  · dsimp; rw [hMC, hND]; ring

/-- Product of an odd and an even supermatrix is odd. -/
theorem odd_mul_even (M N : SuperMatrix R) (hM : isOdd M) (hN : isEven N) :
    isOdd (M * N) := by
  rcases hM with ⟨hMA, hMD⟩
  rcases hN with ⟨hNB, hNC⟩
  constructor
  · dsimp; rw [hMA, hNC]; ring
  · dsimp; rw [hMD, hNB]; ring

/-! ### 4. Graded Supertrace and Supercommutator Cyclicity -/

/-- Graded Supertrace: $\operatorname{str}(M) = A - D$. -/
def supertrace (M : SuperMatrix R) : R :=
  M.A - M.D

theorem supertrace_zero : supertrace (0 : SuperMatrix R) = 0 := by
  dsimp [supertrace]; ring

theorem supertrace_add (M N : SuperMatrix R) :
    supertrace (M + N) = supertrace M + supertrace N := by
  dsimp [supertrace]; ring

theorem supertrace_sub (M N : SuperMatrix R) :
    supertrace (M - N) = supertrace M - supertrace N := by
  dsimp [supertrace]; ring

theorem supertrace_neg (M : SuperMatrix R) :
    supertrace (-M) = -supertrace M := by
  simp only [supertrace, neg_A, neg_D]; ring

theorem supertrace_smul (r : R) (M : SuperMatrix R) :
    supertrace (r • M) = r * supertrace M := by
  dsimp [supertrace]; ring

theorem supertrace_odd (M : SuperMatrix R) (h : isOdd M) :
    supertrace M = 0 := by
  dsimp [supertrace]
  rw [h.1, h.2]
  ring

theorem supertrace_evenPart (M : SuperMatrix R) :
    supertrace (evenPart M) = supertrace M := by
  dsimp [supertrace, evenPart]

theorem supertrace_oddPart (M : SuperMatrix R) :
    supertrace (oddPart M) = 0 := by
  dsimp [supertrace, oddPart]; ring

/-- For even matrices, the supercommutator is the standard commutator $M N - N M$. -/
theorem supertrace_even_supercommutator (M N : SuperMatrix R)
    (hM : isEven M) (hN : isEven N) :
    supertrace (M * N - N * M) = 0 := by
  rcases hM with ⟨hMB, hMC⟩
  rcases hN with ⟨hNB, hNC⟩
  dsimp [supertrace]
  rw [hMB, hMC, hNB, hNC]
  ring

/--
For odd matrices, the supercommutator is the anticommutator $M N + N M$.
Its supertrace vanishes identically by commutativity of the underlying ring:
$$(B_1 C_2 + B_2 C_1) - (C_1 B_2 + C_2 B_1) = 0$$
-/
theorem supertrace_odd_supercommutator (M N : SuperMatrix R)
    (hM : isOdd M) (hN : isOdd N) :
    supertrace (M * N + N * M) = 0 := by
  rcases hM with ⟨hMA, hMD⟩
  rcases hN with ⟨hNA, hND⟩
  dsimp [supertrace]
  rw [hMA, hMD, hNA, hND]
  ring

/-- For mixed even-odd pairs, the supercommutator is the commutator $M N - N M$. -/
theorem supertrace_mixed_supercommutator_even_odd (M N : SuperMatrix R)
    (hM : isEven M) (hN : isOdd N) :
    supertrace (M * N - N * M) = 0 := by
  rcases hM with ⟨hMB, hMC⟩
  rcases hN with ⟨hNA, hND⟩
  dsimp [supertrace]
  rw [hMB, hMC, hNA, hND]
  ring

/-- For mixed odd-even pairs, the supercommutator is the commutator $M N - N M$. -/
theorem supertrace_mixed_supercommutator_odd_even (M N : SuperMatrix R)
    (hM : isOdd M) (hN : isEven N) :
    supertrace (M * N - N * M) = 0 := by
  rcases hM with ⟨hMA, hMD⟩
  rcases hN with ⟨hNB, hNC⟩
  dsimp [supertrace]
  rw [hMA, hMD, hNB, hNC]
  ring

/-- Parity-tagged superbracket $[M, N]_s = M N - (-1)^{|M||N|} N M$. -/
def superbracket (pM pN : Parity) (M N : SuperMatrix R) : SuperMatrix R :=
  match pM, pN with
  | .odd, .odd => M * N + N * M
  | _, _ => M * N - N * M

/-- **Theorem**: The Graded Supertrace annihilates every homogeneous superbracket. -/
theorem supertrace_superbracket_eq_zero (pM pN : Parity) (M N : SuperMatrix R)
    (hM : isHomogeneous pM M) (hN : isHomogeneous pN N) :
    supertrace (superbracket pM pN M N) = 0 := by
  cases pM <;> cases pN
  · exact supertrace_even_supercommutator M N hM hN
  · exact supertrace_mixed_supercommutator_even_odd M N hM hN
  · exact supertrace_mixed_supercommutator_odd_even M N hM hN
  · exact supertrace_odd_supercommutator M N hM hN

/-! ### 5. Diagonal Scalar Idempotent Pairs -/

/-- A diagonal scalar pair with the idempotence calculation below. -/
def diagonalProjector (P_plus P_minus : R) : SuperMatrix R :=
  ⟨P_plus, 0, 0, P_minus⟩

theorem projector_is_even (P_plus P_minus : R) :
    isEven (diagonalProjector P_plus P_minus) :=
  ⟨rfl, rfl⟩

/-- **Theorem**: Idempotence of the diagonal super-projector: $P_+^2 = P_+$ and $P_-^2 = P_- \implies P^2 = P$. -/
theorem projector_idempotent (P_plus P_minus : R)
    (hplus : P_plus ^ 2 = P_plus) (hminus : P_minus ^ 2 = P_minus) :
    (diagonalProjector P_plus P_minus) ^ 2 = diagonalProjector P_plus P_minus := by
  rw [pow_two]
  ext
  · change P_plus * P_plus + 0 * 0 = P_plus
    have h2 : P_plus * P_plus = P_plus ^ 2 := by ring
    rw [h2, hplus]; ring
  · change P_plus * 0 + 0 * P_minus = 0; ring
  · change 0 * P_plus + P_minus * 0 = 0; ring
  · change 0 * 0 + P_minus * P_minus = P_minus
    have h2 : P_minus * P_minus = P_minus ^ 2 := by ring
    rw [h2, hminus]; ring

/-- **Theorem**: Supertrace of the projector computes the graded virtual index: $\operatorname{str}(P) = P_+ - P_-$. -/
theorem projector_supertrace (P_plus P_minus : R) :
    supertrace (diagonalProjector P_plus P_minus) = P_plus - P_minus := by
  dsimp [supertrace, diagonalProjector]

/-- For equal scalar diagonal entries, the scalar supertrace is zero. -/
theorem balanced_projector_supertrace_zero (P_val : R) :
    supertrace (diagonalProjector P_val P_val) = 0 := by
  dsimp [supertrace, diagonalProjector]; ring

/-! ### 6. Diagonal Quotient and Entrywise Exponential Identities -/

/-- Total scalar quotient of the diagonal entries; no general Berezinian is defined here. -/
noncomputable def berezinianEven {K : Type*} [Field K] (M : SuperMatrix K) : K :=
  M.A / M.D

/-- The diagonal quotient of the identity array is one. -/
theorem berezinian_one {K : Type*} [Field K] :
    berezinianEven (1 : SuperMatrix K) = 1 := by
  dsimp [berezinianEven]; simp

/-- The diagonal quotient is multiplicative for even arrays when both denominator entries are nonzero. -/
theorem berezinian_mul_even {K : Type*} [Field K] (M N : SuperMatrix K)
    (hM : isEven M) (hN : isEven N) (hMd : M.D ≠ 0) (hNd : N.D ≠ 0) :
    berezinianEven (M * N) = berezinianEven M * berezinianEven N := by
  rcases hM with ⟨hMB, hMC⟩
  rcases hN with ⟨hNB, hNC⟩
  dsimp [berezinianEven]
  rw [hMB, hMC, hNB, hNC]
  simp only [mul_zero, add_zero, zero_add]
  exact mul_div_mul_comm M.A N.A M.D N.D

/-- The scalar diagonal quotient of a balanced pair is one. -/
theorem balanced_berezinian_one {K : Type*} [Field K] (c : K) (hc : c ≠ 0) :
    berezinianEven (⟨c, 0, 0, c⟩ : SuperMatrix K) = 1 := by
  dsimp [berezinianEven]
  exact div_self hc

/-- Upper off-diagonal scalar shear in the `1|1` array model. -/
def upperShear (b : R) : SuperMatrix R :=
  ⟨1, b, 0, 1⟩

/-- Lower off-diagonal scalar shear in the `1|1` array model. -/
def lowerShear (c : R) : SuperMatrix R :=
  ⟨1, 0, c, 1⟩

/-- The even projection of the upper scalar shear is the identity array. -/
theorem upperShear_evenPart (b : R) : evenPart (upperShear b) = 1 := by
  ext <;> (dsimp [upperShear, evenPart]; try rfl)

/-- The even projection of the lower scalar shear is the identity array. -/
theorem lowerShear_evenPart (c : R) : evenPart (lowerShear c) = 1 := by
  ext <;> (dsimp [lowerShear, evenPart]; try rfl)

/-- Entrywise diagonal construction from the two real scalar exponentials. -/
noncomputable def expEven (M : SuperMatrix ℝ) : SuperMatrix ℝ :=
  ⟨Real.exp M.A, 0, 0, Real.exp M.D⟩

theorem expEven_is_even (M : SuperMatrix ℝ) : isEven (expEven M) :=
  ⟨rfl, rfl⟩

/--
**Theorem**: The quotient of the entrywise diagonal exponential equals the
exponential of the scalar diagonal difference. This is not a matrix
exponential theorem.
-/
theorem berezinian_exp_even (M : SuperMatrix ℝ) :
    berezinianEven (expEven M) = Real.exp (supertrace (evenPart M)) := by
  dsimp [berezinianEven, expEven, supertrace, evenPart]
  rw [Real.exp_sub]

/--
**Theorem (Supertraceless Volume Invariance)**:
When the scalar diagonal difference is zero, the quotient of the entrywise
diagonal exponential is one.
-/
theorem supertraceless_berezinian_exp_one (M : SuperMatrix ℝ)
    (hstr : supertrace (evenPart M) = 0) :
    berezinianEven (expEven M) = 1 := by
  rw [berezinian_exp_even, hstr, Real.exp_zero]

end SuperMatrix

/-! ### 7. Graded Action on a Scalar Pair -/

/--
Carrier `R × R` with coordinates assigned to even and odd positions.
-/
structure SuperVector (R : Type*) where
  plus : R
  minus : R
  deriving DecidableEq, Repr

/-- Concrete inhabited model of the scalar-pair carrier over the real field. -/
def realScalarPairModel : SuperVector ℝ := ⟨1, 0⟩

namespace SuperVector

variable {R : Type*} [CommRing R]

@[ext]
theorem ext (u v : SuperVector R) (hp : u.plus = v.plus) (hm : u.minus = v.minus) : u = v := by
  cases u; cases v; subst hp; subst hm; rfl

instance : Zero (SuperVector R) := ⟨⟨0, 0⟩⟩
instance instInhabitedSuperVector : Inhabited (SuperVector R) := ⟨⟨0, 0⟩⟩
instance : Add (SuperVector R) := ⟨λ u v => ⟨u.plus + v.plus, u.minus + v.minus⟩⟩
instance : Neg (SuperVector R) := ⟨λ u => ⟨-u.plus, -u.minus⟩⟩
instance : Sub (SuperVector R) := ⟨λ u v => ⟨u.plus - v.plus, u.minus - v.minus⟩⟩
instance : SMul R (SuperVector R) := ⟨λ r v => ⟨r * v.plus, r * v.minus⟩⟩

@[simp] theorem zero_plus : (0 : SuperVector R).plus = 0 := rfl
@[simp] theorem zero_minus : (0 : SuperVector R).minus = 0 := rfl

@[simp] theorem add_plus (u v : SuperVector R) : (u + v).plus = u.plus + v.plus := rfl
@[simp] theorem add_minus (u v : SuperVector R) : (u + v).minus = u.minus + v.minus := rfl

@[simp] theorem sub_plus (u v : SuperVector R) : (u - v).plus = u.plus - v.plus := rfl
@[simp] theorem sub_minus (u v : SuperVector R) : (u - v).minus = u.minus - v.minus := rfl

@[simp] theorem smul_plus (r : R) (v : SuperVector R) : (r • v).plus = r * v.plus := rfl
@[simp] theorem smul_minus (r : R) (v : SuperVector R) : (r • v).minus = r * v.minus := rfl

end SuperVector

/--
Action-like operation of the scalar array on a scalar pair:
$$M \cdot v = \begin{pmatrix} A v_+ + B v_- \\ C v_+ + D v_- \end{pmatrix}$$
-/
def act {R : Type*} [CommRing R] (M : SuperMatrix R) (v : SuperVector R) : SuperVector R :=
  ⟨M.A * v.plus + M.B * v.minus, M.C * v.plus + M.D * v.minus⟩

namespace SuperModule

variable {R : Type*} [CommRing R]

theorem act_one (v : SuperVector R) : act 1 v = v := by
  ext <;> (dsimp [act]; ring)

/-- **Theorem**: Associativity of the module action $(M N) \cdot v = M \cdot (N \cdot v)$. -/
theorem act_mul (M N : SuperMatrix R) (v : SuperVector R) :
    act (M * N) v = act M (act N v) := by
  ext <;> (dsimp [act]; ring)

/-- **Theorem**: Left linearity over matrix addition. -/
theorem act_add (M N : SuperMatrix R) (v : SuperVector R) :
    act (M + N) v = act M v + act N v := by
  ext <;> (dsimp [act]; ring)

/-- **Theorem**: Right linearity over vector addition. -/
theorem act_vec_add (M : SuperMatrix R) (u v : SuperVector R) :
    act M (u + v) = act M u + act M v := by
  ext <;> (dsimp [act]; ring)

/-- For a scalar pair with zero odd coordinate, an even array preserves that coordinate. -/
theorem act_even_preserves_grading_plus (M : SuperMatrix R) (v : SuperVector R)
    (hM : SuperMatrix.isEven M) (hv : v.minus = 0) :
    (act M v).minus = 0 := by
  rcases hM with ⟨_, hMC⟩
  dsimp [act]
  rw [hMC, hv]
  ring

/-- For a scalar pair with zero even coordinate, an even array preserves that coordinate. -/
theorem act_even_preserves_grading_minus (M : SuperMatrix R) (v : SuperVector R)
    (hM : SuperMatrix.isEven M) (hv : v.plus = 0) :
    (act M v).plus = 0 := by
  rcases hM with ⟨hMB, _⟩
  dsimp [act]
  rw [hMB, hv]
  ring

/-- For a scalar pair with zero odd coordinate, an odd array maps into the odd coordinate. -/
theorem act_odd_reverses_grading_plus (M : SuperMatrix R) (v : SuperVector R)
    (hM : SuperMatrix.isOdd M) (hv : v.minus = 0) :
    (act M v).plus = 0 := by
  rcases hM with ⟨hMA, _⟩
  dsimp [act]
  rw [hMA, hv]
  ring

/-- For a scalar pair with zero even coordinate, an odd array maps into the even coordinate. -/
theorem act_odd_reverses_grading_minus (M : SuperMatrix R) (v : SuperVector R)
    (hM : SuperMatrix.isOdd M) (hv : v.plus = 0) :
    (act M v).minus = 0 := by
  rcases hM with ⟨_, hMD⟩
  dsimp [act]
  rw [hMD, hv]
  ring

end SuperModule

/-! ### 8. Scalar-Model Certificate -/

/-- Certificate bundling the identities proved for this scalar-entry `1|1` model. -/
structure ScalarOneOneGradedAlgebraCertificate : Prop where
  -- 1. Graded decomposition
  even_odd_decomp : ∀ {R : Type*} [CommRing R] (M : SuperMatrix R),
    SuperMatrix.evenPart M + SuperMatrix.oddPart M = M
  evenPart_is_even : ∀ {R : Type*} [CommRing R] (M : SuperMatrix R),
    SuperMatrix.isEven (SuperMatrix.evenPart M)
  oddPart_is_odd : ∀ {R : Type*} [CommRing R] (M : SuperMatrix R),
    SuperMatrix.isOdd (SuperMatrix.oddPart M)
  -- 2. Graded multiplication rules
  even_mul_even : ∀ {R : Type*} [CommRing R] (M N : SuperMatrix R),
    SuperMatrix.isEven M → SuperMatrix.isEven N → SuperMatrix.isEven (M * N)
  odd_mul_odd : ∀ {R : Type*} [CommRing R] (M N : SuperMatrix R),
    SuperMatrix.isOdd M → SuperMatrix.isOdd N → SuperMatrix.isEven (M * N)
  even_mul_odd : ∀ {R : Type*} [CommRing R] (M N : SuperMatrix R),
    SuperMatrix.isEven M → SuperMatrix.isOdd N → SuperMatrix.isOdd (M * N)
  odd_mul_even : ∀ {R : Type*} [CommRing R] (M N : SuperMatrix R),
    SuperMatrix.isOdd M → SuperMatrix.isEven N → SuperMatrix.isOdd (M * N)
  -- 3. Graded supertrace linearity
  supertrace_add : ∀ {R : Type*} [CommRing R] (M N : SuperMatrix R),
    SuperMatrix.supertrace (M + N) = SuperMatrix.supertrace M + SuperMatrix.supertrace N
  supertrace_odd_vanish : ∀ {R : Type*} [CommRing R] (M : SuperMatrix R),
    SuperMatrix.isOdd M → SuperMatrix.supertrace M = 0
  -- 4. Supercommutator cyclicity
  supertrace_even_supercommutator : ∀ {R : Type*} [CommRing R] (M N : SuperMatrix R),
    SuperMatrix.isEven M → SuperMatrix.isEven N → SuperMatrix.supertrace (M * N - N * M) = 0
  supertrace_odd_supercommutator : ∀ {R : Type*} [CommRing R] (M N : SuperMatrix R),
    SuperMatrix.isOdd M → SuperMatrix.isOdd N → SuperMatrix.supertrace (M * N + N * M) = 0
  supertrace_mixed_supercommutator : ∀ {R : Type*} [CommRing R] (M N : SuperMatrix R),
    SuperMatrix.isEven M → SuperMatrix.isOdd N → SuperMatrix.supertrace (M * N - N * M) = 0
  -- 5. Diagonal scalar idempotent pairs
  projector_idempotent : ∀ {R : Type*} [CommRing R] (p q : R),
    p ^ 2 = p → q ^ 2 = q → (SuperMatrix.diagonalProjector p q) ^ 2 = SuperMatrix.diagonalProjector p q
  projector_supertrace : ∀ {R : Type*} [CommRing R] (p q : R),
    SuperMatrix.supertrace (SuperMatrix.diagonalProjector p q) = p - q
  balanced_projector_supertrace_zero : ∀ {R : Type*} [CommRing R] (p : R),
    SuperMatrix.supertrace (SuperMatrix.diagonalProjector p p) = 0
  -- 6. Diagonal quotient identities
  berezinian_mul : ∀ {K : Type*} [Field K] (M N : SuperMatrix K),
    SuperMatrix.isEven M → SuperMatrix.isEven N → M.D ≠ 0 → N.D ≠ 0 →
    SuperMatrix.berezinianEven (M * N) = SuperMatrix.berezinianEven M * SuperMatrix.berezinianEven N
  balanced_berezinian_one : ∀ {K : Type*} [Field K] (c : K),
    c ≠ 0 → SuperMatrix.berezinianEven (⟨c, 0, 0, c⟩ : SuperMatrix K) = 1
  berezinian_exp_supertrace : ∀ (M : SuperMatrix ℝ),
    SuperMatrix.berezinianEven (SuperMatrix.expEven M) = Real.exp (SuperMatrix.supertrace (SuperMatrix.evenPart M))
  supertraceless_berezinian_exp_one : ∀ (M : SuperMatrix ℝ),
    SuperMatrix.supertrace (SuperMatrix.evenPart M) = 0 →
    SuperMatrix.berezinianEven (SuperMatrix.expEven M) = 1
  -- 7. Graded module action
  act_mul : ∀ {R : Type*} [CommRing R] (M N : SuperMatrix R) (v : SuperVector R),
    act (M * N) v = act M (act N v)
  act_even_preserves_grading : ∀ {R : Type*} [CommRing R] (M : SuperMatrix R) (v : SuperVector R),
    SuperMatrix.isEven M → v.minus = 0 → (act M v).minus = 0
  act_odd_reverses_grading : ∀ {R : Type*} [CommRing R] (M : SuperMatrix R) (v : SuperVector R),
    SuperMatrix.isOdd M → v.minus = 0 → (act M v).plus = 0

/-- Assemble the proved scalar `1|1` graded-algebra identities into their certificate. -/
theorem compile_scalar_one_one_graded_algebra : ScalarOneOneGradedAlgebraCertificate where
  even_odd_decomp := λ M => SuperMatrix.even_add_odd M
  evenPart_is_even := λ M => SuperMatrix.evenPart_is_even M
  oddPart_is_odd := λ M => SuperMatrix.oddPart_is_odd M
  even_mul_even := λ M N hM hN => SuperMatrix.even_mul_even M N hM hN
  odd_mul_odd := λ M N hM hN => SuperMatrix.odd_mul_odd M N hM hN
  even_mul_odd := λ M N hM hN => SuperMatrix.even_mul_odd M N hM hN
  odd_mul_even := λ M N hM hN => SuperMatrix.odd_mul_even M N hM hN
  supertrace_add := λ M N => SuperMatrix.supertrace_add M N
  supertrace_odd_vanish := λ M hM => SuperMatrix.supertrace_odd M hM
  supertrace_even_supercommutator := λ M N hM hN => SuperMatrix.supertrace_even_supercommutator M N hM hN
  supertrace_odd_supercommutator := λ M N hM hN => SuperMatrix.supertrace_odd_supercommutator M N hM hN
  supertrace_mixed_supercommutator := λ M N hM hN => SuperMatrix.supertrace_mixed_supercommutator_even_odd M N hM hN
  projector_idempotent := λ p q hp hq => SuperMatrix.projector_idempotent p q hp hq
  projector_supertrace := λ p q => SuperMatrix.projector_supertrace p q
  balanced_projector_supertrace_zero := λ p => SuperMatrix.balanced_projector_supertrace_zero p
  berezinian_mul := λ M N hM hN hMd hNd => SuperMatrix.berezinian_mul_even M N hM hN hMd hNd
  balanced_berezinian_one := λ c hc => SuperMatrix.balanced_berezinian_one c hc
  berezinian_exp_supertrace := λ M => SuperMatrix.berezinian_exp_even M
  supertraceless_berezinian_exp_one := λ M hstr => SuperMatrix.supertraceless_berezinian_exp_one M hstr
  act_mul := λ M N v => SuperModule.act_mul M N v
  act_even_preserves_grading := λ M v hM hv => SuperModule.act_even_preserves_grading_plus M v hM hv
  act_odd_reverses_grading := λ M v hM hv => SuperModule.act_odd_reverses_grading_plus M v hM hv

end InfoGeometry.SuperGrassmannian.RealSuperGrassmannianModule
