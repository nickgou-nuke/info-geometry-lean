/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import InfoGeometry.Twistor.PenrosePolynomialCCR
import InfoGeometry.Twistor.PerjesMomentOperator

/-!
# Algebraic identities behind two parts of the twistor/Kerr proposal

This file proves only identities on their stated carriers. It contains
noncommutative ring identities, a concrete CCR specialization in the
endomorphism algebra of four-variable polynomials, and the coordinate
factorization used in oblate spheroidal coordinates over a commutative ring.
It also constructs a coordinate-level real `4 × 4` Kerr--Schild metric and
its inverse and determinant. It does not construct a global Lorentzian
manifold, prove Einstein's equations or a global shear-free congruence, or
identify a Penrose sheaf cohomology group.
-/

namespace InfoGeometry.Twistor.KerrAlgebraicCore

open scoped BigOperators

section SpinorFactorization

variable {R : Type*} [CommRing R]

/-- The determinant convention used by the proposed spinor factorization. -/
def det2 (a00 a01 a10 a11 : R) : R := a00 * a11 - a01 * a10

/-- With the exact determinant factors and spinor-index conventions in the
submitted fragment, the Pauli--Lubanski determinant factorization is a
polynomial identity over every commutative ring. -/
theorem pauli_lubanski_spinor_determinant_factorization
    (w10 w11 pi10 pi11 w20 w21 pi20 pi21 : R)
    (bp10 bp11 bw10 bw11 bp20 bp21 bw20 bw21 : R) :
    let mu12 := pi10 * pi21 - pi20 * pi11
    let bmu12 := bp10 * bp21 - bp20 * bp11
    let H11 := w10 * bp10 + w11 * bp11 + pi10 * bw10 + pi11 * bw11
    let H12 := w10 * bp20 + w11 * bp21 + pi10 * bw20 + pi11 * bw21
    let H21 := w20 * bp10 + w21 * bp11 + pi20 * bw10 + pi21 * bw11
    let H22 := w20 * bp20 + w21 * bp21 + pi20 * bw20 + pi21 * bw21
    let p00 := bp10 * pi10 + bp20 * pi20
    let p01 := bp10 * pi11 + bp20 * pi21
    let p10 := bp11 * pi10 + bp21 * pi20
    let p11 := bp11 * pi11 + bp21 * pi21
    let pu00 := p10
    let pu01 := p11
    let pu10 := -p00
    let pu11 := -p01
    let pv00 := p01
    let pv01 := -p00
    let pv10 := p11
    let pv11 := -p10
    let mu00 := -2 * (w11 * bp10 + w21 * bp20)
    let mu11 := 2 * (w10 * bp11 + w20 * bp21)
    let mu01 := (w10 * bp10 - w11 * bp11) + (w20 * bp20 - w21 * bp21)
    let bmu00 := -2 * (bw11 * pi10 + bw21 * pi20)
    let bmu11 := 2 * (bw10 * pi11 + bw20 * pi21)
    let bmu01 := (bw10 * pi10 - bw11 * pi11) + (bw20 * pi20 - bw21 * pi21)
    let W00 := mu00 * pu00 + mu01 * pu10 + bmu00 * pv00 + bmu01 * pv01
    let W01 := mu00 * pu01 + mu01 * pu11 + bmu01 * pv00 + bmu11 * pv01
    let W10 := mu01 * pu00 + mu11 * pu10 + bmu00 * pv10 + bmu01 * pv11
    let W11 := mu01 * pu01 + mu11 * pu11 + bmu01 * pv10 + bmu11 * pv11
    det2 W00 W01 W10 W11 =
      -(mu12 * bmu12 * ((H11 - H22) * (H11 - H22) + 4 * H12 * H21)) := by
  dsimp [det2]
  ring

end SpinorFactorization

section NoncommutativeOperatorIdentity

variable {B : Type*} [Ring B]

/-- Matrix multiplication in this file is genuinely noncommutative: the two
standard off-diagonal matrix units in `Mat₂(B)` have distinct ordered
products whenever the coefficient ring is nontrivial. -/
theorem matTwo_offDiagonalUnits_noncommute [Nontrivial B] :
    ∃ matI matJ : Matrix (Fin 2) (Fin 2) B,
      matI * matJ ≠ matJ * matI := by
  refine ⟨!![(0 : B), 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Real `4 × 4` matrix multiplication is genuinely noncommutative. -/
theorem matFour_offDiagonalUnits_noncommute :
    ∃ matI matJ : Matrix (Fin 4) (Fin 4) ℝ,
      matI * matJ ≠ matJ * matI := by
  refine ⟨(Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ),
    (Matrix.single (1 : Fin 4) (0 : Fin 4) (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ), ?_⟩
  intro h
  have h₁ : (Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) *
      Matrix.single (1 : Fin 4) (0 : Fin 4) (1 : ℝ) =
      Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℝ) := by
    simp [Matrix.single_mul_single_same]
  have h₂ : (Matrix.single (1 : Fin 4) (0 : Fin 4) (1 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ) *
      Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℝ) =
      Matrix.single (1 : Fin 4) (1 : Fin 4) (1 : ℝ) := by
    simp [Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [Matrix.single_apply] at h00

/-- The ordering defect becomes a distinguished additive grade, indexed by
the number of modes. -/
def centralOrderingGrade {ι : Type*} [Fintype ι] (hbar : B) : B :=
  Fintype.card ι • hbar

/-- If the basic commutator is central, its finite-mode ordering grade is
central as well. This isolates the center direction that a trace-free
symmetry sector removes. -/
theorem centralOrderingGrade_commutes {ι : Type*} [Fintype ι]
    (hbar : B) (hcentral : ∀ b : B, hbar * b = b * hbar) :
    ∀ b : B, centralOrderingGrade (ι := ι) hbar * b =
      b * centralOrderingGrade (ι := ι) hbar := by
  intro b
  have hn : ∀ n : ℕ, n • hbar * b = b * (n • hbar) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hnsmul : (n + 1) • hbar = n • hbar + hbar := by
        simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [hnsmul, add_mul, mul_add, ih, hcentral b]
  exact hn (Fintype.card ι)

/-- The difference between the square of the anticommutator and the square of
the commutator is the sum of the two noncommuting sandwich terms. -/
theorem anticommutator_sq_sub_commutator_sq (x y : B) :
    (x * y + y * x) * (x * y + y * x) -
        (x * y - y * x) * (x * y - y * x) =
      2 • (x * (y * y) * x + y * (x * x) * y) := by
  simp only [two_smul]
  simp only [add_mul, mul_add, sub_mul, mul_sub, mul_assoc]
  abel

/-- If both generators square to zero, the anticommutator square and
commutator square agree. This conclusion does not assert that either square
is itself zero. -/
theorem anticommutator_sq_eq_commutator_sq_of_sq_eq_zero
    (x y : B) (hx : x * x = 0) (hy : y * y = 0) :
    (x * y + y * x) * (x * y + y * x) =
      (x * y - y * x) * (x * y - y * x) := by
  have h := anticommutator_sq_sub_commutator_sq x y
  rw [hy, hx] at h
  have hzero :
      (x * y + y * x) * (x * y + y * x) -
          (x * y - y * x) * (x * y - y * x) = 0 := by
    simpa using h
  exact sub_eq_zero.mp hzero

/-- For any finite set of modes, the accumulated ordering defect is its
cardinality times the common commutator. The four-mode Weyl shift is the
specialization `ι = Fin 4`; this form exposes the defect as a graded central
charge indexed by the mode space. -/
theorem finite_channel_commutator_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z w : ι → B) (hbar : B)
    (hcanonical : ∀ i, z i * w i - w i * z i = hbar) :
    (∑ i : ι, (z i * w i - w i * z i)) = Fintype.card ι • hbar := by
  calc
    (∑ i : ι, (z i * w i - w i * z i)) = ∑ _i : ι, hbar := by
      apply Finset.sum_congr rfl
      intro i _
      exact hcanonical i
    _ = Fintype.card ι • hbar := by simp

/-- Finite-mode Weyl ordering separates into its normal-ordered part and the
explicit mode-count defect. This equation is the generic form of the `4ℏ`
shift; it does not assert a representation of a symmetry group. -/
theorem finite_channel_weyl_ordering_shift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z w : ι → B) (hbar : B)
    (hcanonical : ∀ i, z i * w i - w i * z i = hbar) :
    (∑ i : ι, (z i * w i + w i * z i)) =
      2 • (∑ i : ι, w i * z i) + Fintype.card ι • hbar := by
  have hsum := finite_channel_commutator_sum z w hbar hcanonical
  calc
    (∑ i : ι, (z i * w i + w i * z i)) =
        (∑ i : ι, (w i * z i + w i * z i)) +
          (∑ i : ι, (z i * w i - w i * z i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      abel
    _ = 2 • (∑ i : ι, w i * z i) + Fintype.card ι • hbar := by
      rw [hsum, Finset.sum_add_distrib]
      simp only [two_smul]

/-- Weyl-ordered operator coefficients for a finite set of modes and two
twistor channels. -/
def twoTwistorWeylMatrix {n : ℕ} (z w : Fin 2 → Fin n → B) :
    Matrix (Fin 2) (Fin 2) B := fun a b =>
      ∑ i : Fin n, (z a i * w b i + w b i * z a i)

/-- Normal ordering uses the same channel and mode indices as the Weyl form. -/
def twoTwistorNormalMatrix {n : ℕ} (z w : Fin 2 → Fin n → B) :
    Matrix (Fin 2) (Fin 2) B := fun a b =>
      ∑ i : Fin n, (w b i * z a i + w b i * z a i)

/-- A scalar matrix records the central direction in the two-channel
operator algebra. -/
def centralScalarMatrix (c : B) : Matrix (Fin 2) (Fin 2) B :=
  fun a b => if a = b then c else 0

/-- A scalar diagonal matrix is genuinely central in the matrix algebra when
its coefficient is central in the (possibly noncommutative) coefficient
ring. The hypothesis is explicit; no commutativity of `B` is assumed. -/
theorem centralScalarMatrix_commutes {c : B}
    (hc : ∀ b : B, c * b = b * c) (M : Matrix (Fin 2) (Fin 2) B) :
    centralScalarMatrix c * M = M * centralScalarMatrix c := by
  ext i j
  simp only [Matrix.mul_apply, centralScalarMatrix]
  fin_cases i <;> fin_cases j <;>
    simp [hc]

/-- Under the channelwise canonical commutation relations, the full ordering
defect is the central matrix `numberOfModes * hbar * I₂`. The off-diagonal
commutators are included as hypotheses and vanish when the channels differ. -/
theorem two_twistor_weyl_ordering_matrix_defect
    {n : ℕ} (z w : Fin 2 → Fin n → B) (hbar : B)
    (hcanonical : ∀ a b i,
      z a i * w b i - w b i * z a i = if a = b then hbar else 0) :
    twoTwistorWeylMatrix z w - twoTwistorNormalMatrix z w =
      centralScalarMatrix ((Fintype.card (Fin n) : ℕ) • hbar) := by
  ext a b
  change (∑ i : Fin n, (z a i * w b i + w b i * z a i)) -
      ∑ i : Fin n, (w b i * z a i + w b i * z a i) =
    if a = b then (Fintype.card (Fin n) : ℕ) • hbar else 0
  calc
    _ = ∑ i : Fin n,
        (z a i * w b i + w b i * z a i -
          (w b i * z a i + w b i * z a i)) := by
      rw [← Finset.sum_sub_distrib]
    _ = ∑ i : Fin n, (z a i * w b i - w b i * z a i) := by
      apply Finset.sum_congr rfl
      intro i _
      abel
    _ = ∑ i : Fin n, (if a = b then hbar else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcanonical]
    _ = if a = b then (Fintype.card (Fin n) : ℕ) • hbar else 0 := by
      by_cases hab : a = b
      · subst b
        simp
      · simp [hab]

/-- If the basic commutator is central, then the full Weyl-versus-normal
ordering defect is central in the noncommutative two-channel matrix algebra.
This identifies the mode-count shift as a genuine center direction before
the trace-free readout removes it. -/
theorem two_twistor_ordering_defect_is_central
    {n : ℕ} (z w : Fin 2 → Fin n → B) (hbar : B)
    (hcentral : ∀ b : B, hbar * b = b * hbar)
    (hcanonical : ∀ a b i,
      z a i * w b i - w b i * z a i = if a = b then hbar else 0) :
    ∀ M : Matrix (Fin 2) (Fin 2) B,
      (twoTwistorWeylMatrix z w - twoTwistorNormalMatrix z w) * M =
        M * (twoTwistorWeylMatrix z w - twoTwistorNormalMatrix z w) := by
  intro M
  rw [two_twistor_weyl_ordering_matrix_defect z w hbar hcanonical]
  apply centralScalarMatrix_commutes
  intro b
  have hgrade := centralOrderingGrade_commutes (ι := Fin n) hbar hcentral b
  simpa [centralOrderingGrade] using hgrade

/-- Division-free trace-free readout for a two-channel matrix. It is twice
the ordinary trace-free part, so no inverse of `2` is required. -/
def scaledTraceFree2 (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix (Fin 2) (Fin 2) B :=
  M + M - Matrix.trace M • (1 : Matrix (Fin 2) (Fin 2) B)

/-- The trace-free readout forgets a central scalar matrix, while the scalar
matrix itself remains the separate ordering-anomaly grade. -/
theorem scaledTraceFree2_add_central (M : Matrix (Fin 2) (Fin 2) B)
    (c : B) :
    scaledTraceFree2 (M + centralScalarMatrix c) = scaledTraceFree2 M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scaledTraceFree2, centralScalarMatrix, Matrix.trace,
      Fin.sum_univ_two]

/-- Consequently Weyl and normal ordering agree after the division-free
trace-free readout, although their full matrices differ by the central grade
computed above. -/
theorem two_twistor_trace_free_orderings_agree
    {n : ℕ} (z w : Fin 2 → Fin n → B) (hbar : B)
    (hcanonical : ∀ a b i,
      z a i * w b i - w b i * z a i = if a = b then hbar else 0) :
    scaledTraceFree2 (twoTwistorWeylMatrix z w) =
      scaledTraceFree2 (twoTwistorNormalMatrix z w) := by
  have hdef := two_twistor_weyl_ordering_matrix_defect z w hbar hcanonical
  have hsum : twoTwistorWeylMatrix z w =
      twoTwistorNormalMatrix z w +
        centralScalarMatrix ((Fintype.card (Fin n) : ℕ) • hbar) := by
    calc
      twoTwistorWeylMatrix z w =
          (twoTwistorWeylMatrix z w - twoTwistorNormalMatrix z w) +
            twoTwistorNormalMatrix z w := by abel
      _ = centralScalarMatrix ((Fintype.card (Fin n) : ℕ) • hbar) +
            twoTwistorNormalMatrix z w := by rw [hdef]
      _ = twoTwistorNormalMatrix z w +
            centralScalarMatrix ((Fintype.card (Fin n) : ℕ) • hbar) := by abel
  rw [hsum]
  exact scaledTraceFree2_add_central _ _

end NoncommutativeOperatorIdentity

/-! ## Concrete two-channel specialization in the polynomial operator algebra

The preceding matrix theorem is now instantiated in the actual endomorphism
ring of the four-variable polynomial representation.  The four coordinates
are indexed by the two channel bits, so the off-diagonal CCR vanish by
coordinate inequality rather than by an assumed scalar model. -/

section PolynomialOperatorOrdering

open InfoGeometry.Twistor.PenrosePolynomialCCR

/-- Flatten a two-channel, two-mode label into one of the four polynomial
coordinates. -/
def polynomialChannelIndex (a i : Fin 2) : Fin 4 :=
  ⟨2 * a.val + i.val, by omega⟩

theorem polynomialChannelIndex_injective {a b i j : Fin 2}
    (h : polynomialChannelIndex a i = polynomialChannelIndex b j) :
    a = b ∧ i = j := by
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [polynomialChannelIndex] at hv ⊢

noncomputable def polynomialChannelZ (a i : Fin 2) : Operator :=
  Z (polynomialChannelIndex a i)

noncomputable def polynomialChannelW (h : ℂ) (a i : Fin 2) : Operator :=
  W h (polynomialChannelIndex a i)

/-- The four coordinate pairs in the polynomial twistor representation give
the exact four-channel Weyl shift, with `ℏ` represented by `h • 1` in the
noncommutative endomorphism ring. -/
theorem polynomial_four_coordinate_weyl_shift (h : ℂ) :
    (∑ i : Fin 4, (Z i * W h i + W h i * Z i)) =
      2 • (∑ i : Fin 4, W h i * Z i) + 4 • (h • (1 : Operator)) := by
  apply finite_channel_weyl_ordering_shift
  intro i
  simpa using coordinate_CCR h i i

/-- The two-channel CCR are inherited from the concrete coordinate CCR of the
polynomial representation. -/
theorem polynomialChannel_CCR (h : ℂ) (a b i : Fin 2) :
    polynomialChannelZ a i * polynomialChannelW h b i -
        polynomialChannelW h b i * polynomialChannelZ a i =
      if a = b then h • (1 : Operator) else 0 := by
  rw [polynomialChannelZ, polynomialChannelW, coordinate_CCR]
  by_cases hab : a = b
  · subst b
    simp [polynomialChannelIndex]
  · have hne : polynomialChannelIndex a i ≠ polynomialChannelIndex b i := by
      intro heq
      exact hab (polynomialChannelIndex_injective heq).1
    simp [hne, hab]

/-- The represented coordinate creation and annihilation operators are
actually noncommuting whenever the central parameter is nonzero. This turns
the polynomial CCR from a relation in an endomorphism ring into an explicit
noncommutativity witness. -/
theorem polynomialChannel_noncommutes (h : ℂ) (hh : h ≠ 0)
    (a i : Fin 2) :
    polynomialChannelZ a i * polynomialChannelW h a i ≠
      polynomialChannelW h a i * polynomialChannelZ a i := by
  intro heq
  have hccr := polynomialChannel_CCR h a a i
  rw [heq] at hccr
  have hzero : h • (1 : Operator) = 0 := by simpa using hccr.symm
  have hzeroOne := congrArg (fun T : Operator => T (1 : WavePolynomial)) hzero
  have hscalar : h • (1 : WavePolynomial) = 0 := by simpa using hzeroOne
  have hsplit := (smul_eq_zero.mp hscalar)
  rcases hsplit with hzero | hone
  · exact hh hzero
  · exact one_ne_zero hone

/-- In the concrete polynomial operator ring, the two-channel Weyl/normal
ordering defect is exactly the two-mode central matrix grade. -/
theorem polynomial_two_channel_ordering_defect (h : ℂ) :
    twoTwistorWeylMatrix polynomialChannelZ (polynomialChannelW h) -
        twoTwistorNormalMatrix polynomialChannelZ (polynomialChannelW h) =
      centralScalarMatrix (2 • (h • (1 : Operator))) := by
  exact two_twistor_weyl_ordering_matrix_defect
    polynomialChannelZ (polynomialChannelW h) (h • (1 : Operator))
    (by intro a b i; exact polynomialChannel_CCR h a b i)

/-- Scalar identity operators are central in the polynomial endomorphism
algebra. This is proved from the module action and is used only for the
central parameter forced by the CCR. -/
theorem scalarIdentityOperator_commutes (c : ℂ) (T : Operator) :
    (c • (1 : Operator)) * T = T * (c • (1 : Operator)) := by
  apply LinearMap.ext
  intro p
  change c • T p = T (c • p)
  rw [map_smul]

/-- The concrete polynomial Weyl-ordering defect commutes with every matrix
over the polynomial operator algebra. Its central grade is obtained from
the CCR, not stipulated as an extra matrix hypothesis. -/
theorem polynomial_two_channel_ordering_defect_is_central (h : ℂ)
    (M : Matrix (Fin 2) (Fin 2) Operator) :
    (twoTwistorWeylMatrix polynomialChannelZ (polynomialChannelW h) -
        twoTwistorNormalMatrix polynomialChannelZ (polynomialChannelW h)) * M =
      M * (twoTwistorWeylMatrix polynomialChannelZ (polynomialChannelW h) -
        twoTwistorNormalMatrix polynomialChannelZ (polynomialChannelW h)) := by
  rw [polynomial_two_channel_ordering_defect]
  apply centralScalarMatrix_commutes
  intro T
  have hcentral : ∀ T : Operator, (h • (1 : Operator)) * T =
      T * (h • (1 : Operator)) := fun T => scalarIdentityOperator_commutes h T
  have hgrade := centralOrderingGrade_commutes (ι := Fin 2)
    (h • (1 : Operator)) hcentral T
  simpa [centralOrderingGrade] using hgrade

end PolynomialOperatorOrdering

section NoncommutativeKerrSchildOperator

variable {B : Type*} [Ring B]
variable {ι : Type*} [Fintype ι]

/-- The rank-one endomorphism `u ⊗ v` over an arbitrary associative ring.
Entry order is retained: its `(i,j)` coefficient is `u i * v j`. -/
def rankOneOperator (u v : ι → B) : Matrix ι ι B := fun i j => u i * v j

/-- Composition of ordered rank-one operators over an arbitrary ring.
The contraction sits between the output column and input row, with order
`v k * w k` preserved; no commutativity or scalar-valued contraction is
assumed. -/
theorem rankOneOperator_mul_rankOneOperator (u v w z : ι → B) :
    rankOneOperator u v * rankOneOperator w z =
      rankOneOperator u (fun j => (∑ k : ι, v k * w k) * z j) := by
  ext i j
  simp only [Matrix.mul_apply, rankOneOperator]
  calc
    (∑ k : ι, (u i * v k) * (w k * z j)) =
        u i * (∑ k : ι, v k * w k) * z j := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [mul_assoc]
    _ = u i * ((∑ k : ι, v k * w k) * z j) := by
          simp only [mul_assoc]

/-- Exact ordered two-channel commutator for rank-one operators. The two
cross-contractions are kept in their respective orders, so the formula is
valid over a noncommutative coefficient ring. -/
theorem rankOneOperator_commutator (u v w z : ι → B) :
    rankOneOperator u v * rankOneOperator w z -
        rankOneOperator w z * rankOneOperator u v =
      rankOneOperator u (fun j => (∑ k : ι, v k * w k) * z j) -
        rankOneOperator w (fun j => (∑ k : ι, z k * u k) * v j) := by
  rw [rankOneOperator_mul_rankOneOperator, rankOneOperator_mul_rankOneOperator]

/-- A rank-one operator is nilpotent when its ordered contraction `v·u`
vanishes. No commutativity of the coefficient ring is used. -/
theorem rankOneOperator_sq_eq_zero (u v : ι → B)
    (hnull : ∑ i : ι, v i * u i = 0) :
    rankOneOperator u v * rankOneOperator u v = 0 := by
  rw [rankOneOperator_mul_rankOneOperator]
  have hrow : (fun j : ι => (∑ i : ι, v i * u i) * v j) = fun _ => 0 := by
    funext j
    simp [hnull]
  rw [hrow]
  ext i j
  simp [rankOneOperator]

/-- The same ordered null contraction says the rank-one operator annihilates
its generating vector in the native matrix action. -/
theorem rankOneOperator_mulVec_self_eq_zero (u v : ι → B)
    (hnull : ∑ i : ι, v i * u i = 0) :
    Matrix.mulVec (rankOneOperator u v) u = 0 := by
  ext i
  simp only [Matrix.mulVec, rankOneOperator, dotProduct]
  calc
    (∑ j : ι, u i * v j * u j) = u i * (∑ j : ι, v j * u j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [mul_assoc]
    _ = 0 := by rw [hnull]; simp

/-- Ordered weighted rank-one operator.  The amplitude `c` sits between the
two operator-valued factors; no centrality or commutativity assumption is
made. -/
def weightedRankOneOperator (u v : ι → B) (c : B) : Matrix ι ι B :=
  fun i j => u i * c * v j

/-- A weighted rank-one operator is nilpotent when its ordered contraction
vanishes.  The amplitude is retained inside the contraction rather than
commuted through either vector. -/
theorem weightedRankOneOperator_sq_eq_zero (u v : ι → B) (c : B)
    (hnull : ∑ i : ι, v i * u i = 0) :
    weightedRankOneOperator u v c * weightedRankOneOperator u v c = 0 := by
  have hweighted : ∑ i : ι, (c * v i) * u i = 0 := by
    calc
      (∑ i : ι, (c * v i) * u i) = ∑ i : ι, c * (v i * u i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mul_assoc]
      _ = c * (∑ i : ι, v i * u i) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hnull]; simp
  have hop : weightedRankOneOperator u v c =
      rankOneOperator u (fun i => c * v i) := by
    ext i j
    simp [weightedRankOneOperator, rankOneOperator, mul_assoc]
  rw [hop]
  exact rankOneOperator_sq_eq_zero u (fun i => c * v i) hweighted

/-- The ordered amplitude-weighted rank-one operator annihilates its
generating vector under the same null-contraction hypothesis. -/
theorem weightedRankOneOperator_mulVec_self_eq_zero (u v : ι → B) (c : B)
    (hnull : ∑ i : ι, v i * u i = 0) :
    Matrix.mulVec (weightedRankOneOperator u v c) u = 0 := by
  have hweighted : ∑ i : ι, (c * v i) * u i = 0 := by
    calc
      (∑ i : ι, (c * v i) * u i) = ∑ i : ι, c * (v i * u i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mul_assoc]
      _ = c * (∑ i : ι, v i * u i) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hnull]; simp
  have hop : weightedRankOneOperator u v c =
      rankOneOperator u (fun i => c * v i) := by
    ext i j
    simp [weightedRankOneOperator, rankOneOperator, mul_assoc]
  rw [hop]
  exact rankOneOperator_mulVec_self_eq_zero u (fun i => c * v i) hweighted

/-- Kerr–Schild deformation relative to a background operator. The
null rank-one endomorphism is added on the right of the background. -/
def operatorKerrSchildMetric (η N : Matrix ι ι B) : Matrix ι ι B :=
  η + η * N

/-- A null rank-one perturbation contributes zero to the action on its
generating vector. This result needs only a finite index type. -/
theorem operatorKerrSchildMetric_preserves_null_generator
    (η : Matrix ι ι B) (u v : ι → B)
    (hnull : ∑ i : ι, v i * u i = 0) :
    Matrix.mulVec (operatorKerrSchildMetric η (rankOneOperator u v)) u =
      Matrix.mulVec η u := by
  change Matrix.mulVec (η + η * rankOneOperator u v) u = Matrix.mulVec η u
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    rankOneOperator_mulVec_self_eq_zero u v hnull]
  simp

/-- Right action of a matrix on a row operator vector.  The coefficient order
is `v i * T i j`, matching the left action on column vectors. -/
def operatorRowMul (v : ι → B) (T : Matrix ι ι B) : ι → B :=
  fun j => ∑ i : ι, v i * T i j

/-- Change-of-frame covariance of the ordered rank-one operator over an
arbitrary noncommutative ring.  Conjugating `u ⊗ v` transforms the column by
left multiplication and the row by right multiplication, preserving the
order `u_i * v_j` exactly. -/
theorem rankOneOperator_matrix_transport (S T : Matrix ι ι B) (u v : ι → B) :
    S * rankOneOperator u v * T =
      rankOneOperator (Matrix.mulVec S u) (operatorRowMul v T) := by
  ext i j
  simp only [Matrix.mul_apply, rankOneOperator, Matrix.mulVec,
    operatorRowMul, dotProduct]
  calc
    (∑ k : ι, (∑ l : ι, S i l * (u l * v k)) * T k j) =
        ∑ k : ι, ∑ l : ι, (S i l * u l) * (v k * T k j) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [mul_assoc]
    _ = ∑ l : ι, ∑ k : ι, (S i l * u l) * (v k * T k j) := by
      rw [Finset.sum_comm]
    _ = (∑ l : ι, S i l * u l) * (∑ k : ι, v k * T k j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mul_sum]

/-- Nilpotency of a null rank-one operator is preserved by an inverse change
of frame.  The order of the inverse law is explicit: `T * S = 1`. -/
theorem rankOneOperator_similarity_sq_eq_zero (S T : Matrix ι ι B)
    (u v : ι → B) [DecidableEq ι] (hTS : T * S = 1)
    (hnull : ∑ i : ι, v i * u i = 0) :
    rankOneOperator (Matrix.mulVec S u) (operatorRowMul v T) *
      rankOneOperator (Matrix.mulVec S u) (operatorRowMul v T) = 0 := by
  have hN := rankOneOperator_sq_eq_zero u v hnull
  rw [← rankOneOperator_matrix_transport S T u v]
  calc
    (S * rankOneOperator u v * T) * (S * rankOneOperator u v * T) =
        (S * rankOneOperator u v) * (T * S) *
          (rankOneOperator u v * T) := by
      simp [Matrix.mul_assoc]
    _ = (S * rankOneOperator u v) * 1 *
          (rankOneOperator u v * T) := by rw [hTS]
    _ = S * (rankOneOperator u v * rankOneOperator u v) * T := by
      simp [Matrix.mul_assoc]
    _ = 0 := by rw [hN]; simp

variable [DecidableEq ι]

/-- The ordered inverse candidate for `η (1+N)` is `(1-N) η`. -/
def operatorKerrSchildInverse (η N : Matrix ι ι B) : Matrix ι ι B :=
  (1 - N) * η

private theorem nilpotent_plus_minus_factors (N : Matrix ι ι B)
    (hN : N * N = 0) :
    (1 + N) * (1 - N) = 1 ∧ (1 - N) * (1 + N) = 1 := by
  constructor
  · simp only [add_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hN]
    abel
  · simp only [sub_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hN]
    abel

/-- A Kerr--Schild perturbation of any invertible operator matrix has the
ordered inverse `(1-N) * η⁻¹` when `N²=0`. The two inverse equations for the
background are explicit; no involution or commutativity is assumed. -/
theorem operatorKerrSchildMetric_two_sided_inverse_of_background_inverse
    (η ηInv N : Matrix ι ι B)
    (hηR : η * ηInv = 1) (hηL : ηInv * η = 1) (hN : N * N = 0) :
    operatorKerrSchildMetric η N * ((1 - N) * ηInv) = 1 ∧
      ((1 - N) * ηInv) * operatorKerrSchildMetric η N = 1 := by
  have hfac := nilpotent_plus_minus_factors N hN
  constructor
  · change (η + η * N) * ((1 - N) * ηInv) = 1
    calc
      (η + η * N) * ((1 - N) * ηInv) =
          (η * (1 + N)) * ((1 - N) * ηInv) := by
        congr 1
        simp [Matrix.mul_add]
      _ = η * ((1 + N) * (1 - N)) * ηInv := by simp [Matrix.mul_assoc]
      _ = η * 1 * ηInv := by rw [hfac.1]
      _ = 1 := by rw [Matrix.mul_one, hηR]
  · change ((1 - N) * ηInv) * (η + η * N) = 1
    calc
      ((1 - N) * ηInv) * (η + η * N) =
          (1 - N) * (ηInv * η) * (1 + N) := by
        simp [Matrix.mul_add, Matrix.mul_assoc]
      _ = (1 - N) * (1 + N) := by rw [hηL]; simp
      _ = 1 := hfac.2

/-- A genuinely ordered weighted rank-one perturbation has a two-sided
Kerr--Schild inverse over an arbitrary invertible background.  The null
contraction is stated in the original row/column order; the amplitude `c`
is not assumed central and is retained in the nilpotent perturbation.
-/
theorem weightedRankOneOperator_kerrSchild_inverse_of_background_inverse
    (η ηInv : Matrix ι ι B) (u v : ι → B) (c : B)
    (hηR : η * ηInv = 1) (hηL : ηInv * η = 1)
    (hnull : ∑ i : ι, v i * u i = 0) :
    operatorKerrSchildMetric η (weightedRankOneOperator u v c) *
        ((1 - weightedRankOneOperator u v c) * ηInv) = 1 ∧
      ((1 - weightedRankOneOperator u v c) * ηInv) *
        operatorKerrSchildMetric η (weightedRankOneOperator u v c) = 1 := by
  exact operatorKerrSchildMetric_two_sided_inverse_of_background_inverse
    η ηInv (weightedRankOneOperator u v c) hηR hηL
    (weightedRankOneOperator_sq_eq_zero u v c hnull)

/-- Two-sided inverse theorem for noncommutative Kerr–Schild operators.
If the background squares to identity and the ordered rank-one perturbation
is nilpotent, then `η + ηN` is invertible with inverse `(1-N)η`. -/
theorem operatorKerrSchildMetric_two_sided_inverse
    (η N : Matrix ι ι B) (hη : η * η = 1) (hN : N * N = 0) :
    operatorKerrSchildMetric η N * operatorKerrSchildInverse η N = 1 ∧
    operatorKerrSchildInverse η N * operatorKerrSchildMetric η N = 1 := by
  exact operatorKerrSchildMetric_two_sided_inverse_of_background_inverse
    η η N hη hη hN

/-- Kerr--Schild metric construction and its ordered inverse are covariant
under an invertible change of frame in the noncommutative matrix algebra.
Both inverse equations for the frame maps are required explicitly. -/
theorem operatorKerrSchild_change_of_frame
    (S T η N : Matrix ι ι B) (hST : S * T = 1) (hTS : T * S = 1)
    (hη : η * η = 1) (hN : N * N = 0) :
    operatorKerrSchildMetric (S * η * T) (S * N * T) =
        S * operatorKerrSchildMetric η N * T ∧
      operatorKerrSchildInverse (S * η * T) (S * N * T) =
        S * operatorKerrSchildInverse η N * T ∧
      operatorKerrSchildMetric (S * η * T) (S * N * T) *
          operatorKerrSchildInverse (S * η * T) (S * N * T) = 1 ∧
      operatorKerrSchildInverse (S * η * T) (S * N * T) *
          operatorKerrSchildMetric (S * η * T) (S * N * T) = 1 := by
  have hη' : (S * η * T) * (S * η * T) = 1 := by
    calc
      (S * η * T) * (S * η * T) = S * η * (T * S) * η * T := by
        simp [Matrix.mul_assoc]
      _ = S * η * η * T := by rw [hTS]; simp [Matrix.mul_assoc]
      _ = S * (η * η) * T := by simp [Matrix.mul_assoc]
      _ = S * 1 * T := by rw [hη]
      _ = 1 := by simp [hST]
  have hN' : (S * N * T) * (S * N * T) = 0 := by
    calc
      (S * N * T) * (S * N * T) = S * N * (T * S) * N * T := by
        simp [Matrix.mul_assoc]
      _ = S * N * N * T := by rw [hTS]; simp [Matrix.mul_assoc]
      _ = S * (N * N) * T := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [hN]; simp
  have hinv := operatorKerrSchildMetric_two_sided_inverse
    (S * η * T) (S * N * T) hη' hN'
  refine ⟨?_, ?_, hinv.1, hinv.2⟩
  · change S * η * T + (S * η * T) * (S * N * T) =
      S * (η + η * N) * T
    calc
      S * η * T + (S * η * T) * (S * N * T) =
          S * η * T + S * η * (T * S) * N * T := by
        simp [Matrix.mul_assoc]
      _ = S * η * T + S * η * N * T := by rw [hTS]; simp [Matrix.mul_assoc]
      _ = (S * η + S * (η * N)) * T := by
        rw [Matrix.add_mul]
        simp only [Matrix.mul_assoc]
      _ = S * (η + η * N) * T := by
        rw [Matrix.mul_add]
  · change (1 - S * N * T) * (S * η * T) =
      S * ((1 - N) * η) * T
    calc
      (1 - S * N * T) * (S * η * T) =
          S * η * T - (S * N * T) * (S * η * T) := by
        simp only [sub_mul, Matrix.one_mul]
      _ = S * η * T - S * N * (T * S) * η * T := by
        simp [Matrix.mul_assoc]
      _ = S * η * T - S * N * η * T := by rw [hTS]; simp [Matrix.mul_assoc]
      _ = (S * η - S * (N * η)) * T := by
        rw [Matrix.sub_mul]
        simp only [Matrix.mul_assoc]
      _ = S * (η - N * η) * T := by
        rw [Matrix.mul_sub]
      _ = S * ((1 - N) * η) * T := by
        rw [sub_mul, Matrix.one_mul]

/-- A null rank-one operator over a noncommutative coefficient ring yields a
two-sided Kerr–Schild inverse over the same operator matrix algebra. -/
theorem rankOneOperator_kerrSchild_inverse (η : Matrix ι ι B)
    (u v : ι → B) (hη : η * η = 1)
    (hnull : ∑ i : ι, v i * u i = 0) :
    operatorKerrSchildMetric η (rankOneOperator u v) *
        operatorKerrSchildInverse η (rankOneOperator u v) = 1 ∧
    operatorKerrSchildInverse η (rankOneOperator u v) *
        operatorKerrSchildMetric η (rankOneOperator u v) = 1 := by
  exact operatorKerrSchildMetric_two_sided_inverse η
    (rankOneOperator u v) hη (rankOneOperator_sq_eq_zero u v hnull)

/-- A null twistor's actual moment endomorphism is a valid nilpotent
Kerr--Schild perturbation. Consequently the ordered metric operator
`η + η * momentOperator Z` has the two-sided inverse
`(1 - momentOperator Z) * η`, provided the background operator is an
involution. The coefficient ring for the matrices is `ℂ`, but matrix
composition is retained and is noncommutative. -/
theorem nullTwistor_moment_kerrSchild_inverse
    (η : Matrix InfoGeometry.Twistor.TwistorKinematicTensor.Slot
      InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
    (Z : InfoGeometry.Twistor.PenroseIncidence.Twistor4)
    (hη : η * η = 1)
    (hnull : InfoGeometry.Twistor.PerjesConventions.wittPair Z Z = 0) :
    operatorKerrSchildMetric η
        (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) *
          operatorKerrSchildInverse η
            (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) = 1 ∧
    operatorKerrSchildInverse η
        (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) *
          operatorKerrSchildMetric η
            (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) = 1 := by
  apply operatorKerrSchildMetric_two_sided_inverse
  · exact hη
  · rw [InfoGeometry.Twistor.PerjesMomentOperator.momentOperator_square, hnull,
      zero_smul]

/-- The actual null-twistor moment endomorphism also gives a two-sided
Kerr--Schild inverse over any two-sided-invertible background operator.
Unlike `nullTwistor_moment_kerrSchild_inverse`, this result does not assume
that the background is an involution; both ordered background inverse laws
are explicit. -/
theorem nullTwistor_moment_kerrSchild_inverse_of_background_inverse
    (η ηInv : Matrix InfoGeometry.Twistor.TwistorKinematicTensor.Slot
      InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
    (Z : InfoGeometry.Twistor.PenroseIncidence.Twistor4)
    (hηR : η * ηInv = 1) (hηL : ηInv * η = 1)
    (hnull : InfoGeometry.Twistor.PerjesConventions.wittPair Z Z = 0) :
    operatorKerrSchildMetric η
        (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) *
          ((1 - InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) * ηInv) = 1 ∧
      ((1 - InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) * ηInv) *
        operatorKerrSchildMetric η
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) = 1 := by
  apply operatorKerrSchildMetric_two_sided_inverse_of_background_inverse
  · exact hηR
  · exact hηL
  · rw [InfoGeometry.Twistor.PerjesMomentOperator.momentOperator_square, hnull,
      zero_smul]

/-- There are two null-twistor Kerr--Schild deformations of the identity
background that are each invertible but do not commute with one another.
This witnesses that individual nilpotent deformations can be regular while
their ordered two-channel interaction remains genuinely noncommutative. -/
theorem nullTwistor_kerrSchild_pair_noncommuting :
    ∃ Z W : InfoGeometry.Twistor.PenroseIncidence.Twistor4,
      InfoGeometry.Twistor.PerjesConventions.wittPair Z Z = 0 ∧
      InfoGeometry.Twistor.PerjesConventions.wittPair W W = 0 ∧
      operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) *
        operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) ≠
      operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) *
        operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) ∧
      (operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) *
        operatorKerrSchildInverse (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) = 1 ∧
       operatorKerrSchildInverse (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) *
        operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) = 1) ∧
      (operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) *
        operatorKerrSchildInverse (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) = 1 ∧
       operatorKerrSchildInverse (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) *
        operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) = 1) := by
  obtain ⟨Z, W, hZ, hW, hNM⟩ :=
    InfoGeometry.Twistor.PerjesMomentOperator.momentOperators_noncommuting
  have hZN :
      InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z *
        InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W ≠
      InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W *
        InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z := hNM
  have hmetric :
      operatorKerrSchildMetric (1 : Matrix
        InfoGeometry.Twistor.TwistorKinematicTensor.Slot
        InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) *
        operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) ≠
      operatorKerrSchildMetric (1 : Matrix
        InfoGeometry.Twistor.TwistorKinematicTensor.Slot
        InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) *
        operatorKerrSchildMetric (1 : Matrix
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot
          InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ)
          (InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) := by
    intro heq
    apply hZN
    simp only [operatorKerrSchildMetric, Matrix.one_mul] at heq
    change (1 + InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) *
          (1 + InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) =
        (1 + InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) *
          (1 + InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) at heq
    have hdiff :
        (1 + InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) *
            (1 + InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) -
          (1 + InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W) *
            (1 + InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z) =
          InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z *
              InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W -
            InfoGeometry.Twistor.PerjesMomentOperator.momentOperator W *
              InfoGeometry.Twistor.PerjesMomentOperator.momentOperator Z := by
      noncomm_ring
    rw [heq] at hdiff
    exact sub_eq_zero.mp (by simpa using hdiff.symm)
  have hη : (1 : Matrix
      InfoGeometry.Twistor.TwistorKinematicTensor.Slot
      InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ) * 1 = 1 := by simp
  have hinvZ := nullTwistor_moment_kerrSchild_inverse (1 : Matrix
    InfoGeometry.Twistor.TwistorKinematicTensor.Slot
    InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ) Z hη hZ
  have hinvW := nullTwistor_moment_kerrSchild_inverse (1 : Matrix
    InfoGeometry.Twistor.TwistorKinematicTensor.Slot
    InfoGeometry.Twistor.TwistorKinematicTensor.Slot ℂ) W hη hW
  exact ⟨Z, W, hZ, hW, hmetric, hinvZ, hinvW⟩

end NoncommutativeKerrSchildOperator

section KerrCoordinateIdentity

variable {R : Type*} [CommRing R]

/-- Oblate spheroidal coordinates imply the polynomial identity
`x² + y² + (z - i a)² = (r - i a c)²`, expressed as separate real and
imaginary coefficient identities without adjoining `i` to an arbitrary
commutative coefficient ring. -/
theorem oblate_spheroidal_complex_radius_factorization
    (r a c xy z : R)
    (hxy : xy = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    xy + z * z - a * a = r * r - a * a * c * c ∧
      2 * a * z = 2 * a * r * c := by
  constructor
  · rw [hxy, hz]
    ring
  · rw [hz]
    ring

/-- The same coordinate calculation as one complex polynomial identity. The
`ring` step is needed after rewriting `z = r*c` to normalize both products
and powers; rewriting alone does not close the goal. -/
theorem oblate_spheroidal_complex_factorization
    (r a c xy z : ℂ)
    (hxy : xy = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    xy + (z - Complex.I * a) ^ 2 =
      (r - Complex.I * a * c) ^ 2 := by
  rw [hxy, hz]
  simp only [sub_sq, mul_pow, Complex.I_sq]
  ring

end KerrCoordinateIdentity

section KerrSchildMetric

open scoped Matrix

/-- The diagonal Minkowski bilinear form in the coordinate order
`(t,x,y,z)`. -/
def minkowskiMetric4 : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
  if i = j then if i.val = 0 then -1 else 1 else 0

/-- Kerr--Schild rank-one deformation of the Minkowski metric.  This is the
algebraic metric construction from a coefficient `f` and a null covector `k`.
The Kerr choice is `f = G m r / (r^2 + a^2 cos^2 θ)` and `k` is the outgoing
Kerr principal null covector; those geometric data are not constructed here. -/
def kerrSchildMetric4 (f : ℝ) (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => minkowskiMetric4 i j + (2 * f) * k i * k j

/-- Nullity in the Minkowski metric, written as the coordinate contraction. -/
def minkowskiNull4 (k : Fin 4 → ℝ) : Prop :=
  -k 0 * k 0 + k 1 * k 1 + k 2 * k 2 + k 3 * k 3 = 0

/-- The coordinate contraction of a covariant `4 × 4` tensor with a vector.
The explicit four-term form keeps the coordinate convention visible. -/
def contract4 (g : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => g i 0 * k 0 + g i 1 * k 1 + g i 2 * k 2 + g i 3 * k 3

/-- Raise a covector index with `diag(-1,1,1,1)`. -/
def minkowskiRaise4 (k : Fin 4 → ℝ) : Fin 4 → ℝ := fun i =>
  if i = 0 then -k 0 else k i

/-- The Kerr--Schild perturbation represented in the general operator
construction. Its column is the Minkowski-raised null covector and its row
retains the original covector order. -/
def kerrSchildOperator4 (f : ℝ) (k : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  weightedRankOneOperator (minkowskiRaise4 k) k (2 * f)

/-- The Minkowski matrix is an involution on the actual four-coordinate
carrier. -/
theorem minkowskiMetric4_sq : minkowskiMetric4 * minkowskiMetric4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiMetric4, Matrix.mul_apply]

/-- Raising a covector and then applying the background matrix recovers the
original covector. -/
theorem minkowskiMetric4_mul_raise4 (k : Fin 4 → ℝ) :
    Matrix.mulVec minkowskiMetric4 (minkowskiRaise4 k) = k := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, minkowskiMetric4, minkowskiRaise4,
      Fin.sum_univ_four]

/-- Left multiplication of the raised rank-one perturbation by the
Minkowski operator lowers its first index and gives the covariant Kerr--Schild
tensor `2 f k_i k_j`. This is the explicit bridge between the noncommutative
operator formula and the coordinate metric. -/
theorem minkowskiMetric4_mul_kerrSchildOperator4 (f : ℝ) (k : Fin 4 → ℝ) :
    minkowskiMetric4 * kerrSchildOperator4 f k =
      weightedRankOneOperator k k (2 * f) := by
  have hcontract (i : Fin 4) :
      (∑ l : Fin 4, minkowskiMetric4 i l * minkowskiRaise4 k l) = k i := by
    change (Matrix.mulVec minkowskiMetric4 (minkowskiRaise4 k)) i = k i
    rw [minkowskiMetric4_mul_raise4]
  ext i j
  simp only [Matrix.mul_apply, kerrSchildOperator4, weightedRankOneOperator]
  calc
    (∑ l : Fin 4,
        minkowskiMetric4 i l * (minkowskiRaise4 k l * (2 * f) * k j)) =
        (∑ l : Fin 4, minkowskiMetric4 i l * minkowskiRaise4 k l) *
          (2 * f) * k j := by
            calc
              _ = (∑ l : Fin 4,
                  (minkowskiMetric4 i l * minkowskiRaise4 k l) * (2 * f)) * k j := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro l hl
                    ring
              _ = ((∑ l : Fin 4,
                  minkowskiMetric4 i l * minkowskiRaise4 k l) * (2 * f)) * k j := by
                    rw [← Finset.sum_mul]
    _ = k i * (2 * f) * k j := by rw [hcontract i]

/-- The concrete coordinate metric is exactly the general operator
Kerr--Schild construction on the Minkowski background. -/
theorem kerrSchildMetric4_eq_operator (f : ℝ) (k : Fin 4 → ℝ) :
    kerrSchildMetric4 f k =
      operatorKerrSchildMetric minkowskiMetric4 (kerrSchildOperator4 f k) := by
  ext i j
  have hentry := congrFun (congrFun
    (minkowskiMetric4_mul_kerrSchildOperator4 f k) i) j
  change minkowskiMetric4 i j + (2 * f) * k i * k j =
    minkowskiMetric4 i j + (minkowskiMetric4 *
      kerrSchildOperator4 f k) i j
  rw [hentry]
  simp only [weightedRankOneOperator]
  ring

/-- The inverse Kerr--Schild matrix predicted by the rank-one inverse
formula. The null vector is raised with the background Minkowski metric;
the inverse is another genuine `4 × 4` matrix. -/
def kerrSchildInverse4 (f : ℝ) (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => minkowskiMetric4 i j - (2 * f) * minkowskiRaise4 k i * minkowskiRaise4 k j

/-- Nullity of the covector is exactly the ordered contraction required by
the generic rank-one nilpotency theorem. -/
theorem kerrSchildOperator4_null_contraction (k : Fin 4 → ℝ)
    (hk : minkowskiNull4 k) :
    (∑ i : Fin 4, k i * minkowskiRaise4 k i) = 0 := by
  have hcoord :
      -k 0 * k 0 + k 1 * k 1 + k 2 * k 2 + k 3 * k 3 = 0 := hk
  rw [Fin.sum_univ_four]
  simp only [minkowskiRaise4]
  simpa [mul_comm] using hcoord

/-- The actual four-coordinate Kerr--Schild operator is square-zero whenever
its generating covector is Minkowski-null. This instantiates the generic
ordered rank-one theorem, rather than reproving matrix nilpotency by expanding
all sixteen entries. -/
theorem kerrSchildOperator4_sq_zero (f : ℝ) (k : Fin 4 → ℝ)
    (hk : minkowskiNull4 k) :
    kerrSchildOperator4 f k * kerrSchildOperator4 f k = 0 := by
  exact weightedRankOneOperator_sq_eq_zero
    (minkowskiRaise4 k) k (2 * f)
    (kerrSchildOperator4_null_contraction k hk)

/-- The generic noncommutative ordered inverse theorem applies to the
coordinate Kerr--Schild operator on the actual `Fin 4` carrier. The two
background inverse equations are the concrete Minkowski involution law. -/
theorem kerrSchildMetric4_operator_two_sided_inverse
    (f : ℝ) (k : Fin 4 → ℝ) (hk : minkowskiNull4 k) :
    operatorKerrSchildMetric minkowskiMetric4 (kerrSchildOperator4 f k) *
        ((1 - kerrSchildOperator4 f k) * minkowskiMetric4) = 1 ∧
      ((1 - kerrSchildOperator4 f k) * minkowskiMetric4) *
        operatorKerrSchildMetric minkowskiMetric4 (kerrSchildOperator4 f k) = 1 := by
  exact operatorKerrSchildMetric_two_sided_inverse_of_background_inverse
    minkowskiMetric4 minkowskiMetric4 (kerrSchildOperator4 f k)
    minkowskiMetric4_sq minkowskiMetric4_sq
    (kerrSchildOperator4_sq_zero f k hk)

/-- The rank-one Kerr--Schild matrix is symmetric. -/
theorem kerrSchildMetric4_symmetric (f : ℝ) (k : Fin 4 → ℝ) :
    (kerrSchildMetric4 f k).transpose = kerrSchildMetric4 f k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrSchildMetric4, minkowskiMetric4, Matrix.transpose_apply] <;> ring

/-- The proposed inverse is a left inverse of the full rank-one metric matrix
whenever its generating covector is null. The proof expands matrix
composition and cancels the two cross terms; the remaining rank-one term
vanishes by nullity. -/
theorem kerrSchildMetric4_mul_inverse (f : ℝ) (k : Fin 4 → ℝ)
    (hk : minkowskiNull4 k) :
    kerrSchildMetric4 f k * kerrSchildInverse4 f k = 1 := by
  have hnull : -k 0 * k 0 + k 1 * k 1 + k 2 * k 2 + k 3 * k 3 = 0 := hk
  have hentry (i j : Fin 4) :
      (kerrSchildMetric4 f k * kerrSchildInverse4 f k) i j =
        (if i = j then 1 else 0) -
          4 * f ^ 2 * k i * minkowskiRaise4 k j *
            (-k 0 * k 0 + k 1 * k 1 + k 2 * k 2 + k 3 * k 3) := by
    simp [kerrSchildMetric4, kerrSchildInverse4, minkowskiMetric4,
      minkowskiRaise4, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      simp <;> ring
  ext i j
  rw [hentry, hnull]
  simp [Matrix.one_apply]

/-- The same formula is a right inverse. This records two-sided invertibility
without relying on finite-dimensional injectivity or an unproved determinant
claim. -/
theorem kerrSchildInverse_mul_metric4 (f : ℝ) (k : Fin 4 → ℝ)
    (hk : minkowskiNull4 k) :
    kerrSchildInverse4 f k * kerrSchildMetric4 f k = 1 := by
  have htransposeMetric := kerrSchildMetric4_symmetric f k
  have htransposeInverse : (kerrSchildInverse4 f k).transpose =
      kerrSchildInverse4 f k := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kerrSchildInverse4, minkowskiMetric4] <;> ring
  calc
    kerrSchildInverse4 f k * kerrSchildMetric4 f k =
        (kerrSchildMetric4 f k * kerrSchildInverse4 f k).transpose := by
          rw [Matrix.transpose_mul, htransposeMetric, htransposeInverse]
    _ = 1 := by rw [kerrSchildMetric4_mul_inverse f k hk, Matrix.transpose_one]

/-- A null rank-one Kerr--Schild deformation preserves the Minkowski volume
determinant. This is a determinant theorem for the full `4 × 4` matrix, not
just an inverse formula: `det(g) = det(η) = -1`. -/
theorem kerrSchildMetric4_det (f : ℝ) (k : Fin 4 → ℝ)
    (hk : minkowskiNull4 k) :
    (kerrSchildMetric4 f k).det = -1 := by
  let η := minkowskiMetric4
  let u : Matrix (Fin 4) (Fin 1) ℝ := fun i _ => (2 * f) * k i
  let v : Matrix (Fin 1) (Fin 4) ℝ := fun _ j => k j
  have hηsq : η * η = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [η, minkowskiMetric4, Matrix.mul_apply]
  have hηdet : η.det = -1 := by
    have hdiag : η = Matrix.diagonal (fun i : Fin 4 => if i = 0 then -1 else 1) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [η, minkowskiMetric4]
      · simp [η, minkowskiMetric4, hij]
    rw [hdiag, Matrix.det_diagonal]
    norm_num [Fin.prod_univ_succ]
  have hmetric : kerrSchildMetric4 f k = η + u * v := by
    ext i j
    change minkowskiMetric4 i j + (2 * f) * k i * k j =
      minkowskiMetric4 i j + ∑ x : Fin 1, u i x * v x j
    rw [Fin.sum_univ_one]
  have hfactor : η * kerrSchildMetric4 f k = 1 + (η * u) * v := by
    rw [hmetric, Matrix.mul_add, hηsq]
    simp [Matrix.mul_assoc]
  have hηu (i : Fin 4) : (η * u) i 0 = (2 * f) * minkowskiRaise4 k i := by
    change (∑ j : Fin 4, minkowskiMetric4 i j * ((2 * f) * k j)) =
      (2 * f) * minkowskiRaise4 k i
    fin_cases i <;>
      simp [minkowskiMetric4, minkowskiRaise4]
  have hsmallEntry : (v * (η * u)) default default = 0 := by
    have hnull :
        -k 0 * k 0 + k 1 * k 1 + k 2 * k 2 + k 3 * k 3 = 0 := hk
    change (∑ i : Fin 4, k i * (η * u) i 0) = 0
    rw [Fin.sum_univ_four]
    simp only [hηu]
    simp [minkowskiRaise4]
    calc
      -(k 0 * (2 * f * k 0)) + k 1 * (2 * f * k 1) +
          k 2 * (2 * f * k 2) + k 3 * (2 * f * k 3) =
        (2 * f) * (-k 0 * k 0 + k 1 * k 1 +
          k 2 * k 2 + k 3 * k 3) := by ring
      _ = 0 := by rw [hnull]; ring
  have hsmallDet : (1 + v * (η * u)).det = 1 := by
    rw [Matrix.det_unique]
    simp only [Matrix.add_apply, Matrix.one_apply_eq]
    rw [hsmallEntry]
    ring
  have hdetProd :
      (η * kerrSchildMetric4 f k).det = η.det * (kerrSchildMetric4 f k).det :=
    Matrix.det_mul η (kerrSchildMetric4 f k)
  have hdetProdOne : (η * kerrSchildMetric4 f k).det = 1 := by
    rw [hfactor, Matrix.det_one_add_mul_comm, hsmallDet]
  rw [hηdet] at hdetProd
  rw [hdetProdOne] at hdetProd
  linarith

/-- A null Kerr--Schild deformation leaves its generating null direction
unchanged after lowering the vector index: `gᵢⱼ kʲ = ηᵢⱼ kʲ`. This is the
algebraic mechanism behind the shared principal null direction of the flat
background and the rank-one deformed metric. -/
theorem kerrSchild_contract_null_direction (f : ℝ) (k : Fin 4 → ℝ)
    (hk : minkowskiNull4 k) :
    contract4 (kerrSchildMetric4 f k) (minkowskiRaise4 k) = k := by
  have hnull : -k 0 * k 0 + k 1 * k 1 + k 2 * k 2 + k 3 * k 3 = 0 := hk
  have hscaled (i : Fin 4) :
      2 * f * k i * (-k 0 * k 0 + k 1 * k 1 + k 2 * k 2 + k 3 * k 3) = 0 := by
    rw [hnull]
    ring
  funext i
  fin_cases i
  · simp [contract4, kerrSchildMetric4, minkowskiMetric4, minkowskiRaise4]
    nlinarith [hscaled 0]
  · simp [contract4, kerrSchildMetric4, minkowskiMetric4, minkowskiRaise4]
    nlinarith [hscaled 1]
  · simp [contract4, kerrSchildMetric4, minkowskiMetric4, minkowskiRaise4]
    nlinarith [hscaled 2]
  · simp [contract4, kerrSchildMetric4, minkowskiMetric4, minkowskiRaise4]
    nlinarith [hscaled 3]

/-- Consequently the null direction remains null for the deformed tensor,
using the explicit contraction rather than a scalar proxy for the metric. -/
theorem kerrSchild_contract_pair_null (f : ℝ) (k : Fin 4 → ℝ)
    (hk : minkowskiNull4 k) :
    (minkowskiRaise4 k 0) * contract4 (kerrSchildMetric4 f k)
        (minkowskiRaise4 k) 0 +
      (minkowskiRaise4 k 1) * contract4 (kerrSchildMetric4 f k)
        (minkowskiRaise4 k) 1 +
      (minkowskiRaise4 k 2) * contract4 (kerrSchildMetric4 f k)
        (minkowskiRaise4 k) 2 +
      (minkowskiRaise4 k 3) * contract4 (kerrSchildMetric4 f k)
        (minkowskiRaise4 k) 3 = 0 := by
  rw [kerrSchild_contract_null_direction f k hk]
  simp [minkowskiRaise4, minkowskiNull4] at hk ⊢
  linarith

/-- The outgoing Kerr principal null covector in Cartesian Kerr--Schild
coordinates.  Its spatial components are expressed using the oblate radius
`r` and rotation parameter `a`. -/
noncomputable def kerrPrincipalNullCovector (r a x y z : ℝ) : Fin 4 → ℝ := fun i =>
  if i = 0 then 1 else if i = 1 then (r * x + a * y) / (r * r + a * a)
  else if i = 2 then (r * y - a * x) / (r * r + a * a) else z / r

/-- The Kerr--Schild coefficient `G m r / Σ`, with `Σ = r² + a² c²`.
The theorem `kerrSigma_pos_of_radius_ne_zero` proves this denominator positive
on the chart `r ≠ 0`; Lean's field division remains total at singular inputs. -/
noncomputable def kerrSchildCoefficient (G m r a c : ℝ) : ℝ :=
  G * m * r / (r * r + a * a * c * c)

/-- The complex Newman radius determined by the oblate coordinates. -/
def complexKerrRadius (r a c : ℝ) : ℂ :=
  (r : ℂ) - Complex.I * ((a * c : ℝ) : ℂ)

/-- The real Kerr--Schild denominator is the squared complex modulus of the
Newman radius, so the metric coefficient uses the same geometric radius as the
complex incidence factorization. -/
theorem kerrSigma_eq_complexRadius_normSq (r a c : ℝ) :
    Complex.normSq (complexKerrRadius r a c) = r * r + a * a * c * c := by
  rw [Complex.normSq_apply]
  simp [complexKerrRadius, Complex.mul_re, Complex.mul_im]
  ring

/-- Away from the zero-radius locus `r = 0`, the Kerr--Schild denominator is
strictly positive, hence the totalized field division in the coefficient is
the ordinary nonsingular coordinate expression. -/
theorem kerrSigma_pos_of_radius_ne_zero (r a c : ℝ) (hr : r ≠ 0) :
    0 < r * r + a * a * c * c := by
  have hr2 : 0 < r * r := by simpa [pow_two] using sq_pos_of_ne_zero hr
  have hac2 : 0 ≤ (a * c) * (a * c) := by
    simpa [pow_two] using sq_nonneg (a * c)
  nlinarith

/-- The same chart condition makes the Kerr denominator nonzero. -/
theorem kerrSigma_ne_zero_of_radius_ne_zero (r a c : ℝ) (hr : r ≠ 0) :
    r * r + a * a * c * c ≠ 0 :=
  ne_of_gt (kerrSigma_pos_of_radius_ne_zero r a c hr)

/-- The vanishing locus of the real Kerr denominator is the simultaneous
vanishing of the real and imaginary parts of the complex Newman radius. -/
theorem kerrSigma_eq_zero_iff (r a c : ℝ) :
    r * r + a * a * c * c = 0 ↔ r = 0 ∧ a * c = 0 := by
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg r, sq_nonneg (a * c)]
  · rintro ⟨rfl, hac⟩
    nlinarith [sq_nonneg (a * c)]

/-- For nonzero rotation, the denominator's zero locus lies at `r = 0` and
`c = cos θ = 0`. Under the oblate-coordinate relations this is the equatorial
circle `x² + y² = a²`, `z = 0`; this records the coordinate ring singularity
without assigning the totalized rational Kerr metric a value there. -/
theorem kerr_ring_locus_coordinates
    (r a c x y z : ℝ) (ha : a ≠ 0)
    (hSigma : r * r + a * a * c * c = 0)
    (hxy : x * x + y * y = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    r = 0 ∧ c = 0 ∧ x * x + y * y = a * a ∧ z = 0 := by
  have hzero := (kerrSigma_eq_zero_iff r a c).mp hSigma
  rcases hzero with ⟨hr, hac⟩
  have hc : c = 0 := by
    rcases mul_eq_zero.mp hac with hleft | hright
    · exact (ha hleft).elim
    · exact hright
  refine ⟨hr, hc, ?_, ?_⟩
  · simpa [hr, hc] using hxy
  · simpa [hr, hc] using hz

/-- The coordinate hypotheses imply that the Cartesian Kerr principal null
covector is null for the Minkowski form of signature `(-,+,+,+)`. -/
theorem kerrPrincipalNullCovector_is_null
    (r a x y z c : ℝ)
    (hr : r ≠ 0) (hden : r * r + a * a ≠ 0)
    (hxy : x * x + y * y = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    minkowskiNull4 (kerrPrincipalNullCovector r a x y z) := by
  have hden2 : (r * r + a * a) ^ 2 ≠ 0 := pow_ne_zero 2 hden
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hnum : (r * x + a * y) ^ 2 + (r * y - a * x) ^ 2 =
      (r * r + a * a) * (x * x + y * y) := by ring
  have hsum : (r * x + a * y) ^ 2 + (r * y - a * x) ^ 2 +
      (r * r + a * a) ^ 2 * c ^ 2 = (r * r + a * a) ^ 2 := by
    rw [hnum, hxy]
    ring
  unfold minkowskiNull4 kerrPrincipalNullCovector
  norm_num
  field_simp
  rw [hz]
  have hsum' := congrArg (fun q : ℝ => r ^ 2 * q) hsum
  nlinarith [hsum']

/-- In the oblate chart, the concrete Kerr operator has square-zero
rank-one perturbation. This is the hypothesis that activates the general
noncommutative Kerr--Schild inverse theorem. -/
theorem kerrPrincipalOperator_sq_zero
    (G m r a c x y z : ℝ) (hr : r ≠ 0) (hden : r * r + a * a ≠ 0)
    (hxy : x * x + y * y = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    kerrSchildOperator4 (kerrSchildCoefficient G m r a c)
      (kerrPrincipalNullCovector r a x y z) *
    kerrSchildOperator4 (kerrSchildCoefficient G m r a c)
      (kerrPrincipalNullCovector r a x y z) = 0 := by
  exact kerrSchildOperator4_sq_zero _ _
    (kerrPrincipalNullCovector_is_null r a x y z c hr hden hxy hz)

/-- The coordinate Kerr metric, with coefficient `G m r / Σ` and the outgoing
principal null covector.  This is an algebraic Kerr--Schild tensor; no claim
about a Lorentzian manifold, field equations, or global spacetime is bundled
into this definition. -/
noncomputable def kerrMetric4 (G m r a c x y z : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  kerrSchildMetric4 (kerrSchildCoefficient G m r a c)
    (kerrPrincipalNullCovector r a x y z)

/-- The actual oblate-chart Kerr matrix is the specialization of the
background-operator Kerr--Schild construction to its principal null
covector. -/
theorem kerrMetric4_eq_operator (G m r a c x y z : ℝ) :
    kerrMetric4 G m r a c x y z =
      operatorKerrSchildMetric minkowskiMetric4
        (kerrSchildOperator4 (kerrSchildCoefficient G m r a c)
          (kerrPrincipalNullCovector r a x y z)) := by
  exact kerrSchildMetric4_eq_operator _ _

/-- The concrete Kerr metric from the oblate chart has a two-sided inverse
obtained by applying the generic ordered-operator theorem to the represented
principal null covector. -/
theorem kerrMetric4_operator_two_sided_inverse
    (G m r a c x y z : ℝ) (hr : r ≠ 0) (hden : r * r + a * a ≠ 0)
    (hxy : x * x + y * y = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    operatorKerrSchildMetric minkowskiMetric4
        (kerrSchildOperator4 (kerrSchildCoefficient G m r a c)
          (kerrPrincipalNullCovector r a x y z)) *
        ((1 - kerrSchildOperator4 (kerrSchildCoefficient G m r a c)
          (kerrPrincipalNullCovector r a x y z)) * minkowskiMetric4) = 1 ∧
      ((1 - kerrSchildOperator4 (kerrSchildCoefficient G m r a c)
          (kerrPrincipalNullCovector r a x y z)) * minkowskiMetric4) *
        operatorKerrSchildMetric minkowskiMetric4
          (kerrSchildOperator4 (kerrSchildCoefficient G m r a c)
            (kerrPrincipalNullCovector r a x y z)) = 1 := by
  exact kerrSchildMetric4_operator_two_sided_inverse _ _
    (kerrPrincipalNullCovector_is_null r a x y z c hr hden hxy hz)

/-- The generic ordered operator inverse is the same matrix as the explicit
coordinate Kerr inverse. The proof uses uniqueness of a two-sided inverse in
the actual `4 × 4` matrix algebra. -/
theorem kerrMetric4_operator_inverse_eq_coordinate
    (G m r a c x y z : ℝ) (hr : r ≠ 0) (hden : r * r + a * a ≠ 0)
    (hxy : x * x + y * y = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    ((1 - kerrSchildOperator4 (kerrSchildCoefficient G m r a c)
      (kerrPrincipalNullCovector r a x y z)) * minkowskiMetric4) =
      kerrSchildInverse4 (kerrSchildCoefficient G m r a c)
        (kerrPrincipalNullCovector r a x y z) := by
  let N := kerrSchildOperator4 (kerrSchildCoefficient G m r a c)
    (kerrPrincipalNullCovector r a x y z)
  let K := kerrSchildInverse4 (kerrSchildCoefficient G m r a c)
    (kerrPrincipalNullCovector r a x y z)
  have hnull := kerrPrincipalNullCovector_is_null r a x y z c hr hden hxy hz
  have hCA : ((1 - N) * minkowskiMetric4) *
      operatorKerrSchildMetric minkowskiMetric4 N = 1 :=
    (kerrMetric4_operator_two_sided_inverse G m r a c x y z hr hden hxy hz).2
  have hAK : operatorKerrSchildMetric minkowskiMetric4 N * K = 1 := by
    rw [← kerrMetric4_eq_operator G m r a c x y z]
    exact kerrSchildMetric4_mul_inverse _ _ hnull
  change (1 - N) * minkowskiMetric4 = K
  calc
    (1 - N) * minkowskiMetric4 =
        ((1 - N) * minkowskiMetric4) *
          (operatorKerrSchildMetric minkowskiMetric4 N * K) := by
            rw [hAK]
            simp
    _ = (((1 - N) * minkowskiMetric4) *
          operatorKerrSchildMetric minkowskiMetric4 N) * K := by
            rw [← Matrix.mul_assoc]
    _ = K := by rw [hCA]; simp

/-- The explicitly constructed coordinate Kerr--Schild matrix is symmetric. -/
theorem kerrMetric4_symmetric (G m r a c x y z : ℝ) :
    (kerrMetric4 G m r a c x y z).transpose = kerrMetric4 G m r a c x y z := by
  exact kerrSchildMetric4_symmetric _ _

/-- For the actual coordinate Kerr metric, the oblate-coordinate hypotheses
make its generating principal covector null, so the rank-one deformation
preserves that principal direction. This remains a coordinate-level theorem:
it does not assert a global null congruence or solve Einstein's equations. -/
theorem kerrMetric4_contract_principal_null
    (G m r a c x y z : ℝ) (hr : r ≠ 0) (hden : r * r + a * a ≠ 0)
    (hxy : x * x + y * y = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    contract4 (kerrMetric4 G m r a c x y z)
        (minkowskiRaise4 (kerrPrincipalNullCovector r a x y z)) =
      kerrPrincipalNullCovector r a x y z := by
  apply kerrSchild_contract_null_direction
  exact kerrPrincipalNullCovector_is_null r a x y z c hr hden hxy hz

/-- In oblate coordinates, the constructed Kerr--Schild metric has the
explicit rank-one inverse above. The geometric chart hypotheses establish
nullity of the principal covector; the inverse identity is then inherited
from the matrix theorem. -/
theorem kerrMetric4_mul_inverse
    (G m r a c x y z : ℝ) (hr : r ≠ 0) (hden : r * r + a * a ≠ 0)
    (hxy : x * x + y * y = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    kerrMetric4 G m r a c x y z *
      kerrSchildInverse4 (kerrSchildCoefficient G m r a c)
        (kerrPrincipalNullCovector r a x y z) = 1 := by
  apply kerrSchildMetric4_mul_inverse
  exact kerrPrincipalNullCovector_is_null r a x y z c hr hden hxy hz

/-- The same coordinate Kerr inverse is two-sided. -/
theorem kerrMetric4_inverse_mul
    (G m r a c x y z : ℝ) (hr : r ≠ 0) (hden : r * r + a * a ≠ 0)
    (hxy : x * x + y * y = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    kerrSchildInverse4 (kerrSchildCoefficient G m r a c)
      (kerrPrincipalNullCovector r a x y z) *
        kerrMetric4 G m r a c x y z = 1 := by
  apply kerrSchildInverse_mul_metric4
  exact kerrPrincipalNullCovector_is_null r a x y z c hr hden hxy hz

/-- The coordinate Kerr metric also preserves the Minkowski volume
determinant under the oblate-coordinate hypotheses that make its principal
covector null. -/
theorem kerrMetric4_det
    (G m r a c x y z : ℝ) (hr : r ≠ 0) (hden : r * r + a * a ≠ 0)
    (hxy : x * x + y * y = (r * r + a * a) * (1 - c * c))
    (hz : z = r * c) :
    (kerrMetric4 G m r a c x y z).det = -1 := by
  exact kerrSchildMetric4_det (kerrSchildCoefficient G m r a c)
    (kerrPrincipalNullCovector r a x y z)
    (kerrPrincipalNullCovector_is_null r a x y z c hr hden hxy hz)

end KerrSchildMetric

end InfoGeometry.Twistor.KerrAlgebraicCore
