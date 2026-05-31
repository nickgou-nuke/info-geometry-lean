import Mathlib
import InfoGeometry.Analysis.AsanoContractionNative
import InfoGeometry.Analysis.AsanoRuelleObstruction
import InfoGeometry.Canonical.AsanoRuelleCounterexample
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet
import InfoGeometry.Canonical.PrimePartitionPolynomials
import InfoGeometry.Canonical.LeeYangStabilityPacket

/-!
# InfoGeometry.Canonical.LeeYangAsanoDigest

Lean-native digest of the Asano/Ruelle proof family behind the Lee--Yang
finite stability socket.

This file records the theorem shapes extracted from the literature:

* Asano-Ruelle contraction for a separately affine two-variable polynomial;
* Grace's theorem for multiaffine symmetric diagonal slices;
* the finite Lee--Yang source claim already used by the repository.

No contraction proof is claimed here.  The file is the theorem-packet and
owner-map surface that keeps the missing proof substrate explicit.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoDigest

open InfoGeometry.Canonical.PrimeHurwitzLimit
open InfoGeometry.Canonical.PrimePartitionPolynomials
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet

/-- Separately affine two-variable polynomial written in coefficient form. -/
@[rep_depth thermo]
structure TwoVarAffinePolynomial where
  A : ℂ
  B : ℂ
  C : ℂ
  D : ℂ

namespace TwoVarAffinePolynomial

/-- Evaluation of a separately affine two-variable polynomial. -/
@[rep_depth thermo]
def eval (P : TwoVarAffinePolynomial) (z1 z2 : ℂ) : ℂ :=
  P.A + P.B * z1 + P.C * z2 + P.D * z1 * z2

/-- Evaluation at `z1 = 0` eliminates the `B` and `D` terms. -/
@[rep_depth thermo]
theorem eval_zero_left (P : TwoVarAffinePolynomial) (z2 : ℂ) :
    P.eval 0 z2 = P.A + P.C * z2 := by
  simp [eval]

/-- Evaluation at `z2 = 0` eliminates the `C` and `D` terms. -/
@[rep_depth thermo]
theorem eval_zero_right (P : TwoVarAffinePolynomial) (z1 : ℂ) :
    P.eval z1 0 = P.A + P.B * z1 := by
  simp [eval]

/-- Evaluation on the diagonal is a univariate quadratic in `z`. -/
@[rep_depth thermo]
theorem eval_diag (P : TwoVarAffinePolynomial) (z : ℂ) :
    P.eval z z = P.A + (P.B + P.C) * z + P.D * z ^ 2 := by
  unfold eval
  ring_nf

/-- Separately affine form in the first variable. -/
@[rep_depth thermo]
theorem eval_affine_left (P : TwoVarAffinePolynomial) (z1 z2 : ℂ) :
    P.eval z1 z2 = (P.A + P.C * z2) + (P.B + P.D * z2) * z1 := by
  unfold eval
  ring

/-- Separately affine form in the second variable. -/
@[rep_depth thermo]
theorem eval_affine_right (P : TwoVarAffinePolynomial) (z1 z2 : ℂ) :
    P.eval z1 z2 = (P.A + P.B * z1) + (P.C + P.D * z1) * z2 := by
  unfold eval
  ring

/-! ## Nondegenerate Asano algebra: root maps and pole exclusion -/

/--
Solving the bivariate affine equation for the second variable.

If `C + D*z1 ≠ 0`, then the zero of

`A + B*z1 + C*z2 + D*z1*z2`

in the second variable is

`z2 = -(A + B*z1)/(C + D*z1)`.
-/
@[rep_depth thermo]
theorem root_iff_z2_eq_of_right_coeff_ne
    (P : TwoVarAffinePolynomial)
    (z1 z2 : ℂ)
    (hcoeff : P.C + P.D * z1 ≠ 0) :
    P.eval z1 z2 = 0 ↔
      z2 = - (P.A + P.B * z1) / (P.C + P.D * z1) := by
  constructor
  · intro hroot
    have hroot' :
        (P.A + P.B * z1) + (P.C + P.D * z1) * z2 = 0 := by
      simpa [P.eval_affine_right z1 z2] using hroot
    have hlin :
        (P.C + P.D * z1) * z2 = - (P.A + P.B * z1) := by
      calc
        (P.C + P.D * z1) * z2
            =
          ((P.A + P.B * z1) + (P.C + P.D * z1) * z2)
            - (P.A + P.B * z1) := by ring
        _ = 0 - (P.A + P.B * z1) := by rw [hroot']
        _ = - (P.A + P.B * z1) := by ring
    exact
      (eq_div_iff_mul_eq hcoeff :
        z2 = - (P.A + P.B * z1) / (P.C + P.D * z1)
          ↔
        z2 * (P.C + P.D * z1) = - (P.A + P.B * z1)).2
        (by simpa [mul_comm] using hlin)
  · intro hz2
    rw [P.eval_affine_right, hz2]
    have hmul :
        (P.C + P.D * z1) * (-(P.A + P.B * z1) / (P.C + P.D * z1))
          = - (P.A + P.B * z1) := by
      field_simp [hcoeff]
    rw [hmul]
    ring

/--
Solving the bivariate affine equation for the first variable.

If `B + D*z2 ≠ 0`, then the zero in the first variable is

`z1 = -(A + C*z2)/(B + D*z2)`.
-/
@[rep_depth thermo]
theorem root_iff_z1_eq_of_left_coeff_ne
    (P : TwoVarAffinePolynomial)
    (z1 z2 : ℂ)
    (hcoeff : P.B + P.D * z2 ≠ 0) :
    P.eval z1 z2 = 0 ↔
      z1 = - (P.A + P.C * z2) / (P.B + P.D * z2) := by
  constructor
  · intro hroot
    have hroot' :
        (P.A + P.C * z2) + (P.B + P.D * z2) * z1 = 0 := by
      simpa [P.eval_affine_left z1 z2] using hroot
    have hlin :
        (P.B + P.D * z2) * z1 = - (P.A + P.C * z2) := by
      calc
        (P.B + P.D * z2) * z1
            =
          ((P.A + P.C * z2) + (P.B + P.D * z2) * z1)
            - (P.A + P.C * z2) := by ring
        _ = 0 - (P.A + P.C * z2) := by rw [hroot']
        _ = - (P.A + P.C * z2) := by ring
    exact
      (eq_div_iff_mul_eq hcoeff :
        z1 = - (P.A + P.C * z2) / (P.B + P.D * z2)
          ↔
        z1 * (P.B + P.D * z2) = - (P.A + P.C * z2)).2
        (by simpa [mul_comm] using hlin)
  · intro hz1
    rw [P.eval_affine_left, hz1]
    have hmul :
        (P.B + P.D * z2) * (-(P.A + P.C * z2) / (P.B + P.D * z2))
          = - (P.A + P.C * z2) := by
      field_simp [hcoeff]
    rw [hmul]
    ring

/--
Nondegenerate left-pole exclusion.

If `A*D - B*C ≠ 0`, then no zero of `P.eval` can occur at a point satisfying
`C + D*z1 = 0`.
-/
@[rep_depth thermo]
theorem no_root_at_left_pole_of_det_ne_zero
    (P : TwoVarAffinePolynomial)
    (hdet : P.A * P.D - P.B * P.C ≠ 0)
    {z1 z2 : ℂ}
    (hpole : P.C + P.D * z1 = 0) :
    P.eval z1 z2 ≠ 0 := by
  intro hroot

  have hnum : P.A + P.B * z1 = 0 := by
    have hroot' :
        (P.A + P.B * z1) + (P.C + P.D * z1) * z2 = 0 := by
      simpa [P.eval_affine_right z1 z2] using hroot
    rw [hpole] at hroot'
    simpa using hroot'

  have hdet_zero : P.A * P.D - P.B * P.C = 0 := by
    calc
      P.A * P.D - P.B * P.C
          =
        (P.A + P.B * z1) * P.D - P.B * (P.C + P.D * z1) := by
          ring
      _ = 0 * P.D - P.B * 0 := by
          rw [hnum, hpole]
      _ = 0 := by ring

  exact hdet hdet_zero

/--
Nondegenerate right-pole exclusion.

If `A*D - B*C ≠ 0`, then no zero of `P.eval` can occur at a point satisfying
`B + D*z2 = 0`.
-/
@[rep_depth thermo]
theorem no_root_at_right_pole_of_det_ne_zero
    (P : TwoVarAffinePolynomial)
    (hdet : P.A * P.D - P.B * P.C ≠ 0)
    {z1 z2 : ℂ}
    (hpole : P.B + P.D * z2 = 0) :
    P.eval z1 z2 ≠ 0 := by
  intro hroot

  have hnum : P.A + P.C * z2 = 0 := by
    have hroot' :
        (P.A + P.C * z2) + (P.B + P.D * z2) * z1 = 0 := by
      simpa [P.eval_affine_left z1 z2] using hroot
    rw [hpole] at hroot'
    simpa using hroot'

  have hdet_zero : P.A * P.D - P.B * P.C = 0 := by
    calc
      P.A * P.D - P.B * P.C
          =
        (P.A + P.C * z2) * P.D - (P.B + P.D * z2) * P.C := by
          ring
      _ = 0 * P.D - 0 * P.C := by
          rw [hnum, hpole]
      _ = 0 := by ring

  exact hdet hdet_zero

/--
Graph constraint from the zero-free hypothesis.

If `z1 ∉ K1`, and the second-variable root is defined, then that root must
lie in `K2`; otherwise one obtains a forbidden zero off `K1 × K2`.
-/
@[rep_depth thermo]
theorem rootMap_z2_mem_K2_of_zero_free
    (P : TwoVarAffinePolynomial)
    (K1 K2 : Set ℂ)
    (hzeroFree :
      ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → P.eval z1 z2 ≠ 0)
    {z1 : ℂ}
    (hz1 : z1 ∉ K1)
    (hcoeff : P.C + P.D * z1 ≠ 0) :
    - (P.A + P.B * z1) / (P.C + P.D * z1) ∈ K2 := by
  by_contra hnot
  have hroot :
      P.eval z1
        (- (P.A + P.B * z1) / (P.C + P.D * z1)) = 0 := by
    exact
      (P.root_iff_z2_eq_of_right_coeff_ne
        z1
        (- (P.A + P.B * z1) / (P.C + P.D * z1))
        hcoeff).2 rfl
  exact hzeroFree z1
    (- (P.A + P.B * z1) / (P.C + P.D * z1))
    hz1 hnot hroot

/--
Dual graph constraint from the zero-free hypothesis.

If `z2 ∉ K2`, and the first-variable root is defined, then that root must
lie in `K1`.
-/
@[rep_depth thermo]
theorem rootMap_z1_mem_K1_of_zero_free
    (P : TwoVarAffinePolynomial)
    (K1 K2 : Set ℂ)
    (hzeroFree :
      ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → P.eval z1 z2 ≠ 0)
    {z2 : ℂ}
    (hz2 : z2 ∉ K2)
    (hcoeff : P.B + P.D * z2 ≠ 0) :
    - (P.A + P.C * z2) / (P.B + P.D * z2) ∈ K1 := by
  by_contra hnot
  have hroot :
      P.eval
        (- (P.A + P.C * z2) / (P.B + P.D * z2))
        z2 = 0 := by
    exact
      (P.root_iff_z1_eq_of_left_coeff_ne
        (- (P.A + P.C * z2) / (P.B + P.D * z2))
        z2
        hcoeff).2 rfl
  exact hzeroFree
    (- (P.A + P.C * z2) / (P.B + P.D * z2))
    z2 hnot hz2 hroot

/--
Determinant-zero factorization of a separately affine polynomial.

This is the easy algebraic branch of the Asano-Ruelle lemma:
if `A*D = B*C` and `D ≠ 0`, then

`A + B z1 + C z2 + D z1 z2 = D * (z1 + C/D) * (z2 + B/D)`.
-/
@[rep_depth thermo]
theorem factor_det_zero
    (P : TwoVarAffinePolynomial) (hD : P.D ≠ 0)
    (h : P.A * P.D - P.B * P.C = 0)
    (z1 z2 : ℂ) :
    P.eval z1 z2 = P.D * (z1 + P.C / P.D) * (z2 + P.B / P.D) := by
  have hmul : P.A * P.D = P.B * P.C := by
    simpa [sub_eq_zero] using h
  have hmul' : P.D * P.A = P.B * P.C := by
    simpa [mul_comm] using hmul
  have hA : P.A = (P.B * P.C) / P.D := by
    exact
      (eq_div_iff_mul_eq hD :
          P.A = (P.B * P.C) / P.D ↔ P.A * P.D = P.B * P.C).2 hmul
  rw [TwoVarAffinePolynomial.eval, hA]
  field_simp [hD]
  ring

/--
Zero locus of the determinant-zero factorization.

Under the determinant-zero hypothesis, the vanishing of `P.eval z1 z2`
is equivalent to one of the linear factors vanishing.
-/
@[rep_depth thermo]
theorem factor_det_zero_iff
    (P : TwoVarAffinePolynomial) (hD : P.D ≠ 0)
    (h : P.A * P.D - P.B * P.C = 0)
    (z1 z2 : ℂ) :
    P.eval z1 z2 = 0 ↔
      (z1 + P.C / P.D = 0 ∨ z2 + P.B / P.D = 0) := by
  rw [P.factor_det_zero hD h]
  constructor
  · intro hz
    have h' : P.D * ((z1 + P.C / P.D) * (z2 + P.B / P.D)) = 0 := by
      simpa [mul_assoc] using hz
    rcases mul_eq_zero.mp h' with hD0 | hq
    · exact False.elim (hD hD0)
    · exact mul_eq_zero.mp hq
  · intro hz
    rcases hz with hz | hz
    · simp [hz]
    · simp [hz]

/-- Asano contraction `A + D z`. -/
@[rep_depth thermo]
def contract (P : TwoVarAffinePolynomial) (z : ℂ) : ℂ :=
  P.A + P.D * z

/-- The contracted polynomial is the explicit `A + D z` expression. -/
@[rep_depth thermo]
theorem contract_eq (P : TwoVarAffinePolynomial) (z : ℂ) :
    P.contract z = P.A + P.D * z := rfl

/-- Zero locus of the contracted one-variable polynomial. -/
@[rep_depth thermo]
theorem contract_zero_iff
    (P : TwoVarAffinePolynomial) (hD : P.D ≠ 0) (z : ℂ) :
    P.contract z = 0 ↔ z = - P.A / P.D := by
  unfold contract
  constructor
  · intro hz
    have hz' : P.A = - (P.D * z) := by
      simpa using (add_eq_zero_iff_eq_neg).1 hz
    have hneg : - P.A = P.D * z := by
      have := congrArg Neg.neg hz'
      simpa using this
    have hz'' : z * P.D = - P.A := by
      simpa [mul_comm] using hneg.symm
    exact (eq_div_iff_mul_eq hD :
      z = - P.A / P.D ↔ z * P.D = - P.A).2 hz''
  · intro hz
    rw [hz]
    field_simp [hD]
    ring

/-- The Asano quadratic obtained after substituting `u = z / v`. -/
@[rep_depth thermo]
def asanoQuadratic (P : TwoVarAffinePolynomial) (z v : ℂ) : ℂ :=
  P.C * v ^ 2 + (P.A + P.D * z) * v + P.B * z

/-- Multiplying the specialized bivariate evaluation by `v` gives the Asano quadratic. -/
@[rep_depth thermo]
theorem mul_eval_eq_asanoQuadratic
    (P : TwoVarAffinePolynomial) (z v : ℂ) (hv : v ≠ 0) :
    v * P.eval (z / v) v = P.asanoQuadratic z v := by
  unfold eval asanoQuadratic
  field_simp [hv]
  ring

/--
Case 3 algebraic reduction:
`P.eval (z/v) v = 0` if and only if the Asano quadratic vanishes.
This is the purely algebraic reduction before the Riemann-sphere topology.
-/
@[rep_depth thermo]
theorem asano_quadratic_equivalence
    (P : TwoVarAffinePolynomial) (z v : ℂ) (hv : v ≠ 0) :
    P.eval (z / v) v = 0 ↔ P.asanoQuadratic z v = 0 := by
  constructor
  · intro h
    have hmul : v * P.eval (z / v) v = 0 := by
      rw [h, mul_zero]
    rw [P.mul_eval_eq_asanoQuadratic z v hv] at hmul
    exact hmul
  · intro h
    have hmul : v * P.eval (z / v) v = 0 := by
      rw [P.mul_eval_eq_asanoQuadratic z v hv, h]
    exact (mul_eq_zero.mp hmul).resolve_left hv

/-- If the contracted root vanishes, the Asano quadratic drops its middle term. -/
@[rep_depth thermo]
theorem asano_quadratic_at_contracted_root
    (P : TwoVarAffinePolynomial) (z v : ℂ)
    (hz_root : P.contract z = 0) :
    P.asanoQuadratic z v = P.C * v ^ 2 + P.B * z := by
  have hmid : P.A + P.D * z = 0 := by
    simpa [TwoVarAffinePolynomial.contract] using hz_root
  unfold asanoQuadratic
  rw [hmid]
  ring

/-- Minkowski-style product of two subsets of `ℂ`. -/
@[rep_depth thermo]
def setMul (K1 K2 : Set ℂ) : Set ℂ :=
  {z : ℂ | ∃ u ∈ K1, ∃ v ∈ K2, u * v = z}

/-- Reordered presentation of the product set `K1 ⋆ K2`. -/
@[rep_depth thermo]
theorem mem_setMul_iff
    {K1 K2 : Set ℂ} {z : ℂ} :
    z ∈ setMul K1 K2 ↔ ∃ u ∈ K1, ∃ v ∈ K2, u * v = z := Iff.rfl

/-- Swapping the factors of the product set does not change the set. -/
@[rep_depth thermo]
theorem setMul_comm
    (K1 K2 : Set ℂ) :
    setMul K1 K2 = setMul K2 K1 := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨u, hu, v, hv, h⟩
    refine ⟨v, hv, u, hu, ?_⟩
    simpa [mul_comm] using h
  · intro hz
    rcases hz with ⟨u, hu, v, hv, h⟩
    refine ⟨v, hv, u, hu, ?_⟩
    simpa [mul_comm] using h

/-- The Minkowski product of sets is associative. -/
@[rep_depth thermo]
theorem setMul_assoc
    (K1 K2 K3 : Set ℂ) :
    setMul (setMul K1 K2) K3 = setMul K1 (setMul K2 K3) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨u, hu, w, hw, h⟩
    rcases hu with ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b * w, ?_, ?_⟩
    · exact ⟨b, hb, w, hw, rfl⟩
    · calc
        a * (b * w) = (a * b) * w := by rw [mul_assoc]
        _ = z := h
  · intro hz
    rcases hz with ⟨a, ha, v, hv, h⟩
    rcases hv with ⟨b, hb, w, hw, rfl⟩
    refine ⟨a * b, ?_, w, hw, ?_⟩
    · exact ⟨a, ha, b, hb, rfl⟩
    · calc
        (a * b) * w = a * (b * w) := by rw [mul_assoc]
        _ = z := h

/-- Recursive Minkowski product of a list of subsets of `ℂ`. -/
@[rep_depth thermo]
def iteratedSetMul : List (Set ℂ) → Set ℂ
  | [] => {1}
  | K :: Ks => setMul K (iteratedSetMul Ks)

/-- The empty iterated product is `{1}`. -/
@[rep_depth thermo]
theorem iteratedSetMul_nil :
    iteratedSetMul [] = ({1} : Set ℂ) := rfl

/-- Multiplication by the unit set `{1}` is neutral on the left. -/
@[rep_depth thermo]
theorem setMul_one_left
    (K : Set ℂ) :
    setMul ({1} : Set ℂ) K = K := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨u, hu, v, hv, h⟩
    simp at hu
    rcases hu with rfl
    have hzv : z = v := by simpa [one_mul] using h.symm
    simpa [hzv] using hv
  · intro hz
    refine ⟨1, by simp, z, hz, ?_⟩
    simp

/-- Multiplication by the unit set `{1}` is neutral on the right. -/
@[rep_depth thermo]
theorem setMul_one_right
    (K : Set ℂ) :
    setMul K ({1} : Set ℂ) = K := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨u, hu, v, hv, h⟩
    simp at hv
    rcases hv with rfl
    have huz : z = u := by simpa [mul_one] using h.symm
    simpa [huz] using hu
  · intro hz
    refine ⟨z, hz, 1, by simp, ?_⟩
    simp

/-- Appending a set to the iterated product multiplies on the left. -/
@[rep_depth thermo]
theorem iteratedSetMul_cons
    (K : Set ℂ) (Ks : List (Set ℂ)) :
    iteratedSetMul (K :: Ks) = setMul K (iteratedSetMul Ks) := rfl

/-- Appending a list of factors corresponds to set multiplication on the right. -/
@[rep_depth thermo]
theorem iteratedSetMul_append
    (Ks₁ Ks₂ : List (Set ℂ)) :
    iteratedSetMul (Ks₁ ++ Ks₂) =
      setMul (iteratedSetMul Ks₁) (iteratedSetMul Ks₂) := by
  induction Ks₁ with
  | nil =>
      simp [iteratedSetMul, setMul_one_left]
  | cons K Ks ih =>
      simp [iteratedSetMul, ih, setMul_assoc]

/-- If a product vanishes, the negated root lies in the product set. -/
@[rep_depth thermo]
theorem neg_mem_setMul_of_eq
    {K1 K2 : Set ℂ} {u v z : ℂ}
    (hu : u ∈ K1) (hv : v ∈ K2)
    (hz : z = -u * v) :
    (-z) ∈ setMul K1 K2 := by
  refine ⟨u, hu, v, hv, ?_⟩
  simp [hz]

/--
Case 2 root-location transfer for the Asano contraction.

If `P.eval z₁ z₂ = 0` only when `z₁ ∈ K₁` and `z₂ ∈ K₂`, and the
determinant vanishes with `D ≠ 0`, then every contracted root transfers to
the Minkowski product of the microscopic root sets.
-/
@[rep_depth thermo]
theorem asano_case2_zero_transfer
    (P : TwoVarAffinePolynomial) (K1 K2 : Set ℂ)
    (hD : P.D ≠ 0) (hDet : P.A * P.D - P.B * P.C = 0)
    (hRoots : ∀ z1 z2 : ℂ, P.eval z1 z2 = 0 → z1 ∈ K1 ∧ z2 ∈ K2) :
    ∀ z : ℂ, P.contract z = 0 → (-z) ∈ setMul K1 K2 := by
  intro z hz
  have hzEq : z = - P.A / P.D := (P.contract_zero_iff hD z).1 hz
  have hEval : P.eval (- P.C / P.D) (- P.B / P.D) = 0 := by
    exact
      (P.factor_det_zero_iff hD hDet (- P.C / P.D) (- P.B / P.D)).2
        (Or.inl (by ring))
  have hmem := hRoots (- P.C / P.D) (- P.B / P.D) hEval
  rcases hmem with ⟨hu, hv⟩
  refine ⟨- P.C / P.D, hu, - P.B / P.D, hv, ?_⟩
  have hAD : P.A * P.D = P.B * P.C := by
    simpa [sub_eq_zero] using hDet
  have hCB : P.C * P.B = P.D * P.A := by
    calc
      P.C * P.B = P.B * P.C := by ring
      _ = P.A * P.D := hAD.symm
      _ = P.D * P.A := by ring
  have hprod : (- P.C / P.D) * (- P.B / P.D) = P.A / P.D := by
    field_simp [hD]
    exact hCB
  have hzneg : -z = P.A / P.D := by
    rw [hzEq]
    ring
  simpa [hzneg, hprod]

end TwoVarAffinePolynomial

/-- The forbidden contracted set `-K1·K2`. -/
@[rep_depth thermo]
def asanoForbiddenSet (K1 K2 : Set ℂ) : Set ℂ :=
  {z : ℂ | ∃ u ∈ K1, ∃ v ∈ K2, z = -u * v}

/--
Monotonicity of the Asano forbidden set under factor-set inclusion.
-/
@[rep_depth thermo]
theorem asanoForbiddenSet_mono
    {K1 K1' K2 K2' : Set ℂ}
    (h1 : K1 ⊆ K1')
    (h2 : K2 ⊆ K2') :
    asanoForbiddenSet K1 K2 ⊆ asanoForbiddenSet K1' K2' := by
  intro z hz
  rcases hz with ⟨u, hu, v, hv, hzuv⟩
  exact ⟨u, h1 hu, v, h2 hv, hzuv⟩

/-- Introduction rule for the Asano forbidden set. -/
@[rep_depth thermo]
theorem mem_asanoForbiddenSet
    {K1 K2 : Set ℂ} {z u v : ℂ}
    (hu : u ∈ K1) (hv : v ∈ K2) (hz : z = -u * v) :
    z ∈ asanoForbiddenSet K1 K2 := by
  exact ⟨u, hu, v, hv, hz⟩

/-- Elimination rule for the Asano forbidden set. -/
@[rep_depth thermo]
theorem asanoForbiddenSet_elim
    {K1 K2 : Set ℂ} {z : ℂ}
    (hz : z ∈ asanoForbiddenSet K1 K2) :
    ∃ u ∈ K1, ∃ v ∈ K2, z = -u * v := hz

/-- A point is outside the Asano forbidden set if it avoids every product. -/
@[rep_depth thermo]
theorem not_mem_asanoForbiddenSet_of_forall
    {K1 K2 : Set ℂ} {z : ℂ}
    (h : ∀ u ∈ K1, ∀ v ∈ K2, z ≠ -u * v) :
    z ∉ asanoForbiddenSet K1 K2 := by
  intro hz
  rcases hz with ⟨u, hu, v, hv, rfl⟩
  exact h u hu v hv rfl

/-- The Asano forbidden set is empty if one factor set is empty. -/
@[rep_depth thermo]
theorem asanoForbiddenSet_empty_left
    (K2 : Set ℂ) :
    asanoForbiddenSet (∅ : Set ℂ) K2 = ∅ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨u, hu, v, hv, hz⟩
    simp at hu
  · intro hz
    simp at hz

/-- The Asano forbidden set is empty if the second factor set is empty. -/
@[rep_depth thermo]
theorem asanoForbiddenSet_empty_right
    (K1 : Set ℂ) :
    asanoForbiddenSet K1 (∅ : Set ℂ) = ∅ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨u, hu, v, hv, hz⟩
    simp at hv
  · intro hz
    simp at hz

/-- The Asano forbidden set is symmetric in its two factor sets. -/
@[rep_depth thermo]
theorem asanoForbiddenSet_comm
    (K1 K2 : Set ℂ) :
    asanoForbiddenSet K1 K2 = asanoForbiddenSet K2 K1 := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨u, hu, v, hv, hz⟩
    refine ⟨v, hv, u, hu, ?_⟩
    simpa [mul_comm] using hz
  · intro hz
    rcases hz with ⟨u, hu, v, hv, hz⟩
    refine ⟨v, hv, u, hu, ?_⟩
    simpa [mul_comm] using hz

/--
In the determinant-zero branch of the Asano factorization, the contracted root
`-A/D` is exhibited explicitly as a forbidden-set element built from
`-C/D` and `-B/D`.
-/
@[rep_depth thermo]
theorem det_zero_contracted_root_mem_forbidden
    (P : TwoVarAffinePolynomial) (hD : P.D ≠ 0)
    (h : P.A * P.D - P.B * P.C = 0) :
    (- P.A / P.D) ∈ asanoForbiddenSet { - P.C / P.D } { - P.B / P.D } := by
  have hAD : P.A * P.D = P.B * P.C := by
    simpa [sub_eq_zero] using h
  have hCB : P.C * P.B = P.D * P.A := by
    calc
      P.C * P.B = P.B * P.C := by ring
      _ = P.A * P.D := hAD.symm
      _ = P.D * P.A := by ring
  refine ⟨- P.C / P.D, by simp, - P.B / P.D, by simp, ?_⟩
  have hmul : (- P.C / P.D) * (- P.B / P.D) = P.A / P.D := by
    field_simp [hD]
    exact hCB
  have hneg : - P.A / P.D = -(P.A / P.D) := by
    simpa using (neg_div P.D P.A)
  simpa [hmul] using hneg

/--
Source theorem shape for the Asano-Ruelle contraction lemma.

Literature extraction:
if `Φ(z1,z2) = A + B z1 + C z2 + D z1 z2` is nonvanishing whenever
`z1 ∉ K1` and `z2 ∉ K2`, with `0 ∉ K1` and `0 ∉ K2`, then the contracted
polynomial `A + D z` is nonvanishing whenever `z ∉ -K1·K2`.
-/
@[rep_depth thermo]
def AsanoRuelleLemmaSourceClaim : Prop :=
  ∀ (K1 K2 : Set ℂ) (P : TwoVarAffinePolynomial),
    0 ∉ K1 → 0 ∉ K2 →
      IsClosed K1 → IsClosed K2 →
      (∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → P.eval z1 z2 ≠ 0) →
        ∀ z : ℂ, z ∉ asanoForbiddenSet K1 K2 → P.contract z ≠ 0

/--
Truly unrestricted Asano-Ruelle source claim (no `0 ∉ K₁`, `0 ∉ K₂` guards).

This shape is known to be false; see
`asanoRuelleLemmaSourceClaimUnrestricted_false`.
-/
@[rep_depth thermo]
def AsanoRuelleLemmaSourceClaimUnrestricted : Prop :=
  ∀ (K1 K2 : Set ℂ) (P : TwoVarAffinePolynomial),
    (∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → P.eval z1 z2 ≠ 0) →
      ∀ z : ℂ, z ∉ asanoForbiddenSet K1 K2 → P.contract z ≠ 0

/--
The truly unrestricted Asano-Ruelle source claim is false.

This is the vacuity counterexample (`K₁ = univ`, `K₂ = {0}`) proved in
`Analysis.AsanoRuelleObstruction`.
-/
@[rep_depth thermo]
theorem asanoRuelleLemmaSourceClaimUnrestricted_false :
    ¬ AsanoRuelleLemmaSourceClaimUnrestricted := by
  intro hU
  have hObs :
      ∀ (A B C D : ℂ) (K₁ K₂ : Set ℂ),
        (∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          InfoGeometry.Analysis.AsanoRuelleObstruction.Phi A B C D z₁ z₂ ≠ 0) →
        ∀ z : ℂ,
          z ∉ InfoGeometry.Analysis.AsanoRuelleObstruction.forbiddenProductSet K₁ K₂ →
          InfoGeometry.Analysis.AsanoRuelleObstruction.contractedQ A D z ≠ 0 := by
    intro A B C D K₁ K₂ hPhi z hz
    let P : TwoVarAffinePolynomial := ⟨A, B, C, D⟩
    have hPhi' :
        ∀ z1 z2 : ℂ, z1 ∉ K₁ → z2 ∉ K₂ → P.eval z1 z2 ≠ 0 := by
      intro z1 z2 hz1 hz2
      simpa [P, TwoVarAffinePolynomial.eval, InfoGeometry.Analysis.AsanoRuelleObstruction.Phi]
        using hPhi z1 z2 hz1 hz2
    have hz' : z ∉ asanoForbiddenSet K₁ K₂ := by
      simpa [asanoForbiddenSet, InfoGeometry.Analysis.AsanoRuelleObstruction.forbiddenProductSet] using hz
    have hq' : P.contract z ≠ 0 := hU K₁ K₂ P hPhi' z hz'
    simpa [P, TwoVarAffinePolynomial.contract, InfoGeometry.Analysis.AsanoRuelleObstruction.contractedQ]
      using hq'
  exact InfoGeometry.Analysis.AsanoRuelleObstruction.asanoRuelle_unrestricted_claim_false hObs

/--
Unrestricted nondegenerate Asano-Ruelle source claim.

This strengthens the unrestricted shape by adding `P.D ≠ 0` and
`P.A * P.D - P.B * P.C ≠ 0`, but still without any closed/circular-region
hypothesis on `K₁`, `K₂`.
-/
@[rep_depth thermo]
def AsanoRuelleLemmaSourceClaimUnrestrictedNondegenerate : Prop :=
  ∀ (K1 K2 : Set ℂ) (P : TwoVarAffinePolynomial),
    P.D ≠ 0 →
    P.A * P.D - P.B * P.C ≠ 0 →
    (∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → P.eval z1 z2 ≠ 0) →
      ∀ z : ℂ, z ∉ asanoForbiddenSet K1 K2 → P.contract z ≠ 0

/--
Even the unrestricted nondegenerate source claim is false.

This imports the concrete canonical counterexample (`Phi = z₁ z₂ - 1`,
`Q = -1 + z`, `K₁ = {z | z ≠ 0}`, `K₂ = ∅`).
-/
@[rep_depth thermo]
theorem asanoRuelleLemmaSourceClaimUnrestrictedNondegenerate_false :
    ¬ AsanoRuelleLemmaSourceClaimUnrestrictedNondegenerate := by
  intro hN
  let P : TwoVarAffinePolynomial := ⟨(-1 : ℂ), 0, 0, 1⟩
  have hD : P.D ≠ 0 := by
    simpa [P] using
      InfoGeometry.Canonical.AsanoRuelleCounterexample.nondegenerate_coefficients.1
  have hDet : P.A * P.D - P.B * P.C ≠ 0 := by
    simpa [P] using
      InfoGeometry.Canonical.AsanoRuelleCounterexample.nondegenerate_coefficients.2
  have hPhi :
      ∀ z1 z2 : ℂ,
        z1 ∉ InfoGeometry.Canonical.AsanoRuelleCounterexample.K₁ →
        z2 ∉ InfoGeometry.Canonical.AsanoRuelleCounterexample.K₂ →
        P.eval z1 z2 ≠ 0 := by
    intro z1 z2 hz1 hz2
    have h0 :
        InfoGeometry.Canonical.AsanoRuelleCounterexample.Phi z1 z2 ≠ 0 :=
      InfoGeometry.Canonical.AsanoRuelleCounterexample.Phi_zero_free_off_K₁_K₂
        z1 z2 hz1 hz2
    simpa
      [P, TwoVarAffinePolynomial.eval,
       InfoGeometry.Canonical.AsanoRuelleCounterexample.Phi,
       sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using h0
  have hQ :
      P.contract (1 : ℂ) = 0 := by
    simpa [P, TwoVarAffinePolynomial.contract, InfoGeometry.Canonical.AsanoRuelleCounterexample.Q]
      using InfoGeometry.Canonical.AsanoRuelleCounterexample.Q_one_eq_zero
  have hNotForbidden :
      (1 : ℂ) ∉ asanoForbiddenSet
        InfoGeometry.Canonical.AsanoRuelleCounterexample.K₁
        InfoGeometry.Canonical.AsanoRuelleCounterexample.K₂ := by
    simpa [asanoForbiddenSet, InfoGeometry.Canonical.AsanoRuelleCounterexample.forbiddenProduct]
      using InfoGeometry.Canonical.AsanoRuelleCounterexample.one_not_mem_forbiddenProduct
  exact (hN
      InfoGeometry.Canonical.AsanoRuelleCounterexample.K₁
      InfoGeometry.Canonical.AsanoRuelleCounterexample.K₂
      P hD hDet hPhi (1 : ℂ) hNotForbidden) hQ

/--
Closed-set variant of the Asano-Ruelle source claim.

This is the exact shape consumed by the native topological reduction corridor.
-/
@[rep_depth thermo]
def AsanoRuelleLemmaSourceClaimClosed : Prop :=
  ∀ (K1 K2 : Set ℂ) (P : TwoVarAffinePolynomial),
    0 ∉ K1 → 0 ∉ K2 →
      IsClosed K1 → IsClosed K2 →
      (∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → P.eval z1 z2 ≠ 0) →
        ∀ z : ℂ, z ∉ asanoForbiddenSet K1 K2 → P.contract z ≠ 0

/--
Corrected Asano-Ruelle source claim with explicit analytic guards.

This is the practical theorem surface for the Lee--Yang lane:
in addition to zero-exclusion and zero-freeness off `K₁ × K₂`,
we require `K₁`, `K₂` to be closed and bounded.
-/
@[rep_depth thermo]
def AsanoRuelleLemmaSourceClaimClosedBounded : Prop :=
  ∀ (K1 K2 : Set ℂ) (P : TwoVarAffinePolynomial),
    0 ∉ K1 → 0 ∉ K2 →
      IsClosed K1 → IsClosed K2 →
      Bornology.IsBounded K1 → Bornology.IsBounded K2 →
      (∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → P.eval z1 z2 ≠ 0) →
        ∀ z : ℂ, z ∉ asanoForbiddenSet K1 K2 → P.contract z ≠ 0

/--
Unrestricted Asano-Ruelle source claim implies the closed-set variant.
-/
@[rep_depth thermo]
theorem asanoRuelleLemmaSourceClaimClosed_of_sourceClaim
    (hAR : AsanoRuelleLemmaSourceClaim) :
    AsanoRuelleLemmaSourceClaimClosed := by
  intro K1 K2 P h0K1 h0K2 hClosed1 hClosed2 hPhi z hzOff
  exact hAR K1 K2 P h0K1 h0K2 hClosed1 hClosed2 hPhi z hzOff

/--
The unrestricted guarded source claim implies the closed-bounded claim.
-/
@[rep_depth thermo]
theorem asanoRuelleLemmaSourceClaimClosedBounded_of_sourceClaim
    (hAR : AsanoRuelleLemmaSourceClaim) :
    AsanoRuelleLemmaSourceClaimClosedBounded := by
  intro K1 K2 P h0K1 h0K2 hClosed1 hClosed2 _hB1 _hB2 hPhi z hzOff
  exact hAR K1 K2 P h0K1 h0K2 hClosed1 hClosed2 hPhi z hzOff

/--
Pointwise eliminator for the closed-bounded corrected source claim.
-/
@[rep_depth thermo]
theorem asanoRuelleClosedBounded_apply
    (hARcb : AsanoRuelleLemmaSourceClaimClosedBounded)
    {K1 K2 : Set ℂ} (P : TwoVarAffinePolynomial)
    (h0K1 : 0 ∉ K1) (h0K2 : 0 ∉ K2)
    (hClosed1 : IsClosed K1) (hClosed2 : IsClosed K2)
    (hB1 : Bornology.IsBounded K1) (hB2 : Bornology.IsBounded K2)
    (hPhi : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → P.eval z1 z2 ≠ 0)
    {z : ℂ} (hzOff : z ∉ asanoForbiddenSet K1 K2) :
    P.contract z ≠ 0 :=
  hARcb K1 K2 P h0K1 h0K2 hClosed1 hClosed2 hB1 hB2 hPhi z hzOff

/--
Pointwise eliminator for the closed-set Asano-Ruelle source claim.
-/
@[rep_depth thermo]
theorem asanoRuelleClosed_apply
    (hARc : AsanoRuelleLemmaSourceClaimClosed)
    {K1 K2 : Set ℂ} (P : TwoVarAffinePolynomial)
    (h0K1 : 0 ∉ K1) (h0K2 : 0 ∉ K2)
    (hClosed1 : IsClosed K1) (hClosed2 : IsClosed K2)
    (hPhi : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 → P.eval z1 z2 ≠ 0)
    {z : ℂ} (hzOff : z ∉ asanoForbiddenSet K1 K2) :
    P.contract z ≠ 0 :=
  hARc K1 K2 P h0K1 h0K2 hClosed1 hClosed2 hPhi z hzOff

/--
Asano-Ruelle source claim from the explicit endpoint-nondegenerate branch
hypothesis.

This theorem is fully constructive in Lean and routes through
`Analysis.AsanoContractionNative` (no `sorry`).
-/
@[rep_depth thermo]
theorem asanoRuelleLemmaSourceClaim_of_endpointNonDeg
    (hEndpointNonDeg :
      ∀ {K₁ K₂ : Set ℂ} {A B C D : ℂ},
        (0 : ℂ) ∉ K₁ →
        (0 : ℂ) ∉ K₂ →
        (∀ z₁ z₂ : ℂ,
          z₁ ∉ K₁ →
          z₂ ∉ K₂ →
          InfoGeometry.Analysis.AsanoContractionNative.asanoPoly A B C D z₁ z₂ ≠ 0) →
        D ≠ 0 →
        A * D - B * C ≠ 0 →
        ((C ≠ 0 ∧ -(C / D) ∈ K₁) ∨ (B ≠ 0 ∧ -(B / D) ∈ K₂))) :
    AsanoRuelleLemmaSourceClaim := by
  intro K1 K2 P h0K1 h0K2 _hClosed1 _hClosed2 hPhi z hzOff
  have hzf :
      InfoGeometry.Analysis.AsanoContractionNative.ZeroFreeOutside
        K1 K2 P.A P.B P.C P.D := by
    intro z1 z2 hz1 hz2
    simpa
      [InfoGeometry.Analysis.AsanoContractionNative.ZeroFreeOutside,
       InfoGeometry.Analysis.AsanoContractionNative.asanoPoly,
       TwoVarAffinePolynomial.eval]
      using hPhi z1 z2 hz1 hz2
  have hzOff' :
      z ∉ InfoGeometry.Analysis.AsanoContractionNative.signedProductSet K1 K2 := by
    simpa
      [InfoGeometry.Analysis.AsanoContractionNative.signedProductSet,
       asanoForbiddenSet]
      using hzOff
  have hEndpoint :
      P.D ≠ 0 →
      P.A * P.D - P.B * P.C ≠ 0 →
      ((P.C ≠ 0 ∧ -(P.C / P.D) ∈ K1) ∨ (P.B ≠ 0 ∧ -(P.B / P.D) ∈ K2)) := by
    intro hD hDet
    exact hEndpointNonDeg h0K1 h0K2 hzf hD hDet
  have hne :
      InfoGeometry.Analysis.AsanoContractionNative.asanoContract P.A P.D z ≠ 0 :=
    InfoGeometry.Analysis.AsanoContractionNative.asanoContract_ne_zero_outside_signedProduct_of_endpoint_nonDeg
      h0K1 h0K2 hzf hEndpoint hzOff'
  simpa
    [InfoGeometry.Analysis.AsanoContractionNative.asanoContract,
     TwoVarAffinePolynomial.contract]
    using hne

/--
Source theorem shape for Grace's theorem in the Lee--Yang proof family.

The paper route uses a symmetric multiaffine polynomial whose diagonal slice
is the univariate polynomial with roots in a closed circular region.
The conclusion is that the multiaffine polynomial is nonvanishing whenever
each coordinate avoids that circular region.

This packet records the shape only; it does not attempt the proof.
-/
@[rep_depth thermo]
structure GraceSourceData (n : ℕ) where
  Q : Polynomial ℂ
  Φ : (Fin n → ℂ) → ℂ
  diagonal :
    ∀ z : ℂ, Φ (fun _ : Fin n => z) = Q.eval z
  symmetric : Prop
  multiaffine : Prop

/-- The diagonal slice of a Grace source datum is exactly the univariate slice. -/
@[rep_depth thermo]
theorem GraceSourceData.diagonal_const
    {n : ℕ} (D : GraceSourceData n) (z : ℂ) :
    D.Φ (fun _ : Fin n => z) = D.Q.eval z :=
  D.diagonal z

/--
Grace theorem source claim for a multiaffine symmetric diagonal slice.

The exact proof is literature-owned; the Lean file stores the theorem shape
so that later formalization can target it directly.
-/
@[rep_depth thermo]
def GraceTheoremSourceClaim (n : ℕ) : Prop :=
  ∀ (K : Set ℂ) (D : GraceSourceData n),
    (∀ z : ℂ, D.Q.IsRoot z → z ∈ K) →
      ∀ y : Fin n → ℂ, (∀ i : Fin n, y i ∉ K) → D.Φ y ≠ 0

/--
The exact finite Lee--Yang source claim is the theorem shape already used by
the repository.
-/
@[rep_depth thermo]
def LeeYangPolydiscSourceClaim (N : ℕ) : Prop :=
  ∀ (D : FinitePrimeChainData N) (lam : ℝ), 0 < lam →
    (∀ y : Fin N → ℂ,
      (∀ i : Fin N, PrimeHurwitzLimit.InUnitDisk (y i)) →
        multiPartition D lam y ≠ 0) ∧
    (∀ y : Fin N → ℂ,
      (∀ i : Fin N, PrimeHurwitzLimit.OutsideUnitDisk (y i)) →
        multiPartition D lam y ≠ 0)

/-- Package the standard Lee--Yang witness back into the source-claim shape. -/
@[bridge_target_tag, rep_depth thermo]
theorem leeYangPolydiscSourceClaim_of_sorry
    (LY : LeeYangPolydiscWitness) :
    ∀ N : ℕ, LeeYangPolydiscSourceClaim N := by
  intro N D lam hLam
  exact ⟨LY.inner_zero_free D lam hLam, LY.outer_zero_free D lam hLam⟩

/-- Package the source claim into the standard Lee--Yang witness surface. -/
@[bridge_target_tag, rep_depth thermo]
def leeYangPolydiscWitness_of_sourceClaim
    (H : ∀ N : ℕ, LeeYangPolydiscSourceClaim N) :
    LeeYangPolydiscWitness where
  inner_zero_free := by
    intro N D lam hLam y hy
    exact (H N D lam hLam).1 y hy
  outer_zero_free := by
    intro N D lam hLam y hy
    exact (H N D lam hLam).2 y hy

namespace AsanoInduction

open MvPolynomial

/-- 
Key identity: a multiaffine function in two variables is determined by its values at 0 and 1.
This is the heart of the Asano reduction.
-/
theorem multiaffine_2var_expansion (f : ℂ → ℂ → ℂ) 
    (h0 : ∀ y, ∃ a b, ∀ x, f x y = a + b * x)
    (h1 : ∀ x, ∃ a b, ∀ y, f x y = a + b * y)
    (x y : ℂ) :
    f x y = f 0 0 + (f 1 0 - f 0 0) * x + (f 0 1 - f 0 0) * y + 
            (f 1 1 - f 1 0 - f 0 1 + f 0 0) * x * y := by
  rcases h1 x with ⟨a_x, b_x, h_x⟩
  have ha : a_x = f x 0 := by rw [h_x 0]; ring
  have hb : b_x = f x 1 - f x 0 := by
    have h1_val := h_x 1
    rw [ha] at h1_val
    rw [h1_val]
    ring
  rw [h_x y, ha, hb]
  rcases h0 0 with ⟨a0, b0, h0_0⟩
  rcases h0 1 with ⟨a1, b1, h0_1⟩
  have ha0 : a0 = f 0 0 := by rw [h0_0 0]; ring
  have hb0 : b0 = f 1 0 - f 0 0 := by
    have h := h0_0 1
    rw [ha0] at h
    rw [h]; ring
  have ha1 : a1 = f 0 1 := by rw [h0_1 0]; ring
  have hb1 : b1 = f 1 1 - f 0 1 := by
    have h := h0_1 1
    rw [ha1] at h
    rw [h]; ring
  rw [h0_0 x, h0_1 x, ha0, hb0, ha1, hb1]
  ring

/-- 
Helper to evaluate an MvPolynomial on a partial assignment.
Using a sum type to avoid index mapping issues.
-/
def splitEval {n : ℕ} (P : MvPolynomial (Fin 2 ⊕ Fin n) ℂ) (z0 z1 : ℂ) (w : Fin n → ℂ) : ℂ :=
  let z : Fin 2 ⊕ Fin n → ℂ := fun i =>
    match i with
    | Sum.inl 0 => z0
    | Sum.inl 1 => z1
    | Sum.inr j => w j
  eval z P

/-- The 2-variable affine polynomial obtained by fixing the other n variables. -/
def toTwoVar {n : ℕ} (P : MvPolynomial (Fin 2 ⊕ Fin n) ℂ) (w : Fin n → ℂ) : TwoVarAffinePolynomial where
  A := splitEval P 0 0 w
  B := splitEval P 1 0 w - splitEval P 0 0 w
  C := splitEval P 0 1 w - splitEval P 0 0 w
  D := splitEval P 1 1 w - splitEval P 1 0 w - splitEval P 0 1 w + splitEval P 0 0 w

/--
Main Asano induction source claim.

This records the missing repeated-contraction theorem shape without claiming a
kernel-checked proof.  The multiaffine linearity step needed to prove this
claim is intentionally kept as explicit closure debt instead of hidden behind a
`sorry`.
-/
def AsanoInductiveStepSourceClaim : Prop :=
  ∀ {n : ℕ} (P : MvPolynomial (Fin 2 ⊕ Fin n) ℂ),
    (∀ m ∈ P.support, ∀ i, (m i : ℕ) ≤ 1) →
    ∀ (K : Fin 2 ⊕ Fin n → Set ℂ),
      (∀ i, 0 ∉ K i) →
      (∀ z : Fin 2 ⊕ Fin n → ℂ, (∀ i, z i ∉ K i) → eval z P ≠ 0) →
      AsanoRuelleLemmaSourceClaim →
      ∀ w : Fin n → ℂ, (∀ j : Fin n, w j ∉ K (Sum.inr j)) →
        ∀ z : ℂ, z ∉ asanoForbiddenSet (K (Sum.inl 0)) (K (Sum.inl 1)) →
          (toTwoVar P w).contract z ≠ 0


end AsanoInduction

end InfoGeometry.Canonical.LeeYangAsanoDigest
