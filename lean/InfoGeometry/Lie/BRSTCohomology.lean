/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Group.Int.Even

namespace InfoGeometry.Lie.BRSTCohomology

open CategoryTheory

/-! ## Noncommutative matrix BRST contraction

This finite model works over an arbitrary associative ring. Its carriers are
the actual matrix algebra `Mat₂(A)` and its even/odd subspaces, with products
retaining matrix order. The parity restrictions are exact, and the full matrix
operators define a two-periodic natural-number cochain complex exact in every
positive degree. These are algebraic results; they make no Hilbert-space or
geometric claim. -/

section MatrixQuartet

abbrev OperatorMat₂ (A : Type*) := Matrix (Fin 2) (Fin 2) A

/-- Elementary off-diagonal BRST operator matrices. -/
def brstE01 : OperatorMat₂ ℂ := !![0, 1; 0, 0]
def brstE10 : OperatorMat₂ ℂ := !![0, 0; 1, 0]

/-- Non-commutativity witness for the BRST operator matrix carrier. -/
theorem brstMatrix_noncommutative : brstE01 * brstE10 ≠ brstE10 * brstE01 := by
  intro h
  have h00 : (brstE01 * brstE10 : OperatorMat₂ ℂ) 0 0 = (brstE10 * brstE01 : OperatorMat₂ ℂ) 0 0 := by rw [h]
  simp [brstE01, brstE10, Matrix.mul_apply, Fin.sum_univ_two] at h00

section
variable {A : Type*} [Ring A] [Nontrivial A]

/-- Upper and lower elementary matrix units over a generic nontrivial ring. -/
def brstUpper : Matrix (Fin 2) (Fin 2) A := !![0, 1; 0, 0]
def brstLower : Matrix (Fin 2) (Fin 2) A := !![0, 0; 1, 0]

/-- Non-commutativity witness for the generic BRST matrix carrier. -/
theorem brstGenericNoncomm :
    (brstUpper : Matrix (Fin 2) (Fin 2) A) * brstLower ≠ brstLower * brstUpper := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0) h
  simp [brstUpper, brstLower, Matrix.mul_apply, Fin.sum_univ_two] at h00

end

def qOperator (A : Type*) [Ring A] : OperatorMat₂ A :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0
def rOperator (A : Type*) [Ring A] : OperatorMat₂ A :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

def IsEvenOperator (A : Type*) [Ring A] (X : OperatorMat₂ A) : Prop :=
  X 0 1 = 0 ∧ X 1 0 = 0
def IsOddOperator (A : Type*) [Ring A] (X : OperatorMat₂ A) : Prop :=
  X 0 0 = 0 ∧ X 1 1 = 0

/-- The additive groups underlying the even and odd matrix sectors. -/
def evenOperatorSubgroup (A : Type*) [Ring A] : AddSubgroup (OperatorMat₂ A) where
  carrier := {X | IsEvenOperator A X}
  zero_mem' := by simp [IsEvenOperator]
  add_mem' := by
    intro X Y hX hY
    rcases hX with ⟨hX₀₁, hX₁₀⟩
    rcases hY with ⟨hY₀₁, hY₁₀⟩
    constructor <;> simp [hX₀₁, hX₁₀, hY₀₁, hY₁₀]
  neg_mem' := by
    intro X hX
    rcases hX with ⟨hX₀₁, hX₁₀⟩
    constructor <;> simp [hX₀₁, hX₁₀]

def oddOperatorSubgroup (A : Type*) [Ring A] : AddSubgroup (OperatorMat₂ A) where
  carrier := {X | IsOddOperator A X}
  zero_mem' := by simp [IsOddOperator]
  add_mem' := by
    intro X Y hX hY
    rcases hX with ⟨hX₀₀, hX₁₁⟩
    rcases hY with ⟨hY₀₀, hY₁₁⟩
    constructor <;> simp [hX₀₀, hX₁₁, hY₀₀, hY₁₁]
  neg_mem' := by
    intro X hX
    rcases hX with ⟨hX₀₀, hX₁₁⟩
    constructor <;> simp [hX₀₀, hX₁₁]

abbrev EvenOperator (A : Type*) [Ring A] :=
  ↥(evenOperatorSubgroup A)
abbrev OddOperator (A : Type*) [Ring A] :=
  ↥(oddOperatorSubgroup A)

theorem qOperator_sq (A : Type*) [Ring A] :
    qOperator A * qOperator A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qOperator, Matrix.mul_apply]

theorem rOperator_sq (A : Type*) [Ring A] :
    rOperator A * rOperator A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rOperator, Matrix.mul_apply]

theorem qOperator_rOperator_CAR (A : Type*) [Ring A] :
    qOperator A * rOperator A + rOperator A * qOperator A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qOperator, rOperator, Matrix.mul_apply]

/-- The creation and annihilation operators genuinely fail to commute over
every nontrivial coefficient ring; their ordered products occupy different
diagonal matrix corners. -/
theorem qOperator_rOperator_ne_commute (A : Type*) [Ring A] [Nontrivial A] :
    qOperator A * rOperator A ≠ rOperator A * qOperator A := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [qOperator, rOperator, Matrix.mul_apply] at h00

/-- On the full operator matrix algebra, the even-to-odd BRST map is the
commutator action of the noncommuting generator `q`. -/
def fullEvenDifferential (A : Type*) [Ring A] :
    OperatorMat₂ A →ₗ[ℤ] OperatorMat₂ A :=
  LinearMap.mulLeft ℤ (qOperator A) - LinearMap.mulRight ℤ (qOperator A)

/-- On the full operator matrix algebra, the odd-to-even BRST map is the
anticommutator action of `q`. -/
def fullOddDifferential (A : Type*) [Ring A] :
    OperatorMat₂ A →ₗ[ℤ] OperatorMat₂ A :=
  LinearMap.mulLeft ℤ (qOperator A) + LinearMap.mulRight ℤ (qOperator A)

/-- The full-matrix differentials retain the ordered commutator and
anticommutator formulas. -/
@[simp] theorem fullEvenDifferential_apply (A : Type*) [Ring A]
    (X : OperatorMat₂ A) :
    fullEvenDifferential A X = qOperator A * X - X * qOperator A := rfl

@[simp] theorem fullOddDifferential_apply (A : Type*) [Ring A]
    (X : OperatorMat₂ A) :
    fullOddDifferential A X = qOperator A * X + X * qOperator A := rfl

/-- Alternating commutator and anticommutator maps compose to zero on the
entire noncommutative matrix algebra. -/
theorem fullOddDifferential_fullEvenDifferential_zero
    (A : Type*) [Ring A] (X : OperatorMat₂ A) :
    fullOddDifferential A (fullEvenDifferential A X) = 0 := by
  change qOperator A * (qOperator A * X - X * qOperator A) +
      (qOperator A * X - X * qOperator A) * qOperator A = 0
  simp only [mul_sub, sub_mul, Matrix.mul_assoc, qOperator_sq]
  simp
  rw [← Matrix.mul_assoc, qOperator_sq]
  simp

theorem fullEvenDifferential_fullOddDifferential_zero
    (A : Type*) [Ring A] (X : OperatorMat₂ A) :
    fullEvenDifferential A (fullOddDifferential A X) = 0 := by
  change qOperator A * (qOperator A * X + X * qOperator A) -
      (qOperator A * X + X * qOperator A) * qOperator A = 0
  simp only [mul_add, add_mul, Matrix.mul_assoc, qOperator_sq]
  simp
  rw [← Matrix.mul_assoc, qOperator_sq]
  simp

/-- The explicit contracting operator is left multiplication by the opposite
Witt generator `r`. -/
def fullBRSTContract (A : Type*) [Ring A] :
    OperatorMat₂ A →ₗ[ℤ] OperatorMat₂ A :=
  LinearMap.mulLeft ℤ (rOperator A)

/-- The even-to-odd differential and its contraction satisfy the contracting
homotopy identity on the full matrix algebra. -/
theorem fullBRST_homotopy_even (A : Type*) [Ring A]
    (X : OperatorMat₂ A) :
    fullOddDifferential A (fullBRSTContract A X) +
        fullBRSTContract A (fullEvenDifferential A X) = X := by
  change qOperator A * (rOperator A * X) +
      (rOperator A * X) * qOperator A +
      rOperator A * (qOperator A * X - X * qOperator A) = X
  calc
    _ = (qOperator A * rOperator A + rOperator A * qOperator A) * X := by
      noncomm_ring
    _ = X := by rw [qOperator_rOperator_CAR]; simp

/-- The odd-to-even differential and the same contraction satisfy the
contracting homotopy identity on the full matrix algebra. -/
theorem fullBRST_homotopy_odd (A : Type*) [Ring A]
    (X : OperatorMat₂ A) :
    fullEvenDifferential A (fullBRSTContract A X) +
        fullBRSTContract A (fullOddDifferential A X) = X := by
  change qOperator A * (rOperator A * X) -
      (rOperator A * X) * qOperator A +
      rOperator A * (qOperator A * X + X * qOperator A) = X
  calc
    _ = (qOperator A * rOperator A + rOperator A * qOperator A) * X := by
      noncomm_ring
    _ = X := by rw [qOperator_rOperator_CAR]; simp

/-- Every cycle of the full-matrix even differential is a boundary of the
full-matrix odd differential, with an explicit preimage. -/
theorem fullBRST_even_cycle_is_boundary (A : Type*) [Ring A]
    (X : OperatorMat₂ A) (hX : fullEvenDifferential A X = 0) :
    ∃ Y : OperatorMat₂ A, fullOddDifferential A Y = X := by
  refine ⟨fullBRSTContract A X, ?_⟩
  have h := fullBRST_homotopy_even A X
  rw [hX] at h
  simpa using h

/-- Every cycle of the full-matrix odd differential is a boundary of the
full-matrix even differential, with an explicit preimage. -/
theorem fullBRST_odd_cycle_is_boundary (A : Type*) [Ring A]
    (X : OperatorMat₂ A) (hX : fullOddDifferential A X = 0) :
    ∃ Y : OperatorMat₂ A, fullEvenDifferential A Y = X := by
  refine ⟨fullBRSTContract A X, ?_⟩
  have h := fullBRST_homotopy_odd A X
  rw [hX] at h
  simpa using h

/-- The natural-number-indexed differential alternates the commutator and
anticommutator actions on the full matrix algebra. -/
def fullBRSTDifferential (A : Type*) [Ring A] (n : ℕ) :
    OperatorMat₂ A →ₗ[ℤ] OperatorMat₂ A :=
  if n % 2 = 0 then fullEvenDifferential A else fullOddDifferential A

/-- Consecutive full-matrix BRST differentials compose to zero. -/
theorem fullBRSTDifferential_comp_zero (A : Type*) [Ring A] (n : ℕ) :
    (fullBRSTDifferential A (n + 1)).comp (fullBRSTDifferential A n) = 0 := by
  apply LinearMap.ext
  intro X
  by_cases h : n % 2 = 0
  · have hnext : (n + 1) % 2 ≠ 0 := by omega
    simpa [fullBRSTDifferential, h, hnext] using
      fullOddDifferential_fullEvenDifferential_zero A X
  · have hnext : (n + 1) % 2 = 0 := by omega
    simpa [fullBRSTDifferential, h, hnext] using
      fullEvenDifferential_fullOddDifferential_zero A X

/-- The alternating operator maps form a native Mathlib cochain complex on
the full noncommutative matrix algebra. -/
noncomputable def fullBRSTComplex (A : Type*) [Ring A] :
    CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun _ : ℕ => ModuleCat.of ℤ (OperatorMat₂ A))
    (fun n => ModuleCat.ofHom (fullBRSTDifferential A n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact fullBRSTDifferential_comp_zero A n)

/-- At every positive cochain degree, the boundaries of the alternating
full-matrix complex are exactly its cycles. -/
theorem fullBRST_exact_at_positive_degree (A : Type*) [Ring A]
    (n : ℕ) (hn : 0 < n) :
    LinearMap.range (fullBRSTDifferential A (n - 1)) =
      LinearMap.ker (fullBRSTDifferential A n) := by
  ext X
  constructor
  · rintro ⟨Y, hY⟩
    change fullBRSTDifferential A n X = 0
    rw [← hY]
    have hcomp := fullBRSTDifferential_comp_zero A (n - 1)
    have hidx : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    rw [hidx] at hcomp
    change ((fullBRSTDifferential A n).comp
      (fullBRSTDifferential A (n - 1))) Y = 0
    rw [hcomp]
    simp
  · intro hX
    change fullBRSTDifferential A n X = 0 at hX
    by_cases hparity : n % 2 = 0
    · have hprev : (n - 1) % 2 ≠ 0 := by omega
      have hboundary : ∃ Y : OperatorMat₂ A,
          fullOddDifferential A Y = X := by
        apply fullBRST_even_cycle_is_boundary
        simpa [fullBRSTDifferential, hparity] using hX
      rcases hboundary with ⟨Y, hY⟩
      refine ⟨Y, ?_⟩
      simpa [fullBRSTDifferential, hprev] using hY
    · have hprev : (n - 1) % 2 = 0 := by omega
      have hboundary : ∃ Y : OperatorMat₂ A,
          fullEvenDifferential A Y = X := by
        apply fullBRST_odd_cycle_is_boundary
        simpa [fullBRSTDifferential, hparity] using hX
      rcases hboundary with ⟨Y, hY⟩
      refine ⟨Y, ?_⟩
      simpa [fullBRSTDifferential, hprev] using hY

/-- The three consecutive terms of the alternating matrix complex around a
positive degree, represented by Mathlib's native module short complex. -/
noncomputable def fullBRSTDegreeShortComplex (A : Type*) [Ring A]
    (n : ℕ) (hn : 0 < n) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.moduleCatMk
    (fullBRSTDifferential A (n - 1))
    (fullBRSTDifferential A n)
    (by
      have hcomp := fullBRSTDifferential_comp_zero A (n - 1)
      have hindex : (n - 1) + 1 = n := Nat.sub_add_cancel hn
      rw [hindex] at hcomp
      exact hcomp)

/-- Every positive-degree three-term segment of the noncommutative matrix
complex is exact as a Mathlib `ShortComplex`, not merely exact in a parallel
quotient definition. -/
theorem fullBRSTDegreeShortComplex_exact (A : Type*) [Ring A]
    (n : ℕ) (hn : 0 < n) :
    (fullBRSTDegreeShortComplex A n hn).Exact := by
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
  exact fullBRST_exact_at_positive_degree A n hn

set_option linter.style.haveILetI false in
/-- The native Mathlib homology object of each positive-degree segment
vanishes. The result is algebraic module homology over `ℤ`; it makes no
Hilbert-space positivity claim. -/
theorem fullBRSTDegreeShortComplex_homology_isZero
    (A : Type*) [Ring A] (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (fullBRSTDegreeShortComplex A n hn).homology := by
  let S := fullBRSTDegreeShortComplex A n hn
  haveI : S.HasHomology := (fullBRSTDegreeShortComplex_exact A n hn).hasHomology
  exact (ShortComplex.exact_iff_isZero_homology S).mp
    (fullBRSTDegreeShortComplex_exact A n hn)

/-- The cycle module in degree `n` of the full-matrix alternating complex. -/
def fullBRSTCycles (A : Type*) [Ring A] (n : ℕ) :
    Submodule ℤ (OperatorMat₂ A) :=
  LinearMap.ker (fullBRSTDifferential A n)

/-- The degree-zero end of the natural-indexed BRST complex, with the zero
module of incoming boundaries. This is the actual endpoint short complex,
not a two-sided periodic extension that would erase its degree-zero classes. -/
noncomputable def fullBRSTZeroDegreeShortComplex (A : Type*) [Ring A] :
    ShortComplex (ModuleCat ℤ) :=
  ShortComplex.moduleCatMk
    (0 : (Fin 0 → A) →ₗ[ℤ] OperatorMat₂ A)
    (fullBRSTDifferential A 0)
    (by simp)

/-- The incoming map at degree zero has zero range, so the native homology
model is the kernel of the actual outgoing BRST differential. -/
theorem fullBRSTZeroDegree_incoming_range_eq_bot (A : Type*) [Ring A] :
    LinearMap.range
      (fullBRSTZeroDegreeShortComplex A).moduleCatToCycles = ⊥ := by
  have hzero :
      (fullBRSTZeroDegreeShortComplex A).moduleCatToCycles = 0 := by
    ext x
    rfl
  rw [hzero]
  exact LinearMap.range_zero

set_option linter.style.haveILetI false in
/-- Mathlib's native degree-zero homology object is linearly equivalent to
the kernel of the outgoing BRST differential. The quotient in its homology
construction is formed using the exact module instances carried by the
short-complex homology data; the incoming range is proved bottom above. -/
noncomputable def fullBRSTZeroDegree_nativeHomologyEquiv (A : Type*) [Ring A] :
    (fullBRSTZeroDegreeShortComplex A).homology ≃ₗ[ℤ]
      LinearMap.ker (fullBRSTDifferential A 0) := by
  let S := fullBRSTZeroDegreeShortComplex A
  haveI : S.HasHomology := by infer_instance
  letI : AddCommGroup (LinearMap.ker S.g.hom ⧸ S.moduleCatToCycles.range) :=
    S.moduleCatLeftHomologyData.H.isAddCommGroup
  letI : Module ℤ (LinearMap.ker S.g.hom ⧸ S.moduleCatToCycles.range) :=
    S.moduleCatLeftHomologyData.H.isModule
  letI : AddCommGroup (LinearMap.ker S.g.hom) :=
    S.moduleCatLeftHomologyData.K.isAddCommGroup
  letI : Module ℤ (LinearMap.ker S.g.hom) :=
    S.moduleCatLeftHomologyData.K.isModule
  have hrange : LinearMap.range S.moduleCatToCycles = ⊥ :=
    fullBRSTZeroDegree_incoming_range_eq_bot A
  let hquot := Submodule.quotEquivOfEqBot
    (p := S.moduleCatToCycles.range) hrange
  exact S.moduleCatHomologyIso.toLinearEquiv.trans hquot

/-- Boundaries entering a positive degree `n` are the range of the preceding
full-matrix differential. -/
def fullBRSTBoundaries (A : Type*) [Ring A] (n : ℕ) (_hn : 0 < n) :
    Submodule ℤ (OperatorMat₂ A) :=
  LinearMap.range (fullBRSTDifferential A (n - 1))

/-- Algebraic BRST cohomology in positive degree, as cycles modulo boundaries
inside the actual noncommutative matrix carrier. -/
def fullBRSTCohomology (A : Type*) [Ring A] (n : ℕ) (hn : 0 < n) :=
  fullBRSTCycles A n ⧸
    (fullBRSTBoundaries A n hn).comap (fullBRSTCycles A n).subtype

/-- Every positive-degree algebraic cohomology class of this full-matrix
complex vanishes. This is an exact quotient statement, not only a
cycle-implies-boundary witness. -/
theorem fullBRST_cohomology_subsingleton (A : Type*) [Ring A]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (fullBRSTCohomology A n hn) := by
  change Subsingleton
    ((fullBRSTCycles A n) ⧸
      (fullBRSTBoundaries A n hn).comap (fullBRSTCycles A n).subtype)
  rw [Submodule.Quotient.subsingleton_iff]
  apply le_antisymm
  · exact le_top
  · intro x hx
    change (x : OperatorMat₂ A) ∈
      LinearMap.range (fullBRSTDifferential A (n - 1))
    rw [fullBRST_exact_at_positive_degree A n hn]
    exact x.2

/-- The degree-zero differential of the natural-indexed complex is the
commutator with the nilpotent operator `q`; its cycles are exactly the
operator centralizer matrices `[[a,b],[0,a]]`. Thus the initial degree has a
real endpoint sector and must not be inferred from positive-degree exactness. -/
theorem fullBRST_zero_cycle_iff (A : Type*) [Ring A]
    (X : OperatorMat₂ A) :
    fullBRSTDifferential A 0 X = 0 ↔
      ∃ a b : A, X = !![a, b; 0, a] := by
  constructor
  · intro h
    change qOperator A * X - X * qOperator A = 0 at h
    have h10 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 0) 1
    simp [qOperator, Matrix.mul_apply] at h10 h11
    refine ⟨X 0 0, X 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact h10
    · have hdiag : X 1 1 = X 0 0 := sub_eq_zero.mp h11
      exact hdiag
  · rintro ⟨a, b, rfl⟩
    change qOperator A * !![a, b; 0, a] -
      !![a, b; 0, a] * qOperator A = 0
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qOperator, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum]

/-- Degree-zero BRST cycles form the associative centralizer subring of `q`
inside the full noncommutative operator matrix algebra. Multiplicative
closure follows from the ordered commutator derivation law. Since the complex
is indexed by `ℕ`, there is no incoming degree `-1` differential; this
centralizer is therefore the degree-zero cohomology algebra. -/
def fullBRSTZeroCentralizer (A : Type*) [Ring A] : Subring (OperatorMat₂ A) where
  carrier := {X | fullBRSTDifferential A 0 X = 0}
  zero_mem' := by simp [fullBRSTDifferential, fullEvenDifferential]
  one_mem' := by
    change qOperator A * 1 - 1 * qOperator A = 0
    simp
  add_mem' := by
    intro X Y hX hY
    change qOperator A * X - X * qOperator A = 0 at hX
    change qOperator A * Y - Y * qOperator A = 0 at hY
    change qOperator A * (X + Y) - (X + Y) * qOperator A = 0
    calc
      qOperator A * (X + Y) - (X + Y) * qOperator A =
          (qOperator A * X - X * qOperator A) +
            (qOperator A * Y - Y * qOperator A) := by noncomm_ring
      _ = 0 := by rw [hX, hY]; simp
  neg_mem' := by
    intro X hX
    change qOperator A * X - X * qOperator A = 0 at hX
    change qOperator A * (-X) - (-X) * qOperator A = 0
    calc
      qOperator A * (-X) - (-X) * qOperator A =
          -(qOperator A * X - X * qOperator A) := by noncomm_ring
      _ = 0 := by rw [hX]; simp
  mul_mem' := by
    intro X Y hX hY
    change qOperator A * X - X * qOperator A = 0 at hX
    change qOperator A * Y - Y * qOperator A = 0 at hY
    change qOperator A * (X * Y) - (X * Y) * qOperator A = 0
    calc
      qOperator A * (X * Y) - (X * Y) * qOperator A =
          (qOperator A * X - X * qOperator A) * Y +
            X * (qOperator A * Y - Y * qOperator A) := by noncomm_ring
      _ = 0 := by rw [hX, hY]; simp

/-- The centralizer subring has the explicit operator-matrix normal form
`[[a,b],[0,a]]` over the possibly noncommutative coefficient ring. -/
theorem fullBRSTZeroCentralizer_iff (A : Type*) [Ring A]
    (X : OperatorMat₂ A) :
    X ∈ fullBRSTZeroCentralizer A ↔ ∃ a b : A, X = !![a, b; 0, a] := by
  exact fullBRST_zero_cycle_iff A X

/-- The additive degree-zero cohomology, as the kernel of the outgoing
differential. Its inherited multiplication is represented by the subring
`fullBRSTZeroCentralizer`. -/
abbrev fullBRSTZeroCohomology (A : Type*) [Ring A] :=
  fullBRSTZeroCentralizer A

/-- Identify the actual degree-zero cycle module with its centralizer ring.
Both sides consist of the same operator matrices, and the codomain retains
the multiplication inherited from the full noncommutative matrix algebra. -/
def fullBRSTZeroCohomologyAddEquiv (A : Type*) [Ring A] :
    fullBRSTCycles A 0 ≃+ fullBRSTZeroCohomology A where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Mathlib's native degree-zero homology object is additively equivalent to
the explicit noncommutative centralizer. This composes the native homology
identification with the actual kernel-to-centralizer equivalence. -/
noncomputable def fullBRSTZeroDegree_nativeHomologyToCentralizer
    (A : Type*) [Ring A] :
    (fullBRSTZeroDegreeShortComplex A).homology ≃+
      fullBRSTZeroCohomology A := by
  simpa only [fullBRSTCycles] using
    (fullBRSTZeroDegree_nativeHomologyEquiv A).toAddEquiv.trans
      (fullBRSTZeroCohomologyAddEquiv A)

/-- The native degree-zero homology is nonzero whenever the coefficient ring
is nontrivial. Its nonzero class is the preimage of the identity in the
explicit centralizer, so it survives in Mathlib's homology object itself. -/
theorem fullBRSTZeroDegree_nativeHomology_nontrivial
    (A : Type*) [Ring A] [Nontrivial A] :
    ∃ x : (fullBRSTZeroDegreeShortComplex A).homology, x ≠ 0 := by
  let e := fullBRSTZeroDegree_nativeHomologyToCentralizer A
  let u : fullBRSTZeroCohomology A := 1
  have hu : u ≠ 0 := by
    intro hz
    have hmatrix : (1 : OperatorMat₂ A) = 0 := congrArg Subtype.val hz
    exact one_ne_zero hmatrix
  refine ⟨e.symm u, ?_⟩
  intro hx
  have h := congrArg e hx
  exact hu (by simpa using h)

/-- The degree-zero cohomology quotient: cycles modulo the range of the
incoming boundary map. Since the natural-indexed complex has no degree `-1`,
that range is zero, as certified by
`fullBRSTZeroDegree_incoming_range_eq_bot`. -/
abbrev fullBRSTZeroCohomologyQuotient (A : Type*) [Ring A] :=
  fullBRSTCycles A 0 ⧸ (⊥ : Submodule ℤ (fullBRSTCycles A 0))

/-- The degree-zero cohomology quotient is additively equivalent to the
centralizer ring of the BRST generator. This connects the quotient by the
actual zero incoming boundary to the explicit noncommutative endpoint. -/
noncomputable def fullBRSTZeroCohomologyQuotientAddEquiv
    (A : Type*) [Ring A] :
    fullBRSTZeroCohomologyQuotient A ≃+
      fullBRSTZeroCohomology A :=
  (Submodule.quotEquivOfEqBot
      (p := (⊥ : Submodule ℤ (fullBRSTCycles A 0))) rfl).toAddEquiv.trans
    (fullBRSTZeroCohomologyAddEquiv A)

/-- The identity operator is a degree-zero BRST cycle. -/
def fullBRSTIdentityCycle (A : Type*) [Ring A] : fullBRSTCycles A 0 :=
  ⟨1, by
    change qOperator A * (1 : OperatorMat₂ A) -
      (1 : OperatorMat₂ A) * qOperator A = 0
    simp⟩

/-- Over a nontrivial coefficient ring, the identity operator determines a
nonzero degree-zero cohomology class. Hence this endpoint cohomology does not
collapse to zero. -/
theorem fullBRSTIdentityClass_ne_zero (A : Type*) [Ring A] [Nontrivial A] :
    (Submodule.Quotient.mk (fullBRSTIdentityCycle A) :
      fullBRSTZeroCohomologyQuotient A) ≠ 0 := by
  intro h
  have hmem : fullBRSTIdentityCycle A ∈
      (⊥ : Submodule ℤ (fullBRSTCycles A 0)) := by
    exact (Submodule.Quotient.mk_eq_zero (p :=
      (⊥ : Submodule ℤ (fullBRSTCycles A 0)))).mp h
  have hcycle : fullBRSTIdentityCycle A = 0 := by
    simpa only [Submodule.mem_bot] using hmem
  have hmatrix : (1 : OperatorMat₂ A) = 0 := congrArg Subtype.val hcycle
  exact one_ne_zero hmatrix

/-- Multiplication in the degree-zero BRST centralizer, in its actual matrix
normal form. The upper-right coefficient is `a*d + b*c` in this order;
this formula remains valid when the coefficient ring is noncommutative. -/
theorem fullBRSTCentralizer_normalForm_mul (A : Type*) [Ring A]
    (a b c d : A) :
    (!![a, b; 0, a] : OperatorMat₂ A) * !![c, d; 0, c] =
      !![a * c, a * d + b * c; 0, a * c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The Lie bracket in the endpoint centralizer has diagonal coefficient
`a*c - c*a` and upper-right coefficient
`a*d + b*c - c*b - d*a`. This exposes both the coefficient-ring commutator
and the ordered bimodule action in degree-zero BRST cycles. -/
theorem fullBRSTCentralizer_normalForm_commutator (A : Type*) [Ring A]
    (a b c d : A) :
    ((!![a, b; 0, a] : OperatorMat₂ A) * !![c, d; 0, c]) -
        (!![c, d; 0, c] * !![a, b; 0, a]) =
      !![a * c - c * a, a * d + b * c - (c * b + d * a); 0,
        a * c - c * a] := by
  rw [fullBRSTCentralizer_normalForm_mul A, fullBRSTCentralizer_normalForm_mul A]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.of_apply]

/-- The upper-right corner operator that supplies the square-zero part of
the degree-zero BRST centralizer. -/
def fullBRSTOffDiagonal (A : Type*) [Ring A] (x : A) : OperatorMat₂ A :=
  !![0, x; 0, 0]

/-- Every upper-right corner operator is a degree-zero BRST cycle. -/
theorem fullBRSTOffDiagonal_mem_centralizer (A : Type*) [Ring A] (x : A) :
    fullBRSTOffDiagonal A x ∈ fullBRSTZeroCentralizer A := by
  exact (fullBRSTZeroCentralizer_iff A _).2 ⟨0, x, rfl⟩

/-- Products of any two off-diagonal endpoint operators vanish, so this
sector is square-zero even though its left and right coefficient actions may
differ. -/
theorem fullBRSTOffDiagonal_mul (A : Type*) [Ring A] (x y : A) :
    fullBRSTOffDiagonal A x * fullBRSTOffDiagonal A y = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fullBRSTOffDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- Left multiplication by a centralizer element acts on the square-zero
corner by the diagonal coefficient on the left, retaining coefficient order. -/
theorem fullBRSTCentralizer_mul_offDiagonal (A : Type*) [Ring A]
    (a b x : A) :
    (!![a, b; 0, a] : OperatorMat₂ A) * fullBRSTOffDiagonal A x =
      fullBRSTOffDiagonal A (a * x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fullBRSTOffDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- Right multiplication by a centralizer element acts on the square-zero
corner by the diagonal coefficient on the right. This differs from the left
action in a noncommutative coefficient ring. -/
theorem fullBRSTOffDiagonal_mul_centralizer (A : Type*) [Ring A]
    (x a b : A) :
    fullBRSTOffDiagonal A x * (!![a, b; 0, a] : OperatorMat₂ A) =
      fullBRSTOffDiagonal A (x * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fullBRSTOffDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- The adjoint action of the embedded coefficient algebra on the
square-zero BRST sector is the coefficient commutator, with order retained. -/
theorem fullBRSTCentralizerDiagonal_adjoint_offDiagonal (A : Type*) [Ring A]
    (a x : A) :
    (!![a, 0; 0, a] : OperatorMat₂ A) * fullBRSTOffDiagonal A x -
      fullBRSTOffDiagonal A x * (!![a, 0; 0, a] : OperatorMat₂ A) =
      fullBRSTOffDiagonal A (a * x - x * a) := by
  rw [fullBRSTCentralizer_mul_offDiagonal A a 0 x,
    fullBRSTOffDiagonal_mul_centralizer A x a 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fullBRSTOffDiagonal, Matrix.sub_apply]

/-- Whenever the coefficient commutator is nonzero, its induced adjoint
action on the square-zero BRST sector is nonzero as an operator matrix. -/
theorem fullBRSTCentralizerDiagonal_adjoint_nonzero {A : Type*} [Ring A]
    {a x : A} (hax : a * x ≠ x * a) :
    (!![a, 0; 0, a] : OperatorMat₂ A) * fullBRSTOffDiagonal A x -
      fullBRSTOffDiagonal A x * (!![a, 0; 0, a] : OperatorMat₂ A) ≠ 0 := by
  rw [fullBRSTCentralizerDiagonal_adjoint_offDiagonal]
  intro hzero
  have hentry := congrFun (congrFun hzero 0) 1
  change a * x - x * a = 0 at hentry
  exact hax (sub_eq_zero.mp hentry)

/-- The coefficient ring embeds into the degree-zero BRST centralizer by
the diagonal operator `a ↦ diag(a,a)`. -/
def fullBRSTCentralizerDiagonal (A : Type*) [Ring A] : A →+*
    fullBRSTZeroCentralizer A where
  toFun a := ⟨!![a, 0; 0, a],
    (fullBRSTZeroCentralizer_iff A !![a, 0; 0, a]).2 ⟨a, 0, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_zero' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The diagonal operator embedding is injective, so noncommuting coefficient
operators remain distinct in degree-zero BRST cohomology. -/
theorem fullBRSTCentralizerDiagonal_injective (A : Type*) [Ring A] :
    Function.Injective (fullBRSTCentralizerDiagonal A) := by
  intro a b hab
  have hentry := congrFun (congrFun (congrArg Subtype.val hab) 0) 0
  exact hentry

/-- A noncommuting coefficient pair gives a noncommuting pair of degree-zero
BRST cycles; the endpoint centralizer is therefore noncommutative whenever
the coefficient ring is. -/
theorem fullBRSTCentralizer_retains_noncommutativity (A : Type*) [Ring A]
    {a b : A} (hab : a * b ≠ b * a) :
    fullBRSTCentralizerDiagonal A a * fullBRSTCentralizerDiagonal A b ≠
      fullBRSTCentralizerDiagonal A b * fullBRSTCentralizerDiagonal A a := by
  intro h
  apply hab
  apply fullBRSTCentralizerDiagonal_injective A
  simpa only [map_mul] using h

/-- The degree-zero BRST cohomology algebra is commutative exactly when its
coefficient ring is commutative. The forward implication uses the embedded
diagonal copy of `A`; the reverse implication checks the actual ordered
normal-form multiplication of the centralizer matrices. -/
theorem fullBRSTZeroCohomology_commutative_iff (A : Type*) [Ring A] :
    (∀ x y : fullBRSTZeroCohomology A, x * y = y * x) ↔
      ∀ a b : A, a * b = b * a := by
  constructor
  · intro h a b
    have hdiag := h (fullBRSTCentralizerDiagonal A a)
      (fullBRSTCentralizerDiagonal A b)
    apply fullBRSTCentralizerDiagonal_injective A
    simpa only [map_mul] using hdiag
  · intro hComm x y
    obtain ⟨a, b, hx⟩ := (fullBRSTZeroCentralizer_iff A x.1).mp x.2
    obtain ⟨c, d, hy⟩ := (fullBRSTZeroCentralizer_iff A y.1).mp y.2
    apply Subtype.ext
    change x.1 * y.1 = y.1 * x.1
    rw [hx, hy, fullBRSTCentralizer_normalForm_mul A,
      fullBRSTCentralizer_normalForm_mul A]
    ext i j
    fin_cases i <;> fin_cases j
    · exact hComm a c
    · calc
        a * d + b * c = d * a + c * b := by rw [hComm a d, hComm b c]
        _ = c * b + d * a := by abel
    · rfl
    · exact hComm a c

/-- Parameterization of the degree-zero BRST centralizer by its diagonal
coefficient and upper-right operator coefficient. -/
noncomputable def fullBRSTEndpointEquiv (A : Type*) [Ring A] :
    (A × A) ≃ₗ[ℤ] fullBRSTCycles A 0 where
  toFun p := ⟨!![p.1, p.2; 0, p.1],
    (fullBRST_zero_cycle_iff A !![p.1, p.2; 0, p.1]).2 ⟨p.1, p.2, rfl⟩⟩
  invFun X := (X.1 0 0, X.1 0 1)
  left_inv p := by cases p; rfl
  right_inv X := by
    apply Subtype.ext
    rcases (fullBRST_zero_cycle_iff A X.1).1 X.2 with ⟨a, b, hX⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hX, Matrix.of_apply]
  map_add' p q := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply]
  map_smul' z p := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]

/-- The integer-indexed version has no endpoint: its differential alternates
by the parity of the integer degree. -/
def fullBRSTIntDifferential (A : Type*) [Ring A] (n : ℤ) :
    OperatorMat₂ A →ₗ[ℤ] OperatorMat₂ A :=
  if Even n then fullEvenDifferential A else fullOddDifferential A

/-- The integer-indexed alternating differentials compose to zero in every
degree, including negative degrees. -/
theorem fullBRSTIntDifferential_comp_zero (A : Type*) [Ring A] (n : ℤ) :
    (fullBRSTIntDifferential A (n + 1)).comp
      (fullBRSTIntDifferential A n) = 0 := by
  apply LinearMap.ext
  intro X
  by_cases h : Even n
  · have hnext : ¬ Even (n + 1) := by
      intro hn1
      exact ((Int.even_add_one (n := n)).mp hn1) h
    simpa [fullBRSTIntDifferential, h, hnext] using
      fullOddDifferential_fullEvenDifferential_zero A X
  · have hnext : Even (n + 1) := by
      exact (Int.even_add_one (n := n)).mpr h
    simpa [fullBRSTIntDifferential, h, hnext] using
      fullEvenDifferential_fullOddDifferential_zero A X

/-- A native integer-indexed, two-periodic cochain complex on the actual
noncommutative operator matrix algebra. -/
noncomputable def fullBRSTIntComplex (A : Type*) [Ring A] :
    CochainComplex (ModuleCat ℤ) ℤ :=
  CochainComplex.of (fun _ : ℤ => ModuleCat.of ℤ (OperatorMat₂ A))
    (fun n => ModuleCat.ofHom (fullBRSTIntDifferential A n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact fullBRSTIntDifferential_comp_zero A n)

/-- The integer-indexed alternating complex is exact at every degree: the
image of the preceding differential is the kernel of the current one. -/
theorem fullBRSTInt_exact_at_every_degree (A : Type*) [Ring A] (n : ℤ) :
    LinearMap.range (fullBRSTIntDifferential A (n - 1)) =
      LinearMap.ker (fullBRSTIntDifferential A n) := by
  ext X
  constructor
  · rintro ⟨Y, hY⟩
    change fullBRSTIntDifferential A n X = 0
    rw [← hY]
    have hcomp := fullBRSTIntDifferential_comp_zero A (n - 1)
    have hidx : (n - 1) + 1 = n := by ring
    rw [hidx] at hcomp
    change ((fullBRSTIntDifferential A n).comp
      (fullBRSTIntDifferential A (n - 1))) Y = 0
    rw [hcomp]
    simp
  · intro hX
    change fullBRSTIntDifferential A n X = 0 at hX
    by_cases hparity : Even n
    · have hprev : ¬ Even (n - 1) := by
        have hEq : (n - 1) + 1 = n := by ring
        have hrel := Int.even_add_one (n := n - 1)
        rw [hEq] at hrel
        exact hrel.mp hparity
      have hboundary : ∃ Y : OperatorMat₂ A,
          fullOddDifferential A Y = X := by
        apply fullBRST_even_cycle_is_boundary
        simpa [fullBRSTIntDifferential, hparity] using hX
      rcases hboundary with ⟨Y, hY⟩
      refine ⟨Y, ?_⟩
      simpa [fullBRSTIntDifferential, hprev] using hY
    · have hprev : Even (n - 1) := by
        by_contra hprev
        have hEq : (n - 1) + 1 = n := by ring
        have hrel := Int.even_add_one (n := n - 1)
        rw [hEq] at hrel
        have hn : Even n := by
          exact hrel.mpr hprev
        exact hparity hn
      have hboundary : ∃ Y : OperatorMat₂ A,
          fullEvenDifferential A Y = X := by
        apply fullBRST_odd_cycle_is_boundary
        simpa [fullBRSTIntDifferential, hparity] using hX
      rcases hboundary with ⟨Y, hY⟩
      refine ⟨Y, ?_⟩
      simpa [fullBRSTIntDifferential, hprev] using hY

/-- Algebraic cohomology of the integer-indexed complex at degree `n`, defined
as cycles modulo boundaries in `Mat₂(A)`. -/
def fullBRSTIntCohomology (A : Type*) [Ring A] (n : ℤ) :=
  (LinearMap.ker (fullBRSTIntDifferential A n)) ⧸
    (LinearMap.range (fullBRSTIntDifferential A (n - 1))).comap
      (LinearMap.ker (fullBRSTIntDifferential A n)).subtype

/-- Every cohomology class of the bi-infinite alternating matrix complex is
zero. This is algebraic cohomology over `ℤ`, with no inner-product claim. -/
theorem fullBRSTInt_cohomology_subsingleton (A : Type*) [Ring A] (n : ℤ) :
    Subsingleton (fullBRSTIntCohomology A n) := by
  change Subsingleton
    ((LinearMap.ker (fullBRSTIntDifferential A n)) ⧸
      (LinearMap.range (fullBRSTIntDifferential A (n - 1))).comap
        (LinearMap.ker (fullBRSTIntDifferential A n)).subtype)
  rw [Submodule.Quotient.subsingleton_iff]
  apply le_antisymm
  · exact le_top
  · intro x hx
    change (x : OperatorMat₂ A) ∈
      LinearMap.range (fullBRSTIntDifferential A (n - 1))
    rw [fullBRSTInt_exact_at_every_degree A n]
    exact x.2

/-- Differential from even to odd matrices: `qX - Xq`. -/
def evenDifferential (A : Type*) [Ring A] (X : EvenOperator A) : OddOperator A :=
  ⟨qOperator A * X.1 - X.1 * qOperator A, by
    rcases X.2 with ⟨h01, h10⟩
    constructor <;> simp [qOperator, Matrix.mul_apply, h10]⟩

/-- Differential from odd to even matrices: `qX + Xq`. -/
def oddDifferential (A : Type*) [Ring A] (X : OddOperator A) : EvenOperator A :=
  ⟨qOperator A * X.1 + X.1 * qOperator A, by
    rcases X.2 with ⟨h00, h11⟩
    constructor <;> simp [qOperator, Matrix.mul_apply, h00, h11]⟩

/-- The even diagonal matrix unit in the second Witt corner, represented in
the operator algebra by the ordered product `r*q`. -/
def evenVacuumProjector (A : Type*) [Ring A] : EvenOperator A :=
  ⟨rOperator A * qOperator A, by
    constructor <;> simp [rOperator, qOperator, Matrix.mul_apply]⟩

/-- The BRST differential is nonzero: on the second even matrix unit it
produces the off-diagonal Witt generator `q`. -/
theorem evenDifferential_vacuumProjector (A : Type*) [Ring A] :
    (evenDifferential A (evenVacuumProjector A)).1 = qOperator A := by
  change qOperator A * (rOperator A * qOperator A) -
      (rOperator A * qOperator A) * qOperator A = qOperator A
  have hqr : qOperator A * rOperator A = 1 - rOperator A * qOperator A := by
    calc
      qOperator A * rOperator A =
          (qOperator A * rOperator A + rOperator A * qOperator A) -
            rOperator A * qOperator A := by abel
      _ = 1 - rOperator A * qOperator A := by rw [qOperator_rOperator_CAR]
  calc
    qOperator A * (rOperator A * qOperator A) -
        (rOperator A * qOperator A) * qOperator A
      = (qOperator A * rOperator A) * qOperator A -
          rOperator A * (qOperator A * qOperator A) := by simp only [mul_assoc]
    _ = (1 - rOperator A * qOperator A) * qOperator A - rOperator A * 0 := by
          rw [hqr, qOperator_sq]
    _ = qOperator A := by simp [sub_mul, mul_assoc, qOperator_sq]

/-- Over a nontrivial coefficient ring, this exact complex has a genuinely
nonzero differential value on its vacuum projector. -/
theorem evenDifferential_nonzero_value (A : Type*) [Ring A] [Nontrivial A] :
    (evenDifferential A (evenVacuumProjector A)).1 ≠ 0 := by
  rw [evenDifferential_vacuumProjector]
  intro hq
  have h01 := congrFun (congrFun hq 0) 1
  simp [qOperator] at h01

/-- Left multiplication by the opposite Witt operator maps even to odd. -/
def evenContract (A : Type*) [Ring A] (X : EvenOperator A) : OddOperator A :=
  ⟨rOperator A * X.1, by
    rcases X.2 with ⟨h01, h10⟩
    constructor <;> simp [rOperator, Matrix.mul_apply, h01]⟩

/-- Left multiplication by the opposite Witt operator maps odd to even. -/
def oddContract (A : Type*) [Ring A] (X : OddOperator A) : EvenOperator A :=
  ⟨rOperator A * X.1, by
    rcases X.2 with ⟨h00, h11⟩
    constructor <;> simp [rOperator, Matrix.mul_apply, h00]⟩

theorem oddDifferential_evenDifferential_zero (A : Type*) [Ring A]
    (X : EvenOperator A) :
    (oddDifferential A (evenDifferential A X)).1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenDifferential, oddDifferential, qOperator, Matrix.mul_apply,
      Fin.sum_univ_two, X.2.2]

theorem evenDifferential_oddDifferential_zero (A : Type*) [Ring A]
    (X : OddOperator A) :
    (evenDifferential A (oddDifferential A X)).1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenDifferential, oddDifferential, qOperator, Matrix.mul_apply,
      Fin.sum_univ_two, X.2.1, X.2.2]

/-- On the even sector, `d h + h d` is the identity matrix operator. -/
theorem quartet_homotopy_even (A : Type*) [Ring A] (X : EvenOperator A) :
    (oddDifferential A (evenContract A X)).1 +
        (oddContract A (evenDifferential A X)).1 = X.1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenDifferential, oddDifferential, evenContract, oddContract,
      qOperator, rOperator, Matrix.mul_apply, Fin.sum_univ_two, X.2.1, X.2.2]

/-- On the odd sector, `d h + h d` is the identity matrix operator. -/
theorem quartet_homotopy_odd (A : Type*) [Ring A] (X : OddOperator A) :
    (evenDifferential A (oddContract A X)).1 +
        (evenContract A (oddDifferential A X)).1 = X.1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenDifferential, oddDifferential, evenContract, oddContract,
      qOperator, rOperator, Matrix.mul_apply, Fin.sum_univ_two, X.2.1, X.2.2]

/-- Every even cycle is an odd boundary, with an explicit preimage from the
matrix contracting homotopy. -/
theorem even_cycle_is_boundary (A : Type*) [Ring A] (X : EvenOperator A)
    (hX : (evenDifferential A X).1 = 0) :
    ∃ Y : OddOperator A, (oddDifferential A Y).1 = X.1 := by
  refine ⟨evenContract A X, ?_⟩
  have hcontract : (oddContract A (evenDifferential A X)).1 = 0 := by
    change rOperator A * (evenDifferential A X).1 = 0
    rw [hX]
    simp
  have h := quartet_homotopy_even A X
  rw [hcontract] at h
  simpa using h

/-- Every odd cycle is an even boundary, with an explicit preimage from the
matrix contracting homotopy. -/
theorem odd_cycle_is_boundary (A : Type*) [Ring A] (X : OddOperator A)
    (hX : (oddDifferential A X).1 = 0) :
    ∃ Y : EvenOperator A, (evenDifferential A Y).1 = X.1 := by
  refine ⟨oddContract A X, ?_⟩
  have hcontract : (evenContract A (oddDifferential A X)).1 = 0 := by
    change rOperator A * (oddDifferential A X).1 = 0
    rw [hX]
    simp
  have h := quartet_homotopy_odd A X
  rw [hcontract] at h
  simpa using h

/-- The even and odd differentials as additive homomorphisms on the actual
matrix sectors. -/
def evenDifferentialHom (A : Type*) [Ring A] :
    EvenOperator A →+ OddOperator A where
  toFun := evenDifferential A
  map_zero' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [evenDifferential]
  map_add' X Y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [evenDifferential, qOperator, Matrix.mul_apply,
        Matrix.mul_add, Matrix.add_mul] <;> abel

def oddDifferentialHom (A : Type*) [Ring A] :
    OddOperator A →+ EvenOperator A where
  toFun := oddDifferential A
  map_zero' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [oddDifferential]
  map_add' X Y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [oddDifferential, qOperator, Matrix.mul_apply,
        Matrix.mul_add, Matrix.add_mul] ; abel

/-- Exactness as an equality of additive subgroups of the even matrix sector:
cycles of the matrix differential are precisely images from the odd sector. -/
theorem even_differential_exact (A : Type*) [Ring A] :
    AddMonoidHom.range (oddDifferentialHom A) =
      AddMonoidHom.ker (evenDifferentialHom A) := by
  ext X
  constructor
  · rintro ⟨Y, hY⟩
    rw [← hY]
    apply Subtype.ext
    exact evenDifferential_oddDifferential_zero A Y
  · intro hX
    have hcycle : (evenDifferential A X).1 = 0 := by
      exact congrArg Subtype.val hX
    obtain ⟨Y, hY⟩ := even_cycle_is_boundary A X hcycle
    exact ⟨Y, Subtype.ext hY⟩

/-- Exactness on the odd sector: every odd cycle is an even boundary. -/
theorem odd_differential_exact (A : Type*) [Ring A] :
    AddMonoidHom.range (evenDifferentialHom A) =
      AddMonoidHom.ker (oddDifferentialHom A) := by
  ext X
  constructor
  · rintro ⟨Y, hY⟩
    rw [← hY]
    apply Subtype.ext
    exact oddDifferential_evenDifferential_zero A Y
  · intro hX
    have hcycle : (oddDifferential A X).1 = 0 := by
      exact congrArg Subtype.val hX
    obtain ⟨Y, hY⟩ := odd_cycle_is_boundary A X hcycle
    exact ⟨Y, Subtype.ext hY⟩

/-- The even cycles, as a subgroup of the even matrix sector. -/
def evenCycles (A : Type*) [Ring A] : AddSubgroup (EvenOperator A) :=
  AddMonoidHom.ker (evenDifferentialHom A)

/-- Boundaries viewed inside the even cycle subgroup. -/
def evenBoundaries (A : Type*) [Ring A] : AddSubgroup (evenCycles A) :=
  (AddMonoidHom.range (oddDifferentialHom A)).comap (evenCycles A).subtype

/-- The algebraic even cohomology is the actual quotient of cycles by boundaries. -/
abbrev EvenCohomology (A : Type*) [Ring A] :=
  evenCycles A ⧸ evenBoundaries A

/-- The explicit contracting homotopy makes every even cycle a boundary, so this
finite matrix complex has zero even cohomology. -/
theorem evenBoundaries_eq_top (A : Type*) [Ring A] :
    evenBoundaries A = ⊤ := by
  ext X
  constructor
  · intro _
    simp
  · intro _
    change (X.1 : EvenOperator A) ∈ AddMonoidHom.range (oddDifferentialHom A)
    have hker : X.1 ∈ AddMonoidHom.ker (evenDifferentialHom A) := X.2
    rw [← even_differential_exact A] at hker
    exact hker

theorem evenCohomology_subsingleton (A : Type*) [Ring A] :
    Subsingleton (EvenCohomology A) := by
  unfold EvenCohomology
  apply Subsingleton.intro
  intro x y
  have hx : x = 0 := by
    obtain ⟨X, rfl⟩ := QuotientAddGroup.mk'_surjective (evenBoundaries A) x
    apply (QuotientAddGroup.eq_zero_iff _).2
    rw [evenBoundaries_eq_top]
    simp
  have hy : y = 0 := by
    obtain ⟨Y, rfl⟩ := QuotientAddGroup.mk'_surjective (evenBoundaries A) y
    apply (QuotientAddGroup.eq_zero_iff _).2
    rw [evenBoundaries_eq_top]
    simp
  rw [hx, hy]

/-- The odd cycles, as a subgroup of the odd matrix sector. -/
def oddCycles (A : Type*) [Ring A] : AddSubgroup (OddOperator A) :=
  AddMonoidHom.ker (oddDifferentialHom A)

/-- Boundaries viewed inside the odd cycle subgroup. -/
def oddBoundaries (A : Type*) [Ring A] : AddSubgroup (oddCycles A) :=
  (AddMonoidHom.range (evenDifferentialHom A)).comap (oddCycles A).subtype

/-- The algebraic odd cohomology is the actual quotient of odd cycles by boundaries. -/
abbrev OddCohomology (A : Type*) [Ring A] :=
  oddCycles A ⧸ oddBoundaries A

theorem oddBoundaries_eq_top (A : Type*) [Ring A] :
    oddBoundaries A = ⊤ := by
  ext X
  constructor
  · intro _
    simp
  · intro _
    change (X.1 : OddOperator A) ∈ AddMonoidHom.range (evenDifferentialHom A)
    have hker : X.1 ∈ AddMonoidHom.ker (oddDifferentialHom A) := X.2
    rw [← odd_differential_exact A] at hker
    exact hker

theorem oddCohomology_subsingleton (A : Type*) [Ring A] :
    Subsingleton (OddCohomology A) := by
  unfold OddCohomology
  apply Subsingleton.intro
  intro x y
  have hx : x = 0 := by
    obtain ⟨X, rfl⟩ := QuotientAddGroup.mk'_surjective (oddBoundaries A) x
    apply (QuotientAddGroup.eq_zero_iff _).2
    rw [oddBoundaries_eq_top]
    simp
  have hy : y = 0 := by
    obtain ⟨Y, rfl⟩ := QuotientAddGroup.mk'_surjective (oddBoundaries A) y
    apply (QuotientAddGroup.eq_zero_iff _).2
    rw [oddBoundaries_eq_top]
    simp
  rw [hx, hy]



end MatrixQuartet

end InfoGeometry.Lie.BRSTCohomology
