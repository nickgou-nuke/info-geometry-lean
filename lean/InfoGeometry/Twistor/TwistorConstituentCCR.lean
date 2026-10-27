import InfoGeometry.Twistor.PenrosePolynomialCCR
import Mathlib.RingTheory.Derivation.Lie

/-!
# Constituent CCR and quadratic generators on actual polynomials

The polynomial carrier is not a finite matrix approximation. The commutators
are derived from native `MvPolynomial.pderiv`. In particular this constructs
the commuting translation block and its two chiral linear actions; no
Hilbert adjoints or physical spin spectrum are postulated.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwistorConstituentCCR

open scoped BigOperators
variable {σ : Type*} [DecidableEq σ]

abbrev Wave (σ : Type*) := MvPolynomial σ ℂ
abbrev Operator (σ : Type*) := Module.End ℂ (Wave σ)

/-- Coordinate multiplication. -/
def coordinate (i : σ) : Operator σ where
  toFun p := MvPolynomial.X i * p
  map_add' p q := mul_add _ _ _
  map_smul' c p := by simp [Algebra.mul_smul_comm]

/-- Native polynomial partial derivative, viewed as an endomorphism. -/
def partialOp (i : σ) : Operator σ := (MvPolynomial.pderiv i).toLinearMap

def conjugateCoordinate (h : ℂ) (i : σ) : Operator σ := -h • partialOp i

omit [DecidableEq σ] in
@[simp] theorem coordinate_apply (i : σ) (p : Wave σ) :
    coordinate i p = MvPolynomial.X i * p := rfl

omit [DecidableEq σ] in
@[simp] theorem partialOp_apply (i : σ) (p : Wave σ) :
    partialOp i p = MvPolynomial.pderiv i p := rfl

theorem partials_commute (i j : σ) (p : Wave σ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  have hd : (⁅MvPolynomial.pderiv (R := ℂ) i, MvPolynomial.pderiv (R := ℂ) j⁆ :
      Derivation ℂ (Wave σ) (Wave σ)) = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp [Derivation.commutator_apply, Pi.single_apply, hi, hj]
  have h := Derivation.congr_fun hd p
  exact sub_eq_zero.mp (by simpa [Derivation.commutator_apply] using h)

/-- Equation (6.13), for any variable set, including Fin n × Fin 4. -/
theorem coordinate_CCR (h : ℂ) (i j : σ) :
    coordinate i * conjugateCoordinate h j - conjugateCoordinate h j * coordinate i =
      (if i = j then h else 0) • (1 : Operator σ) := by
  apply LinearMap.ext
  intro p
  by_cases hij : i = j
  · subst j
    simp [conjugateCoordinate, Module.End.mul_apply, Algebra.smul_def]
    ring
  · simp [conjugateCoordinate, Module.End.mul_apply, MvPolynomial.pderiv_X, hij, Algebra.smul_def]
    ring

omit [DecidableEq σ] in
theorem coordinate_ZZ (i j : σ) : coordinate i * coordinate j = coordinate j * coordinate i := by
  apply LinearMap.ext
  intro p
  simp [Module.End.mul_apply]
  ring

theorem coordinate_WW (h : ℂ) (i j : σ) :
    conjugateCoordinate h i * conjugateCoordinate h j =
      conjugateCoordinate h j * conjugateCoordinate h i := by
  apply LinearMap.ext
  intro p
  simp [conjugateCoordinate, Module.End.mul_apply, partials_commute]

/-- Compatibility with the pre-existing four-variable realization. -/
theorem coordinate_eq_existing (i : Fin 4) :
    coordinate i = InfoGeometry.Twistor.PenrosePolynomialCCR.Z i := by
  apply LinearMap.ext
  intro p
  exact (InfoGeometry.Twistor.PenrosePolynomialCCR.Z_apply i p).symm

theorem conjugateCoordinate_eq_existing (h : ℂ) (i : Fin 4) :
    conjugateCoordinate h i = InfoGeometry.Twistor.PenrosePolynomialCCR.W h i := by
  apply LinearMap.ext
  intro p
  simpa [conjugateCoordinate] using
    (InfoGeometry.Twistor.PenrosePolynomialCCR.W_apply h i p).symm

/-- Quadratic generators X_a partial_b, with the standard gl commutator sign. -/
def quadratic (a b : σ) : Operator σ := coordinate a * partialOp b

omit [DecidableEq σ] in
@[simp] theorem quadratic_apply (a b : σ) (p : Wave σ) :
    quadratic a b p = MvPolynomial.X a * MvPolynomial.pderiv b p := rfl

theorem quadratic_commutator (a b c d : σ) :
    quadratic a b * quadratic c d - quadratic c d * quadratic a b =
      (if b = c then quadratic a d else 0) -
      (if d = a then quadratic c b else 0) := by
  apply LinearMap.ext
  intro p
  simp only [Module.End.mul_apply, LinearMap.sub_apply, quadratic_apply,
    MvPolynomial.pderiv_mul]
  rw [partials_commute b d p]
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp [MvPolynomial.pderiv_X, hbc, hda] <;> ring

private theorem commutator_sum {ι κ A : Type*} [Fintype ι] [Fintype κ] [Ring A]
    (x : ι → A) (y : κ → A) :
    (∑ i, x i) * (∑ j, y j) - (∑ j, y j) * (∑ i, x i) =
      ∑ i, ∑ j, (x i * y j - y j * x i) := by
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

/-- Sum of the same quadratic generator over n actual constituents. -/
def collective (n : ℕ) (a b : σ) : Operator (Fin n × σ) :=
  ∑ i : Fin n, quadratic (i, a) (i, b)

theorem collective_commutator (n : ℕ) (a b c d : σ) :
    collective n a b * collective n c d - collective n c d * collective n a b =
      (if b = c then collective n a d else 0) -
      (if d = a then collective n c b else 0) := by
  unfold collective
  rw [commutator_sum]
  simp_rw [quadratic_commutator]
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp [Prod.mk.injEq, hbc, hda, Finset.sum_sub_distrib]

abbrev ChiralSlot := Fin 2 ⊕ Fin 2

def translation (n : ℕ) (a b : Fin 2) : Operator (Fin n × ChiralSlot) :=
  collective n (.inl a) (.inr b)

def leftGenerator (n : ℕ) (a b : Fin 2) : Operator (Fin n × ChiralSlot) :=
  collective n (.inl a) (.inl b)

def rightGenerator (n : ℕ) (a b : Fin 2) : Operator (Fin n × ChiralSlot) :=
  collective n (.inr a) (.inr b)

/-- Translations form an abelian ideal in this concrete chiral realization. -/
theorem translations_commute (n : ℕ) (a b c d : Fin 2) :
    translation n a b * translation n c d = translation n c d * translation n a b := by
  apply sub_eq_zero.mp
  simpa [translation] using collective_commutator (σ := ChiralSlot) n (.inl a) (.inr b) (.inl c) (.inr d)

theorem left_translation_commutator (n : ℕ) (a b c d : Fin 2) :
    leftGenerator n a b * translation n c d - translation n c d * leftGenerator n a b =
      if b = c then translation n a d else 0 := by
  simpa [leftGenerator, translation] using
    collective_commutator (σ := ChiralSlot) n (.inl a) (.inl b) (.inl c) (.inr d)

theorem right_translation_commutator (n : ℕ) (a b c d : Fin 2) :
    rightGenerator n a b * translation n c d - translation n c d * rightGenerator n a b =
      -(if d = a then translation n c b else 0) := by
  simpa [rightGenerator, translation] using
    collective_commutator (σ := ChiralSlot) n (.inr a) (.inr b) (.inl c) (.inr d)

theorem chiral_generators_commute (n : ℕ) (a b c d : Fin 2) :
    leftGenerator n a b * rightGenerator n c d = rightGenerator n c d * leftGenerator n a b := by
  apply sub_eq_zero.mp
  simpa [leftGenerator, rightGenerator] using
    collective_commutator (σ := ChiralSlot) n (.inl a) (.inl b) (.inr c) (.inr d)

end InfoGeometry.Twistor.TwistorConstituentCCR
