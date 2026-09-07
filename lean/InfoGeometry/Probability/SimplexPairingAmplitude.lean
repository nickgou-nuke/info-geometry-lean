import Mathlib.Analysis.Convex.StdSimplex
import InfoGeometry.Probability.FisherRaoMadelungIsometry
import InfoGeometry.Krein.FiniteCovarianceMajoranaBlock

/-!
# Independent pairing and nonnegative probability amplitudes

The carrier is Mathlib's finite standard simplex, including its boundary.
Products below construct independent joint distributions; no independence of
arbitrary events is asserted. The amplitude map is an equivalence onto the
nonnegative part of the unit sphere, not a choice of complex phase or dynamics.
The established Madelung and covariance-projection owners are reused.
-/

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Probability.SimplexPairingAmplitude

open InfoGeometry.Probability.FisherRaoMadelungIsometry
open InfoGeometry.Krein.FiniteCovarianceMajoranaBlock

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Squaring and taking nonnegative square roots are inverse, including zero
probabilities. The normalization is part of the native simplex carrier. -/
def amplitudeEquiv : stdSimplex ℝ ι ≃
    {a : ι → ℝ // (∀ i, 0 ≤ a i) ∧ ∑ i, (a i) ^ 2 = 1} where
  toFun P := ⟨fun i => Real.sqrt (P.val i),
    fun i => Real.sqrt_nonneg _,
    madelung_amplitude_norm_sq P.val P.property.1 P.property.2⟩
  invFun a := ⟨fun i => (a.val i) ^ 2,
    fun i => sq_nonneg _, a.property.2⟩
  left_inv P := by
    apply Subtype.ext
    funext i
    exact Real.sq_sqrt (P.property.1 i)
  right_inv a := by
    apply Subtype.ext
    funext i
    exact Real.sqrt_sq (a.property.1 i)

/-- An independent joint distribution is an actual simplex point. -/
theorem product_mem_stdSimplex (P : stdSimplex ℝ ι) (Q : stdSimplex ℝ κ) :
    (fun z : ι × κ => P.val z.1 * Q.val z.2) ∈ stdSimplex ℝ (ι × κ) := by
  constructor
  · intro z
    exact mul_nonneg (P.property.1 _) (Q.property.1 _)
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, Q.property.2, mul_one]
    exact P.property.2

/-- Marginalizing the independent joint law recovers its first factor. -/
theorem product_first_marginal (P : stdSimplex ℝ ι) (Q : stdSimplex ℝ κ) (i : ι) :
    ∑ j, P.val i * Q.val j = P.val i := by
  rw [← Finset.mul_sum, Q.property.2, mul_one]

/-- A joint product law has factorized nonnegative amplitudes. -/
theorem product_amplitude (P : stdSimplex ℝ ι) (Q : stdSimplex ℝ κ) (i : ι) (j : κ) :
    Real.sqrt (P.val i * Q.val j) =
      (amplitudeEquiv P).val i * (amplitudeEquiv Q).val j := by
  exact Real.sqrt_mul (P.property.1 i) _

/-- The amplitude inner product of independent laws multiplies. This is a
finite sum identity, with no Hilbert-space dynamics added. -/
theorem product_amplitude_overlap
    (P R : stdSimplex ℝ ι) (Q S : stdSimplex ℝ κ) :
    (∑ z : ι × κ, Real.sqrt (P.val z.1 * Q.val z.2) *
        Real.sqrt (R.val z.1 * S.val z.2)) =
      (∑ i, Real.sqrt (P.val i) * Real.sqrt (R.val i)) *
      (∑ j, Real.sqrt (Q.val j) * Real.sqrt (S.val j)) := by
  simp_rw [Real.sqrt_mul (P.property.1 _), Real.sqrt_mul (R.property.1 _)]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The binary law is a concrete inhabitant of Mathlib's standard simplex. -/
def binary (p : Set.Icc (0 : ℝ) 1) : stdSimplex ℝ (Fin 2) :=
  ⟨![p.val, 1 - p.val], by
    constructor
    · intro i
      fin_cases i
      · exact p.property.1
      · exact sub_nonneg.mpr p.property.2
    · simp⟩

/-- For two independent copies, the two disjoint mismatch outcomes have twice
the probability of the ordered success/failure outcome. These are not the
intersection of an event with its own complement. -/
theorem binary_mismatch_probability (p : Set.Icc (0 : ℝ) 1) :
    (binary p).val 0 * (binary p).val 1 +
      (binary p).val 1 * (binary p).val 0 = 2 * p.val * (1 - p.val) := by
  simp [binary]
  ring

/-- The amplitude lift gives exactly the repository's existing rank-one
covariance projection; this identifies the two concrete constructions. -/
theorem binary_amplitude_outer_product (p : Set.Icc (0 : ℝ) 1) :
    (fun i j : Fin 2 => (amplitudeEquiv (binary p)).val i *
      (amplitudeEquiv (binary p)).val j) = covarianceProjection p.val := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [amplitudeEquiv, binary, covarianceProjection,
    Real.mul_self_sqrt p.property.1,
    Real.mul_self_sqrt (sub_nonneg.mpr p.property.2), mul_comm]

end InfoGeometry.Probability.SimplexPairingAmplitude
