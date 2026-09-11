import Mathlib.Algebra.BigOperators.Field
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Cartan exponential family

Purely algebraic finite exponential-family chart on a finite Cartan index set.

This layer is separate from the determinant-volume cocycle layer:

* `Z` and `Phi` encode the statistical partition/potential;
* `prob`, `expect`, and `fisherCov` encode the induced finite Fisher geometry;
* the determinant cocycle lives elsewhere (`InfoGeometry.Cocycle.MatrixDetExpTrace`).

The main point is that the statistical partition function is `Tr(exp(θ·H))`
in a Cartan chart, not `det(exp(θ·H))`.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CartanExponentialFamily

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι]

/-- The Cartan partition function `Z(θ) = ∑ᵢ exp(θᵢ)`. -/
noncomputable def Z (θ : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (θ i)

/-- The Cartan Massieu/entropy potential `Φ(θ) = log Z(θ)`. -/
noncomputable def Phi (θ : ι → ℝ) : ℝ :=
  Real.log (Z θ)

/--
Finite diagonal Cartan Weyl/log-volume readout.

For a diagonal Cartan element with coordinates `θᵢ`, the determinant cocycle
gives `log det(exp(diag θ)) = ∑ᵢ θᵢ`.  This is deliberately separate from
`Phi θ = log (∑ᵢ exp θᵢ)`, the statistical Massieu potential.
-/
noncomputable def weylLogVolume (θ : ι → ℝ) : ℝ :=
  ∑ i, θ i

/-- Souriau/Massieu name for the Cartan log-partition potential. -/
noncomputable abbrev massieu (θ : ι → ℝ) : ℝ :=
  Phi θ

/-- The finite Cartan Gibbs/softmax probability. -/
noncomputable def prob (θ : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (θ i) / Z θ

/-- Algebraic log-density of the finite Cartan Gibbs state. -/
noncomputable def logDensity (θ : ι → ℝ) (i : ι) : ℝ :=
  θ i - Phi θ

/-- Surprisal operator readout in the diagonal finite Cartan model. -/
noncomputable def surprisal (θ : ι → ℝ) (i : ι) : ℝ :=
  Phi θ - θ i

/-- Expectation with respect to the Cartan Gibbs/softmax law. -/
noncomputable def expect (θ : ι → ℝ) (X : ι → ℝ) : ℝ :=
  ∑ i, prob θ i * X i

/-- Boltzmann entropy as expected surprisal. -/
noncomputable def boltzmannEntropy (θ : ι → ℝ) : ℝ :=
  expect θ (surprisal θ)

/-- KL divergence between two Cartan exponential-family states. -/
noncomputable def kl (θ η : ι → ℝ) : ℝ :=
  expect θ (fun i => logDensity θ i - logDensity η i)

/--
Massieu-Bregman divergence with orientation matching
`KL(p_θ || p_η)`.
-/
noncomputable def bregmanPhi (θ η : ι → ℝ) : ℝ :=
  Phi η - Phi θ + expect θ (fun i => θ i - η i)

/-- The centered Fisher/covariance bilinear form. -/
noncomputable def fisherCov (θ : ι → ℝ) (X Y : ι → ℝ) : ℝ :=
  ∑ i, prob θ i * (X i - expect θ X) * (Y i - expect θ Y)

/-- A linear Cartan slice is centered when its coordinate sum vanishes. -/
def centered (X : ι → ℝ) : Prop :=
  ∑ i, X i = 0

/-- The Weyl/log-volume Cartan readout is affine along every Cartan direction. -/
theorem weylLogVolume_add_smul (θ X : ι → ℝ) (t : ℝ) :
    weylLogVolume (fun i => θ i + t * X i) =
      weylLogVolume θ + t * weylLogVolume X := by
  unfold weylLogVolume
  rw [Finset.sum_add_distrib]
  rw [Finset.mul_sum]

/--
The determinant/Weyl log-volume readout has zero mixed second finite
difference.  This is the formal finite-Cartan expression of the warning that
`log det(exp(θ·H))` is linear and therefore does not generate Fisher geometry.
-/
theorem weylLogVolume_mixedSecondDifference_zero
    (θ X Y : ι → ℝ) (s t : ℝ) :
    weylLogVolume (fun i => θ i + s * X i + t * Y i)
      - weylLogVolume (fun i => θ i + s * X i)
      - weylLogVolume (fun i => θ i + t * Y i)
      + weylLogVolume θ = 0 := by
  unfold weylLogVolume
  simp only [Finset.sum_add_distrib]
  ring

lemma Z_pos [Nonempty ι] (θ : ι → ℝ) : 0 < Z θ := by
  classical
  unfold Z
  exact
    Finset.sum_pos
      (s := (Finset.univ : Finset ι))
      (f := fun i => Real.exp (θ i))
      (by
        intro i hi
        exact Real.exp_pos _)
      Finset.univ_nonempty

lemma prob_pos (θ : ι → ℝ) (hZ : 0 < Z θ) (i : ι) :
    0 < prob θ i := by
  unfold prob
  exact div_pos (Real.exp_pos _) hZ

lemma prob_nonneg (θ : ι → ℝ) (hZ : 0 < Z θ) (i : ι) :
    0 ≤ prob θ i := by
  exact le_of_lt (prob_pos (θ := θ) hZ i)

lemma prob_sum_one [Nonempty ι] (θ : ι → ℝ) (hZ : 0 < Z θ) :
    ∑ i, prob θ i = 1 := by
  unfold prob Z
  have hne : (∑ i, Real.exp (θ i)) ≠ 0 := ne_of_gt hZ
  calc
    ∑ i, Real.exp (θ i) / ∑ j, Real.exp (θ j)
        = (∑ i, Real.exp (θ i)) / ∑ j, Real.exp (θ j) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset ι))
                (f := fun i => Real.exp (θ i))
                (a := ∑ j, Real.exp (θ j)))
    _ = 1 := by
          exact div_self hne

lemma expect_one [Nonempty ι] (θ : ι → ℝ) (hZ : 0 < Z θ) :
    expect θ (fun _ : ι => (1 : ℝ)) = 1 := by
  unfold expect
  simp [prob_sum_one (θ := θ) hZ]

lemma expect_const [Nonempty ι] (θ : ι → ℝ) (hZ : 0 < Z θ) (c : ℝ) :
    expect θ (fun _ : ι => c) = c := by
  calc
    expect θ (fun _ : ι => c) = ∑ i, prob θ i * c := by rfl
    _ = (∑ i, prob θ i) * c := by
      rw [Finset.sum_mul]
    _ = c := by
      rw [prob_sum_one (θ := θ) hZ]
      ring

lemma expect_add (θ : ι → ℝ) (X Y : ι → ℝ) :
    expect θ (fun i => X i + Y i) = expect θ X + expect θ Y := by
  calc
    expect θ (fun i => X i + Y i) = ∑ i, prob θ i * (X i + Y i) := by rfl
    _ = ∑ i, (prob θ i * X i + prob θ i * Y i) := by
      simp [add_mul, mul_comm]
    _ = ∑ i, prob θ i * X i + ∑ i, prob θ i * Y i := by
      rw [Finset.sum_add_distrib]

lemma expect_neg (θ : ι → ℝ) (X : ι → ℝ) :
    expect θ (fun i => -X i) = -expect θ X := by
  calc
    expect θ (fun i => -X i) = ∑ i, prob θ i * (-X i) := by rfl
    _ = - ∑ i, prob θ i * X i := by
      simp [mul_comm]

lemma expect_sub (θ : ι → ℝ) (X Y : ι → ℝ) :
    expect θ (fun i => X i - Y i) = expect θ X - expect θ Y := by
  simpa [sub_eq_add_neg, expect_neg (θ := θ) Y] using
    expect_add (θ := θ) X (fun i => -Y i)

@[simp] lemma surprisal_eq_neg_logDensity (θ : ι → ℝ) (i : ι) :
    surprisal θ i = -logDensity θ i := by
  unfold surprisal logDensity
  ring

lemma boltzmannEntropy_eq_Phi_sub_expect_parameter
    [Nonempty ι] (θ : ι → ℝ) (hZ : 0 < Z θ) :
    boltzmannEntropy θ = Phi θ - expect θ θ := by
  unfold boltzmannEntropy surprisal
  rw [expect_sub (θ := θ) (fun _ : ι => Phi θ) θ]
  rw [expect_const (θ := θ) (hZ := hZ)]

theorem kl_eq_bregmanPhi [Nonempty ι] (θ η : ι → ℝ) (hZ : 0 < Z θ) :
    kl θ η = bregmanPhi θ η := by
  unfold kl logDensity bregmanPhi
  have hpoint :
      (fun i : ι => θ i - Phi θ - (η i - Phi η))
        =
      (fun i : ι => (θ i - η i) + (Phi η - Phi θ)) := by
    funext i
    ring
  rw [hpoint]
  rw [expect_add (θ := θ) (fun i : ι => θ i - η i) (fun _ : ι => Phi η - Phi θ)]
  rw [expect_const (θ := θ) (hZ := hZ)]
  ring

lemma expect_smul_left (θ : ι → ℝ) (c : ℝ) (X : ι → ℝ) :
    expect θ (fun i => c * X i) = c * expect θ X := by
  calc
    expect θ (fun i => c * X i) = ∑ i, prob θ i * (c * X i) := by rfl
    _ = ∑ i, c * (prob θ i * X i) := by
      simp [mul_assoc, mul_comm]
    _ = c * ∑ i, prob θ i * X i := by
      rw [Finset.mul_sum]

lemma expect_smul_right (θ : ι → ℝ) (c : ℝ) (X : ι → ℝ) :
    expect θ (fun i => X i * c) = expect θ X * c := by
  calc
    expect θ (fun i => X i * c) = ∑ i, prob θ i * (X i * c) := by rfl
    _ = ∑ i, (prob θ i * X i) * c := by
      simp [mul_assoc]
    _ = (∑ i, prob θ i * X i) * c := by
      rw [Finset.sum_mul]

/--
The centered-product definition of `fisherCov` is the usual covariance
formula `E[XY] - E[X]E[Y]`.
-/
theorem fisherCov_eq_expect_mul_sub_expect_mul [Nonempty ι]
    (θ : ι → ℝ) (X Y : ι → ℝ) (hZ : 0 < Z θ) :
    fisherCov θ X Y =
      expect θ (fun i => X i * Y i) - expect θ X * expect θ Y := by
  unfold fisherCov expect
  have hsum := prob_sum_one (θ := θ) hZ
  calc
    ∑ i, prob θ i * (X i - ∑ j, prob θ j * X j) *
        (Y i - ∑ j, prob θ j * Y j)
        = ∑ i,
            (prob θ i * (X i * Y i)
              - (prob θ i * X i) * (∑ j, prob θ j * Y j)
              - (prob θ i * Y i) * (∑ j, prob θ j * X j)
              + prob θ i *
                  ((∑ j, prob θ j * X j) * (∑ j, prob θ j * Y j))) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = (∑ i, prob θ i * (X i * Y i))
        - (∑ i, prob θ i * X i) * (∑ j, prob θ j * Y j)
        - (∑ i, prob θ i * Y i) * (∑ j, prob θ j * X j)
        + (∑ i, prob θ i) *
            ((∑ j, prob θ j * X j) * (∑ j, prob θ j * Y j)) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = (∑ i, prob θ i * (X i * Y i))
        - (∑ i, prob θ i * X i) * (∑ j, prob θ j * Y j) := by
            rw [hsum]
            ring

/-- Self-covariance as second moment minus square of the first moment. -/
theorem fisherCov_self_eq_expect_sq_sub_sq
    [Nonempty ι] (θ : ι → ℝ) (X : ι → ℝ) (hZ : 0 < Z θ) :
    fisherCov θ X X = expect θ (fun i => X i ^ (2 : ℕ)) - expect θ X ^ (2 : ℕ) := by
  let μ : ℝ := expect θ X
  have hsum : ∑ i, prob θ i = 1 := prob_sum_one (θ := θ) hZ
  unfold fisherCov expect
  change
    (∑ i, prob θ i * (X i - μ) * (X i - μ)) =
      (∑ i, prob θ i * X i ^ (2 : ℕ)) - μ ^ (2 : ℕ)
  calc
    ∑ i, prob θ i * (X i - μ) * (X i - μ)
        = ∑ i, (prob θ i * X i ^ (2 : ℕ)
            - (2 : ℝ) * μ * (prob θ i * X i)
            + μ ^ (2 : ℕ) * prob θ i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, prob θ i * X i ^ (2 : ℕ))
        - (2 : ℝ) * μ * (∑ i, prob θ i * X i)
        + μ ^ (2 : ℕ) * (∑ i, prob θ i) := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = (∑ i, prob θ i * X i ^ (2 : ℕ)) - μ ^ (2 : ℕ) := by
          have hμ : (∑ i, prob θ i * X i) = μ := rfl
          rw [hsum, hμ]
          ring

/--
Algebraic pairwise form of the finite Cartan Fisher self-covariance.

This is the derivative-free positivity identity
`Var_p(X) = 1/2 ∑ᵢ∑ⱼ pᵢ pⱼ (Xᵢ - Xⱼ)^2`.
-/
theorem fisherCov_self_eq_half_pairwise
    [Nonempty ι] (θ : ι → ℝ) (X : ι → ℝ) (hZ : 0 < Z θ) :
    fisherCov θ X X =
      (1 / 2 : ℝ) *
        ∑ i, ∑ j, prob θ i * prob θ j * (X i - X j) ^ (2 : ℕ) := by
  have hsum := prob_sum_one (θ := θ) hZ
  rw [fisherCov_eq_expect_mul_sub_expect_mul (θ := θ) (X := X) (Y := X) hZ]
  unfold expect
  calc
    (∑ i, prob θ i * (X i * X i)) -
        (∑ i, prob θ i * X i) * (∑ i, prob θ i * X i)
        = (1 / 2 : ℝ) *
            ((∑ i, ∑ j, prob θ i * prob θ j * (X i * X i))
              - 2 * (∑ i, ∑ j, prob θ i * prob θ j * (X i * X j))
              + (∑ i, ∑ j, prob θ i * prob θ j * (X j * X j))) := by
          have h1 :
              (∑ i, ∑ j, prob θ i * prob θ j * (X i * X i)) =
                ∑ i, prob θ i * (X i * X i) := by
            calc
              ∑ i, ∑ j, prob θ i * prob θ j * (X i * X i)
                  = ∑ i, prob θ i * (X i * X i) * ∑ j, prob θ j := by
                    simp [← Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
              _ = ∑ i, prob θ i * (X i * X i) := by
                    rw [hsum]
                    simp
          have h2 :
              (∑ i, ∑ j, prob θ i * prob θ j * (X j * X j)) =
                ∑ j, prob θ j * (X j * X j) := by
            calc
              ∑ i, ∑ j, prob θ i * prob θ j * (X j * X j)
                  = ∑ i, prob θ i * (∑ j, prob θ j * (X j * X j)) := by
                    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
              _ = (∑ i, prob θ i) * (∑ j, prob θ j * (X j * X j)) := by
                    rw [Finset.sum_mul]
              _ = ∑ j, prob θ j * (X j * X j) := by
                    rw [hsum]
                    simp
          have h3 :
              (∑ i, ∑ j, prob θ i * prob θ j * (X i * X j)) =
                (∑ i, prob θ i * X i) * (∑ j, prob θ j * X j) := by
            calc
              ∑ i, ∑ j, prob θ i * prob θ j * (X i * X j)
                  = ∑ i, (prob θ i * X i) * (∑ j, prob θ j * X j) := by
                    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
              _ = (∑ i, prob θ i * X i) * (∑ j, prob θ j * X j) := by
                    rw [Finset.sum_mul]
          rw [h1, h2, h3]
          ring
    _ = (1 / 2 : ℝ) *
        ∑ i, ∑ j, prob θ i * prob θ j * (X i - X j) ^ (2 : ℕ) := by
          congr 1
          symm
          calc
            ∑ i, ∑ j, prob θ i * prob θ j * (X i - X j) ^ (2 : ℕ)
                = ∑ i, ∑ j,
                    (prob θ i * prob θ j * (X i * X i)
                      - 2 * (prob θ i * prob θ j * (X i * X j))
                      + prob θ i * prob θ j * (X j * X j)) := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    apply Finset.sum_congr rfl
                    intro j _hj
                    ring
            _ = ∑ i, ∑ j, prob θ i * prob θ j * (X i * X i)
                - 2 * (∑ i, ∑ j, prob θ i * prob θ j * (X i * X j))
                + ∑ i, ∑ j, prob θ i * prob θ j * (X j * X j) := by
                    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                      Finset.mul_sum]

/-- The self-covariance is nonnegative. -/
theorem fisherCov_self_nonneg (θ : ι → ℝ) (X : ι → ℝ)
    (hZ : 0 < Z θ) :
    0 ≤ fisherCov θ X X := by
  unfold fisherCov
  refine Finset.sum_nonneg ?_
  intro i hi
  have hsq : 0 ≤ (X i - expect θ X) ^ (2 : ℕ) := sq_nonneg _
  have hprob : 0 ≤ prob θ i := prob_nonneg (θ := θ) hZ i
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hprob hsq

/-- The centered Cartan slice is exactly the zero-sum slice. -/
theorem fisherCov_zero_eq_average_trace_form_of_centered
    [Nonempty ι] (X Y : ι → ℝ) (hX : centered X) (hY : centered Y) :
    fisherCov (fun _ : ι => (0 : ℝ)) X Y =
      (1 / Fintype.card ι : ℝ) * ∑ i, X i * Y i := by
  have hZ0 : Z (fun _ : ι => (0 : ℝ)) = (Fintype.card ι : ℝ) := by
    unfold Z
    simp
  have hprob :
      ∀ i : ι, prob (fun _ : ι => (0 : ℝ)) i = (1 / Fintype.card ι : ℝ) := by
    intro i
    unfold prob
    simp [hZ0]
  have hEX : expect (fun _ : ι => (0 : ℝ)) X = 0 := by
    calc
      expect (fun _ : ι => (0 : ℝ)) X = ∑ i, X i * (1 / Fintype.card ι : ℝ) := by
        unfold expect
        simp [hprob, mul_comm]
      _ = (∑ i, X i) * (1 / Fintype.card ι : ℝ) := by
        rw [Finset.sum_mul]
      _ = 0 := by
        rw [hX]
        ring
  have hEY : expect (fun _ : ι => (0 : ℝ)) Y = 0 := by
    calc
      expect (fun _ : ι => (0 : ℝ)) Y = ∑ i, Y i * (1 / Fintype.card ι : ℝ) := by
        unfold expect
        simp [hprob, mul_comm]
      _ = (∑ i, Y i) * (1 / Fintype.card ι : ℝ) := by
        rw [Finset.sum_mul]
      _ = 0 := by
        rw [hY]
        ring
  unfold fisherCov
  rw [hEX, hEY]
  simp [hprob, mul_comm, mul_left_comm]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Finset.mul_sum (s := Finset.univ) (f := fun i => X i * Y i)
      (1 / Fintype.card ι : ℝ)).symm

end InfoGeometry.Algebraic.CartanExponentialFamily
