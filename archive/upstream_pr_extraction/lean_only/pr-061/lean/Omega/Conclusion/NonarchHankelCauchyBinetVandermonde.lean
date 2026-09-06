import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper-local atomic moment sequence for the conservative nonarchimedean Hankel wrapper. -/
noncomputable def conclusion_nonarch_hankel_cauchy_binet_vandermonde_moment {K : Type*}
    [Field K] {k : Nat} (w b : Fin k -> K) (n : Nat) : K :=
  Finset.univ.sum fun i : Fin k => w i * b i ^ n

/-- Paper-local Hankel moment matrix with shift `r`. -/
noncomputable def conclusion_nonarch_hankel_cauchy_binet_vandermonde_hankel {K : Type*}
    [Field K] {k : Nat} (r : Nat) (w b : Fin k -> K) : Matrix (Fin k) (Fin k) K :=
  fun i j => conclusion_nonarch_hankel_cauchy_binet_vandermonde_moment w b (r + i.1 + j.1)

/-- Paper-local Vandermonde factor for the node vector. -/
noncomputable def conclusion_nonarch_hankel_cauchy_binet_vandermonde_vandermonde {K : Type*}
    [Field K] {k : Nat} (b : Fin k -> K) : K :=
  Matrix.det (fun i j : Fin k => b i ^ (j : Nat))

/-- Left factor in the finite Hankel factorization. -/
noncomputable def conclusion_nonarch_hankel_cauchy_binet_vandermonde_leftFactor
    {K : Type*} [Field K] {k : Nat} (r : Nat) (w b : Fin k -> K) :
    Matrix (Fin k) (Fin k) K :=
  fun i l => w l * b l ^ (r + i.1)

/-- Right Vandermonde factor in the finite Hankel factorization. -/
noncomputable def conclusion_nonarch_hankel_cauchy_binet_vandermonde_rightFactor
    {K : Type*} [Field K] {k : Nat} (b : Fin k -> K) :
    Matrix (Fin k) (Fin k) K :=
  fun l j => b l ^ (j : Nat)

lemma conclusion_nonarch_hankel_eq_leftFactor_mul_rightFactor
    {K : Type*} [Field K] {k : Nat} (r : Nat) (w b : Fin k -> K) :
    conclusion_nonarch_hankel_cauchy_binet_vandermonde_hankel r w b =
      conclusion_nonarch_hankel_cauchy_binet_vandermonde_leftFactor r w b *
        conclusion_nonarch_hankel_cauchy_binet_vandermonde_rightFactor b := by
  ext i j
  simp only [conclusion_nonarch_hankel_cauchy_binet_vandermonde_hankel,
    conclusion_nonarch_hankel_cauchy_binet_vandermonde_moment,
    conclusion_nonarch_hankel_cauchy_binet_vandermonde_leftFactor,
    conclusion_nonarch_hankel_cauchy_binet_vandermonde_rightFactor, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l hl
  rw [pow_add, pow_add]
  ring

/-- Paper label: `thm:conclusion-nonarch-hankel-cauchy-binet-vandermonde`. -/
theorem paper_conclusion_nonarch_hankel_cauchy_binet_vandermonde {K : Type*} [Field K]
    (k r : Nat) (w b : Fin k -> K) :
    Matrix.det (conclusion_nonarch_hankel_cauchy_binet_vandermonde_hankel r w b) =
      Matrix.det (conclusion_nonarch_hankel_cauchy_binet_vandermonde_leftFactor r w b) *
        Matrix.det (conclusion_nonarch_hankel_cauchy_binet_vandermonde_rightFactor b) := by
  rw [conclusion_nonarch_hankel_eq_leftFactor_mul_rightFactor, Matrix.det_mul]

end Omega.Conclusion
