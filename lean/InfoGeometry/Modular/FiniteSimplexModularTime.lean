import InfoGeometry.OperatorAlgebra.FiniteRelativeModularLogBridge
import InfoGeometry.Probability.AitchisonFinite

/-!
# Finite simplex modular time

For strictly positive probabilities `p`, construct the matrix-algebra
automorphism with entries `exp(i*t*(log p_i-log p_j))*A_ij`.
This is the finite faithful diagonal formula `rho^(it) A rho^(-it)`.
It fixes diagonal observables. It is not a motion of the classical simplex,
nor an identification of modular time with laboratory time.

The logarithmic generator reuses the existing finite relative-log owner.
-/

noncomputable section
open scoped BigOperators
namespace InfoGeometry.Modular.FiniteSimplexModularTime

open InfoGeometry.Probability.AitchisonFinite
open InfoGeometry.OperatorAlgebra.FiniteRelativeModularLogBridge

variable {n : ℕ}

/-- Phase of a matrix unit under diagonal modular time. -/
def phase (p : PositiveSimplex n) (t : ℝ) (i j : Fin n) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * ((Real.log (p.val i) - Real.log (p.val j) : ℝ) : ℂ))

theorem phase_compose (p : PositiveSimplex n) (s t : ℝ) (i j : Fin n) :
    phase p (s + t) i j = phase p s i j * phase p t i j := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_chain (p : PositiveSimplex n) (t : ℝ) (i j k : Fin n) :
    phase p t i j * phase p t j k = phase p t i k := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem phase_zero (p : PositiveSimplex n) (i j : Fin n) :
    phase p 0 i j = 1 := by simp [phase]

@[simp] theorem phase_diagonal (p : PositiveSimplex n) (t : ℝ) (i : Fin n) :
    phase p t i i = 1 := by simp [phase]

def flow (p : PositiveSimplex n) (t : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => phase p t i j * A i j

theorem flow_compose (p : PositiveSimplex n) (s t : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    flow p s (flow p t A) = flow p (s + t) A := by
  ext i j
  simp [flow, phase_compose, mul_assoc]

@[simp] theorem flow_zero (p : PositiveSimplex n) (A : Matrix (Fin n) (Fin n) ℂ) :
    flow p 0 A = A := by ext i j; simp [flow]

theorem flow_mul (p : PositiveSimplex n) (t : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    flow p t (A * B) = flow p t A * flow p t B := by
  ext i k
  simp only [flow, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← phase_chain p t i j k]
  ring

@[simp] theorem flow_diagonal (p : PositiveSimplex n) (t : ℝ) (a : Fin n → ℂ) :
    flow p t (Matrix.diagonal a) = Matrix.diagonal a := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [flow]
  · simp [flow, Matrix.diagonal_apply_ne _ h]

/-- A genuine native algebra equivalence, with explicit inverse time. -/
def automorphism (p : PositiveSimplex n) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun := flow p t
  invFun := flow p (-t)
  left_inv A := by rw [flow_compose]; simp
  right_inv A := by rw [flow_compose]; simp
  map_mul' := flow_mul p t
  map_add' A B := by ext i j; simp [flow, mul_add]
  commutes' c := by
    change flow p t (Matrix.diagonal (fun _ => c)) = Matrix.diagonal (fun _ => c)
    exact flow_diagonal p t _

/-- Aitchison coordinates give exactly the same modular frequencies. -/
theorem phase_from_clr (p : PositiveSimplex n) (hn : 0 < n) (t : ℝ) (i j : Fin n) :
    phase p t i j = Complex.exp (Complex.I * (t : ℂ) * ((clr p hn i - clr p hn j : ℝ) : ℂ)) := by
  unfold phase clr
  congr 2
  push_cast
  ring

/-- Exact identification with the established relative-surprisal eigenvalue.
The sign is fixed by the convention `relativeLog = -log p_i + log p_j`. -/
theorem phase_from_relative_log (p : PositiveSimplex n) (t : ℝ) (i j : Fin n) :
    phase p t i j = Complex.exp (-Complex.I * (t : ℂ) *
      ((relativeLogEigenvalue (p.val i) (p.val j) : ℝ) : ℂ)) := by
  unfold phase relativeLogEigenvalue
  congr 1
  push_cast
  ring

/-- Reversing a matrix unit conjugates its modular phase. -/
theorem phase_conj (p : PositiveSimplex n) (t : ℝ) (i j : Fin n) :
    star (phase p t j i) = phase p t i j := by
  unfold phase
  change starRingEnd ℂ (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp
  ring

/-- Modular time preserves the matrix adjoint, not just multiplication. -/
theorem flow_star (p : PositiveSimplex n) (t : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    flow p t (star A) = star (flow p t A) := by
  ext i j
  change phase p t i j * star (A j i) = star (phase p t j i * A j i)
  rw [star_mul, phase_conj]
  ring

/-- Its entrywise infinitesimal generator, in the existing surprisal convention. -/
theorem flow_entry_hasDerivAt (p : PositiveSimplex n) (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    HasDerivAt (fun t : ℝ => flow p t A i j)
      (-Complex.I * ((relativeLogEigenvalue (p.val i) (p.val j) : ℝ) : ℂ) * A i j) 0 := by
  have hi := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul Complex.I).mul_const
    ((Real.log (p.val i) - Real.log (p.val j) : ℝ) : ℂ)
  have he := hi.cexp.mul_const (A i j)
  convert he using 1
  simp [relativeLogEigenvalue]
  ring

theorem relativeLogAction_entry (p : PositiveSimplex n)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    relativeLogAction p.val p.val A i j =
      ((relativeLogEigenvalue (p.val i) (p.val j) : ℝ) : ℂ) * A i j := by
  change (leftSurprisalMatrix p.val * A - A * rightSurprisalMatrix p.val) i j = _
  simp [leftSurprisalMatrix, rightSurprisalMatrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal, relativeLogEigenvalue]
  ring

/-- The full finite matrix-valued derivative equals the existing relative-log
operator multiplied by `-i`; this closes the generator/flow connection. -/
theorem flow_hasDerivAt (p : PositiveSimplex n) (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => flow p t A)
      (-Complex.I • relativeLogAction p.val p.val A) 0 := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have h := flow_entry_hasDerivAt p A i j
  convert h using 1
  simp only [Matrix.smul_apply, smul_eq_mul, relativeLogAction_entry]
  ring

end InfoGeometry.Modular.FiniteSimplexModularTime
