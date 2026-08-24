import Mathlib.Tactic
import InfoGeometry.Tessellation.NilpotentFlow
import InfoGeometry.Algebra.NilpotentModularAutomorphism
import InfoGeometry.Canonical.ModularNilpotentAutomorphism
import InfoGeometry.Canonical.BogoliubovCartanFrameInterpretation

/-!
# DAG.AlgebraicExponential

Lean-checked algebraic exponential bridge for the square-zero `N` sector.

This module deliberately avoids analytic functional calculus.  In the
nilpotent sector, the only implemented exponential is the algebraic unipotent
`1 + N`, with inverse `1 - N`.  The noncommutative modular-flow expansion is
delegated to `InfoGeometry.Algebra.NilpotentModularAutomorphism`, and the
concrete `M₂(ℝ)` modular atom is delegated to
`InfoGeometry.Canonical.ModularNilpotentAutomorphism`.

KAN data is used only as a chart/readout guard: the diagonal `A`-part is a
shadow of the primitive operator, not a replacement for it.
-/

namespace DAG.AlgebraicExponential

/-! ## Generic square-zero algebraic exponential -/

/-- Algebraic exponential in a square-zero sector: `exp(N) = 1 + N`. -/
def algebraicExp {A : Type*} [Ring A] (N : A) (_hN : N * N = 0) : A :=
  1 + N

/-- The inverse candidate for `exp(N)` is `exp(-N) = 1 - N`. -/
@[simp]
theorem algebraicExp_neg_eq_one_sub {A : Type*} [Ring A] (N : A) (hN : N * N = 0) :
    algebraicExp (-N) (by noncomm_ring [hN]) = 1 - N := by
  unfold algebraicExp
  noncomm_ring

/-- Right inverse law for the square-zero algebraic exponential. -/
theorem algebraicExp_mul_neg {A : Type*} [Ring A] (N : A) (hN : N * N = 0) :
    algebraicExp N hN * algebraicExp (-N) (by noncomm_ring [hN]) = 1 := by
  simp [algebraicExp]
  noncomm_ring [hN]

/-- Left inverse law for the square-zero algebraic exponential. -/
theorem algebraicExp_neg_mul {A : Type*} [Ring A] (N : A) (hN : N * N = 0) :
    algebraicExp (-N) (by noncomm_ring [hN]) * algebraicExp N hN = 1 := by
  simp [algebraicExp]
  noncomm_ring [hN]

/-! ## Timed nilpotent sector over a noncommutative ring -/

/--
Timed nilpotent coordinate `E(T) = 1 + T N` over an arbitrary ring.

For scalar time, specialize `T` through the owner algebra map for the carrier.
-/
def timedNilpotentExp {A : Type*} [Ring A] (N T : A) : A :=
  1 + T * N

/--
Group law in the square-zero `N` sector.

The commutation hypothesis `N*T = T*N` is the necessary local algebraic
condition that kills the mixed term `(S*N)*(T*N)`.
-/
theorem timedNilpotentExp_mul {A : Type*} [Ring A]
    (N S T : A) (hN : N * N = 0) (hNT : N * T = T * N) :
    timedNilpotentExp N S * timedNilpotentExp N T =
      timedNilpotentExp N (S + T) := by
  have hNTN : N * (T * N) = 0 := by
    calc
      N * (T * N) = (N * T) * N := by noncomm_ring
      _ = (T * N) * N := by rw [hNT]
      _ = T * (N * N) := by noncomm_ring
      _ = 0 := by rw [hN, mul_zero]
  unfold timedNilpotentExp
  noncomm_ring [hNTN]

/-- Right inverse law for timed nilpotent coordinates. -/
theorem timedNilpotentExp_mul_neg {A : Type*} [Ring A]
    (N T : A) (hN : N * N = 0) (hNT : N * T = T * N) :
    timedNilpotentExp N T * timedNilpotentExp N (-T) = 1 := by
  have hNTN : N * (T * N) = 0 := by
    calc
      N * (T * N) = (N * T) * N := by noncomm_ring
      _ = (T * N) * N := by rw [hNT]
      _ = T * (N * N) := by noncomm_ring
      _ = 0 := by rw [hN, mul_zero]
  unfold timedNilpotentExp
  noncomm_ring [hNTN]

/-- Left inverse law for timed nilpotent coordinates. -/
theorem timedNilpotentExp_neg_mul {A : Type*} [Ring A]
    (N T : A) (hN : N * N = 0) (hNT : N * T = T * N) :
    timedNilpotentExp N (-T) * timedNilpotentExp N T = 1 := by
  have hNTN : N * (T * N) = 0 := by
    calc
      N * (T * N) = (N * T) * N := by noncomm_ring
      _ = (T * N) * N := by rw [hNT]
      _ = T * (N * N) := by noncomm_ring
      _ = 0 := by rw [hN, mul_zero]
  unfold timedNilpotentExp
  noncomm_ring [hNTN]

/-- Nilpotent conjugation by the algebraic exponential coordinate. -/
def nilpotentConjugation {A : Type*} [Ring A] (N T X : A) : A :=
  timedNilpotentExp N T * X * timedNilpotentExp N (-T)

/--
Exact noncommutative polynomial expansion of nilpotent conjugation.

This is the generic owner theorem re-exported through the DAG algebraic
exponential vocabulary.  The time element is central in this version.
-/
theorem nilpotentConjugation_expansion
    {A : Type*} [Ring A] (N X T : A)
    (hTcentral : ∀ Y : A, T * Y = Y * T) (hN : N * N = 0) :
    nilpotentConjugation N T X =
      X + T * (N * X - X * N) - (T * T) * (N * X * N) := by
  unfold nilpotentConjugation timedNilpotentExp
  rw [show 1 + -T * N = 1 - T * N by noncomm_ring]
  exact
    InfoGeometry.Algebra.NilpotentModularAutomorphism.nilpotent_automorphism_expansion_general_time
      N X T hTcentral hN

/-! ## Concrete `M₂(ℝ)` modular nilpotent owner readouts -/

open InfoGeometry.Canonical.ModularNilpotentAutomorphism

/-- Concrete square-zero modular generator in the owner `M₂(ℝ)` lane. -/
theorem matrix_modular_N_sq_zero :
    InfoGeometry.Canonical.SplitCliffordSourceWickBase.N *
        InfoGeometry.Canonical.SplitCliffordSourceWickBase.N =
      (0 : InfoGeometry.Canonical.ModularNilpotentAutomorphism.M2R) :=
  N_sq_zero

/-- Concrete algebraic exponential group law for the owner nilpotent flow. -/
theorem matrix_nilpotentFlow_mul (s t : ℝ) :
    nilpotentFlow s * nilpotentFlow t = nilpotentFlow (s + t) :=
  nilpotentFlow_mul s t

/-- Concrete finite modular automorphism composition law. -/
theorem matrix_modularAutomorphism_comp
    (s t : ℝ) (A : InfoGeometry.Canonical.ModularNilpotentAutomorphism.M2R) :
    modularAutomorphism s (modularAutomorphism t A) =
      modularAutomorphism (s + t) A :=
  modularAutomorphism_comp s t A

/-- Concrete finite replacement for a BCH/exponential-series claim. -/
theorem matrix_modularAutomorphism_exact_expansion
    (t : ℝ) (A : InfoGeometry.Canonical.ModularNilpotentAutomorphism.M2R) :
    modularAutomorphism t A =
      A + t •
        (InfoGeometry.Canonical.SplitCliffordSourceWickBase.N * A -
          A * InfoGeometry.Canonical.SplitCliffordSourceWickBase.N) -
        (t * t) •
          (InfoGeometry.Canonical.SplitCliffordSourceWickBase.N * A *
            InfoGeometry.Canonical.SplitCliffordSourceWickBase.N) :=
  modularAutomorphism_exact_expansion t A

/-! ## KAN chart discipline -/

/--
KAN diagonal readout is only a Cartan shadow of the primitive operator.

This is the safe bridge to the KAN lane: it records the chart discipline and
does not assert a global KAN decomposition theorem.
-/
theorem kan_diagonalReadout_is_Cartan_shadow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (O : InfoGeometry.Canonical.OperatorInBogoliubovKANChart (E := E)) :
    InfoGeometry.Canonical.IsDiagonalCartanShadow (E := E)
      O.frame O.operator O.diagonalReadout :=
  O.diagonalReadout_is_Cartan_shadow

end DAG.AlgebraicExponential
