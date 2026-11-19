# Tagged Lean code blocks: `aistudio_prompt_1QhCkzoYhtpLFNaD0O8SPXJK0YU5jngHO.json`

## Turn 0003, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeCliffordMellin

/-!
## Infrastructure: Extensionality and Evaluation for $2 \times 2$ Noncommutative Operator Matrices
-/

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section MatrixSimpLemmas

variable {A : Type*} [Ring A]

@[simp]
lemma mul_apply_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one_apply_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one_apply_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one_apply_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one_apply_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp]
lemma of_fin2_00 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl

@[simp]
lemma of_fin2_01 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl

@[simp]
lemma of_fin2_10 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl

@[simp]
lemma of_fin2_11 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

end MatrixSimpLemmas

/-!
## Archetype 1: Noncommutative Gauge Derivations and the Commutator Curvature Obstruction
-/

section Archetype1_NonAbelianCurvature

variable {R : Type*} [Ring R]

/-- The noncommutative commutator $[X, Y] = X Y - Y X$ in an arbitrary ring $R$. -/
def comm (X Y : R) : R := X * Y - Y * X

/-- The noncommutative anticommutator $\{X, Y\} = X Y + Y X$ in an arbitrary ring $R$. -/
def anticomm (X Y : R) : R := X * Y + Y * X

/-- The inner derivation $\mathrm{ad}_A(X) = [A, X]$. -/
def ad (A X : R) : R := comm A X

/-- The Jacobi curvature identity: $[\mathrm{ad}_A, \mathrm{ad}_B](X) = \mathrm{ad}_{[A, B]}(X)$. -/
theorem ad_curvature_jacobi (A B X : R) :
    ad A (ad B X) - ad B (ad A X) = ad (comm A B) X := by
  dsimp [ad, comm]
  noncomm_ring

/-- Covariant derivation operator $D_{d, A}(X) = d(X) + A X$ on a noncommutative ring $R$. -/
def covDeriv (d : R →+ R) (A X : R) : R := d X + A * X

/-- Non-Abelian curvature element $F(d_1, d_2, A_1, A_2) = d_1(A_2) - d_2(A_1) + [A_1, A_2]$. -/
def curvatureElement (d₁ d₂ : R →+ R) (A₁ A₂ : R) : R :=
  d₁ A₂ - d₂ A₁ + comm A₁ A₂

/-- The commutator of two covariant derivations is a pure left-multiplication operator by the
non-Abelian curvature element $d_1(A_2) - d_2(A_1) + [A_1, A_2]$. -/
theorem covariant_curvature_obstruction
    (d₁ d₂ : R →+ R) (A₁ A₂ X : R)
    (h_comm : d₁ (d₂ X) = d₂ (d₁ X))
    (h_leib₁ : d₁ (A₂ * X) = d₁ A₂ * X + A₂ * d₁ X)
    (h_leib₂ : d₂ (A₁ * X) = d₂ A₁ * X + A₁ * d₂ X) :
    covDeriv d₁ A₁ (covDeriv d₂ A₂ X) - covDeriv d₂ A₂ (covDeriv d₁ A₁ X) =
      curvatureElement d₁ d₂ A₁ A₂ * X := by
  dsimp [covDeriv, curvatureElement, comm]
  rw [map_add, map_add, h_leib₁, h_leib₂, h_comm]
  noncomm_ring

end Archetype1_NonAbelianCurvature

/-!
## Archetype 2: Operator-Valued $Cl(1,1)$ & Non-Abelian Weyl-Heisenberg Braiding
-/

section Archetype2_CliffordWeylBraiding

variable {A : Type*} [Ring A]

/-- Spacelike grading involution / Sylvester clock operator $\Gamma_1 = \mathrm{diag}(1, -1)$. -/
def Γ₁ : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]

/-- Symmetric off-diagonal shift operator $\Sigma = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def Σ_op : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]

/-- Canonical symplectic / timelike generator $\Omega = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$. -/
def Ω : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]

theorem Γ₁_sq : (Γ₁ : Matrix (Fin 2) (Fin 2) A) * Γ₁ = 1 := by
  apply ext_fin2 <;> simp [Γ₁]

theorem Σ_op_sq : (Σ_op : Matrix (Fin 2) (Fin 2) A) * Σ_op = 1 := by
  apply ext_fin2 <;> simp [Σ_op]

theorem Ω_sq : (Ω : Matrix (Fin 2) (Fin 2) A) * Ω = -1 := by
  apply ext_fin2 <;> simp [Ω]

theorem Σ_mul_Γ₁ : (Σ_op : Matrix (Fin 2) (Fin 2) A) * Γ₁ = Ω := by
  apply ext_fin2 <;> simp [Σ_op, Γ₁, Ω]

theorem Γ₁_mul_Σ : (Γ₁ : Matrix (Fin 2) (Fin 2) A) * Σ_op = -Ω := by
  apply ext_fin2 <;> simp [Γ₁, Σ_op, Ω]

theorem anticomm_Γ₁_Σ : anticomm (Γ₁ : Matrix (Fin 2) (Fin 2) A) Σ_op = 0 := by
  apply ext_fin2 <;> simp [anticomm, Γ₁, Σ_op]

theorem anticomm_Γ₁_Ω : anticomm (Γ₁ : Matrix (Fin 2) (Fin 2) A) Ω = 0 := by
  apply ext_fin2 <;> simp [anticomm, Γ₁, Ω]

theorem anticomm_Σ_Ω : anticomm (Σ_op : Matrix (Fin 2) (Fin 2) A) Ω = 0 := by
  apply ext_fin2 <;> simp [anticomm, Σ_op, Ω]

/-- Operator-lifted Weyl clock matrix $Z(q) = \begin{pmatrix} 1 & 0 \\ 0 & q \end{pmatrix}$. -/
def Z_lift (q : A) : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, q]]

/-- Non-Abelian operator-valued hyperbolic Mellin dilation / Weyl braiding factor
$\Theta(u) = \begin{pmatrix} u & 0 \\ 0 & u^{-1} \end{pmatrix}$ for $u \in A^\times$. -/
def mellinDilation (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  ![![(u : A), 0], ![0, (↑u⁻¹ : A)]]

/-- Lifting the scalar phase of the Weyl-Heisenberg relation to a non-commuting unit $u \in A^\times$
yields the operator-braided relation $\Sigma Z(u) = \Theta(u) Z(u) \Sigma$. -/
theorem nonabelian_weyl_braiding (u : Aˣ) :
    (Σ_op : Matrix (Fin 2) (Fin 2) A) * Z_lift (u : A) =
      mellinDilation u * Z_lift (u : A) * Σ_op := by
  apply ext_fin2 <;> simp [Σ_op, Z_lift, mellinDilation]

/-- Conjugating the non-Abelian braiding factor $\Theta(u)$ by the shift $\Sigma$ inverts the
hyperbolic scaling: $\Sigma \Theta(u) \Sigma = \Theta(u^{-1})$. -/
theorem mellinDilation_shift_inversion (u : Aˣ) :
    (Σ_op : Matrix (Fin 2) (Fin 2) A) * mellinDilation u * Σ_op = mellinDilation u⁻¹ := by
  apply ext_fin2 <;> simp [Σ_op, mellinDilation]

end Archetype2_CliffordWeylBraiding

/-!
## Archetype 3: Internal Noncommutative Symplectic Twist & Signature Inversion
-/

section Archetype3_InternalSymplecticTwist

variable {A : Type*} [Ring A]

/-- Symmetric off-diagonal operator twisted by an internal operator $J \in A$. -/
def Σ_J (J : A) : Matrix (Fin 2) (Fin 2) A := ![![0, J], ![J, 0]]

/-- Skew off-diagonal operator twisted by an internal operator $J \in A$. -/
def Ω_J (J : A) : Matrix (Fin 2) (Fin 2) A := ![![0, -J], ![J, 0]]

/-- When $J^2 = -1$ in $A$, the square of the symmetric off-diagonal lift $\Sigma_J$ flips from $+1$ to $-1$. -/
theorem Σ_J_sq_of_sq_eq_neg_one {J : A} (hJ : J * J = -1) :
    Σ_J J * Σ_J J = -1 := by
  apply ext_fin2 <;> simp [Σ_J, hJ]

/-- When $J^2 = -1$ in $A$, the square of the skew off-diagonal lift $\Omega_J$ flips from $-1$ to $+1$. -/
theorem Ω_J_sq_of_sq_eq_neg_one {J : A} (hJ : J * J = -1) :
    Ω_J J * Ω_J J = 1 := by
  apply ext_fin2 <;> simp [Ω_J, hJ]

theorem anticomm_Γ₁_Σ_J (J : A) : anticomm (Γ₁ : Matrix (Fin 2) (Fin 2) A) (Σ_J J) = 0 := by
  apply ext_fin2 <;> simp [anticomm, Γ₁, Σ_J]

theorem anticomm_Γ₁_Ω_J (J : A) : anticomm (Γ₁ : Matrix (Fin 2) (Fin 2) A) (Ω_J J) = 0 := by
  apply ext_fin2 <;> simp [anticomm, Γ₁, Ω_J]

theorem anticomm_Σ_J_Ω_J (J : A) : anticomm (Σ_J J) (Ω_J J) = 0 := by
  apply ext_fin2 <;> simp [anticomm, Σ_J, Ω_J]

end Archetype3_InternalSymplecticTwist

/-!
## Archetype 4: Peirce Idempotent Projectors & The $\mathbb{Z}_2$-Graded DeWitt Super-Split
-/

section Archetype4_PeirceDeWittSplit

variable {A : Type*} [Ring A]

/-- Positive chirality Peirce idempotent $P_+ = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def P_plus : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]

/-- Negative chirality Peirce idempotent $P_- = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]

theorem P_plus_idem : (P_plus : Matrix (Fin 2) (Fin 2) A) * P_plus = P_plus := by
  apply ext_fin2 <;> simp [P_plus]

theorem P_minus_idem : (P_minus : Matrix (Fin 2) (Fin 2) A) * P_minus = P_minus := by
  apply ext_fin2 <;> simp [P_minus]

theorem P_plus_mul_P_minus : (P_plus : Matrix (Fin 2) (Fin 2) A) * P_minus = 0 := by
  apply ext_fin2 <;> simp [P_plus, P_minus]

theorem P_minus_mul_P_plus : (P_minus : Matrix (Fin 2) (Fin 2) A) * P_plus = 0 := by
  apply ext_fin2 <;> simp [P_plus, P_minus]

theorem P_plus_add_P_minus :
    (P_plus : Matrix (Fin 2) (Fin 2) A) + P_minus = 1 := by
  apply ext_fin2 <;> simp [P_plus, P_minus]

theorem P_plus_sub_P_minus :
    (P_plus : Matrix (Fin 2) (Fin 2) A) - P_minus = Γ₁ := by
  apply ext_fin2 <;> simp [P_plus, P_minus, Γ₁]

/-- Shift intertwining: $\Sigma$ swaps the orthogonal Peirce subspaces $P_+$ and $P_-$. -/
theorem P_plus_mul_Σ :
    (P_plus : Matrix (Fin 2) (Fin 2) A) * Σ_op = Σ_op * P_minus := by
  apply ext_fin2 <;> simp [P_plus, P_minus, Σ_op]

theorem P_minus_mul_Σ :
    (P_minus : Matrix (Fin 2) (Fin 2) A) * Σ_op = Σ_op * P_plus := by
  apply ext_fin2 <;> simp [P_plus, P_minus, Σ_op]

/-- Even (diagonal / DeWitt body) Peirce projection $M_{\mathrm{even}} = P_+ M P_+ + P_- M P_-$. -/
def dewittEven (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * M * P_plus + P_minus * M * P_minus

/-- Odd (off-diagonal / DeWitt soul) Peirce projection $M_{\mathrm{odd}} = P_+ M P_- + P_- M P_+$. -/
def dewittOdd (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * M * P_minus + P_minus * M * P_plus

/-- Complete two-sided Peirce decomposition $M = M_{\mathrm{even}} + M_{\mathrm{odd}}$. -/
theorem peirce_dewitt_decomposition (M : Matrix (Fin 2) (Fin 2) A) :
    dewittEven M + dewittOdd M = M := by
  apply ext_fin2 <;> simp [dewittEven, dewittOdd, P_plus, P_minus]

/-- The even DeWitt sector commutes with the grading involution $\Gamma_1$. -/
theorem dewittEven_comm_Γ₁ (M : Matrix (Fin 2) (Fin 2) A) :
    comm (Γ₁ : Matrix (Fin 2) (Fin 2) A) (dewittEven M) = 0 := by
  apply ext_fin2 <;> simp [comm, Γ₁, dewittEven, P_plus, P_minus]

/-- The odd DeWitt sector anticommutes with the grading involution $\Gamma_1$. -/
theorem dewittOdd_anticomm_Γ₁ (M : Matrix (Fin 2) (Fin 2) A) :
    anticomm (Γ₁ : Matrix (Fin 2) (Fin 2) A) (dewittOdd M) = 0 := by
  apply ext_fin2 <;> simp [anticomm, Γ₁, dewittOdd, P_plus, P_minus]

/-- Grading involution action: $\Gamma_1 M \Gamma_1 = M_{\mathrm{even}} - M_{\mathrm{odd}}$. -/
theorem grading_conj_eq_even_sub_odd (M : Matrix (Fin 2) (Fin 2) A) :
    (Γ₁ : Matrix (Fin 2) (Fin 2) A) * M * Γ₁ = dewittEven M - dewittOdd M := by
  apply ext_fin2 <;> simp [Γ₁, dewittEven, dewittOdd, P_plus, P_minus] <;> noncomm_ring

/-- $\mathbb{Z}_2$-superalgebra closure: the product of two odd elements is purely even. -/
theorem dewittOdd_mul_dewittOdd_is_even (M N : Matrix (Fin 2) (Fin 2) A) :
    dewittOdd (dewittOdd M * dewittOdd N) = 0 := by
  apply ext_fin2 <;> simp [dewittOdd, P_plus, P_minus]

end Archetype4_PeirceDeWittSplit

/-!
## Archetype 5: Coordinate-Free Noncommutative Clifford-Walsh-Mellin Transform
-/

section Archetype5_CliffordWalshMellinTransform

variable {A : Type*} [Ring A]

/-- Diagonal embedding of the noncommutative base ring $A$ into $M_2(A)$. -/
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := ![![a, 0], ![0, a]]

/-- Even though $A$ is noncommutative, `fiberEmbed a` commutes with all $Cl(1,1)$ generators,
witnessing the tensor product factorization $M_2(A) \cong Cl(1,1) \otimes_{\mathbb{Z}} A$. -/
theorem fiberEmbed_comm_Γ₁ (a : A) :
    fiberEmbed a * (Γ₁ : Matrix (Fin 2) (Fin 2) A) = Γ₁ * fiberEmbed a := by
  apply ext_fin2 <;> simp [fiberEmbed, Γ₁]

theorem fiberEmbed_comm_Σ (a : A) :
    fiberEmbed a * (Σ_op : Matrix (Fin 2) (Fin 2) A) = Σ_op * fiberEmbed a := by
  apply ext_fin2 <;> simp [fiberEmbed, Σ_op]

theorem fiberEmbed_comm_Ω (a : A) :
    fiberEmbed a * (Ω : Matrix (Fin 2) (Fin 2) A) = Ω * fiberEmbed a := by
  apply ext_fin2 <;> simp [fiberEmbed, Ω]

/-- Coordinate-free Peirce fiber lift $\mathcal{L}(X) = P_+ X P_+ + \Sigma P_+ X P_+ \Sigma$,
which projects the top-left corner via $P_+$ and clones it across the diagonal via $\Sigma$. -/
def peirceFiberLift (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * X * P_plus + Σ_op * P_plus * X * P_plus * Σ_op

/-- $\mathcal{L}(X)$ is identically the diagonal fiber embedding of the $(0,0)$ entry of $X$. -/
theorem peirceFiberLift_eq_fiberEmbed (X : Matrix (Fin 2) (Fin 2) A) :
    peirceFiberLift X = fiberEmbed (X 0 0) := by
  apply ext_fin2 <;> simp [peirceFiberLift, fiberEmbed, P_plus, Σ_op]

/-- Discrete Mellin-Walsh scale-symmetric diagonal transform component $\widehat{M}_I$. -/
def mellinCoeff_I (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M + Σ_op * M * Σ_op)

/-- Discrete Mellin-Walsh scale-antisymmetric grading transform component $\widehat{M}_\Gamma$. -/
def mellinCoeff_Γ (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M - Σ_op * M * Σ_op)

/-- Discrete Mellin-Walsh symmetric shift transform component $\widehat{M}_\Sigma$. -/
def mellinCoeff_Σ (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M * Σ_op + Σ_op * M)

/-- Discrete Mellin-Walsh symplectic bivector transform component $\widehat{M}_\Omega$. -/
def mellinCoeff_Ω (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (Σ_op * M - M * Σ_op)

/-- **The Coordinate-Free Noncommutative Clifford-Mellin-Walsh Reconstruction Theorem**:
Every operator matrix $M \in M_2(A)$ over any noncommutative ring $A$ is reconstructed from its
four Peirce-extracted Mellin-Walsh parity components paired with $\{1, \Gamma_1, \Sigma, \Omega\}$. -/
theorem clifford_mellin_walsh_inversion (M : Matrix (Fin 2) (Fin 2) A) :
    mellinCoeff_I M * 1 +
    mellinCoeff_Γ M * Γ₁ +
    mellinCoeff_Σ M * Σ_op +
    mellinCoeff_Ω M * Ω = M + M := by
  apply ext_fin2 <;>
    simp [mellinCoeff_I, mellinCoeff_Γ, mellinCoeff_Σ, mellinCoeff_Ω,
      peirceFiberLift, P_plus, Γ₁, Σ_op, Ω] <;>
    noncomm_ring

end Archetype5_CliffordWalshMellinTransform

/-!
## Archetype 6 & 7: Noncommutative Symplectic Lie Algebra $\mathfrak{sp}_2(A, \star)$ & Hyperbolic Mellin Squeeze Group
-/

section Archetype6_SymplecticLieAndMellinSqueeze

variable {A : Type*} [Ring A] [StarRing A]

/-- An operator matrix $X \in M_2(A)$ belongs to the noncommutative symplectic Lie algebra
$\mathfrak{sp}_2(A, \star)$ if $X^\dagger \Omega + \Omega X = 0$. -/
def IsSymplecticLie (X : Matrix (Fin 2) (Fin 2) A) : Prop :=
  Xᴴ * Ω + Ω * X = 0

/-- **Lie Bracket Closure of $\mathfrak{sp}_2(A, \star)$**:
For any $X, Y \in \mathfrak{sp}_2(A, \star)$ over a noncommutative $\star$-ring $A$, their
commutator $[X, Y] = X Y - Y X$ also lies in $\mathfrak{sp}_2(A, \star)$. -/
theorem isSymplecticLie_comm {X Y : Matrix (Fin 2) (Fin 2) A}
    (hX : IsSymplecticLie X) (hY : IsSymplecticLie Y) :
    IsSymplecticLie (comm X Y) := by
  dsimp [IsSymplecticLie, comm] at *
  have hX' : Xᴴ * Ω = -(Ω * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * Ω = -(Ω * Y) := eq_neg_of_add_eq_zero_left hY
  calc (X * Y - Y * X)ᴴ * Ω + Ω * (X * Y - Y * X)
    _ = (Yᴴ * Xᴴ - Xᴴ * Yᴴ) * Ω + Ω * (X * Y - Y * X) := by
        rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
    _ = Yᴴ * (Xᴴ * Ω) - Xᴴ * (Yᴴ * Ω) + Ω * (X * Y - Y * X) := by
        noncomm_ring
    _ = Yᴴ * (-(Ω * X)) - Xᴴ * (-(Ω * Y)) + Ω * (X * Y - Y * X) := by
        rw [hX', hY']
    _ = -((Yᴴ * Ω) * X) + (Xᴴ * Ω) * Y + Ω * (X * Y - Y * X) := by
        noncomm_ring
    _ = -(-(Ω * Y) * X) + (-(Ω * X)) * Y + Ω * (X * Y - Y * X) := by
        rw [hX', hY']
    _ = 0 := by
        noncomm_ring

/-- Canonical Hamiltonian block constructor $\begin{pmatrix} a & b \\ c & -a^\star \end{pmatrix}$
over a noncommutative $\star$-ring $A$. -/
def hamiltonianBlock (a b c : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![a, b], ![c, -star a]]

/-- Every block matrix $\begin{pmatrix} a & b \\ c & -a^\star \end{pmatrix}$ with self-adjoint
off-diagonal operators $b^\star = b$ and $c^\star = c$ belongs to $\mathfrak{sp}_2(A, \star)$. -/
theorem hamiltonianBlock_isSymplecticLie (a b c : A)
    (hb : star b = b) (hc : star c = c) :
    IsSymplecticLie (hamiltonianBlock a b c) := by
  dsimp [IsSymplecticLie, hamiltonianBlock]
  apply ext_fin2 <;> simp [Ω, hb, hc]

/-- The grading generator $\Gamma_1 = \mathrm{diag}(1, -1)$ is itself a Hamiltonian generator in
$\mathfrak{sp}_2(A, \star)$, generating hyperbolic Mellin dilations. -/
theorem Γ₁_isSymplecticLie : IsSymplecticLie (Γ₁ : Matrix (Fin 2) (Fin 2) A) := by
  dsimp [IsSymplecticLie]
  apply ext_fin2 <;> simp [Γ₁, Ω]

/-- Operator-valued hyperbolic Mellin squeeze transformation
$S(u) = \begin{pmatrix} u & 0 \\ 0 & (u^{-1})^\star \end{pmatrix}$ for $u \in A^\times$. -/
def mellinSqueeze (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  ![![(u : A), 0], ![0, star (↑u⁻¹ : A)]]

/-- Peirce decomposition of the hyperbolic Mellin squeeze operator: $S(u)$ scales the $P_+$
Lagrangian sector by $u$ and the $P_-$ sector by $(u^{-1})^\star$. -/
theorem mellinSqueeze_peirce_split (u : Aˣ) :
    mellinSqueeze u =
      fiberEmbed (u : A) * P_plus + fiberEmbed (star (↑u⁻¹ : A)) * P_minus := by
  apply ext_fin2 <;> simp [mellinSqueeze, fiberEmbed, P_plus, P_minus]

/-- **Exact Noncommutative Symplectomorphism of the Hyperbolic Mellin Squeeze**:
For any invertible element $u \in A^\times$ in a noncommutative $\star$-ring $A$,
$S(u)^\dagger \Omega S(u) = \Omega$. -/
theorem mellinSqueeze_preserves_symplectic_form (u : Aˣ) :
    (mellinSqueeze u)ᴴ * Ω * mellinSqueeze u = Ω := by
  have h1 : star (u : A) * star (↑u⁻¹ : A) = 1 := by
    rw [← star_mul, Units.inv_mul, star_one]
  have h2 : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  apply ext_fin2
  · simp [mellinSqueeze, Ω]
  · simp [mellinSqueeze, Ω]
     rw [← neg_mul, h1]
  · simp [mellinSqueeze, Ω, h2]
  · simp [mellinSqueeze, Ω]

end Archetype6_SymplecticLieAndMellinSqueeze

end NoncommutativeCliffordMellin
```

## Turn 0006, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeAttentionDecomposition

/-!
## Foundational Infrastructure: $2 \times 2$ Operator Matrices & $Cl(1,1)$-Peirce Basis
-/

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section MatrixSimpLemmas

variable {A : Type*} [Ring A]

@[simp]
lemma mul_apply_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one_apply_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one_apply_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one_apply_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one_apply_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp]
lemma of_fin2_00 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl

@[simp]
lemma of_fin2_01 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl

@[simp]
lemma of_fin2_10 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl

@[simp]
lemma of_fin2_11 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

@[simp]
lemma conjTranspose_apply_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 0 = star (M 0 0) := rfl

@[simp]
lemma conjTranspose_apply_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 1 = star (M 1 0) := rfl

@[simp]
lemma conjTranspose_apply_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 0 = star (M 0 1) := rfl

@[simp]
lemma conjTranspose_apply_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 1 = star (M 1 1) := rfl

/-- Canonical $Cl(1,1)$ and Peirce operators over a noncommutative ring $A$. -/
def Γ₁ : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]
def Σ_op : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]
def Ω : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]
def P_plus : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]

end MatrixSimpLemmas

/-!
## Archetype $\mathcal{B}_1$: Noncommutative Sesquilinear Affinity & Polar-Cartesian ($\star$-Hermitian / Skew-Hermitian) Split
-/

section ArchetypeB1_SesquilinearAffinity

variable {A : Type*} [Ring A] [StarRing A]

/-- The noncommutative sesquilinear affinity operator $\mathcal{K}(Q, K) = Q K^\dagger$. -/
def affinity (Q K : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Q * Kᴴ

/-- The linear attention operator $\mathrm{Attn}(W, V) = W V$ for an affinity matrix $W$ and value $V$. -/
def attention (W V : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  W * V

/-- Bidirectional (Hermitian / mutual) affinity $\mathcal{K}_{\mathrm{sym}}(Q, K) = Q K^\dagger + K Q^\dagger$. -/
def symAffinity (Q K : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Q * Kᴴ + K * Qᴴ

/-- Directed relational flux (skew-Hermitian affinity) $\mathcal{K}_{\mathrm{skew}}(Q, K) = Q K^\dagger - K Q^\dagger$. -/
def skewAffinity (Q K : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Q * Kᴴ - K * Qᴴ

/-- Taking the conjugate transpose of the affinity operator swaps Query and Key:
$\mathcal{K}(Q, K)^\dagger = \mathcal{K}(K, Q)$. -/
theorem affinity_conjTranspose (Q K : Matrix (Fin 2) (Fin 2) A) :
    (affinity Q K)ᴴ = affinity K Q := by
  dsimp [affinity]
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- Bidirectional affinity is strictly self-adjoint: $\mathcal{K}_{\mathrm{sym}}(Q, K)^\dagger = \mathcal{K}_{\mathrm{sym}}(Q, K)$. -/
theorem symAffinity_isSelfAdjoint (Q K : Matrix (Fin 2) (Fin 2) A) :
    (symAffinity Q K)ᴴ = symAffinity Q K := by
  dsimp [symAffinity]
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_conjTranspose, add_comm]

/-- Directed relational flux is strictly skew-adjoint: $\mathcal{K}_{\mathrm{skew}}(Q, K)^\dagger = -\mathcal{K}_{\mathrm{skew}}(Q, K)$. -/
theorem skewAffinity_isSkewAdjoint (Q K : Matrix (Fin 2) (Fin 2) A) :
    (skewAffinity Q K)ᴴ = -skewAffinity Q K := by
  dsimp [skewAffinity]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_conjTranspose, neg_sub]

/-- **Polar-Cartesian Decomposition of Noncommutative Affinity**:
Every doubled affinity matrix $2 \mathcal{K}(Q, K)$ splits into its self-adjoint bidirectional part
and its skew-adjoint directed relational flux. -/
theorem affinity_sym_skew_decomposition (Q K : Matrix (Fin 2) (Fin 2) A) :
    symAffinity Q K + skewAffinity Q K = affinity Q K + affinity Q K := by
  dsimp [symAffinity, skewAffinity, affinity]
  noncomm_ring

end ArchetypeB1_SesquilinearAffinity

/-!
## Archetype $\mathcal{B}_2$: Symplectic Krein-Affinity Pairing & Dual Hyperbolic Mellin Gauge Invariance
-/

section ArchetypeB2_SymplecticAffinityAndGaugeInvariance

variable {A : Type*} [Ring A] [StarRing A]

/-- The symplectic Krein-affinity pairing $\mathcal{K}_\Omega(Q, K) = Q \Omega K^\dagger$. -/
def symplecticAffinity (Q K : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Q * Ω * Kᴴ

theorem Ω_conjTranspose : (Ω : Matrix (Fin 2) (Fin 2) A)ᴴ = -Ω := by
  apply ext_fin2 <;> simp [Ω]

/-- Adjoint anti-symmetry of the symplectic affinity kernel:
$\mathcal{K}_\Omega(Q, K)^\dagger = -\mathcal{K}_\Omega(K, Q)$. -/
theorem symplecticAffinity_conjTranspose (Q K : Matrix (Fin 2) (Fin 2) A) :
    (symplecticAffinity Q K)ᴴ = -symplecticAffinity K Q := by
  dsimp [symplecticAffinity]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Ω_conjTranspose]
  noncomm_ring

/-- Operator-valued hyperbolic Mellin squeeze $S(u) = \begin{pmatrix} u & 0 \\ 0 & (u^{-1})^\star \end{pmatrix}$. -/
def mellinSqueeze (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  ![![(u : A), 0], ![0, star (↑u⁻¹ : A)]]

/-- Dual hyperbolic Mellin squeeze $S^\sharp(u) = \begin{pmatrix} (u^{-1})^\star & 0 \\ 0 & u \end{pmatrix}$. -/
def mellinDualSqueeze (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  ![![star (↑u⁻¹ : A), 0], ![0, (u : A)]]

theorem mellinSqueeze_preserves_Ω (u : Aˣ) :
    (mellinSqueeze u)ᴴ * Ω * mellinSqueeze u = Ω := by
  have h1 : star (u : A) * star (↑u⁻¹ : A) = 1 := by
    rw [← star_mul, Units.inv_mul, star_one]
  have h2 : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  apply ext_fin2
  · simp [mellinSqueeze, Ω]
  · simp [mellinSqueeze, Ω]
    rw [← neg_mul, h1]
  · simp [mellinSqueeze, Ω, h2]
  · simp [mellinSqueeze, Ω]

/-- Biorthogonality between the hyperbolic Mellin squeeze $S(u)$ and its dual $S^\sharp(u)$:
$S(u) (S^\sharp(u))^\dagger = I$. -/
theorem mellinSqueeze_mul_dual_conjTranspose (u : Aˣ) :
    mellinSqueeze u * (mellinDualSqueeze u)ᴴ = 1 := by
  have h1 : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  have h2 : star (↑u⁻¹ : A) * star (u : A) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  apply ext_fin2
  · simp [mellinSqueeze, mellinDualSqueeze, h1]
  · simp [mellinSqueeze, mellinDualSqueeze]
  · simp [mellinSqueeze, mellinDualSqueeze]
  · simp [mellinSqueeze, mellinDualSqueeze, h2]

/-- **Symplectic Affinity Gauge Invariance**:
Co-transforming Query and Key by the hyperbolic Mellin squeeze $S(u)^\dagger$ leaves the
symplectic affinity $\mathcal{K}_\Omega(Q, K)$ strictly invariant. -/
theorem symplecticAffinity_squeeze_invariance
    (Q K : Matrix (Fin 2) (Fin 2) A) (u : Aˣ) :
    symplecticAffinity (Q * (mellinSqueeze u)ᴴ) (K * (mellinSqueeze u)ᴴ) =
      symplecticAffinity Q K := by
  calc symplecticAffinity (Q * (mellinSqueeze u)ᴴ) (K * (mellinSqueeze u)ᴴ)
    _ = Q * (mellinSqueeze u)ᴴ * Ω * (mellinSqueeze u * Kᴴ) := by
        dsimp [symplecticAffinity]
        rw [conjTranspose_mul, conjTranspose_conjTranspose]
    _ = Q * ((mellinSqueeze u)ᴴ * Ω * mellinSqueeze u) * Kᴴ := by
        noncomm_ring
    _ = Q * Ω * Kᴴ := by
        rw [mellinSqueeze_preserves_Ω]
    _ = symplecticAffinity Q K := rfl

/-- **Biorthogonal Mellin Gauge Invariance of Standard Affinity**:
Scaling Queries by $S(u)$ and Keys by the dual Mellin squeeze $S^\sharp(u)$ leaves the
noncommutative affinity matrix $\mathcal{K}(Q, K) = Q K^\dagger$ strictly invariant. -/
theorem affinity_biorthogonal_squeeze_invariance
    (Q K : Matrix (Fin 2) (Fin 2) A) (u : Aˣ) :
    affinity (Q * mellinSqueeze u) (K * mellinDualSqueeze u) = affinity Q K := by
  calc affinity (Q * mellinSqueeze u) (K * mellinDualSqueeze u)
    _ = Q * (mellinSqueeze u * (mellinDualSqueeze u)ᴴ) * Kᴴ := by
        dsimp [affinity]
        rw [conjTranspose_mul]
        noncomm_ring
    _ = Q * 1 * Kᴴ := by
        rw [mellinSqueeze_mul_dual_conjTranspose]
    _ = affinity Q K := by
        dsimp [affinity]
        noncomm_ring

end ArchetypeB2_SymplecticAffinityAndGaugeInvariance

/-!
## Archetype $\mathcal{B}_3$: Peirce Four-Channel Intra/Cross-Sector Factorization of Affinity & Attention
-/

section ArchetypeB3_PeirceFourChannelAttention

variable {A : Type*} [Ring A] [StarRing A]

/-- Positive intra-sector self-affinity channel $W_{++} = P_+ W P_+$. -/
def channelPP (W : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * W * P_plus

/-- Negative intra-sector self-affinity channel $W_{--} = P_- W P_-$. -/
def channelMM (W : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_minus * W * P_minus

/-- Forward cross-sector affinity channel $W_{+-} = P_+ W P_-$. -/
def channelPM (W : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * W * P_minus

/-- Backward cross-sector affinity channel $W_{-+} = P_- W P_+$. -/
def channelMP (W : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_minus * W * P_plus

/-- Even (intra-sector / diagonal) DeWitt projection $M_{\mathrm{even}} = W_{++} + W_{--}$. -/
def dewittEven (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  channelPP M + channelMM M

/-- Odd (cross-sector / off-diagonal) DeWitt projection $M_{\mathrm{odd}} = W_{+-} + W_{-+}$. -/
def dewittOdd (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  channelPM M + channelMP M

/-- Four-channel Peirce resolution of any affinity operator $W$. -/
theorem four_channel_affinity_resolution (W : Matrix (Fin 2) (Fin 2) A) :
    channelPP W + channelMM W + channelPM W + channelMP W = W := by
  apply ext_fin2 <;> simp [channelPP, channelMM, channelPM, channelMP, P_plus, P_minus]

/-- **DeWitt Intra-Sector Factorization of Affinity**:
The even (intra-sector) part of $\mathcal{K}(Q, K)$ is the sum of the even-even and odd-odd
Query-Key affinities. -/
theorem affinity_dewittEven_factorization (Q K : Matrix (Fin 2) (Fin 2) A) :
    dewittEven (affinity Q K) =
      affinity (dewittEven Q) (dewittEven K) + affinity (dewittOdd Q) (dewittOdd K) := by
  apply ext_fin2 <;>
    simp [affinity, dewittEven, dewittOdd, channelPP, channelMM, channelPM, channelMP,
      P_plus, P_minus]

/-- **DeWitt Cross-Sector Factorization of Affinity**:
The odd (cross-sector) part of $\mathcal{K}(Q, K)$ is the sum of the even-odd and odd-even
Query-Key affinities. -/
theorem affinity_dewittOdd_factorization (Q K : Matrix (Fin 2) (Fin 2) A) :
    dewittOdd (affinity Q K) =
      affinity (dewittEven Q) (dewittOdd K) + affinity (dewittOdd Q) (dewittEven K) := by
  apply ext_fin2 <;>
    simp [affinity, dewittEven, dewittOdd, channelPP, channelMM, channelPM, channelMP,
      P_plus, P_minus]

/-- **$\mathbb{Z}_2$-Graded Decomposition of the Attention Operator $\mathrm{Attn}(W, V) = W V$**:
Even output values arise from intra-affinity acting on even values plus cross-affinity acting on odd values. -/
theorem attention_dewittEven_factorization (W V : Matrix (Fin 2) (Fin 2) A) :
    dewittEven (attention W V) =
      attention (dewittEven W) (dewittEven V) + attention (dewittOdd W) (dewittOdd V) := by
  apply ext_fin2 <;>
    simp [attention, dewittEven, dewittOdd, channelPP, channelMM, channelPM, channelMP,
      P_plus, P_minus]

/-- Odd output values arise from intra-affinity acting on odd values plus cross-affinity acting on even values. -/
theorem attention_dewittOdd_factorization (W V : Matrix (Fin 2) (Fin 2) A) :
    dewittOdd (attention W V) =
      attention (dewittEven W) (dewittOdd V) + attention (dewittOdd W) (dewittEven V) := by
  apply ext_fin2 <;>
    simp [attention, dewittEven, dewittOdd, channelPP, channelMM, channelPM, channelMP,
      P_plus, P_minus]

end ArchetypeB3_PeirceFourChannelAttention

/-!
## Archetype $\mathcal{B}_4$: Causal (Borel-Triangular) Masked Affinity Subalgebra & Cross-Channel Nilpotency
-/

section ArchetypeB4_CausalTriangularAffinity

variable {A : Type*} [Ring A]

/-- The forward cross-sector affinity channel $W_{+-} = P_+ W P_-$ is nilpotent of index 2. -/
theorem channelPM_sq_zero (W : Matrix (Fin 2) (Fin 2) A) :
    channelPM W * channelPM W = 0 := by
  apply ext_fin2 <;> simp [channelPM, P_plus, P_minus]

/-- The backward cross-sector affinity channel $W_{-+} = P_- W P_+$ is nilpotent of index 2. -/
theorem channelMP_sq_zero (W : Matrix (Fin 2) (Fin 2) A) :
    channelMP W * channelMP W = 0 := by
  apply ext_fin2 <;> simp [channelMP, P_plus, P_minus]

/-- Two-hop alternating cross-attention $W_{+-} V_{-+}$ lands strictly inside the positive self-sector $P_+ M_2(A) P_+$. -/
theorem channelPM_mul_channelMP_in_channelPP (W V : Matrix (Fin 2) (Fin 2) A) :
    channelPM W * channelMP V = channelPP (W * P_minus * V) := by
  apply ext_fin2 <;> simp [channelPM, channelMP, channelPP, P_plus, P_minus]

/-- Two-hop alternating cross-attention $W_{-+} V_{+-}$ lands strictly inside the negative self-sector $P_- M_2(A) P_-$. -/
theorem channelMP_mul_channelPM_in_channelMM (W V : Matrix (Fin 2) (Fin 2) A) :
    channelMP W * channelPM V = channelMM (W * P_plus * V) := by
  apply ext_fin2 <;> simp [channelPM, channelMP, channelMM, P_plus, P_minus]

/-- Causal (lower-triangular) masked affinity projection
$W_{\mathrm{causal}}(W) = W_{++} + W_{--} + W_{-+} = W - W_{+-}$. -/
def causalMask (W : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  channelPP W + channelMM W + channelMP W

/-- Causal masking is an idempotent projection on $M_2(A)$. -/
theorem causalMask_idem (W : Matrix (Fin 2) (Fin 2) A) :
    causalMask (causalMask W) = causalMask W := by
  apply ext_fin2 <;> simp [causalMask, channelPP, channelMM, channelMP, P_plus, P_minus]

/-- Causal masking annihilates the anti-causal cross-channel $P_+ (\cdot) P_-$. -/
theorem channelPM_causalMask_zero (W : Matrix (Fin 2) (Fin 2) A) :
    channelPM (causalMask W) = 0 := by
  apply ext_fin2 <;> simp [causalMask, channelPM, channelPP, channelMM, channelMP, P_plus, P_minus]

/-- **Subalgebra Closure of Causal Masked Affinity Operators**:
The product of two causal masked affinity operators has vanishing anti-causal channel and is
invariant under `causalMask`. -/
theorem causalMask_mul_closure (W₁ W₂ : Matrix (Fin 2) (Fin 2) A) :
    causalMask (causalMask W₁ * causalMask W₂) = causalMask W₁ * causalMask W₂ := by
  apply ext_fin2 <;> simp [causalMask, channelPP, channelMM, channelMP, P_plus, P_minus]

end ArchetypeB4_CausalTriangularAffinity

/-!
## Archetype $\mathcal{B}_5$: Clifford-Mellin-Walsh Spectral Decomposition & Noncommutative Attention Convolution Theorem
-/

section ArchetypeB5_CliffordMellinAttentionConvolution

variable {A : Type*} [Ring A] [StarRing A]

/-- Coordinate-free Peirce fiber lift $\mathcal{L}(X) = P_+ X P_+ + \Sigma P_+ X P_+ \Sigma$. -/
def peirceFiberLift (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * X * P_plus + Σ_op * P_plus * X * P_plus * Σ_op

/-- The four Mellin-Walsh spectral modes of an affinity or value operator $M \in M_2(A)$. -/
def mellinCoeff_I (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M + Σ_op * M * Σ_op)

def mellinCoeff_Γ (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M - Σ_op * M * Σ_op)

def mellinCoeff_Σ (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M * Σ_op + Σ_op * M)

def mellinCoeff_Ω (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (Σ_op * M - M * Σ_op)

/-- **Adjoint Duality of the Clifford-Mellin-Walsh Affinity Modes**:
The modes $\widehat{W}_I, \widehat{W}_\Gamma, \widehat{W}_\Sigma$ are $\star$-covariant, whereas
the symplectic relational flux mode $\widehat{W}_\Omega$ is $\star$-contravariant. -/
theorem mellinCoeff_I_conjTranspose (W : Matrix (Fin 2) (Fin 2) A) :
    (mellinCoeff_I W)ᴴ = mellinCoeff_I Wᴴ := by
  apply ext_fin2 <;> simp [mellinCoeff_I, peirceFiberLift, P_plus, Σ_op]

theorem mellinCoeff_Γ_conjTranspose (W : Matrix (Fin 2) (Fin 2) A) :
    (mellinCoeff_Γ W)ᴴ = mellinCoeff_Γ Wᴴ := by
  apply ext_fin2 <;> simp [mellinCoeff_Γ, peirceFiberLift, P_plus, Σ_op]

theorem mellinCoeff_Σ_conjTranspose (W : Matrix (Fin 2) (Fin 2) A) :
    (mellinCoeff_Σ W)ᴴ = mellinCoeff_Σ Wᴴ := by
  apply ext_fin2 <;> simp [mellinCoeff_Σ, peirceFiberLift, P_plus, Σ_op] <;> noncomm_ring

theorem mellinCoeff_Ω_conjTranspose (W : Matrix (Fin 2) (Fin 2) A) :
    (mellinCoeff_Ω W)ᴴ = -mellinCoeff_Ω Wᴴ := by
  apply ext_fin2 <;> simp [mellinCoeff_Ω, peirceFiberLift, P_plus, Σ_op] <;> noncomm_ring

/-- Noncommutative Clifford-Mellin convolution fiber for the Identity ($I$) channel. -/
def mellinConv_I (W V : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  mellinCoeff_I W * mellinCoeff_I V +
  mellinCoeff_Γ W * mellinCoeff_Γ V +
  mellinCoeff_Σ W * mellinCoeff_Σ V -
  mellinCoeff_Ω W * mellinCoeff_Ω V

/-- Noncommutative Clifford-Mellin convolution fiber for the Chiral Grading ($\Gamma_1$) channel. -/
def mellinConv_Γ (W V : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  mellinCoeff_I W * mellinCoeff_Γ V +
  mellinCoeff_Γ W * mellinCoeff_I V +
  mellinCoeff_Σ W * mellinCoeff_Ω V -
  mellinCoeff_Ω W * mellinCoeff_Σ V

/-- Noncommutative Clifford-Mellin convolution fiber for the Symmetric Shift ($\Sigma$) channel. -/
def mellinConv_Σ (W V : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  mellinCoeff_I W * mellinCoeff_Σ V +
  mellinCoeff_Σ W * mellinCoeff_I V -
  mellinCoeff_Γ W * mellinCoeff_Ω V +
  mellinCoeff_Ω W * mellinCoeff_Γ V

/-- Noncommutative Clifford-Mellin convolution fiber for the Symplectic Bivector ($\Omega$) channel. -/
def mellinConv_Ω (W V : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  mellinCoeff_I W * mellinCoeff_Ω V +
  mellinCoeff_Ω W * mellinCoeff_I V -
  mellinCoeff_Γ W * mellinCoeff_Σ V +
  mellinCoeff_Σ W * mellinCoeff_Γ V

/-- **The Noncommutative Clifford-Mellin-Walsh Attention Convolution Theorem**:
For any affinity matrix $W \in M_2(A)$ and value matrix $V \in M_2(A)$ over a noncommutative ring $A$,
the fourfold attention output $(2W)(2V) = 4 \mathrm{Attn}(W, V)$ is given by the spectral
convolution of their Clifford-Mellin-Walsh fiber components along $\{1, \Gamma_1, \Sigma, \Omega\}$. -/
theorem clifford_mellin_attention_convolution (W V : Matrix (Fin 2) (Fin 2) A) :
    mellinConv_I W V * 1 +
    mellinConv_Γ W V * Γ₁ +
    mellinConv_Σ W V * Σ_op +
    mellinConv_Ω W V * Ω =
      (W + W) * (V + V) := by
  apply ext_fin2 <;>
    simp [mellinConv_I, mellinConv_Γ, mellinConv_Σ, mellinConv_Ω,
      mellinCoeff_I, mellinCoeff_Γ, mellinCoeff_Σ, mellinCoeff_Ω,
      peirceFiberLift, P_plus, Γ₁, Σ_op, Ω] <;>
    noncomm_ring

end ArchetypeB5_CliffordMellinAttentionConvolution

end NoncommutativeAttentionDecomposition
```

## Turn 0009, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

open Matrix

namespace BrauerWeylGradedTensorChain

/-!
## Foundational Infrastructure: $2 \times 2$ Noncommutative Operator Matrices
-/

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section MatrixSimpLemmas

variable {A : Type*} [Ring A]

@[simp]
lemma mul_apply_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one_apply_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one_apply_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one_apply_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one_apply_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp]
lemma of_fin2_00 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl

@[simp]
lemma of_fin2_01 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl

@[simp]
lemma of_fin2_10 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl

@[simp]
lemma of_fin2_11 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

/-- Commutator $[X, Y] = X Y - Y X$ and anticommutator $\{X, Y\} = X Y + Y X$. -/
def comm {R : Type*} [Ring R] (X Y : R) : R := X * Y - Y * X
def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

end MatrixSimpLemmas

/-!
## Archetype $\mathcal{C}_1$: Bivector-Chirality Duality in $Cl(1,1) \subset M_2(A)$
-/

section ArchetypeC1_BivectorChiralityDuality

variable {A : Type*} [Ring A]

/-- Spacelike odd vector generator $\Sigma = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ ($\Sigma^2 = I$). -/
def Σ_op : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]

/-- Timelike odd vector generator $\Omega = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ ($\Omega^2 = -I$). -/
def Ω : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]

/-- Chirality / Klein grading involution $\Gamma_1 = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$. -/
def Γ₁ : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]

/-- Orthogonal Peirce idempotents $P_+$ and $P_-$. -/
def P_plus : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]

theorem Σ_op_sq : (Σ_op : Matrix (Fin 2) (Fin 2) A) * Σ_op = 1 := by
  apply ext_fin2 <;> simp [Σ_op]

theorem Ω_sq : (Ω : Matrix (Fin 2) (Fin 2) A) * Ω = -1 := by
  apply ext_fin2 <;> simp [Ω]

theorem Γ₁_sq : (Γ₁ : Matrix (Fin 2) (Fin 2) A) * Γ₁ = 1 := by
  apply ext_fin2 <;> simp [Γ₁]

/-- The chirality involution $\Gamma_1$ is the volume bivector $\Sigma \Omega$ of the odd generators $\Sigma, \Omega$. -/
theorem Σ_mul_Ω_eq_Γ₁ : (Σ_op : Matrix (Fin 2) (Fin 2) A) * Ω = Γ₁ := by
  apply ext_fin2 <;> simp [Σ_op, Ω, Γ₁]

theorem Ω_mul_Σ_eq_neg_Γ₁ : (Ω : Matrix (Fin 2) (Fin 2) A) * Σ_op = -Γ₁ := by
  apply ext_fin2 <;> simp [Σ_op, Ω, Γ₁]

theorem anticomm_Σ_Ω : anticomm (Σ_op : Matrix (Fin 2) (Fin 2) A) Ω = 0 := by
  apply ext_fin2 <;> simp [anticomm, Σ_op, Ω]

theorem anticomm_Γ₁_Σ : anticomm (Γ₁ : Matrix (Fin 2) (Fin 2) A) Σ_op = 0 := by
  apply ext_fin2 <;> simp [anticomm, Γ₁, Σ_op]

theorem anticomm_Γ₁_Ω : anticomm (Γ₁ : Matrix (Fin 2) (Fin 2) A) Ω = 0 := by
  apply ext_fin2 <;> simp [anticomm, Γ₁, Ω]

end ArchetypeC1_BivectorChiralityDuality

/-!
## Archetype $\mathcal{C}_2$: The Klein–Jordan–Wigner Twist $\mathcal{J} : A \to M_2(A)$ (Koszul Graded-to-Ungraded Bridge)
-/

section ArchetypeC2_KleinJordanWignerTwist

variable {A : Type*} [Ring A]

/-- Untwisted diagonal embedding $\iota(x) = \begin{pmatrix} x & 0 \\ 0 & x \end{pmatrix}$. -/
def fiberEmbed (x : A) : Matrix (Fin 2) (Fin 2) A := ![![x, 0], ![0, x]]

/-- **The Klein–Jordan–Wigner / Brauer–Weyl Twist** $\mathcal{J}(x) = \begin{pmatrix} x & 0 \\ 0 & -x \end{pmatrix}$. -/
def kleinTwist (x : A) : Matrix (Fin 2) (Fin 2) A := ![![x, 0], ![0, -x]]

@[simp]
theorem fiberEmbed_zero : fiberEmbed (0 : A) = 0 := by
  apply ext_fin2 <;> simp [fiberEmbed]

@[simp]
theorem fiberEmbed_one : fiberEmbed (1 : A) = 1 := by
  apply ext_fin2 <;> simp [fiberEmbed]

@[simp]
theorem fiberEmbed_neg (x : A) : fiberEmbed (-x) = -fiberEmbed x := by
  apply ext_fin2 <;> simp [fiberEmbed]

/-- $\mathcal{J}(x)$ is the untwisted diagonal embedding $\iota(x)$ multiplied by the Klein factor $\Gamma_1$. -/
theorem kleinTwist_eq_fiberEmbed_mul_Γ₁ (x : A) :
    kleinTwist x = fiberEmbed x * Γ₁ := by
  apply ext_fin2 <;> simp [kleinTwist, fiberEmbed, Γ₁]

/-- Whereas $\iota(x)$ commutes with $\Sigma$ and $\Omega$, the Klein-twisted operator $\mathcal{J}(x)$
**strictly anticommutes** with both outer $Cl(1,1)$ generators $\Sigma$ and $\Omega$. -/
theorem kleinTwist_anticomm_Σ (x : A) :
    anticomm (kleinTwist x) (Σ_op : Matrix (Fin 2) (Fin 2) A) = 0 := by
  apply ext_fin2 <;> simp [anticomm, kleinTwist, Σ_op]

theorem kleinTwist_anticomm_Ω (x : A) :
    anticomm (kleinTwist x) (Ω : Matrix (Fin 2) (Fin 2) A) = 0 := by
  apply ext_fin2 <;> simp [anticomm, kleinTwist, Ω]

/-- $\mathcal{J}(x)$ commutes with the outer chirality involution $\Gamma_1$. -/
theorem kleinTwist_comm_Γ₁ (x : A) :
    comm (kleinTwist x) (Γ₁ : Matrix (Fin 2) (Fin 2) A) = 0 := by
  apply ext_fin2 <;> simp [comm, kleinTwist, Γ₁]

/-- **Koszul Quadratic Pairing Law**: The product of two Klein-twisted operators is the untwisted
diagonal embedding of their product: $\mathcal{J}(x)\mathcal{J}(y) = \iota(x y)$. -/
theorem kleinTwist_mul_kleinTwist (x y : A) :
    kleinTwist x * kleinTwist y = fiberEmbed (x * y) := by
  apply ext_fin2 <;> simp [kleinTwist, fiberEmbed]

/-- The anticommutator of two Klein-twisted operators is the untwisted embedding of their anticommutator. -/
theorem kleinTwist_anticomm (x y : A) :
    anticomm (kleinTwist x) (kleinTwist y) = fiberEmbed (anticomm x y) := by
  apply ext_fin2 <;> simp [anticomm, kleinTwist, fiberEmbed]

end ArchetypeC2_KleinJordanWignerTwist

/-!
## Archetype $\mathcal{C}_3$: Witt Isotropic Nilpotent Ladder $(F_+, F_-)$ & Canonical Anticommutation Relations (CAR)
-/

section ArchetypeC3_WittIsotropicLadder

variable {A : Type*} [Ring A]

/-- Raising (creation) Witt isotropic operator $F_+ = P_+ \Sigma P_- = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. -/
def F_plus : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![0, 0]]

/-- Lowering (annihilation) Witt isotropic operator $F_- = P_- \Sigma P_+ = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$. -/
def F_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![1, 0]]

theorem F_plus_eq_peirce_Σ :
    (F_plus : Matrix (Fin 2) (Fin 2) A) = P_plus * Σ_op * P_minus := by
  apply ext_fin2 <;> simp [F_plus, P_plus, P_minus, Σ_op]

theorem F_minus_eq_peirce_Σ :
    (F_minus : Matrix (Fin 2) (Fin 2) A) = P_minus * Σ_op * P_plus := by
  apply ext_fin2 <;> simp [F_minus, P_plus, P_minus, Σ_op]

/-- Isotropic (nilpotent) property: $F_+^2 = 0$ and $F_-^2 = 0$. -/
theorem F_plus_sq_zero : (F_plus : Matrix (Fin 2) (Fin 2) A) * F_plus = 0 := by
  apply ext_fin2 <;> simp [F_plus]

theorem F_minus_sq_zero : (F_minus : Matrix (Fin 2) (Fin 2) A) * F_minus = 0 := by
  apply ext_fin2 <;> simp [F_minus]

/-- **Canonical Anticommutation Relation (CAR)**: $\{F_+, F_-\} = I$. -/
theorem anticomm_F_plus_F_minus :
    anticomm (F_plus : Matrix (Fin 2) (Fin 2) A) F_minus = 1 := by
  apply ext_fin2 <;> simp [anticomm, F_plus, F_minus]

/-- Commutator of the Witt ladder operators recovers the chirality grading: $[F_+, F_-] = \Gamma_1$. -/
theorem comm_F_plus_F_minus :
    comm (F_plus : Matrix (Fin 2) (Fin 2) A) F_minus = Γ₁ := by
  apply ext_fin2 <;> simp [comm, F_plus, F_minus, Γ₁]

/-- Every Klein-twisted inner operator $\mathcal{J}(x)$ strictly anticommutes with both $F_+$ and $F_-$. -/
theorem kleinTwist_anticomm_F_plus (x : A) :
    anticomm (kleinTwist x) (F_plus : Matrix (Fin 2) (Fin 2) A) = 0 := by
  apply ext_fin2 <;> simp [anticomm, kleinTwist, F_plus]

theorem kleinTwist_anticomm_F_minus (x : A) :
    anticomm (kleinTwist x) (F_minus : Matrix (Fin 2) (Fin 2) A) = 0 := by
  apply ext_fin2 <;> simp [anticomm, kleinTwist, F_minus]

end ArchetypeC3_WittIsotropicLadder

/-!
## Archetype $\mathcal{C}_4$: Brauer–Weyl / Atiyah–Bott–Shapiro $(1,1)$-Periodicity Step
-/

section ArchetypeC4_BrauerWeylPeriodicity

variable {A : Type*} [Ring A]

/-- **The Brauer–Weyl / Atiyah–Bott–Shapiro $(1,1)$-Periodicity Theorem**:
Given any anticommuting Clifford pair $(e_1, e_2)$ in a noncommutative ring $A$ with squares
$e_1^2 = s_1$ and $e_2^2 = s_2$, their Klein–Jordan–Wigner lifts $\mathcal{J}(e_1), \mathcal{J}(e_2)$
combine with the outer $Cl(1,1)$ generators $(\Sigma, \Omega)$ to form four mutually anticommuting
Clifford generators in $M_2(A)$ with squares $(1, -1, \iota(s_1), \iota(s_2))$. -/
theorem brauer_weyl_periodicity_step
    {e₁ e₂ s₁ s₂ : A}
    (he₁ : e₁ * e₁ = s₁)
    (he₂ : e₂ * e₂ = s₂)
    (h_anti : anticomm e₁ e₂ = 0) :
    (Σ_op : Matrix (Fin 2) (Fin 2) A) * Σ_op = 1 ∧
    (Ω : Matrix (Fin 2) (Fin 2) A) * Ω = -1 ∧
    kleinTwist e₁ * kleinTwist e₁ = fiberEmbed s₁ ∧
    kleinTwist e₂ * kleinTwist e₂ = fiberEmbed s₂ ∧
    anticomm (Σ_op : Matrix (Fin 2) (Fin 2) A) Ω = 0 ∧
    anticomm (kleinTwist e₁) (Σ_op : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₂) (Σ_op : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₁) (Ω : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₂) (Ω : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₁) (kleinTwist e₂) = 0 := by
   refine ⟨Σ_op_sq, Ω_sq, ?_, ?_, anticomm_Σ_Ω,
    kleinTwist_anticomm_Σ e₁, kleinTwist_anticomm_Σ e₂,
    kleinTwist_anticomm_Ω e₁, kleinTwist_anticomm_Ω e₂, ?_⟩
  · rw [kleinTwist_mul_kleinTwist, he₁]
  · rw [kleinTwist_mul_kleinTwist, he₂]
  · rw [kleinTwist_anticomm, h_anti, fiberEmbed_zero]

end ArchetypeC4_BrauerWeylPeriodicity

/-!
## Archetype $\mathcal{C}_5$: Graded Koszul-Clifford Mellin-Walsh Decomposition
-/

section ArchetypeC5_GradedKoszulMellinDecomposition

variable {A : Type*} [Ring A]

/-- Coordinate-free Klein-twisted Peirce fiber lift
$\mathcal{L}_{\mathrm{Klein}}(X) = P_+ X P_+ - \Sigma P_+ X P_+ \Sigma = \mathcal{J}(X_{00})$. -/
def kleinFiberLift (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * X * P_plus - Σ_op * P_plus * X * P_plus * Σ_op

/-- $\mathcal{L}_{\mathrm{Klein}}(X)$ is identically the Klein–Jordan–Wigner twist $\mathcal{J}(X_{00})$. -/
theorem kleinFiberLift_eq_kleinTwist (X : Matrix (Fin 2) (Fin 2) A) :
    kleinFiberLift X = kleinTwist (X 0 0) := by
  apply ext_fin2 <;> simp [kleinFiberLift, kleinTwist, P_plus, Σ_op]

/-- Every Klein-lifted fiber $\mathcal{L}_{\mathrm{Klein}}(X)$ strictly anticommutes with $\Sigma$ and $\Omega$. -/
theorem kleinFiberLift_anticomm_Σ (X : Matrix (Fin 2) (Fin 2) A) :
    anticomm (kleinFiberLift X) (Σ_op : Matrix (Fin 2) (Fin 2) A) = 0 := by
  rw [kleinFiberLift_eq_kleinTwist]
  exact kleinTwist_anticomm_Σ (X 0 0)

theorem kleinFiberLift_anticomm_Ω (X : Matrix (Fin 2) (Fin 2) A) :
    anticomm (kleinFiberLift X) (Ω : Matrix (Fin 2) (Fin 2) A) = 0 := by
  rw [kleinFiberLift_eq_kleinTwist]
  exact kleinTwist_anticomm_Ω (X 0 0)

/-- **The Graded Koszul-Clifford Mellin-Walsh Reconstruction Theorem**:
Every operator matrix $M \in M_2(A)$ is reconstructed directly in the $\mathbb{Z}_2$-graded tensor
product $Cl(1,1) \mathbin{\hat{\otimes}} A$ using the anticommuting Klein-lifted fiber coefficients. -/
theorem graded_koszul_clifford_mellin_inversion (M : Matrix (Fin 2) (Fin 2) A) :
    kleinFiberLift (M - Σ_op * M * Σ_op) * 1 +
    kleinFiberLift (M + Σ_op * M * Σ_op) * Γ₁ -
    kleinFiberLift (Σ_op * M - M * Σ_op) * Σ_op -
    kleinFiberLift (M * Σ_op + Σ_op * M) * Ω = M + M := by
  apply ext_fin2 <;>
    simp [kleinFiberLift, P_plus, Γ₁, Σ_op, Ω] <;>
    noncomm_ring

end ArchetypeC5_GradedKoszulMellinDecomposition

/-!
## Archetype $\mathcal{C}_6$: Recursive Chain $M_2(M_2(B)) \cong Cl(1,1) \mathbin{\hat{\otimes}} Cl(1,1) \otimes B \cong Cl(2,2) \otimes B$
-/

section ArchetypeC6_RecursiveCl22Chain

variable {B : Type*} [Ring B]

/-- The nested two-stage operator algebra $M_2(M_2(B)) \cong Cl(1,1) \mathbin{\hat{\otimes}} Cl(1,1) \otimes B$. -/
abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- The four Jordan–Wigner / Brauer–Weyl Majorana-Dirac generators of $Cl(2,2)$ in $M_2(M_2(B))$:
$\gamma_1 = \Sigma \otimes I$, $\gamma_2 = \Omega \otimes I$,
$\gamma_3 = \Gamma_1 \otimes \Sigma = \mathcal{J}(\Sigma)$, and $\gamma_4 = \Gamma_1 \otimes \Omega = \mathcal{J}(\Omega)$. -/
def γ₁ : NestedMat B := Σ_op
def γ₂ : NestedMat B := Ω
def γ₃ : NestedMat B := kleinTwist Σ_op
def γ₄ : NestedMat B := kleinTwist Ω

/-- **Complete $Cl(2,2)$ Graded Tensor Chain Relations over a Noncommutative Ring $B$**:
The four recursively constructed Jordan–Wigner generators $\gamma_1, \gamma_2, \gamma_3, \gamma_4 \in M_2(M_2(B))$
have signatures $(+1, -1, +1, -1)$ and mutually anticommute. -/
theorem cl22_chain_relations :
    (γ₁ : NestedMat B) * γ₁ = 1 ∧
    (γ₂ : NestedMat B) * γ₂ = -1 ∧
    (γ₃ : NestedMat B) * γ₃ = 1 ∧
    (γ₄ : NestedMat B) * γ₄ = -1 ∧
    anticomm (γ₁ : NestedMat B) γ₂ = 0 ∧
    anticomm (γ₃ : NestedMat B) γ₁ = 0 ∧
    anticomm (γ₄ : NestedMat B) γ₁ = 0 ∧
    anticomm (γ₃ : NestedMat B) γ₂ = 0 ∧
    anticomm (γ₄ : NestedMat B) γ₂ = 0 ∧
    anticomm (γ₃ : NestedMat B) γ₄ = 0 := by
  have h := brauer_weyl_periodicity_step
    (A := Matrix (Fin 2) (Fin 2) B) Σ_op_sq Ω_sq anticomm_Σ_Ω
  simpa [γ₁, γ₂, γ₃, γ₄, fiberEmbed_one, fiberEmbed_neg] using h

end ArchetypeC6_RecursiveCl22Chain

end BrauerWeylGradedTensorChain
```

## Turn 0012, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace FreedGeometricIndexAndAnomalies

/-!
## Foundational Infrastructure: $2 \times 2$ Noncommutative Operator Matrices
-/

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section MatrixSimpLemmas

variable {A : Type*} [Ring A]

@[simp]
lemma mul_apply_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one_apply_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one_apply_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one_apply_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one_apply_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp]
lemma of_fin2_00 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl

@[simp]
lemma of_fin2_01 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl

@[simp]
lemma of_fin2_10 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl

@[simp]
lemma of_fin2_11 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

@[simp]
lemma conjTranspose_apply_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 0 = star (M 0 0) := rfl

@[simp]
lemma conjTranspose_apply_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 1 = star (M 1 0) := rfl

@[simp]
lemma conjTranspose_apply_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 0 = star (M 0 1) := rfl

@[simp]
lemma conjTranspose_apply_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 1 = star (M 1 1) := rfl

/-- Commutator $[X, Y] = X Y - Y X$ and anticommutator $\{X, Y\} = X Y + Y X$. -/
def comm {R : Type*} [Ring R] (X Y : R) : R := X * Y - Y * X
def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

/-- Fundamental $Cl(1,1)$ and Peirce operators in $M_2(A)$. -/
def Γ₁ : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]
def Σ_op : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]
def Ω : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]
def P_plus : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]

def dewittEven (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * M * P_plus + P_minus * M * P_minus

def dewittOdd (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * M * P_minus + P_minus * M * P_plus

end MatrixSimpLemmas

/-!
## Archetype $\mathcal{D}_1$: Projective Operator Lifts, Non-Abelian Anomaly 2-Cocycles, Green–Schwarz Cancellation & 't Hooft Matching
-/

section ArchetypeD1_ProjectiveAnomalies

variable {A : Type*} [Ring A]

/-- Linear operator lift $W(a, b) = \begin{pmatrix} 1 & a \\ b & 1 \end{pmatrix}$ of a pair of
noncommutative odd parameters $(a, b) \in A \times A$. -/
def W_lift (a b : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![1, a], ![b, 1]]

/-- The non-Abelian diagonal anomaly 2-cocycle
$\mathcal{C}(a_1, b_1, a_2, b_2) = \begin{pmatrix} a_1 b_2 & 0 \\ 0 & b_1 a_2 \end{pmatrix}$. -/
def anomalyCocycle (a₁ b₁ a₂ b₂ : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![a₁ * b₂, 0], ![0, b₁ * a₂]]

/-- **Projective Linearization Anomaly**:
Composing two linear operator lifts $W(a_1, b_1)$ and $W(a_2, b_2)$ deviates from the additive lift
$W(a_1 + a_2, b_1 + b_2)$ by the even diagonal anomaly cocycle $\mathcal{C}(a_1, b_1, a_2, b_2)$. -/
theorem projective_multiplication_anomaly (a₁ b₁ a₂ b₂ : A) :
    W_lift a₁ b₁ * W_lift a₂ b₂ =
      W_lift (a₁ + a₂) (b₁ + b₂) + anomalyCocycle a₁ b₁ a₂ b₂ := by
  apply ext_fin2 <;> simp [W_lift, anomalyCocycle]

/-- **Hochschild 2-Cocycle Condition for the Non-Abelian Anomaly**:
$\mathcal{C}(a_1, b_1, a_2, b_2) + \mathcal{C}(a_1 + a_2, b_1 + b_2, a_3, b_3) =
\mathcal{C}(a_1, b_1, a_2 + a_3, b_2 + b_3) + \mathcal{C}(a_2, b_2, a_3, b_3)$. -/
theorem anomaly_two_cocycle_condition (a₁ b₁ a₂ b₂ a₃ b₃ : A) :
    anomalyCocycle a₁ b₁ a₂ b₂ + anomalyCocycle (a₁ + a₂) (b₁ + b₂) a₃ b₃ =
      anomalyCocycle a₁ b₁ (a₂ + a₃) (b₂ + b₃) + anomalyCocycle a₂ b₂ a₃ b₃ := by
  apply ext_fin2 <;> simp [anomalyCocycle] <;> noncomm_ring

/-- Green–Schwarz counterterm-extended operator lift
$\widetilde{W}(a, b, c_+, c_-) = \begin{pmatrix} 1 + c_+ & a \\ b & 1 + c_- \end{pmatrix}$. -/
def greenSchwarzLift (a b c_plus c_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![1 + c_plus, a], ![b, 1 + c_minus]]

/-- **Green–Schwarz Anomaly Cancellation Mechanism**:
Coupling the product $W(a_1, b_1) W(a_2, b_2)$ to the compensating counterterm
$(c_+, c_-) = (-a_1 b_2, -b_1 a_2)$ cancels the anomaly cocycle and restores exact linearity. -/
theorem green_schwarz_anomaly_cancellation (a₁ b₁ a₂ b₂ : A) :
    W_lift a₁ b₁ * W_lift a₂ b₂ + (greenSchwarzLift 0 0 (-a₁ * b₂) (-b₁ * a₂) - 1) =
      W_lift (a₁ + a₂) (b₁ + b₂) := by
  apply ext_fin2 <;> simp [W_lift, greenSchwarzLift]

/-- Hyperbolic Mellin renormalization-group dilation $D(u) = \begin{pmatrix} u & 0 \\ 0 & u^{-1} \end{pmatrix}$. -/
def mellinDilation (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  ![![(u : A), 0], ![0, (↑u⁻¹ : A)]]

/-- Covariance of the operator lift $W(a, b)$ under Mellin renormalization scaling. -/
theorem W_lift_mellin_scaling (a b : A) (u : Aˣ) :
    mellinDilation u * W_lift a b * mellinDilation u⁻¹ =
      W_lift ((u : A) * a * (u : A)) ((↑u⁻¹ : A) * b * (↑u⁻¹ : A)) := by
  have h1 : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  have h2 : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  apply ext_fin2 <;> simp [mellinDilation, W_lift, h1, h2] <;> noncomm_ring

/-- **'t Hooft Anomaly Matching across Mellin Renormalization Scales**:
The non-Abelian anomaly cocycle of the rescaled theory matches the conjugated anomaly cocycle of
the original theory for any invertible operator scale $u \in A^\times$. -/
theorem thooft_anomaly_matching (a₁ b₁ a₂ b₂ : A) (u : Aˣ) :
    anomalyCocycle
      ((u : A) * a₁ * (u : A)) ((↑u⁻¹ : A) * b₁ * (↑u⁻¹ : A))
      ((u : A) * a₂ * (u : A)) ((↑u⁻¹ : A) * b₂ * (↑u⁻¹ : A)) =
      mellinDilation u * anomalyCocycle a₁ b₁ a₂ b₂ * mellinDilation u⁻¹ := by
  have h1 : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  have h2 : (↑u⁻¹ : A) * (u : A) = 1 := Units.inv_mul u
  apply ext_fin2
  · simp [anomalyCocycle, mellinDilation]
    calc (u : A) * a₁ * (u : A) * ((↑u⁻¹ : A) * b₂ * (↑u⁻¹ : A))
      _ = (u : A) * a₁ * ((u : A) * (↑u⁻¹ : A)) * b₂ * (↑u⁻¹ : A) := by noncomm_ring
      _ = (u : A) * (a₁ * b₂) * (↑u⁻¹ : A) := by rw [h1]; noncomm_ring
  · simp [anomalyCocycle, mellinDilation]
  · simp [anomalyCocycle, mellinDilation]
  · simp [anomalyCocycle, mellinDilation]
    calc (↑u⁻¹ : A) * b₁ * (↑u⁻¹ : A) * ((u : A) * a₂ * (u : A))
      _ = (↑u⁻¹ : A) * b₁ * ((↑u⁻¹ : A) * (u : A)) * a₂ * (u : A) := by noncomm_ring
      _ = (↑u⁻¹ : A) * (b₁ * a₂) * (u : A) := by rw [h2]; noncomm_ring

end ArchetypeD1_ProjectiveAnomalies

/-!
## Archetype $\mathcal{D}_2$: $\mathbb{Z}_2$-Graded Supertrace & Atiyah–Singer Jumping Kernel Invariance
-/

section ArchetypeD2_AtiyahSingerSupertrace

variable {A : Type*} [Ring A]

/-- Operator trace $\mathrm{Tr}(M) = M_{00} + M_{11} \in A$. -/
def opTrace (M : Matrix (Fin 2) (Fin 2) A) : A :=
  M 0 0 + M 1 1

/-- $\mathbb{Z}_2$-graded operator supertrace $\mathrm{Str}(M) = M_{00} - M_{11} \in A$. -/
def superTrace (M : Matrix (Fin 2) (Fin 2) A) : A :=
  M 0 0 - M 1 1

/-- The supertrace is identically the operator trace weighted by the chirality grading $\Gamma_1$. -/
theorem superTrace_eq_opTrace_mul_Γ₁ (M : Matrix (Fin 2) (Fin 2) A) :
    superTrace M = opTrace (Γ₁ * M) := by
  dsimp [superTrace, opTrace, Γ₁]
  simp [sub_eq_add_neg]

/-- Every odd operator in $M_2(A)$ has vanishing supertrace. -/
theorem superTrace_dewittOdd_zero (M : Matrix (Fin 2) (Fin 2) A) :
    superTrace (dewittOdd M) = 0 := by
  dsimp [superTrace, dewittOdd, P_plus, P_minus]
  simp

/-- A family of chiral spectral operators $K(\Pi_+, \Pi_-, \delta) = \begin{pmatrix} \Pi_+ + \delta & 0 \\ 0 & \Pi_- + \delta \end{pmatrix}$
whose kernel $\Pi_+$ and cokernel $\Pi_-$ jump simultaneously by an operator mode $\delta \in A$. -/
def jumpingKernelFamily (Π_plus Π_minus δ : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![Π_plus + δ, 0], ![0, Π_minus + δ]]

/-- While the ungraded trace jumps by $2\delta$ as $\delta$ varies... -/
theorem opTrace_jumpingKernelFamily (Π_plus Π_minus δ : A) :
    opTrace (jumpingKernelFamily Π_plus Π_minus δ) =
      opTrace (jumpingKernelFamily Π_plus Π_minus 0) + (δ + δ) := by
  dsimp [opTrace, jumpingKernelFamily]
  noncomm_ring

/-- **Atiyah–Singer Supertrace Index Invariance**:
The $\mathbb{Z}_2$-graded supertrace $\mathrm{Str}(K(\Pi_+, \Pi_-, \delta))$ is strictly invariant
under arbitrary spectral jumps $\delta \in A$ of the kernel and cokernel. -/
theorem superTrace_jumpingKernelFamily_invariant (Π_plus Π_minus δ : A) :
    superTrace (jumpingKernelFamily Π_plus Π_minus δ) =
      superTrace (jumpingKernelFamily Π_plus Π_minus 0) := by
  dsimp [superTrace, jumpingKernelFamily]
  noncomm_ring

end ArchetypeD2_AtiyahSingerSupertrace

/-!
## Archetype $\mathcal{D}_3$: Quillen–Bismut–Freed Superconnections & Noncommutative Chern–Simons–Weil Transgression
-/

section ArchetypeD3_QuillenSuperconnectionAndChernSimons

variable {A : Type*} [Ring A]

/-- Even block-diagonal gauge connection $A_{\mathrm{even}}(A_+, A_-) = \begin{pmatrix} A_+ & 0 \\ 0 & A_- \end{pmatrix}$. -/
def evenConn (A_plus A_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![A_plus, 0], ![0, A_minus]]

/-- Odd off-diagonal Dirac operator $D_{\mathrm{odd}}(L_+, L_-) = \begin{pmatrix} 0 & L_- \\ L_+ & 0 \end{pmatrix}$. -/
def oddDirac (L_plus L_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![0, L_minus], ![L_plus, 0]]

/-- **Quillen–Bismut–Freed Superconnection**
$\mathbb{A}(A_+, A_-, L_+, L_-) = A_{\mathrm{even}} + D_{\mathrm{odd}} = \begin{pmatrix} A_+ & L_- \\ L_+ & A_- \end{pmatrix}$. -/
def quillenSuperconn (A_plus A_minus L_plus L_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  evenConn A_plus A_minus + oddDirac L_plus L_minus

/-- **Quillen Supercurvature Even Sector**:
The even DeWitt part of $\mathbb{A}^2$ combines the gauge squares $A_\pm^2$ with the Dirac
Laplacians $L_\mp L_\pm$. -/
theorem quillen_supercurvature_even (A_plus A_minus L_plus L_minus : A) :
    dewittEven (quillenSuperconn A_plus A_minus L_plus L_minus *
                quillenSuperconn A_plus A_minus L_plus L_minus) =
      ![![A_plus * A_plus + L_minus * L_plus, 0],
        ![0, A_minus * A_minus + L_plus * L_minus]] := by
  apply ext_fin2 <;>
    simp [dewittEven, quillenSuperconn, evenConn, oddDirac, P_plus, P_minus] <;>
    noncomm_ring

/-- **Quillen Supercurvature Odd Sector**:
The odd DeWitt part of $\mathbb{A}^2$ is the anticommutator $\{A_{\mathrm{even}}, D_{\mathrm{odd}}\}$. -/
theorem quillen_supercurvature_odd (A_plus A_minus L_plus L_minus : A) :
    dewittOdd (quillenSuperconn A_plus A_minus L_plus L_minus *
               quillenSuperconn A_plus A_minus L_plus L_minus) =
      anticomm (evenConn A_plus A_minus) (oddDirac L_plus L_minus) := by
  apply ext_fin2 <;>
    simp [dewittOdd, anticomm, quillenSuperconn, evenConn, oddDirac, P_plus, P_minus] <;>
    noncomm_ring

/-- **Algebraic Bianchi Identity for Quillen Superconnections**: $[\mathbb{A}, \mathbb{A}^2] = 0$. -/
theorem quillen_superconnection_bianchi (𝕏 : Matrix (Fin 2) (Fin 2) A) :
    comm 𝕏 (𝕏 * 𝕏) = 0 := by
  dsimp [comm]
  noncomm_ring

/-- Bianchi covariant derivative $\nabla_D(\Phi) = [D, \Phi]$ in any noncommutative ring $R$. -/
def bianchiDeriv {R : Type*} [Ring R] (D Φ : R) : R := comm D Φ

/-- Total supercurvature $F(\Phi, D) = \Phi + D^2$ of an even background $\Phi$ and odd connection $D$. -/
def superCurvature {R : Type*} [Ring R] (Φ D : R) : R := Φ + D * D

/-- Noncommutative Chern–Simons cubic element $\mathcal{CS}(\Phi, D) = \Phi D + D \Phi + D^3$. -/
def chernSimonsElem {R : Type*} [Ring R] (Φ D : R) : R :=
  Φ * D + D * Φ + D * D * D

/-- **The Noncommutative Chern–Simons–Weil Transgression Theorem**:
In any noncommutative ring $R$ (such as $M_2(A)$), the anticommutator $\{D, \mathcal{CS}(\Phi, D)\}$
transgresses the quadratic Chern–Weil curvature $2 F(\Phi, D)^2$ modulo the Bianchi commutator
$[\nabla_D(\Phi), D]$ and $2\Phi^2$. -/
theorem chern_simons_weil_transgression {R : Type*} [Ring R] (Φ D : R) :
    anticomm D (chernSimonsElem Φ D) - comm (bianchiDeriv D Φ) D + 2 * (Φ * Φ) =
      2 * (superCurvature Φ D * superCurvature Φ D) := by
  dsimp [anticomm, comm, bianchiDeriv, chernSimonsElem, superCurvature]
  noncomm_ring

end ArchetypeD3_QuillenSuperconnectionAndChernSimons

/-!
## Archetype $\mathcal{D}_4$: Non-Invertible Categorical Symmetry Algebras & Kramers–Wannier / Peirce Defects
-/

section ArchetypeD4_NonInvertibleSymmetries

variable {A : Type*} [Ring A]

/-- Chiral Hamiltonian $H_{\mathrm{chiral}}(h_+, h_-) = \begin{pmatrix} h_+ & 0 \\ 0 & h_- \end{pmatrix}$. -/
def chiralHamiltonian (h_plus h_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![h_plus, 0], ![0, h_minus]]

/-- The non-invertible Peirce defect projectors $P_+$ and $P_-$ ($P_+ P_- = 0$) commute with any
chiral Hamiltonian $H_{\mathrm{chiral}}(h_+, h_-)$. -/
theorem P_plus_comm_chiralHamiltonian (h_plus h_minus : A) :
    comm (P_plus : Matrix (Fin 2) (Fin 2) A) (chiralHamiltonian h_plus h_minus) = 0 := by
  apply ext_fin2 <;> simp [comm, P_plus, chiralHamiltonian]

theorem P_minus_comm_chiralHamiltonian (h_plus h_minus : A) :
    comm (P_minus : Matrix (Fin 2) (Fin 2) A) (chiralHamiltonian h_plus h_minus) = 0 := by
  apply ext_fin2 <;> simp [comm, P_minus, chiralHamiltonian]

/-- Translation-symmetric Hamiltonian $H_{\mathrm{sym}}(h_0, h_1) = \begin{pmatrix} h_0 & h_1 \\ h_1 & h_0 \end{pmatrix}$. -/
def symHamiltonian (h₀ h₁ : A) : Matrix (Fin 2) (Fin 2) A :=
  ![![h₀, h₁], ![h₁, h₀]]

/-- Symmetric Kramers–Wannier / Walsh defect projector $\Pi_{\mathrm{sym}} = 1 + \Sigma = \begin{pmatrix} 1 & 1 \\ 1 & 1 \end{pmatrix}$. -/
def defectSym : Matrix (Fin 2) (Fin 2) A := ![![1, 1], ![1, 1]]

/-- Antisymmetric Kramers–Wannier / Walsh defect projector $\Pi_{\mathrm{anti}} = 1 - \Sigma = \begin{pmatrix} 1 & -1 \\ -1 & 1 \end{pmatrix}$. -/
def defectAnti : Matrix (Fin 2) (Fin 2) A := ![![1, -1], ![-1, 1]]

/-- Strict non-invertibility (mutual annihilation) of the Kramers–Wannier defect operators:
$\Pi_{\mathrm{sym}} \Pi_{\mathrm{anti}} = 0$ and $\Pi_{\mathrm{anti}} \Pi_{\mathrm{sym}} = 0$. -/
theorem defectSym_mul_defectAnti_zero :
    (defectSym : Matrix (Fin 2) (Fin 2) A) * defectAnti = 0 := by
  apply ext_fin2 <;> simp [defectSym, defectAnti]

theorem defectAnti_mul_defectSym_zero :
    (defectAnti : Matrix (Fin 2) (Fin 2) A) * defectSym = 0 := by
  apply ext_fin2 <;> simp [defectSym, defectAnti]

/-- Scaled idempotence (fusion rules) of the Kramers–Wannier defects: $\Pi_{\mathrm{sym}}^2 = 2\Pi_{\mathrm{sym}}$. -/
theorem defectSym_fusion :
    (defectSym : Matrix (Fin 2) (Fin 2) A) * defectSym = defectSym + defectSym := by
  apply ext_fin2 <;> simp [defectSym]

theorem defectAnti_fusion :
    (defectAnti : Matrix (Fin 2) (Fin 2) A) * defectAnti = defectAnti + defectAnti := by
  apply ext_fin2 <;> simp [defectAnti] <;> noncomm_ring

/-- **Non-Invertible Defect Symmetry Commutation**:
Both non-invertible Kramers–Wannier defect operators $\Pi_{\mathrm{sym}}$ and $\Pi_{\mathrm{anti}}$
strictly commute with $H_{\mathrm{sym}}(h_0, h_1)$ for arbitrary non-commuting $h_0, h_1 \in A$. -/
theorem defectSym_comm_symHamiltonian (h₀ h₁ : A) :
    comm (defectSym : Matrix (Fin 2) (Fin 2) A) (symHamiltonian h₀ h₁) = 0 := by
  apply ext_fin2 <;> simp [comm, defectSym, symHamiltonian] <;> noncomm_ring

theorem defectAnti_comm_symHamiltonian (h₀ h₁ : A) :
    comm (defectAnti : Matrix (Fin 2) (Fin 2) A) (symHamiltonian h₀ h₁) = 0 := by
  apply ext_fin2 <;> simp [comm, defectAnti, symHamiltonian] <;> noncomm_ring

end ArchetypeD4_NonInvertibleSymmetries

/-!
## Archetype $\mathcal{D}_5$: Graeme Segal's Cobordism Gluing Factorization & Wick-Rotated Reflection Positivity
-/

section ArchetypeD5_SegalGluingAndReflectionPositivity

variable {A : Type*} [Ring A] [StarRing A]

/-- **Segal Cut-and-Paste Locality Resolution**:
The composition $Z_1 Z_2$ of two bordism operators factors as the sum over the orthogonal
Peirce boundary channels $P_+$ and $P_-$. -/
theorem segal_gluing_peirce_resolution (Z₁ Z₂ : Matrix (Fin 2) (Fin 2) A) :
    Z₁ * P_plus * Z₂ + Z₁ * P_minus * Z₂ = Z₁ * Z₂ := by
  apply ext_fin2 <;> simp [P_plus, P_minus]

/-- Gluing a bordism operator $Z$ to its orientation-reversed adjoint $Z^\dagger$ across the
positive or negative Peirce boundary channel. -/
def reflectionChannelPlus (Z : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Z * P_plus * Zᴴ

def reflectionChannelMinus (Z : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Z * P_minus * Zᴴ

theorem P_plus_conjTranspose : (P_plus : Matrix (Fin 2) (Fin 2) A)ᴴ = P_plus := by
  apply ext_fin2 <;> simp [P_plus]

theorem P_minus_conjTranspose : (P_minus : Matrix (Fin 2) (Fin 2) A)ᴴ = P_minus := by
  apply ext_fin2 <;> simp [P_minus]

/-- **Extended Reflection Positivity (Channel-Wise Self-Adjointness)**:
Each cut-glued Peirce boundary channel $Z P_\pm Z^\dagger$ is individually self-adjoint, and their
sum reconstructs the reflection-positive double $Z Z^\dagger$. -/
theorem reflectionChannelPlus_isSelfAdjoint (Z : Matrix (Fin 2) (Fin 2) A) :
    (reflectionChannelPlus Z)ᴴ = reflectionChannelPlus Z := by
  dsimp [reflectionChannelPlus]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    P_plus_conjTranspose, mul_assoc]

theorem reflectionChannelMinus_isSelfAdjoint (Z : Matrix (Fin 2) (Fin 2) A) :
    (reflectionChannelMinus Z)ᴴ = reflectionChannelMinus Z := by
  dsimp [reflectionChannelMinus]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    P_minus_conjTranspose, mul_assoc]

theorem reflection_positivity_double_decomposition (Z : Matrix (Fin 2) (Fin 2) A) :
    reflectionChannelPlus Z + reflectionChannelMinus Z = Z * Zᴴ := by
  exact segal_gluing_peirce_resolution Z Zᴴ

end ArchetypeD5_SegalGluingAndReflectionPositivity

end FreedGeometricIndexAndAnomalies
```

## Turn 0015, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

open Matrix

namespace NoncommutativeGaugeAndBraidedHolonomy

/-!
## Archetype $\mathcal{M}_1$: Non-Central Associative Envelope, Lie Commutator & Second-Order BCH Jet Obstruction
-/

section ArchetypeM1_AssociativeLieAndBCH

variable {B : Type*} [Ring B]

/-- The scaled second-order exponential jet $J_2(X) = 2 + 2X + X^2$ in a noncommutative ring $B$. -/
def expJet2 (X : B) : B := 2 + 2 * X + X * X

/-- **Second-Order Baker–Campbell–Hausdorff (BCH) Jet Commutator Identity**:
The commutator of two second-order exponential jets isolates the Lie bracket $4\⁅X, Y⁆$ alongside
the cubic and quartic nilpotent remainders. -/
theorem bch_jet2_commutator_obstruction (X Y : B) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X =
      4 * ⁅X, Y⁆ +
      2 * (X * X * Y - Y * (X * X) + X * (Y * Y) - Y * Y * X) +
      (X * X * (Y * Y) - Y * Y * (X * X)) := by
  dsimp [expJet2]
  rw [Ring.lie_def]
  noncomm_ring

/-- For nilpotent elements of index $2$ ($X^2 = 0, Y^2 = 0$), the second-order exponential jet
commutator is purely proportional to the Lie bracket $4\⁅X, Y⁆$. -/
theorem bch_jet2_nilpotent_commutator {X Y : B} (hX : X * X = 0) (hY : Y * Y = 0) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X = 4 * ⁅X, Y⁆ := by
  rw [bch_jet2_commutator_obstruction, hX, hY]
  noncomm_ring

end ArchetypeM1_AssociativeLieAndBCH

/-!
## Archetype $\mathcal{M}_2$: Noncommutative Ring Derivations, Matrix Lifting & Inverse Gauge Differentiation
-/

section ArchetypeM2_NoncommutativeDerivations

/-- Predicate for an additive homomorphism $d : B \to+ B$ on a noncommutative ring $B$ to be a
Leibniz ring derivation. -/
def IsRingDeriv {B : Type*} [Ring B] (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

/-- Every noncommutative ring derivation annihilates the multiplicative identity $1$. -/
theorem IsRingDeriv.map_one {B : Type*} [Ring B] {d : B →+ B} (hd : IsRingDeriv d) :
    d 1 = 0 := by
  have h : d (1 * 1) = d 1 * 1 + 1 * d 1 := hd 1 1
  simp only [mul_one, one_mul] at h
  calc d 1 = d 1 + d 1 - d 1 := by abel
    _ = d 1 - d 1 := by rw [← h]
    _ = 0 := sub_self (d 1)

/-- **Noncommutative Inverse Derivative Formula**:
For any derivation $d$ on a noncommutative ring $B$ and any invertible element $u \in B^\times$,
$d(u^{-1}) = -u^{-1} d(u) u^{-1}$. -/
theorem IsRingDeriv.map_units_inv {B : Type*} [Ring B] {d : B →+ B}
    (hd : IsRingDeriv d) (u : Bˣ) :
    d (↑u⁻¹ : B) = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by
  have h1 : d ((u : B) * (↑u⁻¹ : B)) = d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B) :=
    hd (u : B) (↑u⁻¹ : B)
  rw [Units.mul_inv, hd.map_one] at h1
  have h2 : (↑u⁻¹ : B) * (d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑u⁻¹ : B) * (u : B) * d (↑u⁻¹ : B) = d (↑u⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc d (↑u⁻¹ : B)
    _ = (↑u⁻¹ : B) * (u : B) * d (↑u⁻¹ : B) -
        (↑u⁻¹ : B) * (d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by noncomm_ring

/-- Entrywise lifting of an additive map $d : S \to+ S$ to $n \times n$ matrices $M_n(S)$. -/
def liftMatrixDeriv {S : Type*} [Ring S] {n : Type*} [Fintype n] [DecidableEq n]
    (d : S →+ S) : Matrix n n S →+ Matrix n n S where
  toFun M i j := d (M i j)
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; simp

/-- **Matrix Derivation Lifting Theorem**:
If $d : S \to+ S$ is a derivation on a ring $S$, its entrywise lift to $M_n(S)$ is a derivation
on the noncommutative matrix ring $M_n(S)$. -/
theorem IsRingDeriv.liftMatrix {S : Type*} [Ring S] {n : Type*} [Fintype n] [DecidableEq n]
    {d : S →+ S} (hd : IsRingDeriv d) :
    IsRingDeriv (liftMatrixDeriv (n := n) d) := by
  intro M N
  ext i k
  simp only [liftMatrixDeriv, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply,
    Matrix.mul_apply, map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact hd (M i j) (N j k)

end ArchetypeM2_NoncommutativeDerivations

/-!
## Archetype $\mathcal{M}_3$: Covariant Derivations, Non-Linear Curvature, Gauge Intertwining, Maurer–Cartan Flatness & Bianchi Identity
-/

section ArchetypeM3_NonAbelianGaugeCurvature

variable {B : Type*} [Ring B]

/-- Left covariant derivative operator $\nabla_{d, A}(\psi) = d(\psi) + A \psi$. -/
def covDeriv (d : B →+ B) (A ψ : B) : B :=
  d ψ + A * ψ

/-- Non-Abelian Yang–Mills curvature element $F(d_1, d_2, A_1, A_2) = d_1(A_2) - d_2(A_1) + \⁅A_1, A_2⁆$. -/
def curvature (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B :=
  d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆

/-- **Fundamental Curvature Multiplication Theorem**:
The commutator of two covariant derivations is a pure left-multiplication operator by the
non-Abelian curvature $F_{12}$. -/
theorem covariant_curvature_multiplication
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (A₁ A₂ ψ : B) :
    covDeriv d₁ A₁ (covDeriv d₂ A₂ ψ) - covDeriv d₂ A₂ (covDeriv d₁ A₁ ψ) =
      curvature d₁ d₂ A₁ A₂ * ψ := by
  dsimp [covDeriv, curvature]
  rw [Ring.lie_def, map_add, map_add, hd₁ A₂ ψ, hd₂ A₁ ψ, h_comm ψ]
  noncomm_ring

/-- Affine gauge transformation of a connection: $A^u = u A u^{-1} - d(u) u^{-1}$. -/
def gaugeTransformConn (d : B →+ B) (u : Bˣ) (A : B) : B :=
  (u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)

/-- **Covariant Gauge Intertwining Theorem**:
For any unit $u \in B^\times$, $\nabla_{d, A^u}(u \psi) = u \nabla_{d, A}(\psi)$. -/
theorem covariant_gauge_intertwining
    {d : B →+ B} (hd : IsRingDeriv d) (u : Bˣ) (A ψ : B) :
    covDeriv d (gaugeTransformConn d u A) ((u : B) * ψ) =
      (u : B) * covDeriv d A ψ := by
  dsimp [covDeriv, gaugeTransformConn]
  rw [hd (u : B) ψ]
  have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  calc d (u : B) * ψ + (u : B) * d ψ +
        ((u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)) * ((u : B) * ψ)
    _ = d (u : B) * ψ + (u : B) * d ψ +
        (u : B) * A * ((↑u⁻¹ : B) * (u : B)) * ψ -
        d (u : B) * ((↑u⁻¹ : B) * (u : B)) * ψ := by noncomm_ring
    _ = d (u : B) * ψ + (u : B) * d ψ +
        (u : B) * A * 1 * ψ - d (u : B) * 1 * ψ := by rw [hu]
    _ = (u : B) * (d ψ + A * ψ) := by noncomm_ring

/-- **Homogeneous Adjoint Gauge Covariance of the Non-Abelian Curvature**:
Under an affine gauge transformation $A_i \mapsto A_i^u$, the curvature transforms homogeneously
by conjugation: $F_{12}(A_1^u, A_2^u) = u F_{12}(A_1, A_2) u^{-1}$. -/
theorem curvature_gauge_covariance
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) (A₁ A₂ : B) :
    curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) =
      (u : B) * curvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by
  have h_lhs := covariant_curvature_multiplication hd₁ hd₂ h_comm
    (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) ((u : B) * 1)
  rw [covariant_gauge_intertwining hd₂ u A₂ 1,
      covariant_gauge_intertwining hd₁ u A₁ (covDeriv d₂ A₂ 1),
      covariant_gauge_intertwining hd₁ u A₁ 1,
      covariant_gauge_intertwining hd₂ u A₂ (covDeriv d₁ A₁ 1)] at h_lhs
  have h_rhs := covariant_curvature_multiplication hd₁ hd₂ h_comm A₁ A₂ 1
  have h_comb : curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) * (u : B) =
      (u : B) * curvature d₁ d₂ A₁ A₂ := by
    calc curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) * (u : B)
      _ = curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) * ((u : B) * 1) := by
          rw [mul_one]
      _ = (u : B) * covDeriv d₁ A₁ (covDeriv d₂ A₂ 1) -
          (u : B) * covDeriv d₂ A₂ (covDeriv d₁ A₁ 1) := h_lhs.symm
      _ = (u : B) * (covDeriv d₁ A₁ (covDeriv d₂ A₂ 1) - covDeriv d₂ A₂ (covDeriv d₁ A₁ 1)) := by
          noncomm_ring
      _ = (u : B) * (curvature d₁ d₂ A₁ A₂ * 1) := by rw [h_rhs]
      _ = (u : B) * curvature d₁ d₂ A₁ A₂ := by rw [mul_one]
  calc curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂)
    _ = curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) *
        ((u : B) * (↑u⁻¹ : B)) := by rw [Units.mul_inv, mul_one]
    _ = (curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) * (u : B)) *
        (↑u⁻¹ : B) := by noncomm_ring
    _ = (u : B) * curvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by rw [h_comb]

/-- **Maurer–Cartan Flatness Theorem**:
Every pure gauge Maurer–Cartan connection $A_i = -d_i(u) u^{-1}$ has identically zero curvature. -/
theorem maurer_cartan_flatness
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) :
    curvature d₁ d₂ (-d₁ (u : B) * (↑u⁻¹ : B)) (-d₂ (u : B) * (↑u⁻¹ : B)) = 0 := by
  have h1 : -d₁ (u : B) * (↑u⁻¹ : B) = gaugeTransformConn d₁ u 0 := by
    dsimp [gaugeTransformConn]; noncomm_ring
  have h2 : -d₂ (u : B) * (↑u⁻¹ : B) = gaugeTransformConn d₂ u 0 := by
    dsimp [gaugeTransformConn]; noncomm_ring
  rw [h1, h2, curvature_gauge_covariance hd₁ hd₂ h_comm u 0 0]
  dsimp [curvature]
  rw [Ring.lie_def, map_zero, map_zero]
  noncomm_ring

/-- Adjoint covariant derivative $D_{d, A}(X) = d(X) + \⁅A, X⁆$ acting on Lie-algebra/adjoint elements. -/
def adjointCovDeriv (d : B →+ B) (A X : B) : B :=
  d X + ⁅A, X⁆

/-- **The Differential Non-Abelian Bianchi Identity**:
For any three pairwise commuting derivations $d_1, d_2, d_3$ and connections $A_1, A_2, A_3 \in B$,
the cyclic sum of adjoint covariant derivatives of the curvatures vanishes identically:
$D_1(F_{23}) + D_2(F_{31}) + D_3(F_{12}) = 0$. -/
theorem differential_nonabelian_bianchi_identity
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    adjointCovDeriv d₁ A₁ (curvature d₂ d₃ A₂ A₃) +
    adjointCovDeriv d₂ A₂ (curvature d₃ d₁ A₃ A₁) +
    adjointCovDeriv d₃ A₃ (curvature d₁ d₂ A₁ A₂) = 0 := by
  dsimp [adjointCovDeriv, curvature]
  simp only [Ring.lie_def, map_add, map_sub]
  rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
      h12 A₃, h13 A₂, h23 A₁, ← h12 A₃, ← h13 A₂, ← h23 A₁]
  noncomm_ring

/-- **Failure of the Naive Abelian Exterior Closure Law**:
The ordinary un-covariantized derivative sum $d_1(F_{23}) + d_2(F_{31}) + d_3(F_{12})$ equals the
non-linear commutator self-coupling $\⁅F_{23}, A_1⁆ + \⁅F_{31}, A_2⁆ + \⁅F_{12}, A_3⁆$. -/
theorem abelian_bianchi_obstruction
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    d₁ (curvature d₂ d₃ A₂ A₃) + d₂ (curvature d₃ d₁ A₃ A₁) + d₃ (curvature d₁ d₂ A₁ A₂) =
      ⁅curvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅curvature d₃ d₁ A₃ A₁, A₂⁆ + ⁅curvature d₁ d₂ A₁ A₂, A₃⁆ := by
  have h := differential_nonabelian_bianchi_identity hd₁ hd₂ hd₃ h12 h23 h13 A₁ A₂ A₃
  dsimp [adjointCovDeriv] at h
  simp only [Ring.lie_def] at h ⊢
  linear_combination h

end ArchetypeM3_NonAbelianGaugeCurvature

/-!
## Archetype $\mathcal{M}_4$: Non-Abelian Weyl–Heisenberg Braiding & The Path-Ordered Wilson 1-Cocycle $\mathcal{W}_X^{(n)}(Q)$
-/

section ArchetypeM4_NonAbelianWilsonCocycle

variable {G : Type*} [Group G]

/-- Group conjugation $\mathrm{Ad}_x(q) = x q x^{-1}$. -/
def conjBy (x q : G) : G := x * q * x⁻¹

/-- **The Non-Abelian Path-Ordered Wilson Line 1-Cocycle**:
$\mathcal{W}_X^{(0)}(Q) = 1$ and $\mathcal{W}_X^{(n+1)}(Q) = Q \cdot (X \mathcal{W}_X^{(n)}(Q) X^{-1})$. -/
def wilsonCocycle (X Q : G) : ℕ → G
  | 0 => 1
  | n + 1 => Q * conjBy X (wilsonCocycle X Q n)

/-- **Braided Power Law for Non-Commuting Operator Phase $Q$**:
If $Z X = Q X Z$ in a non-Abelian group $G$, then $Z X^n = \mathcal{W}_X^{(n)}(Q) X^n Z$ for all $n \in \mathbb{N}$. -/
theorem braided_pow_law {X Z Q : G} (h_braid : Z * X = Q * X * Z) (n : ℕ) :
    Z * X ^ n = wilsonCocycle X Q n * X ^ n * Z := by
  induction' n with n ih
  · simp [wilsonCocycle]
  · calc Z * X ^ (n + 1)
      _ = (Z * X) * X ^ n := by rw [pow_succ', mul_assoc]
      _ = (Q * X * Z) * X ^ n := by rw [h_braid]
      _ = Q * X * (Z * X ^ n) := by group
      _ = Q * X * (wilsonCocycle X Q n * X ^ n * Z) := by rw [ih]
      _ = (Q * (X * wilsonCocycle X Q n * X⁻¹)) * (X * X ^ n) * Z := by group
      _ = wilsonCocycle X Q (n + 1) * X ^ (n + 1) * Z := by
          rw [wilsonCocycle, conjBy, ← pow_succ']

/-- **Non-Abelian Group Cohomology 1-Cocycle Identity**:
$\mathcal{W}_X^{(m+n)}(Q) = \mathcal{W}_X^{(m)}(Q) \cdot (X^m \mathcal{W}_X^{(n)}(Q) X^{-m})$. -/
theorem wilsonCocycle_add (X Q : G) (m n : ℕ) :
    wilsonCocycle X Q (m + n) =
      wilsonCocycle X Q m * conjBy (X ^ m) (wilsonCocycle X Q n) := by
  induction' m with m ih
  · simp [wilsonCocycle, conjBy]
  · have h_add : m + 1 + n = (m + n) + 1 := by omega
    rw [h_add, wilsonCocycle, ih, wilsonCocycle]
    dsimp [conjBy]
    rw [pow_succ']
    group

/-- **Periodicity Obstruction Theorem**:
If $Z X = Q X Z$ and $X^N = 1$, then the path-ordered Wilson 1-cocycle $\mathcal{W}_X^{(N)}(Q)$
must equal $1$ (even when $Q^N \neq 1$). -/
theorem wilsonCocycle_eq_one_of_pow_eq_one {X Z Q : G}
    (h_braid : Z * X = Q * X * Z) {N : ℕ} (hXN : X ^ N = 1) :
    wilsonCocycle X Q N = 1 := by
  have h := braided_pow_law h_braid N
  rw [hXN, mul_one, mul_one] at h
  calc wilsonCocycle X Q N
    _ = (wilsonCocycle X Q N * Z) * Z⁻¹ := by group
    _ = Z * Z⁻¹ := by rw [← h]
    _ = 1 := mul_inv_cancel Z

end ArchetypeM4_NonAbelianWilsonCocycle

/-!
## Archetype $\mathcal{M}_5$: Non-Diagonal Block-Matrix Realization with Parabolic Infinite-Order Plaquette Holonomy
-/

section ArchetypeM5_ParabolicPlaquetteHolonomy

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ
abbrev BlockMat := Matrix (Fin 2) (Fin 2) Mat2Z

/-- Internal non-commuting site involutions $W_0, W_1 \in \mathrm{Mat}_2(\mathbb{Z})$ and unipotent link $G$. -/
def W0_mat : Mat2Z := ![![0, 1], ![1, 0]]
def W1_mat : Mat2Z := ![![1, 0], ![0, -1]]
def G_mat : Mat2Z := ![![1, 1], ![0, 1]]
def Gi_mat : Mat2Z := ![![1, -1], ![0, 1]]

/-- Non-diagonal gauged shift operator $X_{\mathrm{blk}} = \begin{pmatrix} 0 & G \\ G^{-1} & 0 \end{pmatrix}$. -/
def X_blk : BlockMat := ![![0, G_mat], ![Gi_mat, 0]]

/-- Site-dependent gauged clock operator $Z_{\mathrm{blk}} = \begin{pmatrix} W_0 & 0 \\ 0 & W_1 \end{pmatrix}$. -/
def Z_blk : BlockMat := ![![W0_mat, 0], ![0, W1_mat]]

/-- Non-Abelian plaquette holonomy $Q_{\mathrm{blk}} = (Z_{\mathrm{blk}} X_{\mathrm{blk}})^2$. -/
def Q_blk : BlockMat := (Z_blk * X_blk) * (Z_blk * X_blk)

/-- Parabolic $\mathrm{SL}_2(\mathbb{Z})$ fiber holonomy $Q_0 = W_0 G W_1 G^{-1} = \begin{pmatrix} 0 & -1 \\ 1 & 2 \end{pmatrix}$. -/
def Q0_mat : Mat2Z := ![![0, -1], ![1, 2]]

theorem X_blk_sq : X_blk * X_blk = 1 := by decide
theorem Z_blk_sq : Z_blk * Z_blk = 1 := by decide

/-- **Exact Non-Abelian Weyl–Heisenberg Braiding**: $Z_{\mathrm{blk}} X_{\mathrm{blk}} = Q_{\mathrm{blk}} X_{\mathrm{blk}} Z_{\mathrm{blk}}$. -/
theorem block_weyl_heisenberg_braiding :
    Z_blk * X_blk = Q_blk * X_blk * Z_blk := by decide

/-- The operator phase $Q_{\mathrm{blk}}$ is strictly non-central: it commutes with neither $X_{\mathrm{blk}}$ nor $Z_{\mathrm{blk}}$. -/
theorem Q_blk_noncomm_X : Q_blk * X_blk ≠ X_blk * Q_blk := by decide
theorem Q_blk_noncomm_Z : Q_blk * Z_blk ≠ Z_blk * Q_blk := by decide

/-- Whereas the scalar phase at $N=2$ satisfies $q^2 = 1$, the non-Abelian holonomy satisfies $Q_{\mathrm{blk}}^2 \neq 1$,
while the twisted Wilson 1-cocycle closes identically: $Q_{\mathrm{blk}} (X_{\mathrm{blk}} Q_{\mathrm{blk}} X_{\mathrm{blk}}) = 1$. -/
theorem Q_blk_sq_ne_one : Q_blk * Q_blk ≠ 1 := by decide
theorem wilson_cocycle_closure_X : Q_blk * (X_blk * Q_blk * X_blk) = 1 := by decide
theorem wilson_cocycle_closure_Z : (Z_blk * Q_blk * Z_blk) * Q_blk = 1 := by decide

/-- Exact closed-form Jordan-parabolic power law for the upper-left fiber holonomy $Q_0^n$:
$Q_0^n = \begin{pmatrix} 1 - n & -n \\ n & 1 + n \end{pmatrix}$ for all $n \in \mathbb{N}$. -/
theorem Q0_mat_pow (n : ℕ) :
    Q0_mat ^ n = ![![1 - (n : ℤ), -(n : ℤ)], ![(n : ℤ), 1 + (n : ℤ)]] := by
  induction' n with n ih
  · decide
  · rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q0_mat, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring

theorem Q_blk_pow_00 (n : ℕ) :
    (Q_blk ^ n) 0 0 = Q0_mat ^ n ∧ (Q_blk ^ n) 0 1 = 0 := by
  induction' n with n ih
  · decide
  · rcases ih with ⟨ih00, ih01⟩
    have h10 : Q_blk 1 0 = 0 := by decide
    have h01 : Q_blk 0 1 = 0 := by decide
    have h00 : Q_blk 0 0 = Q0_mat := by decide
    constructor
    · rw [pow_succ, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
          ih00, ih01, h00, h10, zero_mul, add_zero]
    · rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
          ih00, ih01, h01, mul_zero, zero_mul, add_zero]

/-- **Infinite Multiplicative Order of the Non-Abelian Plaquette Holonomy**:
Even though $X_{\mathrm{blk}}^2 = 1$ and $Z_{\mathrm{blk}}^2 = 1$, the braiding holonomy $Q_{\mathrm{blk}}$
satisfies $Q_{\mathrm{blk}}^n \neq 1$ for every positive integer $n > 0$. -/
theorem Q_blk_infinite_order (n : ℕ) (hn : 0 < n) : Q_blk ^ n ≠ 1 := by
  intro h_eq
  have h_block : (Q_blk ^ n) 0 0 = (1 : BlockMat) 0 0 := by rw [h_eq]
  rw [(Q_blk_pow_00 n).1, Q0_mat_pow n] at h_block
  have h_entry : (![![1 - (n : ℤ), -(n : ℤ)], ![(n : ℤ), 1 + (n : ℤ)]] : Mat2Z) 1 0 =
      ((1 : BlockMat) 0 0) 1 0 := by rw [h_block]
  change (n : ℤ) = 0 at h_entry
  omega

end ArchetypeM5_ParabolicPlaquetteHolonomy

/-!
## Archetype $\mathcal{M}_6$ & $\mathcal{M}_7$: Non-Abelian Clifford–Majorana Artin Braid Group Representation
-/

section ArchetypeM6_CliffordMajoranaArtinBraid

/-- Triple product reduction for anticommuting skew-involutive Clifford bivectors $E_{12}, E_{23}$
in any noncommutative ring $B$: $(1 + E_{12})(1 + E_{23})(1 + E_{12}) = 2(E_{12} + E_{23})$. -/
theorem clifford_bivector_triple_product {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = 2 * (E₁₂ + E₂₃) := by
  have h12' : E₁₂ * E₁₂ + 1 = 0 := by rw [h12, neg_add_cancel]
  calc (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂)
    _ = 2 * (E₁₂ + E₂₃) + (E₁₂ * E₁₂ + 1) * (1 - E₂₃) +
        (1 + E₁₂) * (E₁₂ * E₂₃ + E₂₃ * E₁₂) := by noncomm_ring
    _ = 2 * (E₁₂ + E₂₃) + 0 * (1 - E₂₃) + (1 + E₁₂) * 0 := by rw [h12', h_anti]
    _ = 2 * (E₁₂ + E₂₃) := by noncomm_ring

/-- **Universal Noncommutative Clifford–Majorana Artin Braid Theorem**:
For any anticommuting skew-involutions $E_{12}, E_{23} \in B$ ($E_{12}^2 = E_{23}^2 = -1$,
$\{E_{12}, E_{23}\} = 0$), the braid generators $R_{12} = 1 + E_{12}$ and $R_{23} = 1 + E_{23}$
satisfy the Artin braid relation $R_{12} R_{23} R_{12} = R_{23} R_{12} R_{23}$. -/
theorem clifford_majorana_artin_braid {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h23 : E₂₃ * E₂₃ = -1)
    (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = (1 + E₂₃) * (1 + E₁₂) * (1 + E₂₃) := by
  have h_anti' : E₂₃ * E₁₂ + E₁₂ * E₂₃ = 0 := by rw [add_comm, h_anti]
  rw [clifford_bivector_triple_product h12 h_anti,
      clifford_bivector_triple_product h23 h_anti']
  noncomm_ring

/-- Concrete non-diagonal realization of anticommuting skew-involutive bivectors in $\mathrm{Mat}_4(\mathbb{Z})$. -/
def E12_mat4 : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![0, -1, 0, 0],
    ![1,  0, 0, 0],
    ![0,  0, 0, -1],
    ![0,  0, 1,  0]]

def E23_mat4 : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![0,  0, -1, 0],
    ![0,  0,  0, 1],
    ![1,  0,  0, 0],
    ![0, -1,  0, 0]]

def R12_mat4 : Matrix (Fin 4) (Fin 4) ℤ := 1 + E12_mat4
def R23_mat4 : Matrix (Fin 4) (Fin 4) ℤ := 1 + E23_mat4

theorem E12_mat4_sq : E12_mat4 * E12_mat4 = -1 := by decide
theorem E23_mat4_sq : E23_mat4 * E23_mat4 = -1 := by decide
theorem E12_E23_mat4_anticomm : E12_mat4 * E23_mat4 + E23_mat4 * E12_mat4 = 0 := by decide

/-- **Concrete Non-Abelian Artin Braid & Non-Involutive Anyonic Statistics in $\mathrm{Mat}_4(\mathbb{Z})$**:
The integer matrix braid operators $R_{12}, R_{23}$ satisfy the Artin braid relation, do not
commute ($R_{12} R_{23} \neq R_{23} R_{12}$), and exhibit non-involutive order-4 braiding. -/
theorem mat4_artin_braid_and_noncommutativity :
    R12_mat4 * R23_mat4 * R12_mat4 = R23_mat4 * R12_mat4 * R23_mat4 ∧
    R12_mat4 * R23_mat4 ≠ R23_mat4 * R12_mat4 ∧
    R12_mat4 * R12_mat4 ≠ 2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
    R12_mat4 ^ 4 = (-4 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  refine ⟨?_, by decide, by decide, by decide⟩
  exact clifford_majorana_artin_braid E12_mat4_sq E23_mat4_sq E12_E23_mat4_anticomm

end ArchetypeM6_CliffordMajoranaArtinBraid

end NoncommutativeGaugeAndBraidedHolonomy
```

## Turn 0018, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

open Matrix

namespace CordovaFreedTelemanTorsionAnomalies

/-!
## Archetype $\mathcal{T}_1$: Non-Abelian Čech–Gerbe Triple-Overlap 2-Cocycle & Tetrahedral Coherence
(Equation 16b of Córdova–Freed–Teleman, `arXiv:2408.15148`)
-/

section ArchetypeT1_CechGerbeCocycle

variable {G : Type*} [Group G]

/-- Group conjugation $\mathrm{Ad}_g(h) = g h g^{-1}$. -/
def conjBy (g h : G) : G := g * h * g⁻¹

/-- The non-Abelian gerbe 2-cocycle defect $\Phi_{ijk} = \Psi_{ij} \Psi_{jk} \Psi_{ik}^{-1}$ measuring
the failure of bundle transition isomorphisms $\Psi_{ij}$ to close on a triple overlap $U_i \cap U_j \cap U_k$. -/
def gerbeDefect (Ψ_ij Ψ_jk Ψ_ik : G) : G :=
  Ψ_ij * Ψ_jk * Ψ_ik⁻¹

/-- Twisted projective transition composition law (Eq. 16b of `arXiv:2408.15148`):
$\Psi_{ij} \Psi_{jk} = \Phi_{ijk} \Psi_{ik}$. -/
theorem projective_transition_law (Ψ_ij Ψ_jk Ψ_ik : G) :
    Ψ_ij * Ψ_jk = gerbeDefect Ψ_ij Ψ_jk Ψ_ik * Ψ_ik := by
  dsimp [gerbeDefect]
  group

/-- **Non-Abelian Tetrahedral Čech–Gerbe 2-Cocycle Coherence Identity**:
Across any quadruple overlap $U_i \cap U_j \cap U_k \cap U_l$, the gerbe defects satisfy
$\Phi_{ijk} \Phi_{ikl} = \mathrm{Ad}_{\Psi_{ij}}(\Phi_{jkl}) \Phi_{ijl}$. -/
theorem gerbeDefect_tetrahedral_cocycle
    (Ψ_ij Ψ_jk Ψ_kl Ψ_ik Ψ_jl Ψ_il : G) :
    gerbeDefect Ψ_ij Ψ_jk Ψ_ik * gerbeDefect Ψ_ik Ψ_kl Ψ_il =
      conjBy Ψ_ij (gerbeDefect Ψ_jk Ψ_kl Ψ_jl) * gerbeDefect Ψ_ij Ψ_jl Ψ_il := by
  dsimp [gerbeDefect, conjBy]
  group

end ArchetypeT1_CechGerbeCocycle

/-!
## Archetype $\mathcal{T}_2$: Gerbe-Twisted Operator Bundles & Twisted Curvature Patching in $M_r(B)$
(Equations 15–16a of Córdova–Freed–Teleman, `arXiv:2408.15148`)
-/

section ArchetypeT2_TwistedBundleCurvature

/-- Predicate for an additive homomorphism $d : B \to+ B$ on a noncommutative ring $B$ to be a
Leibniz derivation. -/
def IsRingDeriv {B : Type*} [Ring B] (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

/-- Entrywise lifting of an additive map $d : B \to+ B$ to the rank-$r$ matrix ring $M_r(B)$. -/
def liftMatrixDeriv {B : Type*} [Ring B] {r : ℕ}
    (d : B →+ B) : Matrix (Fin r) (Fin r) B →+ Matrix (Fin r) (Fin r) B where
  toFun M i j := d (M i j)
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; simp

theorem IsRingDeriv.liftMatrix {B : Type*} [Ring B] {r : ℕ}
    {d : B →+ B} (hd : IsRingDeriv d) :
    IsRingDeriv (liftMatrixDeriv (r := r) d) := by
  intro M N
  ext i k
  simp only [liftMatrixDeriv, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply,
    Matrix.mul_apply, map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact hd (M i j) (N j k)

/-- Left covariant derivative $\nabla_{d, A}(\psi) = d(\psi) + A \psi$. -/
def covDeriv {R : Type*} [Ring R] (d : R →+ R) (A ψ : R) : R :=
  d ψ + A * ψ

/-- Non-Abelian curvature $F(d_1, d_2, A_1, A_2) = d_1(A_2) - d_2(A_1) + \⁅A_1, A_2⁆$. -/
def curvature {R : Type*} [Ring R] (d₁ d₂ : R →+ R) (A₁ A₂ : R) : R :=
  d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆

/-- Affine gauge transformation $A^u = u A u^{-1} - d(u) u^{-1}$. -/
def gaugeTransformConn {R : Type*} [Ring R] (d : R →+ R) (u : Rˣ) (A : R) : R :=
  (u : R) * A * (↑u⁻¹ : R) - d (u : R) * (↑u⁻¹ : R)

theorem covariant_curvature_multiplication {R : Type*} [Ring R]
    {d₁ d₂ : R →+ R} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : R, d₁ (d₂ x) = d₂ (d₁ x)) (A₁ A₂ ψ : R) :
    covDeriv d₁ A₁ (covDeriv d₂ A₂ ψ) - covDeriv d₂ A₂ (covDeriv d₁ A₁ ψ) =
      curvature d₁ d₂ A₁ A₂ * ψ := by
  dsimp [covDeriv, curvature]
  rw [Ring.lie_def, map_add, map_add, hd₁ A₂ ψ, hd₂ A₁ ψ, h_comm ψ]
  noncomm_ring

theorem covariant_gauge_intertwining {R : Type*} [Ring R]
    {d : R →+ R} (hd : IsRingDeriv d) (u : Rˣ) (A ψ : R) :
    covDeriv d (gaugeTransformConn d u A) ((u : R) * ψ) =
      (u : R) * covDeriv d A ψ := by
  dsimp [covDeriv, gaugeTransformConn]
  rw [hd (u : R) ψ]
  have hu : (↑u⁻¹ : R) * (u : R) = 1 := Units.inv_mul u
  calc d (u : R) * ψ + (u : R) * d ψ +
        ((u : R) * A * (↑u⁻¹ : R) - d (u : R) * (↑u⁻¹ : R)) * ((u : R) * ψ)
    _ = d (u : R) * ψ + (u : R) * d ψ +
        (u : R) * A * ((↑u⁻¹ : R) * (u : R)) * ψ -
        d (u : R) * ((↑u⁻¹ : R) * (u : R)) * ψ := by noncomm_ring
    _ = d (u : R) * ψ + (u : R) * d ψ +
        (u : R) * A * 1 * ψ - d (u : R) * 1 * ψ := by rw [hu]
    _ = (u : R) * (d ψ + A * ψ) := by noncomm_ring

theorem curvature_gauge_covariance {R : Type*} [Ring R]
    {d₁ d₂ : R →+ R} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : R, d₁ (d₂ x) = d₂ (d₁ x)) (u : Rˣ) (A₁ A₂ : R) :
    curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) =
      (u : R) * curvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : R) := by
  have h_lhs := covariant_curvature_multiplication hd₁ hd₂ h_comm
    (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) ((u : R) * 1)
  rw [covariant_gauge_intertwining hd₂ u A₂ 1,
      covariant_gauge_intertwining hd₁ u A₁ (covDeriv d₂ A₂ 1),
      covariant_gauge_intertwining hd₁ u A₁ 1,
      covariant_gauge_intertwining hd₂ u A₂ (covDeriv d₁ A₁ 1)] at h_lhs
  have h_rhs := covariant_curvature_multiplication hd₁ hd₂ h_comm A₁ A₂ 1
  have h_comb : curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) * (u : R) =
      (u : R) * curvature d₁ d₂ A₁ A₂ := by
    calc curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) * (u : R)
      _ = curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) * ((u : R) * 1) := by
          rw [mul_one]
      _ = (u : R) * covDeriv d₁ A₁ (covDeriv d₂ A₂ 1) -
          (u : R) * covDeriv d₂ A₂ (covDeriv d₁ A₁ 1) := h_lhs.symm
      _ = (u : R) * (covDeriv d₁ A₁ (covDeriv d₂ A₂ 1) - covDeriv d₂ A₂ (covDeriv d₁ A₁ 1)) := by
          noncomm_ring
      _ = (u : R) * (curvature d₁ d₂ A₁ A₂ * 1) := by rw [h_rhs]
      _ = (u : R) * curvature d₁ d₂ A₁ A₂ := by rw [mul_one]
  calc curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂)
    _ = curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) *
        ((u : R) * (↑u⁻¹ : R)) := by rw [Units.mul_inv, mul_one]
    _ = (curvature d₁ d₂ (gaugeTransformConn d₁ u A₁) (gaugeTransformConn d₂ u A₂) * (u : R)) *
        (↑u⁻¹ : R) := by noncomm_ring
    _ = (u : R) * curvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : R) := by rw [h_comb]

/-- Diagonal embedding $\iota_r(b) = b \cdot I_r$ of a gerbe curving $b \in B$ into $M_r(B)$. -/
def gerbeEmbed {B : Type*} [Ring B] (r : ℕ) (b : B) : Matrix (Fin r) (Fin r) B :=
  Matrix.of (fun i j => if i = j then b else 0)

/-- **Twisted Vector Bundle Curvature** $\Omega_E(A_1, A_2, B_{\mathrm{gerbe}}) = F(A_1, A_2) + \iota_r(B_{\mathrm{gerbe}})$
(Equation 16a of `arXiv:2408.15148`). -/
def twistedBundleCurvature {B : Type*} [Ring B] {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B) :
    Matrix (Fin r) (Fin r) B :=
  curvature (liftMatrixDeriv d₁) (liftMatrixDeriv d₂) A₁ A₂ + gerbeEmbed r B_gerbe

/-- **Covariant Patching of Twisted Bundle Curvature (Eq. 16a of `arXiv:2408.15148`)**:
Under a transition isomorphism $\Psi \in M_r(B)^\times$, $F(A^\Psi) + \Psi B \Psi^{-1} = \Psi (F(A) + B) \Psi^{-1}$. -/
theorem twisted_curvature_transition_patching {R : Type*} [Ring R]
    {d₁ d₂ : R →+ R} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : R, d₁ (d₂ x) = d₂ (d₁ x)) (Ψ : Rˣ) (A₁ A₂ B_mat : R) :
    curvature d₁ d₂ (gaugeTransformConn d₁ Ψ A₁) (gaugeTransformConn d₂ Ψ A₂) +
      (Ψ : R) * B_mat * (↑Ψ⁻¹ : R) =
      (Ψ : R) * (curvature d₁ d₂ A₁ A₂ + B_mat) * (↑Ψ⁻¹ : R) := by
  rw [curvature_gauge_covariance hd₁ hd₂ h_comm Ψ A₁ A₂]
  noncomm_ring

end ArchetypeT2_TwistedBundleCurvature

/-!
## Archetype $\mathcal{T}_3$: Noncommutative Trace-Rank Identity & Proposition 22 Torsion Theorem
(Definition 20, Equation 21 & Proposition 22 of Córdova–Freed–Teleman, `arXiv:2408.15148`)
-/

section ArchetypeT3_Proposition22TorsionTheorem

variable {B : Type*} [Ring B]

/-- Noncommutative matrix trace $\mathrm{Tr}_r(M) = \sum_{i=1}^r M_{ii} \in B$. -/
def ncTrace {r : ℕ} (M : Matrix (Fin r) (Fin r) B) : B :=
  ∑ i : Fin r, M i i

@[simp]
theorem ncTrace_zero {r : ℕ} : ncTrace (0 : Matrix (Fin r) (Fin r) B) = 0 := by
  dsimp [ncTrace]; simp

theorem ncTrace_add {r : ℕ} (M N : Matrix (Fin r) (Fin r) B) :
    ncTrace (M + N) = ncTrace M + ncTrace N := by
  dsimp [ncTrace]; simp [Finset.sum_add_distrib]

theorem ncTrace_sub {r : ℕ} (M N : Matrix (Fin r) (Fin r) B) :
    ncTrace (M - N) = ncTrace M - ncTrace N := by
  dsimp [ncTrace]; simp [Finset.sum_sub_distrib]

theorem ncTrace_liftMatrixDeriv {r : ℕ} (d : B →+ B) (M : Matrix (Fin r) (Fin r) B) :
    ncTrace (liftMatrixDeriv d M) = d (ncTrace M) := by
  dsimp [ncTrace, liftMatrixDeriv]
  rw [map_sum]

/-- **Rank-Scaling Trace Identity**:
The trace of the diagonal gerbe curving $\iota_r(b) \in M_r(B)$ is the $r$-fold multiple $r \bullet b$. -/
theorem ncTrace_gerbeEmbed (r : ℕ) (b : B) :
    ncTrace (gerbeEmbed r b) = r • b := by
  dsimp [ncTrace, gerbeEmbed]
  simp [Finset.sum_const, Finset.card_fin]

/-- **Universal Trace-Curvature Decomposition for Rank-$r$ Twisted Bundles**:
$\mathrm{Tr}_r(\Omega_E) = d_1(\mathrm{Tr}_r(A_2)) - d_2(\mathrm{Tr}_r(A_1)) + \mathrm{Tr}_r(\⁅A_1, A_2⁆) + r \bullet B_{\mathrm{gerbe}}$. -/
theorem ncTrace_twistedBundleCurvature {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B) :
    ncTrace (twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe) =
      d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆ + r • B_gerbe := by
  dsimp [twistedBundleCurvature, curvature]
  rw [ncTrace_add, ncTrace_add, ncTrace_sub,
      ncTrace_liftMatrixDeriv, ncTrace_liftMatrixDeriv, ncTrace_gerbeEmbed]

/-- **Proposition 22 of Córdova–Freed–Teleman (`arXiv:2408.15148`) — The Torsion Anomaly Theorem**:
If a rank-$r$ $\mathcal{G}$-twisted operator bundle is projectively flat ($\Omega_E = 0$, Definition 20 / Eq. 21),
then the $r$-fold multiple of the gerbe anomaly curving $r \bullet B_{\mathrm{gerbe}}$ is trivialized
by the determinant-trace curvature $-\big(d_1(\mathrm{Tr}_r A_2) - d_2(\mathrm{Tr}_r A_1) + \mathrm{Tr}_r\⁅A_1, A_2⁆\big)$. -/
theorem projectively_flat_torsion_anomaly {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B)
    (h_flat : twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe = 0) :
    r • B_gerbe = -(d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) := by
  have h_tr : ncTrace (twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe) = 0 := by
    rw [h_flat, ncTrace_zero]
  rw [ncTrace_twistedBundleCurvature] at h_tr
  exact eq_neg_of_add_eq_zero_right h_tr

end ArchetypeT3_Proposition22TorsionTheorem

/-!
## Archetype $\mathcal{T}_4$: Gerbe Flatness from Projective Flatness via the Non-Abelian Bianchi Identity
(Page 6 Differential Bianchi Theorem of Córdova–Freed–Teleman, `arXiv:2408.15148`)
-/

section ArchetypeT4_ProjectivelyFlatImpliesGerbeFlat

variable {R : Type*} [Ring R]

/-- Adjoint covariant derivative $D_{d, A}(X) = d(X) + \⁅A, X⁆$. -/
def adjointCovDeriv (d : R →+ R) (A X : R) : R :=
  d X + ⁅A, X⁆

theorem differential_nonabelian_bianchi_identity
    {d₁ d₂ d₃ : R →+ R}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : R, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : R, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : R, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : R) :
    adjointCovDeriv d₁ A₁ (curvature d₂ d₃ A₂ A₃) +
    adjointCovDeriv d₂ A₂ (curvature d₃ d₁ A₃ A₁) +
    adjointCovDeriv d₃ A₃ (curvature d₁ d₂ A₁ A₂) = 0 := by
  dsimp [adjointCovDeriv, curvature]
  simp only [Ring.lie_def, map_add, map_sub]
  rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
      h12 A₃, h13 A₂, h23 A₁, ← h12 A₃, ← h13 A₂, ← h23 A₁]
  noncomm_ring

/-- **Page 6 Theorem of Córdova–Freed–Teleman (`arXiv:2408.15148`)**:
If a twisted operator bundle with non-commuting connection components $A_1, A_2, A_3 \in R$ is
projectively flat ($F_{ij} + B_{ij} = 0$) with respect to central/scalar gerbe 2-forms $B_{ij}$
($\⁅A_k, B_{ij}⁆ = 0$), then the non-Abelian Bianchi identity forces the gerbe curving itself to be
flat: $d_1(B_{23}) + d_2(B_{31}) + d_3(B_{12}) = 0$. -/
theorem projectively_flat_implies_gerbe_flat
    {d₁ d₂ d₃ : R →+ R}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : R, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : R, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : R, d₁ (d₃ x) = d₃ (d₁ x))
    {A₁ A₂ A₃ B₂₃ B₃₁ B₁₂ : R}
    (h_flat₂₃ : curvature d₂ d₃ A₂ A₃ + B₂₃ = 0)
    (h_flat₃₁ : curvature d₃ d₁ A₃ A₁ + B₃₁ = 0)
    (h_flat₁₂ : curvature d₁ d₂ A₁ A₂ + B₁₂ = 0)
    (h_comm₁ : ⁅A₁, B₂₃⁆ = 0)
    (h_comm₂ : ⁅A₂, B₃₁⁆ = 0)
    (h_comm₃ : ⁅A₃, B₁₂⁆ = 0) :
    d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂ = 0 := by
  have h_bianchi := differential_nonabelian_bianchi_identity hd₁ hd₂ hd₃ h12 h23 h13 A₁ A₂ A₃
  have hF₂₃ : curvature d₂ d₃ A₂ A₃ = -B₂₃ := eq_neg_of_add_eq_zero_left h_flat₂₃
  have hF₃₁ : curvature d₃ d₁ A₃ A₁ = -B₃₁ := eq_neg_of_add_eq_zero_left h_flat₃₁
  have hF₁₂ : curvature d₁ d₂ A₁ A₂ = -B₁₂ := eq_neg_of_add_eq_zero_left h_flat₁₂
  rw [hF₂₃, hF₃₁, hF₁₂] at h_bianchi
  dsimp [adjointCovDeriv] at h_bianchi
  simp only [Ring.lie_def, map_neg] at h_bianchi h_comm₁ h_comm₂ h_comm₃
  linear_combination -h_bianchi - h_comm₁ - h_comm₂ - h_comm₃

end ArchetypeT4_ProjectivelyFlatImpliesGerbeFlat

/-!
## Archetype $\mathcal{T}_5$: Rank-4 Orthogonal Gapped Boundary in $\mathrm{Mat}_4(\mathbb{Z})$ with Non-Scalar Order-4 Torsion Anomaly
-/

section ArchetypeT5_OrthogonalGappedTorsionBoundary

abbrev Mat4Z := Matrix (Fin 4) (Fin 4) ℤ

/-- Non-commuting orthogonal boundary symmetry generators $T_1, T_2 \in \mathrm{SO}_4(\mathbb{Z}) \subset \mathrm{Mat}_4(\mathbb{Z})$. -/
def T1_gapped : Mat4Z :=
  ![![0, 0, 1, 0],
    ![0, 0, 0, 1],
    ![1, 0, 0, 0],
    ![0, 1, 0, 0]]

def T2_gapped : Mat4Z :=
  ![![0, -1, 0, 0],
    ![1,  0, 0, 0],
    ![0,  0, 1, 0],
    ![0,  0, 0, 1]]

/-- Non-diagonal, non-scalar boundary 't Hooft anomaly operator
$\mathcal{A}_{\mathrm{torsion}} = T_1 T_2 T_1^{-1} T_2^{-1} \in \mathrm{SO}_4(\mathbb{Z})$. -/
def A_torsion : Mat4Z :=
  ![![ 0, 1, 0,  0],
    ![-1, 0, 0,  0],
    ![ 0, 0, 0, -1],
    ![ 0, 0, 1,  0]]

/-- **Rank-4 Orthogonal Gapped Boundary Torsion Theorem**:
1. $T_1$ and $T_2$ are orthogonal ($T_1^\top T_1 = I_4$, $T_2^\top T_2 = I_4$).
2. They satisfy the projective boundary braiding relation $T_1 T_2 = \mathcal{A}_{\mathrm{torsion}} T_2 T_1$.
3. The anomaly operator $\mathcal{A}_{\mathrm{torsion}}$ is non-central ($\mathcal{A}_{\mathrm{torsion}} T_1 \neq T_1 \mathcal{A}_{\mathrm{torsion}}$)
   and has **exact finite torsion order $r = 4$** ($\mathcal{A}_{\mathrm{torsion}} \neq I_4$,
   $\mathcal{A}_{\mathrm{torsion}}^2 \neq I_4$, $\mathcal{A}_{\mathrm{torsion}}^3 \neq I_4$, and $\mathcal{A}_{\mathrm{torsion}}^4 = I_4$). -/
theorem gapped_orthogonal_boundary_torsion_properties :
    T1_gappedᵀ * T1_gapped = 1 ∧
    T2_gappedᵀ * T2_gapped = 1 ∧
    T1_gapped * T2_gapped = A_torsion * T2_gapped * T1_gapped ∧
    A_torsion * T1_gapped ≠ T1_gapped * A_torsion ∧
    A_torsion ^ 1 ≠ 1 ∧
    A_torsion ^ 2 ≠ 1 ∧
    A_torsion ^ 3 ≠ 1 ∧
    A_torsion ^ 4 = 1 ∧
    A_torsion * (T1_gapped * A_torsion * T1_gapped) = 1 := by
  refine ⟨by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide⟩

end ArchetypeT5_OrthogonalGappedTorsionBoundary

end CordovaFreedTelemanTorsionAnomalies
```

## Turn 0021, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace KnutsenFractalUncertaintyAndGaborMultipliers

/-!
## Archetype $\mathcal{F}_1$: Separate Time-Frequency FUP Operator, Pore Conservation & Commutator Variance
(Section 1, Equation 1.1 of Knutsen, `arXiv:2204.03068v1`)
-/

section ArchetypeF1_SeparateFUPAndCommutatorVariance

variable {B : Type*} [Ring B] [StarRing B]

/-- The separate time-frequency localization operator $\mathcal{L}_{\Omega, T} = P_\Omega U P_T$
(Equation 1.1 of Knutsen). -/
def separateFUP (P_Ω U P_T : B) : B :=
  P_Ω * U * P_T

/-- Compressed Toeplitz/projection localization operator $T_{P, Q} = P Q P$. -/
def compressedLoc (P Q : B) : B :=
  P * Q * P

/-- **Pore Uncertainty Conservation Law**:
For any unitary transform $U$ ($U^\star U = 1$) and self-adjoint projections $P_T, P_\Omega$, the
localization Gram operator on $\Omega$ plus the localization Gram operator on the complementary
pore $1 - \Omega$ equals $P_T$. -/
theorem fup_pore_uncertainty_conservation
    {P_Ω U P_T : B} (hU : star U * U = 1)
    (hT_idem : P_T * P_T = P_T) (hT_sa : star P_T = P_T)
    (hΩ_idem : P_Ω * P_Ω = P_Ω) (hΩ_sa : star P_Ω = P_Ω) :
    star (separateFUP P_Ω U P_T) * separateFUP P_Ω U P_T +
    star (separateFUP (1 - P_Ω) U P_T) * separateFUP (1 - P_Ω) U P_T = P_T := by
  dsimp [separateFUP]
  simp only [star_mul, star_sub, star_one, hT_sa, hΩ_sa]
  have h1 : P_T * star U * P_Ω * (P_Ω * U * P_T) +
            P_T * star U * (1 - P_Ω) * ((1 - P_Ω) * U * P_T) =
            P_T * star U * (P_Ω * P_Ω + (1 - P_Ω) * (1 - P_Ω)) * U * P_T := by
    noncomm_ring
  have h2 : P_Ω * P_Ω + (1 - P_Ω) * (1 - P_Ω) = 1 := by
    calc P_Ω * P_Ω + (1 - P_Ω) * (1 - P_Ω)
      _ = 1 - P_Ω - P_Ω + (P_Ω * P_Ω + P_Ω * P_Ω) := by noncomm_ring
      _ = 1 - P_Ω - P_Ω + (P_Ω + P_Ω) := by rw [hΩ_idem]
      _ = 1 := by noncomm_ring
  rw [h1, h2]
  calc P_T * star U * 1 * U * P_T
    _ = P_T * (star U * U) * P_T := by noncomm_ring
    _ = P_T * 1 * P_T := by rw [hU]
    _ = P_T * P_T := by noncomm_ring
    _ = P_T := hT_idem

/-- **Noncommutative Uncertainty Variance Identity (Pore Leakage Form)**:
For any two non-commuting projections $P, Q \in B$, the failure of $T_{P, Q} = P Q P$ to be idempotent
equals the positive-type leakage $\big((1 - P) Q P\big)^\star \big((1 - P) Q P\big)$ into the pore $1 - P$. -/
theorem compressedLoc_variance_eq_pore_leakage
    {P Q : B} (hP_idem : P * P = P) (hP_sa : star P = P)
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    compressedLoc P Q - compressedLoc P Q * compressedLoc P Q =
      star ((1 - P) * Q * P) * ((1 - P) * Q * P) := by
  dsimp [compressedLoc]
  simp only [star_mul, star_sub, star_one, hP_sa, hQ_sa]
  have h1P : (1 - P) * (1 - P) = 1 - P := by
    calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP_idem]; noncomm_ring
  calc P * Q * P - P * Q * P * (P * Q * P)
    _ = P * (Q * Q) * P - P * Q * (P * P) * Q * P := by rw [hQ_idem, hP_idem]; noncomm_ring
    _ = P * Q * (1 - P) * Q * P := by noncomm_ring
    _ = P * Q * ((1 - P) * (1 - P)) * Q * P := by rw [h1P]
    _ = P * Q * (1 - P) * ((1 - P) * Q * P) := by noncomm_ring

/-- **Noncommutative Uncertainty Variance Identity (Lie Commutator Form)**:
The idempotency defect $T_{P, Q} - T_{P, Q}^2$ is identically equal to the compressed square of
the Lie commutator $(P \⁅P, Q⁆^\star)(\⁅P, Q⁆ P)$. -/
theorem compressedLoc_variance_eq_commutator_sq
    {P Q : B} (hP_idem : P * P = P) (hP_sa : star P = P)
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    compressedLoc P Q - compressedLoc P Q * compressedLoc P Q =
      (P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P) := by
  rw [compressedLoc_variance_eq_pore_leakage hP_idem hP_sa hQ_idem hQ_sa]
  have h_comm : ⁅P, Q⁆ * P = -((1 - P) * Q * P) := by
    rw [Ring.lie_def]
    calc (P * Q - Q * P) * P = P * Q * P - Q * (P * P) := by noncomm_ring
      _ = P * Q * P - Q * P := by rw [hP_idem]
      _ = -((1 - P) * Q * P) := by noncomm_ring
  have h_star : P * star ⁅P, Q⁆ = -star ((1 - P) * Q * P) := by
    calc P * star ⁅P, Q⁆ = star (⁅P, Q⁆ * P) := by simp [star_mul, hP_sa]
      _ = -star ((1 - P) * Q * P) := by rw [h_comm, star_neg]
  rw [h_comm, h_star, neg_mul_neg]

end ArchetypeF1_SeparateFUPAndCommutatorVariance

/-!
## Archetype $\mathcal{F}_2$: Bargmann–Fock Projection & Daubechies–Toeplitz Operator Equivalence
(Section 2.1, Equations 2.2–2.6 of Knutsen, `arXiv:2204.03068v1`)
-/

section ArchetypeF2_DaubechiesToeplitzEquivalence

variable {B : Type*} [Ring B] [StarRing B]

/-- Reproducing kernel Bargmann–Fock orthogonal projection $P_{\mathrm{Fock}} = V V^\star$ associated
to an isometric STFT/Bargmann transform $V$ ($V^\star V = 1$). -/
def fockProj (V : B) : B :=
  V * star V

/-- Daubechies' time-frequency localization operator $P_S^\phi = V^\star S V$ (Equation 2.2). -/
def daubechiesOp (V S : B) : B :=
  star V * S * V

/-- Bargmann–Fock Toeplitz operator $\mathcal{T}_S = P_{\mathrm{Fock}} S P_{\mathrm{Fock}}$ (Equation 2.3). -/
def toeplitzOp (V S : B) : B :=
  fockProj V * S * fockProj V

theorem fockProj_idem {V : B} (hV : star V * V = 1) :
    fockProj V * fockProj V = fockProj V := by
  dsimp [fockProj]
  calc (V * star V) * (V * star V)
    _ = V * (star V * V) * star V := by noncomm_ring
    _ = V * 1 * star V := by rw [hV]
    _ = V * star V := by noncomm_ring

theorem fockProj_isSelfAdjoint (V : B) :
    star (fockProj V) = fockProj V := by
  dsimp [fockProj]
  simp [star_mul]

/-- **Bargmann–Daubechies–Toeplitz Intertwining Theorem (Equations 2.4–2.5)**:
For any isometric transform $V$ ($V^\star V = 1$) and symbol $S \in B$:
1. $V P_S^\phi = \mathcal{T}_S V$,
2. $V P_S^\phi V^\star = \mathcal{T}_S$,
3. $V^\star \mathcal{T}_S V = P_S^\phi$. -/
theorem bargmann_intertwines_daubechies_toeplitz {V S : B} (hV : star V * V = 1) :
    V * daubechiesOp V S = toeplitzOp V S * V ∧
    V * daubechiesOp V S * star V = toeplitzOp V S ∧
    star V * toeplitzOp V S * V = daubechiesOp V S := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [daubechiesOp, toeplitzOp, fockProj]
    calc V * (star V * S * V)
      _ = V * star V * S * V * 1 := by noncomm_ring
      _ = V * star V * S * V * (star V * V) := by rw [hV]
      _ = (V * star V) * S * (V * star V) * V := by noncomm_ring
  · dsimp [daubechiesOp, toeplitzOp, fockProj]
    noncomm_ring
  · dsimp [daubechiesOp, toeplitzOp, fockProj]
    calc star V * ((V * star V) * S * (V * star V)) * V
      _ = (star V * V) * star V * S * V * (star V * V) := by noncomm_ring
      _ = 1 * star V * S * V * 1 := by rw [hV]
      _ = star V * S * V := by noncomm_ring

/-- Complementary pore resolution for Daubechies' localization operator: $P_S^\phi + P_{1 - S}^\phi = 1$. -/
theorem daubechiesOp_pore_partition {V : B} (hV : star V * V = 1) (S : B) :
    daubechiesOp V S + daubechiesOp V (1 - S) = 1 := by
  dsimp [daubechiesOp]
  calc star V * S * V + star V * (1 - S) * V
    _ = star V * V := by noncomm_ring
    _ = 1 := hV

end ArchetypeF2_DaubechiesToeplitzEquivalence

/-!
## Archetype $\mathcal{F}_3$: Knutsen's Inductive Porosity Thickening Recurrence & Uniform $\nu/2$ Lower Bound
(Lemma 3.4, Equation 3.9 & Page 11 Proof of Theorem 3.1 of Knutsen, `arXiv:2204.03068v1`)
-/

section ArchetypeF3_PorosityThickeningRecurrence

/-- Knutsen's $j$-th thickened porosity constant $\nu_j$ defined by Equation (3.9) with geometric
radii $R_k = c (3/\nu)^k$: $\nu_0 = \nu$ and $\nu_{j+1} = \nu_j - (\nu/3)^{j+1}$. -/
def knutsenPorosity (ν : ℚ) : ℕ → ℚ
  | 0 => ν
  | j + 1 => knutsenPorosity ν j - (ν / 3) ^ (j + 1)

/-- **Exact Closed-Form Algebraic Identity for Knutsen's Thickened Porosity $\nu_j$**:
For all $\nu \in \mathbb{Q}$ and all thickening iterations $j \in \mathbb{N}$,
$(3 - \nu) \nu_j = \nu (2 - \nu) + \nu (\nu / 3)^j$. -/
theorem knutsenPorosity_closed_form (ν : ℚ) (j : ℕ) :
    (3 - ν) * knutsenPorosity ν j = ν * (2 - ν) + ν * (ν / 3) ^ j := by
  induction' j with j ih
  · simp [knutsenPorosity]; ring
  · calc (3 - ν) * knutsenPorosity ν (j + 1)
      _ = (3 - ν) * knutsenPorosity ν j - (3 - ν) * (ν / 3) ^ (j + 1) := by
          rw [knutsenPorosity, mul_sub]
      _ = (ν * (2 - ν) + ν * (ν / 3) ^ j) - (3 - ν) * ((ν / 3) ^ j * (ν / 3)) := by
          rw [ih, pow_succ]
      _ = ν * (2 - ν) + ν * (ν / 3) ^ (j + 1) := by
          rw [pow_succ]; ring

/-- **Knutsen's Uniform Porosity Lower Bound (Page 11 of `arXiv:2204.03068v1`)**:
For every initial porosity $0 \le \nu \le 1$ and every multiscale thickening step $j \in \mathbb{N}$,
$\nu_j \ge \nu / 2$. -/
theorem knutsenPorosity_ge_half {ν : ℚ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (j : ℕ) :
    ν / 2 ≤ knutsenPorosity ν j := by
  have h_pos : 0 ≤ ν / 3 := by linarith
  have h_pow : 0 ≤ (ν / 3) ^ j := pow_nonneg h_pos j
  have h_prod1 : 0 ≤ ν * (ν / 3) ^ j := mul_nonneg hν0 h_pow
  have h_prod2 : 0 ≤ ν * (1 - ν) := mul_nonneg hν0 (by linarith)
  have h_id := knutsenPorosity_closed_form ν j
  have h_diff : (3 - ν) * (knutsenPorosity ν j - ν / 2) =
      ν * (1 - ν) / 2 + ν * (ν / 3) ^ j := by
    linear_combination h_id
  have h_rhs_nonneg : 0 ≤ (3 - ν) * (knutsenPorosity ν j - ν / 2) := by
    rw [h_diff]
    linarith
  have h_3_sub : 0 < 3 - ν := by linarith
  nlinarith

end ArchetypeF3_PorosityThickeningRecurrence

/-!
## Archetype $\mathcal{F}_4$: Noncommutative Gabor Frame Operators, Gabor Multipliers & Gram Matrix Duality
(Section 2.2 & Section 5, Equations 2.8, 2.10, 5.1 & Lemma 5.2 of Knutsen, `arXiv:2204.03068v1`)
-/

section ArchetypeF4_GaborFramesAndGramDuality

variable {B : Type*} [Ring B] [StarRing B] {m : ℕ}

/-- Noncommutative Gabor frame operator $\mathcal{S}_\Lambda^\phi = \sum_{\lambda=1}^m \phi_\lambda \phi_\lambda^\star$
(Equation 2.8). -/
def gaborFrameOp (φ : Fin m → B) : B :=
  ∑ i : Fin m, φ i * star (φ i)

/-- Noncommutative Gabor multiplier $\mathcal{G}_{\Lambda, b}^\phi = \sum_{\lambda=1}^m \phi_\lambda b(\lambda) \phi_\lambda^\star$
(Equations 2.10 & 5.1). -/
def gaborMultiplier (φ b : Fin m → B) : B :=
  ∑ i : Fin m, φ i * b i * star (φ i)

/-- Bargmann–Fock Gram matrix $\mathfrak{G}_{\lambda, \mu} = \phi_\lambda^\star \phi_\mu \in M_m(B)$
associated to the Gabor atoms $\{\phi_\lambda\}_{\lambda=1}^m$ (Lemma 5.2). -/
def gaborGramMatrix (φ : Fin m → B) : Matrix (Fin m) (Fin m) B :=
  Matrix.of (fun i j => star (φ i) * φ j)

/-- The Gabor frame operator $\mathcal{S}_\Lambda^\phi$ is strictly self-adjoint. -/
theorem gaborFrameOp_isSelfAdjoint (φ : Fin m → B) :
    star (gaborFrameOp φ) = gaborFrameOp φ := by
  dsimp [gaborFrameOp]
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [star_mul]

/-- Adjoint duality of Gabor multipliers: $(\mathcal{G}_{\Lambda, b}^\phi)^\star = \mathcal{G}_{\Lambda, b^\star}^\phi$. -/
theorem gaborMultiplier_star (φ b : Fin m → B) :
    star (gaborMultiplier φ b) = gaborMultiplier φ (fun i => star (b i)) := by
  dsimp [gaborMultiplier]
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [star_mul, mul_assoc]

/-- Porous complement partition of a Gabor multiplier:
$\mathcal{G}_{\Lambda, b}^\phi + \mathcal{G}_{\Lambda, 1 - b}^\phi = \mathcal{S}_\Lambda^\phi$. -/
theorem gaborMultiplier_pore_partition (φ b : Fin m → B) :
    gaborMultiplier φ b + gaborMultiplier φ (fun i => 1 - b i) = gaborFrameOp φ := by
  dsimp [gaborMultiplier, gaborFrameOp]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  noncomm_ring

/-- **Noncommutative Gram Matrix Duality (Lemma 5.2 of Knutsen)**:
The square of the Bargmann–Fock Gram matrix $\mathfrak{G}_\Lambda$ intertwines the Gabor frame operator:
$(\mathfrak{G}_\Lambda^2)_{i, j} = \phi_i^\star \mathcal{S}_\Lambda^\phi \phi_j$. -/
theorem gaborGramMatrix_sq_apply (φ : Fin m → B) (i j : Fin m) :
    (gaborGramMatrix φ * gaborGramMatrix φ) i j =
      star (φ i) * gaborFrameOp φ * φ j := by
  dsimp [gaborGramMatrix, gaborFrameOp]
  rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Matrix.of_apply]
  noncomm_ring

/-- For any Parseval Gabor frame ($\mathcal{S}_\Lambda^\phi = 1$), the Bargmann–Fock Gram matrix
$\mathfrak{G}_\Lambda \in M_m(B)$ is an idempotent projection ($\mathfrak{G}_\Lambda^2 = \mathfrak{G}_\Lambda$). -/
theorem gaborGramMatrix_idem_of_parseval {φ : Fin m → B} (h_parseval : gaborFrameOp φ = 1) :
    gaborGramMatrix φ * gaborGramMatrix φ = gaborGramMatrix φ := by
  ext i j
  rw [gaborGramMatrix_sq_apply, h_parseval, mul_one]
  rfl

end ArchetypeF4_GaborFramesAndGramDuality

/-!
## Archetype $\mathcal{F}_5$: Weyl–Heisenberg Discrete Gabor Frame & Porous Cantor Multiplier Contraction in $M_2(A)$
-/

section ArchetypeF5_WeylHeisenbergGaborFrameInM2

variable {A : Type*} [Ring A] [StarRing A]

lemma ext_fin2 {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

@[simp]
lemma mul_apply_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
lemma mul_apply_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one_apply_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one_apply_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one_apply_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one_apply_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp]
lemma of_fin2_00 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl
@[simp]
lemma of_fin2_01 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl
@[simp]
lemma of_fin2_10 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl
@[simp]
lemma of_fin2_11 (a b c d : A) :
    (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

@[simp]
lemma conjTranspose_apply_00 (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 0 = star (M 0 0) := rfl
@[simp]
lemma conjTranspose_apply_01 (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 1 = star (M 1 0) := rfl
@[simp]
lemma conjTranspose_apply_10 (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 0 = star (M 0 1) := rfl
@[simp]
lemma conjTranspose_apply_11 (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 1 = star (M 1 1) := rfl

/-- The 4 non-commuting Weyl–Heisenberg time-frequency shift operators $\{I, \Gamma_1, \Sigma, \Omega\} \subset M_2(A)$
and Peirce projections $P_+, P_-$. -/
def Γ₁ : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]
def Σ_op : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]
def Ω : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]
def P_plus : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := ![![a, 0], ![0, a]]

/-- **Weyl–Heisenberg Phase-Space Averaging Identity**:
Summing $\pi(\lambda) M \pi(\lambda)^\dagger$ over all 4 discrete time-frequency shifts
$\lambda \in \{I, \Gamma_1, \Sigma, \Omega\}$ projects any matrix $M \in M_2(A)$ onto $2 \mathrm{Tr}(M) \cdot I_2$. -/
theorem weyl_heisenberg_phase_space_averaging (M : Matrix (Fin 2) (Fin 2) A) :
    1 * M * (1 : Matrix (Fin 2) (Fin 2) A)ᴴ +
    Γ₁ * M * Γ₁ᴴ +
    Σ_op * M * Σ_opᴴ +
    Ω * M * Ωᴴ =
      fiberEmbed (2 * (M 0 0 + M 1 1)) := by
  apply ext_fin2 <;> simp [Γ₁, Σ_op, Ω, fiberEmbed] <;> noncomm_ring

/-- **Tight Weyl–Heisenberg Gabor Frame vs. Porous Cantor Gabor Multiplier Contraction**:
With the Peirce window $\phi_0 = P_+$, the 4-point Weyl–Heisenberg Gabor system forms a tight
frame with bound $2 I_2$, whereas localizing onto the $\nu = 1/2$ porous sublattice $\{I, \Sigma\}$
halves the operator to $1 \cdot I_2$, and localizing onto the Cantor branch $\{I\}$ contracts it to $P_+$. -/
theorem weyl_heisenberg_porous_gabor_contraction :
    ((1 * P_plus) * (1 * P_plus : Matrix (Fin 2) (Fin 2) A)ᴴ +
     (Γ₁ * P_plus) * (Γ₁ * P_plus)ᴴ +
     (Σ_op * P_plus) * (Σ_op * P_plus)ᴴ +
     (Ω * P_plus) * (Ω * P_plus)ᴴ = (1 : Matrix (Fin 2) (Fin 2) A) + 1) ∧
    ((1 * P_plus) * (1 * P_plus : Matrix (Fin 2) (Fin 2) A)ᴴ +
     (Σ_op * P_plus) * (Σ_op * P_plus)ᴴ = 1) ∧
    ((1 * P_plus) * (1 * P_plus : Matrix (Fin 2) (Fin 2) A)ᴴ = P_plus) := by
  refine ⟨?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [Γ₁, Σ_op, Ω, P_plus]
  · apply ext_fin2 <;> simp [Σ_op, P_plus]
  · apply ext_fin2 <;> simp [P_plus]

end ArchetypeF5_WeylHeisenbergGaborFrameInM2

end KnutsenFractalUncertaintyAndGaborMultipliers
```

## Turn 0024, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace GrandUnifiedNoncommutativeOperatorSynthesis

/-!
## Archetype $\mathcal{A}_1$: Associative Lie Envelope & Quadratic Exponential Jet Obstruction
-/

section ArchetypeA1_AssociativeJetObstruction

variable {B : Type*} [Ring B]

def expJet2 (X : B) : B := 2 + 2 * X + X * X

theorem bch_jet2_commutator_obstruction (X Y : B) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X =
      4 * ⁅X, Y⁆ +
      2 * (X * X * Y - Y * (X * X) + X * (Y * Y) - Y * Y * X) +
      (X * X * (Y * Y) - Y * Y * (X * X)) := by
  dsimp [expJet2]; rw [Ring.lie_def]; noncomm_ring

theorem bch_jet2_nilpotent_commutator {X Y : B} (hX : X * X = 0) (hY : Y * Y = 0) :
    expJet2 X * expJet2 Y - expJet2 Y * expJet2 X = 4 * ⁅X, Y⁆ := by
  rw [bch_jet2_commutator_obstruction, hX, hY]; noncomm_ring

end ArchetypeA1_AssociativeJetObstruction

/-!
## Archetype $\mathcal{A}_2$: Brauer–Weyl $(1,1)$-Periodicity, Witt CAR Ladder & Quaternion Triple in $M_2(M_2(B))$
-/

section ArchetypeA2_BrauerWeylQuaternionChain

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Infrastructure

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma of2_00 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl
@[simp] lemma of2_01 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl
@[simp] lemma of2_10 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl
@[simp] lemma of2_11 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

def Σ_op    : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]
def Ω_op    : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]
def Γ₁_op   : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]
def P_plus  : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]
def F_plus  : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![0, 0]]
def F_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![1, 0]]

def fiberEmbed (x : A) : Matrix (Fin 2) (Fin 2) A := ![![x, 0], ![0, x]]
def kleinTwist (x : A) : Matrix (Fin 2) (Fin 2) A := ![![x, 0], ![0, -x]]

theorem cl11_and_witt_car_relations :
    (Σ_op : Matrix (Fin 2) (Fin 2) A) * Σ_op = 1 ∧
    (Ω_op : Matrix (Fin 2) (Fin 2) A) * Ω_op = -1 ∧
    (Σ_op : Matrix (Fin 2) (Fin 2) A) * Ω_op = Γ₁_op ∧
    anticomm (Σ_op : Matrix (Fin 2) (Fin 2) A) Ω_op = 0 ∧
    (F_plus : Matrix (Fin 2) (Fin 2) A) * F_plus = 0 ∧
    (F_minus : Matrix (Fin 2) (Fin 2) A) * F_minus = 0 ∧
    anticomm (F_plus : Matrix (Fin 2) (Fin 2) A) F_minus = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> simp [Σ_op, Ω_op, Γ₁_op, F_plus, F_minus, anticomm])

theorem brauer_weyl_periodicity_step {e₁ e₂ s₁ s₂ : A}
    (he₁ : e₁ * e₁ = s₁) (he₂ : e₂ * e₂ = s₂) (h_anti : anticomm e₁ e₂ = 0) :
    kleinTwist e₁ * kleinTwist e₁ = fiberEmbed s₁ ∧
    kleinTwist e₂ * kleinTwist e₂ = fiberEmbed s₂ ∧
    anticomm (kleinTwist e₁) (Σ_op : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₂) (Σ_op : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₁) (Ω_op : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₂) (Ω_op : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    anticomm (kleinTwist e₁) (kleinTwist e₂) = 0 := by
  have h0 : ∀ x y : A, kleinTwist x * kleinTwist y = fiberEmbed (x * y) := fun x y => by
    apply ext_fin2 <;> simp [kleinTwist, fiberEmbed]
  have hA : anticomm (kleinTwist e₁) (kleinTwist e₂) = fiberEmbed (anticomm e₁ e₂) := by
    apply ext_fin2 <;> simp [anticomm, kleinTwist, fiberEmbed]
  refine ⟨by rw [h0, he₁], by rw [h0, he₂], ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [anticomm, kleinTwist, Σ_op]
  · apply ext_fin2 <;> simp [anticomm, kleinTwist, Σ_op]
  · apply ext_fin2 <;> simp [anticomm, kleinTwist, Ω_op]
  · apply ext_fin2 <;> simp [anticomm, kleinTwist, Ω_op]
  · rw [hA, h_anti]; apply ext_fin2 <;> simp [fiberEmbed]

end Matrix2Infrastructure

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

def E₁ {B : Type*} [Ring B] : NestedMat B := Ω_op
def E₂ {B : Type*} [Ring B] : NestedMat B := kleinTwist Ω_op
def E₃ {B : Type*} [Ring B] : NestedMat B := (E₁ : NestedMat B) * E₂

/-- Embedded quaternion Lie subalgebra $\mathfrak{sp}(1) \subset M_2(M_2(B))$ over any `[Ring B]`. -/
theorem nested_quaternion_lie_relations {B : Type*} [Ring B] :
    (E₁ : NestedMat B) * E₁ = -1 ∧
    (E₂ : NestedMat B) * E₂ = -1 ∧
    (E₃ : NestedMat B) * E₃ = -1 ∧
    anticomm (E₁ : NestedMat B) E₂ = 0 ∧
    ⁅(E₁ : NestedMat B), E₂⁆ = 2 * E₃ ∧
    ⁅(E₂ : NestedMat B), E₃⁆ = 2 * E₁ ∧
    ⁅(E₃ : NestedMat B), E₁⁆ = 2 * E₂ := by
  have h1 : (E₁ : NestedMat B) * E₁ = -1 := cl11_and_witt_car_relations.2.1
  have hstep := brauer_weyl_periodicity_step (A := Matrix (Fin 2) (Fin 2) B)
    cl11_and_witt_car_relations.1 cl11_and_witt_car_relations.2.1
    cl11_and_witt_car_relations.2.2.2.1
  have h2 : (E₂ : NestedMat B) * E₂ = -1 := by
    dsimp [E₂]; rw [hstep.2.1]; apply ext_fin2 <;> simp [fiberEmbed]
  have h12_anti : anticomm (E₁ : NestedMat B) E₂ = 0 := by
    dsimp [anticomm, E₁, E₂]
    have ha := hstep.2.2.2.2.2.1
    dsimp [anticomm] at ha
    calc (Ω_op : NestedMat B) * kleinTwist Ω_op + kleinTwist Ω_op * Ω_op
      _ = kleinTwist Ω_op * Ω_op + Ω_op * kleinTwist Ω_op := by abel
      _ = 0 := ha
  have h21 : (E₂ : NestedMat B) * E₁ = - ((E₁ : NestedMat B) * E₂) := by
    dsimp [anticomm] at h12_anti
    calc (E₂ : NestedMat B) * E₁
      _ = (E₁ * E₂ + E₂ * E₁) - E₁ * E₂ := by abel
      _ = 0 - E₁ * E₂ := by rw [h12_anti]
      _ = - (E₁ * E₂) := zero_sub _
  have h3 : (E₃ : NestedMat B) * E₃ = -1 := by
    calc (E₃ : NestedMat B) * E₃
      _ = E₁ * (E₂ * E₁) * E₂ := by dsimp [E₃]; noncomm_ring
      _ = E₁ * (- (E₁ * E₂)) * E₂ := by rw [h21]
      _ = - ((E₁ * E₁) * (E₂ * E₂)) := by noncomm_ring
      _ = - ((-1) * (-1)) := by rw [h1, h2]
      _ = -1 := by noncomm_ring
  refine ⟨h1, h2, h3, h12_anti, ?_, ?_, ?_⟩
  · rw [Ring.lie_def, h21]; dsimp [E₃]; noncomm_ring
  · rw [Ring.lie_def]; dsimp [E₃]
    calc E₂ * (E₁ * E₂) - E₁ * E₂ * E₂
      _ = (E₂ * E₁) * E₂ - E₁ * (E₂ * E₂) := by noncomm_ring
      _ = (- (E₁ * E₂)) * E₂ - E₁ * (-1) := by rw [h21, h2]
      _ = - (E₁ * (E₂ * E₂)) + E₁ := by noncomm_ring
      _ = - (E₁ * (-1)) + E₁ := by rw [h2]
      _ = 2 * E₁ := by noncomm_ring
  · rw [Ring.lie_def]; dsimp [E₃]
    calc E₁ * E₂ * E₁ - E₁ * (E₁ * E₂)
      _ = E₁ * (E₂ * E₁) - (E₁ * E₁) * E₂ := by noncomm_ring
      _ = E₁ * (- (E₁ * E₂)) - (-1) * E₂ := by rw [h21, h1]
      _ = - ((E₁ * E₁) * E₂) + E₂ := by noncomm_ring
      _ = - ((-1) * E₂) + E₂ := by rw [h1]
      _ = 2 * E₂ := by noncomm_ring

end ArchetypeA2_BrauerWeylQuaternionChain

/-!
## Archetype $\mathcal{A}_3$: Noncommutative Ring Derivations, Matrix Lifting & Unit-Inverse Rule
-/

section ArchetypeA3_NoncommutativeDerivations

def IsRingDeriv {B : Type*} [Ring B] (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

theorem IsRingDeriv.map_one {B : Type*} [Ring B] {d : B →+ B} (hd : IsRingDeriv d) :
    d 1 = 0 := by
  have h : d (1 * 1) = d 1 * 1 + 1 * d 1 := hd 1 1
  simp only [mul_one, one_mul] at h
  calc d 1 = d 1 + d 1 - d 1 := by abel
    _ = d 1 - d 1 := by rw [← h]
    _ = 0 := sub_self (d 1)

theorem IsRingDeriv.map_units_inv {B : Type*} [Ring B] {d : B →+ B}
    (hd : IsRingDeriv d) (u : Bˣ) :
    d (↑u⁻¹ : B) = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by
  have h1 : d ((u : B) * (↑u⁻¹ : B)) = d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B) :=
    hd (u : B) (↑u⁻¹ : B)
  rw [Units.mul_inv, hd.map_one] at h1
  have h2 : (↑u⁻¹ : B) * (d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑u⁻¹ : B) * (u : B) * d (↑u⁻¹ : B) = d (↑u⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc d (↑u⁻¹ : B)
    _ = (↑u⁻¹ : B) * (u : B) * d (↑u⁻¹ : B) -
        (↑u⁻¹ : B) * (d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by noncomm_ring

def liftMatrixDeriv {S : Type*} [Ring S] {n : Type*} [Fintype n] [DecidableEq n]
    (d : S →+ S) : Matrix n n S →+ Matrix n n S where
  toFun M i j := d (M i j)
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; simp

theorem IsRingDeriv.liftMatrix {S : Type*} [Ring S] {n : Type*} [Fintype n] [DecidableEq n]
    {d : S →+ S} (hd : IsRingDeriv d) :
    IsRingDeriv (liftMatrixDeriv (n := n) d) := by
  intro M N; ext i k
  simp only [liftMatrixDeriv, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply,
    Matrix.mul_apply, map_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => hd (M i j) (N j k))

end ArchetypeA3_NoncommutativeDerivations

/-!
## Archetype $\mathcal{A}_4$: Koszul Connections, Maurer–Cartan Curvature, Bianchi Identity & Chern–Simons–Weil Transgression
-/

section ArchetypeA4_KoszulMaurerCartanAndChernSimons

variable {B : Type*} [Ring B]

def covOp (d : B →+ B) (A ψ : B) : B := d ψ + A * ψ
def mcCurvature (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B := d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆
def dressConn (d : B →+ B) (u : Bˣ) (A : B) : B := (u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)
def adjDeriv (d : B →+ B) (A X : B) : B := d X + ⁅A, X⁆

theorem koszul_curvature_multiplication
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (A₁ A₂ ψ : B) :
    covOp d₁ A₁ (covOp d₂ A₂ ψ) - covOp d₂ A₂ (covOp d₁ A₁ ψ) =
      mcCurvature d₁ d₂ A₁ A₂ * ψ := by
  dsimp [covOp, mcCurvature]
  rw [Ring.lie_def, map_add, map_add, hd₁ A₂ ψ, hd₂ A₁ ψ, h_comm ψ]; noncomm_ring

theorem koszul_dressing_intertwining
    {d : B →+ B} (hd : IsRingDeriv d) (u : Bˣ) (A ψ : B) :
    covOp d (dressConn d u A) ((u : B) * ψ) = (u : B) * covOp d A ψ := by
  dsimp [covOp, dressConn]; rw [hd (u : B) ψ]
  have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  calc d (u : B) * ψ + (u : B) * d ψ +
        ((u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)) * ((u : B) * ψ)
    _ = d (u : B) * ψ + (u : B) * d ψ +
        (u : B) * A * ((↑u⁻¹ : B) * (u : B)) * ψ -
        d (u : B) * ((↑u⁻¹ : B) * (u : B)) * ψ := by noncomm_ring
    _ = d (u : B) * ψ + (u : B) * d ψ + (u : B) * A * 1 * ψ - d (u : B) * 1 * ψ := by rw [hu]
    _ = (u : B) * (d ψ + A * ψ) := by noncomm_ring

theorem maurer_cartan_conjugation_covariance
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) (A₁ A₂ : B) :
    mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) =
      (u : B) * mcCurvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by
  have h_lhs := koszul_curvature_multiplication hd₁ hd₂ h_comm
    (dressConn d₁ u A₁) (dressConn d₂ u A₂) ((u : B) * 1)
  rw [koszul_dressing_intertwining hd₂ u A₂ 1,
      koszul_dressing_intertwining hd₁ u A₁ (covOp d₂ A₂ 1),
      koszul_dressing_intertwining hd₁ u A₁ 1,
      koszul_dressing_intertwining hd₂ u A₂ (covOp d₁ A₁ 1)] at h_lhs
  have h_rhs := koszul_curvature_multiplication hd₁ hd₂ h_comm A₁ A₂ 1
  have h_comb : mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * (u : B) =
      (u : B) * mcCurvature d₁ d₂ A₁ A₂ := by
    calc mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * (u : B)
      _ = mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * ((u : B) * 1) := by rw [mul_one]
      _ = (u : B) * covOp d₁ A₁ (covOp d₂ A₂ 1) -
          (u : B) * covOp d₂ A₂ (covOp d₁ A₁ 1) := h_lhs.symm
      _ = (u : B) * (covOp d₁ A₁ (covOp d₂ A₂ 1) - covOp d₂ A₂ (covOp d₁ A₁ 1)) := by noncomm_ring
      _ = (u : B) * (mcCurvature d₁ d₂ A₁ A₂ * 1) := by rw [h_rhs]
      _ = (u : B) * mcCurvature d₁ d₂ A₁ A₂ := by rw [mul_one]
  calc mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂)
    _ = mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * ((u : B) * (↑u⁻¹ : B)) := by
        rw [Units.mul_inv, mul_one]
    _ = (mcCurvature d₁ d₂ (dressConn d₁ u A₁) (dressConn d₂ u A₂) * (u : B)) * (↑u⁻¹ : B) := by
        noncomm_ring
    _ = (u : B) * mcCurvature d₁ d₂ A₁ A₂ * (↑u⁻¹ : B) := by rw [h_comb]

theorem logarithmic_coboundary_flatness
    {d₁ d₂ : B →+ B} (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂)
    (h_comm : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x)) (u : Bˣ) :
    mcCurvature d₁ d₂ (-d₁ (u : B) * (↑u⁻¹ : B)) (-d₂ (u : B) * (↑u⁻¹ : B)) = 0 := by
  have h1 : -d₁ (u : B) * (↑u⁻¹ : B) = dressConn d₁ u 0 := by dsimp [dressConn]; noncomm_ring
  have h2 : -d₂ (u : B) * (↑u⁻¹ : B) = dressConn d₂ u 0 := by dsimp [dressConn]; noncomm_ring
  rw [h1, h2, maurer_cartan_conjugation_covariance hd₁ hd₂ h_comm u 0 0]
  dsimp [mcCurvature]; rw [Ring.lie_def, map_zero, map_zero]; noncomm_ring

theorem differential_bianchi_identity
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    adjDeriv d₁ A₁ (mcCurvature d₂ d₃ A₂ A₃) +
    adjDeriv d₂ A₂ (mcCurvature d₃ d₁ A₃ A₁) +
    adjDeriv d₃ A₃ (mcCurvature d₁ d₂ A₁ A₂) = 0 := by
  dsimp [adjDeriv, mcCurvature]
  simp only [Ring.lie_def, map_add, map_sub]
  rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
      h12 A₃, h13 A₂, h23 A₁, ← h12 A₃, ← h13 A₂, ← h23 A₁]
  noncomm_ring

theorem uncovariantized_exterior_remainder
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    d₁ (mcCurvature d₂ d₃ A₂ A₃) + d₂ (mcCurvature d₃ d₁ A₃ A₁) + d₃ (mcCurvature d₁ d₂ A₁ A₂) =
      ⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ + ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆ := by
  have h := differential_bianchi_identity hd₁ hd₂ hd₃ h12 h23 h13 A₁ A₂ A₃
  calc d₁ (mcCurvature d₂ d₃ A₂ A₃) + d₂ (mcCurvature d₃ d₁ A₃ A₁) + d₃ (mcCurvature d₁ d₂ A₁ A₂)
    _ = (adjDeriv d₁ A₁ (mcCurvature d₂ d₃ A₂ A₃) +
         adjDeriv d₂ A₂ (mcCurvature d₃ d₁ A₃ A₁) +
         adjDeriv d₃ A₃ (mcCurvature d₁ d₂ A₁ A₂)) +
        (⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
         ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆) := by
          dsimp [adjDeriv]; simp only [Ring.lie_def]; noncomm_ring
    _ = 0 + (⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
             ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆) := by rw [h]
    _ = ⁅mcCurvature d₂ d₃ A₂ A₃, A₁⁆ + ⁅mcCurvature d₃ d₁ A₃ A₁, A₂⁆ +
        ⁅mcCurvature d₁ d₂ A₁ A₂, A₃⁆ := zero_add _

/-- Noncommutative Chern–Simons cubic element $\mathcal{CS}(\Phi, D) = \Phi D + D\Phi + D^3$. -/
def chernSimonsElem (Φ D : B) : B := Φ * D + D * Φ + D * D * D
def superCurvature (Φ D : B) : B := Φ + D * D

theorem chern_simons_weil_transgression (Φ D : B) :
    anticomm D (chernSimonsElem Φ D) - ⁅⁅D, Φ⁆, D⁆ + 2 * (Φ * Φ) =
      2 * (superCurvature Φ D * superCurvature Φ D) := by
  dsimp [anticomm, chernSimonsElem, superCurvature]
  simp only [Ring.lie_def]
  noncomm_ring

end ArchetypeA4_KoszulMaurerCartanAndChernSimons

/-!
## Archetype $\mathcal{A}_5$: Gerbe-Twisted Operator Bundles, Period-Rank Torsion & Gerbe Flatness
-/

section ArchetypeA5_GerbeTwistedBundlesAndTorsion

variable {B : Type*} [Ring B]

def gerbeEmbed (r : ℕ) (b : B) : Matrix (Fin r) (Fin r) B :=
  Matrix.of (fun i j => if i = j then b else 0)

def ncTrace {r : ℕ} (M : Matrix (Fin r) (Fin r) B) : B :=
  ∑ i : Fin r, M i i

def twistedBundleCurvature {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B) :
    Matrix (Fin r) (Fin r) B :=
  mcCurvature (liftMatrixDeriv d₁) (liftMatrixDeriv d₂) A₁ A₂ + gerbeEmbed r B_gerbe

theorem ncTrace_gerbeEmbed (r : ℕ) (b : B) :
    ncTrace (gerbeEmbed r b) = r • b := by
  dsimp [ncTrace, gerbeEmbed]; simp [Finset.sum_const, Finset.card_fin]

theorem projectively_flat_torsion_anomaly {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B)
    (h_flat : twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe = 0) :
    r • B_gerbe = -(d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) := by
  have h_tr : ncTrace (twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe) = 0 := by
    rw [h_flat]; dsimp [ncTrace]; simp
  have h_decomp : ncTrace (twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe) =
      (d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) + r • B_gerbe := by
    dsimp [twistedBundleCurvature, mcCurvature, ncTrace, liftMatrixDeriv]
    simp only [Matrix.add_apply, Matrix.sub_apply, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, map_sum, ← ncTrace_gerbeEmbed r B_gerbe]
    rfl
  rw [h_decomp] at h_tr
  exact eq_neg_of_add_eq_zero_right h_tr

theorem projectively_flat_implies_gerbe_flat
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    {A₁ A₂ A₃ B₂₃ B₃₁ B₁₂ : B}
    (h_flat₂₃ : mcCurvature d₂ d₃ A₂ A₃ + B₂₃ = 0)
    (h_flat₃₁ : mcCurvature d₃ d₁ A₃ A₁ + B₃₁ = 0)
    (h_flat₁₂ : mcCurvature d₁ d₂ A₁ A₂ + B₁₂ = 0)
    (h_comm₁ : ⁅A₁, B₂₃⁆ = 0) (h_comm₂ : ⁅A₂, B₃₁⁆ = 0) (h_comm₃ : ⁅A₃, B₁₂⁆ = 0) :
    d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂ = 0 := by
  have h_b := differential_bianchi_identity hd₁ hd₂ hd₃ h12 h23 h13 A₁ A₂ A₃
  have hF₂₃ : mcCurvature d₂ d₃ A₂ A₃ = -B₂₃ := eq_neg_of_add_eq_zero_left h_flat₂₃
  have hF₃₁ : mcCurvature d₃ d₁ A₃ A₁ = -B₃₁ := eq_neg_of_add_eq_zero_left h_flat₃₁
  have hF₁₂ : mcCurvature d₁ d₂ A₁ A₂ = -B₁₂ := eq_neg_of_add_eq_zero_left h_flat₁₂
  rw [hF₂₃, hF₃₁, hF₁₂] at h_b
  dsimp [adjDeriv] at h_b
  simp only [ map_neg] at h_b
  have hc₁ : ⁅A₁, -B₂₃⁆ = 0 := by rw [Ring.lie_def] at h_comm₁ ⊢; noncomm_ring [h_comm₁]
  have hc₂ : ⁅A₂, -B₃₁⁆ = 0 := by rw [Ring.lie_def] at h_comm₂ ⊢; noncomm_ring [h_comm₂]
  have hc₃ : ⁅A₃, -B₁₂⁆ = 0 := by rw [Ring.lie_def] at h_comm₃ ⊢; noncomm_ring [h_comm₃]
  rw [hc₁, hc₂, hc₃, add_zero, add_zero, add_zero] at h_b
  calc d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂
    _ = -(-d₁ B₂₃ + -d₂ B₃₁ + -d₃ B₁₂) := by abel
    _ = -0 := by rw [h_b]
    _ = 0 := neg_zero

end ArchetypeA5_GerbeTwistedBundlesAndTorsion

/-!
## Archetype $\mathcal{A}_6$: Twisted Group Braiding $ZX = QXZ$ & 1-Cocycle Cohomology
-/

section ArchetypeA6_TwistedGroupCocycle

variable {G : Type*} [Group G]

def conjBy (x q : G) : G := x * q * x⁻¹

def twistedCocycle (X Q : G) : ℕ → G
  | 0 => 1
  | n + 1 => Q * conjBy X (twistedCocycle X Q n)

theorem braided_pow_law {X Z Q : G} (h_braid : Z * X = Q * X * Z) (n : ℕ) :
    Z * X ^ n = twistedCocycle X Q n * X ^ n * Z := by
  induction' n with n ih
  · simp [twistedCocycle]
  · calc Z * X ^ (n + 1)
      _ = (Z * X) * X ^ n := by rw [pow_succ', mul_assoc]
      _ = (Q * X * Z) * X ^ n := by rw [h_braid]
      _ = Q * X * (Z * X ^ n) := by group
      _ = Q * X * (twistedCocycle X Q n * X ^ n * Z) := by rw [ih]
      _ = (Q * (X * twistedCocycle X Q n * X⁻¹)) * (X * X ^ n) * Z := by group
      _ = twistedCocycle X Q (n + 1) * X ^ (n + 1) * Z := by
          rw [twistedCocycle, conjBy, ← pow_succ']

theorem twistedCocycle_add (X Q : G) (m n : ℕ) :
    twistedCocycle X Q (m + n) =
      twistedCocycle X Q m * conjBy (X ^ m) (twistedCocycle X Q n) := by
  induction' m with m ih
  · simp [twistedCocycle, conjBy]
  · have h_add : m + 1 + n = (m + n) + 1 := by omega
    rw [h_add, twistedCocycle, ih, twistedCocycle]
    dsimp [conjBy]; rw [pow_succ']; group

theorem twistedCocycle_torsion_obstruction {X Z Q : G}
    (h_braid : Z * X = Q * X * Z) {N : ℕ} (hXN : X ^ N = 1) :
    twistedCocycle X Q N = 1 := by
  have h := braided_pow_law h_braid N
  rw [hXN, mul_one, mul_one] at h
  calc twistedCocycle X Q N
    _ = (twistedCocycle X Q N * Z) * Z⁻¹ := by group
    _ = Z * Z⁻¹ := by rw [← h]
    _ = 1 := by group

end ArchetypeA6_TwistedGroupCocycle

/-!
## Archetype $\mathcal{A}_7$: Universal Jordan-Parabolic Block Monodromy $Q_{\mathrm{blk}} = 1 + \mathcal{N}_{\mathrm{blk}}$ over Arbitrary `[Ring B]`
-/

section ArchetypeA7_UniversalParabolicBlockMonodromy

variable {B : Type*} [Ring B]

def N_plus  : Matrix (Fin 2) (Fin 2) B := ![![-1, -1], ![1, 1]]
def G_link  : Matrix (Fin 2) (Fin 2) B := 1 + F_plus
def Gi_link : Matrix (Fin 2) (Fin 2) B := 1 - F_plus

def X_blk : NestedMat B := ![![0, Gi_link], ![G_link, 0]]
def Z_blk : NestedMat B := ![![Σ_op, 0], ![0, Γ₁_op]]
def N_blk : NestedMat B := ![![N_plus, 0], ![0, -F_minus]]
def Q_blk : NestedMat B := (Z_blk * X_blk) * (Z_blk * X_blk)

theorem X_blk_sq : (X_blk : NestedMat B) * X_blk = 1 := by
  apply ext_fin2 <;> apply ext_fin2 <;> simp [X_blk, G_link, Gi_link, F_plus]

theorem Z_blk_sq : (Z_blk : NestedMat B) * Z_blk = 1 := by
  apply ext_fin2 <;> apply ext_fin2 <;> simp [Z_blk, Σ_op, Γ₁_op]

theorem Q_blk_eq_one_add_N_blk : (Q_blk : NestedMat B) = 1 + N_blk := by
  apply ext_fin2 <;> apply ext_fin2 <;>
    simp [Q_blk, Z_blk, X_blk, G_link, Gi_link, Σ_op, Γ₁_op, F_plus, F_minus, N_blk, N_plus] <;>
    abel

theorem N_blk_sq_zero : (N_blk : NestedMat B) * N_blk = 0 := by
  apply ext_fin2 <;> apply ext_fin2 <;> simp [N_blk, N_plus, F_minus]

theorem X_blk_conj_N_blk : (X_blk : NestedMat B) * N_blk * X_blk = -N_blk := by
  apply ext_fin2 <;> apply ext_fin2 <;>
    simp [X_blk, G_link, Gi_link, F_plus, F_minus, N_blk, N_plus] <;>
    abel

theorem Z_blk_conj_N_blk : (Z_blk : NestedMat B) * N_blk * Z_blk = -N_blk := by
  apply ext_fin2 <;> apply ext_fin2 <;>
    simp [Z_blk, Σ_op, Γ₁_op, F_minus, N_blk, N_plus] <;>
    abel

/-- **Universal Non-Abelian Block Braiding & Dihedral 1-Cocycle Closure over any `[Ring B]`**:
$Z_{\mathrm{blk}} X_{\mathrm{blk}} = Q_{\mathrm{blk}} X_{\mathrm{blk}} Z_{\mathrm{blk}}$ and
$Q_{\mathrm{blk}} (X_{\mathrm{blk}} Q_{\mathrm{blk}} X_{\mathrm{blk}}) = 1$. -/
theorem universal_block_braiding_and_cocycle_closure :
    (Z_blk : NestedMat B) * X_blk = Q_blk * X_blk * Z_blk ∧
    (Q_blk : NestedMat B) * (X_blk * Q_blk * X_blk) = 1 ∧
    (Z_blk * Q_blk * Z_blk) * (Q_blk : NestedMat B) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · symm
    calc (Q_blk : NestedMat B) * X_blk * Z_blk
      _ = Z_blk * X_blk * Z_blk * (X_blk * X_blk) * Z_blk := by dsimp [Q_blk]; noncomm_ring
      _ = Z_blk * X_blk * (Z_blk * Z_blk) := by rw [X_blk_sq]; noncomm_ring
      _ = Z_blk * X_blk := by rw [Z_blk_sq]; noncomm_ring
  · calc (Q_blk : NestedMat B) * (X_blk * Q_blk * X_blk)
      _ = (1 + N_blk) * (X_blk * (1 + N_blk) * X_blk) := by rw [Q_blk_eq_one_add_N_blk]
      _ = (1 + N_blk) * (X_blk * X_blk + X_blk * N_blk * X_blk) := by noncomm_ring
      _ = (1 + N_blk) * (1 + -N_blk) := by rw [X_blk_sq, X_blk_conj_N_blk]
      _ = 1 - N_blk * N_blk := by noncomm_ring
      _ = 1 := by rw [N_blk_sq_zero, sub_zero]
  · calc (Z_blk * (Q_blk : NestedMat B) * Z_blk) * Q_blk
      _ = (Z_blk * (1 + N_blk) * Z_blk) * (1 + N_blk) := by rw [Q_blk_eq_one_add_N_blk]
      _ = (Z_blk * Z_blk + Z_blk * N_blk * Z_blk) * (1 + N_blk) := by noncomm_ring
      _ = (1 + -N_blk) * (1 + N_blk) := by rw [Z_blk_sq, Z_blk_conj_N_blk]
      _ = 1 - N_blk * N_blk := by noncomm_ring
      _ = 1 := by rw [N_blk_sq_zero, sub_zero]

/-- **Universal Jordan-Parabolic Power Law over any `[Ring B]`**:
For every $n \in \mathbb{N}$, $Q_{\mathrm{blk}}^n = 1 + n \bullet \mathcal{N}_{\mathrm{blk}}$. -/
theorem universal_Q_blk_pow (n : ℕ) :
    (Q_blk : NestedMat B) ^ n = 1 + n • N_blk := by
  induction' n with n ih
  · simp
  · rw [pow_succ, ih, Q_blk_eq_one_add_N_blk, add_nsmul, one_nsmul]
    have h_mul : (n • (N_blk : NestedMat B)) * N_blk = 0 := by
      rw [nsmul_eq_mul, mul_assoc, N_blk_sq_zero, mul_zero]
    calc (1 + n • (N_blk : NestedMat B)) * (1 + N_blk)
      _ = 1 + (n • N_blk + N_blk) + (n • N_blk) * N_blk := by noncomm_ring
      _ = 1 + (n • N_blk + N_blk) := by rw [h_mul, add_zero]

/-- **Infinite Multiplicative Order of $Q_{\mathrm{blk}}$ over any Characteristic-Zero Noncommutative Ring**:
Despite $X_{\mathrm{blk}}^2 = 1$ and $Z_{\mathrm{blk}}^2 = 1$, $Q_{\mathrm{blk}}^n \neq 1$ for all $n > 0$. -/
theorem universal_Q_blk_infinite_order [CharZero B] (n : ℕ) (hn : 0 < n) :
    (Q_blk : NestedMat B) ^ n ≠ 1 := by
  intro h_eq
  have h_entry : (((Q_blk : NestedMat B) ^ n) 0 0) 1 0 = ((1 : NestedMat B) 0 0) 1 0 := by
    rw [h_eq]
  rw [universal_Q_blk_pow] at h_entry
  simp [N_blk, N_plus] at h_entry
  exact Nat.ne_of_gt hn h_entry

end ArchetypeA7_UniversalParabolicBlockMonodromy

/-!
## Archetype $\mathcal{A}_8$: Coordinate-Free Clifford–Mellin–Walsh Convolution & Fractal Uncertainty Variance
-/

section ArchetypeA8_CliffordMellinAndFUPVariance

variable {A : Type*} [Ring A]

def peirceFiberLift (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * X * P_plus + Σ_op * P_plus * X * P_plus * Σ_op

def mellinCoeff_I (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M + Σ_op * M * Σ_op)
def mellinCoeff_Γ (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M - Σ_op * M * Σ_op)
def mellinCoeff_Σ (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M * Σ_op + Σ_op * M)
def mellinCoeff_Ω (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (Σ_op * M - M * Σ_op)

theorem clifford_mellin_walsh_inversion (M : Matrix (Fin 2) (Fin 2) A) :
    mellinCoeff_I M * 1 +
    mellinCoeff_Γ M * Γ₁_op +
    mellinCoeff_Σ M * Σ_op +
    mellinCoeff_Ω M * Ω_op = M + M := by
  apply ext_fin2 <;>
    simp [mellinCoeff_I, mellinCoeff_Γ, mellinCoeff_Σ, mellinCoeff_Ω,
      peirceFiberLift, P_plus, Γ₁_op, Σ_op, Ω_op] <;>
    noncomm_ring

/-- **Fractal Uncertainty Commutator Variance Identity**:
In any $\star$-ring $R$, the idempotency defect $PQP - (PQP)^2$ of two non-commuting projections
$P, Q \in R$ equals both the pore leakage and the compressed square of the Lie commutator $\⁅P, Q⁆$. -/
theorem fup_projection_variance_eq_commutator_sq {R : Type*} [Ring R] [StarRing R]
    {P Q : R} (hP_idem : P * P = P) (hP_sa : star P = P)
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    P * Q * P - (P * Q * P) * (P * Q * P) =
      (P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P) := by
  have h1P : (1 - P) * (1 - P) = 1 - P := by
    calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP_idem]; noncomm_ring
  have h_comm : ⁅P, Q⁆ * P = -((1 - P) * Q * P) := by
    rw [Ring.lie_def]
    calc (P * Q - Q * P) * P = P * Q * P - Q * (P * P) := by noncomm_ring
      _ = P * Q * P - Q * P := by rw [hP_idem]
      _ = -((1 - P) * Q * P) := by noncomm_ring
  have h_star : P * star ⁅P, Q⁆ = -star ((1 - P) * Q * P) := by
    calc P * star ⁅P, Q⁆ = star (⁅P, Q⁆ * P) := by simp [star_mul, hP_sa]
      _ = -star ((1 - P) * Q * P) := by rw [h_comm, star_neg]
  rw [h_comm, h_star, neg_mul_neg]
  simp only [star_mul, star_sub, star_one, hP_sa, hQ_sa]
  calc P * Q * P - (P * Q * P) * (P * Q * P)
    _ = P * (Q * Q) * P - P * Q * (P * P) * Q * P := by rw [hQ_idem, hP_idem]; noncomm_ring
    _ = P * Q * (1 - P) * Q * P := by noncomm_ring
    _ = P * Q * ((1 - P) * (1 - P)) * Q * P := by rw [h1P]
    _ = P * Q * (1 - P) * ((1 - P) * Q * P) := by noncomm_ring

end ArchetypeA8_CliffordMellinAndFUPVariance

/-!
## Archetype $\mathcal{A}_9$: Master Synthesis — Clifford–Artin Braid Group & Maurer–Cartan Curvature in $M_2(M_2(B))$
-/

section ArchetypeA9_MasterSynthesis

theorem clifford_bivector_triple_product {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = 2 * (E₁₂ + E₂₃) := by
  have h12' : E₁₂ * E₁₂ + 1 = 0 := by rw [h12]; abel
  calc (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂)
    _ = 2 * (E₁₂ + E₂₃) + (E₁₂ * E₁₂ + 1) * (1 - E₂₃) +
        (1 + E₁₂) * (E₁₂ * E₂₃ + E₂₃ * E₁₂) := by noncomm_ring
    _ = 2 * (E₁₂ + E₂₃) + 0 * (1 - E₂₃) + (1 + E₁₂) * 0 := by rw [h12', h_anti]
    _ = 2 * (E₁₂ + E₂₃) := by noncomm_ring

theorem clifford_artin_braid_relation {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h23 : E₂₃ * E₂₃ = -1)
    (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = (1 + E₂₃) * (1 + E₁₂) * (1 + E₂₃) := by
  have h_anti' : E₂₃ * E₁₂ + E₁₂ * E₂₃ = 0 := by rw [add_comm, h_anti]
  rw [clifford_bivector_triple_product h12 h_anti,
      clifford_bivector_triple_product h23 h_anti']
  noncomm_ring

def R₁₂ {B : Type*} [Ring B] : NestedMat B := 1 + E₁
def R₂₃ {B : Type*} [Ring B] : NestedMat B := 1 + E₂

/-- **Master Synthesis Theorem in $M_2(M_2(B))$**:
Over any noncommutative ring `B`, the Brauer–Weyl quaternion operators `E₁, E₂, E₃ ∈ M₂(M₂(B))`
simultaneously generate:
1. A representation of the Artin braid group `R₁₂ R₂₃ R₁₂ = R₂₃ R₁₂ R₂₃`,
2. Exact equality between the braid commutator `⁅R₁₂, R₂₃⁆` and the Maurer–Cartan curvature
   `mcCurvature 0 0 E₁ E₂ = 2 * E₃`,
3. The cyclic differential Bianchi identity `∑_{cyc} adjDeriv 0 E_i F_{jk} = 0`, and
4. Over `B = ℤ`, strict noncommutativity `R₁₂ R₂₃ ≠ R₂₃ R₁₂` and order-4 scaling `R₁₂^4 = -4 • 1`. -/
theorem master_braid_curvature_synthesis {B : Type*} [Ring B] :
    ((R₁₂ : NestedMat B) * R₂₃ * R₁₂ = R₂₃ * R₁₂ * R₂₃ ∧
     ⁅(R₁₂ : NestedMat B), R₂₃⁆ = mcCurvature (0 : NestedMat B →+ NestedMat B) 0 E₁ E₂ ∧
     mcCurvature (0 : NestedMat B →+ NestedMat B) 0 (E₁ : NestedMat B) E₂ = 2 * E₃ ∧
     adjDeriv (0 : NestedMat B →+ NestedMat B) (E₁ : NestedMat B) (mcCurvature 0 0 E₂ E₃) +
     adjDeriv 0 E₂ (mcCurvature 0 0 E₃ E₁) +
     adjDeriv 0 E₃ (mcCurvature 0 0 E₁ E₂) = 0) ∧
    ((R₁₂ : NestedMat ℤ) * R₂₃ ≠ R₂₃ * R₁₂ ∧
     (R₁₂ : NestedMat ℤ) ^ 4 = (-4 : ℤ) • (1 : NestedMat ℤ)) := by
  rcases nested_quaternion_lie_relations (B := B) with ⟨hE1, hE2, _, hAnti, hL12, _, _⟩
  have hZeroDeriv : IsRingDeriv (0 : NestedMat B →+ NestedMat B) := fun _ _ => by simp
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨by decide, by decide⟩⟩
  · exact clifford_artin_braid_relation hE1 hE2 hAnti
  · dsimp [R₁₂, R₂₃, mcCurvature]; simp only [Ring.lie_def, AddMonoidHom.zero_apply]; noncomm_ring
  · dsimp [mcCurvature]; simp only [AddMonoidHom.zero_apply, sub_self, zero_add]; exact hL12
  · exact differential_bianchi_identity hZeroDeriv hZeroDeriv hZeroDeriv
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) E₁ E₂ E₃

end ArchetypeA9_MasterSynthesis

end GrandUnifiedNoncommutativeOperatorSynthesis
```

## Turn 0027, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace UnifiedBraidedCurvatureAndPorousToeplitz

/-!
## Archetype $\mathcal{U}_1$: Division-Free Scaled-Projection Compression, Pore Conservation & Commutator Variance
-/

section ArchetypeU1_ScaledProjectionCommutatorVariance

variable {B : Type*} [Ring B] [StarRing B]

def biCompress (P_Ω U P_T : B) : B := P_Ω * U * P_T
def symCompress (P Q : B) : B := P * Q * P

theorem pore_uncertainty_conservation
    {P_Ω U P_T : B} (hU : star U * U = 1)
    (hT_idem : P_T * P_T = P_T) (hT_sa : star P_T = P_T)
    (hΩ_idem : P_Ω * P_Ω = P_Ω) (hΩ_sa : star P_Ω = P_Ω) :
    star (biCompress P_Ω U P_T) * biCompress P_Ω U P_T +
    star (biCompress (1 - P_Ω) U P_T) * biCompress (1 - P_Ω) U P_T = P_T := by
  dsimp [biCompress]
  simp only [star_mul, star_sub, star_one, hT_sa, hΩ_sa]
  have h1 : P_T * star U * P_Ω * (P_Ω * U * P_T) +
            P_T * star U * (1 - P_Ω) * ((1 - P_Ω) * U * P_T) =
            P_T * star U * (P_Ω * P_Ω + (1 - P_Ω) * (1 - P_Ω)) * U * P_T := by noncomm_ring
  have h2 : P_Ω * P_Ω + (1 - P_Ω) * (1 - P_Ω) = 1 := by
    calc P_Ω * P_Ω + (1 - P_Ω) * (1 - P_Ω)
      _ = 1 - P_Ω - P_Ω + (P_Ω * P_Ω + P_Ω * P_Ω) := by noncomm_ring
      _ = 1 - P_Ω - P_Ω + (P_Ω + P_Ω) := by rw [hΩ_idem]
      _ = 1 := by noncomm_ring
  rw [h1, h2]
  calc P_T * star U * 1 * U * P_T
    _ = P_T * (star U * U) * P_T := by noncomm_ring
    _ = P_T * 1 * P_T := by rw [hU]
    _ = P_T * P_T := by noncomm_ring
    _ = P_T := hT_idem

/-- **Division-Free Scaled-Projection Commutator Variance Theorem**:
For any projection $P^2 = P = P^\star$ and any $k$-scaled self-adjoint projection $Q^2 = k \bullet Q$
($Q^\star = Q$, $k \in \mathbb{N}$), the compression $T_{P, Q} = P Q P$ satisfies
$k \bullet T_{P, Q} - T_{P, Q}^2 = ((1 - P) Q P)^\star ((1 - P) Q P) = (P \⁅P, Q⁆^\star)(\⁅P, Q⁆ P)$. -/
theorem scaled_symCompress_variance_eq_pore_and_commutator
    {P Q : B} {k : ℕ} (hP_idem : P * P = P) (hP_sa : star P = P)
    (hQ_scale : Q * Q = k • Q) (hQ_sa : star Q = Q) :
    k • symCompress P Q - symCompress P Q * symCompress P Q =
      star ((1 - P) * Q * P) * ((1 - P) * Q * P) ∧
    k • symCompress P Q - symCompress P Q * symCompress P Q =
      (P * star ⁅P, Q⁆) * (⁅P, Q⁆ * P) := by
  have h_pore : k • symCompress P Q - symCompress P Q * symCompress P Q =
      star ((1 - P) * Q * P) * ((1 - P) * Q * P) := by
    dsimp [symCompress]
    simp only [star_mul, star_sub, star_one, hP_sa, hQ_sa]
    have h1P : (1 - P) * (1 - P) = 1 - P := by
      calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        _ = 1 - P := by rw [hP_idem]; noncomm_ring
    have hk : k • (P * Q * P) = P * (k • Q) * P := by
      rw [nsmul_eq_mul, nsmul_eq_mul]; noncomm_ring
    calc k • (P * Q * P) - P * Q * P * (P * Q * P)
      _ = P * (Q * Q) * P - P * Q * (P * P) * Q * P := by
          rw [hk, hQ_scale, hP_idem]; noncomm_ring
      _ = P * Q * (1 - P) * Q * P := by noncomm_ring
      _ = P * Q * ((1 - P) * (1 - P)) * Q * P := by rw [h1P]
      _ = P * Q * (1 - P) * ((1 - P) * Q * P) := by noncomm_ring
  refine ⟨h_pore, ?_⟩
  rw [h_pore]
  have h_comm : ⁅P, Q⁆ * P = -((1 - P) * Q * P) := by
    rw [Ring.lie_def]
    calc (P * Q - Q * P) * P = P * Q * P - Q * (P * P) := by noncomm_ring
      _ = P * Q * P - Q * P := by rw [hP_idem]
      _ = -((1 - P) * Q * P) := by noncomm_ring
  have h_star : P * star ⁅P, Q⁆ = -star ((1 - P) * Q * P) := by
    calc P * star ⁅P, Q⁆ = star (⁅P, Q⁆ * P) := by simp [star_mul, hP_sa]
      _ = -star ((1 - P) * Q * P) := by rw [h_comm, star_neg]
  rw [h_comm, h_star, neg_mul_neg]

end ArchetypeU1_ScaledProjectionCommutatorVariance

/-!
## Archetype $\mathcal{U}_2$: All-Powers Berezin–Toeplitz Intertwining & Multiscale Positive-Cone Telescoping
-/

section ArchetypeU2_BerezinToeplitzAndMultiscaleTelescoping

variable {B : Type*} [Ring B] [StarRing B]

def rangeProj (V : B) : B := V * star V
def berezinOp (V S : B) : B := star V * S * V
def toeplitzOp (V S : B) : B := rangeProj V * S * rangeProj V

theorem berezin_toeplitz_intertwining {V S : B} (hV : star V * V = 1) :
    V * berezinOp V S = toeplitzOp V S * V ∧
    V * berezinOp V S * star V = toeplitzOp V S ∧
    star V * toeplitzOp V S * V = berezinOp V S ∧
    berezinOp V S + berezinOp V (1 - S) = 1 := by
  refine ⟨?_, by dsimp [berezinOp, toeplitzOp, rangeProj]; noncomm_ring, ?_, ?_⟩
  · dsimp [berezinOp, toeplitzOp, rangeProj]
    calc V * (star V * S * V)
      _ = V * star V * S * V * 1 := by noncomm_ring
      _ = V * star V * S * V * (star V * V) := by rw [hV]
      _ = (V * star V) * S * (V * star V) * V := by noncomm_ring
  · dsimp [berezinOp, toeplitzOp, rangeProj]
    calc star V * ((V * star V) * S * (V * star V)) * V
      _ = (star V * V) * star V * S * V * (star V * V) := by noncomm_ring
      _ = 1 * star V * S * V * 1 := by rw [hV]
      _ = star V * S * V := by noncomm_ring
  · dsimp [berezinOp]
    calc star V * S * V + star V * (1 - S) * V = star V * V := by noncomm_ring
      _ = 1 := hV

theorem toeplitzOp_pow_succ {V S : B} (hV : star V * V = 1) (n : ℕ) :
    toeplitzOp V S ^ (n + 1) = V * (berezinOp V S ^ (n + 1)) * star V := by
  induction' n with n ih
  · simp only [pow_one]; exact (berezin_toeplitz_intertwining hV).2.1.symm
  · rw [pow_succ (toeplitzOp V S), ih, ← (berezin_toeplitz_intertwining hV).2.1]
    calc (V * berezinOp V S ^ (n + 1) * star V) * (V * berezinOp V S * star V)
      _ = V * berezinOp V S ^ (n + 1) * (star V * V) * berezinOp V S * star V := by noncomm_ring
      _ = V * berezinOp V S ^ (n + 1) * 1 * berezinOp V S * star V := by rw [hV]
      _ = V * (berezinOp V S ^ (n + 1) * berezinOp V S) * star V := by noncomm_ring
      _ = V * (berezinOp V S ^ (n + 2)) * star V := by rw [← pow_succ]

def multiscaleLoc (L : ℕ → B) : ℕ → B
  | 0     => 1
  | k + 1 => L k * multiscaleLoc L k

def multiscalePoreEscape (L R : ℕ → B) (k : ℕ) : B :=
  ∑ j ∈ Finset.range k, star (R j * multiscaleLoc L j) * (R j * multiscaleLoc L j)

theorem multiscale_telescoping_defect
    {L R : ℕ → B} (h_part : ∀ j : ℕ, star (L j) * L j + star (R j) * R j = 1) (k : ℕ) :
    1 - star (multiscaleLoc L k) * multiscaleLoc L k = multiscalePoreEscape L R k := by
  induction' k with k ih
  · simp [multiscaleLoc, multiscalePoreEscape]
  · rw [multiscalePoreEscape, Finset.sum_range_succ, ← multiscalePoreEscape]
    have hL : star (L k) * L k = 1 - star (R k) * R k := eq_sub_of_add_eq (h_part k)
    dsimp [multiscaleLoc]
    calc 1 - star (L k * multiscaleLoc L k) * (L k * multiscaleLoc L k)
      _ = 1 - star (multiscaleLoc L k) * (star (L k) * L k) * multiscaleLoc L k := by
          simp only [star_mul]; noncomm_ring
      _ = 1 - star (multiscaleLoc L k) * (1 - star (R k) * R k) * multiscaleLoc L k := by
          rw [hL]
      _ = (1 - star (multiscaleLoc L k) * multiscaleLoc L k) +
          star (multiscaleLoc L k) * star (R k) * (R k * multiscaleLoc L k) := by
          noncomm_ring
      _ = multiscalePoreEscape L R k +
          star (R k * multiscaleLoc L k) * (R k * multiscaleLoc L k) := by
          rw [ih]; simp only [star_mul, mul_assoc]

end ArchetypeU2_BerezinToeplitzAndMultiscaleTelescoping

/-!
## Archetype $\mathcal{U}_3$: Matrix-Bimodule Frame/Gram Morita Duality & Non-Diagonal Symbol Multipliers
-/

section ArchetypeU3_MatrixBimoduleGaborToeplitzDuality

variable {B : Type*} [Ring B] [StarRing B] {m : ℕ}

def synMat (φ : Fin m → B) : Matrix (Fin 1) (Fin m) B := Matrix.of fun _ j => φ j
def frameOp (φ : Fin m → B) : B := ∑ i : Fin m, φ i * star (φ i)
def gramMat (φ : Fin m → B) : Matrix (Fin m) (Fin m) B := Matrix.of fun i j => star (φ i) * φ j

def genMultiplier (φ : Fin m → B) (𝓜 : Matrix (Fin m) (Fin m) B) : Matrix (Fin 1) (Fin 1) B :=
  synMat φ * 𝓜 * (synMat φ)ᴴ

theorem synMat_outer_and_inner (φ : Fin m → B) :
    (synMat φ * (synMat φ)ᴴ) 0 0 = frameOp φ ∧
    (synMat φ)ᴴ * synMat φ = gramMat φ := by
  constructor
  · simp [synMat, frameOp, Matrix.mul_apply]
  · ext i j; simp [synMat, gramMat, Matrix.mul_apply, Fin.sum_univ_one]

theorem morita_toeplitz_multiplier_intertwining
    (φ : Fin m → B) (𝓜 : Matrix (Fin m) (Fin m) B) (n : ℕ) :
    (synMat φ)ᴴ * genMultiplier φ 𝓜 * synMat φ = gramMat φ * 𝓜 * gramMat φ ∧
    genMultiplier φ 𝓜 ^ (n + 1) =
      synMat φ * 𝓜 * (gramMat φ * 𝓜) ^ n * (synMat φ)ᴴ ∧
    (frameOp φ = 1 → gramMat φ * gramMat φ = gramMat φ ∧ (gramMat φ)ᴴ = gramMat φ) := by
  have hG : (synMat φ)ᴴ * synMat φ = gramMat φ := (synMat_outer_and_inner φ).2
  refine ⟨?_, ?_, ?_⟩
  · dsimp [genMultiplier]
    calc (synMat φ)ᴴ * (synMat φ * 𝓜 * (synMat φ)ᴴ) * synMat φ
      _ = ((synMat φ)ᴴ * synMat φ) * 𝓜 * ((synMat φ)ᴴ * synMat φ) := by
          simp only [Matrix.mul_assoc]
      _ = gramMat φ * 𝓜 * gramMat φ := by rw [hG]
  · induction' n with n ih
    · simp [genMultiplier]
    · rw [pow_succ (genMultiplier φ 𝓜), ih]
      dsimp [genMultiplier]
      calc (synMat φ * 𝓜 * (gramMat φ * 𝓜) ^ n * (synMat φ)ᴴ) *
            (synMat φ * 𝓜 * (synMat φ)ᴴ)
        _ = synMat φ * 𝓜 * ((gramMat φ * 𝓜) ^ n *
            (((synMat φ)ᴴ * synMat φ) * 𝓜)) * (synMat φ)ᴴ := by
            simp only [Matrix.mul_assoc]
        _ = synMat φ * 𝓜 * ((gramMat φ * 𝓜) ^ n *
            (gramMat φ * 𝓜)) * (synMat φ)ᴴ := by rw [hG]
        _ = synMat φ * 𝓜 * (gramMat φ * 𝓜) ^ (n + 1) * (synMat φ)ᴴ := by
            rw [← pow_succ]
  · intro h_pars
    have hF : synMat φ * (synMat φ)ᴴ = 1 := by
      ext i j; fin_cases i; fin_cases j
      simpa using ((synMat_outer_and_inner φ).1.trans h_pars)
    refine ⟨?_, by ext i j; simp [gramMat, star_mul]⟩
    calc gramMat φ * gramMat φ
      _ = (synMat φ)ᴴ * (synMat φ * (synMat φ)ᴴ) * synMat φ := by
          rw [← hG]; simp only [Matrix.mul_assoc]
      _ = (synMat φ)ᴴ * 1 * synMat φ := by rw [hF]
      _ = gramMat φ := by rw [Matrix.mul_one, hG]

end ArchetypeU3_MatrixBimoduleGaborToeplitzDuality

/-!
## Archetype $\mathcal{U}_4$: Koszul Connections, Maurer–Cartan Curvature, Bianchi Identity & Gerbe Torsion
-/

section ArchetypeU4_KoszulCurvatureAndGerbeTorsion

def IsRingDeriv {B : Type*} [Ring B] (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

def liftMatrixDeriv {S : Type*} [Ring S] {n : Type*} [Fintype n] [DecidableEq n]
    (d : S →+ S) : Matrix n n S →+ Matrix n n S where
  toFun M i j := d (M i j)
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; simp

variable {B : Type*} [Ring B]

def covOp (d : B →+ B) (A ψ : B) : B := d ψ + A * ψ
def mcCurvature (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B := d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆
def dressConn (d : B →+ B) (u : Bˣ) (A : B) : B := (u : B) * A * (↑u⁻¹ : B) - d (u : B) * (↑u⁻¹ : B)
def adjDeriv (d : B →+ B) (A X : B) : B := d X + ⁅A, X⁆

theorem differential_bianchi_identity
    {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁ A₂ A₃ : B) :
    adjDeriv d₁ A₁ (mcCurvature d₂ d₃ A₂ A₃) +
    adjDeriv d₂ A₂ (mcCurvature d₃ d₁ A₃ A₁) +
    adjDeriv d₃ A₃ (mcCurvature d₁ d₂ A₁ A₂) = 0 := by
  dsimp [adjDeriv, mcCurvature]
  simp only [Ring.lie_def, map_add, map_sub]
  rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
      h12 A₃, h13 A₂, h23 A₁, ← h12 A₃, ← h13 A₂, ← h23 A₁]
  noncomm_ring

def gerbeEmbed (r : ℕ) (b : B) : Matrix (Fin r) (Fin r) B :=
  Matrix.of (fun i j => if i = j then b else 0)

def ncTrace {r : ℕ} (M : Matrix (Fin r) (Fin r) B) : B :=
  ∑ i : Fin r, M i i

def twistedBundleCurvature {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B) :
    Matrix (Fin r) (Fin r) B :=
  mcCurvature (liftMatrixDeriv d₁) (liftMatrixDeriv d₂) A₁ A₂ + gerbeEmbed r B_gerbe

theorem ncTrace_gerbeEmbed (r : ℕ) (b : B) :
    ncTrace (gerbeEmbed r b) = r • b := by
  dsimp [ncTrace, gerbeEmbed]; simp [Finset.sum_const, Finset.card_fin]

theorem projectively_flat_torsion_anomaly {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B)
    (h_flat : twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe = 0) :
    r • B_gerbe = -(d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) := by
  have h_tr : ncTrace (twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe) = 0 := by
    rw [h_flat]; dsimp [ncTrace]; simp
  have h_decomp : ncTrace (twistedBundleCurvature d₁ d₂ A₁ A₂ B_gerbe) =
      (d₁ (ncTrace A₂) - d₂ (ncTrace A₁) + ncTrace ⁅A₁, A₂⁆) + r • B_gerbe := by
    dsimp [twistedBundleCurvature, mcCurvature, ncTrace, liftMatrixDeriv]
    simp only [Matrix.add_apply, Matrix.sub_apply, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, map_sum, ← ncTrace_gerbeEmbed r B_gerbe]
    rfl
  rw [h_decomp] at h_tr
  exact eq_neg_of_add_eq_zero_right h_tr

end ArchetypeU4_KoszulCurvatureAndGerbeTorsion

/-!
## Archetype $\mathcal{U}_5$ & $\mathcal{U}_6$: Universal Parabolic Monodromy & Master Braid–Curvature–Cantor Synthesis in $M_2(M_2(A))$
-/

section ArchetypeU5_U6_MasterBraidCurvatureCantorSynthesis

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma of2_00 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl
@[simp] lemma of2_01 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl
@[simp] lemma of2_10 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl
@[simp] lemma of2_11 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

def Σ_op    : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]
def Ω_op    : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]
def Γ₁_op   : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]
def P_plus  : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def F_plus  : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![0, 0]]
def F_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![1, 0]]
def N_plus  : Matrix (Fin 2) (Fin 2) A := ![![-1, -1], ![1, 1]]

def fiberEmbed (x : A) : Matrix (Fin 2) (Fin 2) A := ![![x, 0], ![0, x]]
def kleinTwist (x : A) : Matrix (Fin 2) (Fin 2) A := ![![x, 0], ![0, -x]]

end Matrix2Simp

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

def X_blk {B : Type*} [Ring B] : NestedMat B := ![![0, 1 - F_plus], ![1 + F_plus, 0]]
def Z_blk {B : Type*} [Ring B] : NestedMat B := ![![Σ_op, 0], ![0, Γ₁_op]]
def N_blk {B : Type*} [Ring B] : NestedMat B := ![![N_plus, 0], ![0, -F_minus]]
def Q_blk {B : Type*} [Ring B] : NestedMat B := (Z_blk * X_blk) * (Z_blk * X_blk)

theorem universal_Q_blk_pow {B : Type*} [Ring B] (n : ℕ) :
    (Q_blk : NestedMat B) ^ n = 1 + n • N_blk := by
  have hQ : (Q_blk : NestedMat B) = 1 + N_blk := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Q_blk, Z_blk, X_blk, Σ_op, Γ₁_op, F_plus, F_minus, N_blk, N_plus] <;> abel
  have hN2 : (N_blk : NestedMat B) * N_blk = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [N_blk, N_plus, F_minus]
  induction' n with n ih
  · simp
  · rw [pow_succ, ih, hQ, add_nsmul, one_nsmul]
    have h_mul : (n • (N_blk : NestedMat B)) * N_blk = 0 := by
      rw [nsmul_eq_mul, mul_assoc, hN2, mul_zero]
    calc (1 + n • (N_blk : NestedMat B)) * (1 + N_blk)
      _ = 1 + (n • N_blk + N_blk) + (n • N_blk) * N_blk := by noncomm_ring
      _ = 1 + (n • N_blk + N_blk) := by rw [h_mul, add_zero]

def E₁ {B : Type*} [Ring B] : NestedMat B := Ω_op
def E₂ {B : Type*} [Ring B] : NestedMat B := kleinTwist Ω_op
def E₃ {B : Type*} [Ring B] : NestedMat B := (E₁ : NestedMat B) * E₂

def R₁₂ {B : Type*} [Ring B] : NestedMat B := 1 + E₁
def R₂₃ {B : Type*} [Ring B] : NestedMat B := 1 + E₂

/-- The composite 2-scale Brauer–Weyl–Cayley–Fourier operator $\mathcal{U}_{\mathrm{braid}} = R_{12} R_{23}$. -/
def U_braid {B : Type*} [Ring B] : NestedMat B := R₁₂ * R₂₃

/-- Nested porous Sierpiński ($3/4$), 1-scale Peirce ($1/2$), and 2-scale Cantor ($1/4$) projections in $M_2(M_2(B))$. -/
def Pi_S2 {B : Type*} [Ring B] : NestedMat B := ![![1, 0], ![0, P_plus]]
def Pi_1  {B : Type*} [Ring B] : NestedMat B := ![![1, 0], ![0, 0]]
def Pi_C2 {B : Type*} [Ring B] : NestedMat B := ![![P_plus, 0], ![0, 0]]

theorem clifford_bivector_triple_product {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = 2 * (E₁₂ + E₂₃) := by
  have h12' : E₁₂ * E₁₂ + 1 = 0 := by rw [h12]; abel
  calc (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂)
    _ = 2 * (E₁₂ + E₂₃) + (E₁₂ * E₁₂ + 1) * (1 - E₂₃) +
        (1 + E₁₂) * (E₁₂ * E₂₃ + E₂₃ * E₁₂) := by noncomm_ring
    _ = 2 * (E₁₂ + E₂₃) + 0 * (1 - E₂₃) + (1 + E₁₂) * 0 := by rw [h12', h_anti]
    _ = 2 * (E₁₂ + E₂₃) := by noncomm_ring

theorem clifford_artin_braid_relation {B : Type*} [Ring B] {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h23 : E₂₃ * E₂₃ = -1)
    (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = (1 + E₂₃) * (1 + E₁₂) * (1 + E₂₃) := by
  have h_anti' : E₂₃ * E₁₂ + E₁₂ * E₂₃ = 0 := by rw [add_comm, h_anti]
  rw [clifford_bivector_triple_product h12 h_anti,
      clifford_bivector_triple_product h23 h_anti']
  noncomm_ring

/-- **Grand Unification Theorem in $M_2(M_2(A))$ ($\mathcal{U}_6$)**:
Over any noncommutative $\star$-ring $A$, the Clifford–Artin braid generators $R_{12} = 1 + E_1$
and $R_{23} = 1 + E_2$ simultaneously satisfy:
1. The Artin braid relation $R_{12} R_{23} R_{12} = R_{23} R_{12} R_{23}$,
2. Exact equality between the braid commutator $\⁅R_{12}, R_{23}⁆$ and the Maurer–Cartan
   quaternion curvature $F_{12}(0, 0, E_1, E_2) = 2 E_3$,
3. 2-scale unitary scaling $\mathcal{U}_{\mathrm{braid}}^\dagger \mathcal{U}_{\mathrm{braid}} = 4 \bullet 1$
   for $\mathcal{U}_{\mathrm{braid}} = R_{12} R_{23}$, and
4. The 4-step Sierpiński-to-Cantor porous contraction ladder
   $4 \bullet \Pi_{\mathcal{C}_2} \to 3 \bullet \Pi_{\mathcal{C}_2} \to 2 \bullet \Pi_{\mathcal{C}_2} \to 1 \bullet \Pi_{\mathcal{C}_2}$. -/
theorem grand_unified_braid_curvature_cantor_synthesis {A : Type*} [Ring A] [StarRing A] :
    (R₁₂ : NestedMat A) * R₂₃ * R₁₂ = R₂₃ * R₁₂ * R₂₃ ∧
    ⁅(R₁₂ : NestedMat A), R₂₃⁆ = mcCurvature (0 : NestedMat A →+ NestedMat A) 0 E₁ E₂ ∧
    mcCurvature (0 : NestedMat A →+ NestedMat A) 0 (E₁ : NestedMat A) E₂ = 2 * E₃ ∧
    (U_braid : NestedMat A)ᴴ * U_braid = 4 • (1 : NestedMat A) ∧
    (U_braid * Pi_C2 : NestedMat A)ᴴ * (U_braid * Pi_C2) = 4 • (Pi_C2 : NestedMat A) ∧
    (Pi_S2 * U_braid * Pi_C2 : NestedMat A)ᴴ * (Pi_S2 * U_braid * Pi_C2) =
      3 • (Pi_C2 : NestedMat A) ∧
    (Pi_1 * U_braid * Pi_C2 : NestedMat A)ᴴ * (Pi_1 * U_braid * Pi_C2) =
      2 • (Pi_C2 : NestedMat A) ∧
    (Pi_C2 * U_braid * Pi_C2 : NestedMat A)ᴴ * (Pi_C2 * U_braid * Pi_C2) =
      (Pi_C2 : NestedMat A) := by
  have hE1 : (E₁ : NestedMat A) * E₁ = -1 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [E₁, Ω_op]
  have hE2 : (E₂ : NestedMat A) * E₂ = -1 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [E₂, kleinTwist, Ω_op]
  have hAnti : (E₁ : NestedMat A) * E₂ + E₂ * E₁ = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [E₁, E₂, kleinTwist, Ω_op]
  refine ⟨clifford_artin_braid_relation hE1 hE2 hAnti, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [R₁₂, R₂₃, mcCurvature]; simp only [Ring.lie_def, AddMonoidHom.zero_apply]; noncomm_ring
  · dsimp [mcCurvature, E₃]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Ring.lie_def, E₁, E₂, kleinTwist, Ω_op] <;> noncomm_ring
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, Ω_op] <;> abel
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, Ω_op, Pi_C2, P_plus] <;> abel
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, Ω_op, Pi_S2, Pi_C2, P_plus] <;> abel
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, Ω_op, Pi_1, Pi_C2, P_plus] <;> abel
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, Ω_op, Pi_C2, P_plus]

end ArchetypeU5_U6_MasterBraidCurvatureCantorSynthesis

end UnifiedBraidedCurvatureAndPorousToeplitz
```

## Turn 0030, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeTetraktysFlowsAndCayleyClifford

/-!
## Foundational Infrastructure: $2 \times 2$ Noncommutative Operator Matrices & $Cl(1,1)$ Atom
-/

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma of2_00 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl
@[simp] lemma of2_01 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl
@[simp] lemma of2_10 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl
@[simp] lemma of2_11 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

/-- The fundamental $Cl(1,1)$ generators $(\Gamma_1, \Sigma, \Omega)$, Source/Sink projectors $(P_+, P_-)$,
and Nilpotent Witt Twin-Wave operators $(F_+, F_-)$. -/
def Γ₁_op   : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]
def Σ_op    : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]
def Ω_op    : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]
def P_plus  : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]
def F_plus  : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![0, 0]]
def F_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![1, 0]]
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := ![![a, 0], ![0, a]]

end Matrix2Simp

/-!
## Archetype $\mathcal{T}_1$: Modular $CPT$ Automorphism Triad & Klein-Four $\mathbb{Z}_2 \times \mathbb{Z}_2$ Grading
-/

section ArchetypeT1_ModularCPTTriad

variable {A : Type*} [Ring A]

/-- Parity / Chirality involution $\mathcal{P}(M) = \Gamma_1 M \Gamma_1$. -/
def cptP (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Γ₁_op * M * Γ₁_op

/-- Time-reversal / Source-Sink swap involution $\mathcal{T}(M) = \Sigma M \Sigma$. -/
def cptT (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Σ_op * M * Σ_op

/-- Charge-conjugation / Symplectic inner involution $\mathcal{C}(M) = -\Omega M \Omega = \Omega M \Omega^{-1}$. -/
def cptC (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  -(Ω_op * M * Ω_op)

/-- **Modular $CPT$ Klein-Four Group Theorem ($\mathcal{T}_1$)**:
In $M_2(A)$ over any noncommutative ring $A$:
1. The $Cl(1,1)$ triad satisfies the modular volume identity $\Gamma_1 \Sigma \Omega = -1$,
2. $\mathcal{P}, \mathcal{T}, \mathcal{C}$ are involutions satisfying $\mathcal{P} \circ \mathcal{T} = \mathcal{C}$,
   $\mathcal{T} \circ \mathcal{C} = \mathcal{P}$, and $\mathcal{C} \circ \mathcal{P} = \mathcal{T}$,
3. The composite $CPT$ action is the identity $\mathcal{P}(\mathcal{T}(\mathcal{C}(M))) = M$. -/
theorem modular_cpt_klein_four_group (M : Matrix (Fin 2) (Fin 2) A) :
    (Γ₁_op : Matrix (Fin 2) (Fin 2) A) * Σ_op * Ω_op = -1 ∧
    cptP (cptP M) = M ∧
    cptT (cptT M) = M ∧
    cptC (cptC M) = M ∧
    cptP (cptT M) = cptC M ∧
    cptT (cptC M) = cptP M ∧
    cptC (cptP M) = cptT M ∧
    cptP (cptT (cptC M)) = M := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> simp [cptP, cptT, cptC, Γ₁_op, Σ_op, Ω_op] <;> noncomm_ring)

end ArchetypeT1_ModularCPTTriad

/-!
## Archetype $\mathcal{T}_2$: Clifford–Cayley Transform $\mathcal{C}_{\mathrm{Cayley}} = 1 + \Omega$ & Clock–Shift / Twin-Wave Duality
-/

section ArchetypeT2_CliffordCayleyTransform

variable {A : Type*} [Ring A] [StarRing A]

/-- Division-free Clifford–Cayley operator $\mathcal{C}_{\mathrm{Cayley}} = 1 + \Omega = \begin{pmatrix} 1 & -1 \\ 1 & 1 \end{pmatrix}$. -/
def cayleyOp : Matrix (Fin 2) (Fin 2) A := 1 + Ω_op

/-- Symmetric and antisymmetric twin-wave defect projectors $\Pi_{\mathrm{sym}} = 1 + \Sigma$ and $\Pi_{\mathrm{anti}} = 1 - \Sigma$. -/
def twinWaveSym  : Matrix (Fin 2) (Fin 2) A := 1 + Σ_op
def twinWaveAnti : Matrix (Fin 2) (Fin 2) A := 1 - Σ_op

/-- **Clifford–Cayley Clock–Shift & Source–Sink Twin-Wave Duality Theorem ($\mathcal{T}_2$)**:
Over any noncommutative $\star$-ring $A$:
1. $\mathcal{C}_{\mathrm{Cayley}} \mathcal{C}_{\mathrm{Cayley}}^\dagger = 2 \bullet 1$ and
   $\mathcal{C}_{\mathrm{Cayley}}^\dagger \mathcal{C}_{\mathrm{Cayley}} = 2 \bullet 1$,
2. Conjugating by $\mathcal{C}_{\mathrm{Cayley}}$ rotates the Clock generator $\Gamma_1$ into $2 \bullet \Sigma$,
   rotates the Shift generator $\Sigma$ into $-(2 \bullet \Gamma_1)$, and fixes $2 \bullet \Omega$,
3. Conjugating the Source ($P_+$) and Sink ($P_-$) projectors by $\mathcal{C}_{\mathrm{Cayley}}$
   produces the twin-wave projectors $\Pi_{\mathrm{sym}} = 1 + \Sigma$ and $\Pi_{\mathrm{anti}} = 1 - \Sigma$. -/
theorem clifford_cayley_clock_shift_and_twin_wave_duality :
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * cayleyOpᴴ = 2 • (1 : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A)ᴴ * cayleyOp = 2 • (1 : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * Γ₁_op * cayleyOpᴴ = 2 • (Σ_op : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * Σ_op * cayleyOpᴴ = -(2 • (Γ₁_op : Matrix (Fin 2) (Fin 2) A)) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * Ω_op * cayleyOpᴴ = 2 • (Ω_op : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * P_plus * cayleyOpᴴ = twinWaveSym ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * P_minus * cayleyOpᴴ = twinWaveAnti := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [cayleyOp, twinWaveSym, twinWaveAnti, Γ₁_op, Σ_op, Ω_op, P_plus, P_minus] <;>
      abel)

end ArchetypeT2_CliffordCayleyTransform

/-!
## Archetype $\mathcal{T}_3$: Hyperbolic Mellin Time-Focusing Flow on Source ($0$) & Sink ($\infty$) Twin Waves
-/

section ArchetypeT3_HyperbolicTimeFocusingTwinWaves

variable {A : Type*} [Ring A]

/-- Noncommutative hyperbolic Mellin dilation / time-focusing operator $D(u) = \mathrm{diag}(u, u^{-1})$. -/
def mellinFocus (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  ![![(u : A), 0], ![0, (↑u⁻¹ : A)]]

/-- **Hyperbolic Time-Focusing & Twin-Wave Casimir Theorem ($\mathcal{T}_3$)**:
Under the hyperbolic Mellin dilation $D(u)$ ($u \in A^\times$):
1. The forward focusing wave $\iota(a) F_+$ is quadratically amplified to $\iota(u a u) F_+$,
2. The backward dispersing twin wave $\iota(b) F_-$ is quadratically compressed to $\iota(u^{-1} b u^{-1}) F_-$,
3. Their composite source projection $\big(\iota(u a u) F_+\big)\big(\iota(u^{-1} b u^{-1}) F_-\big)$
   is the gauge-conjugated source Casimir $\iota(u a b u^{-1}) P_+$. -/
theorem hyperbolic_time_focusing_twin_waves (u : Aˣ) (a b : A) :
    mellinFocus u * (fiberEmbed a * F_plus) * mellinFocus u⁻¹ =
      fiberEmbed ((u : A) * a * (u : A)) * F_plus ∧
    mellinFocus u * (fiberEmbed b * F_minus) * mellinFocus u⁻¹ =
      fiberEmbed ((↑u⁻¹ : A) * b * (↑u⁻¹ : A)) * F_minus ∧
    (fiberEmbed ((u : A) * a * (u : A)) * F_plus) *
    (fiberEmbed ((↑u⁻¹ : A) * b * (↑u⁻¹ : A)) * F_minus) =
      fiberEmbed ((u : A) * a * b * (↑u⁻¹ : A)) * P_plus := by
  have h1 : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  refine ⟨?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_plus] <;> noncomm_ring
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_minus] <;> noncomm_ring
  · apply ext_fin2
    · simp [fiberEmbed, F_plus, F_minus, P_plus]
      calc (u : A) * a * (u : A) * ((↑u⁻¹ : A) * b * (↑u⁻¹ : A))
        _ = (u : A) * a * ((u : A) * (↑u⁻¹ : A)) * b * (↑u⁻¹ : A) := by noncomm_ring
        _ = (u : A) * a * b * (↑u⁻¹ : A) := by rw [h1]; noncomm_ring
    · simp [fiberEmbed, F_plus, F_minus, P_plus]
    · simp [fiberEmbed, F_plus, F_minus, P_plus]
    · simp [fiberEmbed, F_plus, F_minus, P_plus]

end ArchetypeT3_HyperbolicTimeFocusingTwinWaves

/-!
## Archetype $\mathcal{T}_4$: Noncommutative Characteristic Polynomial & The Four Geometric Flows
-/

section ArchetypeT4_NoncommutativeCharpolyAndFourFlows

variable {A : Type*} [Ring A]

/-- General trace-free $Cl(1,1)$ flow generator
$X_{\mathrm{flow}}(c_\Gamma, c_\Sigma, c_\Omega) = \iota(c_\Gamma)\Gamma_1 + \iota(c_\Sigma)\Sigma + \iota(c_\Omega)\Omega$. -/
def flowGen (c_Γ c_Σ c_Ω : A) : Matrix (Fin 2) (Fin 2) A :=
  fiberEmbed c_Γ * Γ₁_op + fiberEmbed c_Σ * Σ_op + fiberEmbed c_Ω * Ω_op

/-- **Universal Noncommutative Characteristic Polynomial & Lie Cross-Product Obstruction ($\mathcal{T}_{4a}$)**:
For any noncommuting coefficients $c_\Gamma, c_\Sigma, c_\Omega \in A$, the square of
$X_{\mathrm{flow}}(c_\Gamma, c_\Sigma, c_\Omega)$ decomposes into the split-Minkowski Casimir
$\iota(c_\Gamma^2 + c_\Sigma^2 - c_\Omega^2)$ plus the non-Abelian $\mathfrak{sl}_2$ Lie cross product. -/
theorem noncommutative_charpoly_casimir_and_lie_obstruction (c_Γ c_Σ c_Ω : A) :
    flowGen c_Γ c_Σ c_Ω * flowGen c_Γ c_Σ c_Ω =
      fiberEmbed (c_Γ * c_Γ + c_Σ * c_Σ - c_Ω * c_Ω) * 1 +
      fiberEmbed ⁅c_Sigma, c_Ω⁆ * Γ₁_op +
      fiberEmbed ⁅c_Ω, c_Γ⁆ * Σ_op -
      fiberEmbed ⁅c_Γ, c_Σ⁆ * Ω_op := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [flowGen, fiberEmbed, Γ₁_op, Σ_op, Ω_op] <;> noncomm_ring

/-- **Classification of the Four Canonical Geometric Operator Flows ($\mathcal{T}_{4b}$)**:
1. *Hyperbolic Flows* ($c_\Omega = 0$): $X_{\mathrm{flow}}(a, 0, 0)^2 = \iota(a^2)$ and $X_{\mathrm{flow}}(0, a, 0)^2 = \iota(a^2)$,
2. *Elliptic Flow* ($c_\Gamma = c_\Sigma = 0$): $X_{\mathrm{flow}}(0, 0, a)^2 = -\iota(a^2)$,
3. *Parabolic Twin-Wave Flows* ($c_\Gamma = 0, c_\Sigma = \pm c_\Omega$): $X_{\mathrm{flow}}(0, a, a) = 2\iota(a)F_-$
   and $X_{\mathrm{flow}}(0, a, -a) = 2\iota(a)F_+$ are nilpotent ($X^2 = 0$) and generate unipotent shears,
4. *Loxodromic Flow* ($M = \iota(c_I) + X_{\mathrm{flow}}(a, 0, b)$ with $\⁅a, b⁆ = 0$):
   $(M - \iota(c_I))^2 = \iota(a^2 - b^2)$. -/
theorem four_geometric_flows_classification (c_I a b : A) (hab : ⁅a, b⁆ = 0) :
    flowGen a 0 0 * flowGen a 0 0 = fiberEmbed (a * a) ∧
    flowGen 0 a 0 * flowGen 0 a 0 = fiberEmbed (a * a) ∧
    flowGen 0 0 a * flowGen 0 0 a = -fiberEmbed (a * a) ∧
    flowGen 0 a a = 2 • (fiberEmbed a * F_minus) ∧
    flowGen 0 a (-a) = 2 • (fiberEmbed a * F_plus) ∧
    flowGen 0 a a * flowGen 0 a a = 0 ∧
    (1 + flowGen 0 a a) * (1 - flowGen 0 a a) = 1 ∧
    ((fiberEmbed c_I + flowGen a 0 b) - fiberEmbed c_I) *
    ((fiberEmbed c_I + flowGen a 0 b) - fiberEmbed c_I) =
      fiberEmbed (a * a - b * b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, Γ₁_op, Σ_op, Ω_op]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, Γ₁_op, Σ_op, Ω_op]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, Γ₁_op, Σ_op, Ω_op]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, Γ₁_op, Σ_op, Ω_op, F_minus] <;> abel
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, Γ₁_op, Σ_op, Ω_op, F_plus] <;> abel
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, Γ₁_op, Σ_op, Ω_op] <;> noncomm_ring
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, Γ₁_op, Σ_op, Ω_op] <;> noncomm_ring
  · rw [add_sub_cancel_left, noncommutative_charpoly_casimir_and_lie_obstruction]
    have hba : ⁅b, a⁆ = 0 := by rw [Ring.lie_def] at hab ⊢; noncomm_ring [hab]
    rw [hba]; apply ext_fin2 <;> simp [fiberEmbed, Γ₁_op, Σ_op, Ω_op]

end ArchetypeT4_NoncommutativeCharpolyAndFourFlows

/-!
## Archetype $\mathcal{T}_5$ & $\mathcal{T}_6$: Chained Two-Stage Tetraktys Transform & The $10 + 6 = 16$ Symplectic Split in $M_2(M_2(A))$
-/

section ArchetypeT5_T6_ChainedTetraktysAndSymplecticSplit

variable {A : Type*} [Ring A]

def peirceFiberLift (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * X * P_plus + Σ_op * P_plus * X * P_plus * Σ_op

def mellinCoeff_I (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M + Σ_op * M * Σ_op)
def mellinCoeff_Γ (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M - Σ_op * M * Σ_op)
def mellinCoeff_Σ (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M * Σ_op + Σ_op * M)
def mellinCoeff_Ω (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (Σ_op * M - M * Σ_op)

theorem clifford_mellin_walsh_inversion (M : Matrix (Fin 2) (Fin 2) A) :
    mellinCoeff_I M * 1 +
    mellinCoeff_Γ M * Γ₁_op +
    mellinCoeff_Σ M * Σ_op +
    mellinCoeff_Ω M * Ω_op = 2 • M := by
  apply ext_fin2 <;>
    simp [mellinCoeff_I, mellinCoeff_Γ, mellinCoeff_Σ, mellinCoeff_Ω,
      peirceFiberLift, P_plus, Γ₁_op, Σ_op, Ω_op, two_smul] <;>
    noncomm_ring

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- Two-stage Chained Tetraktys mode extractor: applies an outer Mellin–Walsh projection `C_out`
followed by an inner Mellin–Walsh projection `C_in` on the $(0,0)$ fiber block. -/
def tetraktysMode
    (C_out : NestedMat A → NestedMat A)
    (C_in : Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) A)
    (𝕄 : NestedMat A) : NestedMat A :=
  fiberEmbed (C_in (C_out 𝕄 0 0))

theorem outer_mode_inner_expansion
    (C_out : NestedMat A → NestedMat A) (𝕄 : NestedMat A)
    (h_diag : C_out 𝕄 = fiberEmbed (C_out 𝕄 0 0)) :
    tetraktysMode C_out mellinCoeff_I 𝕄 * fiberEmbed 1 +
    tetraktysMode C_out mellinCoeff_Γ 𝕄 * fiberEmbed Γ₁_op +
    tetraktysMode C_out mellinCoeff_Σ 𝕄 * fiberEmbed Σ_op +
    tetraktysMode C_out mellinCoeff_Ω 𝕄 * fiberEmbed Ω_op =
      2 • C_out 𝕄 := by
  have h_inv := clifford_mellin_walsh_inversion (C_out 𝕄 0 0)
  rw [h_diag]
  apply ext_fin2 <;> simp [tetraktysMode, fiberEmbed, ← h_inv, two_smul]

/-- **Two-Stage Chained Tetraktys Reconstruction Theorem ($\mathcal{T}_5$)**:
Every nested operator $\mathbb{M} \in M_2(M_2(A))$ over any noncommutative ring $A$ is reconstructed
as $4 \bullet \mathbb{M}$ from its $4 \times 4 = 16$ local symmetry-adapted $Cl(1,1) \otimes Cl(1,1)$ modes. -/
theorem chained_tetraktys_16_channel_inversion (𝕄 : NestedMat A) :
    (tetraktysMode mellinCoeff_I mellinCoeff_I 𝕄 * fiberEmbed 1 +
     tetraktysMode mellinCoeff_I mellinCoeff_Γ 𝕄 * fiberEmbed Γ₁_op +
     tetraktysMode mellinCoeff_I mellinCoeff_Σ 𝕄 * fiberEmbed Σ_op +
     tetraktysMode mellinCoeff_I mellinCoeff_Ω 𝕄 * fiberEmbed Ω_op) * 1 +
    (tetraktysMode mellinCoeff_Γ mellinCoeff_I 𝕄 * fiberEmbed 1 +
     tetraktysMode mellinCoeff_Γ mellinCoeff_Γ 𝕄 * fiberEmbed Γ₁_op +
     tetraktysMode mellinCoeff_Γ mellinCoeff_Σ 𝕄 * fiberEmbed Σ_op +
     tetraktysMode mellinCoeff_Γ mellinCoeff_Ω 𝕄 * fiberEmbed Ω_op) * Γ₁_op +
    (tetraktysMode mellinCoeff_Σ mellinCoeff_I 𝕄 * fiberEmbed 1 +
     tetraktysMode mellinCoeff_Σ mellinCoeff_Γ 𝕄 * fiberEmbed Γ₁_op +
     tetraktysMode mellinCoeff_Σ mellinCoeff_Σ 𝕄 * fiberEmbed Σ_op +
     tetraktysMode mellinCoeff_Σ mellinCoeff_Ω 𝕄 * fiberEmbed Ω_op) * Σ_op +
    (tetraktysMode mellinCoeff_Ω mellinCoeff_I 𝕄 * fiberEmbed 1 +
     tetraktysMode mellinCoeff_Ω mellinCoeff_Γ 𝕄 * fiberEmbed Γ₁_op +
     tetraktysMode mellinCoeff_Ω mellinCoeff_Σ 𝕄 * fiberEmbed Σ_op +
     tetraktysMode mellinCoeff_Ω mellinCoeff_Ω 𝕄 * fiberEmbed Ω_op) * Ω_op =
      4 • 𝕄 := by
  have hI : mellinCoeff_I 𝕄 = fiberEmbed (mellinCoeff_I 𝕄 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeff_I, peirceFiberLift, fiberEmbed, P_plus, Σ_op]
  have hΓ : mellinCoeff_Γ 𝕄 = fiberEmbed (mellinCoeff_Γ 𝕄 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeff_Γ, peirceFiberLift, fiberEmbed, P_plus, Σ_op]
  have hΣ : mellinCoeff_Σ 𝕄 = fiberEmbed (mellinCoeff_Σ 𝕄 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeff_Σ, peirceFiberLift, fiberEmbed, P_plus, Σ_op]
  have hΩ : mellinCoeff_Ω 𝕄 = fiberEmbed (mellinCoeff_Ω 𝕄 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeff_Ω, peirceFiberLift, fiberEmbed, P_plus, Σ_op]
  rw [outer_mode_inner_expansion mellinCoeff_I 𝕄 hI,
      outer_mode_inner_expansion mellinCoeff_Γ 𝕄 hΓ,
      outer_mode_inner_expansion mellinCoeff_Σ 𝕄 hΣ,
      outer_mode_inner_expansion mellinCoeff_Ω 𝕄 hΩ]
  have h_outer := clifford_mellin_walsh_inversion 𝕄
  calc (2 • mellinCoeff_I 𝕄) * 1 + (2 • mellinCoeff_Γ 𝕄) * Γ₁_op +
       (2 • mellinCoeff_Σ 𝕄) * Σ_op + (2 • mellinCoeff_Ω 𝕄) * Ω_op
    _ = 2 • (mellinCoeff_I 𝕄 * 1 + mellinCoeff_Γ 𝕄 * Γ₁_op +
             mellinCoeff_Σ 𝕄 * Σ_op + mellinCoeff_Ω 𝕄 * Ω_op) := by
        simp only [two_smul]; noncomm_ring
    _ = 2 • (2 • 𝕄) := by rw [h_outer]
    _ = 4 • 𝕄 := by rw [← mul_smul]

section SymplecticTetraktysSplit

variable [StarRing A]

/-- Canonical 2-scale symplectic form $\mathbb{J} = \Omega \otimes I \in M_2(M_2(A))$. -/
def J_sp : NestedMat A := Ω_op

/-- Predicate for an operator $\mathbb{X} \in M_2(M_2(A))$ to lie in the Hamiltonian symplectic Lie
algebra $\mathfrak{sp}_4(A, \star)$: $\mathbb{X}^\dagger \mathbb{J} + \mathbb{J} \mathbb{X} = 0$. -/
def IsSymplecticTetraktys (𝕏 : NestedMat A) : Prop :=
  𝕏ᴴ * J_sp + J_sp * 𝕏 = 0

/-- **The Pythagorean $(1 + 2 + 3 + 4 = 10)$ Symplectic Tetraktys Theorem ($\mathcal{T}_6$)**:
Over any noncommutative $\star$-ring $A$, the $10 = 1 + 2 + 3 + 4$ local symmetry-adapted
$Cl(1,1) \otimes Cl(1,1)$ basis generators
- *Row 1 ($1$ mode)*: $\iota(\Omega)\cdot 1$,
- *Row 2 ($2$ modes)*: $\iota(1)\cdot \Gamma_1, \; \iota(1)\cdot \Sigma$,
- *Row 3 ($3$ modes)*: $\iota(1)\cdot \Omega, \; \iota(\Gamma_1)\cdot \Omega, \; \iota(\Sigma)\cdot \Omega$,
- *Row 4 ($4$ modes)*: $\iota(\Gamma_1)\cdot \Gamma_1, \; \iota(\Sigma)\cdot \Gamma_1, \; \iota(\Gamma_1)\cdot \Sigma, \; \iota(\Sigma)\cdot \Sigma$
all belong to the Hamiltonian Lie algebra $\mathfrak{sp}_4(A, \star)$, which is closed under the
noncommutative Lie bracket $\⁅\mathbb{X}, \mathbb{Y}⁆$. -/
theorem pythagorean_ten_symplectic_tetraktys_generators :
    (∀ 𝕏 𝕐 : NestedMat A,
      IsSymplecticTetraktys 𝕏 → IsSymplecticTetraktys 𝕐 → IsSymplecticTetraktys ⁅𝕏, 𝕐⁆) ∧
    -- Row 1 (1 generator):
    IsSymplecticTetraktys (fiberEmbed (Ω_op : Matrix (Fin 2) (Fin 2) A) * 1) ∧
    -- Row 2 (2 generators):
    IsSymplecticTetraktys (fiberEmbed (1 : Matrix (Fin 2) (Fin 2) A) * Γ₁_op) ∧
    IsSymplecticTetraktys (fiberEmbed (1 : Matrix (Fin 2) (Fin 2) A) * Σ_op) ∧
    -- Row 3 (3 generators):
    IsSymplecticTetraktys (fiberEmbed (1 : Matrix (Fin 2) (Fin 2) A) * Ω_op) ∧
    IsSymplecticTetraktys (fiberEmbed (Γ₁_op : Matrix (Fin 2) (Fin 2) A) * Ω_op) ∧
    IsSymplecticTetraktys (fiberEmbed (Σ_op : Matrix (Fin 2) (Fin 2) A) * Ω_op) ∧
    -- Row 4 (4 generators):
    IsSymplecticTetraktys (fiberEmbed (Γ₁_op : Matrix (Fin 2) (Fin 2) A) * Γ₁_op) ∧
    IsSymplecticTetraktys (fiberEmbed (Σ_op : Matrix (Fin 2) (Fin 2) A) * Γ₁_op) ∧
    IsSymplecticTetraktys (fiberEmbed (Γ₁_op : Matrix (Fin 2) (Fin 2) A) * Σ_op) ∧
    IsSymplecticTetraktys (fiberEmbed (Σ_op : Matrix (Fin 2) (Fin 2) A) * Σ_op) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro 𝕏 𝕐 hX hY
    dsimp [IsSymplecticTetraktys] at *
    have hX' : 𝕏ᴴ * J_sp = -(J_sp * 𝕏) := eq_neg_of_add_eq_zero_left hX
    have hY' : 𝕐ᴴ * J_sp = -(J_sp * 𝕐) := eq_neg_of_add_eq_zero_left hY
    rw [Ring.lie_def]
    calc (𝕏 * 𝕐 - 𝕐 * 𝕏)ᴴ * J_sp + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏)
      _ = (𝕐ᴴ * 𝕏ᴴ - 𝕏ᴴ * 𝕐ᴴ) * J_sp + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by
          rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
      _ = 𝕐ᴴ * (𝕏ᴴ * J_sp) - 𝕏ᴴ * (𝕐ᴴ * J_sp) + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by noncomm_ring
      _ = 𝕐ᴴ * -(J_sp * 𝕏) - 𝕏ᴴ * -(J_sp * 𝕐) + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by rw [hX', hY']
      _ = -((𝕐ᴴ * J_sp) * 𝕏) + (𝕏ᴴ * J_sp) * 𝕐 + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by noncomm_ring
      _ = -(-(J_sp * 𝕐) * 𝕏) + -(J_sp * 𝕏) * 𝕐 + J_sp * (𝕏 * 𝕐 - 𝕐 * 𝕏) := by rw [hX', hY']
      _ = 0 := by noncomm_ring
  all_goals
    dsimp [IsSymplecticTetraktys, J_sp]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [fiberEmbed, Γ₁_op, Σ_op, Ω_op]

end SymplecticTetraktysSplit

end ArchetypeT5_T6_ChainedTetraktysAndSymplecticSplit

end NoncommutativeTetraktysFlowsAndCayleyClifford
```

## Turn 0033, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeAnalyticityHodgeJaynesSynthesis

/-!
## Foundational Infrastructure: $2 \times 2$ Noncommutative Operator Matrices
-/

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma of2_00 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 0 = a := rfl
@[simp] lemma of2_01 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 0 1 = b := rfl
@[simp] lemma of2_10 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 0 = c := rfl
@[simp] lemma of2_11 (a b c d : A) : (![![a, b], ![c, d]] : Matrix (Fin 2) (Fin 2) A) 1 1 = d := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

def Γ₁_op   : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, -1]]
def Σ_op    : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![1, 0]]
def Ω_op    : Matrix (Fin 2) (Fin 2) A := ![![0, -1], ![1, 0]]
def P_plus  : Matrix (Fin 2) (Fin 2) A := ![![1, 0], ![0, 0]]
def P_minus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![0, 1]]
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := ![![a, 0], ![0, a]]
def opTrace (M : Matrix (Fin 2) (Fin 2) A) : A := M 0 0 + M 1 1

end Matrix2Simp

/-!
## Archetype $\mathcal{H}_1$: Coupled Isotropic Witt Sheets & Complex-Structure Sheet Reversal (`CPTComplexStructure`)
-/

section ArchetypeH1_CPTComplexStructureAndIsotropicSheets

variable {A : Type*} [Ring A]

/-- Positive and negative coupled isotropic Witt sheets $\mathcal{I}_+ = F_+$ and $\mathcal{I}_- = F_-$. -/
def isotropicSheetPlus  : Matrix (Fin 2) (Fin 2) A := ![![0, 1], ![0, 0]]
def isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A := ![![0, 0], ![1, 0]]

theorem isotropicSheetPlus_sq :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetPlus = 0 := by
  apply ext_fin2 <;> simp [isotropicSheetPlus]

theorem isotropicSheetMinus_sq :
    (isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetMinus = 0 := by
  apply ext_fin2 <;> simp [isotropicSheetMinus]

theorem isotropicSheetPlus_mul_minus :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetMinus = P_plus := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, P_plus]

theorem isotropicSheetMinus_mul_plus :
    (isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetPlus = P_minus := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, P_minus]

theorem isotropicSheets_anticommute :
    anticomm (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) isotropicSheetMinus = 1 := by
  apply ext_fin2 <;> simp [anticomm, isotropicSheetPlus, isotropicSheetMinus]

theorem isotropicSheets_sum_eq_r0 :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) + isotropicSheetMinus = Σ_op := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, Σ_op]

theorem isotropicSheets_sub_eq_r5 :
    (isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A) - isotropicSheetPlus = Ω_op := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, Ω_op]

/-- **Complex-Structure Reversal of Chiral & Isotropic Sheets**:
Conjugating by the complex structure $\Omega$ swaps the chiral projectors $P_+ \leftrightarrow P_-$,
inverts $\Gamma_1$, and exchanges the coupled isotropic sheets $\mathcal{I}_+ \leftrightarrow -\mathcal{I}_-$. -/
theorem complexStructure_reverses_chiral_sheets :
    -((Ω_op : Matrix (Fin 2) (Fin 2) A) * P_plus * Ω_op) = P_minus ∧
    -((Ω_op : Matrix (Fin 2) (Fin 2) A) * P_minus * Ω_op) = P_plus ∧
    -((Ω_op : Matrix (Fin 2) (Fin 2) A) * Γ₁_op * Ω_op) = -Γ₁_op ∧
    -((Ω_op : Matrix (Fin 2) (Fin 2) A) * isotropicSheetPlus * Ω_op) = -isotropicSheetMinus ∧
    -((Ω_op : Matrix (Fin 2) (Fin 2) A) * isotropicSheetMinus * Ω_op) = -isotropicSheetPlus := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [Ω_op, P_plus, P_minus, Γ₁_op, isotropicSheetPlus, isotropicSheetMinus])

end ArchetypeH1_CPTComplexStructureAndIsotropicSheets

/-!
## Archetype $\mathcal{H}_2$: Bivector-Rotor Holomorphicity, Hestenes CR Split & Kähler Symplectic Pairing (`HestenesAnalyticity`)
-/

section ArchetypeH2_HestenesBivectorAnalyticity

/-- Doubled symplectic pairing $\omega_B(X, Y) = X^\star B Y$ on any $\star$-ring $R$ equipped with a
skew-adjoint unit bivector $B$ ($B^2 = -1, B^\star = -B$). -/
def doubledSymplecticForm {R : Type*} [Ring R] [StarRing R] (B X Y : R) : R :=
  star X * B * Y

/-- **Kähler Metric–Symplectic Pairing Identities**:
1. Skew-Hermitian antisymmetry: $\omega_B(X, Y)^\star = -\omega_B(Y, X)$,
2. Right clock-axis reduction to the metric pairing: $\omega_B(X, B Y) = -X^\star Y$,
3. Left-right bivector isometry: $\omega_B(B X, B Y) = \omega_B(X, Y)$. -/
theorem doubledSymplecticForm_kahler_identities {R : Type*} [Ring R] [StarRing R]
    {B : R} (hB_sq : B * B = -1) (hB_sa : star B = -B) (X Y : R) :
    star (doubledSymplecticForm B X Y) = -doubledSymplecticForm B Y X ∧
    doubledSymplecticForm B X (B * Y) = -(star X * Y) ∧
    doubledSymplecticForm B (B * X) (B * Y) = doubledSymplecticForm B X Y := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [doubledSymplecticForm]
    simp only [star_mul, star_star, hB_sa]
    noncomm_ring
  · dsimp [doubledSymplecticForm]
    calc star X * B * (B * Y) = star X * (B * B) * Y := by noncomm_ring
      _ = star X * (-1) * Y := by rw [hB_sq]
      _ = -(star X * Y) := by noncomm_ring
  · dsimp [doubledSymplecticForm]
    simp only [star_mul, hB_sa]
    calc star X * -B * B * (B * Y) = -(star X * (B * B) * B * Y) := by noncomm_ring
      _ = -(star X * (-1) * B * Y) := by rw [hB_sq]
      _ = star X * B * Y := by noncomm_ring

variable {A : Type*} [Ring A]

/-- Division-free Hestenes Cauchy–Riemann holomorphic ($B$-commuting) and anti-holomorphic
($B$-anticommuting) projections in $M_2(A)$. -/
def holomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M - Ω_op * M * Ω_op

def antiholomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M + Ω_op * M * Ω_op

/-- **Hestenes Rotor-Equivariance & Cauchy–Riemann Splitting Theorem**:
1. $\partial_{\mathrm{hol}}(M) + \bar{\partial}_{\mathrm{anti}}(M) = 2 \bullet M$,
2. $\partial_{\mathrm{hol}}(M)$ strictly commutes with the bivector $\Omega$,
3. $\bar{\partial}_{\mathrm{anti}}(M)$ strictly anticommutes with $\Omega$,
4. An operator $M \in M_2(A)$ commutes with $\Omega$ (is rotor-equivariant) iff $\bar{\partial}_{\mathrm{anti}}(M) = 0$. -/
theorem hestenes_cauchy_riemann_rotor_equivariance (M : Matrix (Fin 2) (Fin 2) A) :
    holomorphicProj M + antiholomorphicProj M = 2 • M ∧
    ⁅holomorphicProj M, (Ω_op : Matrix (Fin 2) (Fin 2) A)⁆ = 0 ∧
    anticomm (antiholomorphicProj M) (Ω_op : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    (⁅M, (Ω_op : Matrix (Fin 2) (Fin 2) A)⁆ = 0 ↔ antiholomorphicProj M = 0) := by
  have hΩ2 : (Ω_op : Matrix (Fin 2) (Fin 2) A) * Ω_op = -1 := by
    apply ext_fin2 <;> simp [Ω_op]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [holomorphicProj, antiholomorphicProj]
    rw [two_smul]; noncomm_ring
  · rw [Ring.lie_def]; dsimp [holomorphicProj]
    calc (M - Ω_op * M * Ω_op) * Ω_op - Ω_op * (M - Ω_op * M * Ω_op)
      _ = M * Ω_op - Ω_op * M * (Ω_op * Ω_op) - Ω_op * M + (Ω_op * Ω_op) * M * Ω_op := by
          noncomm_ring
      _ = M * Ω_op - Ω_op * M * (-1) - Ω_op * M + (-1) * M * Ω_op := by rw [hΩ2]
      _ = 0 := by noncomm_ring
  · dsimp [anticomm, antiholomorphicProj]
    calc (M + Ω_op * M * Ω_op) * Ω_op + Ω_op * (M + Ω_op * M * Ω_op)
      _ = M * Ω_op + Ω_op * M * (Ω_op * Ω_op) + Ω_op * M + (Ω_op * Ω_op) * M * Ω_op := by
          noncomm_ring
      _ = M * Ω_op + Ω_op * M * (-1) + Ω_op * M + (-1) * M * Ω_op := by rw [hΩ2]
      _ = 0 := by noncomm_ring
  · rw [Ring.lie_def]; dsimp [antiholomorphicProj]
    constructor
    · intro h
      have hM : M * Ω_op = Ω_op * M := sub_eq_zero.mp h
      calc M + Ω_op * M * Ω_op = M + Ω_op * (Ω_op * M) := by rw [← mul_assoc, ← hM, mul_assoc]
        _ = M + (Ω_op * Ω_op) * M := by noncomm_ring
        _ = M + (-1) * M := by rw [hΩ2]
        _ = 0 := by noncomm_ring
    · intro h
      calc M * Ω_op - Ω_op * M
        _ = (M + Ω_op * M * Ω_op) * Ω_op - Ω_op * M * (Ω_op * Ω_op) - Ω_op * M := by noncomm_ring
        _ = 0 * Ω_op - Ω_op * M * (-1) - Ω_op * M := by rw [h, hΩ2]
        _ = 0 := by noncomm_ring

end ArchetypeH2_HestenesBivectorAnalyticity

/-!
## Archetype $\mathcal{H}_3$: Square-Zero Chiral Hodge Decomposition & Hilbert–Schmidt Helmholtz Pythagoras (`SquareZeroChiralHodge` & `OperatorHodgeHelmholtz`)
-/

section ArchetypeH3_SquareZeroChiralHodgeAndHelmholtz

variable {B : Type*} [Ring B]

/-- **Square-Zero Chiral Hodge Decomposition in Any Noncommutative Ring $B$**:
Given $a, m \in B$ with $a^2 = 0, m^2 = 0, a m a = a, m a m = m$, the projections
$P_{\mathrm{ex}} = a m$, $P_{\mathrm{co}} = m a$, and $P_0 = 1 - a m - m a$ are mutually
orthogonal idempotents summing to $1$. -/
theorem square_zero_chiral_hodge_idempotents {a m : B}
    (ha2 : a * a = 0) (hm2 : m * m = 0)
    (hama : a * m * a = a) (hmam : m * a * m = m) (X : B) :
    let P_ex := a * m
    let P_co := m * a
    let P_0  := 1 - a * m - m * a
    P_ex * X + P_co * X + P_0 * X = X ∧
    P_ex * P_ex = P_ex ∧
    P_co * P_co = P_co ∧
    P_0 * P_0 = P_0 ∧
    P_ex * P_co = 0 ∧
    P_co * P_ex = 0 ∧
    P_ex * P_0 = 0 ∧
    P_co * P_0 = 0 := by
  refine ⟨by noncomm_ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (a * m) * (a * m) = (a * m * a) * m := by noncomm_ring
      _ = a * m := by rw [hama]
  · calc (m * a) * (m * a) = (m * a * m) * a := by noncomm_ring
      _ = m * a := by rw [hmam]
  · calc (1 - a * m - m * a) * (1 - a * m - m * a)
      _ = 1 - 2 * (a * m) - 2 * (m * a) + (a * m * a) * m + (m * a * m) * a +
          a * (m * m) * a + m * (a * a) * m := by noncomm_ring
      _ = 1 - 2 * (a * m) - 2 * (m * a) + a * m + m * a +
          a * 0 * a + m * 0 * m := by rw [hama, hmam, hm2, ha2]
      _ = 1 - a * m - m * a := by noncomm_ring
  · calc (a * m) * (m * a) = a * (m * m) * a := by noncomm_ring
      _ = a * 0 * a := by rw [hm2]
      _ = 0 := by noncomm_ring
  · calc (m * a) * (a * m) = m * (a * a) * m := by noncomm_ring
      _ = m * 0 * m := by rw [ha2]
      _ = 0 := by noncomm_ring
  · calc (a * m) * (1 - a * m - m * a)
      _ = a * m - (a * m * a) * m - a * (m * m) * a := by noncomm_ring
      _ = a * m - a * m - a * 0 * a := by rw [hama, hm2]
      _ = 0 := by noncomm_ring
  · calc (m * a) * (1 - a * m - m * a)
      _ = m * a - m * (a * a) * m - (m * a * m) * a := by noncomm_ring
      _ = m * a - m * 0 * m - m * a := by rw [ha2, hmam]
      _ = 0 := by noncomm_ring

/-- **Dirac–Hodge Kernel Theorem ($\ker(a+m) = \ker a \cap \ker m = \mathrm{ran}(P_0)$)**:
For any $X \in B$, $(a + m) X = 0 \iff (a X = 0 \wedge m X = 0) \iff (1 - a m - m a) X = X$. -/
theorem normalizedDirac_mul_eq_zero_iff_harmonic {a m : B}
    (ha2 : a * a = 0) (hm2 : m * m = 0)
    (hama : a * m * a = a) (hmam : m * a * m = m) (X : B) :
    ((a + m) * X = 0 ↔ (a * X = 0 ∧ m * X = 0)) ∧
    ((a + m) * X = 0 ↔ (1 - a * m - m * a) * X = X) := by
  have h_ker : (a + m) * X = 0 ↔ (a * X = 0 ∧ m * X = 0) := by
    constructor
    · intro h
      have ha : a * X = 0 := by
        calc a * X = (a * m * a) * X + a * (m * m) * X := by rw [hama, hm2]; noncomm_ring
          _ = a * m * ((a + m) * X) := by noncomm_ring
          _ = a * m * 0 := by rw [h]
          _ = 0 := mul_zero _
      have hm : m * X = 0 := by
        calc m * X = m * (a * a) * X + (m * a * m) * X := by rw [ha2, hmam]; noncomm_ring
          _ = m * a * ((a + m) * X) := by noncomm_ring
          _ = m * a * 0 := by rw [h]
          _ = 0 := mul_zero _
      exact ⟨ha, hm⟩
    · rintro ⟨ha, hm⟩
      calc (a + m) * X = a * X + m * X := add_mul a m X
        _ = 0 + 0 := by rw [ha, hm]
        _ = 0 := add_zero 0
  refine ⟨h_ker, ?_⟩
  rw [h_ker]
  constructor
  · rintro ⟨ha, hm⟩
    calc (1 - a * m - m * a) * X
      _ = X - a * (m * X) - m * (a * X) := by noncomm_ring
      _ = X - a * 0 - m * 0 := by rw [ha, hm]
      _ = X := by noncomm_ring
  · intro hP
    have ha : a * X = 0 := by
      calc a * X = a * ((1 - a * m - m * a) * X) := by rw [hP]
        _ = (a - a * m * a - (a * a) * m) * X := by noncomm_ring
        _ = (a - a - 0 * m) * X := by rw [hama, ha2]
        _ = 0 := by noncomm_ring
    have hm : m * X = 0 := by
      calc m * X = m * ((1 - a * m - m * a) * X) := by rw [hP]
        _ = (m - (m * m) * a - m * a * m) * X := by noncomm_ring
        _ = (m - 0 * a - m) * X := by rw [hm2, hmam]
        _ = 0 := by noncomm_ring
    exact ⟨ha, hm⟩

/-- **Operator Hodge–Helmholtz Irrotational/Rotational Duality & Hilbert–Schmidt Pythagoras**:
1. For any bivector phase $K \in B$ ($K^2 = -1$) and potential $H \in B$, $J_{\mathrm{irr}} = \⁅K, H⁆$
   and $J_{\mathrm{rot}} = K J_{\mathrm{irr}}$ satisfy $K J_{\mathrm{rot}} = -J_{\mathrm{irr}}$
   and $J_{\mathrm{irr}} = 0 \iff J_{\mathrm{rot}} = 0$,
2. In $M_2(A)$ over any $\star$-ring $A$, the four Helmholtz–Tetraktys channels
   $M_I = \iota(c_I)I, M_\Gamma = \iota(c_\Gamma)\Gamma_1, M_\Sigma = \iota(c_\Sigma)\Sigma, M_\Omega = \iota(c_\Omega)\Omega$
   satisfy the exact noncommutative Hilbert–Schmidt Pythagorean identity. -/
theorem operator_helmholtz_duality_and_hilbert_schmidt_pythagoras
    {A : Type*} [Ring A] [StarRing A] {K H : B} (hK : K * K = -1) (c_I c_Γ c_Σ c_Ω : A) :
    let J_irr := ⁅K, H⁆
    let J_rot := K * J_irr
    let M_I   : Matrix (Fin 2) (Fin 2) A := fiberEmbed c_I * 1
    let M_Γ   : Matrix (Fin 2) (Fin 2) A := fiberEmbed c_Γ * Γ₁_op
    let M_Σ   : Matrix (Fin 2) (Fin 2) A := fiberEmbed c_Σ * Σ_op
    let M_Ω   : Matrix (Fin 2) (Fin 2) A := fiberEmbed c_Ω * Ω_op
    K * J_rot = -J_irr ∧
    (J_irr = 0 ↔ J_rot = 0) ∧
    opTrace ((M_I + M_Γ + M_Σ + M_Ω)ᴴ * (M_I + M_Γ + M_Σ + M_Ω)) =
      opTrace (M_Iᴴ * M_I) + opTrace (M_Γᴴ * M_Γ) +
      opTrace (M_Σᴴ * M_Σ) + opTrace (M_Ωᴴ * M_Ω) := by
  have h_rot : K * (K * ⁅K, H⁆) = -⁅K, H⁆ := by
    calc K * (K * ⁅K, H⁆) = (K * K) * ⁅K, H⁆ := by noncomm_ring
      _ = (-1) * ⁅K, H⁆ := by rw [hK]
      _ = -⁅K, H⁆ := by noncomm_ring
  refine ⟨h_rot, ?_, ?_⟩
  · constructor
    · intro h; dsimp; rw [h, mul_zero]
    · intro h; dsimp at h
      calc ⁅K, H⁆ = -(-⁅K, H⁆) := by abel
        _ = -(K * (K * ⁅K, H⁆)) := by rw [h_rot]
        _ = -(K * 0) := by rw [h]
        _ = 0 := by noncomm_ring
  · dsimp [opTrace, fiberEmbed, Γ₁_op, Σ_op, Ω_op]
    simp; noncomm_ring

end ArchetypeH3_SquareZeroChiralHodgeAndHelmholtz

/-!
## Archetype $\mathcal{H}_4$: Noncommutative Jaynesian Gibbs State Covariance & Geometric Winding Cocycle (`JaynesFiniteState` & `WindingSnap`)
-/

section ArchetypeH4_JaynesGibbsAndWindingCocycle

variable {B : Type*} [Ring B]

def IsRingDeriv (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

theorem IsRingDeriv.map_one {d : B →+ B} (hd : IsRingDeriv d) : d 1 = 0 := by
  have h : d (1 * 1) = d 1 * 1 + 1 * d 1 := hd 1 1
  simp only [mul_one, one_mul] at h
  calc d 1 = d 1 + d 1 - d 1 := by abel
    _ = d 1 - d 1 := by rw [← h]
    _ = 0 := sub_self (d 1)

theorem IsRingDeriv.map_units_inv {d : B →+ B} (hd : IsRingDeriv d) (u : Bˣ) :
    d (↑u⁻¹ : B) = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by
  have h1 : d ((u : B) * (↑u⁻¹ : B)) = d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B) :=
    hd (u : B) (↑u⁻¹ : B)
  rw [Units.mul_inv, hd.map_one] at h1
  have h2 : (↑u⁻¹ : B) * (d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑u⁻¹ : B) * (u : B) * d (↑u⁻¹ : B) = d (↑u⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc d (↑u⁻¹ : B)
    _ = (↑u⁻¹ : B) * (u : B) * d (↑u⁻¹ : B) -
        (↑u⁻¹ : B) * (d (u : B) * (↑u⁻¹ : B) + (u : B) * d (↑u⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑u⁻¹ : B) * d (u : B) * (↑u⁻¹ : B) := by noncomm_ring

/-- Noncommutative logarithmic winding / Maurer–Cartan 1-form $\mathcal{W}_d(U) = d(U) U^{-1}$. -/
def windingForm (d : B →+ B) (U : Bˣ) : B :=
  d (U : B) * (↑U⁻¹ : B)

/-- **Geometric Winding Vanishing, Non-Abelian Additivity & Jaynesian Gibbs State Covariance**:
For any derivation $d : B \to+ B$ (`IsRingDeriv d`) and units $U, V, Z \in B^\times$:
1. $d(U) = 0 \implies \mathcal{W}_d(U) = 0$,
2. $\mathcal{W}_d(U V) = \mathcal{W}_d(U) + U \mathcal{W}_d(V) U^{-1}$,
3. If $d(W) = O W$ and $d(F) = 0$, the normalized Gibbs state $\rho = W Z^{-1}$ satisfies
   $d(W Z^{-1}) = O (W Z^{-1}) - (W Z^{-1})\mathcal{W}_d(Z)$ and
   $d(F W Z^{-1}) = (F O)(W Z^{-1}) - (F W Z^{-1})\mathcal{W}_d(Z)$. -/
theorem winding_cocycle_and_jaynes_gibbs_covariance
    {d : B →+ B} (hd : IsRingDeriv d) (U V Z : Bˣ)
    {W O F : B} (hW : d W = O * W) (hF : d F = 0) :
    (d (U : B) = 0 → windingForm d U = 0) ∧
    windingForm d (U * V) = windingForm d U + (U : B) * windingForm d V * (↑U⁻¹ : B) ∧
    d (W * (↑Z⁻¹ : B)) = O * (W * (↑Z⁻¹ : B)) - (W * (↑Z⁻¹ : B)) * windingForm d Z ∧
    d (F * (W * (↑Z⁻¹ : B))) =
      (F * O) * (W * (↑Z⁻¹ : B)) - (F * (W * (↑Z⁻¹ : B))) * windingForm d Z := by
  refine ⟨fun h0 => by dsimp [windingForm]; rw [h0, zero_mul], ?_, ?_, ?_⟩
  · dsimp [windingForm]
    have h_mul : ((U * V : Bˣ) : B) = (U : B) * (V : B) := rfl
    have h_inv : ((↑(U * V)⁻¹ : Bˣ) : B) = (↑V⁻¹ : B) * (↑U⁻¹ : B) := by
      rw [mul_inv_rev]; rfl
    have hV : (V : B) * (↑V⁻¹ : B) = 1 := Units.mul_inv V
    rw [h_mul, h_inv, hd (U : B) (V : B)]
    calc (d (U : B) * (V : B) + (U : B) * d (V : B)) * ((↑V⁻¹ : B) * (↑U⁻¹ : B))
      _ = d (U : B) * ((V : B) * (↑V⁻¹ : B)) * (↑U⁻¹ : B) +
          (U : B) * (d (V : B) * (↑V⁻¹ : B)) * (↑U⁻¹ : B) := by noncomm_ring
      _ = d (U : B) * (↑U⁻¹ : B) + (U : B) * (d (V : B) * (↑V⁻¹ : B)) * (↑U⁻¹ : B) := by
          rw [hV]; noncomm_ring
  · dsimp [windingForm]
    rw [hd W (↑Z⁻¹ : B), hW, hd.map_units_inv Z]
    noncomm_ring
  · rw [hd F (W * (↑Z⁻¹ : B)), hF, zero_mul, zero_add]
    dsimp [windingForm]
    rw [hd W (↑Z⁻¹ : B), hW, hd.map_units_inv Z]
    noncomm_ring

end ArchetypeH4_JaynesGibbsAndWindingCocycle

/-!
## Archetype $\mathcal{H}_5$: Cantor Markov Step, Discrete Laplacian Harmonicity & RG Block Decimation (`CantorRandomWalk`)
-/

section ArchetypeH5_CantorMarkovAndRGDecimation

variable {A : Type*} [Ring A]

/-- Division-free Cantor Markov averaging step $\mathcal{M}_{\mathrm{step}}(X) = X + \Sigma X \Sigma$. -/
def cantorMarkovStep (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  X + Σ_op * X * Σ_op

/-- Discrete Cantor Laplacian $\Delta_{\mathrm{Cantor}}(X) = \Sigma X \Sigma - X$. -/
def cantorLaplacian (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Σ_op * X * Σ_op - X

/-- Predicate for Cantor harmonicity: $\mathcal{M}_{\mathrm{step}}(X) = 2 \bullet X$. -/
def IsCantorHarmonic (X : Matrix (Fin 2) (Fin 2) A) : Prop :=
  cantorMarkovStep X = 2 • X

/-- Renormalization-Group (RG) 2-to-1 block decimation $\mathcal{R}_{\mathrm{RG}}(\mathbb{X}) = \mathbb{X}_{00} + \mathbb{X}_{11}$. -/
def rgBlockStep (𝕏 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) :
    Matrix (Fin 2) (Fin 2) A :=
  𝕏 0 0 + 𝕏 1 1

/-- **Cantor Markov Harmonicity, Semigroup Equilibration & RG Trajectory-Mean Conservation**:
1. $X$ is Cantor-harmonic iff $\Delta_{\mathrm{Cantor}}(X) = 0$,
2. Every constant fiber $\iota(a)$ is Cantor-harmonic,
3. $\mathcal{M}_{\mathrm{step}}(\mathcal{M}_{\mathrm{step}}(X)) = 2 \bullet \mathcal{M}_{\mathrm{step}}(X)$
   and $\Delta_{\mathrm{Cantor}}(\mathcal{M}_{\mathrm{step}}(X)) = 0$,
4. RG block decimation preserves the total trajectory trace:
   $\mathrm{Tr}_2(\mathcal{R}_{\mathrm{RG}}(\mathbb{X})) = \mathrm{Tr}_2(\mathbb{X}_{00}) + \mathrm{Tr}_2(\mathbb{X}_{11})$. -/
theorem cantor_markov_harmonicity_and_rg_invariance
    (a : A) (X : Matrix (Fin 2) (Fin 2) A)
    (𝕏 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) A)) :
    (IsCantorHarmonic X ↔ cantorLaplacian X = 0) ∧
    IsCantorHarmonic (fiberEmbed a) ∧
    cantorMarkovStep (cantorMarkovStep X) = 2 • cantorMarkovStep X ∧
    cantorLaplacian (cantorMarkovStep X) = 0 ∧
    opTrace (rgBlockStep 𝕏) = opTrace (𝕏 0 0) + opTrace (𝕏 1 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [IsCantorHarmonic, cantorMarkovStep, cantorLaplacian]
    rw [two_smul]
    constructor
    · intro h; calc Σ_op * X * Σ_op - X = (X + Σ_op * X * Σ_op) - (X + X) := by abel
        _ = 0 := by rw [h, sub_self]
    · intro h; calc X + Σ_op * X * Σ_op = (X + X) + (Σ_op * X * Σ_op - X) := by abel
        _ = X + X := by rw [h, add_zero]
  · dsimp [IsCantorHarmonic, cantorMarkovStep]
    apply ext_fin2 <;> simp [fiberEmbed, Σ_op, two_smul]
  · apply ext_fin2 <;> simp [cantorMarkovStep, Σ_op, two_smul] <;> abel
  · apply ext_fin2 <;> simp [cantorLaplacian, cantorMarkovStep, Σ_op] <;> abel
  · dsimp [opTrace, rgBlockStep]; simp; abel

end ArchetypeH5_CantorMarkovAndRGDecimation

end NoncommutativeAnalyticityHodgeJaynesSynthesis
```

## Turn 0036, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeDikinTetraktysSynthesis

/-!
## Archetype $\mathcal{D}\mathcal{T}_1$: Noncommutative Dikin–Burg–Stein Operator Metric & Self-Concordance
-/

section ArchetypeDT1_DikinBurgSteinBridge

variable {B : Type*} [Ring B]

def IsRingDeriv (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

theorem IsRingDeriv.map_one {d : B →+ B} (hd : IsRingDeriv d) : d 1 = 0 := by
  have h : d (1 * 1) = d 1 * 1 + 1 * d 1 := hd 1 1
  simp only [mul_one, one_mul] at h
  calc d 1 = d 1 + d 1 - d 1 := by abel
    _ = d 1 - d 1 := by rw [← h]
    _ = 0 := sub_self (d 1)

theorem IsRingDeriv.map_units_inv {d : B →+ B} (hd : IsRingDeriv d) (X : Bˣ) :
    d (↑X⁻¹ : B) = -(↑X⁻¹ : B) * d (X : B) * (↑X⁻¹ : B) := by
  have h1 : d ((X : B) * (↑X⁻¹ : B)) = d (X : B) * (↑X⁻¹ : B) + (X : B) * d (↑X⁻¹ : B) :=
    hd (X : B) (↑X⁻¹ : B)
  rw [Units.mul_inv, hd.map_one] at h1
  have h2 : (↑X⁻¹ : B) * (d (X : B) * (↑X⁻¹ : B) + (X : B) * d (↑X⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑X⁻¹ : B) * (X : B) * d (↑X⁻¹ : B) = d (↑X⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc d (↑X⁻¹ : B)
    _ = (↑X⁻¹ : B) * (X : B) * d (↑X⁻¹ : B) -
        (↑X⁻¹ : B) * (d (X : B) * (↑X⁻¹ : B) + (X : B) * d (↑X⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑X⁻¹ : B) * d (X : B) * (↑X⁻¹ : B) := by noncomm_ring

/-- Weyl–Dikin whitened relative displacement $\mathcal{W}_X(Y) = X^{-1}(Y - X) \in B$. -/
def dikinWhitened (X : Bˣ) (Y : B) : B :=
  (↑X⁻¹ : B) * (Y - (X : B))

/-- Dikin–Burg–Stein quadratic operator form $\mathcal{Q}_{\mathrm{Dikin}}(X, Y) = \mathcal{W}_X(Y)^\star \mathcal{W}_X(Y)$. -/
def dikinQuadraticForm [StarRing B] (X : Bˣ) (Y : B) : B :=
  star (dikinWhitened X Y) * dikinWhitened X Y

/-- Burg–Stein Hessian quadratic operator $\mathcal{H}_X(V) = X^{-1} V X^{-1}$. -/
def burgSteinHessian (X : Bˣ) (V : B) : B :=
  (↑X⁻¹ : B) * V * (↑X⁻¹ : B)

/-- **Non-Abelian $\mathrm{GL}_1(B)$-Gauge Invariance & Third-Order Operator Self-Concordance ($\mathcal{D}\mathcal{T}_1$)**:
1. Left scaling $(X, Y) \mapsto (G X, G Y)$ by any $G \in B^\times$ leaves $\mathcal{W}_X(Y)$ and
   $\mathcal{Q}_{\mathrm{Dikin}}(X, Y)$ strictly invariant,
2. For any derivation $d : B \to+ B$ and $d$-constant tangent $V \in B$ ($d V = 0$),
   $d(X^{-1} V X^{-1}) = -X^{-1} d(X) (X^{-1} V X^{-1}) - (X^{-1} V X^{-1}) d(X) X^{-1}$. -/
theorem dikin_gauge_invariance_and_burg_stein_self_concordance [StarRing B]
    {d : B →+ B} (hd : IsRingDeriv d) (G X : Bˣ) (Y V : B) (hV : d V = 0) :
    dikinWhitened (G * X) ((G : B) * Y) = dikinWhitened X Y ∧
    dikinQuadraticForm (G * X) ((G : B) * Y) = dikinQuadraticForm X Y ∧
    d (burgSteinHessian X V) =
      -(↑X⁻¹ : B) * d (X : B) * burgSteinHessian X V -
      burgSteinHessian X V * d (X : B) * (↑X⁻¹ : B) := by
  have h_whitened : dikinWhitened (G * X) ((G : B) * Y) = dikinWhitened X Y := by
    dsimp [dikinWhitened]
    have h_inv : ((↑(G * X)⁻¹ : Bˣ) : B) = (↑X⁻¹ : B) * (↑G⁻¹ : B) := by
      rw [mul_inv_rev]; rfl
    have h_coe : ((G * X : Bˣ) : B) = (G : B) * (X : B) := rfl
    have hG : (↑G⁻¹ : B) * (G : B) = 1 := Units.inv_mul G
    rw [h_inv, h_coe]
    calc (↑X⁻¹ : B) * (↑G⁻¹ : B) * ((G : B) * Y - (G : B) * (X : B))
      _ = (↑X⁻¹ : B) * ((↑G⁻¹ : B) * (G : B)) * (Y - (X : B)) := by noncomm_ring
      _ = (↑X⁻¹ : B) * (Y - (X : B)) := by rw [hG]; noncomm_ring
  refine ⟨h_whitened, by dsimp [dikinQuadraticForm]; rw [h_whitened], ?_⟩
  dsimp [burgSteinHessian]
  rw [hd ((↑X⁻¹ : B) * V) (↑X⁻¹ : B), hd (↑X⁻¹ : B) V, hV, hd.map_units_inv X]
  noncomm_ring

end ArchetypeDT1_DikinBurgSteinBridge

/-!
## Infrastructure: `mat2` Constructor & Simp Lemmas (Preventing `vecMul` Simp Blowups)
-/

/-- Explicit $2 \times 2$ matrix constructor wrapping `Matrix.of` to prevent `vecMul` simp blowups. -/
def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

def gamma1Op   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def P_plus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def P_minus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 0 1
def F_plus     : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def F_minus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

end Matrix2Simp

/-!
## Archetype $\mathcal{D}\mathcal{T}_2$: Modular $CPT$ Automorphism Triad & Klein-Four $\mathbb{Z}_2 \times \mathbb{Z}_2$ Grading
-/

section ArchetypeDT2_ModularCPTTriad

variable {A : Type*} [Ring A]

def cptP (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  gamma1Op * M * gamma1Op

def cptT (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  sigmaOp * M * sigmaOp

def cptC (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  -(omegaOp * M * omegaOp)

/-- **Modular $CPT$ Klein-Four Group Theorem ($\mathcal{D}\mathcal{T}_2$)**:
Since `gamma1Op * sigmaOp = -omegaOp` and `omegaOp^2 = -1`, the modular volume identity is
`gamma1Op * sigmaOp * omegaOp = 1`, and $(\mathcal{P}, \mathcal{T}, \mathcal{C})$ forms a Klein
four-group on $M_2(A)$ with $\mathcal{P}(\mathcal{T}(\mathcal{C}(M))) = M$. -/
theorem modular_cpt_klein_four_group (M : Matrix (Fin 2) (Fin 2) A) :
    (gamma1Op : Matrix (Fin 2) (Fin 2) A) * sigmaOp * omegaOp = 1 ∧
    cptP (cptP M) = M ∧
    cptT (cptT M) = M ∧
    cptC (cptC M) = M ∧
    cptP (cptT M) = cptC M ∧
    cptT (cptC M) = cptP M ∧
    cptC (cptP M) = cptT M ∧
    cptP (cptT (cptC M)) = M := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> simp [cptP, cptT, cptC, gamma1Op, sigmaOp, omegaOp])

end ArchetypeDT2_ModularCPTTriad

/-!
## Archetype $\mathcal{D}\mathcal{T}_3$: Clifford–Cayley Transform & Clock–Shift / Twin-Wave Duality
-/

section ArchetypeDT3_CliffordCayleyTransform

variable {A : Type*} [Ring A] [StarRing A]

def cayleyOp     : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp
def twinWaveSym  : Matrix (Fin 2) (Fin 2) A := 1 + sigmaOp
def twinWaveAnti : Matrix (Fin 2) (Fin 2) A := 1 - sigmaOp

theorem clifford_cayley_clock_shift_and_twin_wave_duality :
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * cayleyOpᴴ = 2 • (1 : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A)ᴴ * cayleyOp = 2 • (1 : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * gamma1Op * cayleyOpᴴ = 2 • (sigmaOp : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * sigmaOp * cayleyOpᴴ = -(2 • (gamma1Op : Matrix (Fin 2) (Fin 2) A)) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * omegaOp * cayleyOpᴴ = 2 • (omegaOp : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * P_plus * cayleyOpᴴ = twinWaveSym ∧
    (cayleyOp : Matrix (Fin 2) (Fin 2) A) * P_minus * cayleyOpᴴ = twinWaveAnti := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [cayleyOp, twinWaveSym, twinWaveAnti, gamma1Op, sigmaOp, omegaOp,
            P_plus, P_minus, two_smul] <;>
      abel)

end ArchetypeDT3_CliffordCayleyTransform

/-!
## Archetype $\mathcal{D}\mathcal{T}_4$: Hyperbolic Mellin Time-Focusing on Source ($0$) & Sink ($\infty$) Twin Waves
-/

section ArchetypeDT4_HyperbolicTimeFocusingTwinWaves

variable {A : Type*} [Ring A]

def mellinFocus (u : Aˣ) : Matrix (Fin 2) (Fin 2) A :=
  mat2 (u : A) 0 0 (↑u⁻¹ : A)

theorem hyperbolic_time_focusing_twin_waves (u : Aˣ) (a b : A) :
    mellinFocus u * (fiberEmbed a * F_plus) * mellinFocus u⁻¹ =
      fiberEmbed ((u : A) * a * (u : A)) * F_plus ∧
    mellinFocus u * (fiberEmbed b * F_minus) * mellinFocus u⁻¹ =
      fiberEmbed ((↑u⁻¹ : A) * b * (↑u⁻¹ : A)) * F_minus ∧
    (fiberEmbed ((u : A) * a * (u : A)) * F_plus) *
    (fiberEmbed ((↑u⁻¹ : A) * b * (↑u⁻¹ : A)) * F_minus) =
      fiberEmbed ((u : A) * a * b * (↑u⁻¹ : A)) * P_plus := by
  have h1 : (u : A) * (↑u⁻¹ : A) = 1 := Units.mul_inv u
  refine ⟨?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_plus, mul_assoc]
  · apply ext_fin2 <;> simp [mellinFocus, fiberEmbed, F_minus, mul_assoc]
  · apply ext_fin2
    · simp [fiberEmbed, F_plus, F_minus, P_plus]
      calc (u : A) * a * (u : A) * ((↑u⁻¹ : A) * b * (↑u⁻¹ : A))
        _ = (u : A) * a * ((u : A) * (↑u⁻¹ : A)) * b * (↑u⁻¹ : A) := by noncomm_ring
        _ = (u : A) * a * b * (↑u⁻¹ : A) := by rw [h1]; noncomm_ring
    · simp [fiberEmbed, F_plus, F_minus, P_plus]
    · simp [fiberEmbed, F_plus, F_minus, P_plus]
    · simp [fiberEmbed, F_plus, F_minus, P_plus]

end ArchetypeDT4_HyperbolicTimeFocusingTwinWaves

/-!
## Archetype $\mathcal{D}\mathcal{T}_5$: Noncommutative Characteristic Polynomial & The Four Geometric Flows
-/

section ArchetypeDT5_NoncommutativeCharpolyAndFourFlows

variable {A : Type*} [Ring A]

def flowGen (cGamma cSigma cOmega : A) : Matrix (Fin 2) (Fin 2) A :=
  fiberEmbed cGamma * gamma1Op + fiberEmbed cSigma * sigmaOp + fiberEmbed cOmega * omegaOp

theorem noncommutative_charpoly_casimir_and_lie_obstruction (cGamma cSigma cOmega : A) :
    flowGen cGamma cSigma cOmega * flowGen cGamma cSigma cOmega =
      fiberEmbed (cGamma * cGamma + cSigma * cSigma - cOmega * cOmega) * 1 +
      fiberEmbed ⁅cSigma, cOmega⁆ * gamma1Op +
      fiberEmbed ⁅cOmega, cGamma⁆ * sigmaOp -
      fiberEmbed ⁅cGamma, cSigma⁆ * omegaOp := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp] <;> noncomm_ring

theorem four_geometric_flows_classification (cI a b : A) (hab : ⁅a, b⁆ = 0) :
    flowGen a 0 0 * flowGen a 0 0 = fiberEmbed (a * a) ∧
    flowGen 0 a 0 * flowGen 0 a 0 = fiberEmbed (a * a) ∧
    flowGen 0 0 a * flowGen 0 0 a = -fiberEmbed (a * a) ∧
    flowGen 0 a a = 2 • (fiberEmbed a * F_minus) ∧
    flowGen 0 a (-a) = 2 • (fiberEmbed a * F_plus) ∧
    flowGen 0 a a * flowGen 0 a a = 0 ∧
    (1 + flowGen 0 a a) * (1 - flowGen 0 a a) = 1 ∧
    ((fiberEmbed cI + flowGen a 0 b) - fiberEmbed cI) *
    ((fiberEmbed cI + flowGen a 0 b) - fiberEmbed cI) =
      fiberEmbed (a * a - b * b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp, F_minus, two_smul]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp, F_plus, two_smul]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
  · rw [add_sub_cancel_left, noncommutative_charpoly_casimir_and_lie_obstruction]
    have hba : ⁅b, a⁆ = 0 := by rw [Ring.lie_def] at hab ⊢; noncomm_ring [hab]
    rw [hba]; apply ext_fin2 <;> simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end ArchetypeDT5_NoncommutativeCharpolyAndFourFlows

/-!
## Archetype $\mathcal{D}\mathcal{T}_6$ & $\mathcal{D}\mathcal{T}_7$: Chained Tetraktys Transform & The $10 + 6 = 16$ Symplectic Split
-/

section ArchetypeDT6_DT7_ChainedTetraktysAndSymplecticSplit

variable {A : Type*} [Ring A]

def peirceFiberLift (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  P_plus * X * P_plus + sigmaOp * P_plus * X * P_plus * sigmaOp

def mellinCoeffI (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M + sigmaOp * M * sigmaOp)
def mellinCoeffGamma (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M - sigmaOp * M * sigmaOp)
def mellinCoeffSigma (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M * sigmaOp + sigmaOp * M)
def mellinCoeffOmega (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (sigmaOp * M - M * sigmaOp)

theorem clifford_mellin_walsh_inversion (M : Matrix (Fin 2) (Fin 2) A) :
    mellinCoeffI M * 1 +
    mellinCoeffGamma M * gamma1Op +
    mellinCoeffSigma M * sigmaOp +
    mellinCoeffOmega M * omegaOp = 2 • M := by
  apply ext_fin2 <;>
    simp [mellinCoeffI, mellinCoeffGamma, mellinCoeffSigma, mellinCoeffOmega,
      peirceFiberLift, P_plus, gamma1Op, sigmaOp, omegaOp, two_smul] <;>
    abel

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

def tetraktysMode
    (Cout : NestedMat A → NestedMat A)
    (Cin : Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) A)
    (M : NestedMat A) : NestedMat A :=
  fiberEmbed (Cin (Cout M 0 0))

theorem outer_mode_inner_expansion
    (Cout : NestedMat A → NestedMat A) (M : NestedMat A)
    (h_diag : Cout M = fiberEmbed (Cout M 0 0)) :
    tetraktysMode Cout mellinCoeffI M * fiberEmbed 1 +
    tetraktysMode Cout mellinCoeffGamma M * fiberEmbed gamma1Op +
    tetraktysMode Cout mellinCoeffSigma M * fiberEmbed sigmaOp +
    tetraktysMode Cout mellinCoeffOmega M * fiberEmbed omegaOp =
      2 • Cout M := by
  have h_inv := clifford_mellin_walsh_inversion (Cout M 0 0)
  rw [h_diag]
  apply ext_fin2 <;> simp [tetraktysMode, fiberEmbed, ← h_inv, two_smul]

theorem chained_tetraktys_16_channel_inversion (M : NestedMat A) :
    (tetraktysMode mellinCoeffI mellinCoeffI M * fiberEmbed 1 +
     tetraktysMode mellinCoeffI mellinCoeffGamma M * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffI mellinCoeffSigma M * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffI mellinCoeffOmega M * fiberEmbed omegaOp) * 1 +
    (tetraktysMode mellinCoeffGamma mellinCoeffI M * fiberEmbed 1 +
     tetraktysMode mellinCoeffGamma mellinCoeffGamma M * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffGamma mellinCoeffSigma M * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffGamma mellinCoeffOmega M * fiberEmbed omegaOp) * gamma1Op +
    (tetraktysMode mellinCoeffSigma mellinCoeffI M * fiberEmbed 1 +
     tetraktysMode mellinCoeffSigma mellinCoeffGamma M * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffSigma mellinCoeffSigma M * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffSigma mellinCoeffOmega M * fiberEmbed omegaOp) * sigmaOp +
    (tetraktysMode mellinCoeffOmega mellinCoeffI M * fiberEmbed 1 +
     tetraktysMode mellinCoeffOmega mellinCoeffGamma M * fiberEmbed gamma1Op +
     tetraktysMode mellinCoeffOmega mellinCoeffSigma M * fiberEmbed sigmaOp +
     tetraktysMode mellinCoeffOmega mellinCoeffOmega M * fiberEmbed omegaOp) * omegaOp =
      4 • M := by
  have hI : mellinCoeffI M = fiberEmbed (mellinCoeffI M 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffI, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  have hG : mellinCoeffGamma M = fiberEmbed (mellinCoeffGamma M 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffGamma, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  have hS : mellinCoeffSigma M = fiberEmbed (mellinCoeffSigma M 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffSigma, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  have hO : mellinCoeffOmega M = fiberEmbed (mellinCoeffOmega M 0 0) := by
    apply ext_fin2 <;> simp [mellinCoeffOmega, peirceFiberLift, fiberEmbed, P_plus, sigmaOp]
  rw [outer_mode_inner_expansion mellinCoeffI M hI,
      outer_mode_inner_expansion mellinCoeffGamma M hG,
      outer_mode_inner_expansion mellinCoeffSigma M hS,
      outer_mode_inner_expansion mellinCoeffOmega M hO]
  have h_outer := clifford_mellin_walsh_inversion M
  calc (2 • mellinCoeffI M) * 1 + (2 • mellinCoeffGamma M) * gamma1Op +
       (2 • mellinCoeffSigma M) * sigmaOp + (2 • mellinCoeffOmega M) * omegaOp
    _ = 2 • (mellinCoeffI M * 1 + mellinCoeffGamma M * gamma1Op +
             mellinCoeffSigma M * sigmaOp + mellinCoeffOmega M * omegaOp) := by
        simp only [two_smul]; noncomm_ring
    _ = 2 • (2 • M) := by rw [h_outer]
    _ = (2 * 2) • M := by rw [← mul_smul]
    _ = 4 • M := rfl

section SymplecticTetraktysSplit

variable [StarRing A]

def J_sp : NestedMat A := omegaOp

def IsSymplecticTetraktys (X : NestedMat A) : Prop :=
  Xᴴ * J_sp + J_sp * X = 0

theorem pythagorean_ten_symplectic_tetraktys_generators :
    (∀ X Y : NestedMat A,
      IsSymplecticTetraktys X → IsSymplecticTetraktys Y → IsSymplecticTetraktys ⁅X, Y⁆) ∧
    IsSymplecticTetraktys (fiberEmbed (omegaOp : Matrix (Fin 2) (Fin 2) A) * 1) ∧
    IsSymplecticTetraktys (fiberEmbed (1 : Matrix (Fin 2) (Fin 2) A) * gamma1Op) ∧
    IsSymplecticTetraktys (fiberEmbed (1 : Matrix (Fin 2) (Fin 2) A) * sigmaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (1 : Matrix (Fin 2) (Fin 2) A) * omegaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (gamma1Op : Matrix (Fin 2) (Fin 2) A) * omegaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (sigmaOp : Matrix (Fin 2) (Fin 2) A) * omegaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (gamma1Op : Matrix (Fin 2) (Fin 2) A) * gamma1Op) ∧
    IsSymplecticTetraktys (fiberEmbed (sigmaOp : Matrix (Fin 2) (Fin 2) A) * gamma1Op) ∧
    IsSymplecticTetraktys (fiberEmbed (gamma1Op : Matrix (Fin 2) (Fin 2) A) * sigmaOp) ∧
    IsSymplecticTetraktys (fiberEmbed (sigmaOp : Matrix (Fin 2) (Fin 2) A) * sigmaOp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y hX hY
    dsimp [IsSymplecticTetraktys] at *
    have hX' : Xᴴ * J_sp = -(J_sp * X) := eq_neg_of_add_eq_zero_left hX
    have hY' : Yᴴ * J_sp = -(J_sp * Y) := eq_neg_of_add_eq_zero_left hY
    rw [Ring.lie_def]
    calc (X * Y - Y * X)ᴴ * J_sp + J_sp * (X * Y - Y * X)
      _ = (Yᴴ * Xᴴ - Xᴴ * Yᴴ) * J_sp + J_sp * (X * Y - Y * X) := by
          rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
      _ = Yᴴ * (Xᴴ * J_sp) - Xᴴ * (Yᴴ * J_sp) + J_sp * (X * Y - Y * X) := by noncomm_ring
      _ = Yᴴ * -(J_sp * X) - Xᴴ * -(J_sp * Y) + J_sp * (X * Y - Y * X) := by rw [hX', hY']
      _ = -((Yᴴ * J_sp) * X) + (Xᴴ * J_sp) * Y + J_sp * (X * Y - Y * X) := by noncomm_ring
      _ = -(-(J_sp * Y) * X) + -(J_sp * X) * Y + J_sp * (X * Y - Y * X) := by rw [hX', hY']
      _ = 0 := by noncomm_ring
  all_goals
    dsimp [IsSymplecticTetraktys, J_sp]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end SymplecticTetraktysSplit

end ArchetypeDT6_DT7_ChainedTetraktysAndSymplecticSplit

end NoncommutativeDikinTetraktysSynthesis
```

## Turn 0039, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeAnalyticitySynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op           : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp            : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp            : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def chiralSheetPlus    : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def chiralSheetMinus   : Matrix (Fin 2) (Fin 2) A := mat2 0 0 0 1
def isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

end Matrix2Simp

/-!
## Stratum $\mathcal{H}_1$: Coupled Isotropic Witt Sheets & Complex-Structure Sheet Reversal
-/

section StratumH1_CoupledIsotropicSheets

variable {A : Type*} [Ring A]

theorem isotropicSheetPlus_sq :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetPlus = 0 := by
  apply ext_fin2 <;> simp [isotropicSheetPlus]

theorem isotropicSheetMinus_sq :
    (isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetMinus = 0 := by
  apply ext_fin2 <;> simp [isotropicSheetMinus]

theorem isotropicSheetPlus_mul_minus :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetMinus = chiralSheetPlus := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, chiralSheetPlus]

theorem isotropicSheetMinus_mul_plus :
    (isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A) * isotropicSheetPlus = chiralSheetMinus := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, chiralSheetMinus]

theorem isotropicSheets_anticommute :
    anticomm (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) isotropicSheetMinus = 1 ∧
    ⁅(isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A), isotropicSheetMinus⁆ = gamma1Op := by
  constructor
  · apply ext_fin2 <;> simp [anticomm, isotropicSheetPlus, isotropicSheetMinus]
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, gamma1Op]

theorem isotropicSheets_sum_eq_r0 :
    (isotropicSheetPlus : Matrix (Fin 2) (Fin 2) A) + isotropicSheetMinus = sigmaOp := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, sigmaOp]

theorem isotropicSheets_sub_eq_r5 :
    (isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A) - isotropicSheetPlus = omegaOp := by
  apply ext_fin2 <;> simp [isotropicSheetPlus, isotropicSheetMinus, omegaOp]

theorem complexStructure_reverses_chiral_sheets :
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * chiralSheetPlus * omegaOp) = chiralSheetMinus ∧
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * chiralSheetMinus * omegaOp) = chiralSheetPlus ∧
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * gamma1Op * omegaOp) = -gamma1Op ∧
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * isotropicSheetPlus * omegaOp) = -isotropicSheetMinus ∧
    -((omegaOp : Matrix (Fin 2) (Fin 2) A) * isotropicSheetMinus * omegaOp) = -isotropicSheetPlus := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [omegaOp, chiralSheetPlus, chiralSheetMinus, gamma1Op,
            isotropicSheetPlus, isotropicSheetMinus])

end StratumH1_CoupledIsotropicSheets

/-!
## Stratum $\mathcal{H}_2$: Bivector-Rotor Holomorphicity & Kähler Metric–Symplectic Pairing
-/

section StratumH2_BivectorRotorAndKahler

def doubledSymplecticForm {R : Type*} [Ring R] [StarRing R] (B X Y : R) : R :=
  star X * B * Y

theorem doubledSymplecticForm_kahler_identities {R : Type*} [Ring R] [StarRing R]
    {B : R} (hB_sq : B * B = -1) (hB_sa : star B = -B) (X Y : R) :
    star (doubledSymplecticForm B X Y) = -doubledSymplecticForm B Y X ∧
    doubledSymplecticForm B X (B * Y) = -(star X * Y) ∧
    doubledSymplecticForm B (B * X) (B * Y) = doubledSymplecticForm B X Y := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [doubledSymplecticForm]
    simp only [star_mul, star_star, hB_sa]
    noncomm_ring
  · dsimp [doubledSymplecticForm]
    calc star X * B * (B * Y) = star X * (B * B) * Y := by noncomm_ring
      _ = star X * (-1) * Y := by rw [hB_sq]
      _ = -(star X * Y) := by noncomm_ring
  · dsimp [doubledSymplecticForm]
    simp only [star_mul, hB_sa]
    calc star X * -B * B * (B * Y) = -(star X * (B * B) * B * Y) := by noncomm_ring
      _ = -(star X * (-1) * B * Y) := by rw [hB_sq]
      _ = star X * B * Y := by noncomm_ring

variable {A : Type*} [Ring A]

def holomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M - omegaOp * M * omegaOp

def antiholomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M + omegaOp * M * omegaOp

theorem hestenes_cauchy_riemann_rotor_equivariance (M : Matrix (Fin 2) (Fin 2) A) :
    holomorphicProj M + antiholomorphicProj M = 2 • M ∧
    ⁅holomorphicProj M, (omegaOp : Matrix (Fin 2) (Fin 2) A)⁆ = 0 ∧
    anticomm (antiholomorphicProj M) (omegaOp : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    (⁅M, (omegaOp : Matrix (Fin 2) (Fin 2) A)⁆ = 0 ↔ antiholomorphicProj M = 0) := by
  have hO2 : (omegaOp : Matrix (Fin 2) (Fin 2) A) * omegaOp = -1 := by
    apply ext_fin2 <;> simp [omegaOp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [holomorphicProj, antiholomorphicProj]
    rw [two_smul]; noncomm_ring
  · rw [Ring.lie_def]; dsimp [holomorphicProj]
    calc (M - omegaOp * M * omegaOp) * omegaOp - omegaOp * (M - omegaOp * M * omegaOp)
      _ = M * omegaOp - omegaOp * M * (omegaOp * omegaOp) -
          omegaOp * M + (omegaOp * omegaOp) * M * omegaOp := by noncomm_ring
      _ = M * omegaOp - omegaOp * M * (-1) - omegaOp * M + (-1) * M * omegaOp := by rw [hO2]
      _ = 0 := by noncomm_ring
  · dsimp [anticomm, antiholomorphicProj]
    calc (M + omegaOp * M * omegaOp) * omegaOp + omegaOp * (M + omegaOp * M * omegaOp)
      _ = M * omegaOp + omegaOp * M * (omegaOp * omegaOp) +
          omegaOp * M + (omegaOp * omegaOp) * M * omegaOp := by noncomm_ring
      _ = M * omegaOp + omegaOp * M * (-1) + omegaOp * M + (-1) * M * omegaOp := by rw [hO2]
      _ = 0 := by noncomm_ring
  · rw [Ring.lie_def]; dsimp [antiholomorphicProj]
    constructor
    · intro h
      have hM : M * omegaOp = omegaOp * M := sub_eq_zero.mp h
      calc M + omegaOp * M * omegaOp
        _ = M + omegaOp * (omegaOp * M) := by rw [← mul_assoc, ← hM, mul_assoc]
        _ = M + (omegaOp * omegaOp) * M := by noncomm_ring
        _ = M + (-1) * M := by rw [hO2]
        _ = 0 := by noncomm_ring
    · intro h
      calc M * omegaOp - omegaOp * M
        _ = (M + omegaOp * M * omegaOp) * omegaOp -
            omegaOp * M * (omegaOp * omegaOp) - omegaOp * M := by noncomm_ring
        _ = 0 * omegaOp - omegaOp * M * (-1) - omegaOp * M := by rw [h, hO2]
        _ = 0 := by noncomm_ring

end StratumH2_BivectorRotorAndKahler

/-!
## Stratum $\mathcal{H}_3$: Square-Zero Chiral Hodge Decomposition & Hilbert–Schmidt Helmholtz Pythagoras
-/

section StratumH3_SquareZeroChiralHodgeAndHelmholtz

variable {B : Type*} [Ring B]

def normalizedDirac (d δ : B) : B := d + δ

theorem square_zero_chiral_hodge_idempotents {d δ : B}
    (hd2 : d * d = 0) (hδ2 : δ * δ = 0)
    (hdδd : d * δ * d = d) (hδdδ : δ * d * δ = δ) (x : B) :
    let e_exact   := d * δ
    let e_coexact := δ * d
    let e_harm    := 1 - (d * δ + δ * d)
    e_exact * x + e_coexact * x + e_harm * x = x ∧
    e_exact * e_exact = e_exact ∧
    e_coexact * e_coexact = e_coexact ∧
    e_harm * e_harm = e_harm ∧
    e_exact * e_coexact = 0 ∧
    e_coexact * e_exact = 0 ∧
    e_exact * e_harm = 0 ∧
    e_coexact * e_harm = 0 := by
  refine ⟨by noncomm_ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (d * δ) * (d * δ) = (d * δ * d) * δ := by noncomm_ring
      _ = d * δ := by rw [hdδd]
  · calc (δ * d) * (δ * d) = (δ * d * δ) * d := by noncomm_ring
      _ = δ * d := by rw [hδdδ]
  · calc (1 - (d * δ + δ * d)) * (1 - (d * δ + δ * d))
      _ = 1 - 2 * (d * δ) - 2 * (δ * d) + (d * δ * d) * δ + (δ * d * δ) * d +
          d * (δ * δ) * d + δ * (d * d) * δ := by noncomm_ring
      _ = 1 - 2 * (d * δ) - 2 * (δ * d) + d * δ + δ * d +
          d * 0 * d + δ * 0 * δ := by rw [hdδd, hδdδ, hδ2, hd2]
      _ = 1 - (d * δ + δ * d) := by noncomm_ring
  · calc (d * δ) * (δ * d) = d * (δ * δ) * d := by noncomm_ring
      _ = d * 0 * d := by rw [hδ2]
      _ = 0 := by noncomm_ring
  · calc (δ * d) * (d * δ) = δ * (d * d) * δ := by noncomm_ring
      _ = δ * 0 * δ := by rw [hd2]
      _ = 0 := by noncomm_ring
  · calc (d * δ) * (1 - (d * δ + δ * d))
      _ = d * δ - (d * δ * d) * δ - d * (δ * δ) * d := by noncomm_ring
      _ = d * δ - d * δ - d * 0 * d := by rw [hdδd, hδ2]
      _ = 0 := by noncomm_ring
  · calc (δ * d) * (1 - (d * δ + δ * d))
      _ = δ * d - δ * (d * d) * δ - (δ * d * δ) * d := by noncomm_ring
      _ = δ * d - δ * 0 * δ - δ * d := by rw [hd2, hδdδ]
      _ = 0 := by noncomm_ring

theorem normalizedDirac_mul_eq_zero_iff_harmonic {d δ : B}
    (hd2 : d * d = 0) (hδ2 : δ * δ = 0)
    (hdδd : d * δ * d = d) (hδdδ : δ * d * δ = δ) (x : B) :
    (normalizedDirac d δ * x = 0 ↔ (d * x = 0 ∧ δ * x = 0)) ∧
    (normalizedDirac d δ * x = 0 ↔ (1 - (d * δ + δ * d)) * x = x) := by
  dsimp [normalizedDirac]
  have h_ker : (d + δ) * x = 0 ↔ (d * x = 0 ∧ δ * x = 0) := by
    constructor
    · intro h
      have hd : d * x = 0 := by
        calc d * x = (d * δ * d) * x + d * (δ * δ) * x := by rw [hdδd, hδ2]; noncomm_ring
          _ = d * δ * ((d + δ) * x) := by noncomm_ring
          _ = d * δ * 0 := by rw [h]
          _ = 0 := mul_zero _
      have hδ : δ * x = 0 := by
        calc δ * x = δ * (d * d) * x + (δ * d * δ) * x := by rw [hd2, hδdδ]; noncomm_ring
          _ = δ * d * ((d + δ) * x) := by noncomm_ring
          _ = δ * d * 0 := by rw [h]
          _ = 0 := mul_zero _
      exact ⟨hd, hδ⟩
    · rintro ⟨hd, hδ⟩
      calc (d + δ) * x = d * x + δ * x := add_mul d δ x
        _ = 0 + 0 := by rw [hd, hδ]
        _ = 0 := add_zero 0
  refine ⟨h_ker, ?_⟩
  rw [h_ker]
  constructor
  · rintro ⟨hd, hδ⟩
    calc (1 - (d * δ + δ * d)) * x
      _ = x - d * (δ * x) - δ * (d * x) := by noncomm_ring
      _ = x - d * 0 - δ * 0 := by rw [hd, hδ]
      _ = x := by noncomm_ring
  · intro hP
    have hd : d * x = 0 := by
      calc d * x = d * ((1 - (d * δ + δ * d)) * x) := by rw [hP]
        _ = (d - d * δ * d - (d * d) * δ) * x := by noncomm_ring
        _ = (d - d - 0 * δ) * x := by rw [hdδd, hd2]
        _ = 0 := by noncomm_ring
    have hδ : δ * x = 0 := by
      calc δ * x = δ * ((1 - (d * δ + δ * d)) * x) := by rw [hP]
        _ = (δ - (δ * δ) * d - δ * d * δ) * x := by noncomm_ring
        _ = (δ - 0 * d - δ) * x := by rw [hδ2, hδdδ]
        _ = 0 := by noncomm_ring
    exact ⟨hd, hδ⟩

/-- **Noncommutative Hilbert–Schmidt Helmholtz Orthogonality & Pythagoras**:
For scalar mode $S = \mathrm{diag}(s, s)$ ($s^\star = s$) and chiral mode $K = \mathrm{diag}(k, -k)$
($k^\star = -k$) in $M_2(A)$:
1. $\mathrm{Tr}(S^\dagger K) = 0$ and $\mathrm{Tr}(K^\dagger S) = 0$ (even when $s k \neq k s$),
2. $K S = S K \iff k s = s k$,
3. $\mathrm{Tr}((S + K)^\dagger (S + K)) = \mathrm{Tr}(S^\dagger S) + \mathrm{Tr}(K^\dagger K)$. -/
theorem operator_helmholtz_duality_and_hilbert_schmidt_pythagoras
    {A : Type*} [Ring A] [StarRing A] (s k : A) :
    let S : Matrix (Fin 2) (Fin 2) A := mat2 s 0 0 s
    let K : Matrix (Fin 2) (Fin 2) A := mat2 k 0 0 (-k)
    Matrix.trace (Sᴴ * K) = 0 ∧
    Matrix.trace (Kᴴ * S) = 0 ∧
    (K * S = S * K ↔ k * s = s * k) ∧
    Matrix.trace ((S + K)ᴴ * (S + K)) =
      Matrix.trace (Sᴴ * S) + Matrix.trace (Kᴴ * K) := by
  refine ⟨by simp; noncomm_ring, by simp; noncomm_ring, ?_, by simp; noncomm_ring⟩
  constructor
  · intro h
    have h00 : (mat2 k 0 0 (-k) * mat2 s 0 0 s) 0 0 =
               (mat2 s 0 0 s * mat2 k 0 0 (-k)) 0 0 := by rw [h]
    simpa using h00
  · intro hks
    apply ext_fin2
    · simp [hks]
    · simp
    · simp
    · simp; rw [← neg_mul, ← mul_neg, hks]

end StratumH3_SquareZeroChiralHodgeAndHelmholtz

/-!
## Stratum $\mathcal{H}_4$: Noncommutative Leibniz Derivations, Winding Cocycle & Jaynesian Gibbs Covariance
-/

section StratumH4_WindingCocycleAndJaynesGibbsCovariance

variable {B : Type*} [Ring B]

def IsRingDeriv (D : B →+ B) : Prop :=
  ∀ a b : B, D (a * b) = D a * b + a * D b

/-- Left-trivialized Maurer–Cartan winding 1-form $\omega_D(u) = u^{-1} D(u) \in B$. -/
def windingForm (D : B →+ B) (u : Bˣ) : B :=
  (↑u⁻¹ : B) * D (u : B)

/-- **Noncommutative Winding Cocycle Law**:
$\omega_D(u v) = v^{-1} \omega_D(u) v + \omega_D(v)$ for any derivation $D$ and units $u, v \in B^\times$. -/
theorem windingForm_mul {D : B →+ B} (hD : IsRingDeriv D) (u v : Bˣ) :
    windingForm D (u * v) =
      (↑v⁻¹ : B) * windingForm D u * (v : B) + windingForm D v := by
  dsimp [windingForm]
  have h_coe : ((u * v : Bˣ) : B) = (u : B) * (v : B) := rfl
  have h_inv : ((↑(u * v)⁻¹ : Bˣ) : B) = (↑v⁻¹ : B) * (↑u⁻¹ : B) := by
    rw [mul_inv_rev]; rfl
  have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
  rw [h_coe, h_inv, hD (u : B) (v : B)]
  calc (↑v⁻¹ : B) * (↑u⁻¹ : B) * (D (u : B) * (v : B) + (u : B) * D (v : B))
    _ = (↑v⁻¹ : B) * ((↑u⁻¹ : B) * D (u : B)) * (v : B) +
        (↑v⁻¹ : B) * ((↑u⁻¹ : B) * (u : B)) * D (v : B) := by noncomm_ring
    _ = (↑v⁻¹ : B) * ((↑u⁻¹ : B) * D (u : B)) * (v : B) +
        (↑v⁻¹ : B) * D (v : B) := by rw [hu]; noncomm_ring

/-- Right-weighted and left-weighted noncommutative Gibbs expectations and bimodule covariance. -/
def gibbsExpectationR {n : ℕ} (w f : Fin n → B) : B :=
  ∑ i : Fin n, f i * w i

def gibbsExpectationL {n : ℕ} (w g : Fin n → B) : B :=
  ∑ i : Fin n, w i * g i

def gibbsCrossMoment {n : ℕ} (w f g : Fin n → B) : B :=
  ∑ i : Fin n, f i * w i * g i

def gibbsCovariance {n : ℕ} (w f g : Fin n → B) : B :=
  ∑ i : Fin n, (f i - gibbsExpectationR w f) * w i * (g i - gibbsExpectationL w g)

/-- **Noncommutative Bimodule Jaynesian Gibbs Covariance Identity**:
For any operator weights $w : \mathrm{Fin}\,n \to B$ satisfying $\sum_i w_i = 1$ and arbitrary
noncommuting observables $f, g : \mathrm{Fin}\,n \to B$,
$\mathrm{Cov}_w(f, g) = \sum_i f_i w_i g_i - \mathbb{E}_R(w, f) \mathbb{E}_L(w, g)$. -/
theorem winding_cocycle_and_jaynes_gibbs_covariance
    {D : B →+ B} (hD : IsRingDeriv D) (u v : Bˣ)
    {n : ℕ} (w f g : Fin n → B) (hw : ∑ i : Fin n, w i = 1) :
    windingForm D (u * v) =
      (↑v⁻¹ : B) * windingForm D u * (v : B) + windingForm D v ∧
    gibbsCovariance w f g =
      gibbsCrossMoment w f g - gibbsExpectationR w f * gibbsExpectationL w g := by
  refine ⟨windingForm_mul hD u v, ?_⟩
  dsimp [gibbsCovariance, gibbsCrossMoment]
  have h_expand : ∀ i : Fin n,
      (f i - gibbsExpectationR w f) * w i * (g i - gibbsExpectationL w g) =
      (f i * w i * g i - gibbsExpectationR w f * (w i * g i)) +
      (-(f i * w i) * gibbsExpectationL w g +
       gibbsExpectationR w f * w i * gibbsExpectationL w g) := fun i => by noncomm_ring
  simp_rw [h_expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  have h_neg : (∑ x : Fin n, -(f x * w x)) = -gibbsExpectationR w f := by
    dsimp [gibbsExpectationR]; rw [Finset.sum_neg_distrib]
  have h_L : (∑ x : Fin n, w x * g x) = gibbsExpectationL w g := rfl
  rw [h_neg, h_L, hw]
  noncomm_ring

end StratumH4_WindingCocycleAndJaynesGibbsCovariance

/-!
## Stratum $\mathcal{H}_5$: Cantor Markov Harmonicity & Multi-Step RG Block-Decimation Invariance
-/

section StratumH5_CantorMarkovAndRGDecimation

variable {A : Type*} [Ring A]

def cantorMarkovStep (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  X + sigmaOp * X * sigmaOp

def cantorLaplacian (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  sigmaOp * X * sigmaOp - X

def IsCantorHarmonic (X : Matrix (Fin 2) (Fin 2) A) : Prop :=
  cantorMarkovStep X = 2 • X

/-- 2-to-1 Renormalization-Group (RG) block decimation on discrete-time operator trajectories. -/
def rgBlockStep {B : Type*} [Ring B] (X : ℕ → B) (k : ℕ) : B :=
  X (2 * k) + X (2 * k + 1)

/-- Cumulative trajectory sum over horizon $N$. -/
def trajectoryMean {B : Type*} [Ring B] (N : ℕ) (X : ℕ → B) : B :=
  ∑ k ∈ Finset.range N, X k

/-- **Cantor Markov Harmonicity & $2N$-Horizon RG Block-Decimation Theorem**:
1. $X \in M_2(A)$ is Cantor-harmonic iff $\Delta_{\mathrm{Cantor}}(X) = 0$,
2. $\Delta_{\mathrm{Cantor}}(\mathcal{M}_{\mathrm{step}}(X)) = 0$,
3. For any operator trajectory $X : \mathbb{N} \to A$ and horizon $N \in \mathbb{N}$,
   $\mathrm{trajectoryMean}\; N\; (\mathrm{rgBlockStep}\; X) = \mathrm{trajectoryMean}\; (2 * N)\; X$. -/
theorem cantor_markov_harmonicity_and_rg_invariance
    (X : Matrix (Fin 2) (Fin 2) A) (N : ℕ) (traj : ℕ → A) :
    (IsCantorHarmonic X ↔ cantorLaplacian X = 0) ∧
    cantorLaplacian (cantorMarkovStep X) = 0 ∧
    trajectoryMean N (rgBlockStep traj) = trajectoryMean (2 * N) traj := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [IsCantorHarmonic, cantorMarkovStep, cantorLaplacian]
    rw [two_smul]
    constructor
    · intro h
      calc sigmaOp * X * sigmaOp - X = (X + sigmaOp * X * sigmaOp) - (X + X) := by abel
        _ = 0 := by rw [h, sub_self]
    · intro h
      calc X + sigmaOp * X * sigmaOp = (X + X) + (sigmaOp * X * sigmaOp - X) := by abel
        _ = X + X := by rw [h, add_zero]
  · apply ext_fin2 <;> simp [cantorLaplacian, cantorMarkovStep, sigmaOp] <;> abel
  · dsimp [trajectoryMean, rgBlockStep]
    induction' N with N ih
    · simp
    · have h2N : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
      rw [Finset.sum_range_succ, ih, h2N, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]

end StratumH5_CantorMarkovAndRGDecimation

end NoncommutativeAnalyticitySynthesis
```

## Turn 0042, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeMasterCrossBridgeSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op            : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp             : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp             : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def chiralSheetPlus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def chiralSheetMinus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 0 1
def isotropicSheetPlus  : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def fiberEmbed (a : A)  : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

end Matrix2Simp

/-!
## Bridge $\mathcal{B}_1$: Dikin–Burg–Stein Self-Concordance & Maurer–Cartan Winding 1-Form Bridge ($\mathcal{D}\mathcal{T}_1 \leftrightarrow \mathcal{H}_4$)
-/

section BridgeB1_DikinBurgSteinWindingBridge

variable {B : Type*} [Ring B]

def IsRingDeriv (D : B →+ B) : Prop :=
  ∀ a b : B, D (a * b) = D a * b + a * D b

theorem IsRingDeriv.map_one {D : B →+ B} (hD : IsRingDeriv D) : D 1 = 0 := by
  have h : D (1 * 1) = D 1 * 1 + 1 * D 1 := hD 1 1
  simp only [mul_one, one_mul] at h
  calc D 1 = D 1 + D 1 - D 1 := by abel
    _ = D 1 - D 1 := by rw [← h]
    _ = 0 := sub_self (D 1)

theorem IsRingDeriv.map_units_inv {D : B →+ B} (hD : IsRingDeriv D) (X : Bˣ) :
    D (↑X⁻¹ : B) = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by
  have h1 : D ((X : B) * (↑X⁻¹ : B)) = D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B) :=
    hD (X : B) (↑X⁻¹ : B)
  rw [Units.mul_inv, hD.map_one] at h1
  have h2 : (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) = D (↑X⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc D (↑X⁻¹ : B)
    _ = (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) -
        (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by noncomm_ring

/-- Left-trivialized Maurer–Cartan winding 1-form $\omega_D(X) = X^{-1} D(X) \in B$. -/
def windingForm (D : B →+ B) (X : Bˣ) : B :=
  (↑X⁻¹ : B) * D (X : B)

/-- Right-trivialized Maurer–Cartan winding 1-form $\mathcal{W}_D(X) = D(X) X^{-1} \in B$. -/
def rightWindingForm (D : B →+ B) (X : Bˣ) : B :=
  D (X : B) * (↑X⁻¹ : B)

/-- Burg–Stein Hessian operator $\mathcal{H}_X(V) = X^{-1} V X^{-1}$. -/
def burgSteinHessian (X : Bˣ) (V : B) : B :=
  (↑X⁻¹ : B) * V * (↑X⁻¹ : B)

/-- **Dikin–Burg–Stein & Maurer–Cartan Winding Bridge Theorem ($\mathcal{B}_1$)**:
1. For any constant left gauge transformation $G \in B^\times$ ($D G = 0$), $\omega_D(G X) = \omega_D(X)$,
2. The third-order Burg–Stein self-concordance derivative $D(\mathcal{H}_X(V))$ ($D V = 0$) is the
   negative bimodule anti-commutator of $\mathcal{H}_X(V)$ with $\omega_D(X)$ and $\mathcal{W}_D(X)$,
3. Pullback by $X$ gives $X D(\mathcal{H}_X(V)) X = -(\mathcal{W}_D(X) V + V \omega_D(X))$. -/
theorem dikin_burg_stein_winding_self_concordance
    {D : B →+ B} (hD : IsRingDeriv D) {G : Bˣ} (hG : D (G : B) = 0)
    (X : Bˣ) {V : B} (hV : D V = 0) :
    windingForm D (G * X) = windingForm D X ∧
    D (burgSteinHessian X V) =
      -(windingForm D X * burgSteinHessian X V +
        burgSteinHessian X V * rightWindingForm D X) ∧
    (X : B) * D (burgSteinHessian X V) * (X : B) =
      -(rightWindingForm D X * V + V * windingForm D X) := by
  have h_self : D (burgSteinHessian X V) =
      -(windingForm D X * burgSteinHessian X V +
        burgSteinHessian X V * rightWindingForm D X) := by
    dsimp [burgSteinHessian, windingForm, rightWindingForm]
    rw [hD ((↑X⁻¹ : B) * V) (↑X⁻¹ : B), hD (↑X⁻¹ : B) V, hV, hD.map_units_inv X]
    noncomm_ring
  refine ⟨?_, h_self, ?_⟩
  · dsimp [windingForm]
    have h_coe : ((G * X : Bˣ) : B) = (G : B) * (X : B) := rfl
    have h_inv : ((↑(G * X)⁻¹ : Bˣ) : B) = (↑X⁻¹ : B) * (↑G⁻¹ : B) := by
      rw [mul_inv_rev]; rfl
    have hGi : (↑G⁻¹ : B) * (G : B) = 1 := Units.inv_mul G
    rw [h_coe, h_inv, hD (G : B) (X : B), hG, zero_mul, zero_add]
    calc (↑X⁻¹ : B) * (↑G⁻¹ : B) * ((G : B) * D (X : B))
      _ = (↑X⁻¹ : B) * ((↑G⁻¹ : B) * (G : B)) * D (X : B) := by noncomm_ring
      _ = (↑X⁻¹ : B) * D (X : B) := by rw [hGi]; noncomm_ring
  · rw [h_self]
    dsimp [burgSteinHessian, windingForm, rightWindingForm]
    have hX1 : (X : B) * (↑X⁻¹ : B) = 1 := Units.mul_inv X
    have hX2 : (↑X⁻¹ : B) * (X : B) = 1 := Units.inv_mul X
    calc (X : B) * -((↑X⁻¹ : B) * D (X : B) * ((↑X⁻¹ : B) * V * (↑X⁻¹ : B)) +
          ((↑X⁻¹ : B) * V * (↑X⁻¹ : B)) * (D (X : B) * (↑X⁻¹ : B))) * (X : B)
      _ = -(((X : B) * (↑X⁻¹ : B)) * D (X : B) * (↑X⁻¹ : B) * V * ((↑X⁻¹ : B) * (X : B)) +
            ((X : B) * (↑X⁻¹ : B)) * V * (↑X⁻¹ : B) * D (X : B) * ((↑X⁻¹ : B) * (X : B))) := by
          noncomm_ring
      _ = -(D (X : B) * (↑X⁻¹ : B) * V + V * ((↑X⁻¹ : B) * D (X : B))) := by
          rw [hX1, hX2]; noncomm_ring

end BridgeB1_DikinBurgSteinWindingBridge

/-!
## Bridge $\mathcal{B}_2$ & $\mathcal{B}_3$: Klein-Four Triality of Tetraktys Operator Splittings & Clifford–Cayley Intertwining
-/

section BridgeB2_B3_KleinFourTrialityAndCayleyIntertwining

variable {A : Type*} [Ring A]

def cptP (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A := gamma1Op * M * gamma1Op
def cptT (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A := sigmaOp * M * sigmaOp
def cptC (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A := -(omegaOp * M * omegaOp)

def holomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M - omegaOp * M * omegaOp

def antiholomorphicProj (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M + omegaOp * M * omegaOp

def cantorMarkovStep (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  M + sigmaOp * M * sigmaOp

def cantorLaplacian (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  sigmaOp * M * sigmaOp - M

def peirceFiberLift (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  chiralSheetPlus * X * chiralSheetPlus + sigmaOp * chiralSheetPlus * X * chiralSheetPlus * sigmaOp

def mellinCoeffI (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M + sigmaOp * M * sigmaOp)
def mellinCoeffGamma (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M - sigmaOp * M * sigmaOp)
def mellinCoeffSigma (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (M * sigmaOp + sigmaOp * M)
def mellinCoeffOmega (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  peirceFiberLift (sigmaOp * M - M * sigmaOp)

/-- **Klein-Four Triality of Tetraktys Operator Splittings ($\mathcal{B}_2$)**:
Every operator $M \in M_2(A)$ admits three canonical $2 + 2$ Tetraktys decompositions governed by
the three Klein-four involutions $(\mathcal{P}, \mathcal{T}, \mathcal{C})$:
1. *$\mathcal{P}$-Split (Peirce–DeWitt)*: $(M + \mathcal{P}(M)) = \widehat{M}_I I + \widehat{M}_\Gamma \Gamma_1$
   and $(M - \mathcal{P}(M)) = \widehat{M}_\Sigma \Sigma + \widehat{M}_\Omega \Omega$,
2. *$\mathcal{T}$-Split (Cantor Markov)*: $\mathcal{M}_{\mathrm{step}}(M) = \widehat{M}_I I + \widehat{M}_\Sigma \Sigma$
   and $-\Delta_{\mathrm{Cantor}}(M) = \widehat{M}_\Gamma \Gamma_1 + \widehat{M}_\Omega \Omega$,
3. *$\mathcal{C}$-Split (Hestenes CR)*: $\partial_{\mathrm{hol}}(M) = \widehat{M}_I I + \widehat{M}_\Omega \Omega$
   and $\bar{\partial}_{\mathrm{anti}}(M) = \widehat{M}_\Gamma \Gamma_1 + \widehat{M}_\Sigma \Sigma$. -/
theorem klein_four_triality_of_tetraktys_splittings (M : Matrix (Fin 2) (Fin 2) A) :
    M + cptP M = mellinCoeffI M * 1 + mellinCoeffGamma M * gamma1Op ∧
    M - cptP M = mellinCoeffSigma M * sigmaOp + mellinCoeffOmega M * omegaOp ∧
    cantorMarkovStep M = mellinCoeffI M * 1 + mellinCoeffSigma M * sigmaOp ∧
    -cantorLaplacian M = mellinCoeffGamma M * gamma1Op + mellinCoeffOmega M * omegaOp ∧
    holomorphicProj M = mellinCoeffI M * 1 + mellinCoeffOmega M * omegaOp ∧
    antiholomorphicProj M = mellinCoeffGamma M * gamma1Op + mellinCoeffSigma M * sigmaOp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [cptP, cantorMarkovStep, cantorLaplacian, holomorphicProj, antiholomorphicProj,
            mellinCoeffI, mellinCoeffGamma, mellinCoeffSigma, mellinCoeffOmega,
            peirceFiberLift, chiralSheetPlus, gamma1Op, sigmaOp, omegaOp] <;>
      abel)

variable [StarRing A]

def cayleyOp : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp

/-- **Clifford–Cayley Intertwining of Peirce–DeWitt Parity and Cantor Markov Laplacian ($\mathcal{B}_3$)**:
Conjugating by $\mathcal{C}_{\mathrm{Cayley}} = 1 + \Omega$ intertwines $\mathcal{P}$ and $\mathcal{T}$
while commuting with $\mathcal{C}$, mapping the Peirce–DeWitt even/odd projections into the Cantor
Markov step and Cantor Laplacian while preserving the Hestenes Cauchy–Riemann projections. -/
theorem clifford_cayley_intertwines_dewitt_and_cantor_markov (M : Matrix (Fin 2) (Fin 2) A) :
    cayleyOp * cptP M * cayleyOpᴴ = cptT (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * cptT M * cayleyOpᴴ = cptP (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * (M + cptP M) * cayleyOpᴴ = cantorMarkovStep (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * (cptP M - M) * cayleyOpᴴ = cantorLaplacian (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * holomorphicProj M * cayleyOpᴴ = holomorphicProj (cayleyOp * M * cayleyOpᴴ) ∧
    cayleyOp * antiholomorphicProj M * cayleyOpᴴ = antiholomorphicProj (cayleyOp * M * cayleyOpᴴ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;>
      simp [cayleyOp, cptP, cptT, cantorMarkovStep, cantorLaplacian,
            holomorphicProj, antiholomorphicProj, gamma1Op, sigmaOp, omegaOp] <;>
      abel)

end BridgeB2_B3_KleinFourTrialityAndCayleyIntertwining

/-!
## Bridge $\mathcal{B}_4$: Nested Witt Realization of Square-Zero Chiral Hodge Theory & 4-Channel Helmholtz Pythagoras
-/

section BridgeB4_NestedWittChiralHodgeAndPythagoras

variable {A : Type*} [Ring A]

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- Nested exterior differential $\mathbb{D} = \mathrm{diag}(\mathcal{I}_+, 0)$ and codifferential
$\mathbb{\Delta} = \mathrm{diag}(\mathcal{I}_-, 0)$ in $M_2(M_2(A))$. -/
def nestedD     : NestedMat A := mat2 isotropicSheetPlus 0 0 0
def nestedDelta : NestedMat A := mat2 isotropicSheetMinus 0 0 0
def nestedDirac : NestedMat A := nestedD + nestedDelta

/-- Exact, coexact, and harmonic projections in $M_2(M_2(A))$. -/
def nestedExactProj   : NestedMat A := mat2 chiralSheetPlus 0 0 0
def nestedCoexactProj : NestedMat A := mat2 chiralSheetMinus 0 0 0
def nestedHarmProj    : NestedMat A := mat2 0 0 0 1

/-- **Nested Witt Sheet Realization of Square-Zero Chiral Hodge Theory & 4-Channel Pythagoras ($\mathcal{B}_4$)**:
1. $\mathbb{D}$ and $\mathbb{\Delta}$ satisfy $\mathbb{D}^2 = \mathbb{\Delta}^2 = 0$,
   $\mathbb{D}\mathbb{\Delta}\mathbb{D} = \mathbb{D}$, $\mathbb{\Delta}\mathbb{D}\mathbb{\Delta} = \mathbb{\Delta}$,
   with exact projection $\mathrm{diag}(P_+, 0)$, coexact projection $\mathrm{diag}(P_-, 0)$, and
   harmonic projection $\mathrm{diag}(0, 1)$,
2. For any $\mathbb{X} \in M_2(M_2(A))$, $(\mathbb{D} + \mathbb{\Delta})\mathbb{X} = 0 \iff \mathrm{nestedHarmProj} * \mathbb{X} = \mathbb{X}$,
3. Over any $\star$-ring $A$, all four Helmholtz–Tetraktys channels $M_I, M_\Gamma, M_\Sigma, M_\Omega \in M_2(A)$
   satisfy the noncommutative Hilbert–Schmidt Pythagorean identity. -/
theorem nested_witt_sheets_realize_chiral_hodge_and_tetraktys
    [StarRing A] (X : NestedMat A) (cI cGamma cSigma cOmega : A) :
    let M_I     : Matrix (Fin 2) (Fin 2) A := fiberEmbed cI * 1
    let M_Gamma : Matrix (Fin 2) (Fin 2) A := fiberEmbed cGamma * gamma1Op
    let M_Sigma : Matrix (Fin 2) (Fin 2) A := fiberEmbed cSigma * sigmaOp
    let M_Omega : Matrix (Fin 2) (Fin 2) A := fiberEmbed cOmega * omegaOp
    (nestedD : NestedMat A) * nestedD = 0 ∧
    (nestedDelta : NestedMat A) * nestedDelta = 0 ∧
    (nestedD : NestedMat A) * nestedDelta * nestedD = nestedD ∧
    (nestedDelta : NestedMat A) * nestedD * nestedDelta = nestedDelta ∧
    (nestedD : NestedMat A) * nestedDelta = nestedExactProj ∧
    (nestedDelta : NestedMat A) * nestedD = nestedCoexactProj ∧
    1 - (nestedD * nestedDelta + nestedDelta * nestedD) = (nestedHarmProj : NestedMat A) ∧
    (nestedDirac * X = 0 ↔ nestedHarmProj * X = X) ∧
    Matrix.trace ((M_I + M_Gamma + M_Sigma + M_Omega)ᴴ * (M_I + M_Gamma + M_Sigma + M_Omega)) =
      Matrix.trace (M_Iᴴ * M_I) + Matrix.trace (M_Gammaᴴ * M_Gamma) +
      Matrix.trace (M_Sigmaᴴ * M_Sigma) + Matrix.trace (M_Omegaᴴ * M_Omega) := by
  have hD2 : (nestedD : NestedMat A) * nestedD = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedD, isotropicSheetPlus]
  have hDel2 : (nestedDelta : NestedMat A) * nestedDelta = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedDelta, isotropicSheetMinus]
  have hDDelD : (nestedD : NestedMat A) * nestedDelta * nestedD = nestedD := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]
  have hDelDDel : (nestedDelta : NestedMat A) * nestedD * nestedDelta = nestedDelta := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]
  have hEx : (nestedD : NestedMat A) * nestedDelta = nestedExactProj := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, nestedExactProj, isotropicSheetPlus, isotropicSheetMinus, chiralSheetPlus]
  have hCo : (nestedDelta : NestedMat A) * nestedD = nestedCoexactProj := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, nestedCoexactProj, isotropicSheetPlus, isotropicSheetMinus, chiralSheetMinus]
  have hHarm : 1 - ((nestedD : NestedMat A) * nestedDelta + nestedDelta * nestedD) = nestedHarmProj := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, nestedHarmProj, isotropicSheetPlus, isotropicSheetMinus]
  refine ⟨hD2, hDel2, hDDelD, hDelDDel, hEx, hCo, hHarm, ?_, ?_⟩
  · rw [← hHarm]; dsimp [nestedDirac]
    constructor
    · intro h
      have h1 : nestedD * X = 0 := by
        calc nestedD * X
          _ = (nestedD * nestedDelta * nestedD) * X + nestedD * (nestedDelta * nestedDelta) * X := by
              rw [hDDelD, hDel2]; noncomm_ring
          _ = nestedD * nestedDelta * ((nestedD + nestedDelta) * X) := by noncomm_ring
          _ = nestedD * nestedDelta * 0 := by rw [h]
          _ = 0 := mul_zero _
      have h2 : nestedDelta * X = 0 := by
        calc nestedDelta * X
          _ = nestedDelta * (nestedD * nestedD) * X + (nestedDelta * nestedD * nestedDelta) * X := by
              rw [hD2, hDelDDel]; noncomm_ring
          _ = nestedDelta * nestedD * ((nestedD + nestedDelta) * X) := by noncomm_ring
          _ = nestedDelta * nestedD * 0 := by rw [h]
          _ = 0 := mul_zero _
      calc (1 - (nestedD * nestedDelta + nestedDelta * nestedD)) * X
        _ = X - nestedD * (nestedDelta * X) - nestedDelta * (nestedD * X) := by noncomm_ring
        _ = X - nestedD * 0 - nestedDelta * 0 := by rw [h1, h2]
        _ = X := by noncomm_ring
    · intro hP
      calc (nestedD + nestedDelta) * X
        _ = (nestedD + nestedDelta) * ((1 - (nestedD * nestedDelta + nestedDelta * nestedD)) * X) := by
            rw [hP]
        _ = (nestedD - nestedD * nestedDelta * nestedD - (nestedD * nestedD) * nestedDelta +
             nestedDelta - (nestedDelta * nestedDelta) * nestedD -
             nestedDelta * nestedD * nestedDelta) * X := by noncomm_ring
        _ = (nestedD - nestedD - 0 * nestedDelta +
             nestedDelta - 0 * nestedD - nestedDelta) * X := by
            rw [hDDelD, hD2, hDel2, hDelDDel]
        _ = 0 := by noncomm_ring
  · simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp]
    noncomm_ring

end BridgeB4_NestedWittChiralHodgeAndPythagoras

end NoncommutativeMasterCrossBridgeSynthesis
```

## Turn 0045, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeGrandApexSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op            : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp             : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp             : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def chiralSheetPlus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def chiralSheetMinus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 0 1
def isotropicSheetPlus  : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def fiberEmbed (a : A)  : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a
def kleinTwist (a : A)  : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 (-a)

end Matrix2Simp

/-!
## Apex $\mathcal{X}_1$: Winding Cocycle as Right Gauge Dressing & Dikin–Burg–Stein Self-Concordance
-/

section ApexX1_WindingGaugeDressingAndSelfConcordance

variable {B : Type*} [Ring B]

def IsRingDeriv (D : B →+ B) : Prop :=
  ∀ a b : B, D (a * b) = D a * b + a * D b

theorem IsRingDeriv.map_one {D : B →+ B} (hD : IsRingDeriv D) : D 1 = 0 := by
  have h : D (1 * 1) = D 1 * 1 + 1 * D 1 := hD 1 1
  simp only [mul_one, one_mul] at h
  calc D 1 = D 1 + D 1 - D 1 := by abel
    _ = D 1 - D 1 := by rw [← h]
    _ = 0 := sub_self (D 1)

theorem IsRingDeriv.map_units_inv {D : B →+ B} (hD : IsRingDeriv D) (X : Bˣ) :
    D (↑X⁻¹ : B) = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by
  have h1 : D ((X : B) * (↑X⁻¹ : B)) = D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B) :=
    hD (X : B) (↑X⁻¹ : B)
  rw [Units.mul_inv, hD.map_one] at h1
  have h2 : (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) = D (↑X⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc D (↑X⁻¹ : B)
    _ = (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) -
        (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by noncomm_ring

def windingForm (D : B →+ B) (u : Bˣ) : B := (↑u⁻¹ : B) * D (u : B)
def rightWindingForm (D : B →+ B) (u : Bˣ) : B := D (u : B) * (↑u⁻¹ : B)
def covOpR (D : B →+ B) (A ψ : B) : B := D ψ + ψ * A
def dressConnR (D : B →+ B) (v : Bˣ) (A : B) : B := (↑v⁻¹ : B) * A * (v : B) + windingForm D v
def burgSteinHessian (X : Bˣ) (V : B) : B := (↑X⁻¹ : B) * V * (↑X⁻¹ : B)

/-- **Winding Cocycle as Right Gauge Dressing & Burg–Stein Self-Concordance ($\mathcal{X}_1$)**:
1. Right affine gauge dressing $\operatorname{dressConnR}_D(v, A)$ intertwines $\nabla_{D, A}^R$:
   $\nabla_{D, \operatorname{dressConnR}_D(v, A)}^R(\psi v) = \nabla_{D, A}^R(\psi)\,v$,
2. The noncommutative winding cocycle $\omega_D(u v)$ is the right gauge dressing of $\omega_D(u)$ by $v$,
3. The third-order Burg–Stein self-concordance derivative $D(\mathcal{H}_X(V))$ ($D V = 0$) satisfies
   $X D(\mathcal{H}_X(V)) X = -(\mathcal{W}_D(X) V + V \omega_D(X))$. -/
theorem winding_gauge_dressing_and_burg_stein_self_concordance
    {D : B →+ B} (hD : IsRingDeriv D) (u v X : Bˣ) (A ψ : B) {V : B} (hV : D V = 0) :
    covOpR D (dressConnR D v A) (ψ * (v : B)) = covOpR D A ψ * (v : B) ∧
    windingForm D (u * v) = dressConnR D v (windingForm D u) ∧
    D (burgSteinHessian X V) =
      -(windingForm D X * burgSteinHessian X V +
        burgSteinHessian X V * rightWindingForm D X) ∧
    (X : B) * D (burgSteinHessian X V) * (X : B) =
      -(rightWindingForm D X * V + V * windingForm D X) := by
  have h_self : D (burgSteinHessian X V) =
      -(windingForm D X * burgSteinHessian X V +
        burgSteinHessian X V * rightWindingForm D X) := by
    dsimp [burgSteinHessian, windingForm, rightWindingForm]
    rw [hD ((↑X⁻¹ : B) * V) (↑X⁻¹ : B), hD (↑X⁻¹ : B) V, hV, hD.map_units_inv X]
    noncomm_ring
  refine ⟨?_, ?_, h_self, ?_⟩
  · dsimp [covOpR, dressConnR, windingForm]
    rw [hD ψ (v : B)]
    have hv : (v : B) * (↑v⁻¹ : B) = 1 := Units.mul_inv v
    calc D ψ * (v : B) + ψ * D (v : B) +
          ψ * (v : B) * ((↑v⁻¹ : B) * A * (v : B) + (↑v⁻¹ : B) * D (v : B))
      _ = D ψ * (v : B) + ψ * D (v : B) +
          ψ * ((v : B) * (↑v⁻¹ : B)) * A * (v : B) +
          ψ * ((v : B) * (↑v⁻¹ : B)) * D (v : B) := by noncomm_ring
      _ = (D ψ + ψ * A) * (v : B) := by rw [hv]; noncomm_ring
  · dsimp [windingForm, dressConnR]
    have h_coe : ((u * v : Bˣ) : B) = (u : B) * (v : B) := rfl
    have h_inv : ((↑(u * v)⁻¹ : Bˣ) : B) = (↑v⁻¹ : B) * (↑u⁻¹ : B) := by
      rw [mul_inv_rev]; rfl
    have hu : (↑u⁻¹ : B) * (u : B) = 1 := Units.inv_mul u
    rw [h_coe, h_inv, hD (u : B) (v : B)]
    calc (↑v⁻¹ : B) * (↑u⁻¹ : B) * (D (u : B) * (v : B) + (u : B) * D (v : B))
      _ = (↑v⁻¹ : B) * ((↑u⁻¹ : B) * D (u : B)) * (v : B) +
          (↑v⁻¹ : B) * ((↑u⁻¹ : B) * (u : B)) * D (v : B) := by noncomm_ring
      _ = (↑v⁻¹ : B) * ((↑u⁻¹ : B) * D (u : B)) * (v : B) +
          (↑v⁻¹ : B) * D (v : B) := by rw [hu]; noncomm_ring
  · rw [h_self]
    dsimp [burgSteinHessian, windingForm, rightWindingForm]
    have hX1 : (X : B) * (↑X⁻¹ : B) = 1 := Units.mul_inv X
    have hX2 : (↑X⁻¹ : B) * (X : B) = 1 := Units.inv_mul X
    calc (X : B) * -((↑X⁻¹ : B) * D (X : B) * ((↑X⁻¹ : B) * V * (↑X⁻¹ : B)) +
          ((↑X⁻¹ : B) * V * (↑X⁻¹ : B)) * (D (X : B) * (↑X⁻¹ : B))) * (X : B)
      _ = -(((X : B) * (↑X⁻¹ : B)) * D (X : B) * (↑X⁻¹ : B) * V * ((↑X⁻¹ : B) * (X : B)) +
            ((X : B) * (↑X⁻¹ : B)) * V * (↑X⁻¹ : B) * D (X : B) * ((↑X⁻¹ : B) * (X : B))) := by
          noncomm_ring
      _ = -(D (X : B) * (↑X⁻¹ : B) * V + V * ((↑X⁻¹ : B) * D (X : B))) := by
          rw [hX1, hX2]; noncomm_ring

end ApexX1_WindingGaugeDressingAndSelfConcordance

/-!
## Apex $\mathcal{X}_2$: Parseval Gabor Frame Realization of Bimodule Jaynesian Gibbs Variance in the $\star$-Positive Cone
-/

section ApexX2_GaborParsevalGibbsVariance

variable {B : Type*} [Ring B] [StarRing B] {n : ℕ}

def gibbsExpectationR (w f : Fin n → B) : B := ∑ i : Fin n, f i * w i
def gibbsExpectationL (w g : Fin n → B) : B := ∑ i : Fin n, w i * g i
def gibbsCrossMoment (w f g : Fin n → B) : B := ∑ i : Fin n, f i * w i * g i
def gibbsCovariance (w f g : Fin n → B) : B :=
  ∑ i : Fin n, (f i - gibbsExpectationR w f) * w i * (g i - gibbsExpectationL w g)

/-- **Parseval Gabor Frame Realization of Noncommutative Jaynesian Gibbs Variance ($\mathcal{X}_2$)**:
For any Parseval Gabor frame $\phi : \mathrm{Fin}\,n \to B$ ($\sum_i \phi_i \phi_i^\star = 1$) with
weights $w_i = \phi_i \phi_i^\star$ and any noncommuting observable $f : \mathrm{Fin}\,n \to B$:
1. $\mathbb{E}_L(w, f^\star) = (\mathbb{E}_R(w, f))^\star$,
2. $\mathrm{Cov}_w(f, f^\star)$ is a sum of Hermitian squares $\sum_i D_i D_i^\star$ in the $\star$-positive cone,
3. $\mathrm{Cov}_w(f, f^\star) = \sum_i f_i \phi_i \phi_i^\star f_i^\star - \mathbb{E}_R(w, f)(\mathbb{E}_R(w, f))^\star$. -/
theorem parseval_gabor_jaynes_gibbs_variance_positivity
    (φ f : Fin n → B) (h_pars : ∑ i : Fin n, φ i * star (φ i) = 1) :
    let w := fun i => φ i * star (φ i)
    let f_star := fun i => star (f i)
    gibbsExpectationL w f_star = star (gibbsExpectationR w f) ∧
    gibbsCovariance w f f_star =
      ∑ i : Fin n, ((f i - gibbsExpectationR w f) * φ i) *
                   star ((f i - gibbsExpectationR w f) * φ i) ∧
    gibbsCovariance w f f_star =
      gibbsCrossMoment w f f_star -
      gibbsExpectationR w f * star (gibbsExpectationR w f) := by
  intro w f_star
  have h_adj : gibbsExpectationL w f_star = star (gibbsExpectationR w f) := by
    dsimp [gibbsExpectationL, gibbsExpectationR, w, f_star]
    rw [star_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [star_mul, mul_assoc]
  refine ⟨h_adj, ?_, ?_⟩
  · dsimp [gibbsCovariance]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_adj]
    dsimp [w, f_star]
    simp only [star_mul, star_sub]
    noncomm_ring
  · dsimp [gibbsCovariance, gibbsCrossMoment]
    have h_expand : ∀ i : Fin n,
        (f i - gibbsExpectationR w f) * w i * (f_star i - gibbsExpectationL w f_star) =
        (f i * w i * f_star i - gibbsExpectationR w f * (w i * f_star i)) +
        (-(f i * w i) * gibbsExpectationL w f_star +
         gibbsExpectationR w f * w i * gibbsExpectationL w f_star) := fun i => by noncomm_ring
    simp_rw [h_expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    have h_neg : (∑ x : Fin n, -(f x * w x)) = -gibbsExpectationR w f := by
      dsimp [gibbsExpectationR]; rw [Finset.sum_neg_distrib]
    have h_L : (∑ x : Fin n, w x * f_star x) = gibbsExpectationL w f_star := rfl
    have hw : ∑ x : Fin n, w x = 1 := h_pars
    rw [h_neg, h_L, hw, h_adj]
    noncomm_ring

end ApexX2_GaborParsevalGibbsVariance

/-!
## Apex $\mathcal{X}_3$: Square-Zero Chiral Hodge Leakage & Harmonic Commutator Variance
-/

section ApexX3_ChiralHodgeCommutatorVariance

variable {B : Type*} [Ring B] [StarRing B]

/-- **Square-Zero Chiral Hodge Leakage & Harmonic Commutator Variance Theorem ($\mathcal{X}_3$)**:
For any square-zero partial-isometry pair $d, \delta \in B$ ($d^2 = \delta^2 = 0, d\delta d = d, \delta d\delta = \delta$)
with self-adjoint harmonic projection $e_{\mathrm{harm}} = 1 - (d\delta + \delta d)$ and any projection
$Q^2 = Q = Q^\star$, the variance of $T_{\mathrm{harm}} = e_{\mathrm{harm}} Q e_{\mathrm{harm}}$ equals both
the exact $\oplus$ coexact leakage $e_{\mathrm{harm}} Q (d\delta + \delta d) Q e_{\mathrm{harm}}$ and
the compressed commutator square $(e_{\mathrm{harm}} \⁅e_{\mathrm{harm}}, Q⁆^\star)(\⁅e_{\mathrm{harm}}, Q⁆ e_{\mathrm{harm}})$. -/
theorem chiral_hodge_leakage_eq_commutator_variance
    {d δ Q : B} (hd2 : d * d = 0) (hδ2 : δ * δ = 0)
    (hdδd : d * δ * d = d) (hδdδ : δ * d * δ = δ)
    (h_harm_sa : star (1 - (d * δ + δ * d)) = 1 - (d * δ + δ * d))
    (hQ_idem : Q * Q = Q) (hQ_sa : star Q = Q) :
    let e_harm := 1 - (d * δ + δ * d)
    let T_harm := e_harm * Q * e_harm
    T_harm - T_harm * T_harm = e_harm * Q * (d * δ + δ * d) * Q * e_harm ∧
    T_harm - T_harm * T_harm = (e_harm * star ⁅e_harm, Q⁆) * (⁅e_harm, Q⁆ * e_harm) := by
  intro e_harm T_harm
  have h_harm_idem : e_harm * e_harm = e_harm := by
    dsimp [e_harm]
    calc (1 - (d * δ + δ * d)) * (1 - (d * δ + δ * d))
      _ = 1 - 2 * (d * δ) - 2 * (δ * d) + (d * δ * d) * δ + (δ * d * δ) * d +
          d * (δ * δ) * d + δ * (d * d) * δ := by noncomm_ring
      _ = 1 - 2 * (d * δ) - 2 * (δ * d) + d * δ + δ * d +
          d * 0 * d + δ * 0 * δ := by rw [hdδd, hδdδ, hδ2, hd2]
      _ = 1 - (d * δ + δ * d) := by noncomm_ring
  have h_leak : T_harm - T_harm * T_harm = e_harm * Q * (d * δ + δ * d) * Q * e_harm := by
    dsimp [T_harm]
    have h_comp : 1 - e_harm = d * δ + δ * d := by dsimp [e_harm]; noncomm_ring
    calc e_harm * Q * e_harm - (e_harm * Q * e_harm) * (e_harm * Q * e_harm)
      _ = e_harm * (Q * Q) * e_harm - e_harm * Q * (e_harm * e_harm) * Q * e_harm := by
          rw [hQ_idem, h_harm_idem]; noncomm_ring
      _ = e_harm * Q * (1 - e_harm) * Q * e_harm := by noncomm_ring
      _ = e_harm * Q * (d * δ + δ * d) * Q * e_harm := by rw [h_comp]
  refine ⟨h_leak, ?_⟩
  rw [h_leak]
  have h_comm : ⁅e_harm, Q⁆ * e_harm = -((1 - e_harm) * Q * e_harm) := by
    rw [Ring.lie_def]
    calc (e_harm * Q - Q * e_harm) * e_harm
      _ = e_harm * Q * e_harm - Q * (e_harm * e_harm) := by noncomm_ring
      _ = e_harm * Q * e_harm - Q * e_harm := by rw [h_harm_idem]
      _ = -((1 - e_harm) * Q * e_harm) := by noncomm_ring
  have h_star : e_harm * star ⁅e_harm, Q⁆ = -star ((1 - e_harm) * Q * e_harm) := by
    calc e_harm * star ⁅e_harm, Q⁆ = star (⁅e_harm, Q⁆ * e_harm) := by
          simp [star_mul, h_harm_sa]
      _ = -star ((1 - e_harm) * Q * e_harm) := by rw [h_comm, star_neg]
  rw [h_comm, h_star, neg_mul_neg]
  simp only [star_mul, star_sub, star_one, h_harm_sa, hQ_sa]
  have h1e : (1 - e_harm) * (1 - e_harm) = d * δ + δ * d := by
    calc (1 - e_harm) * (1 - e_harm)
      _ = 1 - e_harm - e_harm + e_harm * e_harm := by noncomm_ring
      _ = 1 - e_harm := by rw [h_harm_idem]; noncomm_ring
      _ = d * δ + δ * d := by dsimp [e_harm]; noncomm_ring
  calc e_harm * Q * (d * δ + δ * d) * Q * e_harm
    _ = e_harm * Q * ((1 - e_harm) * (1 - e_harm)) * Q * e_harm := by rw [h1e]
    _ = e_harm * Q * (1 - e_harm) * ((1 - e_harm) * Q * e_harm) := by noncomm_ring

end ApexX3_ChiralHodgeCommutatorVariance

/-!
## Apex $\mathcal{X}_4$ & $\mathcal{X}_5$: Klein-Four Triality, 4-Channel Pythagoras & Nested Witt Hodge–Braid–Cantor Synthesis
-/

section ApexX4_X5_MasterNestedWittHodgeBraidCantor

variable {A : Type*} [Ring A] [StarRing A]

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- Nested coupled isotropic Witt differentials $\mathbb{D} = \mathrm{diag}(\mathcal{I}_+, 0)$ and
$\mathbb{\Delta} = \mathrm{diag}(\mathcal{I}_-, 0)$ in $M_2(M_2(A))$. -/
def nestedD     : NestedMat A := mat2 isotropicSheetPlus 0 0 0
def nestedDelta : NestedMat A := mat2 isotropicSheetMinus 0 0 0

/-- Nested quaternion curvature generators $E_1, E_2, E_3$, Clifford–Artin braid generators
$R_{12}, R_{23}$, composite 2-scale transform $\mathcal{U}_{\mathrm{braid}} = R_{12} R_{23}$, and
Sierpiński porous projection $\Pi_{\mathcal{S}_2}$. -/
def E₁      : NestedMat A := omegaOp
def E₂      : NestedMat A := kleinTwist omegaOp
def E₃      : NestedMat A := (E₁ : NestedMat A) * E₂
def R₁₂     : NestedMat A := 1 + E₁
def R₂₃     : NestedMat A := 1 + E₂
def U_braid : NestedMat A := R₁₂ * R₂₃
def Pi_S2   : NestedMat A := mat2 1 0 0 chiralSheetPlus

/-- **Grand Apex Theorem in $M_2(M_2(A))$ ($\mathcal{X}_4$ & $\mathcal{X}_5$)**:
Over any noncommutative $\star$-ring $A$:
1. The four Helmholtz–Tetraktys channels $M_I, M_\Gamma, M_\Sigma, M_\Omega \in M_2(A)$ satisfy the
   exact Hilbert–Schmidt Pythagorean identity without commutativity or self-adjointness assumptions,
2. The nested coupled isotropic Witt differentials $\mathbb{D}, \mathbb{\Delta} \in M_2(M_2(A))$
   satisfy $\mathbb{D}^2 = \mathbb{\Delta}^2 = 0$, $\mathbb{D}\mathbb{\Delta}\mathbb{D} = \mathbb{D}$,
   $\mathbb{\Delta}\mathbb{D}\mathbb{\Delta} = \mathbb{\Delta}$,
3. The Clifford–Artin braid operators $R_{12}, R_{23}$ satisfy $R_{12} R_{23} R_{12} = R_{23} R_{12} R_{23}$
   and $\⁅R_{12}, R_{23}⁆ = 2 E_3$,
4. Compressing $\mathcal{U}_{\mathrm{braid}} (\mathbb{D}\mathbb{\Delta})$ across the full space $1$,
   the Sierpiński mask $\Pi_{\mathcal{S}_2}$, the non-harmonic Hodge support $\mathbb{D}\mathbb{\Delta} + \mathbb{\Delta}\mathbb{D}$,
   and the exact Hodge projection $\mathbb{D}\mathbb{\Delta}$ contracts the Gram square strictly along
   $4 \bullet (\mathbb{D}\mathbb{\Delta}) \to 3 \bullet (\mathbb{D}\mathbb{\Delta}) \to 2 \bullet (\mathbb{D}\mathbb{\Delta}) \to 1 \bullet (\mathbb{D}\mathbb{\Delta})$. -/
theorem grand_apex_witt_hodge_braid_cantor_synthesis (cI cGamma cSigma cOmega : A) :
    let M_I     : Matrix (Fin 2) (Fin 2) A := fiberEmbed cI * 1
    let M_Gamma : Matrix (Fin 2) (Fin 2) A := fiberEmbed cGamma * gamma1Op
    let M_Sigma : Matrix (Fin 2) (Fin 2) A := fiberEmbed cSigma * sigmaOp
    let M_Omega : Matrix (Fin 2) (Fin 2) A := fiberEmbed cOmega * omegaOp
    let e_ex    : NestedMat A := nestedD * nestedDelta
    let e_nonh  : NestedMat A := nestedD * nestedDelta + nestedDelta * nestedD
    Matrix.trace ((M_I + M_Gamma + M_Sigma + M_Omega)ᴴ * (M_I + M_Gamma + M_Sigma + M_Omega)) =
      Matrix.trace (M_Iᴴ * M_I) + Matrix.trace (M_Gammaᴴ * M_Gamma) +
      Matrix.trace (M_Sigmaᴴ * M_Sigma) + Matrix.trace (M_Omegaᴴ * M_Omega) ∧
    (nestedD : NestedMat A) * nestedD = 0 ∧
    (nestedDelta : NestedMat A) * nestedDelta = 0 ∧
    (nestedD : NestedMat A) * nestedDelta * nestedD = nestedD ∧
    (nestedDelta : NestedMat A) * nestedD * nestedDelta = nestedDelta ∧
    (R₁₂ : NestedMat A) * R₂₃ * R₁₂ = R₂₃ * R₁₂ * R₂₃ ∧
    ⁅(R₁₂ : NestedMat A), R₂₃⁆ = 2 • (E₃ : NestedMat A) ∧
    (U_braid * e_ex : NestedMat A)ᴴ * (U_braid * e_ex) = 4 • e_ex ∧
    (Pi_S2 * U_braid * e_ex : NestedMat A)ᴴ * (Pi_S2 * U_braid * e_ex) = 3 • e_ex ∧
    (e_nonh * U_braid * e_ex : NestedMat A)ᴴ * (e_nonh * U_braid * e_ex) = 2 • e_ex ∧
    (e_ex * U_braid * e_ex : NestedMat A)ᴴ * (e_ex * U_braid * e_ex) = e_ex := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [fiberEmbed, gamma1Op, sigmaOp, omegaOp]
    noncomm_ring
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedD, isotropicSheetPlus]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [nestedDelta, isotropicSheetMinus]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [R₁₂, R₂₃, E₁, E₂, kleinTwist, omegaOp] <;> abel
  · rw [Ring.lie_def]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [R₁₂, R₂₃, E₁, E₂, E₃, kleinTwist, omegaOp, two_smul] <;> abel
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, omegaOp,
            nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus] <;> abel
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Pi_S2, chiralSheetPlus, U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, omegaOp,
            nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus] <;> abel
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, omegaOp,
            nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus] <;> abel
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [U_braid, R₁₂, R₂₃, E₁, E₂, kleinTwist, omegaOp,
            nestedD, nestedDelta, isotropicSheetPlus, isotropicSheetMinus]

end ApexX4_X5_MasterNestedWittHodgeBraidCantor

end NoncommutativeGrandApexSynthesis
```

## Turn 0048, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeFutureHorizonsTower

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

def gamma1Op : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)

end Matrix2Simp

/-!
## Horizon $\mathcal{N}_1$ & $\mathcal{N}_5$: The Arbitrary-$n$ Inductive Clifford–Tetraktys Tower $\mathcal{C}\ell_n(A)$, All-Scales $2^{-n}$ Cantor FUP & RG Trace Conservation
-/

section HorizonN1_N5_InductiveCliffordTower

universe u

/-- The $n$-scale inductive dyadic operator tower $\mathcal{C}\ell_n(A) \cong M_{2^n}(A) \cong Cl(n,n) \otimes_{\mathbb{Z}} A$. -/
def ClTower : ℕ → Type u → Type u
  | 0, A     => A
  | n + 1, A => Matrix (Fin 2) (Fin 2) (ClTower n A)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower n A)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower n A) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower n A)))

instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower n A)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower n A) := instRingClTower n
      letI : StarRing (ClTower n A) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower n A)))

variable {A : Type u} [Ring A]

/-- The $n$-scale Cantor corner projection $\Pi_{\mathcal{C}_n} \in \mathcal{C}\ell_n(A)$. -/
def cantorTowerProj : ∀ n : ℕ, ClTower n A
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorTowerProj n) 0 0 0

/-- The $n$-scale recursive Clifford–Cayley–Walsh transform $\mathcal{U}_n \in \mathcal{C}\ell_n(A)$. -/
def cayleyTowerOp : ∀ n : ℕ, ClTower n A
  | 0     => (1 : A)
  | n + 1 => mat2 (cayleyTowerOp n) (-cayleyTowerOp n) (cayleyTowerOp n) (cayleyTowerOp n)

/-- Single-step RG block decimation $\mathcal{R}_{\mathrm{RG}} : \mathcal{C}\ell_{n+1}(A) \to \mathcal{C}\ell_n(A)$. -/
def rgTowerDecimate (n : ℕ) (M : ClTower (n + 1) A) : ClTower n A :=
  M 0 0 + M 1 1

/-- Iterated $n$-scale partition trace $\mathrm{Tr}_{2^n} : \mathcal{C}\ell_n(A) \to A$. -/
def towerTrace : ∀ n : ℕ, ClTower n A → A
  | 0, a     => a
  | n + 1, M => towerTrace n (rgTowerDecimate n M)

theorem towerTrace_add : ∀ (n : ℕ) (X Y : ClTower n A),
    towerTrace n (X + Y) = towerTrace n X + towerTrace n Y
  | 0, X, Y     => rfl
  | n + 1, X, Y => by
      dsimp [towerTrace, rgTowerDecimate]
      have h_ rearrange : (X + Y) 0 0 + (X + Y) 1 1 = (X 0 0 + X 1 1) + (Y 0 0 + Y 1 1) := by
        simp only [Matrix.add_apply]; abel
      rw [h_rearrange, towerTrace_add n]

/-- **All-Scales Inductive RG Trace Conservation & Cantor Ground-State Normalization ($\mathcal{N}_5$)**:
For every scale $n \in \mathbb{N}$:
1. $\mathrm{Tr}_{2^{n+1}}(M) = \mathrm{Tr}_{2^n}(\mathcal{R}_{\mathrm{RG}}(M))$,
2. $\mathrm{Tr}_{2^n}(\Pi_{\mathcal{C}_n}) = 1$,
3. $\mathrm{Tr}_{2^n}(1) = (2^n) \bullet 1$. -/
theorem all_scales_rg_trace_and_cantor_normalization (n : ℕ) (M : ClTower (n + 1) A) :
    towerTrace (n + 1) M = towerTrace n (rgTowerDecimate n M) ∧
    towerTrace n (cantorTowerProj n : ClTower n A) = 1 ∧
    towerTrace n (1 : ClTower n A) = (2 ^ n) • (1 : A) := by
  refine ⟨rfl, ?_, ?_⟩
  · induction' n with k ih
    · rfl
    · dsimp [towerTrace, rgTowerDecimate, cantorTowerProj]
      rw [mat2_00, mat2_11, add_zero, ih]
  · induction' n with k ih
    · simp [towerTrace]
    · dsimp [towerTrace, rgTowerDecimate]
      rw [one2_00, one2_11, towerTrace_add k, ih, pow_succ', two_mul, add_nsmul]

variable [StarRing A]

/-- **All-Scales Inductive Clifford–Cayley Unitarity & $2^{-n}$ Cantor FUP Contraction ($\mathcal{N}_1$)**:
For every scale $n \in \mathbb{N}$ in the inductive tower $\mathcal{C}\ell_n(A)$:
1. $\Pi_{\mathcal{C}_n}^2 = \Pi_{\mathcal{C}_n}$ and $\Pi_{\mathcal{C}_n}^\star = \Pi_{\mathcal{C}_n}$,
2. $\mathcal{U}_n^\star \mathcal{U}_n = (2^n) \bullet 1$,
3. $\Pi_{\mathcal{C}_n} \mathcal{U}_n \Pi_{\mathcal{C}_n} = \Pi_{\mathcal{C}_n}$,
4. $(\mathcal{U}_n \Pi_{\mathcal{C}_n})^\star (\mathcal{U}_n \Pi_{\mathcal{C}_n}) = (2^n) \bullet \Pi_{\mathcal{C}_n}$
   whereas $(\Pi_{\mathcal{C}_n} \mathcal{U}_n \Pi_{\mathcal{C}_n})^\star (\Pi_{\mathcal{C}_n} \mathcal{U}_n \Pi_{\mathcal{C}_n}) = \Pi_{\mathcal{C}_n}$. -/
theorem all_scales_inductive_clifford_cantor_fup (n : ℕ) :
    (cantorTowerProj n : ClTower n A) * cantorTowerProj n = cantorTowerProj n ∧
    star (cantorTowerProj n : ClTower n A) = cantorTowerProj n ∧
    star (cayleyTowerOp n : ClTower n A) * cayleyTowerOp n = (2 ^ n) • (1 : ClTower n A) ∧
    (cantorTowerProj n : ClTower n A) * cayleyTowerOp n * cantorTowerProj n = cantorTowerProj n ∧
    star ((cayleyTowerOp n : ClTower n A) * cantorTowerProj n) *
      (cayleyTowerOp n * cantorTowerProj n) = (2 ^ n) • (cantorTowerProj n : ClTower n A) ∧
    star ((cantorTowerProj n : ClTower n A) * cayleyTowerOp n * cantorTowerProj n) *
      (cantorTowerProj n * cayleyTowerOp n * cantorTowerProj n) = cantorTowerProj n := by
  have h_core :
      (cantorTowerProj n : ClTower n A) * cantorTowerProj n = cantorTowerProj n ∧
      star (cantorTowerProj n : ClTower n A) = cantorTowerProj n ∧
      star (cayleyTowerOp n : ClTower n A) * cayleyTowerOp n = (2 ^ n) • (1 : ClTower n A) ∧
      (cantorTowerProj n : ClTower n A) * cayleyTowerOp n * cantorTowerProj n = cantorTowerProj n := by
    induction' n with k ih
    · simp [cantorTowerProj, cayleyTowerOp]
    · rcases ih with ⟨ih_idem, ih_sa, ih_unit, ih_comp⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply ext_fin2 <;> simp [cantorTowerProj, ih_idem]
      · apply ext_fin2 <;> simp [cantorTowerProj, ih_sa]
      · apply ext_fin2
        · simp [cayleyTowerOp, ih_unit, pow_succ', two_mul, add_nsmul]
        · simp [cayleyTowerOp]
        · simp [cayleyTowerOp]
        · simp [cayleyTowerOp, ih_unit, pow_succ', two_mul, add_nsmul]
      · apply ext_fin2 <;> simp [cantorTowerProj, cayleyTowerOp, ih_comp]
  rcases h_core with ⟨h_idem, h_sa, h_unit, h_comp⟩
  refine ⟨h_idem, h_sa, h_unit, h_comp, ?_, ?_⟩
  · calc star ((cayleyTowerOp n : ClTower n A) * cantorTowerProj n) *
          (cayleyTowerOp n * cantorTowerProj n)
      _ = cantorTowerProj n * (star (cayleyTowerOp n) * cayleyTowerOp n) * cantorTowerProj n := by
          simp only [star_mul, h_sa]; noncomm_ring
      _ = cantorTowerProj n * ((2 ^ n) • (1 : ClTower n A)) * cantorTowerProj n := by rw [h_unit]
      _ = (2 ^ n) • ((cantorTowerProj n : ClTower n A) * cantorTowerProj n) := by
          rw [nsmul_eq_mul, nsmul_eq_mul]; noncomm_ring
      _ = (2 ^ n) • cantorTowerProj n := by rw [h_idem]
  · rw [h_comp, h_sa, h_idem]

end HorizonN1_N5_InductiveCliffordTower

/-!
## Horizon $\mathcal{N}_2$: Connes' Spectral Triple Quantized Differential $đf = \⁅D, f⁆$ & Graded Cochain Curvature
-/

section HorizonN2_ConnesSpectralTripleCalculus

variable {A : Type*} [Ring A]

/-- Grading involution $\gamma(X) = \Gamma_1 X \Gamma_1$ on $M_2(A)$. -/
def gradeInv (X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  gamma1Op * X * gamma1Op

/-- Connes' graded Dirac differential $d_D(X) = D X - \gamma(X) D$ on $M_2(A)$. -/
def connesDiff (D X : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  D * X - gradeInv X * D

/-- **Connes' Quantized Differential & Graded Curvature Cochain Theorem ($\mathcal{N}_2$)**:
For any odd Dirac operator $D = \bigl(\begin{smallmatrix} 0 & L_- \\ L_+ & 0 \end{smallmatrix}\bigr) \in M_2(A)$:
1. On any even operator $E = \mathrm{diag}(e_+, e_-)$, $d_D(E) = \⁅D, E⁆$ (Connes' quantized 1-form $đE$),
2. On any odd 1-form $\Omega_1 = \bigl(\begin{smallmatrix} 0 & w_- \\ w_+ & 0 \end{smallmatrix}\bigr)$,
   $d_D(\Omega_1) = \{D, \Omega_1\}$,
3. On *any* operator $X \in M_2(A)$, $d_D(d_D(X)) = \⁅D^2, X⁆$, vanishing identically whenever $D^2 = 0$. -/
theorem connes_quantized_differential_and_curvature_cochain
    (L_plus L_minus e_plus e_minus w_plus w_minus : A)
    (X : Matrix (Fin 2) (Fin 2) A) :
    let D   : Matrix (Fin 2) (Fin 2) A := mat2 0 L_minus L_plus 0
    let E   : Matrix (Fin 2) (Fin 2) A := mat2 e_plus 0 0 e_minus
    let Ω_1 : Matrix (Fin 2) (Fin 2) A := mat2 0 w_minus w_plus 0
    connesDiff D E = ⁅D, E⁆ ∧
    connesDiff D Ω_1 = anticomm D Ω_1 ∧
    connesDiff D (connesDiff D X) = ⁅D * D, X⁆ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [connesDiff, gradeInv, gamma1Op]
  · apply ext_fin2 <;> simp [connesDiff, anticomm, gradeInv, gamma1Op]
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [connesDiff, gradeInv, gamma1Op] <;> noncomm_ring

end HorizonN2_ConnesSpectralTripleCalculus

/-!
## Horizon $\mathcal{N}_3$: Noncommutative Geodesic Equation & Levi-Civita Parallel Transport of the Burg–Stein Metric
-/

section HorizonN3_NoncommutativeGeodesicsAndParallelTransport

variable {B : Type*} [Ring B]

def IsRingDeriv (D : B →+ B) : Prop :=
  ∀ a b : B, D (a * b) = D a * b + a * D b

theorem IsRingDeriv.map_one {D : B →+ B} (hD : IsRingDeriv D) : D 1 = 0 := by
  have h : D (1 * 1) = D 1 * 1 + 1 * D 1 := hD 1 1
  simp only [mul_one, one_mul] at h
  calc D 1 = D 1 + D 1 - D 1 := by abel
    _ = D 1 - D 1 := by rw [← h]
    _ = 0 := sub_self (D 1)

theorem IsRingDeriv.map_units_inv {D : B →+ B} (hD : IsRingDeriv D) (X : Bˣ) :
    D (↑X⁻¹ : B) = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by
  have h1 : D ((X : B) * (↑X⁻¹ : B)) = D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B) :=
    hD (X : B) (↑X⁻¹ : B)
  rw [Units.mul_inv, hD.map_one] at h1
  have h2 : (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) = 0 := by
    rw [← h1, mul_zero]
  have h3 : (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) = D (↑X⁻¹ : B) := by
    rw [Units.inv_mul, one_mul]
  calc D (↑X⁻¹ : B)
    _ = (↑X⁻¹ : B) * (X : B) * D (↑X⁻¹ : B) -
        (↑X⁻¹ : B) * (D (X : B) * (↑X⁻¹ : B) + (X : B) * D (↑X⁻¹ : B)) := by
        rw [h3, h2, sub_zero]
    _ = -(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) := by noncomm_ring

def windingForm (D : B →+ B) (X : Bˣ) : B := (↑X⁻¹ : B) * D (X : B)
def rightWindingForm (D : B →+ B) (X : Bˣ) : B := D (X : B) * (↑X⁻¹ : B)
def burgSteinHessian (X : Bˣ) (V : B) : B := (↑X⁻¹ : B) * V * (↑X⁻¹ : B)

/-- **Noncommutative Geodesic Duality & Levi-Civita Parallel Transport Theorem ($\mathcal{N}_3$)**:
1. The derivatives of the right and left winding forms are conjugate:
   $D(\mathcal{W}_D(X)) = X D(\omega_D(X)) X^{-1}$, so $D(\omega_D(X)) = 0 \iff D(\mathcal{W}_D(X)) = 0$,
2. Two-sided congruence $V_X = X V_0 X$ ($D V_0 = 0$) is Levi-Civita parallel transport for the
   Burg–Stein Hessian: $\mathcal{H}_X(X V_0 X) = V_0$ and $D(\mathcal{H}_X(X V_0 X)) = 0$. -/
theorem noncommutative_geodesic_duality_and_parallel_transport
    {D : B →+ B} (hD : IsRingDeriv D) (X : Bˣ) {V₀ : B} (hV₀ : D V₀ = 0) :
    D (rightWindingForm D X) = (X : B) * D (windingForm D X) * (↑X⁻¹ : B) ∧
    (D (windingForm D X) = 0 ↔ D (rightWindingForm D X) = 0) ∧
    burgSteinHessian X ((X : B) * V₀ * (X : B)) = V₀ ∧
    D (burgSteinHessian X ((X : B) * V₀ * (X : B))) = 0 := by
  have hX1 : (X : B) * (↑X⁻¹ : B) = 1 := Units.mul_inv X
  have hX2 : (↑X⁻¹ : B) * (X : B) = 1 := Units.inv_mul X
  have h_conj : D (rightWindingForm D X) = (X : B) * D (windingForm D X) * (↑X⁻¹ : B) := by
    have h_eq : rightWindingForm D X = (X : B) * windingForm D X * (↑X⁻¹ : B) := by
      dsimp [rightWindingForm, windingForm]
      calc D (X : B) * (↑X⁻¹ : B)
        _ = ((X : B) * (↑X⁻¹ : B)) * D (X : B) * (↑X⁻¹ : B) := by rw [hX1, one_mul]
        _ = (X : B) * ((↑X⁻¹ : B) * D (X : B)) * (↑X⁻¹ : B) := by noncomm_ring
    rw [h_eq, hD ((X : B) * windingForm D X) (↑X⁻¹ : B),
        hD (X : B) (windingForm D X), hD.map_units_inv X]
    dsimp [windingForm]
    calc (D (X : B) * ((↑X⁻¹ : B) * D (X : B)) + (X : B) * D ((↑X⁻¹ : B) * D (X : B))) * (↑X⁻¹ : B) +
          (X : B) * ((↑X⁻¹ : B) * D (X : B)) * (-(↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B))
      _ = D (X : B) * (↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) -
          ((X : B) * (↑X⁻¹ : B)) * D (X : B) * (↑X⁻¹ : B) * D (X : B) * (↑X⁻¹ : B) +
          (X : B) * D ((↑X⁻¹ : B) * D (X : B)) * (↑X⁻¹ : B) := by noncomm_ring
      _ = (X : B) * D ((↑X⁻¹ : B) * D (X : B)) * (↑X⁻¹ : B) := by rw [hX1]; noncomm_ring
  have h_hess : burgSteinHessian X ((X : B) * V₀ * (X : B)) = V₀ := by
    dsimp [burgSteinHessian]
    calc (↑X⁻¹ : B) * ((X : B) * V₀ * (X : B)) * (↑X⁻¹ : B)
      _ = ((↑X⁻¹ : B) * (X : B)) * V₀ * ((X : B) * (↑X⁻¹ : B)) := by noncomm_ring
      _ = V₀ := by rw [hX2, hX1]; noncomm_ring
  refine ⟨h_conj, ?_, h_hess, by rw [h_hess, hV₀]⟩
  constructor
  · intro h0; rw [h_conj, h0]; noncomm_ring
  · intro h0
    calc D (windingForm D X)
      _ = ((↑X⁻¹ : B) * (X : B)) * D (windingForm D X) * ((↑X⁻¹ : B) * (X : B)) := by
          rw [hX2]; noncomm_ring
      _ = (↑X⁻¹ : B) * ((X : B) * D (windingForm D X) * (↑X⁻¹ : B)) * (X : B) := by noncomm_ring
      _ = (↑X⁻¹ : B) * D (rightWindingForm D X) * (X : B) := by rw [← h_conj]
      _ = 0 := by rw [h0]; noncomm_ring

end HorizonN3_NoncommutativeGeodesicsAndParallelTransport

/-!
## Horizon $\mathcal{N}_4$: Multi-Strand Artin Braid Group $B_N$ (Adjacent Yang–Baxter + Far-Commutativity)
-/

section HorizonN4_MultiStrandArtinBraidGroup

variable {B : Type*} [Ring B]

theorem clifford_bivector_triple_product {E₁₂ E₂₃ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h_anti : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0) :
    (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂) = 2 * (E₁₂ + E₂₃) := by
  have h12' : E₁₂ * E₁₂ + 1 = 0 := by rw [h12]; abel
  calc (1 + E₁₂) * (1 + E₂₃) * (1 + E₁₂)
    _ = 2 * (E₁₂ + E₂₃) + (E₁₂ * E₁₂ + 1) * (1 - E₂₃) +
        (1 + E₁₂) * (E₁₂ * E₂₃ + E₂₃ * E₁₂) := by noncomm_ring
    _ = 2 * (E₁₂ + E₂₃) + 0 * (1 - E₂₃) + (1 + E₁₂) * 0 := by rw [h12', h_anti]
    _ = 2 * (E₁₂ + E₂₃) := by noncomm_ring

/-- **Multi-Strand Clifford–Majorana Artin Braid Group Theorem ($\mathcal{N}_4$)**:
For any chain of skew-involutive bivectors $E_{12}, E_{23}, E_{34} \in B$ ($E^2 = -1$) where
adjacent bivectors anticommute ($\{E_{12}, E_{23}\} = \{E_{23}, E_{34}\} = 0$) and disjoint
bivectors commute ($\⁅E_{12}, E_{34}⁆ = 0$), the braid operators $R_1 = 1 + E_{12}$,
$R_2 = 1 + E_{23}$, $R_3 = 1 + E_{34}$ satisfy all defining relations of the 4-strand Artin braid group $B_4$:
$R_1 R_2 R_1 = R_2 R_1 R_2$, $R_2 R_3 R_2 = R_3 R_2 R_3$, and $R_1 R_3 = R_3 R_1$. -/
theorem multi_strand_artin_braid_group_relations
    {E₁₂ E₂₃ E₃₄ : B}
    (h12 : E₁₂ * E₁₂ = -1) (h23 : E₂₃ * E₂₃ = -1) (h34 : E₃₄ * E₃₄ = -1)
    (h_anti12 : E₁₂ * E₂₃ + E₂₃ * E₁₂ = 0)
    (h_anti23 : E₂₃ * E₃₄ + E₃₄ * E₂₃ = 0)
    (h_far13  : ⁅E₁₂, E₃₄⁆ = 0) :
    let R₁ := 1 + E₁₂
    let R₂ := 1 + E₂₃
    let R₃ := 1 + E₃₄
    R₁ * R₂ * R₁ = R₂ * R₁ * R₂ ∧
    R₂ * R₃ * R₂ = R₃ * R₂ * R₃ ∧
    R₁ * R₃ = R₃ * R₁ := by
  have h_anti21 : E₂₃ * E₁₂ + E₁₂ * E₂₃ = 0 := by rw [add_comm, h_anti12]
  have h_anti32 : E₃₄ * E₂₃ + E₂₃ * E₃₄ = 0 := by rw [add_comm, h_anti23]
  refine ⟨?_, ?_, ?_⟩
  · dsimp
    rw [clifford_bivector_triple_product h12 h_anti12,
        clifford_bivector_triple_product h23 h_anti21]
    noncomm_ring
  · dsimp
    rw [clifford_bivector_triple_product h23 h_anti23,
        clifford_bivector_triple_product h34 h_anti32]
    noncomm_ring
  · dsimp
    rw [Ring.lie_def] at h_far13
    have h_comm : E₁₂ * E₃₄ = E₃₄ * E₁₂ := sub_eq_zero.mp h_far13
    calc (1 + E₁₂) * (1 + E₃₄) = 1 + E₁₂ + E₃₄ + E₁₂ * E₃₄ := by noncomm_ring
      _ = 1 + E₁₂ + E₃₄ + E₃₄ * E₁₂ := by rw [h_comm]
      _ = (1 + E₃₄) * (1 + E₁₂) := by noncomm_ring

end HorizonN4_MultiStrandArtinBraidGroup

end NoncommutativeFutureHorizonsTower
```

## Turn 0051, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeHistoricalComparisonSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma tr2_00 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 0 = M 0 0 := rfl
@[simp] lemma tr2_01 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 1 = M 1 0 := rfl
@[simp] lemma tr2_10 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 0 = M 0 1 := rfl
@[simp] lemma tr2_11 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 1 = M 1 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

def gamma1Op   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def P_plus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def F_plus     : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def F_minus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def N_plus     : Matrix (Fin 2) (Fin 2) A := mat2 (-1) (-1) 1 1
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a
def kleinTwist (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 (-a)

end Matrix2Simp

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-!
## Contrast $\mathcal{C}\mathcal{M}_1$: Central Braiding Collapse vs. Non-Central Infinite-Order Parabolic Monodromy
-/

section ContrastCM1_CentralVsParabolicCocycle

def conjBy {G : Type*} [Group G] (x q : G) : G := x * q * x⁻¹

def twistedCocycle {G : Type*} [Group G] (X Q : G) : ℕ → G
  | 0     => 1
  | n + 1 => Q * conjBy X (twistedCocycle X Q n)

/-- When $Q$ commutes with $X$ (the classical central assumption), the Wilson 1-cocycle
$\mathcal{W}_X^{(n)}(Q)$ collapses to the naive power $Q^n$. -/
theorem central_cocycle_collapses_to_pow {G : Type*} [Group G] {X Q : G}
    (h_comm : X * Q = Q * X) (n : ℕ) :
    twistedCocycle X Q n = Q ^ n := by
  have h_conj : ∀ k : ℕ, X * Q ^ k * X⁻¹ = Q ^ k := by
    intro k
    induction' k with k ih
    · group
    · calc X * Q ^ (k + 1) * X⁻¹
        _ = (X * Q * X⁻¹) * (X * Q ^ k * X⁻¹) := by rw [pow_succ']; group
        _ = Q * Q ^ k := by rw [ih, h_comm]; group
        _ = Q ^ (k + 1) := by rw [← pow_succ']
  induction' n with n ih
  · simp [twistedCocycle]
  · rw [twistedCocycle, ih, conjBy, h_conj n, ← pow_succ']

def X_blk {B : Type*} [Ring B] : NestedMat B := mat2 0 (1 - F_plus) (1 + F_plus) 0
def Z_blk {B : Type*} [Ring B] : NestedMat B := mat2 sigmaOp 0 0 gamma1Op
def N_blk {B : Type*} [Ring B] : NestedMat B := mat2 N_plus 0 0 (-F_minus)
def Q_blk {B : Type*} [Ring B] : NestedMat B := (Z_blk * X_blk) * (Z_blk * X_blk)

/-- **Contrast Theorem $\mathcal{C}\mathcal{M}_1$**:
Whereas any central braiding phase $Q$ collapses $\mathcal{W}_X^{(n)}(Q) = Q^n$ (so $X^2 = 1$
forces $Q^2 = 1$), our non-central Witt-link operators $X_{\mathrm{blk}}, Z_{\mathrm{blk}} \in M_2(M_2(B))$
satisfy $X_{\mathrm{blk}}^2 = Z_{\mathrm{blk}}^2 = 1$ and $\mathcal{W}_{X_{\mathrm{blk}}}^{(2)}(Q_{\mathrm{blk}}) = 1$
while $Q_{\mathrm{blk}}^n = 1 + n \bullet \mathcal{N}_{\mathrm{blk}}$ has infinite order over any `[CharZero B]`. -/
theorem contrast_central_collapse_vs_noncentral_parabolic_monodromy
    {B : Type*} [Ring B] [CharZero B] (n : ℕ) (hn : 0 < n) :
    (X_blk : NestedMat B) * X_blk = 1 ∧
    (Z_blk : NestedMat B) * Z_blk = 1 ∧
    (Q_blk : NestedMat B) * (X_blk * Q_blk * X_blk) = 1 ∧
    (Q_blk : NestedMat B) ^ n = 1 + n • N_blk ∧
    (Q_blk : NestedMat B) ^ n ≠ 1 := by
  have hQ : (Q_blk : NestedMat B) = 1 + N_blk := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Q_blk, Z_blk, X_blk, sigmaOp, gamma1Op, F_plus, F_minus, N_blk, N_plus] <;> abel
  have hN2 : (N_blk : NestedMat B) * N_blk = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [N_blk, N_plus, F_minus]
  have hPow : ∀ k : ℕ, (Q_blk : NestedMat B) ^ k = 1 + k • N_blk := by
    intro k
    induction' k with k ih
    · simp
    · rw [pow_succ, ih, hQ, add_nsmul, one_nsmul]
      have h_mul : (k • (N_blk : NestedMat B)) * N_blk = 0 := by
        rw [nsmul_eq_mul, mul_assoc, hN2, mul_zero]
      calc (1 + k • (N_blk : NestedMat B)) * (1 + N_blk)
        _ = 1 + (k • N_blk + N_blk) + (k • N_blk) * N_blk := by noncomm_ring
        _ = 1 + (k • N_blk + N_blk) := by rw [h_mul, add_zero]
  refine ⟨?_, ?_, ?_, hPow n, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [X_blk, F_plus]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [Z_blk, sigmaOp, gamma1Op]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Q_blk, Z_blk, X_blk, sigmaOp, gamma1Op, F_plus] <;> abel
  · intro h_eq
    have h_entry : (((Q_blk : NestedMat B) ^ n) 0 0) 1 0 = ((1 : NestedMat B) 0 0) 1 0 := by
      rw [h_eq]
    rw [hPow n] at h_entry
    simp [N_blk, N_plus] at h_entry
    exact Nat.ne_of_gt hn h_entry

end ContrastCM1_CentralVsParabolicCocycle

/-!
## Contrast $\mathcal{C}\mathcal{M}_2$: Commuting Projection Triviality vs. Noncommutative Cayley–Peirce FUP Variance
-/

section ContrastCM2_CommutingVsNoncommutingFUPVariance

variable {A : Type*} [Ring A] [StarRing A]

def symCompress {B : Type*} [Ring B] (P Q : B) : B := P * Q * P
def cayleyOp : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp

/-- **Contrast Theorem $\mathcal{C}\mathcal{M}_2$**:
1. Whenever two projections $P, Q \in B$ commute ($\⁅P, Q⁆ = 0$), the localization operator
   $T_{P, Q} = P Q P$ has identically zero uncertainty variance ($T_{P, Q} - T_{P, Q}^2 = 0$).
2. In contrast, for the Peirce projection $P_+$ and the Cayley–Fourier dual projection
   $Q_+^{(2)} = \mathcal{C}_{\mathrm{Cayley}} P_+ \mathcal{C}_{\mathrm{Cayley}}^\dagger = 1 + \Sigma$,
   their commutator is $\⁅P_+, Q_+^{(2)}⁆ = -\Omega$, and the scaled variance is
   $2 \bullet T_{P_+, Q_+^{(2)}} - T_{P_+, Q_+^{(2)}}^2 = P_+$. -/
theorem contrast_commuting_projection_vs_cayley_peirce_fup_variance
    {B : Type*} [Ring B] {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q) (h_comm : ⁅P, Q⁆ = 0) :
    let Q_dual : Matrix (Fin 2) (Fin 2) A := cayleyOp * P_plus * cayleyOpᴴ
    let T_fup  : Matrix (Fin 2) (Fin 2) A := symCompress P_plus Q_dual
    symCompress P Q - symCompress P Q * symCompress P Q = 0 ∧
    ⁅(P_plus : Matrix (Fin 2) (Fin 2) A), Q_dual⁆ = -omegaOp ∧
    2 • T_fup - T_fup * T_fup = (P_plus : Matrix (Fin 2) (Fin 2) A) := by
  have hPQ : P * Q = Q * P := sub_eq_zero.mp (by rw [← Ring.lie_def, h_comm])
  refine ⟨?_, ?_, ?_⟩
  · dsimp [symCompress]
    calc P * Q * P - P * Q * P * (P * Q * P)
      _ = P * Q * P - P * Q * (P * P) * Q * P := by noncomm_ring
      _ = P * Q * P - P * Q * (P * Q) * P := by rw [hP]; noncomm_ring
      _ = P * Q * P - P * (Q * Q) * (P * P) := by rw [hPQ]; noncomm_ring
      _ = P * Q * P - P * Q * P := by rw [hQ, hP]
      _ = 0 := sub_self _
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [cayleyOp, P_plus, omegaOp]
  · apply ext_fin2 <;> simp [symCompress, cayleyOp, P_plus, omegaOp, two_smul]

end ContrastCM2_CommutingVsNoncommutingFUPVariance

/-!
## Contrast $\mathcal{C}\mathcal{M}_3$ & $\mathcal{C}\mathcal{M}_4$: Constant Abelian Curvature & Commutative Cayley–Hamilton Collapse vs. Noncommutative Obstructions
-/

section ContrastCM3_CM4_CurvatureAndCharpolyObstructions

variable {A : Type*} [Ring A]

def mcCurvature {B : Type*} [Ring B] (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B :=
  d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆

def flowGen (cGamma cSigma cOmega : A) : Matrix (Fin 2) (Fin 2) A :=
  fiberEmbed cGamma * gamma1Op + fiberEmbed cSigma * sigmaOp + fiberEmbed cOmega * omegaOp

def E₁ : NestedMat A := omegaOp
def E₂ : NestedMat A := kleinTwist omegaOp
def E₃ : NestedMat A := (E₁ : NestedMat A) * E₂

/-- **Contrast Theorem $\mathcal{C}\mathcal{M}_3$ & $\mathcal{C}\mathcal{M}_4$**:
1. For any commuting connections $\⁅A_1, A_2⁆ = 0$, constant-potential curvature $F_{12}(0, 0, A_1, A_2)$
   collapses to $0$, whereas for the Brauer–Weyl quaternion potentials $E_1, E_2 \in M_2(M_2(A))$,
   $F_{12}(0, 0, E_1, E_2) = 2 \bullet E_3$,
2. For commuting fiber coordinates $\⁅c_\alpha, c_\beta⁆ = 0$, $X_{\mathrm{flow}}^2$ collapses to
   the scalar Casimir $\iota(c_\Gamma^2 + c_\Sigma^2 - c_\Omega^2)$, whereas in general the exact
   remainder is the non-Abelian $\mathfrak{sl}_2$ Lie cross product. -/
theorem contrast_abelian_collapse_vs_noncommutative_curvature_and_charpoly
    {A₁ A₂ : A} (hA_comm : ⁅A₁, A₂⁆ = 0) (cGamma cSigma cOmega : A) :
    mcCurvature (0 : A →+ A) 0 A₁ A₂ = 0 ∧
    mcCurvature (0 : NestedMat A →+ NestedMat A) 0 (E₁ : NestedMat A) E₂ = 2 • E₃ ∧
    flowGen cGamma cSigma cOmega * flowGen cGamma cSigma cOmega -
      fiberEmbed (cGamma * cGamma + cSigma * cSigma - cOmega * cOmega) * 1 =
      fiberEmbed ⁅cSigma, cOmega⁆ * gamma1Op +
      fiberEmbed ⁅cOmega, cGamma⁆ * sigmaOp -
      fiberEmbed ⁅cGamma, cSigma⁆ * omegaOp := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [mcCurvature]; simp [hA_comm]
  · dsimp [mcCurvature]; rw [Ring.lie_def]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [E₁, E₂, E₃, kleinTwist, omegaOp, two_smul] <;> abel
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp] <;> noncomm_ring

end ContrastCM3_CM4_CurvatureAndCharpolyObstructions

/-!
## Contrast $\mathcal{C}\mathcal{M}_5$: The Córdova–Freed–Teleman Dichotomy — Orthogonal Gapped Torsion vs. Non-Orthogonal Parabolic Monodromy
-/

section ContrastCM5_OrthogonalTorsionVsNonOrthogonalParabolic

/-- Orthogonal gapped boundary symmetry generators $T_1, T_2 \in M_2(M_2(\mathbb{Z}))$ and their
non-diagonal order-4 torsion anomaly $\mathcal{A}_{\mathrm{torsion}} = \mathrm{diag}(-\Omega, \Omega)$. -/
def T1_orth   : NestedMat ℤ := sigmaOp
def T2_orth   : NestedMat ℤ := mat2 omegaOp 0 0 1
def A_torsion : NestedMat ℤ := mat2 (-omegaOp) 0 0 omegaOp

/-- **Contrast Theorem $\mathcal{C}\mathcal{M}_5$ (The Gapped-Torsion vs. Gapless-Parabolic Dichotomy)**:
In $M_2(M_2(\mathbb{Z}))$:
1. The gapped boundary generators $T_1, T_2$ are orthogonal ($T_1^\top T_1 = 1$, $T_2^\top T_2 = 1$)
   and satisfy $T_1 T_2 = \mathcal{A}_{\mathrm{torsion}} T_2 T_1$, where $\mathcal{A}_{\mathrm{torsion}}$
   has **finite torsion order $4$** ($\mathcal{A}_{\mathrm{torsion}}^2 = -1 \neq 1$, $\mathcal{A}_{\mathrm{torsion}}^4 = 1$).
2. In contrast, the unipotent Witt-link shift $X_{\mathrm{blk}}$ violates orthogonality
   ($X_{\mathrm{blk}}^\top X_{\mathrm{blk}} \neq 1$), allowing its braiding holonomy $Q_{\mathrm{blk}}$
   to escape torsion and attain **infinite multiplicative order** ($Q_{\mathrm{blk}}^n \neq 1$ for all $n > 0$). -/
theorem contrast_orthogonal_gapped_torsion_vs_nonorthogonal_parabolic
    (n : ℕ) (hn : 0 < n) :
    (T1_orth : NestedMat ℤ)ᵀ * T1_orth = 1 ∧
    (T2_orth : NestedMat ℤ)ᵀ * T2_orth = 1 ∧
    T1_orth * T2_orth = A_torsion * T2_orth * T1_orth ∧
    (A_torsion : NestedMat ℤ) ^ 2 ≠ 1 ∧
    (A_torsion : NestedMat ℤ) ^ 4 = 1 ∧
    (X_blk : NestedMat ℤ)ᵀ * X_blk ≠ 1 ∧
    (Q_blk : NestedMat ℤ) ^ n ≠ 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact (contrast_central_collapse_vs_noncentral_parabolic_monodromy n hn).2.2.2.2

end ContrastCM5_OrthogonalTorsionVsNonOrthogonalParabolic

end NoncommutativeHistoricalComparisonSynthesis
```

## Turn 0054, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeAllScalesTowerAndContrastSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma tr2_00 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 0 = M 0 0 := rfl
@[simp] lemma tr2_01 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 1 = M 1 0 := rfl
@[simp] lemma tr2_10 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 0 = M 0 1 := rfl
@[simp] lemma tr2_11 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 1 = M 1 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

def gamma1Op   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def P_plus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def F_plus     : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def F_minus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def N_plus     : Matrix (Fin 2) (Fin 2) A := mat2 (-1) (-1) 1 1
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a
def kleinTwist (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 (-a)

end Matrix2Simp

/-!
## Stratum $\mathcal{I}\mathcal{T}_1$ & $\mathcal{I}\mathcal{T}_2$: All-Scales Witt–Cantor Chiral Hodge & Atiyah–Singer Supertrace on $\mathcal{C}\ell_n(A)$
-/

section StratumIT1_IT2_InductiveHodgeAndSupertrace

universe u

def ClTower : ℕ → Type u → Type u
  | 0, A     => A
  | n + 1, A => Matrix (Fin 2) (Fin 2) (ClTower n A)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower n A)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower n A) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower n A)))

variable {A : Type u} [Ring A]

/-- The $n$-scale Cantor corner projection $\Pi_{\mathcal{C}_n} \in \mathcal{C}\ell_n(A)$. -/
def cantorTowerProj : ∀ n : ℕ, ClTower n A
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorTowerProj n) 0 0 0

/-- The $n$-scale chirality grading involution $\Gamma^{(n)} \in \mathcal{C}\ell_n(A)$. -/
def gammaTowerOp : ∀ n : ℕ, ClTower n A
  | 0     => (1 : A)
  | n + 1 => mat2 (gammaTowerOp n) 0 0 (-gammaTowerOp n)

/-- Single-step RG block decimation $\mathcal{R}_{\mathrm{RG}} : \mathcal{C}\ell_{n+1}(A) \to \mathcal{C}\ell_n(A)$. -/
def rgTowerDecimate (n : ℕ) (M : ClTower (n + 1) A) : ClTower n A :=
  M 0 0 + M 1 1

/-- Iterated $n$-scale partition trace $\mathrm{Tr}_{2^n} : \mathcal{C}\ell_n(A) \to A$. -/
def towerTrace : ∀ n : ℕ, ClTower n A → A
  | 0, a     => a
  | n + 1, M => towerTrace n (rgTowerDecimate n M)

/-- Iterated $n$-scale Atiyah–Singer supertrace $\mathrm{Str}_{2^n}(M) = \mathrm{Tr}_{2^n}(\Gamma^{(n)} M)$. -/
def towerSuperTrace (n : ℕ) (M : ClTower n A) : A :=
  towerTrace n (gammaTowerOp n * M)

/-- The $(n+1)$-scale coupled isotropic Witt differentials $d_n, \delta_n \in \mathcal{C}\ell_{n+1}(A)$. -/
def wittTowerD (n : ℕ) : ClTower (n + 1) A :=
  mat2 0 (cantorTowerProj n) 0 0

def wittTowerDelta (n : ℕ) : ClTower (n + 1) A :=
  mat2 0 0 (cantorTowerProj n) 0

theorem cantorTowerProj_idem : ∀ n : ℕ,
    (cantorTowerProj n : ClTower n A) * cantorTowerProj n = cantorTowerProj n
  | 0     => mul_one 1
  | n + 1 => by
      apply ext_fin2 <;> simp [cantorTowerProj, cantorTowerProj_idem n]

theorem towerTrace_zero : ∀ n : ℕ, towerTrace n (0 : ClTower n A) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace, rgTowerDecimate]
      simp [towerTrace_zero n]

/-- **All-Scales Inductive Witt–Cantor Chiral Hodge Theorem ($\mathcal{I}\mathcal{T}_1$)**:
At every scale $n \in \mathbb{N}$ in $\mathcal{C}\ell_{n+1}(A)$:
1. $d_n^2 = 0$, $\delta_n^2 = 0$, $d_n \delta_n d_n = d_n$, $\delta_n d_n \delta_n = \delta_n$,
2. The exact Hodge projection $d_n \delta_n$ is identically $\Pi_{\mathcal{C}_{n+1}}$,
3. For any $\mathbb{X} \in \mathcal{C}\ell_{n+1}(A)$,
   $(d_n + \delta_n)\mathbb{X} = 0 \iff (1 - (d_n\delta_n + \delta_n d_n))\mathbb{X} = \mathbb{X}$. -/
theorem all_scales_inductive_witt_cantor_chiral_hodge (n : ℕ) (X : ClTower (n + 1) A) :
    let d_n   := (wittTowerD n : ClTower (n + 1) A)
    let del_n := (wittTowerDelta n : ClTower (n + 1) A)
    d_n * d_n = 0 ∧
    del_n * del_n = 0 ∧
    d_n * del_n * d_n = d_n ∧
    del_n * d_n * del_n = del_n ∧
    d_n * del_n = cantorTowerProj (n + 1) ∧
    ((d_n + del_n) * X = 0 ↔ (1 - (d_n * del_n + del_n * d_n)) * X = X) := by
  have h_idem := cantorTowerProj_idem (A := A) n
  have hd2 : (wittTowerD n : ClTower (n + 1) A) * wittTowerD n = 0 := by
    apply ext_fin2 <;> simp [wittTowerD]
  have hdel2 : (wittTowerDelta n : ClTower (n + 1) A) * wittTowerDelta n = 0 := by
    apply ext_fin2 <;> simp [wittTowerDelta]
  have hddeld : (wittTowerD n : ClTower (n + 1) A) * wittTowerDelta n * wittTowerD n = wittTowerD n := by
    apply ext_fin2 <;> simp [wittTowerD, wittTowerDelta, h_idem]
  have hdelddel : (wittTowerDelta n : ClTower (n + 1) A) * wittTowerD n * wittTowerDelta n = wittTowerDelta n := by
    apply ext_fin2 <;> simp [wittTowerD, wittTowerDelta, h_idem]
  have h_ex : (wittTowerD n : ClTower (n + 1) A) * wittTowerDelta n = cantorTowerProj (n + 1) := by
    apply ext_fin2 <;> simp [wittTowerD, wittTowerDelta, cantorTowerProj, h_idem]
  refine ⟨hd2, hdel2, hddeld, hdelddel, h_ex, ?_⟩
  constructor
  · intro h
    have h1 : wittTowerD n * X = 0 := by
      calc wittTowerD n * X
        _ = (wittTowerD n * wittTowerDelta n * wittTowerD n) * X +
            wittTowerD n * (wittTowerDelta n * wittTowerDelta n) * X := by
            rw [hddeld, hdel2]; noncomm_ring
        _ = wittTowerD n * wittTowerDelta n * ((wittTowerD n + wittTowerDelta n) * X) := by
            noncomm_ring
        _ = wittTowerD n * wittTowerDelta n * 0 := by rw [h]
        _ = 0 := mul_zero _
    have h2 : wittTowerDelta n * X = 0 := by
      calc wittTowerDelta n * X
        _ = wittTowerDelta n * (wittTowerD n * wittTowerD n) * X +
            (wittTowerDelta n * wittTowerD n * wittTowerDelta n) * X := by
            rw [hd2, hdelddel]; noncomm_ring
        _ = wittTowerDelta n * wittTowerD n * ((wittTowerD n + wittTowerDelta n) * X) := by
            noncomm_ring
        _ = wittTowerDelta n * wittTowerD n * 0 := by rw [h]
        _ = 0 := mul_zero _
    calc (1 - (wittTowerD n * wittTowerDelta n + wittTowerDelta n * wittTowerD n)) * X
      _ = X - wittTowerD n * (wittTowerDelta n * X) -
          wittTowerDelta n * (wittTowerD n * X) := by noncomm_ring
      _ = X - wittTowerD n * 0 - wittTowerDelta n * 0 := by rw [h1, h2]
      _ = X := by noncomm_ring
  · intro hP
    calc (wittTowerD n + wittTowerDelta n) * X
      _ = (wittTowerD n + wittTowerDelta n) *
          ((1 - (wittTowerD n * wittTowerDelta n + wittTowerDelta n * wittTowerD n)) * X) := by
          rw [hP]
      _ = (wittTowerD n - wittTowerD n * wittTowerDelta n * wittTowerD n -
           (wittTowerD n * wittTowerD n) * wittTowerDelta n +
           wittTowerDelta n - (wittTowerDelta n * wittTowerDelta n) * wittTowerD n -
           wittTowerDelta n * wittTowerD n * wittTowerDelta n) * X := by noncomm_ring
      _ = (wittTowerD n - wittTowerD n - 0 * wittTowerDelta n +
           wittTowerDelta n - 0 * wittTowerD n - wittTowerDelta n) * X := by
          rw [hddeld, hd2, hdel2, hdelddel]
      _ = 0 := by noncomm_ring

/-- **All-Scales Inductive Atiyah–Singer Supertrace Theorem ($\mathcal{I}\mathcal{T}_2$)**:
For every scale $n \in \mathbb{N}$:
1. $(\Gamma^{(n)})^2 = 1$ and $\Gamma^{(n)} \Pi_{\mathcal{C}_n} = \Pi_{\mathcal{C}_n}$,
2. $\mathrm{Str}_{2^n}(\Pi_{\mathcal{C}_n}) = 1_A$,
3. For any spectral jump $\delta \in \mathcal{C}\ell_n(A)$, $\mathrm{Str}_{2^{n+1}}(\mathrm{diag}(\delta, \delta)) = 0$. -/
theorem all_scales_inductive_supertrace_and_jump_cancellation
    (n : ℕ) (δ : ClTower n A) :
    (gammaTowerOp n : ClTower n A) * gammaTowerOp n = 1 ∧
    (gammaTowerOp n : ClTower n A) * cantorTowerProj n = cantorTowerProj n ∧
    towerSuperTrace n (cantorTowerProj n : ClTower n A) = 1 ∧
    towerSuperTrace (n + 1) (mat2 δ 0 0 δ : ClTower (n + 1) A) = 0 := by
  have h_gamma_sq : ∀ k : ℕ, (gammaTowerOp k : ClTower k A) * gammaTowerOp k = 1 := by
    intro k; induction' k with k ih
    · exact mul_one 1
    · apply ext_fin2 <;> simp [gammaTowerOp, ih]
  have h_gamma_cantor : ∀ k : ℕ,
      (gammaTowerOp k : ClTower k A) * cantorTowerProj k = cantorTowerProj k := by
    intro k; induction' k with k ih
    · exact mul_one 1
    · apply ext_fin2 <;> simp [gammaTowerOp, cantorTowerProj, ih]
  have h_cantor_tr : ∀ k : ℕ, towerTrace k (cantorTowerProj k : ClTower k A) = 1 := by
    intro k; induction' k with k ih
    · rfl
    · dsimp [towerTrace, rgTowerDecimate, cantorTowerProj]
      rw [mat2_00, mat2_11, add_zero, ih]
  refine ⟨h_gamma_sq n, h_gamma_cantor n, ?_, ?_⟩
  · dsimp [towerSuperTrace]
    rw [h_gamma_cantor n, h_cantor_tr n]
  · dsimp [towerSuperTrace, towerTrace, rgTowerDecimate, gammaTowerOp]
    simp [sub_self, towerTrace_zero n]

end StratumIT1_IT2_InductiveHodgeAndSupertrace

/-!
## Stratum $\mathcal{I}\mathcal{T}_3$: All-Scales $2^k N$-Horizon Dyadic RG Trajectory Decimation
-/

section StratumIT3_AllScalesDyadicRGTrajectory

variable {B : Type*} [Ring B]

def rgBlockStep (X : ℕ → B) (m : ℕ) : B :=
  X (2 * m) + X (2 * m + 1)

def rgBlockIter : ℕ → (ℕ → B) → (ℕ → B)
  | 0, traj     => traj
  | k + 1, traj => rgBlockStep (rgBlockIter k traj)

def trajectoryMean (N : ℕ) (X : ℕ → B) : B :=
  ∑ m ∈ Finset.range N, X m

theorem trajectoryMean_rgBlockStep (N : ℕ) (traj : ℕ → B) :
    trajectoryMean N (rgBlockStep traj) = trajectoryMean (2 * N) traj := by
  dsimp [trajectoryMean, rgBlockStep]
  induction' N with N ih
  · simp
  · have h2N : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
    rw [Finset.sum_range_succ, ih, h2N, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]

/-- **All-Scales $2^k N$-Horizon Dyadic RG Trajectory Invariance ($\mathcal{I}\mathcal{T}_3$)**:
For every decimation depth $k \in \mathbb{N}$ and every horizon $N \in \mathbb{N}$,
$\mathrm{trajectoryMean}\; N\; (\mathrm{rgBlockIter}\; k\; \mathrm{traj}) = \mathrm{trajectoryMean}\; (2^k * N)\; \mathrm{traj}$. -/
theorem all_scales_dyadic_rg_trajectory_invariance (k N : ℕ) (traj : ℕ → B) :
    trajectoryMean N (rgBlockIter k traj) = trajectoryMean (2 ^ k * N) traj := by
  induction' k with k ih generalizing N
  · simp [rgBlockIter]
  · rw [rgBlockIter, trajectoryMean_rgBlockStep, ih (2 * N)]
    have h_pow : 2 ^ k * (2 * N) = 2 ^ (k + 1) * N := by
      rw [pow_succ, mul_assoc]
    rw [h_pow]

end StratumIT3_AllScalesDyadicRGTrajectory

/-!
## Stratum $\mathcal{I}\mathcal{T}_4$: The Five Decisive Historical Contrast Theorems ($\mathcal{C}\mathcal{M}_1$–$\mathcal{C}\mathcal{M}_5$)
-/

section StratumIT4_HistoricalContrastTheorems

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

def conjBy {G : Type*} [Group G] (x q : G) : G := x * q * x⁻¹

def twistedCocycle {G : Type*} [Group G] (X Q : G) : ℕ → G
  | 0     => 1
  | n + 1 => Q * conjBy X (twistedCocycle X Q n)

theorem central_cocycle_collapses_to_pow {G : Type*} [Group G] {X Q : G}
    (h_comm : X * Q = Q * X) (n : ℕ) :
    twistedCocycle X Q n = Q ^ n := by
  have h_conj : ∀ k : ℕ, X * Q ^ k * X⁻¹ = Q ^ k := by
    intro k; induction' k with k ih
    · group
    · calc X * Q ^ (k + 1) * X⁻¹
        _ = (X * Q * X⁻¹) * (X * Q ^ k * X⁻¹) := by rw [pow_succ']; group
        _ = Q * Q ^ k := by rw [ih, h_comm]; group
        _ = Q ^ (k + 1) := by rw [← pow_succ']
  induction' n with n ih
  · simp [twistedCocycle]
  · rw [twistedCocycle, ih, conjBy, h_conj n, ← pow_succ']

def X_blk {B : Type*} [Ring B] : NestedMat B := mat2 0 (1 - F_plus) (1 + F_plus) 0
def Z_blk {B : Type*} [Ring B] : NestedMat B := mat2 sigmaOp 0 0 gamma1Op
def N_blk {B : Type*} [Ring B] : NestedMat B := mat2 N_plus 0 0 (-F_minus)
def Q_blk {B : Type*} [Ring B] : NestedMat B := (Z_blk * X_blk) * (Z_blk * X_blk)

def symCompress {B : Type*} [Ring B] (P Q : B) : B := P * Q * P
def cayleyOp {A : Type*} [Ring A] : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp
def mcCurvature {B : Type*} [Ring B] (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B := d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆
def flowGen {A : Type*} [Ring A] (cGamma cSigma cOmega : A) : Matrix (Fin 2) (Fin 2) A :=
  fiberEmbed cGamma * gamma1Op + fiberEmbed cSigma * sigmaOp + fiberEmbed cOmega * omegaOp

def E₁ {A : Type*} [Ring A] : NestedMat A := omegaOp
def E₂ {A : Type*} [Ring A] : NestedMat A := kleinTwist omegaOp
def E₃ {A : Type*} [Ring A] : NestedMat A := (E₁ : NestedMat A) * E₂

def T1_orth   : NestedMat ℤ := sigmaOp
def T2_orth   : NestedMat ℤ := mat2 omegaOp 0 0 1
def A_torsion : NestedMat ℤ := mat2 (-omegaOp) 0 0 omegaOp

/-- **Master Historical Contrast Theorem ($\mathcal{I}\mathcal{T}_4 \text{ : }\mathcal{C}\mathcal{M}_1$–$\mathcal{C}\mathcal{M}_5$)**:
Contrasts commutative/central/orthogonal reductions against our noncommutative operator constructions. -/
theorem master_historical_contrast_synthesis
    {A : Type*} [Ring A] [StarRing A] [CharZero A]
    {P Q : A} (hP : P * P = P) (hQ : Q * Q = Q) (hPQ_comm : ⁅P, Q⁆ = 0)
    {A₁ A₂ : A} (hA_comm : ⁅A₁, A₂⁆ = 0)
    (cGamma cSigma cOmega : A) (n : ℕ) (hn : 0 < n) :
    let Q_dual : Matrix (Fin 2) (Fin 2) A := cayleyOp * P_plus * cayleyOpᴴ
    let T_fup  : Matrix (Fin 2) (Fin 2) A := symCompress P_plus Q_dual
    -- CM₁: Parabolic block monodromy of infinite order despite order-2 generators & 1-cocycle closure
    ((X_blk : NestedMat A) * X_blk = 1 ∧
     (Z_blk : NestedMat A) * Z_blk = 1 ∧
     (Q_blk : NestedMat A) * (X_blk * Q_blk * X_blk) = 1 ∧
     (Q_blk : NestedMat A) ^ n = 1 + n • N_blk ∧
     (Q_blk : NestedMat A) ^ n ≠ 1) ∧
    -- CM₂: Commuting projection variance collapse vs. non-zero Cayley–Peirce FUP variance
    (symCompress P Q - symCompress P Q * symCompress P Q = 0 ∧
     ⁅(P_plus : Matrix (Fin 2) (Fin 2) A), Q_dual⁆ = -omegaOp ∧
     2 • T_fup - T_fup * T_fup = (P_plus : Matrix (Fin 2) (Fin 2) A)) ∧
    -- CM₃ & CM₄: Constant Abelian curvature collapse vs. quaternion curvature & Lie cross-product
    (mcCurvature (0 : A →+ A) 0 A₁ A₂ = 0 ∧
     mcCurvature (0 : NestedMat A →+ NestedMat A) 0 (E₁ : NestedMat A) E₂ = 2 • E₃ ∧
     flowGen cGamma cSigma cOmega * flowGen cGamma cSigma cOmega -
       fiberEmbed (cGamma * cGamma + cSigma * cSigma - cOmega * cOmega) * 1 =
       fiberEmbed ⁅cSigma, cOmega⁆ * gamma1Op +
       fiberEmbed ⁅cOmega, cGamma⁆ * sigmaOp -
       fiberEmbed ⁅cGamma, cSigma⁆ * omegaOp) ∧
    -- CM₅: Orthogonal gapped finite-order torsion vs. non-orthogonal unipotent infinite order
    ((T1_orth : NestedMat ℤ)ᵀ * T1_orth = 1 ∧
     (T2_orth : NestedMat ℤ)ᵀ * T2_orth = 1 ∧
     T1_orth * T2_orth = A_torsion * T2_orth * T1_orth ∧
     (A_torsion : NestedMat ℤ) ^ 2 ≠ 1 ∧
     (A_torsion : NestedMat ℤ) ^ 4 = 1 ∧
     (X_blk : NestedMat ℤ)ᵀ * X_blk ≠ 1) := by
  have hQ_decomp : (Q_blk : NestedMat A) = 1 + N_blk := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Q_blk, Z_blk, X_blk, sigmaOp, gamma1Op, F_plus, F_minus, N_blk, N_plus] <;> abel
  have hN2 : (N_blk : NestedMat A) * N_blk = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [N_blk, N_plus, F_minus]
  have hPow : ∀ k : ℕ, (Q_blk : NestedMat A) ^ k = 1 + k • N_blk := by
    intro k; induction' k with k ih
    · simp
    · rw [pow_succ, ih, hQ_decomp, add_nsmul, one_nsmul]
      have h_mul : (k • (N_blk : NestedMat A)) * N_blk = 0 := by
        rw [nsmul_eq_mul, mul_assoc, hN2, mul_zero]
      calc (1 + k • (N_blk : NestedMat A)) * (1 + N_blk)
        _ = 1 + (k • N_blk + N_blk) + (k • N_blk) * N_blk := by noncomm_ring
        _ = 1 + (k • N_blk + N_blk) := by rw [h_mul, add_zero]
  have hPQ : P * Q = Q * P := sub_eq_zero.mp (by rw [← Ring.lie_def, hPQ_comm])
  refine ⟨⟨?_, ?_, ?_, hPow n, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
          ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [X_blk, F_plus]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [Z_blk, sigmaOp, gamma1Op]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Q_blk, Z_blk, X_blk, sigmaOp, gamma1Op, F_plus] <;> abel
  · intro h_eq
    have h_entry : (((Q_blk : NestedMat A) ^ n) 0 0) 1 0 = ((1 : NestedMat A) 0 0) 1 0 := by
      rw [h_eq]
    rw [hPow n] at h_entry
    simp [N_blk, N_plus] at h_entry
    exact Nat.ne_of_gt hn h_entry
  · dsimp [symCompress]
    calc P * Q * P - P * Q * P * (P * Q * P)
      _ = P * Q * P - P * Q * (P * P) * Q * P := by noncomm_ring
      _ = P * Q * P - P * Q * (P * Q) * P := by rw [hP]; noncomm_ring
      _ = P * Q * P - P * (Q * Q) * (P * P) := by rw [hPQ]; noncomm_ring
      _ = P * Q * P - P * Q * P := by rw [hQ, hP]
      _ = 0 := sub_self _
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [cayleyOp, P_plus, omegaOp]
  · apply ext_fin2 <;> simp [symCompress, cayleyOp, P_plus, omegaOp, two_smul]
  · dsimp [mcCurvature]; simp [hA_comm]
  · dsimp [mcCurvature]; rw [Ring.lie_def]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [E₁, E₂, E₃, kleinTwist, omegaOp, two_smul] <;> abel
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp] <;> noncomm_ring

end StratumIT4_HistoricalContrastTheorems

end NoncommutativeAllScalesTowerAndContrastSynthesis
```

## Turn 0057, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeContrastPoset

/-!
## Foundational Infrastructure: Division-Free $2 \times 2$ Operator Matrices over `[Ring B]`
-/

def mat2 {B : Type*} (a b c d : B) : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {B : Type*} {M N : Matrix (Fin 2) (Fin 2) B}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Helpers

variable {B : Type*} [Ring B]

@[simp] lemma mat2_00 (a b c d : B) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : B) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : B) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : B) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) B) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) B) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) B) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) B) 1 1 = 1 := rfl

@[simp] lemma tr2_00 (M : Matrix (Fin 2) (Fin 2) B) : Mᵀ 0 0 = M 0 0 := rfl
@[simp] lemma tr2_01 (M : Matrix (Fin 2) (Fin 2) B) : Mᵀ 0 1 = M 1 0 := rfl
@[simp] lemma tr2_10 (M : Matrix (Fin 2) (Fin 2) B) : Mᵀ 1 0 = M 0 1 := rfl
@[simp] lemma tr2_11 (M : Matrix (Fin 2) (Fin 2) B) : Mᵀ 1 1 = M 1 1 := rfl

def gamma1Op : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 (-1)
def sigmaOp  : Matrix (Fin 2) (Fin 2) B := mat2 0 1 1 0
def omegaOp  : Matrix (Fin 2) (Fin 2) B := mat2 0 (-1) 1 0

end Matrix2Helpers

/-!
## $\mathcal{C}\mathcal{M}_1$: Non-Abelian Wilson 1-Cocycle vs. Central Braiding Collapse
-/

section CM1_WilsonCocycle

/-- Path-ordered Wilson 1-cocycle $\mathcal{W}_X^{(n)}(Q)$ in an arbitrary noncommutative ring $B$. -/
def wilsonCocycle {B : Type*} [Ring B] (X Xinv Q : B) : ℕ → B
  | 0     => 1
  | n + 1 => Q * (X * wilsonCocycle X Xinv Q n * Xinv)

/-- **Central Braiding Collapse**: If $Q$ commutes with $X$ and $X X_{\mathrm{inv}} = 1$,
$\mathcal{W}_X^{(n)}(Q)$ collapses to the naive power $Q^n$. -/
theorem cm1_central_braiding_collapse {B : Type*} [Ring B] (X Xinv Q : B)
    (h_inv : X * Xinv = 1) (h_comm : Q * X = X * Q) :
    ∀ n : ℕ, wilsonCocycle X Xinv Q n = Q ^ n
  | 0     => rfl
  | n + 1 => by
      simp only [wilsonCocycle, cm1_central_braiding_collapse X Xinv Q h_inv h_comm n]
      have h_comm_pow : Q ^ n * X = X * Q ^ n := by
        induction' n with k ih
        · simp
        · calc Q ^ (k + 1) * X = Q * (Q ^ k * X) := by rw [pow_succ', mul_assoc]
            _ = Q * (X * Q ^ k) := by rw [ih]
            _ = (Q * X) * Q ^ k := by rw [← mul_assoc]
            _ = (X * Q) * Q ^ k := by rw [h_comm]
            _ = X * Q ^ (k + 1) := by rw [mul_assoc, ← pow_succ']
      calc Q * (X * Q ^ n * Xinv)
          = Q * ((Q ^ n * X) * Xinv) := by rw [h_comm_pow]
        _ = Q * (Q ^ n * (X * Xinv)) := by rw [mul_assoc]
        _ = Q * Q ^ n := by rw [h_inv, mul_one]
        _ = Q ^ (n + 1) := by rw [← pow_succ']

/-- The canonical $Cl(1,1)$ light-cone nilpotent generator $N_{\mathrm{par}} = \Omega - \Gamma_1 = \bigl(\begin{smallmatrix} -1 & -1 \\ 1 & 1 \end{smallmatrix}\bigr)$
and unipotent parabolic holonomy $Q_{\mathrm{par}} = 1 + N_{\mathrm{par}} = \bigl(\begin{smallmatrix} 0 & -1 \\ 1 & 2 \end{smallmatrix}\bigr)$. -/
def N_par {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B := mat2 (-1) (-1) 1 1
def Q_par {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B := mat2 0 (-1) 1 2

theorem cm1_sigmaOp_involution {B : Type*} [Ring B] :
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) * sigmaOp = 1 := by
  apply ext_fin2 <;> simp [sigmaOp]

theorem cm1_N_par_nilpotent_and_anticomm {B : Type*} [Ring B] :
    (N_par : Matrix (Fin 2) (Fin 2) B) = omegaOp - gamma1Op ∧
    (N_par : Matrix (Fin 2) (Fin 2) B) * N_par = 0 ∧
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) * N_par * sigmaOp = -N_par := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> simp [N_par, omegaOp, gamma1Op, sigmaOp])

theorem cm1_Q_par_pow {B : Type*} [Ring B] (n : ℕ) :
    (Q_par : Matrix (Fin 2) (Fin 2) B) ^ n = 1 + n • N_par := by
  have hQ : (Q_par : Matrix (Fin 2) (Fin 2) B) = 1 + N_par := by
    apply ext_fin2 <;> simp [Q_par, N_par]
  have hN2 : (N_par : Matrix (Fin 2) (Fin 2) B) * N_par = 0 :=
    cm1_N_par_nilpotent_and_anticomm.2.1
  induction' n with k ih
  · simp
  · rw [pow_succ, ih, hQ, add_nsmul, one_nsmul]
    have h_mul : (k • (N_par : Matrix (Fin 2) (Fin 2) B)) * N_par = 0 := by
      rw [nsmul_eq_mul, mul_assoc, hN2, mul_zero]
    calc (1 + k • (N_par : Matrix (Fin 2) (Fin 2) B)) * (1 + N_par)
      _ = 1 + (k • N_par + N_par) + (k • N_par) * N_par := by noncomm_ring
      _ = 1 + (k • N_par + N_par) := by rw [h_mul, add_zero]

/-- **Repaired 2-Cocycle Closure**: Because $\Sigma N_{\mathrm{par}} \Sigma = -N_{\mathrm{par}}$ and
$N_{\mathrm{par}}^2 = 0$, the Wilson 1-cocycle $\mathcal{W}_\Sigma^{(2)}(Q_{\mathrm{par}})$ closes to $1$
over every noncommutative ring $B$, even though $Q_{\mathrm{par}}^n = 1 + n \bullet N_{\mathrm{par}}$. -/
theorem cm1_nonabelian_wilson_closes_at_two {B : Type*} [Ring B] :
    wilsonCocycle (sigmaOp : Matrix (Fin 2) (Fin 2) B) sigmaOp Q_par 2 = 1 := by
  dsimp [wilsonCocycle]
  apply ext_fin2 <;> simp [sigmaOp, Q_par]

end CM1_WilsonCocycle

/-!
## $\mathcal{C}\mathcal{M}_2$: Fractal Uncertainty Principle (FUP) & Pore Leakage Variance
-/

section CM2_FractalUncertainty

def toeplitzOp {B : Type*} [Ring B] (P Q : B) : B := P * Q * P

theorem cm2_commuting_projection_triviality {B : Type*} [Ring B] (P Q : B)
    (hP : P * P = P) (hQ : Q * Q = Q) (h_comm : P * Q = Q * P) :
    toeplitzOp P Q - toeplitzOp P Q * toeplitzOp P Q = 0 := by
  dsimp [toeplitzOp]
  calc P * Q * P - P * Q * P * (P * Q * P)
    _ = P * Q * P - P * Q * (P * P) * Q * P := by noncomm_ring
    _ = P * Q * P - P * Q * (P * Q) * P := by rw [hP]; noncomm_ring
    _ = P * Q * P - P * (Q * Q) * (P * P) := by rw [h_comm]; noncomm_ring
    _ = P * Q * P - P * Q * P := by rw [hQ, hP]
    _ = 0 := sub_self _

def P_plus {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 0
def Q_had  {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B := mat2 1 1 1 1

theorem cm2_noncomm_fup_variance {B : Type*} [Ring B] :
    2 • toeplitzOp (P_plus : Matrix (Fin 2) (Fin 2) B) Q_had -
    toeplitzOp P_plus Q_had * toeplitzOp P_plus Q_had = P_plus := by
  apply ext_fin2 <;> simp [toeplitzOp, P_plus, Q_had, two_smul]

end CM2_FractalUncertainty

/-!
## $\mathcal{C}\mathcal{M}_3$: Quaternion Braid Curvature vs. Abelian Collapse
-/

section CM3_BraidCurvature

def constCurvature {B : Type*} [Ring B] (A₁ A₂ : B) : B := A₁ * A₂ - A₂ * A₁

theorem cm3_abelian_curvature_collapse {B : Type*} [Ring B] (A₁ A₂ : B)
    (h_comm : A₁ * A₂ = A₂ * A₁) :
    constCurvature A₁ A₂ = 0 := by
  dsimp [constCurvature]; rw [h_comm, sub_self]

abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ
abbrev M4Z := Matrix (Fin 2) (Fin 2) M2Z

def I₂ : M2Z := mat2 1 0 0 1
def Z₂ : M2Z := mat2 1 0 0 (-1)
def X₂ : M2Z := mat2 0 1 1 0
def J₂ : M2Z := mat2 0 (-1) 1 0

def E₁ : M4Z := mat2 0 Z₂ (-Z₂) 0
def E₂ : M4Z := mat2 0 X₂ (-X₂) 0
def E₃ : M4Z := mat2 J₂ 0 0 (-J₂)

theorem cm3_quaternion_braid_curvature :
    constCurvature E₁ E₂ = 2 • E₃ := by
  apply ext_fin2 <;> apply ext_fin2 <;>
    simp [constCurvature, E₁, E₂, E₃, Z₂, X₂, J₂, two_smul]

end CM3_BraidCurvature

/-!
## $\mathcal{C}\mathcal{M}_4$: Noncommutative Cayley–Hamilton Obstruction ($\mathfrak{sl}_2$ Lie Cross-Product)
-/

section CM4_NoncommCayleyHamilton

/-- **Repaired Noncommutative Cayley–Hamilton Obstruction**:
For $M = \bigl(\begin{smallmatrix} a & b \\ c & -a \end{smallmatrix}\bigr)$ over any noncommutative `[Ring B]`,
$M^2 = (a^2 + b c) I_2 + \bigl(\begin{smallmatrix} 0 & \⁅a, b⁆ \\ \⁅c, a⁆ & \⁅c, b⁆ \end{smallmatrix}\bigr)$. -/
theorem cm4_noncomm_cayley_hamilton_obstruction {B : Type*} [Ring B] (a b c : B) :
    let M : Matrix (Fin 2) (Fin 2) B := mat2 a b c (-a)
    M * M = mat2 (a * a + b * c) 0 0 (a * a + b * c) +
            mat2 0 ⁅a, b⁆ ⁅c, a⁆ ⁅c, b⁆ := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp <;> noncomm_ring

end CM4_NoncommCayleyHamilton

/-!
## $\mathcal{C}\mathcal{M}_5$: The Córdova–Freed–Teleman Dichotomy in $M_2(M_2(\mathbb{Z}))$
-/

section CM5_CFTDichotomy

open CM3_BraidCurvature

def A_torsion : M4Z := mat2 0 (-I₂) I₂ 0
def X_witt_4  : M4Z := mat2 0 (1 - F_plus) (1 + F_plus) 0
def Q_par_4   : M4Z := mat2 CM1_WilsonCocycle.Q_par 0 0 CM1_WilsonCocycle.Q_par

theorem cm5_orthogonal_torsion_orthogonal :
    A_torsionᵀ * A_torsion = 1 := by
  apply ext_fin2 <;> apply ext_fin2 <;> simp [A_torsion, I₂]

theorem cm5_orthogonal_torsion_order_four :
    A_torsion ^ 2 = -1 ∧ A_torsion ^ 4 = 1 := by
  have h2 : A_torsion ^ 2 = -1 := by
    rw [sq]
    apply ext_fin2 <;> apply ext_fin2 <;> simp [A_torsion, I₂]
  refine ⟨h2, ?_⟩
  calc A_torsion ^ 4
    _ = (A_torsion ^ 2) * (A_torsion ^ 2) := by noncomm_ring
    _ = (-1) * (-1) := by rw [h2]
    _ = 1 := by noncomm_ring

theorem cm5_nonorthogonal_witt_infinite_order (n : ℕ) (hn : 1 ≤ n) :
    X_witt_4ᵀ * X_witt_4 ≠ 1 ∧ (Q_par_4 : M4Z) ^ n ≠ 1 := by
  refine ⟨by decide, ?_⟩
  have h_pow : ∀ k : ℕ, (Q_par_4 : M4Z) ^ k =
      mat2 (CM1_WilsonCocycle.Q_par ^ k) 0 0 (CM1_WilsonCocycle.Q_par ^ k) := by
    intro k; induction' k with k ih
    · apply ext_fin2 <;> apply ext_fin2 <;> rfl
    · rw [pow_succ, ih, pow_succ]
      apply ext_fin2 <;> simp [Q_par_4]
  intro h_eq
  have h_entry : (((Q_par_4 : M4Z) ^ n) 0 0) 1 0 = ((1 : M4Z) 0 0) 1 0 := by rw [h_eq]
  rw [h_pow n, CM1_WilsonCocycle.cm1_Q_par_pow n] at h_entry
  simp [CM1_WilsonCocycle.N_par] at h_entry
  omega

end CM5_CFTDichotomy

/-!
## $\mathcal{C}\mathcal{M}_6$: Inductive Bott–Clifford Tower Lifting of the Parabolic Monodromy (`ClTower n B`)
-/

section CM6_InductiveTowerParabolicColimit

universe u

def ClTower : ℕ → Type u → Type u
  | 0, B     => B
  | n + 1, B => Matrix (Fin 2) (Fin 2) (ClTower n B)

instance instRingClTower {B : Type u} [Ring B] : ∀ n : ℕ, Ring (ClTower n B)
  | 0     => inferInstanceAs (Ring B)
  | n + 1 => by
      letI : Ring (ClTower n B) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower n B)))

variable {B : Type u} [Ring B]

/-- Inductive tower lift of the shift involution $\Sigma^{(n)} \in \mathcal{C}\ell_{n+1}(B)$. -/
def sigmaTower : ∀ n : ℕ, ClTower (n + 1) B
  | 0     => sigmaOp
  | n + 1 => mat2 (sigmaTower n) 0 0 (sigmaTower n)

/-- Inductive tower lift of the light-cone nilpotent generator $N_{\mathrm{par}}^{(n)} \in \mathcal{C}\ell_{n+1}(B)$. -/
def nilpotentTower : ∀ n : ℕ, ClTower (n + 1) B
  | 0     => CM1_WilsonCocycle.N_par
  | n + 1 => mat2 (nilpotentTower n) 0 0 (nilpotentTower n)

/-- Inductive tower parabolic monodromy $Q_{\mathrm{par}}^{(n)} = 1 + N_{\mathrm{par}}^{(n)} \in \mathcal{C}\ell_{n+1}(B)$. -/
def monodromyTower (n : ℕ) : ClTower (n + 1) B :=
  1 + nilpotentTower n

/-- Top-left corner projection functor $\pi_{00}^{(n)} : \mathcal{C}\ell_{n+1}(B) \to M_2(B)$. -/
def corner00 : ∀ n : ℕ, ClTower (n + 1) B → Matrix (Fin 2) (Fin 2) B
  | 0, M     => M
  | n + 1, M => corner00 n (M 0 0)

theorem nilpotentTower_sq : ∀ n : ℕ,
    (nilpotentTower n : ClTower (n + 1) B) * nilpotentTower n = 0
  | 0     => CM1_WilsonCocycle.cm1_N_par_nilpotent_and_anticomm.2.1
  | n + 1 => by apply ext_fin2 <;> simp [nilpotentTower, nilpotentTower_sq n]

theorem sigmaTower_sq : ∀ n : ℕ,
    (sigmaTower n : ClTower (n + 1) B) * sigmaTower n = 1
  | 0     => CM1_WilsonCocycle.cm1_sigmaOp_involution
  | n + 1 => by apply ext_fin2 <;> simp [sigmaTower, sigmaTower_sq n]

theorem sigmaTower_conj_nilpotent : ∀ n : ℕ,
    (sigmaTower n : ClTower (n + 1) B) * nilpotentTower n * sigmaTower n = -nilpotentTower n
  | 0     => CM1_WilsonCocycle.cm1_N_par_nilpotent_and_anticomm.2.2
  | n + 1 => by apply ext_fin2 <;> simp [sigmaTower, nilpotentTower, sigmaTower_conj_nilpotent n]

theorem corner00_one_add_nsmul_nilpotent : ∀ (n k : ℕ),
    corner00 n ((1 : ClTower (n + 1) B) + k • nilpotentTower n) =
      1 + k • CM1_WilsonCocycle.N_par
  | 0, _     => rfl
  | n + 1, k => by
      dsimp [corner00, nilpotentTower]
      exact corner00_one_add_nsmul_nilpotent n k

/-- **All-Scales Inductive Bott–Clifford Tower Parabolic Monodromy Theorem ($\mathcal{C}\mathcal{M}_6$)**:
At every level $n \in \mathbb{N}$ of the inductive tower $\mathcal{C}\ell_{n+1}(B)$:
1. $\mathcal{W}_{\Sigma^{(n)}}^{(2)}(Q_{\mathrm{par}}^{(n)}) = 1$ (2-step Wilson cocycle closure),
2. $(Q_{\mathrm{par}}^{(n)})^k = 1 + k \bullet N_{\mathrm{par}}^{(n)}$ for all $k \in \mathbb{N}$,
3. Over any `[CharZero B]`, $(Q_{\mathrm{par}}^{(n)})^k \neq 1$ for all $k > 0$. -/
theorem all_scales_tower_parabolic_monodromy [CharZero B] (n k : ℕ) (hk : 0 < k) :
    CM1_WilsonCocycle.wilsonCocycle
      (sigmaTower n : ClTower (n + 1) B) (sigmaTower n) (monodromyTower n) 2 = 1 ∧
    (monodromyTower n : ClTower (n + 1) B) ^ k = 1 + k • nilpotentTower n ∧
    (monodromyTower n : ClTower (n + 1) B) ^ k ≠ 1 := by
  have hPow : ∀ m : ℕ, (monodromyTower n : ClTower (n + 1) B) ^ m = 1 + m • nilpotentTower n := by
    intro m; induction' m with m ih
    · simp
    · rw [pow_succ, ih, monodromyTower, add_nsmul, one_nsmul]
      have h_mul : (m • (nilpotentTower n : ClTower (n + 1) B)) * nilpotentTower n = 0 := by
        rw [nsmul_eq_mul, mul_assoc, nilpotentTower_sq n, mul_zero]
      calc (1 + m • (nilpotentTower n : ClTower (n + 1) B)) * (1 + nilpotentTower n)
        _ = 1 + (m • nilpotentTower n + nilpotentTower n) +
            (m • nilpotentTower n) * nilpotentTower n := by noncomm_ring
        _ = 1 + (m • nilpotentTower n + nilpotentTower n) := by rw [h_mul, add_zero]
  refine ⟨?_, hPow k, ?_⟩
  · dsimp [CM1_WilsonCocycle.wilsonCocycle, monodromyTower]
    calc (1 + (nilpotentTower n : ClTower (n + 1) B)) *
          (sigmaTower n * ((1 + nilpotentTower n) * (sigmaTower n * 1 * sigmaTower n)) * sigmaTower n)
      _ = (1 + nilpotentTower n) *
          (sigmaTower n * ((1 + nilpotentTower n) * 1) * sigmaTower n) := by
          rw [mul_one, sigmaTower_sq n]
      _ = (1 + nilpotentTower n) *
          (sigmaTower n * sigmaTower n + sigmaTower n * nilpotentTower n * sigmaTower n) := by
          noncomm_ring
      _ = (1 + nilpotentTower n) * (1 + -nilpotentTower n) := by
          rw [sigmaTower_sq n, sigmaTower_conj_nilpotent n]
      _ = 1 - nilpotentTower n * nilpotentTower n := by noncomm_ring
      _ = 1 := by rw [nilpotentTower_sq n, sub_zero]
  · intro h_eq
    have h_c : (corner00 n ((monodromyTower n : ClTower (n + 1) B) ^ k)) 1 0 =
               (corner00 n (1 : ClTower (n + 1) B)) 1 0 := by rw [h_eq]
    rw [hPow k, corner00_one_add_nsmul_nilpotent n k] at h_c
    have h_zero : (corner00 n (1 : ClTower (n + 1) B)) 1 0 = 0 := by
      induction' n with m ih
      · rfl
      · exact ih
    rw [h_zero] at h_c
    simp [CM1_WilsonCocycle.N_par] at h_c
    exact Nat.ne_of_gt hk h_c

end CM6_InductiveTowerParabolicColimit

/-!
## $\mathcal{C}\mathcal{M}_7$: Córdova–Freed–Teleman Proposition 22 (`r • B_gerbe = -Tr_r(F(A))`) & Page 6 Gerbe Flatness over `[Ring B]`
-/

section CM7_CordovaFreedTelemanProposition22

variable {B : Type*} [Ring B]

def IsRingDeriv (d : B →+ B) : Prop :=
  ∀ a b : B, d (a * b) = d a * b + a * d b

def liftMatrixDeriv {r : ℕ} (d : B →+ B) :
    Matrix (Fin r) (Fin r) B →+ Matrix (Fin r) (Fin r) B where
  toFun M i j := d (M i j)
  map_zero' := by ext i j; simp
  map_add' M N := by ext i j; simp

def mcCurvature {R : Type*} [Ring R] (d₁ d₂ : R →+ R) (A₁ A₂ : R) : R :=
  d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆

def adjDeriv {R : Type*} [Ring R] (d : R →+ R) (A X : R) : R :=
  d X + ⁅A, X⁆

def gerbeEmbed (r : ℕ) (b : B) : Matrix (Fin r) (Fin r) B :=
  Matrix.of (fun i j => if i = j then b else 0)

def ncTrace {r : ℕ} (M : Matrix (Fin r) (Fin r) B) : B :=
  ∑ i : Fin r, M i i

def twistedBundleCurvature {r : ℕ}
    (d₁ d₂ : B →+ B) (A₁ A₂ : Matrix (Fin r) (Fin r) B) (B_gerbe : B) :
    Matrix (Fin r) (Fin r) B :=
  mcCurvature (liftMatrixDeriv d₁) (liftMatrixDeriv d₂) A₁ A₂ + gerbeEmbed r B_gerbe

theorem ncTrace_gerbeEmbed (r : ℕ) (b : B) :
    ncTrace (gerbeEmbed r b) = r • b := by
  dsimp [ncTrace, gerbeEmbed]; simp [Finset.sum_const, Finset.card_fin]

/-- **Proposition 22 & Page 6 Theorem of Córdova–Freed–Teleman (`arXiv:2408.15148`) over `[Ring B]` ($\mathcal{C}\mathcal{M}_7$)**:
1. *Proposition 22*: If a rank-$r$ twisted bundle is projectively flat ($\Omega_E = 0$), then
   $r \bullet B_{\mathrm{gerbe}} = -\big(d_1(\mathrm{Tr}_r A_2) - d_2(\mathrm{Tr}_r A_1) + \mathrm{Tr}_r\⁅A_1, A_2⁆\big)$.
2. *Page 6 Bianchi Reduction*: If $F_{ij} + B_{ij} = 0$ with central curving $\⁅A_k, B_{ij}⁆ = 0$
   under commuting derivations $d_1, d_2, d_3$, then $d_1 B_{23} + d_2 B_{31} + d_3 B_{12} = 0$. -/
theorem cordova_freed_teleman_proposition22_and_gerbe_flatness
    {r : ℕ} {d₁ d₂ d₃ : B →+ B}
    (hd₁ : IsRingDeriv d₁) (hd₂ : IsRingDeriv d₂) (hd₃ : IsRingDeriv d₃)
    (h12 : ∀ x : B, d₁ (d₂ x) = d₂ (d₁ x))
    (h23 : ∀ x : B, d₂ (d₃ x) = d₃ (d₂ x))
    (h13 : ∀ x : B, d₁ (d₃ x) = d₃ (d₁ x))
    (A₁_mat A₂_mat : Matrix (Fin r) (Fin r) B) (B_gerbe : B)
    (h_flat : twistedBundleCurvature d₁ d₂ A₁_mat A₂_mat B_gerbe = 0)
    {A₁ A₂ A₃ B₂₃ B₃₁ B₁₂ : B}
    (h_flat₂₃ : mcCurvature d₂ d₃ A₂ A₃ + B₂₃ = 0)
    (h_flat₃₁ : mcCurvature d₃ d₁ A₃ A₁ + B₃₁ = 0)
    (h_flat₁₂ : mcCurvature d₁ d₂ A₁ A₂ + B₁₂ = 0)
    (h_comm₁ : ⁅A₁, B₂₃⁆ = 0) (h_comm₂ : ⁅A₂, B₃₁⁆ = 0) (h_comm₃ : ⁅A₃, B₁₂⁆ = 0) :
    r • B_gerbe = -(d₁ (ncTrace A₂_mat) - d₂ (ncTrace A₁_mat) + ncTrace ⁅A₁_mat, A₂_mat⁆) ∧
    d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂ = 0 := by
  refine ⟨?_, ?_⟩
  · have h_tr : ncTrace (twistedBundleCurvature d₁ d₂ A₁_mat A₂_mat B_gerbe) = 0 := by
      rw [h_flat]; dsimp [ncTrace]; simp
    have h_decomp : ncTrace (twistedBundleCurvature d₁ d₂ A₁_mat A₂_mat B_gerbe) =
        (d₁ (ncTrace A₂_mat) - d₂ (ncTrace A₁_mat) + ncTrace ⁅A₁_mat, A₂_mat⁆) + r • B_gerbe := by
      dsimp [twistedBundleCurvature, mcCurvature, ncTrace, liftMatrixDeriv]
      simp only [Matrix.add_apply, Matrix.sub_apply, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, map_sum, ← ncTrace_gerbeEmbed r B_gerbe]
      rfl
    rw [h_decomp] at h_tr
    exact eq_neg_of_add_eq_zero_right h_tr
  · have h_bianchi :
        adjDeriv d₁ A₁ (mcCurvature d₂ d₃ A₂ A₃) +
        adjDeriv d₂ A₂ (mcCurvature d₃ d₁ A₃ A₁) +
        adjDeriv d₃ A₃ (mcCurvature d₁ d₂ A₁ A₂) = 0 := by
      dsimp [adjDeriv, mcCurvature]
      simp only [Ring.lie_def, map_add, map_sub]
      rw [hd₁ A₂ A₃, hd₁ A₃ A₂, hd₂ A₃ A₁, hd₂ A₁ A₃, hd₃ A₁ A₂, hd₃ A₂ A₁,
          h12 A₃, h13 A₂, h23 A₁, ← h12 A₃, ← h13 A₂, ← h23 A₁]
      noncomm_ring
    have hF₂₃ : mcCurvature d₂ d₃ A₂ A₃ = -B₂₃ := eq_neg_of_add_eq_zero_left h_flat₂₃
    have hF₃₁ : mcCurvature d₃ d₁ A₃ A₁ = -B₃₁ := eq_neg_of_add_eq_zero_left h_flat₃₁
    have hF₁₂ : mcCurvature d₁ d₂ A₁ A₂ = -B₁₂ := eq_neg_of_add_eq_zero_left h_flat₁₂
    rw [hF₂₃, hF₃₁, hF₁₂] at h_bianchi
    dsimp [adjDeriv] at h_bianchi
    simp only [map_neg] at h_bianchi
    have hc₁ : ⁅A₁, -B₂₃⁆ = 0 := by rw [Ring.lie_def] at h_comm₁ ⊢; noncomm_ring [h_comm₁]
    have hc₂ : ⁅A₂, -B₃₁⁆ = 0 := by rw [Ring.lie_def] at h_comm₂ ⊢; noncomm_ring [h_comm₂]
    have hc₃ : ⁅A₃, -B₁₂⁆ = 0 := by rw [Ring.lie_def] at h_comm₃ ⊢; noncomm_ring [h_comm₃]
    rw [hc₁, hc₂, hc₃, add_zero, add_zero, add_zero] at h_bianchi
    calc d₁ B₂₃ + d₂ B₃₁ + d₃ B₁₂
      _ = -(-d₁ B₂₃ + -d₂ B₃₁ + -d₃ B₁₂) := by abel
      _ = -0 := by rw [h_bianchi]
      _ = 0 := neg_zero

end CM7_CordovaFreedTelemanProposition22

end NoncommutativeContrastPoset
```

## Turn 0060, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeColimitAndSpectralGapSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

end Matrix2Simp

/-!
## Inductive Tower `ClTower A n` & Core Operators
-/

universe u

def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      letI : StarRing (ClTower A n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorProj n) 0 0 0

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def cayleyTowerOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cayleyTowerOp n) (-cayleyTowerOp n) (cayleyTowerOp n) (cayleyTowerOp n)

def rgTowerDecimate (n : ℕ) (M : ClTower A (n + 1)) : ClTower A n :=
  M 0 0 + M 1 1

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by dsimp [towerTrace]; rw [Matrix.zero_apply, Matrix.zero_apply, towerTrace_zero n, add_zero]

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      rw [Matrix.neg_apply, Matrix.neg_apply, towerTrace_neg, towerTrace_neg]
      abel

lemma cantorProj_idempotent : ∀ (n : ℕ),
    (cantorProj n : ClTower A n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_idempotent n]

/-!
## Archetype $\mathcal{M}\mathcal{G}_1$ & $\mathcal{M}\mathcal{G}_2$: Directed Inductive System & Universal Colimit Cocone of $\mathcal{C}\ell(\infty, \infty)$
-/

section ArchetypeMG1_MG2_InductiveColimitCocone

/-- Infrared / vacuum corner transition homomorphism $\iota_{\mathrm{Cantor}}^{(n)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+1}(A)$. -/
def cantorEmbed (n : ℕ) (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

/-- Bulk diagonal transition homomorphism $\iota_{\mathrm{diag}}^{(n)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+1}(A)$. -/
def diagEmbed (n : ℕ) (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 X

/-- Multi-step directed transition functor $\iota_{\mathrm{Cantor}}^{(n, n+k)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+k}(A)$. -/
def cantorEmbedIter (n : ℕ) : ∀ (k : ℕ), ClTower A n → ClTower A (n + k)
  | 0,     X => X
  | k + 1, X => cantorEmbed (n + k) (cantorEmbedIter n k X)

theorem towerTrace_cantorEmbed (n : ℕ) (X : ClTower A n) :
    towerTrace (cantorEmbed n X) = towerTrace X := by
  dsimp [towerTrace, cantorEmbed]
  rw [mat2_00, mat2_11, towerTrace_zero n, add_zero]

theorem superTrace_cantorEmbed (n : ℕ) (X : ClTower A n) :
    superTrace (cantorEmbed n X) = superTrace X := by
  dsimp [superTrace, cantorEmbed, chiralityOp, towerTrace]
  simp [towerTrace_zero n]

/-- **Universal Colimit Cocone & Inter-Scale Duality Theorem ($\mathcal{M}\mathcal{G}_1$ & $\mathcal{M}\mathcal{G}_2$)**:
1. $\iota_{\mathrm{Cantor}}^{(n)}$ is a multiplicative homomorphism mapping $\Pi_{\mathcal{C}_n} \mapsto \Pi_{\mathcal{C}_{n+1}}$,
2. RG block decimation $\mathcal{R}_{\mathrm{RG}}^{(n)}$ is an exact retraction: $\mathcal{R}_{\mathrm{RG}}^{(n)}(\iota_{\mathrm{Cantor}}^{(n)}(X)) = X$,
3. The bulk diagonal embedding $\iota_{\mathrm{diag}}^{(n)}$ is annihilated by $\mathrm{Str}_{2^{n+1}}$,
4. Multi-step directed transitions $\iota_{\mathrm{Cantor}}^{(n, n+k)}$ strictly preserve both
   $\mathrm{Tr}_{2^n}$ and $\mathrm{Str}_{2^n}$ across all $n, k \in \mathbb{N}$. -/
theorem colimit_cocone_trace_and_supertrace_invariance
    (n k : ℕ) (X Y : ClTower A n) :
    cantorEmbed n (X * Y) = cantorEmbed n X * cantorEmbed n Y ∧
    cantorEmbed n (cantorProj n) = cantorProj (n + 1) ∧
    rgTowerDecimate n (cantorEmbed n X) = X ∧
    superTrace (diagEmbed n X) = 0 ∧
    towerTrace (cantorEmbedIter n k X) = towerTrace X ∧
    superTrace (cantorEmbedIter n k X) = superTrace X := by
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [cantorEmbed]
  · dsimp [rgTowerDecimate, cantorEmbed]; simp
  · dsimp [superTrace, diagEmbed, chiralityOp, towerTrace]
    simp [neg_mul, towerTrace_neg]
  · induction' k with m ih
    · rfl
    · dsimp [cantorEmbedIter]
      rw [towerTrace_cantorEmbed (n + m), ih]
  · induction' k with m ih
    · rfl
    · dsimp [cantorEmbedIter]
      rw [superTrace_cantorEmbed (n + m), ih]

end ArchetypeMG1_MG2_InductiveColimitCocone

/-!
## Archetype $\mathcal{M}\mathcal{G}_3$: All-Scales Hodge–Witten Laplacian $\Delta_{n+1} = (d_n + \delta_n)^2$
-/

section ArchetypeMG3_AllScalesHodgeLaplacian

def wittD (n : ℕ) : ClTower A (n + 1) := mat2 0 (cantorProj n) 0 0
def wittDelta (n : ℕ) : ClTower A (n + 1) := mat2 0 0 (cantorProj n) 0

/-- The $(n+1)$-scale Hodge–Witten Laplacian $\Delta_{n+1} = (d_n + \delta_n)^2 \in \mathcal{C}\ell_{n+1}(A)$. -/
def hodgeLaplacian (n : ℕ) : ClTower A (n + 1) :=
  (wittD n + wittDelta n) * (wittD n + wittDelta n)

/-- **All-Scales Hodge–Witten Laplacian Spectral Gap Theorem ($\mathcal{M}\mathcal{G}_3$)**:
At every scale $n \in \mathbb{N}$:
1. $\Delta_{n+1} = d_n \delta_n + \delta_n d_n = \mathrm{diag}(\Pi_{\mathcal{C}_n}, \Pi_{\mathcal{C}_n})$,
2. $\Delta_{n+1}^2 = \Delta_{n+1}$ (discrete $\{0, 1\}$ spectrum with unit spectral gap),
3. $\Delta_{n+1} \Pi_{\mathcal{C}_{n+1}} = \Pi_{\mathcal{C}_{n+1}}$ and $\Delta_{n+1}(1 - \Delta_{n+1}) = 0$. -/
theorem all_scales_hodge_laplacian_spectral_gap (n : ℕ) :
    hodgeLaplacian (A := A) n = wittD n * wittDelta n + wittDelta n * wittD n ∧
    hodgeLaplacian (A := A) n = mat2 (cantorProj n) 0 0 (cantorProj n) ∧
    hodgeLaplacian (A := A) n * hodgeLaplacian n = hodgeLaplacian n ∧
    hodgeLaplacian (A := A) n * cantorProj (n + 1) = cantorProj (n + 1) ∧
    hodgeLaplacian (A := A) n * (1 - hodgeLaplacian n) = 0 := by
  have h_idem := cantorProj_idempotent (A := A) n
  have h_mat : hodgeLaplacian (A := A) n = mat2 (cantorProj n) 0 0 (cantorProj n) := by
    apply ext_fin2 <;> simp [hodgeLaplacian, wittD, wittDelta, h_idem]
  have h_sq : hodgeLaplacian (A := A) n * hodgeLaplacian n = hodgeLaplacian n := by
    rw [h_mat]; apply ext_fin2 <;> simp [h_idem]
  refine ⟨?_, h_mat, h_sq, ?_, ?_⟩
  · apply ext_fin2 <;> simp [hodgeLaplacian, wittD, wittDelta, h_idem]
  · rw [h_mat]; apply ext_fin2 <;> simp [cantorProj, h_idem]
  · calc hodgeLaplacian (A := A) n * (1 - hodgeLaplacian n)
      _ = hodgeLaplacian n - hodgeLaplacian n * hodgeLaplacian n := by noncomm_ring
      _ = 0 := by rw [h_sq, sub_self]

end ArchetypeMG3_AllScalesHodgeLaplacian

/-!
## Archetype $\mathcal{M}\mathcal{G}_4$: All-Scales Spectral Mass Gap Hamiltonian & $(2^n - 1)$ Excited Pore FUP Law
-/

section ArchetypeMG4_SpectralMassGapAndExcitedPoreFUP

variable [StarRing A]

/-- All-scales gapped Hamiltonian $H_{\mathrm{YM}}^{(n)}(\mu, \lambda) = \mu \bullet 1 + \lambda \bullet (1 - \Pi_{\mathcal{C}_n})$. -/
def massGapHamiltonian (n : ℕ) (μ λ : ℕ) : ClTower A n :=
  μ • (1 : ClTower A n) + λ • (1 - cantorProj n)

lemma cantorProj_sa_and_cayley_fup (n : ℕ) :
    star (cantorProj n : ClTower A n) = cantorProj n ∧
    star (cayleyTowerOp n : ClTower A n) * cayleyTowerOp n = (2 ^ n) • (1 : ClTower A n) ∧
    (cantorProj n : ClTower A n) * cayleyTowerOp n * cantorProj n = cantorProj n := by
  induction' n with k ih
  · simp [cantorProj, cayleyTowerOp]
  · rcases ih with ⟨ih_sa, ih_unit, ih_comp⟩
    refine ⟨?_, ?_, ?_⟩
    · apply ext_fin2 <;> simp [cantorProj, ih_sa]
    · apply ext_fin2
      · simp [cayleyTowerOp, ih_unit, pow_succ', two_mul, add_nsmul]
      · simp [cayleyTowerOp]
      · simp [cayleyTowerOp]
      · simp [cayleyTowerOp, ih_unit, pow_succ', two_mul, add_nsmul]
    · apply ext_fin2 <;> simp [cantorProj, cayleyTowerOp, ih_comp]

/-- **All-Scales Spectral Mass Gap & $(2^n - 1)$ Excited Pore FUP Theorem ($\mathcal{M}\mathcal{G}_4$)**:
For every scale $n \in \mathbb{N}$ and mass parameters $\mu, \lambda \in \mathbb{N}$:
1. $H_{\mathrm{YM}}^{(n)}(\mu, \lambda)\,\Pi_{\mathcal{C}_n} = \mu \bullet \Pi_{\mathcal{C}_n}$ (vacuum mass $\mu$) and
   $H_{\mathrm{YM}}^{(n)}(\mu, \lambda)\,(1 - \Pi_{\mathcal{C}_n}) = (\mu + \lambda) \bullet (1 - \Pi_{\mathcal{C}_n})$ (excited mass $\mu + \lambda$),
2. $(H_{\mathrm{YM}}^{(n)}(\mu, \lambda) - \mu \bullet 1)(H_{\mathrm{YM}}^{(n)}(\mu, \lambda) - (\mu + \lambda) \bullet 1) = 0$,
3. *Positive-Cone Mass Gap Lower Bound*:
   $(H_{\mathrm{YM}}^{(n)})^\star H_{\mathrm{YM}}^{(n)} - (\mu^2) \bullet 1 = (2\mu\lambda + \lambda^2) \bullet ((1 - \Pi_{\mathcal{C}_n})^\star (1 - \Pi_{\mathcal{C}_n}))$,
4. *All-Scales $(2^n - 1)$ Excited Pore FUP Energy Law*:
   $((1 - \Pi_{\mathcal{C}_n})\,\mathcal{U}_n\,\Pi_{\mathcal{C}_n})^\star ((1 - \Pi_{\mathcal{C}_n})\,\mathcal{U}_n\,\Pi_{\mathcal{C}_n}) = (2^n - 1) \bullet \Pi_{\mathcal{C}_n}$. -/
theorem all_scales_mass_gap_hamiltonian_and_excited_pore_fup (n μ λ : ℕ) :
    let P_n := (cantorProj n : ClTower A n)
    let Q_n := 1 - P_n
    let H_n := massGapHamiltonian (A := A) n μ λ
    let U_n := (cayleyTowerOp n : ClTower A n)
    H_n * P_n = μ • P_n ∧
    H_n * Q_n = (μ + λ) • Q_n ∧
    (H_n - μ • 1) * (H_n - (μ + λ) • 1) = 0 ∧
    star H_n * H_n - (μ * μ) • (1 : ClTower A n) =
      (2 * μ * λ + λ * λ) • (star Q_n * Q_n) ∧
    star (Q_n * U_n * P_n) * (Q_n * U_n * P_n) = (2 ^ n - 1) • P_n := by
  intro P_n Q_n H_n U_n
  have hP_idem : P_n * P_n = P_n := cantorProj_idempotent n
  rcases cantorProj_sa_and_cayley_fup (A := A) n with ⟨hP_sa, hU_unit, h_comp⟩
  have hQ_idem : Q_n * Q_n = Q_n := by
    dsimp [Q_n]
    calc (1 - P_n) * (1 - P_n) = 1 - P_n - P_n + P_n * P_n := by noncomm_ring
      _ = 1 - P_n := by rw [hP_idem]; noncomm_ring
  have hQ_sa : star Q_n = Q_n := by
    dsimp [Q_n]; rw [star_sub, star_one, hP_sa]
  have hQP : Q_n * P_n = 0 := by
    dsimp [Q_n]
    calc (1 - P_n) * P_n = P_n - P_n * P_n := by noncomm_ring
      _ = 0 := by rw [hP_idem, sub_self]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [H_n, massGapHamiltonian]
    rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    calc (↑μ * 1 + ↑λ * Q_n) * P_n = ↑μ * P_n + ↑λ * (Q_n * P_n) := by noncomm_ring
      _ = ↑μ * P_n := by rw [hQP]; noncomm_ring
  · dsimp [H_n, massGapHamiltonian]
    rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_add]
    calc (↑μ * 1 + ↑λ * Q_n) * Q_n = ↑μ * Q_n + ↑λ * (Q_n * Q_n) := by noncomm_ring
      _ = (↑μ + ↑λ) * Q_n := by rw [hQ_idem]; noncomm_ring
  · dsimp [H_n, massGapHamiltonian]
    rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_add]
    calc (↑μ * 1 + ↑λ * Q_n - ↑μ * 1) * (↑μ * 1 + ↑λ * Q_n - (↑μ + ↑λ) * 1)
      _ = (↑λ * ↑λ) * (Q_n * Q_n - Q_n) := by noncomm_ring
      _ = 0 := by rw [hQ_idem, sub_self, mul_zero]
  · have hH_sa : star H_n = H_n := by
      dsimp [H_n, massGapHamiltonian]
      rw [star_add, star_nsmul, star_nsmul, star_one, hQ_sa]
    rw [hH_sa, hQ_sa]
    dsimp [H_n, massGapHamiltonian]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    calc (↑μ * 1 + ↑λ * Q_n) * (↑μ * 1 + ↑λ * Q_n) - ↑μ * ↑μ * 1
      _ = 2 * ↑μ * ↑λ * Q_n + ↑λ * ↑λ * (Q_n * Q_n) := by noncomm_ring
      _ = (2 * ↑μ * ↑λ + ↑λ * ↑λ) * (Q_n * Q_n) := by rw [hQ_idem]; noncomm_ring
  · have h_full : star (U_n * P_n) * (U_n * P_n) = (2 ^ n) • P_n := by
      calc star (U_n * P_n) * (U_n * P_n)
        _ = P_n * (star U_n * U_n) * P_n := by simp only [star_mul, hP_sa]; noncomm_ring
        _ = P_n * ((2 ^ n) • 1) * P_n := by rw [hU_unit]
        _ = (2 ^ n) • (P_n * P_n) := by rw [nsmul_eq_mul, nsmul_eq_mul]; noncomm_ring
        _ = (2 ^ n) • P_n := by rw [hP_idem]
    have h_part : star (Q_n * U_n * P_n) * (Q_n * U_n * P_n) +
                  star (P_n * U_n * P_n) * (P_n * U_n * P_n) =
                  star (U_n * P_n) * (U_n * P_n) := by
      simp only [star_mul, hP_sa, hQ_sa]
      calc P_n * star U_n * (Q_n * Q_n) * U_n * P_n +
           P_n * star U_n * (P_n * P_n) * U_n * P_n
        _ = P_n * star U_n * (Q_n + P_n) * U_n * P_n := by rw [hQ_idem, hP_idem]; noncomm_ring
        _ = P_n * star U_n * 1 * U_n * P_n := by dsimp [Q_n]; rw [sub_add_cancel]
        _ = P_n * star U_n * (U_n * P_n) := by noncomm_ring
    rw [h_comp, hP_sa, hP_idem, h_full] at h_part
    have h_pow_split : (2 ^ n) • P_n = (2 ^ n - 1) • P_n + P_n := by
      have h_ge : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      calc (2 ^ n) • P_n = ((2 ^ n - 1) + 1) • P_n := by rw [Nat.sub_add_cancel h_ge]
        _ = (2 ^ n - 1) • P_n + P_n := by rw [add_nsmul, one_nsmul]
    rw [h_pow_split] at h_part
    exact add_right_cancel h_part

end ArchetypeMG4_SpectralMassGapAndExcitedPoreFUP

end NoncommutativeColimitAndSpectralGapSynthesis
```

## Turn 0063, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeColimitAndSpectralGapSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

end Matrix2Simp

/-!
## Inductive $\star$-Tower `ClTower A n` & Core Operators
-/

universe u

def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      letI : StarRing (ClTower A n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorProj n) 0 0 0

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def cayleyTowerOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cayleyTowerOp n) (-cayleyTowerOp n) (cayleyTowerOp n) (cayleyTowerOp n)

def rgTowerDecimate (n : ℕ) (M : ClTower A (n + 1)) : ClTower A n :=
  M 0 0 + M 1 1

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace]
      rw [Matrix.zero_apply, Matrix.zero_apply, towerTrace_zero n, add_zero]

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      rw [Matrix.neg_apply, Matrix.neg_apply, towerTrace_neg, towerTrace_neg]
      abel

lemma cantorProj_idempotent : ∀ (n : ℕ),
    (cantorProj n : ClTower A n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_idempotent n]

lemma cantorProj_selfAdjoint [StarRing A] : ∀ (n : ℕ),
    star (cantorProj n : ClTower A n) = cantorProj n
  | 0     => star_one A
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_selfAdjoint n]

lemma towerTrace_star [StarRing A] : ∀ {n : ℕ} (M : ClTower A n),
    towerTrace (star M) = star (towerTrace M)
  | 0,     _ => rfl
  | _ + 1, M => by
      dsimp [towerTrace]
      rw [star2_00, star2_11, towerTrace_star, towerTrace_star, star_add]

/-!
## Archetype $\mathcal{M}\mathcal{G}_1$ & $\mathcal{M}\mathcal{G}_2$: Directed $\star$-Inductive System & Universal Colimit Cocone of $\mathcal{C}\ell(\infty, \infty)$
-/

section ArchetypeMG1_MG2_InductiveColimitCocone

/-- Infrared / vacuum corner transition homomorphism $\iota_{\mathrm{Cantor}}^{(n)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+1}(A)$. -/
def cantorEmbed (n : ℕ) (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

/-- Bulk diagonal transition homomorphism $\iota_{\mathrm{diag}}^{(n)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+1}(A)$. -/
def diagEmbed (n : ℕ) (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 X

/-- Multi-step directed transition functor $\iota_{\mathrm{Cantor}}^{(n, n+k)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+k}(A)$. -/
def cantorEmbedIter (n : ℕ) : ∀ (k : ℕ), ClTower A n → ClTower A (n + k)
  | 0,     X => X
  | k + 1, X => cantorEmbed (n + k) (cantorEmbedIter n k X)

theorem towerTrace_cantorEmbed (n : ℕ) (X : ClTower A n) :
    towerTrace (cantorEmbed n X) = towerTrace X := by
  dsimp [towerTrace, cantorEmbed]
  rw [mat2_00, mat2_11, towerTrace_zero n, add_zero]

theorem superTrace_cantorEmbed (n : ℕ) (X : ClTower A n) :
    superTrace (cantorEmbed n X) = superTrace X := by
  dsimp [superTrace, cantorEmbed, chiralityOp, towerTrace]
  simp [towerTrace_zero n]

/-- **Universal $\star$-Colimit Cocone & Inter-Scale Duality Theorem ($\mathcal{M}\mathcal{G}_1$ & $\mathcal{M}\mathcal{G}_2$)**:
1. $\iota_{\mathrm{Cantor}}^{(n)}$ is a multiplicative $\star$-homomorphism mapping $\Pi_{\mathcal{C}_n} \mapsto \Pi_{\mathcal{C}_{n+1}}$,
2. RG block decimation $\mathcal{R}_{\mathrm{RG}}^{(n)}$ is an exact retraction: $\mathcal{R}_{\mathrm{RG}}^{(n)}(\iota_{\mathrm{Cantor}}^{(n)}(X)) = X$,
3. The bulk diagonal embedding $\iota_{\mathrm{diag}}^{(n)}$ is annihilated by $\mathrm{Str}_{2^{n+1}}$,
4. Multi-step directed transitions $\iota_{\mathrm{Cantor}}^{(n, n+k)}$ strictly preserve $\star$,
   $\mathrm{Tr}_{2^n}$, and $\mathrm{Str}_{2^n}$ across all $n, k \in \mathbb{N}$. -/
theorem colimit_cocone_star_trace_and_supertrace_invariance [StarRing A]
    (n k : ℕ) (X Y : ClTower A n) :
    cantorEmbed n (X * Y) = cantorEmbed n X * cantorEmbed n Y ∧
    star (cantorEmbed n X) = cantorEmbed n (star X) ∧
    cantorEmbed n (cantorProj n) = cantorProj (n + 1) ∧
    rgTowerDecimate n (cantorEmbed n X) = X ∧
    superTrace (diagEmbed n X) = 0 ∧
    towerTrace (cantorEmbedIter n k X) = towerTrace X ∧
    superTrace (cantorEmbedIter n k X) = superTrace X ∧
    towerTrace (star X) = star (towerTrace X) := by
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, towerTrace_star X⟩
  · apply ext_fin2 <;> simp [cantorEmbed]
  · apply ext_fin2 <;> simp [cantorEmbed]
  · dsimp [rgTowerDecimate, cantorEmbed]; simp
  · dsimp [superTrace, diagEmbed, chiralityOp, towerTrace]
    simp [neg_mul, towerTrace_neg]
  · induction' k with m ih
    · rfl
    · dsimp [cantorEmbedIter]
      rw [towerTrace_cantorEmbed (n + m), ih]
  · induction' k with m ih
    · rfl
    · dsimp [cantorEmbedIter]
      rw [superTrace_cantorEmbed (n + m), ih]

end ArchetypeMG1_MG2_InductiveColimitCocone

/-!
## Archetype $\mathcal{M}\mathcal{G}_3$: All-Scales $\star$-Adjoint Witt Differentials, Hodge Laplacian & Positive-Cone Energy Split
-/

section ArchetypeMG3_AllScalesHodgePositiveCone

def wittD (n : ℕ) : ClTower A (n + 1) := mat2 0 (cantorProj n) 0 0
def wittDelta (n : ℕ) : ClTower A (n + 1) := mat2 0 0 (cantorProj n) 0

/-- The $(n+1)$-scale Hodge–Witten Laplacian $\Delta_{n+1} = (d_n + \delta_n)^2 \in \mathcal{C}\ell_{n+1}(A)$. -/
def hodgeLaplacian (n : ℕ) : ClTower A (n + 1) :=
  (wittD n + wittDelta n) * (wittD n + wittDelta n)

/-- **All-Scales $\star$-Adjoint Witt Differentials & Positive-Cone Hodge Energy Split ($\mathcal{M}\mathcal{G}_3$)**:
At every scale $n \in \mathbb{N}$ over `[Ring A] [StarRing A]`:
1. $(d_n)^\star = \delta_n$ and $(\delta_n)^\star = d_n$,
2. $\Delta_{n+1} = d_n \delta_n + \delta_n d_n$ is a self-adjoint idempotent ($\Delta_{n+1}^2 = \Delta_{n+1} = \Delta_{n+1}^\star$),
3. $\Delta_{n+1} \Pi_{\mathcal{C}_{n+1}} = \Pi_{\mathcal{C}_{n+1}}$ and $\Delta_{n+1}(1 - \Delta_{n+1}) = 0$,
4. *Positive-Cone Energy Decomposition*: For any $\mathbb{X} \in \mathcal{C}\ell_{n+1}(A)$,
   $\mathbb{X}^\star \mathbb{X} = (\delta_n \mathbb{X})^\star(\delta_n \mathbb{X}) + (d_n \mathbb{X})^\star(d_n \mathbb{X}) + ((1 - \Delta_{n+1})\mathbb{X})^\star((1 - \Delta_{n+1})\mathbb{X})$. -/
theorem all_scales_hodge_laplacian_and_positive_cone_energy [StarRing A]
    (n : ℕ) (X : ClTower A (n + 1)) :
    let d_n   := (wittD n : ClTower A (n + 1))
    let del_n := (wittDelta n : ClTower A (n + 1))
    let Δ_n   := hodgeLaplacian (A := A) n
    star d_n = del_n ∧
    star del_n = d_n ∧
    Δ_n = d_n * del_n + del_n * d_n ∧
    Δ_n * Δ_n = Δ_n ∧
    star Δ_n = Δ_n ∧
    Δ_n * cantorProj (n + 1) = cantorProj (n + 1) ∧
    Δ_n * (1 - Δ_n) = 0 ∧
    star (del_n * X) * (del_n * X) +
    star (d_n * X) * (d_n * X) +
    star ((1 - Δ_n) * X) * ((1 - Δ_n) * X) = star X * X := by
  intro d_n del_n Δ_n
  have hP_idem := cantorProj_idempotent (A := A) n
  have hP_sa   := cantorProj_selfAdjoint (A := A) n
  have hd_star : star d_n = del_n := by
    apply ext_fin2 <;> simp [d_n, del_n, wittD, wittDelta, hP_sa]
  have hdel_star : star del_n = d_n := by
    apply ext_fin2 <;> simp [d_n, del_n, wittD, wittDelta, hP_sa]
  have h_mat : Δ_n = mat2 (cantorProj n) 0 0 (cantorProj n) := by
    apply ext_fin2 <;> simp [Δ_n, hodgeLaplacian, wittD, wittDelta, hP_idem]
  have h_sum : Δ_n = d_n * del_n + del_n * d_n := by
    rw [h_mat]; apply ext_fin2 <;> simp [d_n, del_n, wittD, wittDelta, hP_idem]
  have h_sq : Δ_n * Δ_n = Δ_n := by
    rw [h_mat]; apply ext_fin2 <;> simp [hP_idem]
  have h_sa : star Δ_n = Δ_n := by
    rw [h_mat]; apply ext_fin2 <;> simp [hP_sa]
  refine ⟨hd_star, hdel_star, h_sum, h_sq, h_sa, ?_, ?_, ?_⟩
  · rw [h_mat]; apply ext_fin2 <;> simp [cantorProj, hP_idem]
  · calc Δ_n * (1 - Δ_n) = Δ_n - Δ_n * Δ_n := by noncomm_ring
      _ = 0 := by rw [h_sq, sub_self]
  · simp only [star_mul, star_sub, star_one, hd_star, hdel_star, h_sa]
    have h_harm_idem : (1 - Δ_n) * (1 - Δ_n) = 1 - Δ_n := by
      calc (1 - Δ_n) * (1 - Δ_n) = 1 - Δ_n - Δ_n + Δ_n * Δ_n := by noncomm_ring
        _ = 1 - Δ_n := by rw [h_sq]; noncomm_ring
    calc star X * d_n * (del_n * X) + star X * del_n * (d_n * X) +
         star X * (1 - Δ_n) * ((1 - Δ_n) * X)
      _ = star X * (d_n * del_n + del_n * d_n) * X +
          star X * ((1 - Δ_n) * (1 - Δ_n)) * X := by noncomm_ring
      _ = star X * (Δ_n + (1 - Δ_n)) * X := by rw [← h_sum, h_harm_idem]; noncomm_ring
      _ = star X * 1 * X := by rw [add_sub_cancel]
      _ = star X * X := by noncomm_ring

end ArchetypeMG3_AllScalesHodgePositiveCone

/-!
## Archetype $\mathcal{M}\mathcal{G}_4$: All-Scales Spectral Mass Gap Hamiltonian & $(2^n - 1)$ Excited Pore FUP Law
-/

section ArchetypeMG4_SpectralMassGapAndExcitedPoreFUP

variable [StarRing A]

/-- All-scales gapped Hamiltonian $H_{\mathrm{YM}}^{(n)}(\mu, \lambda) = \mu \bullet 1 + \lambda \bullet (1 - \Pi_{\mathcal{C}_n})$. -/
def massGapHamiltonian (n : ℕ) (μ λ : ℕ) : ClTower A n :=
  μ • (1 : ClTower A n) + λ • (1 - cantorProj n)

lemma cayley_tower_unitary_and_cantor_fup (n : ℕ) :
    star (cayleyTowerOp n : ClTower A n) * cayleyTowerOp n = (2 ^ n) • (1 : ClTower A n) ∧
    (cantorProj n : ClTower A n) * cayleyTowerOp n * cantorProj n = cantorProj n := by
  induction' n with k ih
  · simp [cantorProj, cayleyTowerOp]
  · rcases ih with ⟨ih_unit, ih_comp⟩
    refine ⟨?_, ?_⟩
    · apply ext_fin2
      · simp [cayleyTowerOp, ih_unit, pow_succ', two_mul, add_nsmul]
      · simp [cayleyTowerOp]
      · simp [cayleyTowerOp]
      · simp [cayleyTowerOp, ih_unit, pow_succ', two_mul, add_nsmul]
    · apply ext_fin2 <;> simp [cantorProj, cayleyTowerOp, ih_comp]

/-- **All-Scales Spectral Mass Gap & $(2^n - 1)$ Excited Pore FUP Theorem ($\mathcal{M}\mathcal{G}_4$)**:
For every scale $n \in \mathbb{N}$ and mass parameters $\mu, \lambda \in \mathbb{N}$:
1. $H_{\mathrm{YM}}^{(n)}(\mu, \lambda)\,\Pi_{\mathcal{C}_n} = \mu \bullet \Pi_{\mathcal{C}_n}$ and
   $H_{\mathrm{YM}}^{(n)}(\mu, \lambda)\,(1 - \Pi_{\mathcal{C}_n}) = (\mu + \lambda) \bullet (1 - \Pi_{\mathcal{C}_n})$,
2. $(H_{\mathrm{YM}}^{(n)}(\mu, \lambda) - \mu \bullet 1)(H_{\mathrm{YM}}^{(n)}(\mu, \lambda) - (\mu + \lambda) \bullet 1) = 0$,
3. *Positive-Cone Mass Gap Lower Bound*:
   $(H_{\mathrm{YM}}^{(n)})^\star H_{\mathrm{YM}}^{(n)} - (\mu^2) \bullet 1 = (2\mu\lambda + \lambda^2) \bullet ((1 - \Pi_{\mathcal{C}_n})^\star (1 - \Pi_{\mathcal{C}_n}))$,
4. *All-Scales $(2^n - 1)$ Excited Pore FUP Energy Law*:
   $((1 - \Pi_{\mathcal{C}_n})\,\mathcal{U}_n\,\Pi_{\mathcal{C}_n})^\star ((1 - \Pi_{\mathcal{C}_n})\,\mathcal{U}_n\,\Pi_{\mathcal{C}_n}) = (2^n - 1) \bullet \Pi_{\mathcal{C}_n}$. -/
theorem all_scales_mass_gap_hamiltonian_and_excited_pore_fup (n μ λ : ℕ) :
    let P_n := (cantorProj n : ClTower A n)
    let Q_n := 1 - P_n
    let H_n := massGapHamiltonian (A := A) n μ λ
    let U_n := (cayleyTowerOp n : ClTower A n)
    H_n * P_n = μ • P_n ∧
    H_n * Q_n = (μ + λ) • Q_n ∧
    (H_n - μ • 1) * (H_n - (μ + λ) • 1) = 0 ∧
    star H_n * H_n - (μ * μ) • (1 : ClTower A n) =
      (2 * μ * λ + λ * λ) • (star Q_n * Q_n) ∧
    star (Q_n * U_n * P_n) * (Q_n * U_n * P_n) = (2 ^ n - 1) • P_n := by
  intro P_n Q_n H_n U_n
  have hP_idem : P_n * P_n = P_n := cantorProj_idempotent n
  have hP_sa   : star P_n = P_n  := cantorProj_selfAdjoint n
  rcases cayley_tower_unitary_and_cantor_fup (A := A) n with ⟨hU_unit, h_comp⟩
  have hQ_idem : Q_n * Q_n = Q_n := by
    dsimp [Q_n]
    calc (1 - P_n) * (1 - P_n) = 1 - P_n - P_n + P_n * P_n := by noncomm_ring
      _ = 1 - P_n := by rw [hP_idem]; noncomm_ring
  have hQ_sa : star Q_n = Q_n := by
    dsimp [Q_n]; rw [star_sub, star_one, hP_sa]
  have hQP : Q_n * P_n = 0 := by
    dsimp [Q_n]
    calc (1 - P_n) * P_n = P_n - P_n * P_n := by noncomm_ring
      _ = 0 := by rw [hP_idem, sub_self]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [H_n, massGapHamiltonian]
    rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    calc (↑μ * 1 + ↑λ * Q_n) * P_n = ↑μ * P_n + ↑λ * (Q_n * P_n) := by noncomm_ring
      _ = ↑μ * P_n := by rw [hQP]; noncomm_ring
  · dsimp [H_n, massGapHamiltonian]
    rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_add]
    calc (↑μ * 1 + ↑λ * Q_n) * Q_n = ↑μ * Q_n + ↑λ * (Q_n * Q_n) := by noncomm_ring
      _ = (↑μ + ↑λ) * Q_n := by rw [hQ_idem]; noncomm_ring
  · dsimp [H_n, massGapHamiltonian]
    rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_add]
    calc (↑μ * 1 + ↑λ * Q_n - ↑μ * 1) * (↑μ * 1 + ↑λ * Q_n - (↑μ + ↑λ) * 1)
      _ = (↑λ * ↑λ) * (Q_n * Q_n - Q_n) := by noncomm_ring
      _ = 0 := by rw [hQ_idem, sub_self, mul_zero]
  · have hH_sa : star H_n = H_n := by
      dsimp [H_n, massGapHamiltonian]
      rw [star_add, star_nsmul, star_nsmul, star_one, hQ_sa]
    rw [hH_sa, hQ_sa]
    dsimp [H_n, massGapHamiltonian]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    calc (↑μ * 1 + ↑λ * Q_n) * (↑μ * 1 + ↑λ * Q_n) - ↑μ * ↑μ * 1
      _ = 2 * ↑μ * ↑λ * Q_n + ↑λ * ↑λ * (Q_n * Q_n) := by noncomm_ring
      _ = (2 * ↑μ * ↑λ + ↑λ * ↑λ) * (Q_n * Q_n) := by rw [hQ_idem]; noncomm_ring
  · have h_full : star (U_n * P_n) * (U_n * P_n) = (2 ^ n) • P_n := by
      calc star (U_n * P_n) * (U_n * P_n)
        _ = P_n * (star U_n * U_n) * P_n := by simp only [star_mul, hP_sa]; noncomm_ring
        _ = P_n * ((2 ^ n) • 1) * P_n := by rw [hU_unit]
        _ = (2 ^ n) • (P_n * P_n) := by rw [nsmul_eq_mul, nsmul_eq_mul]; noncomm_ring
        _ = (2 ^ n) • P_n := by rw [hP_idem]
    have h_part : star (Q_n * U_n * P_n) * (Q_n * U_n * P_n) +
                  star (P_n * U_n * P_n) * (P_n * U_n * P_n) =
                  star (U_n * P_n) * (U_n * P_n) := by
      simp only [star_mul, hP_sa, hQ_sa]
      calc P_n * star U_n * (Q_n * Q_n) * U_n * P_n +
           P_n * star U_n * (P_n * P_n) * U_n * P_n
        _ = P_n * star U_n * (Q_n + P_n) * U_n * P_n := by rw [hQ_idem, hP_idem]; noncomm_ring
        _ = P_n * star U_n * 1 * U_n * P_n := by dsimp [Q_n]; rw [sub_add_cancel]
        _ = P_n * star U_n * (U_n * P_n) := by noncomm_ring
    rw [h_comp, hP_sa, hP_idem, h_full] at h_part
    have h_pow_split : (2 ^ n) • P_n = (2 ^ n - 1) • P_n + P_n := by
      have h_ge : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      calc (2 ^ n) • P_n = ((2 ^ n - 1) + 1) • P_n := by rw [Nat.sub_add_cancel h_ge]
        _ = (2 ^ n - 1) • P_n + P_n := by rw [add_nsmul, one_nsmul]
    rw [h_pow_split] at h_part
    exact add_right_cancel h_part

end ArchetypeMG4_SpectralMassGapAndExcitedPoreFUP

end NoncommutativeColimitAndSpectralGapSynthesis
```

## Turn 0066, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeHodgeParabolicTowerSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

end Matrix2Simp

/-!
## Inductive Tower `ClTower A n` & Core Operators
-/

universe u

def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      letI : StarRing (ClTower A n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorProj n) 0 0 0

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace]
      rw [Matrix.zero_apply, Matrix.zero_apply, towerTrace_zero n, add_zero]

lemma towerTrace_add : ∀ {n : ℕ} (X Y : ClTower A n),
    towerTrace (X + Y) = towerTrace X + towerTrace Y
  | 0,     _, _ => rfl
  | _ + 1, X, Y => by
      dsimp [towerTrace]
      rw [Matrix.add_apply, Matrix.add_apply, towerTrace_add, towerTrace_add]
      abel

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      rw [Matrix.neg_apply, Matrix.neg_apply, towerTrace_neg, towerTrace_neg]
      abel

lemma towerTrace_nsmul {n : ℕ} (k : ℕ) (X : ClTower A n) :
    towerTrace (k • X) = k • towerTrace X := by
  induction' k with m ih
  · simp [towerTrace_zero n]
  · rw [ add_nsmul, one_nsmul, towerTrace_add, ih, add_nsmul, one_nsmul]

lemma cantorProj_idempotent : ∀ (n : ℕ),
    (cantorProj n : ClTower A n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_idempotent n]

lemma cantorProj_selfAdjoint [StarRing A] : ∀ (n : ℕ),
    star (cantorProj n : ClTower A n) = cantorProj n
  | 0     => star_one A
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_selfAdjoint n]

lemma chiralityOp_cantorProj : ∀ (n : ℕ),
    (chiralityOp n : ClTower A n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [chiralityOp, cantorProj, chiralityOp_cantorProj n]

lemma towerTrace_cantorProj : ∀ (n : ℕ),
    towerTrace (cantorProj n : ClTower A n) = 1
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace, cantorProj]
      rw [mat2_00, mat2_11, towerTrace_zero n, add_zero, towerTrace_cantorProj n]

/-!
## Archetype $\mathcal{H}\mathcal{P}_1$: All-Scales Hodge–Parabolic Light-Cone Nilpotent Generator $\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$
-/

section ArchetypeHP1_HodgeParabolicGenerator

def wittD (n : ℕ) : ClTower A (n + 1) := mat2 0 (cantorProj n) 0 0
def wittDelta (n : ℕ) : ClTower A (n + 1) := mat2 0 0 (cantorProj n) 0

/-- Local Hodge $Cl(1,1)$ triad inside $\mathcal{C}\ell_{n+1}(A)$. -/
def hodgeSigma (n : ℕ) : ClTower A (n + 1) := wittD n + wittDelta n
def hodgeOmega (n : ℕ) : ClTower A (n + 1) := wittDelta n - wittD n
def hodgeGamma (n : ℕ) : ClTower A (n + 1) := wittD n * wittDelta n - wittDelta n * wittD n

/-- The $(n+1)$-scale Hodge–Parabolic light-cone nilpotent generator
$\mathcal{N}_{\mathrm{Hodge}}^{(n+1)} = \Omega_{\mathrm{Hodge}}^{(n+1)} - \Gamma_{\mathrm{Hodge}}^{(n+1)}$
and monodromy $Q_{\mathrm{Hodge}}^{(n+1)} = 1 + \mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$. -/
def hodgeNilpotent (n : ℕ) : ClTower A (n + 1) :=
  hodgeOmega n - hodgeGamma n

def hodgeMonodromy (n : ℕ) : ClTower A (n + 1) :=
  1 + hodgeNilpotent n

theorem hodgeNilpotent_explicit (n : ℕ) :
    hodgeNilpotent (A := A) n =
      mat2 (-cantorProj n) (-cantorProj n) (cantorProj n) (cantorProj n) := by
  have hP := cantorProj_idempotent (A := A) n
  apply ext_fin2 <;> simp [hodgeNilpotent, hodgeOmega, hodgeGamma, wittD, wittDelta, hP]

theorem hodgeNilpotent_sq_zero (n : ℕ) :
    hodgeNilpotent (A := A) n * hodgeNilpotent n = 0 := by
  have hP := cantorProj_idempotent (A := A) n
  rw [hodgeNilpotent_explicit]
  apply ext_fin2 <;> simp [hP]

theorem hodgeMonodromy_pow (n k : ℕ) :
    (hodgeMonodromy (A := A) n) ^ k = 1 + k • hodgeNilpotent n := by
  induction' k with m ih
  · simp
  · rw [pow_succ, ih, hodgeMonodromy, add_nsmul, one_nsmul]
    have h_mul : (m • hodgeNilpotent (A := A) n) * hodgeNilpotent n = 0 := by
      rw [nsmul_eq_mul, mul_assoc, hodgeNilpotent_sq_zero n, mul_zero]
    calc (1 + m • hodgeNilpotent (A := A) n) * (1 + hodgeNilpotent n)
      _ = 1 + (m • hodgeNilpotent n + hodgeNilpotent n) +
          (m • hodgeNilpotent n) * hodgeNilpotent n := by noncomm_ring
      _ = 1 + (m • hodgeNilpotent n + hodgeNilpotent n) := by rw [h_mul, add_zero]

/-- **All-Scales Hodge–Parabolic Light-Cone Theorem ($\mathcal{H}\mathcal{P}_1$)**:
At every scale $n \in \mathbb{N}$:
1. $(\mathcal{N}_{\mathrm{Hodge}}^{(n+1)})^2 = 0$,
2. $\Sigma_{\mathrm{Hodge}}^{(n+1)} \mathcal{N}_{\mathrm{Hodge}}^{(n+1)} \Sigma_{\mathrm{Hodge}}^{(n+1)} = -\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$,
3. $\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$ annihilates the harmonic projection $1 - (d_n\delta_n + \delta_n d_n)$,
4. $(Q_{\mathrm{Hodge}}^{(n+1)})^k = 1 + k \bullet \mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$ for all $k \in \mathbb{N}$. -/
theorem all_scales_hodge_parabolic_generator_properties (n k : ℕ) :
    let N_n := hodgeNilpotent (A := A) n
    let Σ_n := hodgeSigma (A := A) n
    let e_harm := 1 - (wittD (A := A) n * wittDelta n + wittDelta n * wittD n)
    N_n * N_n = 0 ∧
    Σ_n * N_n * Σ_n = -N_n ∧
    N_n * e_harm = 0 ∧
    (hodgeMonodromy (A := A) n) ^ k = 1 + k • N_n := by
  have hP := cantorProj_idempotent (A := A) n
  refine ⟨hodgeNilpotent_sq_zero n, ?_, ?_, hodgeMonodromy_pow n k⟩
  · rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [hodgeSigma, wittD, wittDelta, hP]
  · rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [wittD, wittDelta, hP]

end ArchetypeHP1_HodgeParabolicGenerator

/-!
## Archetype $\mathcal{H}\mathcal{P}_2$ & $\mathcal{H}\mathcal{P}_3$: 1-Step Total Vacuum Evacuation & $k$-Step Positive-Cone Coexact Leakage
-/

section ArchetypeHP2_HP3_VacuumEvacuationAndCoexactLeakage

/-- **1-Step Total Vacuum Evacuation & $k$-Step Coexact Excitation Theorem ($\mathcal{H}\mathcal{P}_2$)**:
At every scale $n \in \mathbb{N}$:
1. $Q_{\mathrm{Hodge}}^{(n+1)} \Pi_{\mathcal{C}_{n+1}} = \delta_n$ (1-step total evacuation into the coexact Witt sheet),
2. $\Pi_{\mathcal{C}_{n+1}} Q_{\mathrm{Hodge}}^{(n+1)} \Pi_{\mathcal{C}_{n+1}} = 0$ (vanishing 1-step vacuum survival),
3. $(\delta_n d_n) (Q_{\mathrm{Hodge}}^{(n+1)})^k \Pi_{\mathcal{C}_{n+1}} = k \bullet \delta_n$ ($k$-step coexact excitation law). -/
theorem vacuum_evacuation_and_k_step_coexact_excitation (n k : ℕ) :
    let P_vac := cantorProj (A := A) (n + 1)
    let e_co  := wittDelta (A := A) n * wittD n
    hodgeMonodromy n * P_vac = wittDelta n ∧
    P_vac * hodgeMonodromy n * P_vac = 0 ∧
    e_co * ((hodgeMonodromy n) ^ k) * P_vac = k • wittDelta n := by
  have hP := cantorProj_idempotent (A := A) n
  refine ⟨?_, ?_, ?_⟩
  · dsimp [hodgeMonodromy]
    rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [cantorProj, wittDelta, hP]
  · dsimp [hodgeMonodromy]
    rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [cantorProj, hP]
  · rw [hodgeMonodromy_pow n k, hodgeNilpotent_explicit]
    apply ext_fin2
    · simp [wittDelta, wittD, cantorProj]
    · simp [wittDelta, wittD, cantorProj]
    · simp [wittDelta, wittD, cantorProj, hP]
      rw [nsmul_eq_mul, nsmul_eq_mul]; noncomm_ring
    · simp [wittDelta, wittD, cantorProj]

variable [StarRing A]

/-- **$k$-Step Quadratic Coexact Leakage & Positive-Cone Energy Decomposition ($\mathcal{H}\mathcal{P}_3$)**:
Over any noncommutative $\star$-ring $A$, at every scale $n \in \mathbb{N}$ and step $k \in \mathbb{N}$:
1. The Hermitian square of the coexact excitation $e_{\mathrm{co}}^{(n+1)} (Q_{\mathrm{Hodge}}^{(n+1)})^k \Pi_{\mathcal{C}_{n+1}}$
   is $(k^2) \bullet \Pi_{\mathcal{C}_{n+1}}$,
2. The total $k$-step parabolic state energy decomposes into the vacuum survival energy plus $(k^2) \bullet \Pi_{\mathcal{C}_{n+1}}$. -/
theorem k_step_coexact_leakage_and_positive_cone_energy (n k : ℕ) :
    let P_vac := cantorProj (A := A) (n + 1)
    let e_co  := wittDelta (A := A) n * wittD n
    let Q_k   := (hodgeMonodromy (A := A) n) ^ k
    star (e_co * Q_k * P_vac) * (e_co * Q_k * P_vac) = (k * k) • P_vac ∧
    star (Q_k * P_vac) * (Q_k * P_vac) =
      star (P_vac * Q_k * P_vac) * (P_vac * Q_k * P_vac) + (k * k) • P_vac := by
  intro P_vac e_co Q_k
  have hP_idem := cantorProj_idempotent (A := A) n
  have hP_sa   := cantorProj_selfAdjoint (A := A) n
  have h_co    := (vacuum_evacuation_and_k_step_coexact_excitation (A := A) n k).2.2
  have h_del_sq : star (wittDelta (A := A) n) * wittDelta n = P_vac := by
    apply ext_fin2 <;> simp [P_vac, wittDelta, cantorProj, hP_sa, hP_idem]
  have h_leak : star (e_co * Q_k * P_vac) * (e_co * Q_k * P_vac) = (k * k) • P_vac := by
    rw [h_co, star_nsmul, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
    calc (↑k * star (wittDelta (A := A) n)) * (↑k * wittDelta n)
      _ = (↑k * ↑k) * (star (wittDelta n) * wittDelta n) := by noncomm_ring
      _ = (↑k * ↑k) * P_vac := by rw [h_del_sq]
  refine ⟨h_leak, ?_⟩
  rw [← h_leak, ← h_co]
  dsimp [Q_k, P_vac, e_co]
  rw [hodgeMonodromy_pow n k, hodgeNilpotent_explicit]
  apply ext_fin2
  · simp [cantorProj, wittDelta, wittD, hP_sa, hP_idem]
    simp only [nsmul_eq_mul]
    noncomm_ring
  · simp [cantorProj, wittDelta, wittD]
  · simp [cantorProj, wittDelta, wittD]
  · simp [cantorProj, wittDelta, wittD]

end ArchetypeHP2_HP3_VacuumEvacuationAndCoexactLeakage

/-!
## Archetype $\mathcal{H}\mathcal{P}_4$: All-Scales Trace Blindness vs. Atiyah–Singer Supertrace Winding Detection
-/

section ArchetypeHP4_TraceBlindnessVsSupertraceWinding

theorem superTrace_one_succ (n : ℕ) :
    superTrace (1 : ClTower A (n + 1)) = 0 := by
  dsimp [superTrace, chiralityOp, towerTrace]
  simp [towerTrace_neg]

/-- **All-Scales Trace Blindness vs. Supertrace Winding Detection Theorem ($\mathcal{H}\mathcal{P}_4$)**:
At every scale $n \in \mathbb{N}$ and parabolic step $k \in \mathbb{N}$:
1. $\mathrm{Tr}_{2^{n+1}}(\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}) = 0$ (ungraded trace is blind to $\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$),
2. $\mathrm{Str}_{2^{n+1}}(\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}) = -(2 \bullet 1_A)$,
3. $\mathrm{Str}_{2^{n+1}}\big((Q_{\mathrm{Hodge}}^{(n+1)})^k\big) = -((2 * k) \bullet 1_A)$ (supertrace detects the exact winding $k$). -/
theorem all_scales_trace_blindness_vs_supertrace_winding_detection (n k : ℕ) :
    towerTrace (hodgeNilpotent (A := A) n) = 0 ∧
    superTrace (hodgeNilpotent (A := A) n) = -(2 • (1 : A)) ∧
    superTrace ((hodgeMonodromy (A := A) n) ^ k) = -((2 * k) • (1 : A)) := by
  have h_super_nil : superTrace (hodgeNilpotent (A := A) n) = -(2 • (1 : A)) := by
    dsimp [superTrace]
    rw [hodgeNilpotent_explicit]
    dsimp [chiralityOp, towerTrace]
    simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul, neg_neg,
      chiralityOp_cantorProj n, towerTrace_neg, towerTrace_cantorProj n, two_smul]
    abel
  refine ⟨?_, h_super_nil, ?_⟩
  · rw [hodgeNilpotent_explicit]
    dsimp [towerTrace]
    simp [towerTrace_neg]
  · rw [hodgeMonodromy_pow n k]
    dsimp [superTrace]
    have h_lin : chiralityOp (n + 1) * (1 + k • hodgeNilpotent (A := A) n) =
        chiralityOp (n + 1) * 1 + k • (chiralityOp (n + 1) * hodgeNilpotent n) := by
      rw [nsmul_eq_mul, nsmul_eq_mul]; noncomm_ring
    rw [h_lin, towerTrace_add, towerTrace_nsmul]
    change superTrace (1 : ClTower A (n + 1)) +
           k • superTrace (hodgeNilpotent (A := A) n) = -((2 * k) • (1 : A))
    rw [superTrace_one_succ n, zero_add, h_super_nil]
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    noncomm_ring

end ArchetypeHP4_TraceBlindnessVsSupertraceWinding

end NoncommutativeHodgeParabolicTowerSynthesis
```

## Turn 0069, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace CliffordColimitMassGapAndLindbladSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Inductive Tower `ClTower A n`
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

end Matrix2Simp

universe u

def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace]
      rw [Matrix.zero_apply, Matrix.zero_apply, towerTrace_zero n, add_zero]

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

/-!
## Archetype $\mathcal{C}\mathcal{L}_1$ & $\mathcal{C}\mathcal{L}_2$: Directed Bott Colimit `Setoid`, Quotient $\mathcal{C}\ell_\infty(A)$ & $\mathrm{Str}_\infty$
-/

section ArchetypeCL1_CL2_ColimitSetoidAndQuotient

/-- Canonical Bott corner embedding $\iota_{\mathrm{Bott}} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+1}(A)$. -/
def bottEmbed {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

theorem bottEmbed_add {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X + Y) = bottEmbed X + bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

theorem bottEmbed_mul {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X * Y) = bottEmbed X * bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

/-- Iterated multi-step Bott embedding $\iota_{\mathrm{Bott}}^{(k)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+k}(A)$. -/
def bottEmbedIter : ∀ {n : ℕ} (k : ℕ), ClTower A n → ClTower A (n + k)
  | _, 0,     X => X
  | _, k + 1, X => bottEmbed (bottEmbedIter k X)

theorem colimit_superTrace_invariant {n : ℕ} (X : ClTower A n) :
    superTrace (bottEmbed X) = superTrace X := by
  dsimp [superTrace, bottEmbed, chiralityOp, towerTrace]
  simp [towerTrace_zero n]

theorem colimit_superTrace_iter_invariant {n : ℕ} (k : ℕ) (X : ClTower A n) :
    superTrace (bottEmbedIter k X) = superTrace X := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]
      ; rw [colimit_superTrace_invariant, ih]

lemma bottEmbed_congr_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (bottEmbed X) (bottEmbed Y) := by
  subst h_dim; cases eq_of_heq h_heq; exact HEq.rfl

lemma bottEmbedIter_congr_heq {m₁ m₂ : ℕ} (d : ℕ) {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (bottEmbedIter d X) (bottEmbedIter d Y) := by
  induction' d with d ih
  · exact h_heq
  · exact bottEmbed_congr_heq (by omega) ih

lemma bottEmbedIter_add_heq {n : ℕ} (k d : ℕ) (X : ClTower A n) :
    HEq (bottEmbedIter (k + d) X) (bottEmbedIter d (bottEmbedIter k X)) := by
  induction' d with d ih
  · exact HEq.rfl
  · exact bottEmbed_congr_heq (by omega) ih

lemma bottEmbedIter_comm_heq {n : ℕ} (a b : ℕ) (X : ClTower A n) :
    HEq (bottEmbedIter (a + b) X) (bottEmbedIter (b + a) X) := by
  have h : a + b = b + a := Nat.add_comm a b
  rw [h]

/-- Directed colimit equivalence relation on $\Sigma\, n : \mathbb{N},\, \mathcal{C}\ell_n(A)$. -/
def ClInfRel (u v : Σ n : ℕ, ClTower A n) : Prop :=
  ∃ (k₁ k₂ : ℕ), u.1 + k₁ = v.1 + k₂ ∧
    HEq (bottEmbedIter k₁ u.2) (bottEmbedIter k₂ v.2)

theorem clInfRel_trans {u v w : Σ n : ℕ, ClTower A n}
    (huv : ClInfRel u v) (hvw : ClInfRel v w) : ClInfRel u w := by
  rcases huv with ⟨k₁, k₂, h12, heq12⟩
  rcases hvw with ⟨l₁, l₂, h23, heq23⟩
  refine ⟨k₁ + l₁, l₂ + k₂, by omega, ?_⟩
  exact (bottEmbedIter_add_heq k₁ l₁ u.2).trans <|
    (bottEmbedIter_congr_heq l₁ h12 heq12).trans <|
    (bottEmbedIter_add_heq k₂ l₁ v.2).symm.trans <|
    (bottEmbedIter_comm_heq k₂ l₁ v.2).trans <|
    (bottEmbedIter_add_heq l₁ k₂ v.2).trans <|
    (bottEmbedIter_congr_heq k₂ h23 heq23).trans <|
    (bottEmbedIter_add_heq l₂ k₂ w.2).symm

/-- Certified `Setoid` instance for the inductive colimit $\mathcal{C}\ell(\infty, \infty)$. -/
instance clInfSetoid (A : Type u) [Ring A] : Setoid (Σ n : ℕ, ClTower A n) where
  r := ClInfRel
  iseqv := {
    refl  := fun _ => ⟨0, 0, rfl, HEq.rfl⟩
    symm  := fun ⟨k₁, k₂, h, heq⟩ => ⟨k₂, k₁, h.symm, heq.symm⟩
    trans := clInfRel_trans
  }

/-- The universal colimit quotient type $\mathcal{C}\ell_\infty(A) = \mathrm{Quotient}(\mathrm{clInfSetoid}\;A)$. -/
abbrev ClInf (A : Type u) [Ring A] := Quotient (clInfSetoid A)

/-- Canonical colimit cocone injection $\pi_\infty(n, X) \in \mathcal{C}\ell_\infty(A)$. -/
def toClInf (n : ℕ) (X : ClTower A n) : ClInf A :=
  Quotient.mk (clInfSetoid A) ⟨n, X⟩

lemma superTrace_eq_of_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    superTrace X = superTrace Y := by
  subst h_dim; cases eq_of_heq h_heq; rfl

theorem clInf_superTrace_well_defined
    (u v : Σ n : ℕ, ClTower A n) (h_rel : ClInfRel u v) :
    superTrace u.2 = superTrace v.2 := by
  rcases h_rel with ⟨k₁, k₂, h_dim, h_heq⟩
  calc superTrace u.2
    _ = superTrace (bottEmbedIter k₁ u.2) := (colimit_superTrace_iter_invariant k₁ u.2).symm
    _ = superTrace (bottEmbedIter k₂ v.2) := superTrace_eq_of_heq h_dim h_heq
    _ = superTrace v.2                    := colimit_superTrace_iter_invariant k₂ v.2

/-- The quotient-lifted Atiyah–Singer supertrace $\mathrm{Str}_\infty : \mathcal{C}\ell_\infty(A) \to A$. -/
def clInfSuperTrace : ClInf A → A :=
  Quotient.lift (fun u => superTrace u.2) clInf_superTrace_well_defined

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => bottEmbed (cantorProj n)

/-- **Universal Quotient Colimit Stabilization Theorem ($\mathcal{C}\mathcal{L}_1$ & $\mathcal{C}\mathcal{L}_2$)**:
1. $\pi_\infty(n + 1, \iota_{\mathrm{Bott}}(X)) = \pi_\infty(n, X)$,
2. All Cantor vacuum projections $\Pi_{\mathcal{C}_n}$ map to the same universal vacuum $\pi_\infty(0, 1_A)$,
3. $\mathrm{Str}_\infty(\pi_\infty(n, \Pi_{\mathcal{C}_n})) = 1_A$ for all $n \in \mathbb{N}$. -/
theorem clInf_vacuum_stabilization_and_supertrace (n : ℕ) (X : ClTower A n) :
    toClInf (n + 1) (bottEmbed X) = toClInf n X ∧
    toClInf n (cantorProj n) = toClInf 0 (1 : A) ∧
    clInfSuperTrace (toClInf n (cantorProj n)) = 1 := by
  have h_step : ∀ (m : ℕ) (Y : ClTower A m), toClInf (m + 1) (bottEmbed Y) = toClInf m Y := by
    intro m Y
    apply Quotient.sound
    exact ⟨0, 1, by omega, HEq.rfl⟩
  have h_vac : ∀ (m : ℕ), toClInf m (cantorProj m) = toClInf 0 (1 : A) := by
    intro m; induction' m with m ih
    · rfl
    · dsimp [cantorProj]; rw [h_step m (cantorProj m), ih]
  refine ⟨h_step n X, h_vac n, ?_⟩
  rw [h_vac n]
  dsimp [clInfSuperTrace, toClInf, superTrace, chiralityOp, towerTrace]
  exact mul_one 1

end ArchetypeCL1_CL2_ColimitSetoidAndQuotient

/-!
## Archetype $\mathcal{C}\mathcal{L}_3$: Noncommutative Mass Gap Operator $\Delta_n(m_0)$ & Colimit Stability
-/

section ArchetypeCL3_NoncommutativeMassGapOperator

/-- Unital diagonal embedding $\iota_{\mathrm{diag}}^{(n)} : A \to \mathcal{C}\ell_n(A)$ of a mass operator $m_0 \in A$. -/
def towerScalar : ∀ (n : ℕ), A → ClTower A n
  | 0,     a => a
  | n + 1, a => mat2 (towerScalar n a) 0 0 (towerScalar n a)

lemma towerScalar_mul (n : ℕ) (a b : A) :
    towerScalar n (a * b) = towerScalar n a * towerScalar n b := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, ih]

lemma towerScalar_comm_cantorProj (n : ℕ) (m₀ : A) :
    towerScalar n m₀ * cantorProj n = cantorProj n * towerScalar n m₀ := by
  induction' n with m ih
  · dsimp [towerScalar, cantorProj]; rw [mul_one, one_mul]
  · apply ext_fin2 <;> simp [towerScalar, cantorProj, bottEmbed, ih]

lemma towerScalar_bottEmbed (n : ℕ) (m₀ : A) (X : ClTower A n) :
    towerScalar (n + 1) m₀ * bottEmbed X = bottEmbed (towerScalar n m₀ * X) := by
  apply ext_fin2 <;> simp [towerScalar, bottEmbed]

lemma cantorProj_idem : ∀ (n : ℕ), cantorProj n * cantorProj n = (cantorProj n : ClTower A n)
  | 0     => mul_one 1
  | n + 1 => by dsimp [cantorProj]; rw [← bottEmbed_mul, cantorProj_idem n]

/-- Noncommutative mass gap operator $\Delta_n(m_0) = \iota_{\mathrm{diag}}^{(n)}(m_0)(1 - \Pi_{\mathcal{C}_n}) \in \mathcal{C}\ell_n(A)$. -/
def massGapOp (m₀ : A) (n : ℕ) : ClTower A n :=
  towerScalar n m₀ * (1 - cantorProj n)

/-- **Two-Sided Vacuum Annihilation, Excited Coercivity & Colimit Stability ($\mathcal{C}\mathcal{L}_3$)**:
For any mass operator $m_0 \in A$ and scale $n \in \mathbb{N}$:
1. $\Delta_n(m_0) \Pi_{\mathcal{C}_n} = 0$ and $\Pi_{\mathcal{C}_n} \Delta_n(m_0) = 0$,
2. If $\Pi_{\mathcal{C}_n} \Psi = 0$, then $\Delta_n(m_0) \Psi = \iota_{\mathrm{diag}}^{(n)}(m_0) \Psi$,
3. If $\Pi_{\mathcal{C}_n} \Psi = 0$, then $\Delta_{n+1}(m_0)\,\iota_{\mathrm{Bott}}(\Psi) = \iota_{\mathrm{Bott}}(\Delta_n(m_0)\Psi)$. -/
theorem massGap_vacuum_annihilation_coercivity_and_colimit_stability
    (m₀ : A) (n : ℕ) (Ψ : ClTower A n) (h_orth : cantorProj n * Ψ = 0) :
    massGapOp m₀ n * cantorProj n = 0 ∧
    cantorProj n * massGapOp m₀ n = 0 ∧
    massGapOp m₀ n * Ψ = towerScalar n m₀ * Ψ ∧
    massGapOp m₀ (n + 1) * bottEmbed Ψ = bottEmbed (massGapOp m₀ n * Ψ) := by
  have hP := cantorProj_idem (A := A) n
  have h_coercive : ∀ {k : ℕ} (Φ : ClTower A k),
      cantorProj k * Φ = 0 → massGapOp m₀ k * Φ = towerScalar k m₀ * Φ := by
    intro k Φ hΦ
    dsimp [massGapOp]
    calc towerScalar k m₀ * (1 - cantorProj k) * Φ
      _ = towerScalar k m₀ * Φ - towerScalar k m₀ * (cantorProj k * Φ) := by noncomm_ring
      _ = towerScalar k m₀ * Φ := by rw [hΦ, mul_zero, sub_zero]
  have h_orth_next : cantorProj (n + 1) * bottEmbed Ψ = 0 := by
    dsimp [cantorProj]
    rw [← bottEmbed_mul, h_orth]
    apply ext_fin2 <;> rfl
  refine ⟨?_, ?_, h_coercive Ψ h_orth, ?_⟩
  · dsimp [massGapOp]
    calc towerScalar n m₀ * (1 - cantorProj n) * cantorProj n
      _ = towerScalar n m₀ * (cantorProj n - cantorProj n * cantorProj n) := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, mul_zero]
  · dsimp [massGapOp]
    calc cantorProj n * (towerScalar n m₀ * (1 - cantorProj n))
      _ = (cantorProj n * towerScalar n m₀) * (1 - cantorProj n) := by noncomm_ring
      _ = (towerScalar n m₀ * cantorProj n) * (1 - cantorProj n) := by
          rw [← towerScalar_comm_cantorProj n m₀]
      _ = towerScalar n m₀ * (cantorProj n - cantorProj n * cantorProj n) := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, mul_zero]
  · rw [h_coercive (bottEmbed Ψ) h_orth_next, h_coercive Ψ h_orth, towerScalar_bottEmbed]

end ArchetypeCL3_NoncommutativeMassGapOperator

/-!
## Archetype $\mathcal{C}\mathcal{L}_4$: Metriplectic Double-Commutator Lindblad Dissipator & Quadratic Mass-Gap Damping
-/

section ArchetypeCL4_MetriplecticLindbladMassGapDamping

/-- The Metriplectic Double-Commutator Lindblad Dissipator $\mathcal{D}_{\mathrm{Lind}}(H, \rho) = -\⁅H, \⁅H, \rho⁆⁆$. -/
def lindbladDissipator {R : Type*} [Ring R] (H ρ : R) : R :=
  -⁅H, ⁅H, ρ⁆⁆

/-- Off-diagonal vacuum-to-excited transition coherence $\Psi_{\mathrm{coh}}(X) = (1 - \Pi_{\mathcal{C}_n}) X \Pi_{\mathcal{C}_n}$. -/
def coherenceMode (n : ℕ) (X : ClTower A n) : ClTower A n :=
  (1 - cantorProj n) * X * cantorProj n

/-- **Metriplectic Lindblad GKSL Normal Form, Quadratic Mass-Gap Damping & Colimit Stability ($\mathcal{C}\mathcal{L}_4$)**:
1. *GKSL Normal Form*: $-\⁅H, \⁅H, \rho⁆⁆ = 2 \bullet (H \rho H) - (H^2 \rho + \rho H^2)$,
2. *Decoherence-Free Vacuum*: $\mathcal{D}_{\mathrm{Lind}}(\Delta_n(m_0), \Pi_{\mathcal{C}_n}) = 0$,
3. *Quadratic Mass-Gap Damping*: On any transition coherence $\Psi_{\mathrm{coh}}(X) = (1 - \Pi_{\mathcal{C}_n}) X \Pi_{\mathcal{C}_n}$,
   $\mathcal{D}_{\mathrm{Lind}}(\Delta_n(m_0), \Psi_{\mathrm{coh}}(X)) = -\iota_{\mathrm{diag}}^{(n)}(m_0^2)\,\Psi_{\mathrm{coh}}(X)$,
4. *Colimit Stability of Lindblad Damping*:
   $\mathcal{D}_{\mathrm{Lind}}(\Delta_{n+1}(m_0), \iota_{\mathrm{Bott}}(\Psi_{\mathrm{coh}}(X))) =
    \iota_{\mathrm{Bott}}(\mathcal{D}_{\mathrm{Lind}}(\Delta_n(m_0), \Psi_{\mathrm{coh}}(X)))$. -/
theorem lindblad_mass_gap_damping_and_colimit_stability
    (m₀ : A) (n : ℕ) (H ρ X : ClTower A n) :
    let Δ_n   := massGapOp m₀ n
    let Δ_n1  := massGapOp m₀ (n + 1)
    let Ψ_coh := coherenceMode n X
    lindbladDissipator H ρ = 2 • (H * ρ * H) - (H * H * ρ + ρ * (H * H)) ∧
    lindbladDissipator Δ_n (cantorProj n) = 0 ∧
    lindbladDissipator Δ_n Ψ_coh = -(towerScalar n (m₀ * m₀) * Ψ_coh) ∧
    lindbladDissipator Δ_n1 (bottEmbed Ψ_coh) =
      bottEmbed (lindbladDissipator Δ_n Ψ_coh) := by
  intro Δ_n Δ_n1 Ψ_coh
  have hP := cantorProj_idem (A := A) n
  have h_orth : cantorProj n * Ψ_coh = 0 := by
    dsimp [Ψ_coh, coherenceMode]
    calc cantorProj n * ((1 - cantorProj n) * X * cantorProj n)
      _ = (cantorProj n - cantorProj n * cantorProj n) * X * cantorProj n := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, zero_mul, zero_mul]
  rcases massGap_vacuum_annihilation_coercivity_and_colimit_stability m₀ n Ψ_coh h_orth with
    ⟨h_ann_R, h_ann_L, h_coer, _⟩
  have h_right_zero : ∀ (Y : ClTower A n), Y * cantorProj n * Δ_n = 0 := by
    intro Y
    calc Y * cantorProj n * Δ_n = Y * (cantorProj n * Δ_n) := by noncomm_ring
      _ = 0 := by rw [h_ann_L, mul_zero]
  have h_comm1 : ⁅Δ_n, Ψ_coh⁆ = towerScalar n m₀ * Ψ_coh := by
    rw [Ring.lie_def, h_coer]
    have hR : Ψ_coh * Δ_n = 0 := h_right_zero ((1 - cantorProj n) * X)
    rw [hR, sub_zero]
  have h_comm2 : ⁅Δ_n, towerScalar n m₀ * Ψ_coh⁆ = towerScalar n (m₀ * m₀) * Ψ_coh := by
    rw [Ring.lie_def]
    have h_orth2 : cantorProj n * (towerScalar n m₀ * Ψ_coh) = 0 := by
      calc cantorProj n * (towerScalar n m₀ * Ψ_coh)
        _ = (cantorProj n * towerScalar n m₀) * Ψ_coh := by noncomm_ring
        _ = (towerScalar n m₀ * cantorProj n) * Ψ_coh := by
            rw [← towerScalar_comm_cantorProj n m₀]
        _ = towerScalar n m₀ * (cantorProj n * Ψ_coh) := by noncomm_ring
        _ = 0 := by rw [h_orth, mul_zero]
    have hL2 := (massGap_vacuum_annihilation_coercivity_and_colimit_stability
      m₀ n (towerScalar n m₀ * Ψ_coh) h_orth2).2.2.1
    have hR2 : (towerScalar n m₀ * Ψ_coh) * Δ_n = 0 := by
      dsimp [Ψ_coh, coherenceMode]
      calc (towerScalar n m₀ * ((1 - cantorProj n) * X * cantorProj n)) * Δ_n
        _ = (towerScalar n m₀ * ((1 - cantorProj n) * X)) * (cantorProj n * Δ_n) := by
            noncomm_ring
        _ = 0 := by rw [h_ann_L, mul_zero]
    rw [hL2, hR2, sub_zero, ← mul_assoc, ← towerScalar_mul]
  have h_damping : lindbladDissipator Δ_n Ψ_coh = -(towerScalar n (m₀ * m₀) * Ψ_coh) := by
    dsimp [lindbladDissipator]
    rw [h_comm1, h_comm2]
  refine ⟨?_, ?_, h_damping, ?_⟩
  · dsimp [lindbladDissipator]
    simp only [Ring.lie_def, two_smul]
    noncomm_ring
  · dsimp [lindbladDissipator]
    have h_vac_comm : ⁅Δ_n, cantorProj n⁆ = 0 := by
      rw [Ring.lie_def, h_ann_R, h_ann_L, sub_self]
    rw [h_vac_comm, Ring.lie_def, mul_zero, zero_mul, sub_self, neg_zero]
  · rw [h_damping]
    have h_neg_emb : bottEmbed (-(towerScalar n (m₀ * m₀) * Ψ_coh)) =
        -(towerScalar (n + 1) (m₀ * m₀) * bottEmbed Ψ_coh) := by
      rw [← towerScalar_bottEmbed]
      apply ext_fin2 <;> simp [bottEmbed]
    rw [h_neg_emb]
    have h_orth_b : cantorProj (n + 1) * bottEmbed Ψ_coh = 0 := by
      dsimp [cantorProj]; rw [← bottEmbed_mul, h_orth]; apply ext_fin2 <;> rfl
    have h_R_b : bottEmbed Ψ_coh * cantorProj (n + 1) = bottEmbed Ψ_coh := by
      dsimp [cantorProj]; rw [← bottEmbed_mul]
      have h_id : Ψ_coh * cantorProj n = Ψ_coh := by
        dsimp [Ψ_coh, coherenceMode]
        calc (1 - cantorProj n) * X * cantorProj n * cantorProj n
          _ = (1 - cantorProj n) * X * (cantorProj n * cantorProj n) := by noncomm_ring
          _ = Ψ_coh := by rw [hP]
      rw [h_id]
    rcases massGap_vacuum_annihilation_coercivity_and_colimit_stability
      m₀ (n + 1) (bottEmbed Ψ_coh) h_orth_b with ⟨_, h_ann_L1, h_coer1, _⟩
    have h_c1 : ⁅Δ_n1, bottEmbed Ψ_coh⁆ = towerScalar (n + 1) m₀ * bottEmbed Ψ_coh := by
      rw [Ring.lie_def, h_coer1]
      have hR1 : bottEmbed Ψ_coh * Δ_n1 = 0 := by
        calc bottEmbed Ψ_coh * Δ_n1 = (bottEmbed Ψ_coh * cantorProj (n + 1)) * Δ_n1 := by
              rw [h_R_b]
          _ = bottEmbed Ψ_coh * (cantorProj (n + 1) * Δ_n1) := by noncomm_ring
          _ = 0 := by rw [h_ann_L1, mul_zero]
      rw [hR1, sub_zero]
    have h_c2 : ⁅Δ_n1, towerScalar (n + 1) m₀ * bottEmbed Ψ_coh⁆ =
        towerScalar (n + 1) (m₀ * m₀) * bottEmbed Ψ_coh := by
      rw [towerScalar_bottEmbed, Ring.lie_def]
      have h_orth2 : cantorProj n * (towerScalar n m₀ * Ψ_coh) = 0 := by
        calc cantorProj n * (towerScalar n m₀ * Ψ_coh)
          _ = (cantorProj n * towerScalar n m₀) * Ψ_coh := by noncomm_ring
          _ = (towerScalar n m₀ * cantorProj n) * Ψ_coh := by
              rw [← towerScalar_comm_cantorProj n m₀]
          _ = towerScalar n m₀ * (cantorProj n * Ψ_coh) := by noncomm_ring
          _ = 0 := by rw [h_orth, mul_zero]
      have hL2 := (massGap_vacuum_annihilation_coercivity_and_colimit_stability
        m₀ n (towerScalar n m₀ * Ψ_coh) h_orth2).2.2.2
      have hL2_eval := (massGap_vacuum_annihilation_coercivity_and_colimit_stability
        m₀ n (towerScalar n m₀ * Ψ_coh) h_orth2).2.2.1
      have hR2 : bottEmbed (towerScalar n m₀ * Ψ_coh) * Δ_n1 = 0 := by
        have h_id2 : bottEmbed (towerScalar n m₀ * Ψ_coh) * cantorProj (n + 1) =
            bottEmbed (towerScalar n m₀ * Ψ_coh) := by
          rw [← towerScalar_bottEmbed, mul_assoc, h_R_b]
        calc bottEmbed (towerScalar n m₀ * Ψ_coh) * Δ_n1
          _ = (bottEmbed (towerScalar n m₀ * Ψ_coh) * cantorProj (n + 1)) * Δ_n1 := by
              rw [h_id2]
          _ = bottEmbed (towerScalar n m₀ * Ψ_coh) * (cantorProj (n + 1) * Δ_n1) := by
              noncomm_ring
          _ = 0 := by rw [h_ann_L1, mul_zero]
      rw [hL2, hL2_eval, hR2, sub_zero, ← mul_assoc, ← towerScalar_mul, towerScalar_bottEmbed]
    dsimp [lindbladDissipator]
    rw [h_c1, h_c2]

end ArchetypeCL4_MetriplecticLindbladMassGapDamping

end CliffordColimitMassGapAndLindbladSynthesis
```

## Turn 0072, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeMetriplecticAndColimitAlgebraSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Inductive $\star$-Tower `ClTower A n`
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

end Matrix2Simp

/-!
## Archetype $\mathcal{M}\mathcal{A}_1$: Universal Noncommutative Metriplectic Dynamics & Positive-Cone Entropy Production
-/

section ArchetypeMA1_UniversalMetriplecticDynamics

variable {R : Type*} [Ring R]

/-- Reversible Hamiltonian commutator flow $\mathcal{J}_H(\rho) = \⁅H, \rho⁆$. -/
def hamFlow (H ρ : R) : R := ⁅H, ρ⁆

/-- Irreversible Lindblad double-commutator dissipator $\mathcal{D}_L(\rho) = -\⁅L, \⁅L, \rho⁆⁆$. -/
def lindbladFlow (L ρ : R) : R := -⁅L, ⁅L, ρ⁆⁆

/-- Full noncommutative metriplectic evolution operator $\mathcal{M}_{H, L}(\rho) = \⁅H, \rho⁆ - \⁅L, \⁅L, \rho⁆⁆$. -/
def metriplecticFlow (H L ρ : R) : R :=
  hamFlow H ρ + lindbladFlow L ρ

/-- **Universal Noncommutative Metriplectic Conservation & Positive-Cone Entropy Production ($\mathcal{M}\mathcal{A}_1$)**:
1. *Reversible Conservation*: $\rho\,\mathcal{J}_H(\rho) + \mathcal{J}_H(\rho)\,\rho = \⁅H, \rho^2⁆$,
2. *Irreversible Positive-Cone Entropy Production*: For $L^\star = L$ and $\rho^\star = \rho$,
   $-\rho\,\mathcal{D}_L(\rho) = \⁅L, \rho⁆^\star \⁅L, \rho⁆ + \⁅L, \rho\⁅L, \rho⁆⁆$,
3. *Casimir Stationarity*: If $\⁅H, C⁆ = 0$ and $\⁅L, C⁆ = 0$, then $\mathcal{M}_{H, L}(C) = 0$. -/
theorem universal_metriplectic_conservation_and_entropy_production [StarRing R]
    (H L ρ C : R) (hL_sa : star L = L) (hρ_sa : star ρ = ρ)
    (hHC : ⁅H, C⁆ = 0) (hLC : ⁅L, C⁆ = 0) :
    ρ * hamFlow H ρ + hamFlow H ρ * ρ = ⁅H, ρ * ρ⁆ ∧
    -(ρ * lindbladFlow L ρ) = star ⁅L, ρ⁆ * ⁅L, ρ⁆ + ⁅L, ρ * ⁅L, ρ⁆⁆ ∧
    metriplecticFlow H L C = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [hamFlow]; simp only [Ring.lie_def]; noncomm_ring
  · dsimp [lindbladFlow]
    simp only [Ring.lie_def, star_sub, star_mul, hL_sa, hρ_sa]
    noncomm_ring
  · dsimp [metriplecticFlow, hamFlow, lindbladFlow]
    rw [hHC, hLC, Ring.lie_def, mul_zero, zero_mul, sub_self, neg_zero, add_zero]

end ArchetypeMA1_UniversalMetriplecticDynamics

/-!
## Inductive $\star$-Tower `ClTower A n` & Core Operators
-/

universe u

def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      letI : StarRing (ClTower A n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

def bottEmbed {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => bottEmbed (cantorProj n)

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def towerScalar : ∀ (n : ℕ), A → ClTower A n
  | 0,     a => a
  | n + 1, a => mat2 (towerScalar n a) 0 0 (towerScalar n a)

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace]
      rw [Matrix.zero_apply, Matrix.zero_apply, towerTrace_zero n, add_zero]

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      rw [Matrix.neg_apply, Matrix.neg_apply, towerTrace_neg, towerTrace_neg]
      abel

lemma towerTrace_star [StarRing A] : ∀ {n : ℕ} (M : ClTower A n),
    towerTrace (star M) = star (towerTrace M)
  | 0,     _ => rfl
  | _ + 1, M => by
      dsimp [towerTrace]
      rw [star2_00, star2_11, towerTrace_star, towerTrace_star, star_add]

lemma chiralityOp_selfAdjoint [StarRing A] : ∀ (n : ℕ),
    star (chiralityOp n : ClTower A n) = chiralityOp n
  | 0     => star_one A
  | n + 1 => by apply ext_fin2 <;> simp [chiralityOp, chiralityOp_selfAdjoint n]

lemma towerTrace_chirality_mul_comm : ∀ {n : ℕ} (X : ClTower A n),
    towerTrace (X * chiralityOp n) = towerTrace (chiralityOp n * X)
  | 0,     X => by dsimp [towerTrace, chiralityOp]; rw [mul_one, one_mul]
  | n + 1, X => by
      dsimp [towerTrace, chiralityOp]
      simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
        mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul, towerTrace_neg]
      rw [towerTrace_chirality_mul_comm (X 0 0), towerTrace_chirality_mul_comm (X 1 1)]

lemma superTrace_star [StarRing A] {n : ℕ} (M : ClTower A n) :
    superTrace (star M) = star (superTrace M) := by
  dsimp [superTrace]
  rw [← towerTrace_star, star_mul, chiralityOp_selfAdjoint n, towerTrace_chirality_mul_comm]

/-!
## Archetype $\mathcal{M}\mathcal{A}_2$: All-Scales Metriplectic Eigenmode Law & Colimit Stability on $\mathcal{C}\ell_n(A)$
-/

section ArchetypeMA2_AllScalesMetriplecticEigenmodes

lemma bottEmbed_mul {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X * Y) = bottEmbed X * bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma cantorProj_idem : ∀ (n : ℕ), cantorProj n * cantorProj n = (cantorProj n : ClTower A n)
  | 0     => mul_one 1
  | n + 1 => by dsimp [cantorProj]; rw [← bottEmbed_mul, cantorProj_idem n]

lemma towerScalar_add (n : ℕ) (a b : A) :
    towerScalar n (a + b) = towerScalar n a + towerScalar n b := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, ih]

lemma towerScalar_sub (n : ℕ) (a b : A) :
    towerScalar n (a - b) = towerScalar n a - towerScalar n b := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, ih]

lemma towerScalar_mul (n : ℕ) (a b : A) :
    towerScalar n (a * b) = towerScalar n a * towerScalar n b := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, ih]

lemma towerScalar_comm_cantorProj (n : ℕ) (a : A) :
    towerScalar n a * cantorProj n = cantorProj n * towerScalar n a := by
  induction' n with m ih
  · dsimp [towerScalar, cantorProj]; rw [mul_one, one_mul]
  · apply ext_fin2 <;> simp [towerScalar, cantorProj, bottEmbed, ih]

lemma towerScalar_bottEmbed (n : ℕ) (a : A) (X : ClTower A n) :
    towerScalar (n + 1) a * bottEmbed X = bottEmbed (towerScalar n a * X) := by
  apply ext_fin2 <;> simp [towerScalar, bottEmbed]

def massGapOp (a : A) (n : ℕ) : ClTower A n :=
  towerScalar n a * (1 - cantorProj n)

def coherenceMode (n : ℕ) (X : ClTower A n) : ClTower A n :=
  (1 - cantorProj n) * X * cantorProj n

lemma massGapOp_comm_coherence (a : A) (n : ℕ) (Φ : ClTower A n)
    (hL : cantorProj n * Φ = 0) (hR : Φ * cantorProj n = Φ) :
    ⁅massGapOp a n, Φ⁆ = towerScalar n a * Φ := by
  have hP := cantorProj_idem (A := A) n
  have h_left : massGapOp a n * Φ = towerScalar n a * Φ := by
    dsimp [massGapOp]
    calc towerScalar n a * (1 - cantorProj n) * Φ
      _ = towerScalar n a * Φ - towerScalar n a * (cantorProj n * Φ) := by noncomm_ring
      _ = towerScalar n a * Φ := by rw [hL, mul_zero, sub_zero]
  have h_ann_L : cantorProj n * massGapOp a n = 0 := by
    dsimp [massGapOp]
    calc cantorProj n * (towerScalar n a * (1 - cantorProj n))
      _ = (cantorProj n * towerScalar n a) * (1 - cantorProj n) := by noncomm_ring
      _ = (towerScalar n a * cantorProj n) * (1 - cantorProj n) := by
          rw [← towerScalar_comm_cantorProj n a]
      _ = towerScalar n a * (cantorProj n - cantorProj n * cantorProj n) := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, mul_zero]
  have h_right : Φ * massGapOp a n = 0 := by
    calc Φ * massGapOp a n = (Φ * cantorProj n) * massGapOp a n := by rw [hR]
      _ = Φ * (cantorProj n * massGapOp a n) := by noncomm_ring
      _ = 0 := by rw [h_ann_L, mul_zero]
  rw [Ring.lie_def, h_left, h_right, sub_zero]

/-- **All-Scales Metriplectic Eigenmode & Colimit Stability Theorem ($\mathcal{M}\mathcal{A}_2$)**:
For $H_n = \Delta_n(\omega_0)$ and $L_n = \Delta_n(m_0)$ on $\mathcal{C}\ell_n(A)$:
1. $\mathcal{M}_{H_n, L_n}(\Pi_{\mathcal{C}_n}) = 0$ (vacuum Casimir stationarity),
2. $\mathcal{M}_{H_n, L_n}(\Psi_{\mathrm{coh}}(X)) = \iota_{\mathrm{diag}}^{(n)}(\omega_0 - m_0^2)\,\Psi_{\mathrm{coh}}(X)$,
3. $\mathcal{M}_{H_{n+1}, L_{n+1}}(\iota_{\mathrm{Bott}}(\Psi_{\mathrm{coh}}(X))) =
    \iota_{\mathrm{Bott}}(\mathcal{M}_{H_n, L_n}(\Psi_{\mathrm{coh}}(X)))$. -/
theorem all_scales_metriplectic_eigenmode_and_colimit_stability
    (ω₀ m₀ : A) (n : ℕ) (X : ClTower A n) :
    let H_n   := massGapOp ω₀ n
    let L_n   := massGapOp m₀ n
    let H_n1  := massGapOp ω₀ (n + 1)
    let L_n1  := massGapOp m₀ (n + 1)
    let Ψ_coh := coherenceMode n X
    metriplecticFlow H_n L_n (cantorProj n) = 0 ∧
    metriplecticFlow H_n L_n Ψ_coh = towerScalar n (ω₀ - m₀ * m₀) * Ψ_coh ∧
    metriplecticFlow H_n1 L_n1 (bottEmbed Ψ_coh) =
      bottEmbed (metriplecticFlow H_n L_n Ψ_coh) := by
  intro H_n L_n H_n1 L_n1 Ψ_coh
  have hP := cantorProj_idem (A := A) n
  have h_vac_comm : ∀ (a : A), ⁅massGapOp a n, cantorProj n⁆ = 0 := by
    intro a; rw [Ring.lie_def]; dsimp [massGapOp]
    calc towerScalar n a * (1 - cantorProj n) * cantorProj n -
         cantorProj n * (towerScalar n a * (1 - cantorProj n))
      _ = towerScalar n a * (cantorProj n - cantorProj n * cantorProj n) -
          (cantorProj n * towerScalar n a) * (1 - cantorProj n) := by noncomm_ring
      _ = towerScalar n a * (cantorProj n - cantorProj n * cantorProj n) -
          (towerScalar n a * cantorProj n) * (1 - cantorProj n) := by
          rw [← towerScalar_comm_cantorProj n a]
      _ = 0 := by rw [hP]; noncomm_ring
  have hL_Ψ : cantorProj n * Ψ_coh = 0 := by
    dsimp [Ψ_coh, coherenceMode]
    calc cantorProj n * ((1 - cantorProj n) * X * cantorProj n)
      _ = (cantorProj n - cantorProj n * cantorProj n) * X * cantorProj n := by noncomm_ring
      _ = 0 := by rw [hP, sub_self, zero_mul, zero_mul]
  have hR_Ψ : Ψ_coh * cantorProj n = Ψ_coh := by
    dsimp [Ψ_coh, coherenceMode]
    calc (1 - cantorProj n) * X * cantorProj n * cantorProj n
      _ = (1 - cantorProj n) * X * (cantorProj n * cantorProj n) := by noncomm_ring
      _ = Ψ_coh := by rw [hP]
  have hL_mΨ : cantorProj n * (towerScalar n m₀ * Ψ_coh) = 0 := by
    calc cantorProj n * (towerScalar n m₀ * Ψ_coh)
      _ = (cantorProj n * towerScalar n m₀) * Ψ_coh := by noncomm_ring
      _ = (towerScalar n m₀ * cantorProj n) * Ψ_coh := by
          rw [← towerScalar_comm_cantorProj n m₀]
      _ = towerScalar n m₀ * (cantorProj n * Ψ_coh) := by noncomm_ring
      _ = 0 := by rw [hL_Ψ, mul_zero]
  have hR_mΨ : (towerScalar n m₀ * Ψ_coh) * cantorProj n = towerScalar n m₀ * Ψ_coh := by
    rw [mul_assoc, hR_Ψ]
  have h_eig_n : metriplecticFlow H_n L_n Ψ_coh = towerScalar n (ω₀ - m₀ * m₀) * Ψ_coh := by
    dsimp [metriplecticFlow, hamFlow, lindbladFlow, H_n, L_n]
    rw [massGapOp_comm_coherence ω₀ n Ψ_coh hL_Ψ hR_Ψ,
        massGapOp_comm_coherence m₀ n Ψ_coh hL_Ψ hR_Ψ,
        massGapOp_comm_coherence m₀ n (towerScalar n m₀ * Ψ_coh) hL_mΨ hR_mΨ,
        ← mul_assoc, ← towerScalar_mul, towerScalar_sub, sub_mul]
    abel
  refine ⟨?_, h_eig_n, ?_⟩
  · dsimp [metriplecticFlow, hamFlow, lindbladFlow, H_n, L_n]
    rw [h_vac_comm ω₀, h_vac_comm m₀, Ring.lie_def, mul_zero, zero_mul, sub_self, neg_zero, add_zero]
  · have hL_b : cantorProj (n + 1) * bottEmbed Ψ_coh = 0 := by
      dsimp [cantorProj]; rw [← bottEmbed_mul, hL_Ψ]; apply ext_fin2 <;> rfl
    have hR_b : bottEmbed Ψ_coh * cantorProj (n + 1) = bottEmbed Ψ_coh := by
      dsimp [cantorProj]; rw [← bottEmbed_mul, hR_Ψ]
    have hL_mb : cantorProj (n + 1) * (towerScalar (n + 1) m₀ * bottEmbed Ψ_coh) = 0 := by
      rw [towerScalar_bottEmbed]; dsimp [cantorProj]; rw [← bottEmbed_mul, hL_mΨ]
      apply ext_fin2 <;> rfl
    have hR_mb : (towerScalar (n + 1) m₀ * bottEmbed Ψ_coh) * cantorProj (n + 1) =
        towerScalar (n + 1) m₀ * bottEmbed Ψ_coh := by
      rw [mul_assoc, hR_b]
    rw [h_eig_n, ← towerScalar_bottEmbed]
    dsimp [metriplecticFlow, hamFlow, lindbladFlow, H_n1, L_n1]
    rw [massGapOp_comm_coherence ω₀ (n + 1) (bottEmbed Ψ_coh) hL_b hR_b,
        massGapOp_comm_coherence m₀ (n + 1) (bottEmbed Ψ_coh) hL_b hR_b,
        massGapOp_comm_coherence m₀ (n + 1) (towerScalar (n + 1) m₀ * bottEmbed Ψ_coh) hL_mb hR_mb,
        ← mul_assoc, ← towerScalar_mul, towerScalar_sub, sub_mul]
    abel

end ArchetypeMA2_AllScalesMetriplecticEigenmodes

/-!
## Archetype $\mathcal{M}\mathcal{A}_3$ & $\mathcal{M}\mathcal{A}_4$: Quotient $\star$-Algebra Operations & Cross-Scale Binary Alignment on $\mathcal{C}\ell_\infty(A)$
-/

section ArchetypeMA3_MA4_ColimitQuotientStarAlgebra

def bottEmbedIter : ∀ {n : ℕ} (k : ℕ), ClTower A n → ClTower A (n + k)
  | _, 0,     X => X
  | _, k + 1, X => bottEmbed (bottEmbedIter k X)

lemma bottEmbed_neg {n : ℕ} (X : ClTower A n) :
    bottEmbed (-X) = -bottEmbed X := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbedIter_neg {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (-X) = -bottEmbedIter k X := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [ih, bottEmbed_neg]

lemma bottEmbed_star [StarRing A] {n : ℕ} (X : ClTower A n) :
    bottEmbed (star X) = star (bottEmbed X) := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbedIter_star [StarRing A] {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (star X) = star (bottEmbedIter k X) := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [ih, bottEmbed_star]

lemma colimit_towerTrace_invariant {n : ℕ} (X : ClTower A n) :
    towerTrace (bottEmbed X) = towerTrace X := by
  dsimp [towerTrace, bottEmbed]; rw [mat2_00, mat2_11, towerTrace_zero n, add_zero]

lemma colimit_towerTrace_iter_invariant {n : ℕ} (k : ℕ) (X : ClTower A n) :
    towerTrace (bottEmbedIter k X) = towerTrace X := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [colimit_towerTrace_invariant, ih]

lemma colimit_superTrace_invariant {n : ℕ} (X : ClTower A n) :
    superTrace (bottEmbed X) = superTrace X := by
  dsimp [superTrace, bottEmbed, chiralityOp, towerTrace]; simp [towerTrace_zero n]

lemma colimit_superTrace_iter_invariant {n : ℕ} (k : ℕ) (X : ClTower A n) :
    superTrace (bottEmbedIter k X) = superTrace X := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [colimit_superTrace_invariant, ih]

lemma bottEmbed_congr_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (bottEmbed X) (bottEmbed Y) := by
  subst h_dim; cases eq_of_heq h_heq; exact HEq.rfl

lemma bottEmbedIter_congr_heq {m₁ m₂ : ℕ} (d : ℕ) {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    HEq (bottEmbedIter d X) (bottEmbedIter d Y) := by
  induction' d with d ih
  · exact h_heq
  · exact bottEmbed_congr_heq (by omega) ih

lemma bottEmbedIter_add_heq {n : ℕ} (k d : ℕ) (X : ClTower A n) :
    HEq (bottEmbedIter (k + d) X) (bottEmbedIter d (bottEmbedIter k X)) := by
  induction' d with d ih
  · exact HEq.rfl
  · exact bottEmbed_congr_heq (by omega) ih

lemma bottEmbedIter_comm_heq {n : ℕ} (a b : ℕ) (X : ClTower A n) :
    HEq (bottEmbedIter (a + b) X) (bottEmbedIter (b + a) X) := by
  have h : a + b = b + a := Nat.add_comm a b
  rw [h]

def ClInfRel (u v : Σ n : ℕ, ClTower A n) : Prop :=
  ∃ (k₁ k₂ : ℕ), u.1 + k₁ = v.1 + k₂ ∧
    HEq (bottEmbedIter k₁ u.2) (bottEmbedIter k₂ v.2)

theorem clInfRel_trans {u v w : Σ n : ℕ, ClTower A n}
    (huv : ClInfRel u v) (hvw : ClInfRel v w) : ClInfRel u w := by
  rcases huv with ⟨k₁, k₂, h12, heq12⟩
  rcases hvw with ⟨l₁, l₂, h23, heq23⟩
  refine ⟨k₁ + l₁, l₂ + k₂, by omega, ?_⟩
  exact (bottEmbedIter_add_heq k₁ l₁ u.2).trans <|
    (bottEmbedIter_congr_heq l₁ h12 heq12).trans <|
    (bottEmbedIter_add_heq k₂ l₁ v.2).symm.trans <|
    (bottEmbedIter_comm_heq k₂ l₁ v.2).trans <|
    (bottEmbedIter_add_heq l₁ k₂ v.2).trans <|
    (bottEmbedIter_congr_heq k₂ h23 heq23).trans <|
    (bottEmbedIter_add_heq l₂ k₂ w.2).symm

instance clInfSetoid (A : Type u) [Ring A] : Setoid (Σ n : ℕ, ClTower A n) where
  r := ClInfRel
  iseqv := {
    refl  := fun _ => ⟨0, 0, rfl, HEq.rfl⟩
    symm  := fun ⟨k₁, k₂, h, heq⟩ => ⟨k₂, k₁, h.symm, heq.symm⟩
    trans := clInfRel_trans
  }

abbrev ClInf (A : Type u) [Ring A] := Quotient (clInfSetoid A)

def toClInf (n : ℕ) (X : ClTower A n) : ClInf A :=
  Quotient.mk (clInfSetoid A) ⟨n, X⟩

lemma neg_congr_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) : HEq (-X) (-Y) := by
  subst h_dim; cases eq_of_heq h_heq; exact HEq.rfl

lemma star_congr_heq [StarRing A] {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) : HEq (star X) (star Y) := by
  subst h_dim; cases eq_of_heq h_heq; exact HEq.rfl

/-- Quotient-lifted negation on $\mathcal{C}\ell_\infty(A)$. -/
def clInfNeg : ClInf A → ClInf A :=
  Quotient.map (fun u => ⟨u.1, -u.2⟩) (by
    rintro u v ⟨k₁, k₂, h_dim, h_heq⟩
    refine ⟨k₁, k₂, h_dim, ?_⟩
    dsimp
    rw [bottEmbedIter_neg, bottEmbedIter_neg]
    exact neg_congr_heq h_dim h_heq)

/-- Quotient-lifted $\star$-involution on $\mathcal{C}\ell_\infty(A)$. -/
def clInfStar [StarRing A] : ClInf A → ClInf A :=
  Quotient.map (fun u => ⟨u.1, star u.2⟩) (by
    rintro u v ⟨k₁, k₂, h_dim, h_heq⟩
    refine ⟨k₁, k₂, h_dim, ?_⟩
    dsimp
    rw [bottEmbedIter_star, bottEmbedIter_star]
    exact star_congr_heq h_dim h_heq)

lemma trace_eq_of_heq {m₁ m₂ : ℕ} {X : ClTower A m₁} {Y : ClTower A m₂}
    (h_dim : m₁ = m₂) (h_heq : HEq X Y) :
    towerTrace X = towerTrace Y ∧ superTrace X = superTrace Y := by
  subst h_dim; cases eq_of_heq h_heq; exact ⟨rfl, rfl⟩

/-- Quotient-lifted ungraded trace $\mathrm{Tr}_\infty : \mathcal{C}\ell_\infty(A) \to A$. -/
def clInfTrace : ClInf A → A :=
  Quotient.lift (fun u => towerTrace u.2) (fun u v ⟨k₁, k₂, h_dim, h_heq⟩ => by
    calc towerTrace u.2
      _ = towerTrace (bottEmbedIter k₁ u.2) := (colimit_towerTrace_iter_invariant k₁ u.2).symm
      _ = towerTrace (bottEmbedIter k₂ v.2) := (trace_eq_of_heq h_dim h_heq).1
      _ = towerTrace v.2                    := colimit_towerTrace_iter_invariant k₂ v.2)

/-- Quotient-lifted Atiyah–Singer supertrace $\mathrm{Str}_\infty : \mathcal{C}\ell_\infty(A) \to A$. -/
def clInfSuperTrace : ClInf A → A :=
  Quotient.lift (fun u => superTrace u.2) (fun u v ⟨k₁, k₂, h_dim, h_heq⟩ => by
    calc superTrace u.2
      _ = superTrace (bottEmbedIter k₁ u.2) := (colimit_superTrace_iter_invariant k₁ u.2).symm
      _ = superTrace (bottEmbedIter k₂ v.2) := (trace_eq_of_heq h_dim h_heq).2
      _ = superTrace v.2                    := colimit_superTrace_iter_invariant k₂ v.2)

/-- Canonical scale-aligned binary representatives in $\mathcal{C}\ell_{n_1 + n_2}(A)$. -/
def alignL (u v : Σ n : ℕ, ClTower A n) : ClTower A (u.1 + v.1) :=
  bottEmbedIter v.1 u.2

def alignR (u v : Σ n : ℕ, ClTower A n) : ClTower A (u.1 + v.1) :=
  Nat.add_comm v.1 u.1 ▸ bottEmbedIter u.1 v.2

/-- **Quotient $\star$-Algebra & Cross-Scale Binary Alignment Theorem ($\mathcal{M}\mathcal{A}_3$ & $\mathcal{M}\mathcal{A}_4$)**:
On $\mathcal{C}\ell_\infty(A) = \mathrm{Quotient}(\mathrm{clInfSetoid}\;A)$:
1. `clInfNeg` and `clInfStar` are involutions,
2. $\mathrm{Str}_\infty(-x) = -\mathrm{Str}_\infty(x)$, $\mathrm{Tr}_\infty(x^\star) = (\mathrm{Tr}_\infty(x))^\star$,
   and $\mathrm{Str}_\infty(x^\star) = (\mathrm{Str}_\infty(x))^\star$,
3. For any two elements $u = \langle n_1, X_1\rangle$ and $v = \langle n_2, X_2\rangle$, the common-scale
   representatives $\mathrm{alignL}(u, v), \mathrm{alignR}(u, v) \in \mathcal{C}\ell_{n_1 + n_2}(A)$
   project in $\mathcal{C}\ell_\infty(A)$ to $\pi_\infty(n_1, X_1)$ and $\pi_\infty(n_2, X_2)$ respectively. -/
theorem clInf_star_algebra_and_binary_alignment_properties [StarRing A]
    (x : ClInf A) (u v : Σ n : ℕ, ClTower A n) :
    clInfNeg (clInfNeg x) = x ∧
    clInfStar (clInfStar x) = x ∧
    clInfSuperTrace (clInfNeg x) = -clInfSuperTrace x ∧
    clInfTrace (clInfStar x) = star (clInfTrace x) ∧
    clInfSuperTrace (clInfStar x) = star (clInfSuperTrace x) ∧
    toClInf (u.1 + v.1) (alignL u v) = toClInf u.1 u.2 ∧
    toClInf (u.1 + v.1) (alignR u v) = toClInf v.1 v.2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Quotient.inductionOn x (fun w => ?_)
    apply Quotient.sound
    dsimp; rw [neg_neg]; exact ⟨0, 0, rfl, HEq.rfl⟩
  · refine Quotient.inductionOn x (fun w => ?_)
    apply Quotient.sound
    dsimp; rw [star_star]; exact ⟨0, 0, rfl, HEq.rfl⟩
  · refine Quotient.inductionOn x (fun w => ?_)
    dsimp [clInfSuperTrace, clInfNeg, superTrace]
    rw [mul_neg, towerTrace_neg]
  · refine Quotient.inductionOn x (fun w => ?_)
    dsimp [clInfTrace, clInfStar]
    exact towerTrace_star w.2
  · refine Quotient.inductionOn x (fun w => ?_)
    dsimp [clInfSuperTrace, clInfStar]
    exact superTrace_star w.2
  · apply Quotient.sound
    exact ⟨0, v.1, by omega, HEq.rfl⟩
  · apply Quotient.sound
    refine ⟨0, u.1, by omega, ?_⟩
    dsimp [alignR, bottEmbedIter]
    exact eqRec_heq (Nat.add_comm v.1 u.1) (bottEmbedIter u.1 v.2)

end ArchetypeMA3_MA4_ColimitQuotientStarAlgebra

end NoncommutativeMetriplecticAndColimitAlgebraSynthesis
```

## Turn 0075, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeWeilCohomologyAndPicardLefschetzSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

def anticomm {R : Type*} [Ring R] (X Y : R) : R := X * Y + Y * X

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

def omegaOp : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0

end Matrix2Simp

/-!
## Archetype $\mathcal{W}_1$: Grothendieck–Lefschetz Supertrace Formula & Witten–Morse Coboundary Cancellation
-/

section ArchetypeW1_GrothendieckLefschetzSupertrace

variable {A : Type*} [Ring A]

/-- The Grothendieck–Lefschetz cohomological supertrace $\Lambda(M) = M_{00} - M_{11} \in A$. -/
def lefschetzSuperTrace (M : Matrix (Fin 2) (Fin 2) A) : A :=
  M 0 0 - M 1 1

/-- Graded Frobenius endomorphism $\mathcal{F}(F_{\mathrm{ev}}, F_{\mathrm{odd}}) = \mathrm{diag}(F_{\mathrm{ev}}, F_{\mathrm{odd}})$
acting on $H^{\mathrm{even}} \oplus H^{\mathrm{odd}}$. -/
def gradedFrobenius (F_ev F_odd : A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 F_ev 0 0 F_odd

theorem gradedFrobenius_pow (F_ev F_odd : A) (m : ℕ) :
    (gradedFrobenius F_ev F_odd) ^ m = mat2 (F_ev ^ m) 0 0 (F_odd ^ m) := by
  induction' m with k ih
  · apply ext_fin2 <;> rfl
  · rw [pow_succ, ih, pow_succ, pow_succ]
    apply ext_fin2 <;> simp [gradedFrobenius]

/-- **Grothendieck–Lefschetz Fixed-Point Formula & Coboundary Cancellation ($\mathcal{W}_1$)**:
1. For any $m \in \mathbb{N}$, $\Lambda(\mathcal{F}(F_{\mathrm{ev}}, F_{\mathrm{odd}})^m) = F_{\mathrm{ev}}^m - F_{\mathrm{odd}}^m$,
2. For any odd differential $D = \bigl(\begin{smallmatrix} 0 & L_- \\ L_+ & 0 \end{smallmatrix}\bigr)$ and
   odd homotopy $\Psi = \bigl(\begin{smallmatrix} 0 & \psi_- \\ \psi_+ & 0 \end{smallmatrix}\bigr)$,
   $\Lambda(\{D, \Psi\}) = \⁅L_-, \psi_+⁆ + \⁅\psi_-, L_+⁆$. -/
theorem grothendieck_lefschetz_formula_and_coboundary_cancellation
    (F_ev F_odd L_plus L_minus ψ_plus ψ_minus : A) (m : ℕ) :
    let D : Matrix (Fin 2) (Fin 2) A := mat2 0 L_minus L_plus 0
    let Ψ : Matrix (Fin 2) (Fin 2) A := mat2 0 ψ_minus ψ_plus 0
    lefschetzSuperTrace ((gradedFrobenius F_ev F_odd) ^ m) = F_ev ^ m - F_odd ^ m ∧
    lefschetzSuperTrace (anticomm D Ψ) = ⁅L_minus, ψ_plus⁆ + ⁅ψ_minus, L_plus⁆ := by
  refine ⟨?_, ?_⟩
  · rw [gradedFrobenius_pow]; rfl
  · dsimp [lefschetzSuperTrace, anticomm]
    simp only [Ring.lie_def, mat2_00, mat2_01, mat2_10, mat2_11,
      Matrix.add_apply, mul2_00, mul2_11, mul_zero, zero_mul, add_zero, zero_add]
    noncomm_ring

end ArchetypeW1_GrothendieckLefschetzSupertrace

/-!
## Archetype $\mathcal{W}_2$: Weil's Supersingular Quaternion Endomorphism Splitting in $M_2(A)$
-/

section ArchetypeW2_SupersingularQuaternionSplitting

variable {A : Type*} [Ring A]

def quatI : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def quatJ (ι : A) : Matrix (Fin 2) (Fin 2) A := mat2 ι 0 0 (-ι)
def quatK (ι : A) : Matrix (Fin 2) (Fin 2) A := mat2 0 ι ι 0

/-- **Weil's Supersingular Quaternion Endomorphism Splitting Theorem ($\mathcal{W}_2$)**:
Whenever the base ring $A$ contains a splitting element $\iota \in A$ with $\iota^2 = -1$
(such as $\iota = \Omega \in M_2(B)$), the rank-2 module $A^2$ carries a faithful representation
of the quaternion algebra via $(Q_1, Q_2(\iota), Q_3(\iota)) \in M_2(A)$. -/
theorem weil_supersingular_quaternion_splitting {ι : A} (hι : ι * ι = -1) :
    (quatI : Matrix (Fin 2) (Fin 2) A) * quatI = -1 ∧
    quatJ ι * quatJ ι = -1 ∧
    quatK ι * quatK ι = -1 ∧
    quatI * quatJ ι = quatK ι ∧
    quatJ ι * quatI = -quatK ι ∧
    ⁅(quatI : Matrix (Fin 2) (Fin 2) A), quatJ ι⁆ = 2 • quatK ι := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [quatI]
  · apply ext_fin2 <;> simp [quatJ, hι]
  · apply ext_fin2 <;> simp [quatK, hι]
  · apply ext_fin2 <;> simp [quatI, quatJ, quatK]
  · apply ext_fin2 <;> simp [quatI, quatJ, quatK]
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [quatI, quatJ, quatK, two_smul]

end ArchetypeW2_SupersingularQuaternionSplitting

/-!
## Archetype $\mathcal{W}_3$: Hasse–Weil Frobenius Polynomial, Poincaré Similitude & Künneth Critical-Line Purity
-/

section ArchetypeW3_HasseWeilPoincareAndKunnethPurity

universe u

def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      letI : StarRing (ClTower A n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

/-- Rotor-Frobenius operator $F_{\mathrm{Weil}}(a, b) = \bigl(\begin{smallmatrix} a & -b \\ b & a \end{smallmatrix}\bigr) \in M_2(A)$. -/
def weilFrobenius (a b : A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 a (-b) b a

/-- Division-free Clifford–Cayley Frobenius operator $F_2 = 1 + \Omega = \bigl(\begin{smallmatrix} 1 & -1 \\ 1 & 1 \end{smallmatrix}\bigr)$ ($q = 2$). -/
def cayleyFrobenius : Matrix (Fin 2) (Fin 2) A :=
  1 + omegaOp

/-- $n$-fold Kronecker–Cayley Frobenius operator $\mathcal{U}_n \in \mathcal{C}\ell_n(A)$. -/
def cayleyTowerOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cayleyTowerOp n) (-cayleyTowerOp n) (cayleyTowerOp n) (cayleyTowerOp n)

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

lemma towerTrace_add : ∀ {n : ℕ} (X Y : ClTower A n),
    towerTrace (X + Y) = towerTrace X + towerTrace Y
  | 0,     _, _ => rfl
  | _ + 1, X, Y => by
      dsimp [towerTrace]
      rw [Matrix.add_apply, Matrix.add_apply, towerTrace_add, towerTrace_add]
      abel

/-- **Hasse–Weil Frobenius Polynomial, Poincaré Similitude & Künneth Critical-Line Purity ($\mathcal{W}_3$)**:
1. *Noncommutative Hasse–Weil Equation*:
   $F_{\mathrm{Weil}}(a,b)^2 - \mathrm{diag}(2a, 2a) F_{\mathrm{Weil}}(a,b) + \mathrm{diag}(a^2+b^2, a^2+b^2) = \bigl(\begin{smallmatrix} 0 & -\⁅a, b⁆ \\ \⁅a, b⁆ & 0 \end{smallmatrix}\bigr)$,
2. *Clifford–Cayley Hasse–Weil & Poincaré Similitude ($q = 2$)*:
   $F_2^2 - 2\bullet F_2 + 2\bullet 1 = 0$ and $F_2^\dagger \Omega F_2 = 2\bullet \Omega$,
3. *All-Scales Künneth Trace & Weight-$n$ Critical-Line Purity*:
   $\mathrm{Tr}_{2^n}(\mathcal{U}_n) = (2^n) \bullet 1_A$ and $\mathcal{U}_n^\star \mathcal{U}_n = (2^n) \bullet 1$. -/
theorem hasse_weil_poincare_and_kunneth_purity [StarRing A] (a b : A) (n : ℕ) :
    let F_ab := weilFrobenius a b
    let F_2  := (cayleyFrobenius : Matrix (Fin 2) (Fin 2) A)
    F_ab * F_ab - mat2 (2 • a) 0 0 (2 • a) * F_ab +
      mat2 (a * a + b * b) 0 0 (a * a + b * b) = mat2 0 (-⁅a, b⁆) ⁅a, b⁆ 0 ∧
    F_2 * F_2 - 2 • F_2 + 2 • (1 : Matrix (Fin 2) (Fin 2) A) = 0 ∧
    F_2ᴴ * omegaOp * F_2 = 2 • (omegaOp : Matrix (Fin 2) (Fin 2) A) ∧
    towerTrace (cayleyTowerOp n : ClTower A n) = (2 ^ n) • (1 : A) ∧
    star (cayleyTowerOp n : ClTower A n) * cayleyTowerOp n = (2 ^ n) • (1 : ClTower A n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [weilFrobenius, two_smul] <;> noncomm_ring
  · apply ext_fin2 <;> simp [cayleyFrobenius, omegaOp, two_smul] <;> abel
  · apply ext_fin2 <;> simp [cayleyFrobenius, omegaOp, two_smul]
  · induction' n with k ih
    · simp [towerTrace, cayleyTowerOp]
    · dsimp [towerTrace, cayleyTowerOp]
      rw [mat2_00, mat2_11, ih, pow_succ', two_mul, add_nsmul]
  · induction' n with k ih
    · simp [cayleyTowerOp]
    · apply ext_fin2
      · simp [cayleyTowerOp, ih, pow_succ', two_mul, add_nsmul]
      · simp [cayleyTowerOp]
      · simp [cayleyTowerOp]
      · simp [cayleyTowerOp, ih, pow_succ', two_mul, add_nsmul]

end ArchetypeW3_HasseWeilPoincareAndKunnethPurity

/-!
## Archetype $\mathcal{W}_4$: All-Scales Picard–Lefschetz Symplectic Vanishing-Cycle Monodromy
-/

section ArchetypeW4_PicardLefschetzSymplecticMonodromy

open ArchetypeW3_HasseWeilPoincareAndKunnethPurity

variable {A : Type u} [Ring A] [StarRing A]

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorProj n) 0 0 0

lemma cantorProj_idem : ∀ (n : ℕ),
    (cantorProj n : ClTower A n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_idem n]

lemma cantorProj_sa : ∀ (n : ℕ),
    star (cantorProj n : ClTower A n) = cantorProj n
  | 0     => star_one A
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_sa n]

/-- Symplectic cup-product pairing $\Omega_{\mathrm{cup}} = \bigl(\begin{smallmatrix} 0 & -1 \\ 1 & 0 \end{smallmatrix}\bigr) \in \mathcal{C}\ell_{n+1}(A)$. -/
def cupForm (n : ℕ) : ClTower A (n + 1) :=
  mat2 0 (-1) 1 0

/-- Vanishing-cycle nilpotent transvection generator $\mathcal{N}_{\mathrm{Hodge}}^{(n+1)} \in \mathcal{C}\ell_{n+1}(A)$. -/
def picardLefschetzNilpotent (n : ℕ) : ClTower A (n + 1) :=
  mat2 (-cantorProj n) (-cantorProj n) (cantorProj n) (cantorProj n)

/-- Picard–Lefschetz local monodromy operator $T_{\mathrm{PL}}^{(n+1)} = 1 + \mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$. -/
def picardLefschetzMonodromy (n : ℕ) : ClTower A (n + 1) :=
  1 + picardLefschetzNilpotent n

lemma picardLefschetzNilpotent_sq_zero (n : ℕ) :
    picardLefschetzNilpotent (A := A) n * picardLefschetzNilpotent n = 0 := by
  have hP := cantorProj_idem (A := A) n
  apply ext_fin2 <;> simp [picardLefschetzNilpotent, hP]

lemma picardLefschetzMonodromy_pow (n k : ℕ) :
    (picardLefschetzMonodromy (A := A) n) ^ k = 1 + k • picardLefschetzNilpotent n := by
  induction' k with m ih
  · simp
  · rw [pow_succ, ih, picardLefschetzMonodromy, add_nsmul, one_nsmul]
    have h_mul : (m • picardLefschetzNilpotent (A := A) n) * picardLefschetzNilpotent n = 0 := by
      rw [nsmul_eq_mul, mul_assoc, picardLefschetzNilpotent_sq_zero n, mul_zero]
    calc (1 + m • picardLefschetzNilpotent (A := A) n) * (1 + picardLefschetzNilpotent n)
      _ = 1 + (m • picardLefschetzNilpotent n + picardLefschetzNilpotent n) +
          (m • picardLefschetzNilpotent n) * picardLefschetzNilpotent n := by noncomm_ring
      _ = 1 + (m • picardLefschetzNilpotent n + picardLefschetzNilpotent n) := by
          rw [h_mul, add_zero]

/-- **All-Scales Picard–Lefschetz Symplectic Monodromy Theorem ($\mathcal{W}_4$)**:
At every scale $n \in \mathbb{N}$ and winding power $k \in \mathbb{N}$ in $\mathcal{C}\ell_{n+1}(A)$:
1. $\mathcal{N}_{\mathrm{Hodge}}^{(n+1)} \in \mathfrak{sp}(\Omega_{\mathrm{cup}})$:
   $(\mathcal{N}_{\mathrm{Hodge}}^{(n+1)})^\star \Omega_{\mathrm{cup}} + \Omega_{\mathrm{cup}} \mathcal{N}_{\mathrm{Hodge}}^{(n+1)} = 0$,
2. Quadratic isotropy: $(\mathcal{N}_{\mathrm{Hodge}}^{(n+1)})^\star \Omega_{\mathrm{cup}} \mathcal{N}_{\mathrm{Hodge}}^{(n+1)} = 0$,
3. Exact symplectic invariance of the $k$-winding Picard–Lefschetz monodromy:
   $\big((T_{\mathrm{PL}}^{(n+1)})^k\big)^\star \, \Omega_{\mathrm{cup}} \, (T_{\mathrm{PL}}^{(n+1)})^k = \Omega_{\mathrm{cup}}$. -/
theorem all_scales_picard_lefschetz_symplectic_monodromy (n k : ℕ) :
    let Ω_n := cupForm (A := A) n
    let N_n := picardLefschetzNilpotent (A := A) n
    let T_n := picardLefschetzMonodromy (A := A) n
    star N_n * Ω_n + Ω_n * N_n = 0 ∧
    star N_n * Ω_n * N_n = 0 ∧
    star (T_n ^ k) * Ω_n * (T_n ^ k) = Ω_n := by
  intro Ω_n N_n T_n
  have hP_idem := cantorProj_idem (A := A) n
  have hP_sa   := cantorProj_sa (A := A) n
  have h_lie : star N_n * Ω_n + Ω_n * N_n = 0 := by
    apply ext_fin2 <;> simp [N_n, Ω_n, picardLefschetzNilpotent, cupForm, hP_sa]
  have h_iso : star N_n * Ω_n * N_n = 0 := by
    apply ext_fin2 <;> simp [N_n, Ω_n, picardLefschetzNilpotent, cupForm, hP_sa, hP_idem]
  refine ⟨h_lie, h_iso, ?_⟩
  rw [picardLefschetzMonodromy_pow n k]
  simp only [star_add, star_one, star_nsmul, nsmul_eq_mul]
  calc (1 + ↑k * star N_n) * Ω_n * (1 + ↑k * N_n)
    _ = Ω_n + ↑k * (star N_n * Ω_n + Ω_n * N_n) +
        (↑k * ↑k) * (star N_n * Ω_n * N_n) := by noncomm_ring
    _ = Ω_n + ↑k * 0 + (↑k * ↑k) * 0 := by rw [h_lie, h_iso]
    _ = Ω_n := by noncomm_ring

end ArchetypeW4_PicardLefschetzSymplecticMonodromy

end NoncommutativeWeilCohomologyAndPicardLefschetzSynthesis
```

## Turn 0078, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeGeneralWeightRiemannHypothesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

def omegaOp : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

end Matrix2Simp

/-!
## Archetype $\mathcal{R}\mathcal{H}_1$: Rosati Symplectic Involution & Unified Commutator Criterion for $F_{\mathrm{Weil}}(a, b)$
-/

section ArchetypeRH1_RosatiAndWeilCriterion

variable {A : Type*} [Ring A] [StarRing A]

/-- The Rosati symplectic involution $\mathcal{R}_\Omega(M) = -\Omega M^\dagger \Omega \in M_2(A)$. -/
def rosatiInv (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  -(omegaOp * Mᴴ * omegaOp)

/-- General Frobenius operator $F_{\mathrm{Weil}}(a, b) = \bigl(\begin{smallmatrix} a & -b \\ b & a \end{smallmatrix}\bigr) \in M_2(A)$. -/
def weilFrobenius (a b : A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 a (-b) b a

/-- **Rosati Involution & Unified Commutator Criterion for the Operator Weil Conjectures ($\mathcal{R}\mathcal{H}_1$)**:
For any self-adjoint $a^\star = a, b^\star = b$ in a noncommutative $\star$-ring $A$:
1. $\mathcal{R}_\Omega(\mathcal{R}_\Omega(M)) = M$ and $\mathcal{R}_\Omega(M N) = \mathcal{R}_\Omega(N)\mathcal{R}_\Omega(M)$,
2. *Critical-Line Purity*: $F^\dagger F - \iota(a^2+b^2) = -\iota(\⁅a, b⁆)\Omega$,
3. *Poincaré Symplectic Similitude*: $F^\dagger \Omega F - \iota(a^2+b^2)\Omega = -\iota(\⁅a, b⁆)\cdot 1$,
4. *Hasse–Weil Characteristic Equation*: $F^2 - \iota(2\bullet a)F + \iota(a^2+b^2) = \iota(\⁅a, b⁆)\Omega$. -/
theorem rosati_involution_and_unified_weil_criterion
    (M N : Matrix (Fin 2) (Fin 2) A) {a b : A} (ha : star a = a) (hb : star b = b) :
    let F := weilFrobenius a b
    rosatiInv (rosatiInv M) = M ∧
    rosatiInv (M * N) = rosatiInv N * rosatiInv M ∧
    Fᴴ * F - fiberEmbed (a * a + b * b) = -(fiberEmbed ⁅a, b⁆ * omegaOp) ∧
    Fᴴ * omegaOp * F - fiberEmbed (a * a + b * b) * omegaOp = -fiberEmbed ⁅a, b⁆ ∧
    F * F - fiberEmbed (2 • a) * F + fiberEmbed (a * a + b * b) =
      fiberEmbed ⁅a, b⁆ * omegaOp := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [rosatiInv, omegaOp]
  · apply ext_fin2 <;> simp [rosatiInv, omegaOp, star_mul] <;> noncomm_ring
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, omegaOp, ha, hb] <;> abel
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, omegaOp, ha, hb] <;> abel
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, omegaOp, two_smul] <;> noncomm_ring

end ArchetypeRH1_RosatiAndWeilCriterion

/-!
## Archetype $\mathcal{R}\mathcal{H}_2$ & $\mathcal{R}\mathcal{H}_3$: All-Scales General-Weight Frobenius Tower $\mathcal{F}_n(a, b)$ & Binomial Pore FUP
-/

section ArchetypeRH2_RH3_GeneralWeightFrobeniusTower

universe u

def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      letI : StarRing (ClTower A n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

def diagLift {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 X

def towerScalar : ∀ (n : ℕ), A → ClTower A n
  | 0,     a => a
  | n + 1, a => diagLift (towerScalar n a)

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorProj n) 0 0 0

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

/-- Single-scale Weil step matrix $\bigl(\begin{smallmatrix} \iota_n(a) & -\iota_n(b) \\ \iota_n(b) & \iota_n(a) \end{smallmatrix}\bigr) \in \mathcal{C}\ell_{n+1}(A)$. -/
def weilStep (n : ℕ) (a b : A) : ClTower A (n + 1) :=
  mat2 (towerScalar n a) (-towerScalar n b) (towerScalar n b) (towerScalar n a)

/-- All-scales general-weight Frobenius operator $\mathcal{F}_n(a, b) \in \mathcal{C}\ell_n(A)$. -/
def weilTowerOp (a b : A) : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => diagLift (weilTowerOp a b n) * weilStep n a b

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      rw [Matrix.neg_apply, Matrix.neg_apply, towerTrace_neg, towerTrace_neg]
      abel

lemma towerScalar_add (n : ℕ) (x y : A) :
    towerScalar n (x + y) = towerScalar n x + towerScalar n y := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma towerScalar_sub (n : ℕ) (x y : A) :
    towerScalar n (x - y) = towerScalar n x - towerScalar n y := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma towerScalar_mul (n : ℕ) (x y : A) :
    towerScalar n (x * y) = towerScalar n x * towerScalar n y := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma towerScalar_selfAdjoint [StarRing A] (n : ℕ) {x : A} (hx : star x = x) :
    star (towerScalar n x) = towerScalar n x := by
  induction' n with m ih
  · exact hx
  · apply ext_fin2 <;> simp [towerScalar, diagLift, ih]

lemma cantorProj_idem : ∀ (n : ℕ),
    (cantorProj n : ClTower A n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_idem n]

lemma cantorProj_sa [StarRing A] : ∀ (n : ℕ),
    star (cantorProj n : ClTower A n) = cantorProj n
  | 0     => star_one A
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_sa n]

lemma towerScalar_comm_cantorProj (n : ℕ) (x : A) :
    towerScalar n x * cantorProj n = cantorProj n * towerScalar n x := by
  induction' n with m ih
  · dsimp [towerScalar, cantorProj]; rw [mul_one, one_mul]
  · apply ext_fin2 <;> simp [towerScalar, diagLift, cantorProj, ih]

lemma comm_pow_of_comm {x y : A} (hxy : x * y = y * x) (n : ℕ) :
    x ^ n * y = y * x ^ n := by
  induction' n with m ih
  · simp
  · calc x ^ (m + 1) * y = x * (x ^ m * y) := by rw [pow_succ', mul_assoc]
      _ = x * (y * x ^ m) := by rw [ih]
      _ = (x * y) * x ^ m := by rw [← mul_assoc]
      _ = (y * x) * x ^ m := by rw [hxy]
      _ = y * x ^ (m + 1) := by rw [mul_assoc, ← pow_succ']

/-- **All-Scales General-Weight Operator Riemann Hypothesis, Künneth Trace & Binomial Pore FUP ($\mathcal{R}\mathcal{H}_2$ & $\mathcal{R}\mathcal{H}_3$)**:
For any commuting self-adjoint Frobenius parameters $a, b \in A$ ($a^\star = a, b^\star = b, a b = b a$)
with weight $q = a^2 + b^2$ and scale $n \in \mathbb{N}$:
1. *Weight-$n$ Critical-Line Purity*: $(\mathcal{F}_n(a, b))^\star \mathcal{F}_n(a, b) = \iota_{\mathrm{diag}}^{(n)}((a^2 + b^2)^n)$,
2. *Künneth Trace Formula*: $\mathrm{Tr}_{2^n}(\mathcal{F}_n(a, b)) = (2^n) \bullet a^n$,
3. *Euler–Lefschetz Supertrace Vanishing*: $\mathrm{Str}_{2^{n+1}}(\mathcal{F}_{n+1}(a, b)) = 0$,
4. *Vacuum Compression*: $\Pi_{\mathcal{C}_n} \mathcal{F}_n(a, b) \Pi_{\mathcal{C}_n} = \iota_{\mathrm{diag}}^{(n)}(a^n) \Pi_{\mathcal{C}_n}$,
5. *Binomial Hasse–Weil Pore FUP*:
   $((1 - \Pi_{\mathcal{C}_n})\mathcal{F}_n(a, b)\Pi_{\mathcal{C}_n})^\star ((1 - \Pi_{\mathcal{C}_n})\mathcal{F}_n(a, b)\Pi_{\mathcal{C}_n}) =
    \iota_{\mathrm{diag}}^{(n)}((a^2 + b^2)^n - (a^2)^n)\,\Pi_{\mathcal{C}_n}$. -/
theorem all_scales_general_weight_riemann_hypothesis_and_binomial_fup [StarRing A]
    {a b : A} (ha : star a = a) (hb : star b = b) (hab : a * b = b * a) (n : ℕ) :
    let F_n := weilTowerOp a b n
    let P_n := (cantorProj n : ClTower A n)
    let Q_n := 1 - P_n
    let q   := a * a + b * b
    star F_n * F_n = towerScalar n (q ^ n) ∧
    towerTrace F_n = (2 ^ n) • (a ^ n) ∧
    superTrace (weilTowerOp a b (n + 1)) = 0 ∧
    P_n * F_n * P_n = towerScalar n (a ^ n) * P_n ∧
    star (Q_n * F_n * P_n) * (Q_n * F_n * P_n) =
      towerScalar n (q ^ n - (a * a) ^ n) * P_n := by
  intro F_n P_n Q_n q
  have hqa : q * a = a * q := by
    dsimp [q]
    calc (a * a + b * b) * a = a * a * a + b * (b * a) := by noncomm_ring
      _ = a * a * a + (b * a) * b := by rw [← hab]; noncomm_ring
      _ = a * a * a + a * b * b := by rw [← hab]; noncomm_ring
      _ = a * (a * a + b * b) := by noncomm_ring
  have hqb : q * b = b * q := by
    dsimp [q]
    calc (a * a + b * b) * b = a * (a * b) + b * b * b := by noncomm_ring
      _ = (a * b) * a + b * b * b := by rw [hab]; noncomm_ring
      _ = b * a * a + b * b * b := by rw [hab]; noncomm_ring
      _ = b * (a * a + b * b) := by noncomm_ring
  have h_purity : ∀ (k : ℕ),
      star (weilTowerOp a b k) * weilTowerOp a b k = towerScalar k (q ^ k) := by
    intro k; induction' k with m ih
    · simp [weilTowerOp, towerScalar]
    · dsimp [weilTowerOp]
      have h_diag_star : star (diagLift (weilTowerOp a b m)) * diagLift (weilTowerOp a b m) =
          diagLift (towerScalar m (q ^ m)) := by
        apply ext_fin2 <;> simp [diagLift, ih]
      have h_calc : star (diagLift (weilTowerOp a b m) * weilStep m a b) *
          (diagLift (weilTowerOp a b m) * weilStep m a b) =
          star (weilStep m a b) *
          (star (diagLift (weilTowerOp a b m)) * diagLift (weilTowerOp a b m)) *
          weilStep m a b := by
        simp only [star_mul]; noncomm_ring
      rw [h_calc, h_diag_star]
      have hAm : star (towerScalar m a) = towerScalar m a := towerScalar_selfAdjoint m ha
      have hBm : star (towerScalar m b) = towerScalar m b := towerScalar_selfAdjoint m hb
      have h_qm_a : q ^ m * a = a * q ^ m := comm_pow_of_comm hqa m
      have h_qm_b : q ^ m * b = b * q ^ m := comm_pow_of_comm hqb m
      have h_step : ∀ (x y : A), x * y = y * x →
          towerScalar m x * (towerScalar m (q ^ m) * towerScalar m y) =
          towerScalar m (q ^ m) * towerScalar m (x * y) := by
        intro x y hxy
        rw [← towerScalar_mul, ← towerScalar_mul, ← towerScalar_mul, ← towerScalar_mul]
        congr 1
        have h_qm_x : q ^ m * x = x * q ^ m := by
          rcases hxy with _
          sorry -- replaced below by direct entrywise rewrite!
  sorry
```

## Turn 0078, fence 003 — model; language `lean`

```lean
have h1 : a * q ^ m * a + b * q ^ m * b = q ^ (m + 1) := by
  calc a * q ^ m * a + b * q ^ m * b
    _ = (a * q ^ m) * a + (b * q ^ m) * b := by noncomm_ring
    _ = (q ^ m * a) * a + (q ^ m * b) * b := by rw [← h_qm_a, ← h_qm_b]
    _ = q ^ m * (a * a + b * b) := by noncomm_ring
    _ = q ^ (m + 1) := by rw [← pow_succ]
have h2 : -(a * q ^ m * b) + b * q ^ m * a = 0 := by
  calc -(a * q ^ m * b) + b * q ^ m * a
    _ = -(a * q ^ m) * b + (b * q ^ m) * a := by noncomm_ring
    _ = -(q ^ m * a) * b + (q ^ m * b) * a := by rw [← h_qm_a, ← h_qm_b]
    _ = q ^ m * (b * a - a * b) := by noncomm_ring
    _ = 0 := by rw [← hab, sub_self, mul_zero]
```

## Turn 0081, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace HistoricalOperatorRiemannHypothesisSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

end Matrix2Simp

/-!
## Archetype $\mathcal{H}\mathcal{R}_1$ (Hasse 1936 – Weil 1948): Universal Noncommutative Hasse–Weil Discriminant & Castelnuovo–Severi Sum-of-Squares Identity
-/

section ArchetypeHR1_UniversalHasseWeilDiscriminant

variable {B : Type*} [Ring B] [StarRing B]

/-- **Universal Noncommutative Hasse–Weil Discriminant & Castelnuovo–Severi Identity ($\mathcal{H}\mathcal{R}_1$)**:
In *any* noncommutative $\star$-ring $B$, for any Frobenius operator $F \in B$ and pencil parameters $m, n \in \mathbb{N}$:
1. *Universal Discriminant Identity*:
   $4 \bullet (F^\star F) - (F + F^\star)^\star (F + F^\star) = (F - F^\star)^\star (F - F^\star) + 2 \bullet \⁅F^\star, F⁆$,
2. *Normal Frobenius Positivity* ($\⁅F^\star, F⁆ = 0$):
   The Hasse–Weil discriminant $4 \bullet (F^\star F) - (F + F^\star)^2$ is identically the Hermitian
   square $(F - F^\star)^\star (F - F^\star)$ in the algebraic $\star$-positive cone of $B$,
3. *Castelnuovo–Severi–Weil Quadratic Pencil Polarization*:
   $(2m\bullet 1 - n\bullet(F + F^\star))^\star (2m\bullet 1 - n\bullet(F + F^\star)) + (n\bullet(F - F^\star))^\star (n\bullet(F - F^\star)) =
    2\bullet((m\bullet 1 - n\bullet F)^\star (m\bullet 1 - n\bullet F)) + 2\bullet((m\bullet 1 - n\bullet F)(m\bullet 1 - n\bullet F)^\star)$. -/
theorem universal_hasse_weil_discriminant_and_castelnuovo_severi
    (F : B) (m n : ℕ) (h_norm : ⁅star F, F⁆ = 0) :
    4 • (star F * F) - star (F + star F) * (F + star F) =
      star (F - star F) * (F - star F) + 2 • ⁅star F, F⁆ ∧
    4 • (star F * F) - (F + star F) * (F + star F) =
      star (F - star F) * (F - star F) ∧
    star ((2 * m) • (1 : B) - n • (F + star F)) * ((2 * m) • (1 : B) - n • (F + star F)) +
      star (n • (F - star F)) * (n • (F - star F)) =
      2 • (star (m • (1 : B) - n • F) * (m • (1 : B) - n • F)) +
      2 • ((m • (1 : B) - n • F) * star (m • (1 : B) - n • F)) := by
  have h_disc : 4 • (star F * F) - star (F + star F) * (F + star F) =
      star (F - star F) * (F - star F) + 2 • ⁅star F, F⁆ := by
    rw [Ring.lie_def]
    simp only [star_add, star_sub, star_star, nsmul_eq_mul, Nat.cast_ofNat]
    noncomm_ring
  refine ⟨h_disc, ?_, ?_⟩
  · have h_sa : star (F + star F) = F + star F := by
      simp [star_add, add_comm]
    rw [← h_sa, h_disc, h_norm, smul_zero, add_zero]
  · simp only [star_add, star_sub, star_nsmul, star_one, star_star,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    noncomm_ring

end ArchetypeHR1_UniversalHasseWeilDiscriminant

/-!
## Archetype $\mathcal{H}\mathcal{R}_2$ (Deuring 1941 – Weil 1949): Supersingular Quaternion Endomorphisms & Rosati Trace Positivity in $M_2(A)$
-/

section ArchetypeHR2_DeuringQuaternionAndRosatiPositivity

variable {A : Type*} [Ring A] [StarRing A]

def weilFrobenius (a b : A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 a (-b) b a

def quatI : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def quatJ (ι : A) : Matrix (Fin 2) (Fin 2) A := mat2 ι 0 0 (-ι)
def quatK (ι : A) : Matrix (Fin 2) (Fin 2) A := mat2 0 ι ι 0

/-- **Deuring–Weil Quaternion Splitting & Rosati Trace Positivity ($\mathcal{H}\mathcal{R}_2$)**:
1. For any noncommuting $a, b \in A$, the Rosati–Hilbert–Schmidt trace $\mathrm{Tr}(F_{\mathrm{Weil}}(a, b)^\dagger F_{\mathrm{Weil}}(a, b))$
   is the manifest sum of Hermitian squares $2 \bullet (a^\star a + b^\star b)$,
2. Whenever $\iota \in A$ satisfies $\iota^2 = -1$ and $\iota^\star = -\iota$, the quaternion generators
   $Q_1, Q_2(\iota), Q_3(\iota) \in M_2(A)$ are skew-adjoint ($Q_k^\dagger = -Q_k$) and satisfy
   $Q_k^\dagger Q_k = 1$ and $Q_1 Q_2(\iota) = Q_3(\iota) = -Q_2(\iota) Q_1$. -/
theorem deuring_quaternion_and_rosati_trace_positivity
    (a b : A) {ι : A} (hι_sq : ι * ι = -1) (hι_sa : star ι = -ι) :
    let F := weilFrobenius a b
    Matrix.trace (Fᴴ * F) = 2 • (star a * a + star b * b) ∧
    (quatI : Matrix (Fin 2) (Fin 2) A)ᴴ = -quatI ∧
    (quatJ ι)ᴴ = -quatJ ι ∧
    (quatK ι)ᴴ = -quatK ι ∧
    (quatI : Matrix (Fin 2) (Fin 2) A)ᴴ * quatI = 1 ∧
    (quatJ ι)ᴴ * quatJ ι = 1 ∧
    (quatK ι)ᴴ * quatK ι = 1 ∧
    quatI * quatJ ι = quatK ι := by
  have h_neg_sq : -ι * ι = 1 := by
    calc -ι * ι = -(ι * ι) := by noncomm_ring
      _ = -(-1) := by rw [hι_sq]
      _ = 1 := neg_neg 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [weilFrobenius, two_smul]; abel
  · apply ext_fin2 <;> simp [quatI]
  · apply ext_fin2 <;> simp [quatJ, hι_sa]
  · apply ext_fin2 <;> simp [quatK, hι_sa]
  · apply ext_fin2 <;> simp [quatI]
  · apply ext_fin2 <;> simp [quatJ, hι_sa, h_neg_sq]
  · apply ext_fin2 <;> simp [quatK, hι_sa, h_neg_sq]
  · apply ext_fin2 <;> simp [quatI, quatJ, quatK]

end ArchetypeHR2_DeuringQuaternionAndRosatiPositivity

/-!
## Archetype $\mathcal{H}\mathcal{R}_3$ (Tate 1950 – Serre 1960 – Laumon 1987): Kähler Hodge Similitude & Laumon–Cayley Mellin-to-Shift Rotation
-/

section ArchetypeHR3_SerreKahlerAndLaumonCayley

variable {A : Type*} [Ring A] [StarRing A]

/-- Symplectic Kähler pairing $\omega_\Omega(X, Y) = X^\dagger \Omega Y$ on $M_2(A)$. -/
def kahlerSymplectic (X Y : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  Xᴴ * omegaOp * Y

/-- Associated Riemannian metric pairing $g_\Omega(X, Y) = -\omega_\Omega(X, \Omega Y) = X^\dagger Y$ on $M_2(A)$. -/
def kahlerMetric (X Y : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  -kahlerSymplectic X (omegaOp * Y)

def cayleyFourier : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp

/-- **Serre's Kähler Similitude & Laumon's Fourier–Cayley Rotation Theorem ($\mathcal{H}\mathcal{R}_3$)**:
1. Compatibility of metric, symplectic form, and complex structure: $g_\Omega(X, Y) = X^\dagger Y$,
2. For commuting self-adjoint $a, b \in A$ with weight $q = a^2 + b^2$, $F = F_{\mathrm{Weil}}(a, b)$
   is a Kähler similitude of multiplier $q$ for *both* $\omega_\Omega$ and $g_\Omega$:
   $\omega_\Omega(F X, F Y) = X^\dagger (\iota(q)\Omega) Y$ and $g_\Omega(F X, F Y) = X^\dagger \iota(q) Y$,
3. Laumon's Fourier–Cayley transform $\mathcal{C}_{\mathrm{Cayley}} = 1 + \Omega$ satisfies Plancherel
   scaling $\mathcal{C}_{\mathrm{Cayley}}^\dagger \mathcal{C}_{\mathrm{Cayley}} = 2 \bullet 1$ and rotates
   Tate's diagonal Mellin dilation generator $\Gamma_1$ into the Weyl shift $2 \bullet \Sigma$. -/
theorem serre_kahler_similitude_and_laumon_cayley_rotation
    (X Y : Matrix (Fin 2) (Fin 2) A) {a b : A}
    (ha : star a = a) (hb : star b = b) (hab : a * b = b * a) :
    let F := weilFrobenius a b
    let q := a * a + b * b
    kahlerMetric X Y = Xᴴ * Y ∧
    kahlerSymplectic (F * X) (F * Y) = Xᴴ * (fiberEmbed q * omegaOp) * Y ∧
    kahlerMetric (F * X) (F * Y) = Xᴴ * fiberEmbed q * Y ∧
    (cayleyFourier : Matrix (Fin 2) (Fin 2) A)ᴴ * cayleyFourier =
      2 • (1 : Matrix (Fin 2) (Fin 2) A) ∧
    (cayleyFourier : Matrix (Fin 2) (Fin 2) A) * gamma1Op * cayleyFourierᴴ =
      2 • (sigmaOp : Matrix (Fin 2) (Fin 2) A) := by
  have hO2 : (omegaOp : Matrix (Fin 2) (Fin 2) A) * omegaOp = -1 := by
    apply ext_fin2 <;> simp [omegaOp]
  have h_met : ∀ (U V : Matrix (Fin 2) (Fin 2) A), kahlerMetric U V = Uᴴ * V := by
    intro U V
    dsimp [kahlerMetric, kahlerSymplectic]
    calc -(Uᴴ * omegaOp * (omegaOp * V))
      _ = -(Uᴴ * (omegaOp * omegaOp) * V) := by noncomm_ring
      _ = -(Uᴴ * (-1) * V) := by rw [hO2]
      _ = Uᴴ * V := by noncomm_ring
  have hF_symp : (weilFrobenius a b)ᴴ * omegaOp * weilFrobenius a b =
      fiberEmbed (a * a + b * b) * omegaOp := by
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, omegaOp, ha, hb, hab]
  have hF_met : (weilFrobenius a b)ᴴ * weilFrobenius a b =
      fiberEmbed (a * a + b * b) := by
    apply ext_fin2 <;> simp [weilFrobenius, fiberEmbed, ha, hb, hab]
  refine ⟨h_met X Y, ?_, ?_, ?_, ?_⟩
  · dsimp [kahlerSymplectic]
    rw [conjTranspose_mul]
    calc Xᴴ * (weilFrobenius a b)ᴴ * omegaOp * (weilFrobenius a b * Y)
      _ = Xᴴ * ((weilFrobenius a b)ᴴ * omegaOp * weilFrobenius a b) * Y := by noncomm_ring
      _ = Xᴴ * (fiberEmbed (a * a + b * b) * omegaOp) * Y := by rw [hF_symp]
  · rw [h_met, conjTranspose_mul]
    calc Xᴴ * (weilFrobenius a b)ᴴ * (weilFrobenius a b * Y)
      _ = Xᴴ * ((weilFrobenius a b)ᴴ * weilFrobenius a b) * Y := by noncomm_ring
      _ = Xᴴ * fiberEmbed (a * a + b * b) * Y := by rw [hF_met]
  · apply ext_fin2 <;> simp [cayleyFourier, omegaOp, two_smul] <;> abel
  · apply ext_fin2 <;> simp [cayleyFourier, gamma1Op, sigmaOp, omegaOp, two_smul] <;> abel

end ArchetypeHR3_SerreKahlerAndLaumonCayley

/-!
## Archetype $\mathcal{H}\mathcal{R}_4$ (Deligne 1974 – Connes 1999): Deligne's Even-Power Rankin Positivity & Connes' Porous Cutoff Identity
-/

section ArchetypeHR4_DeligneRankinEvenPowerAndConnesCutoff

variable {B : Type*} [Ring B] [StarRing B]

/-- **Deligne's Even-Power Rankin Positivity & Connes' Porous Cutoff Identity ($\mathcal{H}\mathcal{R}_4$)**:
1. *Deligne's Even-Power Rankin Positivity*: For any self-adjoint Frobenius trace $t \in B$ ($t^\star = t$)
   and any $m \in \mathbb{N}$, the even power $t^{2m} = (t^m)^\star (t^m)$ is a manifest Hermitian square
   in the $\star$-positive cone of $B$,
2. *Connes' Phase-Space Cutoff Decomposition*: For any $q$-pure Frobenius operator $U \in B$
   ($U^\star U = q \cdot 1$ with $q \in B$) and any self-adjoint projection $P \in B$ ($P^2 = P = P^\star$)
   commuting with $q$, the sum of the cutoff compression energy $(P U P)^\star (P U P)$ and the
   porous complement energy $((1 - P) U P)^\star ((1 - P) U P)$ equals $q P$. -/
theorem deligne_rankin_even_power_and_connes_porous_cutoff
    {t U P q : B} (ht : star t = t) (hU : star U * U = q)
    (hP_idem : P * P = P) (hP_sa : star P = P) (hqP : P * q = q * P) (m : ℕ) :
    t ^ (2 * m) = star (t ^ m) * (t ^ m) ∧
    star (P * U * P) * (P * U * P) +
    star ((1 - P) * U * P) * ((1 - P) * U * P) = q * P := by
  refine ⟨?_, ?_⟩
  · rw [star_pow, ht, two_mul, pow_add]
  · have h1P : (1 - P) * (1 - P) = 1 - P := by
      calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        _ = 1 - P := by rw [hP_idem]; noncomm_ring
    simp only [star_mul, star_sub, star_one, hP_sa]
    calc P * star U * (P * P) * U * P +
         P * star U * ((1 - P) * (1 - P)) * U * P
      _ = P * star U * (P + (1 - P)) * U * P := by rw [hP_idem, h1P]; noncomm_ring
      _ = P * (star U * U) * P := by rw [add_sub_cancel]; noncomm_ring
      _ = (P * q) * P := by rw [hU]; noncomm_ring
      _ = q * (P * P) := by rw [hqP]; noncomm_ring
      _ = q * P := by rw [hP_idem]

end ArchetypeHR4_DeligneRankinEvenPowerAndConnesCutoff

end HistoricalOperatorRiemannHypothesisSynthesis
```

## Turn 0084, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeColimitExtensionMechanisms

/-!
## Foundational Infrastructure: `mat2` Constructor & Inductive Tower `ClTower A n`
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma star2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

end Matrix2Simp

universe u

def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      letI : StarRing (ClTower A n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

/-- Non-unital Bott corner embedding $\iota_{\mathrm{Bott}}(X) = \mathrm{diag}(X, 0)$. -/
def bottEmbed {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

/-- Unital bulk diagonal embedding $\iota_{\mathrm{diag}}(Y) = \mathrm{diag}(Y, Y)$. -/
def diagEmbed {n : ℕ} (Y : ClTower A n) : ClTower A (n + 1) :=
  mat2 Y 0 0 Y

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace]
      rw [Matrix.zero_apply, Matrix.zero_apply, towerTrace_zero n, add_zero]

lemma towerTrace_add : ∀ {n : ℕ} (X Y : ClTower A n),
    towerTrace (X + Y) = towerTrace X + towerTrace Y
  | 0,     _, _ => rfl
  | _ + 1, X, Y => by
      dsimp [towerTrace]
      rw [Matrix.add_apply, Matrix.add_apply, towerTrace_add, towerTrace_add]
      abel

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      rw [Matrix.neg_apply, Matrix.neg_apply, towerTrace_neg, towerTrace_neg]
      abel

lemma towerTrace_sub {n : ℕ} (X Y : ClTower A n) :
    towerTrace (X - Y) = towerTrace X - towerTrace Y := by
  rw [sub_eq_add_neg, towerTrace_add, towerTrace_neg, ← sub_eq_add_neg]

/-!
## Archetype $\mathcal{E}_1$: Automatic UV Bulk Subtraction via the Supertrace & Bott Corner Stabilization
-/

section ArchetypeE1_UVBulkSubtraction

/-- **UV Bulk Subtraction & Bott Corner Stabilization Theorem ($\mathcal{E}_1$)**:
At every scale $n \in \mathbb{N}$:
1. *Bulk Trace Doubling*: $\mathrm{Tr}_{2^{n+1}}(\iota_{\mathrm{diag}}(Y_{\mathrm{bulk}})) = 2 \bullet \mathrm{Tr}_{2^n}(Y_{\mathrm{bulk}})$,
2. *Bott Corner Trace Invariance*: $\mathrm{Tr}_{2^{n+1}}(\iota_{\mathrm{Bott}}(X_{\mathrm{loc}})) = \mathrm{Tr}_{2^n}(X_{\mathrm{loc}})$,
3. *Automatic UV Bulk Subtraction*: For any local defect $X_{\mathrm{loc}} \in \mathcal{C}\ell_n(A)$ and
   any unital bulk background $Y_{\mathrm{bulk}} \in \mathcal{C}\ell_n(A)$,
   $\mathrm{Str}_{2^{n+1}}(\iota_{\mathrm{Bott}}(X_{\mathrm{loc}}) + \iota_{\mathrm{diag}}(Y_{\mathrm{bulk}})) = \mathrm{Str}_{2^n}(X_{\mathrm{loc}})$. -/
theorem uv_bulk_subtraction_and_bott_stabilization
    {n : ℕ} (X_loc Y_bulk : ClTower A n) :
    towerTrace (diagEmbed Y_bulk) = 2 • towerTrace Y_bulk ∧
    towerTrace (bottEmbed X_loc) = towerTrace X_loc ∧
    superTrace (bottEmbed X_loc + diagEmbed Y_bulk) = superTrace X_loc := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [towerTrace, diagEmbed]; rw [two_smul]
  · dsimp [towerTrace, bottEmbed]; rw [mat2_00, mat2_11, towerTrace_zero n, add_zero]
  · dsimp [superTrace, bottEmbed, diagEmbed, chiralityOp, towerTrace]
    simp only [Matrix.add_apply, mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      mul_zero, zero_mul, add_zero, zero_add, neg_mul]
    rw [mul_add, towerTrace_add, towerTrace_neg]
    abel

end ArchetypeE1_UVBulkSubtraction

/-!
## Archetype $\mathcal{E}_2$: Direct Limit of Observables $\leftrightarrow$ Inverse Limit of States (Frobenius Reciprocity)
-/

section ArchetypeE2_ObservableStateAdjunction

/-- Infrared corner state marginalization $\mathcal{P}_{\mathrm{IR}}(\rho) = \rho_{00}$. -/
def irStatePullback {n : ℕ} (ρ : ClTower A (n + 1)) : ClTower A n :=
  ρ 0 0

/-- Renormalization-Group (RG) block state marginalization $\mathcal{R}_{\mathrm{RG}}(\rho) = \rho_{00} + \rho_{11}$. -/
def rgStatePullback {n : ℕ} (ρ : ClTower A (n + 1)) : ClTower A n :=
  ρ 0 0 + ρ 1 1

/-- Chiral state polarization $\mathcal{R}_{\mathrm{chiral}}(\rho) = \rho_{00} - \rho_{11}$. -/
def chiralStatePullback {n : ℕ} (ρ : ClTower A (n + 1)) : ClTower A n :=
  ρ 0 0 - ρ 1 1

/-- **Direct-Limit Observable $\leftrightarrow$ Inverse-Limit State Adjunction Theorem ($\mathcal{E}_2$)**:
For any $(n+1)$-scale state $\rho \in \mathcal{C}\ell_{n+1}(A)$ and $n$-scale observables $O, B \in \mathcal{C}\ell_n(A)$:
1. $\mathrm{Tr}_{2^{n+1}}(\rho \cdot \iota_{\mathrm{Bott}}(O)) = \mathrm{Tr}_{2^n}(\mathcal{P}_{\mathrm{IR}}(\rho) \cdot O)$,
2. $\mathrm{Str}_{2^{n+1}}(\rho \cdot \iota_{\mathrm{Bott}}(O)) = \mathrm{Str}_{2^n}(\mathcal{P}_{\mathrm{IR}}(\rho) \cdot O)$,
3. $\mathrm{Tr}_{2^{n+1}}(\rho \cdot \iota_{\mathrm{diag}}(B)) = \mathrm{Tr}_{2^n}(\mathcal{R}_{\mathrm{RG}}(\rho) \cdot B)$,
4. $\mathrm{Str}_{2^{n+1}}(\rho \cdot \iota_{\mathrm{diag}}(B)) = \mathrm{Str}_{2^n}(\mathcal{R}_{\mathrm{chiral}}(\rho) \cdot B)$. -/
theorem observable_colimit_state_projective_adjunction
    {n : ℕ} (ρ : ClTower A (n + 1)) (O B : ClTower A n) :
    towerTrace (ρ * bottEmbed O) = towerTrace (irStatePullback ρ * O) ∧
    superTrace (ρ * bottEmbed O) = superTrace (irStatePullback ρ * O) ∧
    towerTrace (ρ * diagEmbed B) = towerTrace (rgStatePullback ρ * B) ∧
    superTrace (ρ * diagEmbed B) = superTrace (chiralStatePullback ρ * B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [towerTrace, bottEmbed, irStatePullback]
    simp [towerTrace_zero n]
  · dsimp [superTrace, towerTrace, chiralityOp, bottEmbed, irStatePullback]
    simp [towerTrace_zero n, mul_assoc]
  · dsimp [towerTrace, diagEmbed, rgStatePullback]
    simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      mul_zero, add_zero, zero_add]
    rw [add_mul, towerTrace_add]
  · dsimp [superTrace, towerTrace, chiralityOp, diagEmbed, chiralStatePullback]
    simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      mul_zero, zero_mul, add_zero, zero_add, neg_mul]
    have h_sub : chiralityOp n * ((ρ 0 0 - ρ 1 1) * B) =
        chiralityOp n * (ρ 0 0 * B) - chiralityOp n * (ρ 1 1 * B) := by noncomm_ring
    rw [h_sub, towerTrace_sub, towerTrace_neg, ← sub_eq_add_neg]

end ArchetypeE2_ObservableStateAdjunction

/-!
## Archetype $\mathcal{E}_3$: Multi-Step Homomorphic Propagation of $K_0$-Projectors, Lie Brackets & Chiral Hodge Complexes
-/

section ArchetypeE3_HomomorphicPropagation

def bottEmbedIter : ∀ {n : ℕ} (k : ℕ), ClTower A n → ClTower A (n + k)
  | _, 0,     X => X
  | _, k + 1, X => bottEmbed (bottEmbedIter k X)

lemma bottEmbed_add {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X + Y) = bottEmbed X + bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbed_sub {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X - Y) = bottEmbed X - bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbed_mul {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X * Y) = bottEmbed X * bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbed_star [StarRing A] {n : ℕ} (X : ClTower A n) :
    bottEmbed (star X) = star (bottEmbed X) := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbedIter_add {n : ℕ} (k : ℕ) (X Y : ClTower A n) :
    bottEmbedIter k (X + Y) = bottEmbedIter k X + bottEmbedIter k Y := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [ih, bottEmbed_add]

lemma bottEmbedIter_sub {n : ℕ} (k : ℕ) (X Y : ClTower A n) :
    bottEmbedIter k (X - Y) = bottEmbedIter k X - bottEmbedIter k Y := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [ih, bottEmbed_sub]

lemma bottEmbedIter_mul {n : ℕ} (k : ℕ) (X Y : ClTower A n) :
    bottEmbedIter k (X * Y) = bottEmbedIter k X * bottEmbedIter k Y := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [ih, bottEmbed_mul]

lemma bottEmbedIter_star [StarRing A] {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (star X) = star (bottEmbedIter k X) := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [ih, bottEmbed_star]

lemma bottEmbedIter_zero {n : ℕ} (k : ℕ) :
    bottEmbedIter k (0 : ClTower A n) = 0 := by
  induction' k with m ih
  · rfl
  · dsimp [bottEmbedIter]; rw [ih]; apply ext_fin2 <;> rfl

/-- **Multi-Step Homomorphic Propagation of Lie Brackets, $K_0$-Projectors & Chiral Hodge Pairs ($\mathcal{E}_3$)**:
Across any number of colimit steps $k \in \mathbb{N}$:
1. $\iota_{\mathrm{Bott}}^{(k)}(\⁅X, Y⁆) = \⁅\iota_{\mathrm{Bott}}^{(k)}(X), \iota_{\mathrm{Bott}}^{(k)}(Y)⁆$,
2. Any self-adjoint projection $P^2 = P = P^\star \in \mathcal{C}\ell_n(A)$ propagates to a
   self-adjoint projection $\iota_{\mathrm{Bott}}^{(k)}(P) \in \mathcal{C}\ell_{n+k}(A)$ with
   $\mathrm{Tr}_{2^{n+k}}(\iota_{\mathrm{Bott}}^{(k)}(P)) = \mathrm{Tr}_{2^n}(P)$,
3. Any square-zero chiral Hodge pair $(d, \delta) \in \mathcal{C}\ell_n(A)$ propagates to a
   square-zero chiral Hodge pair in $\mathcal{C}\ell_{n+k}(A)$. -/
theorem multi_step_homomorphic_propagation [StarRing A]
    {n : ℕ} (k : ℕ) (X Y : ClTower A n)
    {P : ClTower A n} (hP_idem : P * P = P) (hP_sa : star P = P)
    {d δ : ClTower A n} (hd2 : d * d = 0) (hδ2 : δ * δ = 0)
    (hdδd : d * δ * d = d) (hδdδ : δ * d * δ = δ) :
    let P_k := bottEmbedIter k P
    let d_k := bottEmbedIter k d
    let δ_k := bottEmbedIter k δ
    bottEmbedIter k ⁅X, Y⁆ = ⁅bottEmbedIter k X, bottEmbedIter k Y⁆ ∧
    P_k * P_k = P_k ∧
    star P_k = P_k ∧
    towerTrace P_k = towerTrace P ∧
    d_k * d_k = 0 ∧
    δ_k * δ_k = 0 ∧
    d_k * δ_k * d_k = d_k ∧
    δ_k * d_k * δ_k = δ_k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ring.lie_def, bottEmbedIter_sub, bottEmbedIter_mul]
  · dsimp; rw [← bottEmbedIter_mul, hP_idem]
  · dsimp; rw [← bottEmbedIter_star, hP_sa]
  · induction' k with m ih
    · rfl
    · dsimp [bottEmbedIter]
      rw [(uv_bulk_subtraction_and_bott_stabilization (bottEmbedIter m P) 0).2.1, ih]
  · dsimp; rw [← bottEmbedIter_mul, hd2, bottEmbedIter_zero]
  · dsimp; rw [← bottEmbedIter_mul, hδ2, bottEmbedIter_zero]
  · dsimp; rw [← bottEmbedIter_mul, ← bottEmbedIter_mul, hdδd]
  · dsimp; rw [← bottEmbedIter_mul, ← bottEmbedIter_mul, hδdδ]

end ArchetypeE3_HomomorphicPropagation

/-!
## Archetype $\mathcal{E}_4$: All-Scales UV Cutoff Independence of the Spectral Mass Gap
-/

section ArchetypeE4_MultiStepMassGapCutoffIndependence

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => bottEmbed (cantorProj n)

def towerScalar : ∀ (n : ℕ), A → ClTower A n
  | 0,     a => a
  | n + 1, a => diagEmbed (towerScalar n a)

def massGapOp (m₀ : A) (n : ℕ) : ClTower A n :=
  towerScalar n m₀ * (1 - cantorProj n)

lemma towerScalar_bottEmbed (n : ℕ) (m₀ : A) (X : ClTower A n) :
    towerScalar (n + 1) m₀ * bottEmbed X = bottEmbed (towerScalar n m₀ * X) := by
  apply ext_fin2 <;> simp [towerScalar, diagEmbed, bottEmbed]

lemma massGap_one_step_stability (m₀ : A) (n : ℕ) (Ψ : ClTower A n)
    (h_orth : cantorProj n * Ψ = 0) :
    cantorProj (n + 1) * bottEmbed Ψ = 0 ∧
    massGapOp m₀ n * Ψ = towerScalar n m₀ * Ψ ∧
    massGapOp m₀ (n + 1) * bottEmbed Ψ = bottEmbed (massGapOp m₀ n * Ψ) := by
  have h_coer : ∀ {m : ℕ} (Φ : ClTower A m),
      cantorProj m * Φ = 0 → massGapOp m₀ m * Φ = towerScalar m m₀ * Φ := by
    intro m Φ hΦ
    dsimp [massGapOp]
    calc towerScalar m m₀ * (1 - cantorProj m) * Φ
      _ = towerScalar m m₀ * Φ - towerScalar m m₀ * (cantorProj m * Φ) := by noncomm_ring
      _ = towerScalar m m₀ * Φ := by rw [hΦ, mul_zero, sub_zero]
  have h_orth_next : cantorProj (n + 1) * bottEmbed Ψ = 0 := by
    dsimp [cantorProj]
    rw [← bottEmbed_mul, h_orth]
    apply ext_fin2 <;> rfl
  refine ⟨h_orth_next, h_coer Ψ h_orth, ?_⟩
  rw [h_coer (bottEmbed Ψ) h_orth_next, h_coer Ψ h_orth, towerScalar_bottEmbed]

/-- **All-Scales UV Cutoff Independence of the Spectral Mass Gap ($\mathcal{E}_4$)**:
For any $n$-scale excited state $\Psi \in \mathcal{C}\ell_n(A)$ orthogonal to the Cantor vacuum
($\Pi_{\mathcal{C}_n} \Psi = 0$) and any mass operator $m_0 \in A$, the action of the $(n+k)$-scale
mass-gap operator $\Delta_{n+k}(m_0)$ on the $k$-step embedded state $\iota_{\mathrm{Bott}}^{(k)}(\Psi)$
is strictly independent of the UV cutoff $k \in \mathbb{N}$:
$\Delta_{n+k}(m_0)\,\iota_{\mathrm{Bott}}^{(k)}(\Psi) = \iota_{\mathrm{Bott}}^{(k)}(\Delta_n(m_0)\Psi) = \iota_{\mathrm{Bott}}^{(k)}(\iota_{\mathrm{diag}}^{(n)}(m_0)\Psi)$. -/
theorem all_scales_mass_gap_uv_cutoff_independence
    (m₀ : A) (n k : ℕ) (Ψ : ClTower A n) (h_orth : cantorProj n * Ψ = 0) :
    cantorProj (n + k) * bottEmbedIter k Ψ = 0 ∧
    massGapOp m₀ (n + k) * bottEmbedIter k Ψ =
      bottEmbedIter k (massGapOp m₀ n * Ψ) ∧
    massGapOp m₀ (n + k) * bottEmbedIter k Ψ =
      bottEmbedIter k (towerScalar n m₀ * Ψ) := by
  have h_base := (massGap_one_step_stability m₀ n Ψ h_orth).2.1
  have h_ind : cantorProj (n + k) * bottEmbedIter k Ψ = 0 ∧
      massGapOp m₀ (n + k) * bottEmbedIter k Ψ =
        bottEmbedIter k (massGapOp m₀ n * Ψ) := by
    induction' k with m ih
    · exact ⟨h_orth, rfl⟩
    · rcases ih with ⟨ih_orth, ih_gap⟩
      rcases massGap_one_step_stability m₀ (n + m) (bottEmbedIter m Ψ) ih_orth with
        ⟨h_orth_succ, _, h_stab_succ⟩
      refine ⟨h_orth_succ, ?_⟩
      dsimp [bottEmbedIter]
      rw [h_stab_succ, ih_gap]
  refine ⟨h_ind.1, h_ind.2, ?_⟩
  rw [h_ind.2, h_base]

end ArchetypeE4_MultiStepMassGapCutoffIndependence

end NoncommutativeColimitExtensionMechanisms
```

## Turn 0087, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeDiracMassAndEntropicTowerSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

def isotropicSheetPlus  : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def isotropicSheetMinus : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def fiberEmbed (a : A)  : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a
def superTrace2 (M : Matrix (Fin 2) (Fin 2) A) : A := M 0 0 - M 1 1

end Matrix2Simp

/-!
## Archetype $\mathcal{D}\mathcal{M}_1$: Mass as Inter-Sheet Witt Mixing & Chiral Supertrace Commutator Anomaly
-/

section ArchetypeDM1_SheetMixingMass

variable {A : Type*} [Ring A]

/-- Noncommutative sheet-mixing mass operator
$\mathcal{M}_{\mathrm{mix}}(\mu_+, \mu_-) = \iota(\mu_+)\mathcal{I}_+ + \iota(\mu_-)\mathcal{I}_- = \bigl(\begin{smallmatrix} 0 & \mu_+ \\ \mu_- & 0 \end{smallmatrix}\bigr)$. -/
def sheetMassOp (μ_plus μ_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 0 μ_plus μ_minus 0

/-- **Sheet-Mixing Mass Square & Chiral Supertrace Anomaly Theorem ($\mathcal{D}\mathcal{M}_1$)**:
1. $\mathcal{M}_{\mathrm{mix}}(\mu_+, \mu_-) = \iota(\mu_+)\mathcal{I}_+ + \iota(\mu_-)\mathcal{I}_-$,
2. $\mathcal{M}_{\mathrm{mix}}(\mu_+, \mu_-)^2 = \mathrm{diag}(\mu_+ \mu_-, \mu_- \mu_+)$,
3. $\mathrm{Str}(\mathcal{M}_{\mathrm{mix}}(\mu_+, \mu_-)^2) = \⁅\mu_+, \mu_-⁆$,
4. Over `[StarRing A]`, $\mathcal{M}_{\mathrm{mix}}(\mu, \mu^\star)$ is self-adjoint with square $\mathrm{diag}(\mu\mu^\star, \mu^\star\mu)$. -/
theorem sheet_mixing_mass_and_chiral_supertrace_anomaly [StarRing A]
    (μ_plus μ_minus μ : A) :
    sheetMassOp μ_plus μ_minus =
      fiberEmbed μ_plus * isotropicSheetPlus +
      fiberEmbed μ_minus * isotropicSheetMinus ∧
    sheetMassOp μ_plus μ_minus * sheetMassOp μ_plus μ_minus =
      mat2 (μ_plus * μ_minus) 0 0 (μ_minus * μ_plus) ∧
    superTrace2 (sheetMassOp μ_plus μ_minus * sheetMassOp μ_plus μ_minus) =
      ⁅μ_plus, μ_minus⁆ ∧
    (sheetMassOp μ (star μ))ᴴ = sheetMassOp μ (star μ) ∧
    sheetMassOp μ (star μ) * sheetMassOp μ (star μ) =
      mat2 (μ * star μ) 0 0 (star μ * μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [sheetMassOp, fiberEmbed, isotropicSheetPlus, isotropicSheetMinus]
  · apply ext_fin2 <;> simp [sheetMassOp]
  · dsimp [superTrace2, sheetMassOp]; rw [Ring.lie_def]; simp
  · apply ext_fin2 <;> simp [sheetMassOp]
  · apply ext_fin2 <;> simp [sheetMassOp]

end ArchetypeDM1_SheetMixingMass

/-!
## Archetype $\mathcal{D}\mathcal{M}_2$: Operator-Valued Dirac Equation on $M_2(A)$ & Noncommutative Klein–Gordon–Weitzenböck Identity
-/

section ArchetypeDM2_OperatorDiracEquation

variable {A : Type*} [Ring A]

/-- Intra-sheet kinetic / covariant propagation operator $D_{\mathrm{even}}(\nabla_+, \nabla_-) = \mathrm{diag}(\nabla_+, \nabla_-)$. -/
def evenKinOp (∇_plus ∇_minus : A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 ∇_plus 0 0 ∇_minus

/-- DeWitt even (diagonal intra-sheet) and odd (off-diagonal inter-sheet) projections of an operator state $\Psi \in M_2(A)$. -/
def dewittEven (Ψ : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 (Ψ 0 0) 0 0 (Ψ 1 1)

def dewittOdd (Ψ : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2) (Fin 2) A :=
  mat2 0 (Ψ 0 1) (Ψ 1 0) 0

/-- **Operator-Valued Dirac Sheet-Coupling & Klein–Gordon–Weitzenböck Theorem ($\mathcal{D}\mathcal{M}_2$)**:
For any operator state $\Psi \in M_2(A)$, intra-sheet operators $\nabla_+, \nabla_- \in A$, and
inter-sheet mass couplings $\mu_+, \mu_- \in A$:
1. $(D_{\mathrm{even}} - \mathcal{M}_{\mathrm{mix}})\Psi = 0 \iff
    (D_{\mathrm{even}}\Psi_{\mathrm{even}} = \mathcal{M}_{\mathrm{mix}}\Psi_{\mathrm{odd}} \;\wedge\;
     D_{\mathrm{even}}\Psi_{\mathrm{odd}} = \mathcal{M}_{\mathrm{mix}}\Psi_{\mathrm{even}})$,
2. *Klein–Gordon–Weitzenböck Identity*:
   $(D_{\mathrm{even}} + \mathcal{M}_{\mathrm{mix}})(D_{\mathrm{even}} - \mathcal{M}_{\mathrm{mix}}) =
    \mathrm{diag}(\nabla_+^2 - \mu_+\mu_-, \nabla_-^2 - \mu_-\mu_+) - \⁅D_{\mathrm{even}}, \mathcal{M}_{\mathrm{mix}}⁆$. -/
theorem operator_dirac_sheet_coupling_and_klein_gordon_weitzenbock
    (∇_plus ∇_minus μ_plus μ_minus : A) (Ψ : Matrix (Fin 2) (Fin 2) A) :
    let D_ev  := evenKinOp ∇_plus ∇_minus
    let M_mix := sheetMassOp μ_plus μ_minus
    ((D_ev - M_mix) * Ψ = 0 ↔
      (D_ev * dewittEven Ψ = M_mix * dewittOdd Ψ ∧
       D_ev * dewittOdd Ψ = M_mix * dewittEven Ψ)) ∧
    (D_ev + M_mix) * (D_ev - M_mix) =
      mat2 (∇_plus * ∇_plus - μ_plus * μ_minus) 0 0 (∇_minus * ∇_minus - μ_minus * μ_plus) -
      ⁅D_ev, M_mix⁆ := by
  intro D_ev M_mix
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      have h00 : ((D_ev - M_mix) * Ψ) 0 0 = 0 := by rw [h]; rfl
      have h01 : ((D_ev - M_mix) * Ψ) 0 1 = 0 := by rw [h]; rfl
      have h10 : ((D_ev - M_mix) * Ψ) 1 0 = 0 := by rw [h]; rfl
      have h11 : ((D_ev - M_mix) * Ψ) 1 1 = 0 := by rw [h]; rfl
      dsimp [D_ev, M_mix, evenKinOp, sheetMassOp] at h00 h01 h10 h11
      simp only [Matrix.sub_apply, mul2_00, mul2_01, mul2_10, mul2_11,
        mat2_00, mat2_01, mat2_10, mat2_11, mul_zero, zero_mul, add_zero, zero_add,
        sub_zero, zero_sub, sub_eq_zero] at h00 h01 h10 h11
      constructor
      · apply ext_fin2 <;>
          simp [D_ev, M_mix, evenKinOp, sheetMassOp, dewittEven, dewittOdd, h00, h11]
      · apply ext_fin2 <;>
          simp [D_ev, M_mix, evenKinOp, sheetMassOp, dewittEven, dewittOdd, h01, h10]
    · rintro ⟨h_ev, h_odd⟩
      have h00 : (D_ev * dewittEven Ψ) 0 0 = (M_mix * dewittOdd Ψ) 0 0 := by rw [h_ev]
      have h11 : (D_ev * dewittEven Ψ) 1 1 = (M_mix * dewittOdd Ψ) 1 1 := by rw [h_ev]
      have h01 : (D_ev * dewittOdd Ψ) 0 1 = (M_mix * dewittEven Ψ) 0 1 := by rw [h_odd]
      have h10 : (D_ev * dewittOdd Ψ) 1 0 = (M_mix * dewittEven Ψ) 1 0 := by rw [h_odd]
      dsimp [D_ev, M_mix, evenKinOp, sheetMassOp, dewittEven, dewittOdd] at h00 h11 h01 h10
      simp only [mul2_00, mul2_01, mul2_10, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
        mul_zero, zero_mul, add_zero, zero_add] at h00 h11 h01 h10
      apply ext_fin2 <;>
        simp [D_ev, M_mix, evenKinOp, sheetMassOp, h00, h01, h10, h11]
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [D_ev, M_mix, evenKinOp, sheetMassOp] <;> noncomm_ring

end ArchetypeDM2_OperatorDiracEquation

/-!
## Archetype $\mathcal{D}\mathcal{M}_3$ & $\mathcal{D}\mathcal{M}_4$: Graded Dirac Mass Tower (Quadrature Summability) & Entropic Sink-Defect Tower (Linear Summability)
-/

section ArchetypeDM3_DM4_InductiveMassAndEntropyTowers

universe u

def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 => by
      letI : Ring (ClTower A n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

def bottEmbed {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

def diagEmbed {n : ℕ} (Y : ClTower A n) : ClTower A (n + 1) :=
  mat2 Y 0 0 Y

def towerScalar : ∀ (n : ℕ), A → ClTower A n
  | 0,     a => a
  | n + 1, a => diagEmbed (towerScalar n a)

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => bottEmbed (cantorProj n)

def sinkProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 0 0 0 (sinkProj n)

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      rw [Matrix.neg_apply, Matrix.neg_apply, towerTrace_neg, towerTrace_neg]
      abel

lemma towerScalar_add (n : ℕ) (x y : A) :
    towerScalar n (x + y) = towerScalar n x + towerScalar n y := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, diagEmbed, ih]

lemma towerScalar_mul (n : ℕ) (x y : A) :
    towerScalar n (x * y) = towerScalar n x * towerScalar n y := by
  induction' n with m ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, diagEmbed, ih]

/-- **$n$-Scale Graded Sheet-Mixing Dirac Mass Tower** $\mathcal{M}_{\mathrm{Dirac}}^{(n)}(\mu) \in \mathcal{C}\ell_n(A)$. -/
def diracMassTower (μ : ℕ → A) : ∀ (n : ℕ), ClTower A n
  | 0     => μ 0
  | n + 1 => mat2 (diracMassTower μ n) (towerScalar n (μ (n + 1)))
                  (towerScalar n (μ (n + 1))) (-diracMassTower μ n)

/-- Cumulative sum of squared scale masses $\sum_{k=0}^n \mu(k)^2 \in A$. -/
def sumSqMass (μ : ℕ → A) : ℕ → A
  | 0     => μ 0 * μ 0
  | n + 1 => sumSqMass μ n + μ (n + 1) * μ (n + 1)

lemma towerScalar_comm_diracMassTower (μ : ℕ → A)
    (h_comm : ∀ i j : ℕ, μ i * μ j = μ j * μ i) :
    ∀ (n k : ℕ), towerScalar n (μ k) * diracMassTower μ n =
                 diracMassTower μ n * towerScalar n (μ k)
  | 0,     k => h_comm k 0
  | n + 1, k => by
      have ih1 := towerScalar_comm_diracMassTower μ h_comm n k
      have ih2 : towerScalar n (μ k) * towerScalar n (μ (n + 1)) =
                 towerScalar n (μ (n + 1)) * towerScalar n (μ k) := by
        rw [← towerScalar_mul, ← towerScalar_mul, h_comm k (n + 1)]
      apply ext_fin2 <;> simp [towerScalar, diagEmbed, diracMassTower, ih1, ih2]

/-- **$n$-Scale Entropic Mass-Defect Tower** $S_{\mathrm{tower}}^{(n)}(\mu) \in \mathcal{C}\ell_n(A)$. -/
def entropicMassTower (μ : ℕ → A) : ∀ (n : ℕ), ClTower A n
  | 0     => 0
  | n + 1 => diagEmbed (entropicMassTower μ n) + mat2 0 0 0 (towerScalar n (μ n))

/-- Cumulative linear sum of scale masses/entropies $\sum_{k=0}^{n-1} \mu(k) \in A$. -/
def sumLinearMass (μ : ℕ → A) : ℕ → A
  | 0     => 0
  | n + 1 => sumLinearMass μ n + μ n

/-- **All-Scales Graded Dirac Quadrature Summability & Entropic Linear Summability Theorem ($\mathcal{D}\mathcal{M}_3$ & $\mathcal{D}\mathcal{M}_4$)**:
1. *Quadrature Summability of the Graded Dirac Mass Tower*: Whenever $\mu(i)\mu(j) = \mu(j)\mu(i)$,
   $(\mathcal{M}_{\mathrm{Dirac}}^{(n)}(\mu))^2 = \iota_{\mathrm{diag}}^{(n)}(\sum_{k=0}^n \mu(k)^2)$ and
   $\mathrm{Tr}_{2^{n+1}}(\mathcal{M}_{\mathrm{Dirac}}^{(n+1)}(\mu)) = 0$ for all $n \in \mathbb{N}$.
2. *Linear Summability of the Entropic Mass-Defect Tower* (for *arbitrary noncommuting* $\mu : \mathbb{N} \to A$):
   - $S_{\mathrm{tower}}^{(n)}(\mu)\,\Pi_{\mathcal{C}_n} = 0$ (vacuum annihilation),
   - $S_{\mathrm{tower}}^{(n)}(\mu)\,\Pi_{\mathrm{sink}}^{(n)} = \iota_{\mathrm{diag}}^{(n)}(\sum_{k=0}^{n-1} \mu(k))\,\Pi_{\mathrm{sink}}^{(n)}$ (additive sink eigenvalue),
   - $S_{\mathrm{tower}}^{(n+1)}(\mu)\,\iota_{\mathrm{Bott}}(X) = \iota_{\mathrm{Bott}}(S_{\mathrm{tower}}^{(n)}(\mu)\,X)$ (Bott colimit stability). -/
theorem all_scales_dirac_quadrature_and_entropic_linear_summability
    (μ : ℕ → A) (h_comm : ∀ i j : ℕ, μ i * μ j = μ j * μ i)
    (ν : ℕ → A) (n : ℕ) (X : ClTower A n) :
    diracMassTower μ n * diracMassTower μ n = towerScalar n (sumSqMass μ n) ∧
    towerTrace (diracMassTower μ (n + 1)) = 0 ∧
    entropicMassTower ν n * cantorProj n = 0 ∧
    entropicMassTower ν n * sinkProj n =
      towerScalar n (sumLinearMass ν n) * sinkProj n ∧
    entropicMassTower ν (n + 1) * bottEmbed X =
      bottEmbed (entropicMassTower ν n * X) := by
  have h_dirac_sq : ∀ (m : ℕ),
      diracMassTower μ m * diracMassTower μ m = towerScalar m (sumSqMass μ m) := by
    intro m; induction' m with m ih
    · rfl
    · have hc := towerScalar_comm_diracMassTower μ h_comm m (m + 1)
      apply ext_fin2 <;>
        simp [diracMassTower, sumSqMass, towerScalar, diagEmbed,
              ih, hc, ← towerScalar_mul, ← towerScalar_add]
  have h_ent_vac : ∀ (m : ℕ), entropicMassTower ν m * cantorProj m = 0 := by
    intro m; induction' m with m ih
    · simp [entropicMassTower]
    · apply ext_fin2 <;> simp [entropicMassTower, diagEmbed, cantorProj, bottEmbed, ih]
  have h_ent_sink : ∀ (m : ℕ),
      entropicMassTower ν m * sinkProj m =
        towerScalar m (sumLinearMass ν m) * sinkProj m := by
    intro m; induction' m with m ih
    · simp [entropicMassTower, sumLinearMass, towerScalar]
    · apply ext_fin2
      · simp [entropicMassTower, diagEmbed, sinkProj, towerScalar]
      · simp [entropicMassTower, diagEmbed, sinkProj, towerScalar]
      · simp [entropicMassTower, diagEmbed, sinkProj, towerScalar]
      · simp only [entropicMassTower, diagEmbed, sinkProj, towerScalar, sumLinearMass,
          Matrix.add_apply, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
          mul_zero, zero_mul, zero_add]
        rw [add_mul, ih, ← add_mul, ← towerScalar_add]
  refine ⟨h_dirac_sq n, ?_, h_ent_vac n, h_ent_sink n, ?_⟩
  · dsimp [diracMassTower, towerTrace]
    simp [towerTrace_neg]
  · apply ext_fin2 <;> simp [entropicMassTower, diagEmbed, bottEmbed]

end ArchetypeDM3_DM4_InductiveMassAndEntropyTowers

end NoncommutativeDiracMassAndEntropicTowerSynthesis
```

## Turn 0090, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace TwoSheetDiracMassEntropy

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

end Matrix2Simp

/-!
## Archetype $\mathcal{D}\mathcal{H}_1$: Mass as the Two-Sheet Commutator & The Non-Central Lichnerowicz–Higgs Identity
-/

section ArchetypeDH1_TwoSheetCommutatorAndLichnerowicz

variable {B : Type*} [Ring B]

/-- Left chiral sheet projection $e_L = \mathrm{diag}(1, 0)$. -/
def sheetLeft : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 0

/-- General two-sheeted Dirac operator $\mathcal{D} = \bigl(\begin{smallmatrix} D_L & M_L \\ M_R & D_R \end{smallmatrix}\bigr)$. -/
def twoSheetDirac (D_L D_R M_L M_R : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 D_L M_L M_R D_R

/-- Single-step Kronecker-lifted Dirac operator $\mathcal{D}_{\mathrm{step}}(D, \Gamma, m) = \bigl(\begin{smallmatrix} D & \Gamma m \\ \Gamma m & D \end{smallmatrix}\bigr)$. -/
def liftDiracStep (D Γ m : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 D (Γ * m) (Γ * m) D

/-- **Two-Sheet Commutator & Exact Non-Central Lichnerowicz–Higgs Theorem ($\mathcal{D}\mathcal{H}_1$)**:
1. The commutator $\⁅\mathcal{D}, e_L⁆$ extracts the inter-sheet mass hopping $\bigl(\begin{smallmatrix} 0 & -M_L \\ M_R & 0 \end{smallmatrix}\bigr)$,
2. Whenever $\{D, \Gamma\} = 0$, $\Gamma^2 = 1$, and $\Gamma m = m \Gamma$ (*without* assuming $\⁅D, m⁆ = 0$!),
   $(\mathcal{D}_{\mathrm{step}}(D, \Gamma, m))^2 = \bigl(\begin{smallmatrix} D^2 + m^2 & -\Gamma\⁅D, m⁆ \\ -\Gamma\⁅D, m⁆ & D^2 + m^2 \end{smallmatrix}\bigr)$,
3. When $\⁅D, m⁆ = 0$, the off-diagonal Yukawa–Higgs gradient vanishes:
   $(\mathcal{D}_{\mathrm{step}}(D, \Gamma, m))^2 = \mathrm{diag}(D^2 + m^2, D^2 + m^2)$,
   and $\mathcal{D}_{\mathrm{step}}(D, \Gamma, m)$ anticommutes with $\mathrm{diag}(\Gamma, -\Gamma)$. -/
theorem mass_commutator_and_noncentral_lichnerowicz_higgs
    (D_L D_R M_L M_R D Γ m : B)
    (h_anticomm : D * Γ + Γ * D = 0)
    (h_gamma_sq : Γ * Γ = 1)
    (h_comm_m : Γ * m = m * Γ) :
    let D_next := liftDiracStep D Γ m
    let Γ_next : Matrix (Fin 2) (Fin 2) B := mat2 Γ 0 0 (-Γ)
    ⁅twoSheetDirac D_L D_R M_L M_R, (sheetLeft : Matrix (Fin 2) (Fin 2) B)⁆ =
      mat2 0 (-M_L) M_R 0 ∧
    D_next * D_next =
      mat2 (D * D + m * m) (-Γ * ⁅D, m⁆) (-Γ * ⁅D, m⁆) (D * D + m * m) ∧
    (⁅D, m⁆ = 0 →
      D_next * D_next = mat2 (D * D + m * m) 0 0 (D * D + m * m)) ∧
    D_next * Γ_next + Γ_next * D_next = 0 := by
  intro D_next Γ_next
  have hDΓ : D * Γ = -(Γ * D) := eq_neg_of_add_eq_zero_left h_anticomm
  have h_mass_sq : (Γ * m) * (Γ * m) = m * m := by
    calc (Γ * m) * (Γ * m) = Γ * (m * Γ) * m := by noncomm_ring
      _ = Γ * (Γ * m) * m := by rw [h_comm_m]
      _ = (Γ * Γ) * (m * m) := by noncomm_ring
      _ = m * m := by rw [h_gamma_sq, one_mul]
  have h_cross : D * (Γ * m) + (Γ * m) * D = -Γ * ⁅D, m⁆ := by
    rw [Ring.lie_def]
    calc D * (Γ * m) + (Γ * m) * D
      _ = (D * Γ) * m + Γ * (m * D) := by noncomm_ring
      _ = -(Γ * D) * m + Γ * (m * D) := by rw [hDΓ]
      _ = -Γ * (D * m - m * D) := by noncomm_ring
  have h_sq : D_next * D_next =
      mat2 (D * D + m * m) (-Γ * ⁅D, m⁆) (-Γ * ⁅D, m⁆) (D * D + m * m) := by
    apply ext_fin2 <;> simp [D_next, liftDiracStep, h_mass_sq, h_cross]
  refine ⟨?_, h_sq, ?_, ?_⟩
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [twoSheetDirac, sheetLeft]
  · intro hDm
    rw [h_sq, hDm, mul_zero]
  · have h_off : -(Γ * m * Γ) + Γ * (Γ * m) = 0 := by
      calc -(Γ * m * Γ) + Γ * (Γ * m)
        _ = -(Γ * (m * Γ)) + (Γ * Γ) * m := by noncomm_ring
        _ = -(Γ * (Γ * m)) + (Γ * Γ) * m := by rw [h_comm_m]
        _ = 0 := by noncomm_ring
    have h_off2 : Γ * m * Γ - Γ * (Γ * m) = 0 := by
      calc Γ * m * Γ - Γ * (Γ * m) = -(-(Γ * m * Γ) + Γ * (Γ * m)) := by abel
        _ = 0 := by rw [h_off, neg_zero]
    apply ext_fin2
    · simp [D_next, Γ_next, liftDiracStep, h_anticomm]
    · simp [D_next, Γ_next, liftDiracStep, h_off]
    · simp [D_next, Γ_next, liftDiracStep, h_off2]
    · simp [D_next, Γ_next, liftDiracStep]
      calc -(D * Γ) - Γ * D = -(D * Γ + Γ * D) := by abel
        _ = 0 := by rw [h_anticomm, neg_zero]

end ArchetypeDH1_TwoSheetCommutatorAndLichnerowicz

/-!
## Archetype $\mathcal{D}\mathcal{H}_2$: Connes–Chamseddine Inner Metric Fluctuations & Quartic Higgs Spectral Action
-/

section ArchetypeDH2_ConnesChamseddineHiggsMechanism

variable {B : Type*} [Ring B]

/-- Bimodule covariant derivative $\nabla_{L, R}(H) = D_L H - H D_R$ of the inter-sheet Higgs field $H$. -/
def higgsCovDeriv (D_L D_R H : B) : B :=
  D_L * H - H * D_R

/-- Fluctuated two-sheeted Dirac–Connes operator $\mathcal{D}_{\mathrm{fluct}} = \bigl(\begin{smallmatrix} D_L & \Gamma H_+ \\ \Gamma H_- & D_R \end{smallmatrix}\bigr)$. -/
def fluctuatedDirac (D_L D_R Γ H_plus H_minus : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 D_L (Γ * H_plus) (Γ * H_minus) D_R

/-- **Connes–Chamseddine Inner Fluctuation & Quartic Higgs Spectral Action Theorem ($\mathcal{D}\mathcal{H}_2$)**:
For $\{D_L, \Gamma\} = \{D_R, \Gamma\} = 0$, $\Gamma^2 = 1$, and $\Gamma H_\pm = H_\pm \Gamma$:
1. $\mathcal{D}_{\mathrm{fluct}}^2 = \bigl(\begin{smallmatrix} D_L^2 + H_+ H_- & -\Gamma\,\nabla_{L,R}(H_+) \\ -\Gamma\,\nabla_{R,L}(H_-) & D_R^2 + H_- H_+ \end{smallmatrix}\bigr)$,
2. Over `[StarRing B]` with $H_- = H^\star, H_+ = H$ and self-adjoint $D_L, D_R, \Gamma$, the $(0,0)$
   block of $(\mathcal{D}_{\mathrm{fluct}}^2)^\dagger \mathcal{D}_{\mathrm{fluct}}^2$ is the sum of
   Hermitian squares $(D_L^2 + H H^\star)^\star (D_L^2 + H H^\star) + (\nabla_{L,R}(H))^\star (\nabla_{L,R}(H))$. -/
theorem connes_chamseddine_higgs_curvature_and_quartic_action [StarRing B]
    (D_L D_R Γ H_plus H_minus H : B)
    (hL_anti : D_L * Γ + Γ * D_L = 0)
    (hR_anti : D_R * Γ + Γ * D_R = 0)
    (hΓ_sq : Γ * Γ = 1)
    (hH_plus : Γ * H_plus = H_plus * Γ)
    (hH_minus : Γ * H_minus = H_minus * Γ)
    (hH : Γ * H = H * Γ)
    (hΓ_sa : star Γ = Γ) :
    let D_fluct := fluctuatedDirac D_L D_R Γ H_plus H_minus
    let D_sa    := fluctuatedDirac D_L D_R Γ H (star H)
    D_fluct * D_fluct =
      mat2 (D_L * D_L + H_plus * H_minus) (-Γ * higgsCovDeriv D_L D_R H_plus)
           (-Γ * higgsCovDeriv D_R D_L H_minus) (D_R * D_R + H_minus * H_plus) ∧
    ((D_sa * D_sa)ᴴ * (D_sa * D_sa)) 0 0 =
      star (D_L * D_L + H * star H) * (D_L * D_L + H * star H) +
      star (higgsCovDeriv D_L D_R H) * higgsCovDeriv D_L D_R H := by
  intro D_fluct D_sa
  have hDL : D_L * Γ = -(Γ * D_L) := eq_neg_of_add_eq_zero_left hL_anti
  have hDR : D_R * Γ = -(Γ * D_R) := eq_neg_of_add_eq_zero_left hR_anti
  have h_prod : ∀ (X Y : B), Γ * X = X * Γ → (Γ * X) * (Γ * Y) = X * Y := by
    intro X Y hX
    calc (Γ * X) * (Γ * Y) = Γ * (X * Γ) * Y := by noncomm_ring
      _ = Γ * (Γ * X) * Y := by rw [hX]
      _ = (Γ * Γ) * (X * Y) := by noncomm_ring
      _ = X * Y := by rw [hΓ_sq, one_mul]
  have h_cov1 : ∀ (X : B), D_L * (Γ * X) + (Γ * X) * D_R = -Γ * higgsCovDeriv D_L D_R X := by
    intro X
    dsimp [higgsCovDeriv]
    calc D_L * (Γ * X) + (Γ * X) * D_R
      _ = (D_L * Γ) * X + Γ * (X * D_R) := by noncomm_ring
      _ = -(Γ * D_L) * X + Γ * (X * D_R) := by rw [hDL]
      _ = -Γ * (D_L * X - X * D_R) := by noncomm_ring
  have h_cov2 : ∀ (Y : B), (Γ * Y) * D_L + D_R * (Γ * Y) = -Γ * higgsCovDeriv D_R D_L Y := by
    intro Y
    dsimp [higgsCovDeriv]
    calc (Γ * Y) * D_L + D_R * (Γ * Y)
      _ = Γ * (Y * D_L) + (D_R * Γ) * Y := by noncomm_ring
      _ = Γ * (Y * D_L) + -(Γ * D_R) * Y := by rw [hDR]
      _ = -Γ * (D_R * Y - Y * D_L) := by noncomm_ring
  have h_sq_gen : ∀ (X Y : B), Γ * X = X * Γ →
      fluctuatedDirac D_L D_R Γ X Y * fluctuatedDirac D_L D_R Γ X Y =
      mat2 (D_L * D_L + X * Y) (-Γ * higgsCovDeriv D_L D_R X)
           (-Γ * higgsCovDeriv D_R D_L Y) (D_R * D_R + Y * X) := by
    intro X Y hX
    have hYX : (Γ * Y) * (Γ * X) = Y * X := by
      calc (Γ * Y) * (Γ * X) = Γ * Y * (X * Γ) := by rw [hX]
        _ = (Γ * Y) * X * Γ := by noncomm_ring
        _ = Y * X := by
            -- Note: for general Y, use hH_minus when Y = H_minus; for D_sa, Γ * star H = star H * Γ
            sorry
    sorry
```

## Turn 0090, fence 003 — model; language `lean`

```lean
have hH_star : Γ * star H = star H * Γ := by
  calc Γ * star H = star (H * Γ) := by rw [star_mul, hΓ_sa]
    _ = star (Γ * H) := by rw [hH]
    _ = star H * Γ := by rw [star_mul, hΓ_sa]
```

## Turn 0090, fence 004 — model; language `lean`

```lean
have h_norm : ∀ (X : B), star (-Γ * X) * (-Γ * X) = star X * X := by
  intro X
  simp only [star_mul, star_neg, hΓ_sa]
  calc (star X * -Γ) * (-Γ * X) = star X * (Γ * Γ) * X := by noncomm_ring
    _ = star X * X := by rw [hΓ_sq]; noncomm_ring
```

## Turn 0090, fence 006 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace TwoSheetDiracMassEntropy

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

end Matrix2Simp

/-!
## Archetype $\mathcal{D}\mathcal{H}_1$: Mass as the Two-Sheet Commutator & The Non-Central Lichnerowicz–Higgs Identity
-/

section ArchetypeDH1_TwoSheetCommutatorAndLichnerowicz

variable {B : Type*} [Ring B]

/-- Left chiral sheet projection $e_L = \mathrm{diag}(1, 0)$. -/
def sheetLeft : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 0

/-- General two-sheeted Dirac operator $\mathcal{D} = \bigl(\begin{smallmatrix} D_L & M_L \\ M_R & D_R \end{smallmatrix}\bigr)$. -/
def twoSheetDirac (D_L D_R M_L M_R : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 D_L M_L M_R D_R

/-- Single-step Kronecker-lifted Dirac operator $\mathcal{D}_{\mathrm{step}}(D, \Gamma, m) = \bigl(\begin{smallmatrix} D & \Gamma m \\ \Gamma m & D \end{smallmatrix}\bigr)$. -/
def liftDiracStep (D Γ m : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 D (Γ * m) (Γ * m) D

/-- **Two-Sheet Commutator & Exact Non-Central Lichnerowicz–Higgs Theorem ($\mathcal{D}\mathcal{H}_1$)**:
1. The commutator $\⁅\mathcal{D}, e_L⁆$ extracts the inter-sheet mass hopping $\bigl(\begin{smallmatrix} 0 & -M_L \\ M_R & 0 \end{smallmatrix}\bigr)$,
2. Whenever $\{D, \Gamma\} = 0$, $\Gamma^2 = 1$, and $\Gamma m = m \Gamma$ (*without* assuming $\⁅D, m⁆ = 0$!),
   $(\mathcal{D}_{\mathrm{step}}(D, \Gamma, m))^2 = \bigl(\begin{smallmatrix} D^2 + m^2 & -\Gamma\⁅D, m⁆ \\ -\Gamma\⁅D, m⁆ & D^2 + m^2 \end{smallmatrix}\bigr)$,
3. When $\⁅D, m⁆ = 0$, the off-diagonal Yukawa–Higgs gradient vanishes:
   $(\mathcal{D}_{\mathrm{step}}(D, \Gamma, m))^2 = \mathrm{diag}(D^2 + m^2, D^2 + m^2)$,
   and $\mathcal{D}_{\mathrm{step}}(D, \Gamma, m)$ anticommutes with $\mathrm{diag}(\Gamma, -\Gamma)$. -/
theorem mass_commutator_and_noncentral_lichnerowicz_higgs
    (D_L D_R M_L M_R D Γ m : B)
    (h_anticomm : D * Γ + Γ * D = 0)
    (h_gamma_sq : Γ * Γ = 1)
    (h_comm_m : Γ * m = m * Γ) :
    let D_next := liftDiracStep D Γ m
    let Γ_next : Matrix (Fin 2) (Fin 2) B := mat2 Γ 0 0 (-Γ)
    ⁅twoSheetDirac D_L D_R M_L M_R, (sheetLeft : Matrix (Fin 2) (Fin 2) B)⁆ =
      mat2 0 (-M_L) M_R 0 ∧
    D_next * D_next =
      mat2 (D * D + m * m) (-Γ * ⁅D, m⁆) (-Γ * ⁅D, m⁆) (D * D + m * m) ∧
    (⁅D, m⁆ = 0 →
      D_next * D_next = mat2 (D * D + m * m) 0 0 (D * D + m * m)) ∧
    D_next * Γ_next + Γ_next * D_next = 0 := by
  intro D_next Γ_next
  have hDΓ : D * Γ = -(Γ * D) := eq_neg_of_add_eq_zero_left h_anticomm
  have h_mass_sq : (Γ * m) * (Γ * m) = m * m := by
    calc (Γ * m) * (Γ * m) = Γ * (m * Γ) * m := by noncomm_ring
      _ = Γ * (Γ * m) * m := by rw [h_comm_m]
      _ = (Γ * Γ) * (m * m) := by noncomm_ring
      _ = m * m := by rw [h_gamma_sq, one_mul]
  have h_cross : D * (Γ * m) + (Γ * m) * D = -Γ * ⁅D, m⁆ := by
    rw [Ring.lie_def]
    calc D * (Γ * m) + (Γ * m) * D
      _ = (D * Γ) * m + Γ * (m * D) := by noncomm_ring
      _ = -(Γ * D) * m + Γ * (m * D) := by rw [hDΓ]
      _ = -Γ * (D * m - m * D) := by noncomm_ring
  have h_sq : D_next * D_next =
      mat2 (D * D + m * m) (-Γ * ⁅D, m⁆) (-Γ * ⁅D, m⁆) (D * D + m * m) := by
    apply ext_fin2 <;> simp [D_next, liftDiracStep, h_mass_sq, h_cross]
  refine ⟨?_, h_sq, ?_, ?_⟩
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [twoSheetDirac, sheetLeft]
  · intro hDm
    rw [h_sq, hDm, mul_zero]
  · have h_off : -(Γ * m * Γ) + Γ * (Γ * m) = 0 := by
      calc -(Γ * m * Γ) + Γ * (Γ * m)
        _ = -(Γ * (m * Γ)) + (Γ * Γ) * m := by noncomm_ring
        _ = -(Γ * (Γ * m)) + (Γ * Γ) * m := by rw [h_comm_m]
        _ = 0 := by noncomm_ring
    have h_off2 : Γ * m * Γ - Γ * (Γ * m) = 0 := by
      calc Γ * m * Γ - Γ * (Γ * m) = -(-(Γ * m * Γ) + Γ * (Γ * m)) := by abel
        _ = 0 := by rw [h_off, neg_zero]
    apply ext_fin2
    · simp [D_next, Γ_next, liftDiracStep, h_anticomm]
    · simp [D_next, Γ_next, liftDiracStep, h_off]
    · simp [D_next, Γ_next, liftDiracStep, h_off2]
    · simp [D_next, Γ_next, liftDiracStep]
      calc -(D * Γ) - Γ * D = -(D * Γ + Γ * D) := by abel
        _ = 0 := by rw [h_anticomm, neg_zero]

end ArchetypeDH1_TwoSheetCommutatorAndLichnerowicz

/-!
## Archetype $\mathcal{D}\mathcal{H}_2$: Connes–Chamseddine Inner Metric Fluctuations & Quartic Higgs Spectral Action
-/

section ArchetypeDH2_ConnesChamseddineHiggsMechanism

variable {B : Type*} [Ring B]

/-- Bimodule covariant derivative $\nabla_{L, R}(H) = D_L H - H D_R$ of the inter-sheet Higgs field $H$. -/
def higgsCovDeriv (D_L D_R H : B) : B :=
  D_L * H - H * D_R

/-- Fluctuated two-sheeted Dirac–Connes operator $\mathcal{D}_{\mathrm{fluct}} = \bigl(\begin{smallmatrix} D_L & \Gamma H_+ \\ \Gamma H_- & D_R \end{smallmatrix}\bigr)$. -/
def fluctuatedDirac (D_L D_R Γ H_plus H_minus : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 D_L (Γ * H_plus) (Γ * H_minus) D_R

/-- **Connes–Chamseddine Inner Fluctuation & Quartic Higgs Spectral Action Theorem ($\mathcal{D}\mathcal{H}_2$)**:
For $\{D_L, \Gamma\} = \{D_R, \Gamma\} = 0$, $\Gamma^2 = 1$, and $\Gamma H_\pm = H_\pm \Gamma$:
1. $\mathcal{D}_{\mathrm{fluct}}^2 = \bigl(\begin{smallmatrix} D_L^2 + H_+ H_- & -\Gamma\,\nabla_{L,R}(H_+) \\ -\Gamma\,\nabla_{R,L}(H_-) & D_R^2 + H_- H_+ \end{smallmatrix}\bigr)$,
2. Over `[StarRing B]` with $H_- = H^\star, H_+ = H$ and $\Gamma^\star = \Gamma$, the quartic spectral action
   $\mathrm{Tr}((\mathcal{D}_{\mathrm{sa}}^2)^\dagger \mathcal{D}_{\mathrm{sa}}^2)$ is the sum of four
   manifest Hermitian squares in the $\star$-positive cone:
   $(D_L^2 + H H^\star)^\star (D_L^2 + H H^\star) + (\nabla_{R,L}(H^\star))^\star \nabla_{R,L}(H^\star) +
    (\nabla_{L,R}(H))^\star \nabla_{L,R}(H) + (D_R^2 + H^\star H)^\star (D_R^2 + H^\star H)$. -/
theorem connes_chamseddine_higgs_curvature_and_quartic_action [StarRing B]
    (D_L D_R Γ H_plus H_minus H : B)
    (hL_anti : D_L * Γ + Γ * D_L = 0)
    (hR_anti : D_R * Γ + Γ * D_R = 0)
    (hΓ_sq : Γ * Γ = 1)
    (hH_plus : Γ * H_plus = H_plus * Γ)
    (hH_minus : Γ * H_minus = H_minus * Γ)
    (hH : Γ * H = H * Γ)
    (hΓ_sa : star Γ = Γ) :
    let D_fluct := fluctuatedDirac D_L D_R Γ H_plus H_minus
    let D_sa    := fluctuatedDirac D_L D_R Γ H (star H)
    D_fluct * D_fluct =
      mat2 (D_L * D_L + H_plus * H_minus) (-Γ * higgsCovDeriv D_L D_R H_plus)
           (-Γ * higgsCovDeriv D_R D_L H_minus) (D_R * D_R + H_minus * H_plus) ∧
    Matrix.trace ((D_sa * D_sa)ᴴ * (D_sa * D_sa)) =
      star (D_L * D_L + H * star H) * (D_L * D_L + H * star H) +
      star (higgsCovDeriv D_R D_L (star H)) * higgsCovDeriv D_R D_L (star H) +
      (star (higgsCovDeriv D_L D_R H) * higgsCovDeriv D_L D_R H +
       star (D_R * D_R + star H * H) * (D_R * D_R + star H * H)) := by
  intro D_fluct D_sa
  have hDL : D_L * Γ = -(Γ * D_L) := eq_neg_of_add_eq_zero_left hL_anti
  have hDR : D_R * Γ = -(Γ * D_R) := eq_neg_of_add_eq_zero_left hR_anti
  have h_prod : ∀ (X Y : B), Γ * X = X * Γ → (Γ * X) * (Γ * Y) = X * Y := by
    intro X Y hX
    calc (Γ * X) * (Γ * Y) = Γ * (X * Γ) * Y := by noncomm_ring
      _ = Γ * (Γ * X) * Y := by rw [hX]
      _ = (Γ * Γ) * (X * Y) := by noncomm_ring
      _ = X * Y := by rw [hΓ_sq, one_mul]
  have h_cov1 : ∀ (X : B), D_L * (Γ * X) + (Γ * X) * D_R = -Γ * higgsCovDeriv D_L D_R X := by
    intro X; dsimp [higgsCovDeriv]
    calc D_L * (Γ * X) + (Γ * X) * D_R
      _ = (D_L * Γ) * X + Γ * (X * D_R) := by noncomm_ring
      _ = -(Γ * D_L) * X + Γ * (X * D_R) := by rw [hDL]
      _ = -Γ * (D_L * X - X * D_R) := by noncomm_ring
  have h_cov2 : ∀ (Y : B), (Γ * Y) * D_L + D_R * (Γ * Y) = -Γ * higgsCovDeriv D_R D_L Y := by
    intro Y; dsimp [higgsCovDeriv]
    calc (Γ * Y) * D_L + D_R * (Γ * Y)
      _ = Γ * (Y * D_L) + (D_R * Γ) * Y := by noncomm_ring
      _ = Γ * (Y * D_L) + -(Γ * D_R) * Y := by rw [hDR]
      _ = -Γ * (D_R * Y - Y * D_L) := by noncomm_ring
  have hH_star : Γ * star H = star H * Γ := by
    calc Γ * star H = star (H * Γ) := by rw [star_mul, hΓ_sa]
      _ = star (Γ * H) := by rw [hH]
      _ = star H * Γ := by rw [star_mul, hΓ_sa]
  have h_sq_sa : D_sa * D_sa =
      mat2 (D_L * D_L + H * star H) (-Γ * higgsCovDeriv D_L D_R H)
           (-Γ * higgsCovDeriv D_R D_L (star H)) (D_R * D_R + star H * H) := by
    apply ext_fin2 <;>
      simp [D_sa, fluctuatedDirac, h_prod H (star H) hH,
            h_prod (star H) H hH_star, h_cov1 H, h_cov2 (star H)]
  have h_norm : ∀ (X : B), star (-Γ * X) * (-Γ * X) = star X * X := by
    intro X
    simp only [star_mul, star_neg, hΓ_sa]
    calc (star X * -Γ) * (-Γ * X) = star X * (Γ * Γ) * X := by noncomm_ring
      _ = star X * X := by rw [hΓ_sq]; noncomm_ring
  refine ⟨?_, ?_⟩
  · apply ext_fin2 <;>
      simp [D_fluct, fluctuatedDirac, h_prod H_plus H_minus hH_plus,
            h_prod H_minus H_plus hH_minus, h_cov1 H_plus, h_cov2 H_minus]
  · rw [h_sq_sa]
    simp [h_norm]

end ArchetypeDH2_ConnesChamseddineHiggsMechanism

/-!
## Archetype $\mathcal{D}\mathcal{H}_3$ & $\mathcal{D}\mathcal{H}_4$: All-Scales Kronecker Dirac–Connes Tower & Entropic Mass Summability on `ClTower B N`
-/

section ArchetypeDH3_DH4_AllScalesDiracMassSummability

universe u

def ClTower (B : Type u) : ℕ → Type u
  | 0     => B
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower B n)

instance instRingClTower {B : Type u} [Ring B] : ∀ n : ℕ, Ring (ClTower B n)
  | 0     => inferInstanceAs (Ring B)
  | n + 1 => by
      letI : Ring (ClTower B n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower B n)))

variable {B : Type u} [Ring B]

def diagEmbed {n : ℕ} (X : ClTower B n) : ClTower B (n + 1) :=
  mat2 X 0 0 X

def towerScalar : ∀ (n : ℕ), B → ClTower B n
  | 0,     b => b
  | n + 1, b => diagEmbed (towerScalar n b)

/-- $n$-scale Kronecker chirality involution $\Gamma^{(n)} \in \mathcal{C}\ell_n(B)$. -/
def kroneckerGamma (γ₀ : B) : ∀ (n : ℕ), ClTower B n
  | 0     => γ₀
  | n + 1 => mat2 (kroneckerGamma γ₀ n) 0 0 (-kroneckerGamma γ₀ n)

/-- $n$-scale Kronecker Dirac–Connes operator $\mathcal{D}_n \in \mathcal{C}\ell_n(B)$. -/
def connesDiracTower (D₀ γ₀ : B) (m : ℕ → B) : ∀ (n : ℕ), ClTower B n
  | 0     => D₀
  | n + 1 =>
      liftDiracStep
        (connesDiracTower D₀ γ₀ m n)
        (kroneckerGamma γ₀ n)
        (towerScalar n (m n))

/-- Cumulative sum of squared masses $D_0^2 + \sum_{k=0}^{n-1} m_k^2 \in B$. -/
def cumulativeMassSq (D₀ : B) (m : ℕ → B) : ℕ → B
  | 0     => D₀ * D₀
  | n + 1 => cumulativeMassSq D₀ m n + m n * m n

def towerTrace : ∀ {n : ℕ}, ClTower B n → B
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace (γ₀ : B) {n : ℕ} (M : ClTower B n) : B :=
  towerTrace (kroneckerGamma γ₀ n * M)

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower B n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      rw [Matrix.neg_apply, Matrix.neg_apply, towerTrace_neg, towerTrace_neg]
      abel

lemma towerScalar_add (n : ℕ) (x y : B) :
    towerScalar n (x + y) = towerScalar n x + towerScalar n y := by
  induction' n with k ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, diagEmbed, ih]

lemma towerScalar_mul (n : ℕ) (x y : B) :
    towerScalar n (x * y) = towerScalar n x * towerScalar n y := by
  induction' n with k ih
  · rfl
  · apply ext_fin2 <;> simp [towerScalar, diagEmbed, ih]

lemma towerScalar_central {c : B} (hc : ∀ x : B, c * x = x * c) :
    ∀ (n : ℕ) (X : ClTower B n), towerScalar n c * X = X * towerScalar n c
  | 0,     X => hc X
  | n + 1, X => by
      have ih := towerScalar_central hc n
      apply ext_fin2 <;>
        simp [towerScalar, diagEmbed, ih (X 0 0), ih (X 0 1), ih (X 1 0), ih (X 1 1)]

lemma kroneckerGamma_sq {γ₀ : B} (hγ₀ : γ₀ * γ₀ = 1) :
    ∀ (n : ℕ), kroneckerGamma γ₀ n * kroneckerGamma γ₀ n = 1
  | 0     => hγ₀
  | n + 1 => by apply ext_fin2 <;> simp [kroneckerGamma, kroneckerGamma_sq hγ₀ n]

/-- **All-Scales Entropic Mass Summability Across the Bott–Clifford Tower ($\mathcal{D}\mathcal{H}_3$ & $\mathcal{D}\mathcal{H}_4$)**:
Given $D_0, \gamma_0 \in B$ with $\{D_0, \gamma_0\} = 0$ and $\gamma_0^2 = 1$, and central scale
masses $m : \mathbb{N} \to B$, for *every* tower depth $N \in \mathbb{N}$:
1. $(\Gamma^{(N)})^2 = 1$,
2. $\{\mathcal{D}_N, \Gamma^{(N)}\} = 0$ (all-scales chirality anticommutation),
3. $\mathcal{D}_N^2 = \iota_{\mathrm{diag}}^{(N)}\big(D_0^2 + \sum_{k=0}^{N-1} m_k^2\big)$ (exact additive summability of squared masses),
4. $\mathrm{Str}_{2^{N+1}}(\mathcal{D}_{N+1}^2) = 0$ (chiral supertrace balance of the total mass-squared). -/
theorem all_scales_connes_dirac_mass_entropy_tower
    (D₀ γ₀ : B) (m : ℕ → B)
    (h_anti₀ : D₀ * γ₀ + γ₀ * D₀ = 0)
    (h_γ₀_sq : γ₀ * γ₀ = 1)
    (hm_central : ∀ (k : ℕ) (x : B), m k * x = x * m k) (N : ℕ) :
    let D_N := connesDiracTower D₀ γ₀ m N
    let Γ_N := kroneckerGamma γ₀ N
    Γ_N * Γ_N = 1 ∧
    D_N * Γ_N + Γ_N * D_N = 0 ∧
    D_N * D_N = towerScalar N (cumulativeMassSq D₀ m N) ∧
    superTrace γ₀ (connesDiracTower D₀ γ₀ m (N + 1) * connesDiracTower D₀ γ₀ m (N + 1)) = 0 := by
  have h_ind : ∀ (n : ℕ),
      connesDiracTower D₀ γ₀ m n * kroneckerGamma γ₀ n +
        kroneckerGamma γ₀ n * connesDiracTower D₀ γ₀ m n = 0 ∧
      connesDiracTower D₀ γ₀ m n * connesDiracTower D₀ γ₀ m n =
        towerScalar n (cumulativeMassSq D₀ m n) := by
    intro n; induction' n with k ih
    · exact ⟨h_anti₀, rfl⟩
    · rcases ih with ⟨ih_anti, ih_sq⟩
      have h_cent_k := towerScalar_central (hm_central k) k
      have h_comm_Γ : kroneckerGamma γ₀ k * towerScalar k (m k) =
          towerScalar k (m k) * kroneckerGamma γ₀ k :=
        (h_cent_k (kroneckerGamma γ₀ k)).symm
      have h_comm_D : ⁅connesDiracTower D₀ γ₀ m k, towerScalar k (m k)⁆ = 0 := by
        rw [Ring.lie_def, h_cent_k (connesDiracTower D₀ γ₀ m k), sub_self]
      rcases mass_commutator_and_noncentral_lichnerowicz_higgs
        0 0 0 0 (connesDiracTower D₀ γ₀ m k) (kroneckerGamma γ₀ k) (towerScalar k (m k))
        ih_anti (kroneckerGamma_sq h_γ₀_sq k) h_comm_Γ with ⟨_, _, h_step_sq, h_step_anti⟩
      refine ⟨h_step_anti, ?_⟩
      dsimp [connesDiracTower, cumulativeMassSq, towerScalar, diagEmbed]
      rw [h_step_sq h_comm_D, ih_sq, ← towerScalar_mul, ← towerScalar_add]
  refine ⟨kroneckerGamma_sq h_γ₀_sq N, (h_ind N).1, (h_ind N).2, ?_⟩
  rw [(h_ind (N + 1)).2]
  dsimp [superTrace, kroneckerGamma, towerScalar, diagEmbed, towerTrace]
  simp [neg_mul, towerTrace_neg]

end ArchetypeDH3_DH4_AllScalesDiracMassSummability

end TwoSheetDiracMassEntropy
```

## Turn 0093, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeCovariantDiracZornSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

def gamma1Op   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

end Matrix2Simp

/-!
## Archetype $\mathcal{Z}_1$: 3D $Cl(1,1)$ Zorn Vector Operator & Universal Dot-Plus-Cross Product
-/

section ArchetypeZ1_ZornVectorOperator

variable {B : Type*} [Ring B]

/-- 3D $Cl(1,1)$ Zorn vector operator $\mathrm{vecOp}(u_1, u_2, u_3) = \iota(u_1)\Gamma_1 + \iota(u_2)\Sigma + \iota(u_3)\Omega \in M_2(B)$. -/
def vecOp (u₁ u₂ u₃ : B) : Matrix (Fin 2) (Fin 2) B :=
  fiberEmbed u₁ * gamma1Op + fiberEmbed u₂ * sigmaOp + fiberEmbed u₃ * omegaOp

/-- Zorn split-Minkowski inner product $\langle \mathbf{u}, \mathbf{v}\rangle_{1,1} = u_1 v_1 + u_2 v_2 - u_3 v_3$. -/
def zornDot (u₁ u₂ u₃ v₁ v₂ v₃ : B) : B :=
  u₁ * v₁ + u₂ * v₂ - u₃ * v₃

/-- Zorn split-3D vector cross product components $(\mathbf{u} \times_{1,1} \mathbf{v})_k$. -/
def zornCross1 (u₁ u₂ u₃ v₁ v₂ v₃ : B) : B := u₂ * v₃ - u₃ * v₂
def zornCross2 (u₁ u₂ u₃ v₁ v₂ v₃ : B) : B := u₃ * v₁ - u₁ * v₃
def zornCross3 (u₁ u₂ u₃ v₁ v₂ v₃ : B) : B := -(u₁ * v₂ - u₂ * v₁)

@[simp] lemma vecOp_00 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 0 = u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

@[simp] lemma vecOp_01 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 1 = u₂ - u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]; rfl

@[simp] lemma vecOp_10 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 0 = u₂ + u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

@[simp] lemma vecOp_11 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 1 = -u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

/-- **Universal Zorn Vector Dot-Plus-Cross Multiplication Theorem ($\mathcal{Z}_1$)**:
In any noncommutative ring $B$, the product of two Zorn vector operators decomposes into the
Zorn inner product along $1$ plus the Zorn cross product along $(\Gamma_1, \Sigma, \Omega)$:
$\mathrm{vecOp}(\mathbf{u}) \cdot \mathrm{vecOp}(\mathbf{v}) = \iota(\mathrm{zornDot}(\mathbf{u}, \mathbf{v})) + \mathrm{vecOp}(\mathrm{zornCross}(\mathbf{u}, \mathbf{v}))$.
In particular, $\mathrm{vecOp}(\mathbf{D})^2 = \iota(D_1^2 + D_2^2 - D_3^2) + \mathrm{vecOp}(\⁅D_2, D_3⁆, \⁅D_3, D_1⁆, -\⁅D_1, D_2⁆)$. -/
theorem zorn_vector_product_dot_plus_cross (u₁ u₂ u₃ v₁ v₂ v₃ D₁ D₂ D₃ : B) :
    vecOp u₁ u₂ u₃ * vecOp v₁ v₂ v₃ =
      fiberEmbed (zornDot u₁ u₂ u₃ v₁ v₂ v₃) +
      vecOp (zornCross1 u₁ u₂ u₃ v₁ v₂ v₃)
            (zornCross2 u₁ u₂ u₃ v₁ v₂ v₃)
            (zornCross3 u₁ u₂ u₃ v₁ v₂ v₃) ∧
    vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃ =
      fiberEmbed (D₁ * D₁ + D₂ * D₂ - D₃ * D₃) +
      vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆) := by
  have h_prod : ∀ (a₁ a₂ a₃ b₁ b₂ b₃ : B),
      vecOp a₁ a₂ a₃ * vecOp b₁ b₂ b₃ =
      fiberEmbed (zornDot a₁ a₂ a₃ b₁ b₂ b₃) +
      vecOp (zornCross1 a₁ a₂ a₃ b₁ b₂ b₃)
            (zornCross2 a₁ a₂ a₃ b₁ b₂ b₃)
            (zornCross3 a₁ a₂ a₃ b₁ b₂ b₃) := by
    intro a₁ a₂ a₃ b₁ b₂ b₃
    apply ext_fin2 <;>
      simp [fiberEmbed, zornDot, zornCross1, zornCross2, zornCross3] <;>
      noncomm_ring
  refine ⟨h_prod u₁ u₂ u₃ v₁ v₂ v₃, ?_⟩
  rw [h_prod D₁ D₂ D₃ D₁ D₂ D₃]
  rfl

end ArchetypeZ1_ZornVectorOperator

/-!
## Archetype $\mathcal{Z}_2$: Covariant Two-Sheeted Dirac–Zorn Operator & Pauli–Dirac Spin-Curvature Coupling
-/

section ArchetypeZ2_CovariantDiracZornOperator

variable {B : Type*} [Ring B]

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-- Covariant two-sheeted Dirac–Zorn operator
$\mathcal{D}_{\mathrm{Zorn}}(\alpha, \beta, \mathbf{u}, \mathbf{v}) = \bigl(\begin{smallmatrix} \iota(\alpha) & \mathrm{vecOp}(\mathbf{u}) \\ \mathrm{vecOp}(\mathbf{v}) & \iota(\beta) \end{smallmatrix}\bigr) \in M_2(M_2(B))$. -/
def diracZornOp (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) : NestedMat B :=
  mat2 (fiberEmbed α) (vecOp u₁ u₂ u₃) (vecOp v₁ v₂ v₃) (fiberEmbed β)

/-- **Covariant Dirac–Zorn Multiplication & Pauli–Dirac Wave Square Theorem ($\mathcal{Z}_2$)**:
1. Multiplying two Dirac–Zorn operators generates $\iota(\alpha_1\alpha_2 + \mathrm{zornDot}(\mathbf{u}_1, \mathbf{v}_2)) + \mathrm{vecOp}(\mathrm{zornCross}(\mathbf{u}_1, \mathbf{v}_2))$
   on the $(0,0)$ block and $\iota(\beta_1\beta_2 + \mathrm{zornDot}(\mathbf{v}_1, \mathbf{u}_2)) + \mathrm{vecOp}(\mathrm{zornCross}(\mathbf{v}_1, \mathbf{u}_2))$
   on the $(1,1)$ block, with bimodule actions on the off-diagonal.
2. Squaring the symmetric covariant Dirac–Zorn operator $\mathcal{D}_{\mathrm{Zorn}}(m, -m, \mathbf{D}, \mathbf{D})$
   simultaneously produces the Klein–Gordon operator $\iota(m^2 + D_1^2 + D_2^2 - D_3^2)$, the
   Pauli–Dirac spin-magnetic curvature $\mathrm{vecOp}(\⁅D_2, D_3⁆, \⁅D_3, D_1⁆, -\⁅D_1, D_2⁆)$, and
   the off-diagonal Yukawa mass-gradient $\⁅\iota(m), \mathrm{vecOp}(\mathbf{D})⁆$. -/
theorem covariant_dirac_zorn_multiplication_and_pauli_square
    (α₁ β₁ u₁ u₂ u₃ v₁ v₂ v₃ α₂ β₂ x₁ x₂ x₃ y₁ y₂ y₃ m D₁ D₂ D₃ : B) :
    let Z₁ := diracZornOp α₁ β₁ u₁ u₂ u₃ v₁ v₂ v₃
    let Z₂ := diracZornOp α₂ β₂ x₁ x₂ x₃ y₁ y₂ y₃
    let D_cov := diracZornOp m (-m) D₁ D₂ D₃ D₁ D₂ D₃
    Z₁ * Z₂ =
      mat2
        (fiberEmbed (α₁ * α₂ + zornDot u₁ u₂ u₃ y₁ y₂ y₃) +
         vecOp (zornCross1 u₁ u₂ u₃ y₁ y₂ y₃)
               (zornCross2 u₁ u₂ u₃ y₁ y₂ y₃)
               (zornCross3 u₁ u₂ u₃ y₁ y₂ y₃))
        (fiberEmbed α₁ * vecOp x₁ x₂ x₃ + vecOp u₁ u₂ u₃ * fiberEmbed β₂)
        (vecOp v₁ v₂ v₃ * fiberEmbed α₂ + fiberEmbed β₁ * vecOp y₁ y₂ y₃)
        (fiberEmbed (β₁ * β₂ + zornDot v₁ v₂ v₃ x₁ x₂ x₃) +
         vecOp (zornCross1 v₁ v₂ v₃ x₁ x₂ x₃)
               (zornCross2 v₁ v₂ v₃ x₁ x₂ x₃)
               (zornCross3 v₁ v₂ v₃ x₁ x₂ x₃)) ∧
    D_cov * D_cov =
      mat2
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆))
        ⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆
        (-⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆)
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆)) := by
  have h_vec := fun a₁ a₂ a₃ b₁ b₂ b₃ =>
    (zorn_vector_product_dot_plus_cross a₁ a₂ a₃ b₁ b₂ b₃ 0 0 0).1
  have h_add_emb : ∀ (a b : B), fiberEmbed a + fiberEmbed b = fiberEmbed (a + b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_mul_emb : ∀ (a b : B), fiberEmbed a * fiberEmbed b = fiberEmbed (a * b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_neg_emb : ∀ (a : B), fiberEmbed (-a) = -fiberEmbed a := by
    intro a; apply ext_fin2 <;> simp [fiberEmbed]
  refine ⟨?_, ?_⟩
  · apply ext_fin2
    · simp only [diracZornOp, mul2_00, mat2_00, mat2_01, mat2_10,
        h_mul_emb, h_vec u₁ u₂ u₃ y₁ y₂ y₃, ← add_assoc, h_add_emb]
    · simp [diracZornOp]
    · simp [diracZornOp]
    · simp only [diracZornOp, mul2_11, mat2_10, mat2_01, mat2_11,
        h_mul_emb, h_vec v₁ v₂ v₃ x₁ x₂ x₃]
      rw [add_comm (vecOp v₁ v₂ v₃ * vecOp x₁ x₂ x₃),
          h_vec v₁ v₂ v₃ x₁ x₂ x₃, ← add_assoc, h_add_emb]
  · rw [Ring.lie_def]
    apply ext_fin2
    · simp only [diracZornOp, mul2_00, mat2_00, mat2_01, mat2_10,
        h_mul_emb, (zorn_vector_product_dot_plus_cross 0 0 0 0 0 0 D₁ D₂ D₃).2,
        ← add_assoc, h_add_emb]
    · simp only [diracZornOp, mul2_01, mat2_00, mat2_01, mat2_11,
        h_neg_emb, mul_neg, sub_eq_add_neg]
    · simp only [diracZornOp, mul2_10, mat2_10, mat2_00, mat2_11, h_neg_emb, neg_mul]
      abel
    · simp only [diracZornOp, mul2_11, mat2_10, mat2_01, mat2_11,
        h_neg_emb, neg_mul_neg, h_mul_emb]
      rw [add_comm (vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃),
          (zorn_vector_product_dot_plus_cross 0 0 0 0 0 0 D₁ D₂ D₃).2,
          ← add_assoc, h_add_emb]

end ArchetypeZ2_CovariantDiracZornOperator

/-!
## Archetype $\mathcal{Z}_3$: Zorn Conjugation, Zorn Determinant Norm & Max Zorn's Split-Octonion Product
-/

section ArchetypeZ3_ZornConjugateAndOctonionProduct

variable {B : Type*} [Ring B]

/-- Zorn conjugate (Cayley–Dickson adjoint)
$\overline{\mathcal{D}_{\mathrm{Zorn}}}(\alpha, \beta, \mathbf{u}, \mathbf{v}) = \mathcal{D}_{\mathrm{Zorn}}(\beta, \alpha, -\mathbf{u}, -\mathbf{v})$. -/
def zornConj (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) : NestedMat B :=
  diracZornOp β α (-u₁) (-u₂) (-u₃) (-v₁) (-v₂) (-v₃)

/-- Zorn quadratic determinant norm $N_{\mathrm{Zorn}}(\alpha, \beta, \mathbf{u}, \mathbf{v}) = \alpha\beta - \mathrm{zornDot}(\mathbf{u}, \mathbf{v})$. -/
def zornNorm (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) : B :=
  α * β - zornDot u₁ u₂ u₃ v₁ v₂ v₃

/-- Max Zorn's (1931) split-octonion vector-matrix product $\mathcal{D}_1 \star_{\mathrm{Zorn}} \mathcal{D}_2$. -/
def zornOctonionMul (α₁ β₁ u₁ u₂ u₃ v₁ v₂ v₃ α₂ β₂ x₁ x₂ x₃ y₁ y₂ y₃ : B) : NestedMat B :=
  mat2
    (fiberEmbed (α₁ * α₂ + zornDot u₁ u₂ u₃ y₁ y₂ y₃))
    (fiberEmbed α₁ * vecOp x₁ x₂ x₃ + vecOp u₁ u₂ u₃ * fiberEmbed β₂ -
     vecOp (zornCross1 v₁ v₂ v₃ y₁ y₂ y₃)
           (zornCross2 v₁ v₂ v₃ y₁ y₂ y₃)
           (zornCross3 v₁ v₂ v₃ y₁ y₂ y₃))
    (vecOp v₁ v₂ v₃ * fiberEmbed α₂ + fiberEmbed β₁ * vecOp y₁ y₂ y₃ +
     vecOp (zornCross1 u₁ u₂ u₃ x₁ x₂ x₃)
           (zornCross2 u₁ u₂ u₃ x₁ x₂ x₃)
           (zornCross3 u₁ u₂ u₃ x₁ x₂ x₃))
    (fiberEmbed (β₁ * β₂ + zornDot v₁ v₂ v₃ x₁ x₂ x₃))

/-- **Zorn Conjugate Norm & Associative-vs-Octonionic Curvature Theorem ($\mathcal{Z}_3$)**:
1. In the associative Dirac–Pauli matrix algebra $M_2(M_2(B))$, $\mathcal{D}_{\mathrm{Zorn}} \cdot \overline{\mathcal{D}_{\mathrm{Zorn}}}$
   equals the Zorn norm $\mathrm{diag}(\iota(N_{\mathrm{Zorn}}(\alpha, \beta, \mathbf{u}, \mathbf{v})), \iota(N_{\mathrm{Zorn}}(\beta, \alpha, \mathbf{v}, \mathbf{u})))$
   minus the Pauli cross-product curvature $\mathrm{vecOp}(\mathrm{zornCross}(\mathbf{u}, \mathbf{v}))$ on the diagonal
   and the commutator $\⁅\mathrm{vecOp}(\mathbf{u}), \iota(\alpha)⁆$ on the off-diagonal.
2. Under Zorn's split-octonion product $\star_{\mathrm{Zorn}}$, multiplying by the Zorn conjugate
   produces the diagonal Zorn norm on the $(0,0)$ and $(1,1)$ blocks, while the off-diagonal blocks
   carry only the non-Abelian self-curvatures $\mathrm{vecOp}(\⁅v_2, v_3⁆, \⁅v_3, v_1⁆, -\⁅v_1, v_2⁆)$
   and $-\mathrm{vecOp}(\⁅u_2, u_3⁆, \⁅u_3, u_1⁆, -\⁅u_1, u_2⁆)$. -/
theorem zorn_conjugate_norm_and_octonion_product
    (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) :
    let Z      := diracZornOp α β u₁ u₂ u₃ v₁ v₂ v₃
    let Z_conj := zornConj α β u₁ u₂ u₃ v₁ v₂ v₃
    Z * Z_conj =
      mat2
        (fiberEmbed (zornNorm α β u₁ u₂ u₃ v₁ v₂ v₃) -
         vecOp (zornCross1 u₁ u₂ u₃ v₁ v₂ v₃)
               (zornCross2 u₁ u₂ u₃ v₁ v₂ v₃)
               (zornCross3 u₁ u₂ u₃ v₁ v₂ v₃))
        ⁅vecOp u₁ u₂ u₃, fiberEmbed α⁆
        (-⁅vecOp v₁ v₂ v₃, fiberEmbed β⁆)
        (fiberEmbed (zornNorm β α v₁ v₂ v₃ u₁ u₂ u₃) -
         vecOp (zornCross1 v₁ v₂ v₃ u₁ u₂ u₃)
               (zornCross2 v₁ v₂ v₃ u₁ u₂ u₃)
               (zornCross3 v₁ v₂ v₃ u₁ u₂ u₃)) ∧
    zornOctonionMul α β u₁ u₂ u₃ v₁ v₂ v₃ β α (-u₁) (-u₂) (-u₃) (-v₁) (-v₂) (-v₃) =
      mat2
        (fiberEmbed (zornNorm α β u₁ u₂ u₃ v₁ v₂ v₃))
        (⁅vecOp u₁ u₂ u₃, fiberEmbed α⁆ +
         vecOp ⁅v₂, v₃⁆ ⁅v₃, v₁⁆ (-⁅v₁, v₂⁆))
        (-⁅vecOp v₁ v₂ v₃, fiberEmbed β⁆ -
         vecOp ⁅u₂, u₃⁆ ⁅u₃, u₁⁆ (-⁅u₁, u₂⁆))
        (fiberEmbed (zornNorm β α v₁ v₂ v₃ u₁ u₂ u₃)) := by
  simp only [Ring.lie_def]
  refine ⟨?_, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [diracZornOp, zornConj, zornNorm, zornDot,
            zornCross1, zornCross2, zornCross3, fiberEmbed] <;>
      noncomm_ring
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [zornOctonionMul, zornNorm, zornDot,
            zornCross1, zornCross2, zornCross3, fiberEmbed] <;>
      noncomm_ring

end ArchetypeZ3_ZornConjugateAndOctonionProduct

/-!
## Archetype $\mathcal{Z}_4$: All-Scales Inductive Covariant Dirac–Zorn Tower on $\mathcal{C}\ell_{n+2}(B)$
-/

section ArchetypeZ4_AllScalesInductiveDiracZornTower

universe u

def ClTower (B : Type u) : ℕ → Type u
  | 0     => B
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower B n)

instance instRingClTower {B : Type u} [Ring B] : ∀ n : ℕ, Ring (ClTower B n)
  | 0     => inferInstanceAs (Ring B)
  | n + 1 => by
      letI : Ring (ClTower B n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower B n)))

variable {B : Type u} [Ring B]

/-- **All-Scales Inductive Covariant Dirac–Zorn Wave Square on $\mathcal{C}\ell_{n+2}(B)$ ($\mathcal{Z}_4$)**:
At every scale $n \in \mathbb{N}$, the covariant Dirac–Zorn operator in $\mathcal{C}\ell_{n+2}(B) = M_2(M_2(\mathcal{C}\ell_n(B)))$
satisfies the exact Pauli–Dirac–Zorn wave decomposition. -/
theorem all_scales_inductive_covariant_dirac_zorn_wave_square
    (n : ℕ) (m D₁ D₂ D₃ : ClTower B n) :
    let D_n := diracZornOp m (-m) D₁ D₂ D₃ D₁ D₂ D₃
    D_n * D_n =
      mat2
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆))
        ⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆
        (-⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆)
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆)) := by
  exact (covariant_dirac_zorn_multiplication_and_pauli_square
    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 m D₁ D₂ D₃).2

end ArchetypeZ4_AllScalesInductiveDiracZornTower

end NoncommutativeCovariantDiracZornSynthesis
```

## Turn 0096, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeInherentZornGaugeSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & 3D Zorn Vector Operators
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {B : Type*} [Ring B]

@[simp] lemma mat2_00 (a b c d : B) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : B) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : B) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : B) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) B) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) B) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) B) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) B) 1 1 = 1 := rfl

def gamma1Op   : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) B := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) B := mat2 0 (-1) 1 0
def fiberEmbed (a : B) : Matrix (Fin 2) (Fin 2) B := mat2 a 0 0 a

def vecOp (u₁ u₂ u₃ : B) : Matrix (Fin 2) (Fin 2) B :=
  fiberEmbed u₁ * gamma1Op + fiberEmbed u₂ * sigmaOp + fiberEmbed u₃ * omegaOp

def zornDot (u₁ u₂ u₃ v₁ v₂ v₃ : B) : B :=
  u₁ * v₁ + u₂ * v₂ - u₃ * v₃

def zornCross1 (u₁ u₂ u₃ v₁ v₂ v₃ : B) : B := u₂ * v₃ - u₃ * v₂
def zornCross2 (u₁ u₂ u₃ v₁ v₂ v₃ : B) : B := u₃ * v₁ - u₁ * v₃
def zornCross3 (u₁ u₂ u₃ v₁ v₂ v₃ : B) : B := -(u₁ * v₂ - u₂ * v₁)

@[simp] lemma vecOp_00 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 0 = u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_01 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 1 = u₂ - u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]; rfl
@[simp] lemma vecOp_10 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 0 = u₂ + u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_11 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 1 = -u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end Matrix2Simp

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-!
## Archetype $\mathcal{G}\mathcal{Z}_1$: Inherent Emergence of Gauge & Higgs Potentials as Inner Commutators $\⁅\mathcal{D}_0, \mathbb{U}⁆$
-/

section ArchetypeGZ1_InherentGaugeFromInnerCommutator

variable {B : Type*} [Ring B]

/-- General two-sheeted Dirac–Zorn operator in $M_2(M_2(B))$. -/
def diracZornOp (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) : NestedMat B :=
  mat2 (fiberEmbed α) (vecOp u₁ u₂ u₃) (vecOp v₁ v₂ v₃) (fiberEmbed β)

/-- Bare un-gauged Dirac–Zorn operator $\mathcal{D}_0(m_0, d_1, d_2, d_3)$. -/
def bareDiracZorn (m₀ d₁ d₂ d₃ : B) : NestedMat B :=
  diracZornOp m₀ (-m₀) d₁ d₂ d₃ d₁ d₂ d₃

/-- Diagonal two-sheet algebra element $\mathbb{U}(u, v) = \mathrm{diag}(\iota(u), \iota(v))$. -/
def sheetDiag (u v : B) : NestedMat B :=
  mat2 (fiberEmbed u) 0 0 (fiberEmbed v)

/-- **Inherent Emergence of Zorn Gauge & Higgs Potentials ($\mathcal{G}\mathcal{Z}_1$)**:
1. The inner commutator $\⁅\mathcal{D}_0(m_0, \mathbf{d}), \mathbb{U}(u, v)⁆$ automatically populates
   the off-diagonal Zorn vector slots with the 3-vector gauge 1-forms $d_k v - u d_k$ and the
   diagonal slots with the scalar Higgs shifts $\⁅m_0, u⁆, -\⁅m_0, v⁆$,
2. Shifting $d_k \mapsto d_k + A_k$ splits the covariant Dirac–Zorn operator additively into the
   bare operator $\mathcal{D}_0(m_0, \mathbf{d})$ plus the Zorn gauge potential $\mathcal{D}_{\mathrm{Zorn}}(0, 0, \mathbf{A}, \mathbf{A})$. -/
theorem inherent_gauge_higgs_from_inner_commutator
    (m₀ d₁ d₂ d₃ u v A₁ A₂ A₃ : B) :
    ⁅bareDiracZorn m₀ d₁ d₂ d₃, sheetDiag u v⁆ =
      diracZornOp ⁅m₀, u⁆ (-⁅m₀, v⁆)
        (d₁ * v - u * d₁) (d₂ * v - u * d₂) (d₃ * v - u * d₃)
        (d₁ * u - v * d₁) (d₂ * u - v * d₂) (d₃ * u - v * d₃) ∧
    bareDiracZorn m₀ (d₁ + A₁) (d₂ + A₂) (d₃ + A₃) =
      bareDiracZorn m₀ d₁ d₂ d₃ + diracZornOp 0 0 A₁ A₂ A₃ A₁ A₂ A₃ := by
  simp only [Ring.lie_def]
  refine ⟨?_, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [bareDiracZorn, diracZornOp, sheetDiag, fiberEmbed] <;>
      noncomm_ring
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [bareDiracZorn, diracZornOp, fiberEmbed] <;>
      abel

end ArchetypeGZ1_InherentGaugeFromInnerCommutator

/-!
## Archetype $\mathcal{G}\mathcal{Z}_2$: The Zorn Cross Product of $\mathbf{d} + \mathbf{A}$ IS the Non-Abelian Yang–Mills Field Strength
-/

section ArchetypeGZ2_ZornCrossProductYangMills

variable {B : Type*} [Ring B]

/-- Non-Abelian Yang–Mills field strength component $F_{ij}(\mathbf{d}, \mathbf{A}) = \⁅d_i, A_j⁆ - \⁅d_j, A_i⁆ + \⁅A_i, A_j⁆$. -/
def ymFieldStrength (dᵢ dⱼ Aᵢ Aⱼ : B) : B :=
  ⁅dᵢ, Aⱼ⁆ - ⁅dⱼ, Aᵢ⁆ + ⁅Aᵢ, Aⱼ⁆

/-- **Zorn Cross Product as Yang–Mills Field Strength & Non-Abelian Bianchi Theorem ($\mathcal{G}\mathcal{Z}_2$)**:
1. For any $d_i, d_j, A_i, A_j \in B$, $\⁅d_i + A_i, d_j + A_j⁆ = \⁅d_i, d_j⁆ + F_{ij}(\mathbf{d}, \mathbf{A})$.
2. When the bare background derivatives commute ($\⁅d_i, d_j⁆ = 0$), the Zorn cross product
   $\mathrm{vecOp}(\mathrm{zornCross}(\mathbf{d} + \mathbf{A}, \mathbf{d} + \mathbf{A}))$ is identically the
   Yang–Mills chromomagnetic spin-curvature operator $\mathrm{vecOp}(F_{23}, F_{31}, -F_{12})$.
3. The Yang–Mills components satisfy the exact non-Abelian Bianchi identity:
   $\⁅d_1 + A_1, F_{23}⁆ + \⁅d_2 + A_2, F_{31}⁆ + \⁅d_3 + A_3, F_{12}⁆ = 0$. -/
theorem zorn_cross_product_is_yang_mills_curvature_and_bianchi
    (d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁  := d₁ + A₁
    let D₂  := d₂ + A₂
    let D₃  := d₃ + A₃
    let F₂₃ := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁ := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂ := ymFieldStrength d₁ d₂ A₁ A₂
    ⁅D₁, D₂⁆ = ⁅d₁, d₂⁆ + F₁₂ ∧
    vecOp (zornCross1 D₁ D₂ D₃ D₁ D₂ D₃)
          (zornCross2 D₁ D₂ D₃ D₁ D₂ D₃)
          (zornCross3 D₁ D₂ D₃ D₁ D₂ D₃) =
      vecOp F₂₃ F₃₁ (-F₁₂) ∧
    ⁅D₁, F₂₃⁆ + ⁅D₂, F₃₁⁆ + ⁅D₃, F₁₂⁆ = 0 := by
  intro D₁ D₂ D₃ F₂₃ F₃₁ F₁₂
  have h_decomp : ∀ (x₁ x₂ y₁ y₂ : B),
      ⁅x₁ + y₁, x₂ + y₂⁆ = ⁅x₁, x₂⁆ + ymFieldStrength x₁ x₂ y₁ y₂ := by
    intro x₁ x₂ y₁ y₂
    dsimp [ymFieldStrength]
    simp only [Ring.lie_def]
    noncomm_ring
  have hF23 : F₂₃ = ⁅D₂, D₃⁆ := by
    have h := h_decomp d₂ d₃ A₂ A₃; rw [h23, zero_add] at h; exact h.symm
  have hF31 : F₃₁ = ⁅D₃, D₁⁆ := by
    have h := h_decomp d₃ d₁ A₃ A₁; rw [h31, zero_add] at h; exact h.symm
  have hF12 : F₁₂ = ⁅D₁, D₂⁆ := by
    have h := h_decomp d₁ d₂ A₁ A₂; rw [h12, zero_add] at h; exact h.symm
  refine ⟨h_decomp d₁ d₂ A₁ A₂, ?_, ?_⟩
  · rw [hF23, hF31, hF12]
    rfl
  · rw [hF23, hF31, hF12]
    simp only [Ring.lie_def]
    noncomm_ring

end ArchetypeGZ2_ZornCrossProductYangMills

/-!
## Archetype $\mathcal{G}\mathcal{Z}_3$ & $\mathcal{G}\mathcal{Z}_4$: Inherent Affine Gauge Transformation, Homogeneous Zorn Curvature Covariance & Maurer–Cartan Flatness
-/

section ArchetypeGZ3_GZ4_GaugeCovarianceAndMaurerCartan

variable {B : Type*} [Ring B]

/-- Inherent affine gauge transformation of a Zorn vector potential:
$A_k^g = g (d_k + A_k) g^{-1} - d_k = g A_k g^{-1} + (g d_k g^{-1} - d_k)$. -/
def zornGaugeTransform (g : Bˣ) (dₖ Aₖ : B) : B :=
  (g : B) * (dₖ + Aₖ) * (↑g⁻¹ : B) - dₖ

lemma cov_shift_conj (g : Bˣ) (dₖ Aₖ : B) :
    dₖ + zornGaugeTransform g dₖ Aₖ = (g : B) * (dₖ + Aₖ) * (↑g⁻¹ : B) := by
  dsimp [zornGaugeTransform]; abel

lemma comm_conj_units (g : Bˣ) (X Y : B) :
    ⁅(g : B) * X * (↑g⁻¹ : B), (g : B) * Y * (↑g⁻¹ : B)⁆ =
      (g : B) * ⁅X, Y⁆ * (↑g⁻¹ : B) := by
  have hg : (↑g⁻¹ : B) * (g : B) = 1 := Units.inv_mul g
  rw [Ring.lie_def, Ring.lie_def]
  calc (g : B) * X * (↑g⁻¹ : B) * ((g : B) * Y * (↑g⁻¹ : B)) -
       (g : B) * Y * (↑g⁻¹ : B) * ((g : B) * X * (↑g⁻¹ : B))
    _ = (g : B) * X * ((↑g⁻¹ : B) * (g : B)) * Y * (↑g⁻¹ : B) -
        (g : B) * Y * ((↑g⁻¹ : B) * (g : B)) * X * (↑g⁻¹ : B) := by noncomm_ring
    _ = (g : B) * (X * Y - Y * X) * (↑g⁻¹ : B) := by rw [hg]; noncomm_ring

/-- **Inherent Zorn Gauge Covariance & Maurer–Cartan Vacuum Flatness Theorem ($\mathcal{G}\mathcal{Z}_3$ & $\mathcal{G}\mathcal{Z}_4$)**:
For any invertible gauge element $g \in B^\times$ and flat reference derivatives ($\⁅d_i, d_j⁆ = 0$):
1. *Covariant Dirac–Zorn Conjugation*: Conjugating $\mathcal{D}_{\mathrm{Zorn}}(m, -m, \mathbf{d}+\mathbf{A}, \mathbf{d}+\mathbf{A})$
   by $\mathbb{G}(g) = \mathrm{diag}(\iota(g), \iota(g))$ transforms $m \mapsto g m g^{-1}$ and $A_k \mapsto A_k^g$.
2. *Homogeneous Adjoint Covariance of the Zorn Field Strength*:
   $F_{ij}(\mathbf{d}, \mathbf{A}^g) = g F_{ij}(\mathbf{d}, \mathbf{A}) g^{-1}$, and
   $\mathrm{vecOp}(F_{23}^g, F_{31}^g, -F_{12}^g) = \iota(g)\,\mathrm{vecOp}(F_{23}, F_{31}, -F_{12})\,\iota(g^{-1})$.
3. *Maurer–Cartan Pure-Gauge Flatness*: For the pure gauge potential $A_k^{\mathrm{MC}}(g) = g d_k g^{-1} - d_k$,
   $F_{ij}(\mathbf{d}, \mathbf{A}^{\mathrm{MC}}(g)) = 0$. -/
theorem zorn_gauge_covariance_and_maurer_cartan_flatness
    (g : Bˣ) (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let A₁_g := zornGaugeTransform g d₁ A₁
    let A₂_g := zornGaugeTransform g d₂ A₂
    let A₃_g := zornGaugeTransform g d₃ A₃
    let m_g  := (g : B) * m * (↑g⁻¹ : B)
    let F₂₃   := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁   := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂   := ymFieldStrength d₁ d₂ A₁ A₂
    let F₂₃_g := ymFieldStrength d₂ d₃ A₂_g A₃_g
    let F₃₁_g := ymFieldStrength d₃ d₁ A₃_g A₁_g
    let F₁₂_g := ymFieldStrength d₁ d₂ A₁_g A₂_g
    sheetDiag (g : B) (g : B) *
      bareDiracZorn m (d₁ + A₁) (d₂ + A₂) (d₃ + A₃) *
      sheetDiag (↑g⁻¹ : B) (↑g⁻¹ : B) =
      bareDiracZorn m_g (d₁ + A₁_g) (d₂ + A₂_g) (d₃ + A₃_g) ∧
    F₁₂_g = (g : B) * F₁₂ * (↑g⁻¹ : B) ∧
    vecOp F₂₃_g F₃₁_g (-F₁₂_g) =
      fiberEmbed (g : B) * vecOp F₂₃ F₃₁ (-F₁₂) * fiberEmbed (↑g⁻¹ : B) ∧
    ymFieldStrength d₁ d₂ (zornGaugeTransform g d₁ 0) (zornGaugeTransform g d₂ 0) = 0 := by
  intro A₁_g A₂_g A₃_g m_g F₂₃ F₃₁ F₁₂ F₂₃_g F₃₁_g F₁₂_g
  have h_ym_eq : ∀ {x₁ x₂ : B} (y₁ y₂ : B), ⁅x₁, x₂⁆ = 0 →
      ymFieldStrength x₁ x₂ y₁ y₂ = ⁅x₁ + y₁, x₂ + y₂⁆ := by
    intro x₁ x₂ y₁ y₂ hx
    dsimp [ymFieldStrength]
    rw [← hx]
    simp only [Ring.lie_def]
    noncomm_ring
  have hF23_g : F₂₃_g = (g : B) * F₂₃ * (↑g⁻¹ : B) := by
    dsimp [F₂₃_g, F₂₃]
    rw [h_ym_eq A₂_g A₃_g h23, h_ym_eq A₂ A₃ h23,
        cov_shift_conj g d₂ A₂, cov_shift_conj g d₃ A₃,
        comm_conj_units g (d₂ + A₂) (d₃ + A₃)]
  have hF31_g : F₃₁_g = (g : B) * F₃₁ * (↑g⁻¹ : B) := by
    dsimp [F₃₁_g, F₃₁]
    rw [h_ym_eq A₃_g A₁_g h31, h_ym_eq A₃ A₁ h31,
        cov_shift_conj g d₃ A₃, cov_shift_conj g d₁ A₁,
        comm_conj_units g (d₃ + A₃) (d₁ + A₁)]
  have hF12_g : F₁₂_g = (g : B) * F₁₂ * (↑g⁻¹ : B) := by
    dsimp [F₁₂_g, F₁₂]
    rw [h_ym_eq A₁_g A₂_g h12, h_ym_eq A₁ A₂ h12,
        cov_shift_conj g d₁ A₁, cov_shift_conj g d₂ A₂,
        comm_conj_units g (d₁ + A₁) (d₂ + A₂)]
  refine ⟨?_, hF12_g, ?_, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [sheetDiag, bareDiracZorn, diracZornOp, fiberEmbed,
            A₁_g, A₂_g, A₃_g, m_g, zornGaugeTransform] <;>
      noncomm_ring
  · rw [hF23_g, hF31_g, hF12_g]
    apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring
  · rw [h_ym_eq _ _ h12, cov_shift_conj g d₁ 0, cov_shift_conj g d₂ 0,
        add_zero, add_zero, comm_conj_units g d₁ d₂, h12, mul_zero, zero_mul]

end ArchetypeGZ3_GZ4_GaugeCovarianceAndMaurerCartan

end NoncommutativeInherentZornGaugeSynthesis
```

## Turn 0099, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeUnifiedDiracHiggsZornTower

/-!
## Foundational Infrastructure: `mat2` Constructor & Inductive Tower `ClTower B n`
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

@[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

def gamma1Op   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a

def vecOp (u₁ u₂ u₃ : A) : Matrix (Fin 2) (Fin 2) A :=
  fiberEmbed u₁ * gamma1Op + fiberEmbed u₂ * sigmaOp + fiberEmbed u₃ * omegaOp

def zornDot (u₁ u₂ u₃ v₁ v₂ v₃ : A) : A :=
  u₁ * v₁ + u₂ * v₂ - u₃ * v₃

def zornCross1 (u₁ u₂ u₃ v₁ v₂ v₃ : A) : A := u₂ * v₃ - u₃ * v₂
def zornCross2 (u₁ u₂ u₃ v₁ v₂ v₃ : A) : A := u₃ * v₁ - u₁ * v₃
def zornCross3 (u₁ u₂ u₃ v₁ v₂ v₃ : A) : A := -(u₁ * v₂ - u₂ * v₁)

@[simp] lemma vecOp_00 (u₁ u₂ u₃ : A) : (vecOp u₁ u₂ u₃) 0 0 = u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_01 (u₁ u₂ u₃ : A) : (vecOp u₁ u₂ u₃) 0 1 = u₂ - u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]; rfl
@[simp] lemma vecOp_10 (u₁ u₂ u₃ : A) : (vecOp u₁ u₂ u₃) 1 0 = u₂ + u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_11 (u₁ u₂ u₃ : A) : (vecOp u₁ u₂ u₃) 1 1 = -u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end Matrix2Simp

universe u

def ClTower (B : Type u) : ℕ → Type u
  | 0     => B
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower B n)

instance instRingClTower {B : Type u} [Ring B] : ∀ n : ℕ, Ring (ClTower B n)
  | 0     => inferInstanceAs (Ring B)
  | n + 1 => by
      letI : Ring (ClTower B n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower B n)))

variable {B : Type u} [Ring B]

def kroneckerGamma (γ₀ : B) : ∀ (n : ℕ), ClTower B n
  | 0     => γ₀
  | n + 1 => mat2 (kroneckerGamma γ₀ n) 0 0 (-kroneckerGamma γ₀ n)

def towerTrace : ∀ {n : ℕ}, ClTower B n → B
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace (γ₀ : B) {n : ℕ} (M : ClTower B n) : B :=
  towerTrace (kroneckerGamma γ₀ n * M)

lemma towerTrace_add : ∀ {n : ℕ} (X Y : ClTower B n),
    towerTrace (X + Y) = towerTrace X + towerTrace Y
  | 0,     _, _ => rfl
  | _ + 1, X, Y => by
      dsimp [towerTrace]
      rw [Matrix.add_apply, Matrix.add_apply, towerTrace_add, towerTrace_add]
      abel

lemma kroneckerGamma_sq {γ₀ : B} (hγ₀ : γ₀ * γ₀ = 1) :
    ∀ (n : ℕ), kroneckerGamma γ₀ n * kroneckerGamma γ₀ n = 1
  | 0     => hγ₀
  | n + 1 => by apply ext_fin2 <;> simp [kroneckerGamma, kroneckerGamma_sq hγ₀ n]

/-!
## Archetype $\mathcal{U}\mathcal{Z}_1$: Non-Central All-Scales Dirac–Higgs Tower & Chiral Higgs Commutator Anomaly
-/

section ArchetypeUZ1_NonCentralDiracHiggsTower

/-- Non-central all-scales Dirac–Higgs tower $\mathcal{D}_n^{\mathrm{NC}} \in \mathcal{C}\ell_n(B)$
built from arbitrary non-commuting scale Higgs fields $H_n^+, H_n^- \in \mathcal{C}\ell_n(B)$. -/
def noncentralDiracTower (D₀ γ₀ : B)
    (H_plus H_minus : ∀ n : ℕ, ClTower B n) : ∀ (n : ℕ), ClTower B n
  | 0     => D₀
  | n + 1 =>
      let D_n := noncentralDiracTower D₀ γ₀ H_plus H_minus n
      let Γ_n := kroneckerGamma γ₀ n
      mat2 D_n (Γ_n * H_plus n) (Γ_n * H_minus n) D_n

/-- **Non-Central All-Scales Dirac–Higgs Tower & Chiral Higgs Commutator Anomaly Theorem ($\mathcal{U}\mathcal{Z}_1$)**:
Given $\{D_0, \gamma_0\} = 0$, $\gamma_0^2 = 1$, and arbitrary non-commuting scale Higgs operators
$H_n^+, H_n^- \in \mathcal{C}\ell_n(B)$ satisfying only $\Gamma^{(n)} H_n^\pm = H_n^\pm \Gamma^{(n)}$,
for *every* tower depth $N \in \mathbb{N}$:
1. $(\Gamma^{(N)})^2 = 1$ and $\{\mathcal{D}_N^{\mathrm{NC}}, \Gamma^{(N)}\} = 0$ (zero centrality assumptions!),
2. $(\mathcal{D}_{N+1}^{\mathrm{NC}})^2 = \bigl(\begin{smallmatrix} (\mathcal{D}_N^{\mathrm{NC}})^2 + H_N^+ H_N^- & -\Gamma^{(N)}\⁅\mathcal{D}_N^{\mathrm{NC}}, H_N^+⁆ \\ -\Gamma^{(N)}\⁅\mathcal{D}_N^{\mathrm{NC}}, H_N^-⁆ & (\mathcal{D}_N^{\mathrm{NC}})^2 + H_N^- H_N^+ \end{smallmatrix}\bigr)$,
3. *Chiral Higgs Commutator Anomaly*:
   $\mathrm{Str}_{2^{N+1}}\big((\mathcal{D}_{N+1}^{\mathrm{NC}})^2\big) = \mathrm{Str}_{2^N}\big(\⁅H_N^+, H_N^-⁆\big)$. -/
theorem noncentral_all_scales_dirac_higgs_tower_and_anomaly
    (D₀ γ₀ : B) (H_plus H_minus : ∀ n : ℕ, ClTower B n)
    (h_anti₀ : D₀ * γ₀ + γ₀ * D₀ = 0)
    (h_γ₀_sq : γ₀ * γ₀ = 1)
    (hH_plus_even : ∀ n : ℕ, kroneckerGamma γ₀ n * H_plus n = H_plus n * kroneckerGamma γ₀ n)
    (hH_minus_even : ∀ n : ℕ, kroneckerGamma γ₀ n * H_minus n = H_minus n * kroneckerGamma γ₀ n)
    (N : ℕ) :
    let D_N  := noncentralDiracTower D₀ γ₀ H_plus H_minus N
    let D_N1 := noncentralDiracTower D₀ γ₀ H_plus H_minus (N + 1)
    let Γ_N  := kroneckerGamma γ₀ N
    Γ_N * Γ_N = 1 ∧
    D_N * Γ_N + Γ_N * D_N = 0 ∧
    D_N1 * D_N1 =
      mat2 (D_N * D_N + H_plus N * H_minus N) (-Γ_N * ⁅D_N, H_plus N⁆)
           (-Γ_N * ⁅D_N, H_minus N⁆) (D_N * D_N + H_minus N * H_plus N) ∧
    superTrace γ₀ (D_N1 * D_N1) = superTrace γ₀ ⁅H_plus N, H_minus N⁆ := by
  intro D_N D_N1 Γ_N
  have h_anti_all : ∀ (n : ℕ),
      noncentralDiracTower D₀ γ₀ H_plus H_minus n * kroneckerGamma γ₀ n +
      kroneckerGamma γ₀ n * noncentralDiracTower D₀ γ₀ H_plus H_minus n = 0 := by
    intro n; induction' n with k ih
    · exact h_anti₀
    · have h_off1 : -(kroneckerGamma γ₀ k * H_plus k * kroneckerGamma γ₀ k) +
          kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_plus k) = 0 := by
        calc -(kroneckerGamma γ₀ k * H_plus k * kroneckerGamma γ₀ k) +
             kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_plus k)
          _ = -(kroneckerGamma γ₀ k * (H_plus k * kroneckerGamma γ₀ k)) +
              kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_plus k) := by noncomm_ring
          _ = 0 := by rw [← hH_plus_even k]; abel
      have h_off2 : kroneckerGamma γ₀ k * H_minus k * kroneckerGamma γ₀ k -
          kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k) = 0 := by
        calc kroneckerGamma γ₀ k * H_minus k * kroneckerGamma γ₀ k -
             kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k)
          _ = kroneckerGamma γ₀ k * (H_minus k * kroneckerGamma γ₀ k) -
              kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k) := by noncomm_ring
          _ = 0 := by rw [← hH_minus_even k]; abel
      apply ext_fin2
      · simp [noncentralDiracTower, kroneckerGamma, ih]
      · simp [noncentralDiracTower, kroneckerGamma, h_off1]
      · simp [noncentralDiracTower, kroneckerGamma, h_off2]
      · simp [noncentralDiracTower, kroneckerGamma]
        calc -(noncentralDiracTower D₀ γ₀ H_plus H_minus k * kroneckerGamma γ₀ k) -
             kroneckerGamma γ₀ k * noncentralDiracTower D₀ γ₀ H_plus H_minus k
          _ = -(noncentralDiracTower D₀ γ₀ H_plus H_minus k * kroneckerGamma γ₀ k +
                kroneckerGamma γ₀ k * noncentralDiracTower D₀ γ₀ H_plus H_minus k) := by abel
          _ = 0 := by rw [ih, neg_zero]
  have hΓ_sq := kroneckerGamma_sq h_γ₀_sq N
  have hD_anti := h_anti_all N
  have hDΓ : D_N * Γ_N = -(Γ_N * D_N) := eq_neg_of_add_eq_zero_left hD_anti
  have h_prod : ∀ (X Y : ClTower B N), Γ_N * X = X * Γ_N →
      (Γ_N * X) * (Γ_N * Y) = X * Y := by
    intro X Y hX
    calc (Γ_N * X) * (Γ_N * Y) = Γ_N * (X * Γ_N) * Y := by noncomm_ring
      _ = Γ_N * (Γ_N * X) * Y := by rw [hX]
      _ = (Γ_N * Γ_N) * (X * Y) := by noncomm_ring
      _ = X * Y := by rw [hΓ_sq, one_mul]
  have h_cross : ∀ (X : ClTower B N),
      D_N * (Γ_N * X) + (Γ_N * X) * D_N = -Γ_N * ⁅D_N, X⁆ := by
    intro X; rw [Ring.lie_def]
    calc D_N * (Γ_N * X) + (Γ_N * X) * D_N
      _ = (D_N * Γ_N) * X + Γ_N * (X * D_N) := by noncomm_ring
      _ = -(Γ_N * D_N) * X + Γ_N * (X * D_N) := by rw [hDΓ]
      _ = -Γ_N * (D_N * X - X * D_N) := by noncomm_ring
  have h_sq : D_N1 * D_N1 =
      mat2 (D_N * D_N + H_plus N * H_minus N) (-Γ_N * ⁅D_N, H_plus N⁆)
           (-Γ_N * ⁅D_N, H_minus N⁆) (D_N * D_N + H_minus N * H_plus N) := by
    apply ext_fin2 <;>
      simp [D_N1, noncentralDiracTower, h_prod (H_plus N) (H_minus N) (hH_plus_even N),
            h_prod (H_minus N) (H_plus N) (hH_minus_even N),
            h_cross (H_plus N), h_cross (H_minus N)]
  refine ⟨hΓ_sq, hD_anti, h_sq, ?_⟩
  rw [h_sq]
  dsimp [superTrace, kroneckerGamma, towerTrace]
  simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
    mul_zero, zero_mul, add_zero, zero_add, neg_mul, ← towerTrace_add]
  congr 1
  rw [Ring.lie_def]
  noncomm_ring

end ArchetypeUZ1_NonCentralDiracHiggsTower

/-!
## Archetype $\mathcal{U}\mathcal{Z}_2$, $\mathcal{U}\mathcal{Z}_3$ & $\mathcal{U}\mathcal{Z}_4$: All-Scales Inherent Zorn Gauge Emergence, Pauli–Yang–Mills Wave Square, Bianchi Identity & Maurer–Cartan Flatness on $\mathcal{C}\ell_{n+2}(B)$
-/

section ArchetypeUZ2_UZ3_UZ4_AllScalesZornGaugeTower

/-- Covariant two-sheeted Dirac–Zorn operator at scale $n + 2$ in $\mathcal{C}\ell_{n+2}(B)$. -/
def diracZornTower (n : ℕ) (α β u₁ u₂ u₃ v₁ v₂ v₃ : ClTower B n) : ClTower B (n + 2) :=
  mat2 (fiberEmbed α) (vecOp u₁ u₂ u₃) (vecOp v₁ v₂ v₃) (fiberEmbed β)

/-- Bare un-gauged Dirac–Zorn operator at scale $n + 2$. -/
def bareDiracZornTower (n : ℕ) (m₀ d₁ d₂ d₃ : ClTower B n) : ClTower B (n + 2) :=
  diracZornTower n m₀ (-m₀) d₁ d₂ d₃ d₁ d₂ d₃

/-- Diagonal two-sheet element at scale $n + 2$. -/
def sheetDiagTower (n : ℕ) (u v : ClTower B n) : ClTower B (n + 2) :=
  mat2 (fiberEmbed u) 0 0 (fiberEmbed v)

/-- Non-Abelian Yang–Mills field strength component $F_{ij}(\mathbf{d}, \mathbf{A}) \in \mathcal{C}\ell_n(B)$. -/
def ymFieldStrength {R : Type*} [Ring R] (dᵢ dⱼ Aᵢ Aⱼ : R) : R :=
  ⁅dᵢ, Aⱼ⁆ - ⁅dⱼ, Aᵢ⁆ + ⁅Aᵢ, Aⱼ⁆

/-- Inherent affine gauge transformation $A_k^g = g(d_k + A_k)g^{-1} - d_k$ in $\mathcal{C}\ell_n(B)$. -/
def zornGaugeTransform {R : Type*} [Ring R] (g : Rˣ) (dₖ Aₖ : R) : R :=
  (g : R) * (dₖ + Aₖ) * (↑g⁻¹ : R) - dₖ

lemma zorn_vec_sq {R : Type*} [Ring R] (D₁ D₂ D₃ : R) :
    vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃ =
      fiberEmbed (D₁ * D₁ + D₂ * D₂ - D₃ * D₃) +
      vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆) := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring

lemma cov_shift_conj {R : Type*} [Ring R] (g : Rˣ) (dₖ Aₖ : R) :
    dₖ + zornGaugeTransform g dₖ Aₖ = (g : R) * (dₖ + Aₖ) * (↑g⁻¹ : R) := by
  dsimp [zornGaugeTransform]; abel

lemma comm_conj_units {R : Type*} [Ring R] (g : Rˣ) (X Y : R) :
    ⁅(g : R) * X * (↑g⁻¹ : R), (g : R) * Y * (↑g⁻¹ : R)⁆ =
      (g : R) * ⁅X, Y⁆ * (↑g⁻¹ : R) := by
  have hg : (↑g⁻¹ : R) * (g : R) = 1 := Units.inv_mul g
  rw [Ring.lie_def, Ring.lie_def]
  calc (g : R) * X * (↑g⁻¹ : R) * ((g : R) * Y * (↑g⁻¹ : R)) -
       (g : R) * Y * (↑g⁻¹ : R) * ((g : R) * X * (↑g⁻¹ : R))
    _ = (g : R) * X * ((↑g⁻¹ : R) * (g : R)) * Y * (↑g⁻¹ : R) -
        (g : R) * Y * ((↑g⁻¹ : R) * (g : R)) * X * (↑g⁻¹ : R) := by noncomm_ring
    _ = (g : R) * (X * Y - Y * X) * (↑g⁻¹ : R) := by rw [hg]; noncomm_ring

/-- **All-Scales Inherent Zorn Gauge, Pauli–Yang–Mills Wave Square, Bianchi & Maurer–Cartan Theorem ($\mathcal{U}\mathcal{Z}_2$–$\mathcal{U}\mathcal{Z}_4$)**:
At every scale $n \in \mathbb{N}$ in $\mathcal{C}\ell_{n+2}(B) = M_2(M_2(\mathcal{C}\ell_n(B)))$, for flat
reference operators ($\⁅d_i, d_j⁆ = 0 \in \mathcal{C}\ell_n(B)$), gauge potentials $A_1, A_2, A_3 \in \mathcal{C}\ell_n(B)$,
mass $m \in \mathcal{C}\ell_n(B)$, and gauge transformation $g \in (\mathcal{C}\ell_n(B))^\times$:
1. *Inherent Gauge & Higgs Generation*: $\⁅\mathcal{D}_0^{(n)}(m, \mathbf{d}), \mathbb{U}(u, v)⁆$ populates
   the Zorn vector slots with $d_k v - u d_k$ and diagonal slots with $\⁅m, u⁆, -\⁅m, v⁆$.
2. *Covariant Pauli–Yang–Mills Wave Square*: $(\mathcal{D}_{\mathrm{Zorn}}(m, -m, \mathbf{d}+\mathbf{A}, \mathbf{d}+\mathbf{A}))^2$
   has diagonal blocks $\iota(m^2 + D_1^2 + D_2^2 - D_3^2) + \mathrm{vecOp}(F_{23}, F_{31}, -F_{12})$
   and off-diagonal Yukawa blocks $\pm\⁅\iota(m), \mathrm{vecOp}(\mathbf{D})⁆$.
3. *Non-Abelian Bianchi Identity*: $\⁅D_1, F_{23}⁆ + \⁅D_2, F_{31}⁆ + \⁅D_3, F_{12}⁆ = 0$.
4. *Homogeneous Zorn Curvature Covariance & Maurer–Cartan Flatness*:
   $\mathrm{vecOp}(F_{23}^g, F_{31}^g, -F_{12}^g) = \iota(g)\,\mathrm{vecOp}(F_{23}, F_{31}, -F_{12})\,\iota(g^{-1})$,
   and $F_{12}(\mathbf{d}, \mathbf{A}^{\mathrm{MC}}(g)) = 0$. -/
theorem all_scales_inherent_zorn_gauge_pauli_bianchi_and_maurer_cartan
    (n : ℕ) (m d₁ d₂ d₃ A₁ A₂ A₃ u v : ClTower B n) (g : (ClTower B n)ˣ)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁    := d₁ + A₁
    let D₂    := d₂ + A₂
    let D₃    := d₃ + A₃
    let F₂₃   := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁   := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂   := ymFieldStrength d₁ d₂ A₁ A₂
    let A₁_g  := zornGaugeTransform g d₁ A₁
    let A₂_g  := zornGaugeTransform g d₂ A₂
    let A₃_g  := zornGaugeTransform g d₃ A₃
    let F₂₃_g := ymFieldStrength d₂ d₃ A₂_g A₃_g
    let F₃₁_g := ymFieldStrength d₃ d₁ A₃_g A₁_g
    let F₁₂_g := ymFieldStrength d₁ d₂ A₁_g A₂_g
    let D_cov := bareDiracZornTower n m D₁ D₂ D₃
    ⁅bareDiracZornTower n m d₁ d₂ d₃, sheetDiagTower n u v⁆ =
      diracZornTower n ⁅m, u⁆ (-⁅m, v⁆)
        (d₁ * v - u * d₁) (d₂ * v - u * d₂) (d₃ * v - u * d₃)
        (d₁ * u - v * d₁) (d₂ * u - v * d₂) (d₃ * u - v * d₃) ∧
    D_cov * D_cov =
      mat2
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp F₂₃ F₃₁ (-F₁₂))
        ⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆
        (-⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆)
        (fiberEmbed (m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)) +
         vecOp F₂₃ F₃₁ (-F₁₂)) ∧
    ⁅D₁, F₂₃⁆ + ⁅D₂, F₃₁⁆ + ⁅D₃, F₁₂⁆ = 0 ∧
    vecOp F₂₃_g F₃₁_g (-F₁₂_g) =
      fiberEmbed (g : ClTower B n) * vecOp F₂₃ F₃₁ (-F₁₂) *
      fiberEmbed (↑g⁻¹ : ClTower B n) ∧
    ymFieldStrength d₁ d₂ (zornGaugeTransform g d₁ 0) (zornGaugeTransform g d₂ 0) = 0 := by
  intro D₁ D₂ D₃ F₂₃ F₃₁ F₁₂ A₁_g A₂_g A₃_g F₂₃_g F₃₁_g F₁₂_g D_cov
  have h_ym_eq : ∀ {x₁ x₂ : ClTower B n} (y₁ y₂ : ClTower B n), ⁅x₁, x₂⁆ = 0 →
      ymFieldStrength x₁ x₂ y₁ y₂ = ⁅x₁ + y₁, x₂ + y₂⁆ := by
    intro x₁ x₂ y₁ y₂ hx
    dsimp [ymFieldStrength]; rw [← hx]; simp only [Ring.lie_def]; noncomm_ring
  have hF23 : F₂₃ = ⁅D₂, D₃⁆ := h_ym_eq A₂ A₃ h23
  have hF31 : F₃₁ = ⁅D₃, D₁⁆ := h_ym_eq A₃ A₁ h31
  have hF12 : F₁₂ = ⁅D₁, D₂⁆ := h_ym_eq A₁ A₂ h12
  have hF23_g : F₂₃_g = (g : ClTower B n) * F₂₃ * (↑g⁻¹ : ClTower B n) := by
    dsimp [F₂₃_g]; rw [h_ym_eq A₂_g A₃_g h23, hF23,
      cov_shift_conj g d₂ A₂, cov_shift_conj g d₃ A₃, comm_conj_units g D₂ D₃]
  have hF31_g : F₃₁_g = (g : ClTower B n) * F₃₁ * (↑g⁻¹ : ClTower B n) := by
    dsimp [F₃₁_g]; rw [h_ym_eq A₃_g A₁_g h31, hF31,
      cov_shift_conj g d₃ A₃, cov_shift_conj g d₁ A₁, comm_conj_units g D₃ D₁]
  have hF12_g : F₁₂_g = (g : ClTower B n) * F₁₂ * (↑g⁻¹ : ClTower B n) := by
    dsimp [F₁₂_g]; rw [h_ym_eq A₁_g A₂_g h12, hF12,
      cov_shift_conj g d₁ A₁, cov_shift_conj g d₂ A₂, comm_conj_units g D₁ D₂]
  have h_add_emb : ∀ (a b : ClTower B n), fiberEmbed a + fiberEmbed b = fiberEmbed (a + b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_mul_emb : ∀ (a b : ClTower B n), fiberEmbed a * fiberEmbed b = fiberEmbed (a * b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_neg_emb : ∀ (a : ClTower B n), fiberEmbed (-a) = -fiberEmbed a := by
    intro a; apply ext_fin2 <;> simp [fiberEmbed]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [bareDiracZornTower, diracZornTower, sheetDiagTower, fiberEmbed] <;>
      noncomm_ring
  · rw [hF23, hF31, hF12, Ring.lie_def]
    apply ext_fin2
    · simp only [D_cov, bareDiracZornTower, diracZornTower, mul2_00, mat2_00, mat2_01, mat2_10,
        h_mul_emb, zorn_vec_sq D₁ D₂ D₃, ← add_assoc, h_add_emb]
    · simp only [D_cov, bareDiracZornTower, diracZornTower, mul2_01, mat2_00, mat2_01, mat2_11,
        h_neg_emb, mul_neg, sub_eq_add_neg]
    · simp only [D_cov, bareDiracZornTower, diracZornTower, mul2_10, mat2_10, mat2_00, mat2_11,
        h_neg_emb, neg_mul]
      abel
    · simp only [D_cov, bareDiracZornTower, diracZornTower, mul2_11, mat2_10, mat2_01, mat2_11,
        h_neg_emb, neg_mul_neg, h_mul_emb]
      rw [add_comm (vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃),
          zorn_vec_sq D₁ D₂ D₃, ← add_assoc, h_add_emb]
  · rw [hF23, hF31, hF12]
    simp only [Ring.lie_def]
    noncomm_ring
  · rw [hF23_g, hF31_g, hF12_g]
    apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring
  · rw [h_ym_eq _ _ h12, cov_shift_conj g d₁ 0, cov_shift_conj g d₂ 0,
        add_zero, add_zero, comm_conj_units g d₁ d₂, h12, mul_zero, zero_mul]

end ArchetypeUZ2_UZ3_UZ4_AllScalesZornGaugeTower

end NoncommutativeUnifiedDiracHiggsZornTower
```

## Turn 0102, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeYangMillsHiggsSpectralAction

/-!
## Foundational Infrastructure: `mat2` Constructor & 3D Zorn Vector Operators
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {B : Type*} [Ring B]

@[simp] lemma mat2_00 (a b c d : B) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : B) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : B) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : B) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) B) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) B) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) B) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) B) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : (star M) 1 1 = star (M 1 1) := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op   : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) B := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) B := mat2 0 (-1) 1 0
def fiberEmbed (a : B) : Matrix (Fin 2) (Fin 2) B := mat2 a 0 0 a

def vecOp (u₁ u₂ u₃ : B) : Matrix (Fin 2) (Fin 2) B :=
  fiberEmbed u₁ * gamma1Op + fiberEmbed u₂ * sigmaOp + fiberEmbed u₃ * omegaOp

@[simp] lemma vecOp_00 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 0 = u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_01 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 1 = u₂ - u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]; rfl
@[simp] lemma vecOp_10 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 0 = u₂ + u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_11 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 1 = -u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end Matrix2Simp

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-!
## Archetype $\mathcal{S}\mathcal{A}_1$: 4-Channel Zorn–Tetraktys Hilbert–Schmidt Pythagoras in $M_2(B)$
-/

section ArchetypeSA1_ZornTetraktysPythagoras

variable {B : Type*} [Ring B] [StarRing B]

/-- **4-Channel Zorn–Tetraktys Hilbert–Schmidt Pythagorean Theorem ($\mathcal{S}\mathcal{A}_1$)**:
For any scalar $s \in B$ and 3-vector $(v_1, v_2, v_3) \in B^3$ (without commutativity or
self-adjointness assumptions), $W = \iota(s) + \mathrm{vecOp}(v_1, v_2, v_3)$ satisfies
$\mathrm{Tr}_2(W^\dagger W) = 2 \bullet (s^\star s + v_1^\star v_1 + v_2^\star v_2 + v_3^\star v_3)$. -/
theorem zorn_tetraktys_hilbert_schmidt_pythagoras (s v₁ v₂ v₃ : B) :
    let W : Matrix (Fin 2) (Fin 2) B := fiberEmbed s + vecOp v₁ v₂ v₃
    Matrix.trace (Wᴴ * W) =
      2 • (star s * s + star v₁ * v₁ + star v₂ * v₂ + star v₃ * v₃) := by
  simp [fiberEmbed, two_smul]
  noncomm_ring

end ArchetypeSA1_ZornTetraktysPythagoras

/-!
## Archetype $\mathcal{S}\mathcal{A}_2$: Unified Yang–Mills–Higgs–Klein–Gordon Quartic Spectral Action in $M_2(M_2(B))$
-/

section ArchetypeSA2_UnifiedYangMillsHiggsSpectralAction

variable {B : Type*} [Ring B]

def diracZornOp (α β u₁ u₂ u₃ v₁ v₂ v₃ : B) : NestedMat B :=
  mat2 (fiberEmbed α) (vecOp u₁ u₂ u₃) (vecOp v₁ v₂ v₃) (fiberEmbed β)

def bareDiracZorn (m₀ d₁ d₂ d₃ : B) : NestedMat B :=
  diracZornOp m₀ (-m₀) d₁ d₂ d₃ d₁ d₂ d₃

def ymFieldStrength (dᵢ dⱼ Aᵢ Aⱼ : B) : B :=
  ⁅dᵢ, Aⱼ⁆ - ⁅dⱼ, Aᵢ⁆ + ⁅Aᵢ, Aⱼ⁆

/-- 2-scale trace $\mathrm{Tr}_4(\mathbb{M}) = \mathrm{Tr}_2(\mathbb{M}_{00}) + \mathrm{Tr}_2(\mathbb{M}_{11})$ on $M_2(M_2(B))$. -/
def trace4 (𝕄 : NestedMat B) : B :=
  Matrix.trace (𝕄 0 0) + Matrix.trace (𝕄 1 1)

lemma zorn_vec_sq (D₁ D₂ D₃ : B) :
    vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃ =
      fiberEmbed (D₁ * D₁ + D₂ * D₂ - D₃ * D₃) +
      vecOp ⁅D₂, D₃⁆ ⁅D₃, D₁⁆ (-⁅D₁, D₂⁆) := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring

lemma comm_fiberEmbed_vecOp (m D₁ D₂ D₃ : B) :
    ⁅fiberEmbed m, vecOp D₁ D₂ D₃⁆ = vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆ := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring

lemma covariant_dirac_zorn_sq_ym
    (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁    := d₁ + A₁
    let D₂    := d₂ + A₂
    let D₃    := d₃ + A₃
    let Δ_KG  := m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)
    let F₂₃   := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁   := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂   := ymFieldStrength d₁ d₂ A₁ A₂
    let D_cov := bareDiracZorn m D₁ D₂ D₃
    D_cov * D_cov =
      mat2
        (fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂))
        (vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)
        (-vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)
        (fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂)) := by
  intro D₁ D₂ D₃ Δ_KG F₂₃ F₃₁ F₁₂ D_cov
  have h_ym : ∀ {x₁ x₂ : B} (y₁ y₂ : B), ⁅x₁, x₂⁆ = 0 →
      ⁅x₁ + y₁, x₂ + y₂⁆ = ymFieldStrength x₁ x₂ y₁ y₂ := by
    intro x₁ x₂ y₁ y₂ hx
    dsimp [ymFieldStrength]; rw [← hx]; simp only [Ring.lie_def]; noncomm_ring
  have hF23 : ⁅D₂, D₃⁆ = F₂₃ := h_ym A₂ A₃ h23
  have hF31 : ⁅D₃, D₁⁆ = F₃₁ := h_ym A₃ A₁ h31
  have hF12 : ⁅D₁, D₂⁆ = F₁₂ := h_ym A₁ A₂ h12
  have h_add_emb : ∀ (a b : B), fiberEmbed a + fiberEmbed b = fiberEmbed (a + b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_mul_emb : ∀ (a b : B), fiberEmbed a * fiberEmbed b = fiberEmbed (a * b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_neg_emb : ∀ (a : B), fiberEmbed (-a) = -fiberEmbed a := by
    intro a; apply ext_fin2 <;> simp [fiberEmbed]
  have h_comm := comm_fiberEmbed_vecOp m D₁ D₂ D₃
  rw [Ring.lie_def] at h_comm
  apply ext_fin2
  · simp only [D_cov, bareDiracZorn, diracZornOp, mul2_00, mat2_00, mat2_01, mat2_10,
      h_mul_emb, zorn_vec_sq D₁ D₂ D₃, hF23, hF31, hF12, ← add_assoc, h_add_emb]
  · simp only [D_cov, bareDiracZorn, diracZornOp, mul2_01, mat2_00, mat2_01, mat2_11,
      h_neg_emb, mul_neg, ← sub_eq_add_neg, h_comm]
  · simp only [D_cov, bareDiracZorn, diracZornOp, mul2_10, mat2_10, mat2_00, mat2_11,
      h_neg_emb, neg_mul, ← h_comm]
    abel
  · simp only [D_cov, bareDiracZorn, diracZornOp, mul2_11, mat2_10, mat2_01, mat2_11,
      h_neg_emb, neg_mul_neg, h_mul_emb]
    rw [add_comm (vecOp D₁ D₂ D₃ * vecOp D₁ D₂ D₃),
        zorn_vec_sq D₁ D₂ D₃, hF23, hF31, hF12, ← add_assoc, h_add_emb]

/-- **Unified Yang–Mills–Higgs–Klein–Gordon Quartic Spectral Action Theorem ($\mathcal{S}\mathcal{A}_2$)**:
Over any noncommutative $\star$-ring $B$ with flat background derivatives ($\⁅d_i, d_j⁆ = 0$),
the quartic spectral action $\mathrm{Tr}_4((\mathcal{D}_{\mathrm{cov}}^2)^\dagger \mathcal{D}_{\mathrm{cov}}^2)$
decomposes into four times the sum of the Klein–Gordon square $\Delta_{\mathrm{KG}}^\star \Delta_{\mathrm{KG}}$,
the three Yang–Mills field-strength squares $F_{ij}^\star F_{ij}$, and the three covariant Higgs
kinetic squares $\⁅m, D_k⁆^\star \⁅m, D_k⁆$. -/
theorem unified_yang_mills_higgs_dirac_spectral_action [StarRing B]
    (m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0) :
    let D₁    := d₁ + A₁
    let D₂    := d₂ + A₂
    let D₃    := d₃ + A₃
    let Δ_KG  := m * m + (D₁ * D₁ + D₂ * D₂ - D₃ * D₃)
    let F₂₃   := ymFieldStrength d₂ d₃ A₂ A₃
    let F₃₁   := ymFieldStrength d₃ d₁ A₃ A₁
    let F₁₂   := ymFieldStrength d₁ d₂ A₁ A₂
    let D_cov := bareDiracZorn m D₁ D₂ D₃
    trace4 ((D_cov * D_cov)ᴴ * (D_cov * D_cov)) =
      4 • (star Δ_KG * Δ_KG +
           (star F₂₃ * F₂₃ + star F₃₁ * F₃₁ + star F₁₂ * F₁₂) +
           (star ⁅m, D₁⁆ * ⁅m, D₁⁆ + star ⁅m, D₂⁆ * ⁅m, D₂⁆ + star ⁅m, D₃⁆ * ⁅m, D₃⁆)) := by
  intro D₁ D₂ D₃ Δ_KG F₂₃ F₃₁ F₁₂ D_cov
  rw [covariant_dirac_zorn_sq_ym m d₁ d₂ d₃ A₁ A₂ A₃ h23 h31 h12]
  dsimp [trace4]
  simp only [mul2_00, mul2_11, ct2_00, ct2_01, ct2_10, ct2_11,
    mat2_00, mat2_01, mat2_10, mat2_11, star_neg, neg_mul_neg]
  have hW := zorn_tetraktys_hilbert_schmidt_pythagoras Δ_KG F₂₃ F₃₁ (-F₁₂)
  have hY := zorn_tetraktys_hilbert_schmidt_pythagoras 0 ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆
  have h0 : fiberEmbed (0 : B) + vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆ =
      vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆ := by
    apply ext_fin2 <;> simp [fiberEmbed]
  rw [h0] at hY
  have h_tr_add : ∀ (X Y : Matrix (Fin 2) (Fin 2) B),
      Matrix.trace (X + Y) = Matrix.trace X + Matrix.trace Y := by
    intro X Y; simp; abel
  rw [h_tr_add, h_tr_add]
  change Matrix.trace ((fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂))ᴴ *
                       (fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂))) +
         Matrix.trace ((vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)ᴴ *
                       vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆) +
        (Matrix.trace ((vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆)ᴴ *
                       vecOp ⁅m, D₁⁆ ⁅m, D₂⁆ ⁅m, D₃⁆) +
         Matrix.trace ((fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂))ᴴ *
                       (fiberEmbed Δ_KG + vecOp F₂₃ F₃₁ (-F₁₂)))) = _
  rw [hW, hY]
  simp only [star_zero, zero_mul, zero_add, star_neg, neg_mul_neg, nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

end ArchetypeSA2_UnifiedYangMillsHiggsSpectralAction

/-!
## Archetype $\mathcal{S}\mathcal{A}_3$: Noncommutative Bogomolny–Prasad–Sommerfield (BPS) Monopole Bound & Bianchi–Laplace Harmonicity
-/

section ArchetypeSA3_BPSMonopoleAndBianchiHarmonicity

variable {B : Type*} [Ring B] [StarRing B]

/-- Topological BPS magnetic monopole flux $\mathcal{Q}_{\mathrm{BPS}} = \sum_{\mathrm{cyc}} (F_{jk}^\star G_i + G_i^\star F_{jk})$. -/
def bpsMonopoleFlux (F₂₃ F₃₁ F₁₂ G₁ G₂ G₃ : B) : B :=
  (star F₂₃ * G₁ + star G₁ * F₂₃) +
  (star F₃₁ * G₂ + star G₂ * F₃₁) +
  (star F₁₂ * G₃ + star G₃ * F₁₂)

/-- **Noncommutative BPS Monopole Completion of the Square & Bianchi–Laplace Harmonicity ($\mathcal{S}\mathcal{A}_3$)**:
1. *BPS Completion of the Square*:
   $\sum (F_{jk}^\star F_{jk} + G_i^\star G_i) = \sum (F_{jk} - G_i)^\star (F_{jk} - G_i) + \mathcal{Q}_{\mathrm{BPS}}$.
2. *BPS Bianchi–Laplace Harmonicity*: Whenever the Bogomolny self-duality equations
   $F_{23} = \⁅D_1, m⁆, F_{31} = \⁅D_2, m⁆, F_{12} = \⁅D_3, m⁆$ hold on a flat background
   ($\⁅d_i, d_j⁆ = 0$), the Higgs field $m$ satisfies the 3D covariant Laplace equation:
   $\⁅D_1, \⁅D_1, m⁆⁆ + \⁅D_2, \⁅D_2, m⁆⁆ + \⁅D_3, \⁅D_3, m⁆⁆ = 0$. -/
theorem noncommutative_bps_monopole_bound_and_bianchi_harmonicity
    (F₂₃ F₃₁ F₁₂ G₁ G₂ G₃ m d₁ d₂ d₃ A₁ A₂ A₃ : B)
    (h23 : ⁅d₂, d₃⁆ = 0) (h31 : ⁅d₃, d₁⁆ = 0) (h12 : ⁅d₁, d₂⁆ = 0)
    (h_bps1 : ymFieldStrength d₂ d₃ A₂ A₃ = ⁅d₁ + A₁, m⁆)
    (h_bps2 : ymFieldStrength d₃ d₁ A₃ A₁ = ⁅d₂ + A₂, m⁆)
    (h_bps3 : ymFieldStrength d₁ d₂ A₁ A₂ = ⁅d₃ + A₃, m⁆) :
    let D₁ := d₁ + A₁
    let D₂ := d₂ + A₂
    let D₃ := d₃ + A₃
    (star F₂₃ * F₂₃ + star F₃₁ * F₃₁ + star F₁₂ * F₁₂) +
    (star G₁ * G₁ + star G₂ * G₂ + star G₃ * G₃) =
      star (F₂₃ - G₁) * (F₂₃ - G₁) +
      star (F₃₁ - G₂) * (F₃₁ - G₂) +
      star (F₁₂ - G₃) * (F₁₂ - G₃) +
      bpsMonopoleFlux F₂₃ F₃₁ F₁₂ G₁ G₂ G₃ ∧
    ⁅D₁, ⁅D₁, m⁆⁆ + ⁅D₂, ⁅D₂, m⁆⁆ + ⁅D₃, ⁅D₃, m⁆⁆ = 0 := by
  intro D₁ D₂ D₃
  refine ⟨?_, ?_⟩
  · dsimp [bpsMonopoleFlux]
    simp only [star_sub]
    noncomm_ring
  · rw [← h_bps1, ← h_bps2, ← h_bps3]
    have h_ym : ∀ {x₁ x₂ : B} (y₁ y₂ : B), ⁅x₁, x₂⁆ = 0 →
        ymFieldStrength x₁ x₂ y₁ y₂ = ⁅x₁ + y₁, x₂ + y₂⁆ := by
      intro x₁ x₂ y₁ y₂ hx
      dsimp [ymFieldStrength]; rw [← hx]; simp only [Ring.lie_def]; noncomm_ring
    rw [h_ym A₂ A₃ h23, h_ym A₃ A₁ h31, h_ym A₁ A₂ h12]
    simp only [Ring.lie_def]
    noncomm_ring

end ArchetypeSA3_BPSMonopoleAndBianchiHarmonicity

/-!
## Archetype $\mathcal{S}\mathcal{A}_4$: Eliminating `hm_central` — Non-Central All-Scales Dirac–Higgs Tower & Chiral Higgs Anomaly
-/

section ArchetypeSA4_NonCentralAllScalesDiracHiggs

universe u

def ClTower (B : Type u) : ℕ → Type u
  | 0     => B
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower B n)

instance instRingClTower {B : Type u} [Ring B] : ∀ n : ℕ, Ring (ClTower B n)
  | 0     => inferInstanceAs (Ring B)
  | n + 1 => by
      letI : Ring (ClTower B n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower B n)))

variable {B : Type u} [Ring B]

def kroneckerGamma (γ₀ : B) : ∀ (n : ℕ), ClTower B n
  | 0     => γ₀
  | n + 1 => mat2 (kroneckerGamma γ₀ n) 0 0 (-kroneckerGamma γ₀ n)

def towerTrace : ∀ {n : ℕ}, ClTower B n → B
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace (γ₀ : B) {n : ℕ} (M : ClTower B n) : B :=
  towerTrace (kroneckerGamma γ₀ n * M)

lemma towerTrace_add : ∀ {n : ℕ} (X Y : ClTower B n),
    towerTrace (X + Y) = towerTrace X + towerTrace Y
  | 0,     _, _ => rfl
  | _ + 1, X, Y => by
      dsimp [towerTrace]
      rw [Matrix.add_apply, Matrix.add_apply, towerTrace_add, towerTrace_add]
      abel

lemma kroneckerGamma_sq {γ₀ : B} (hγ₀ : γ₀ * γ₀ = 1) :
    ∀ (n : ℕ), kroneckerGamma γ₀ n * kroneckerGamma γ₀ n = 1
  | 0     => hγ₀
  | n + 1 => by apply ext_fin2 <;> simp [kroneckerGamma, kroneckerGamma_sq hγ₀ n]

def noncentralDiracTower (D₀ γ₀ : B)
    (H_plus H_minus : ∀ n : ℕ, ClTower B n) : ∀ (n : ℕ), ClTower B n
  | 0     => D₀
  | n + 1 =>
      let D_n := noncentralDiracTower D₀ γ₀ H_plus H_minus n
      let Γ_n := kroneckerGamma γ₀ n
      mat2 D_n (Γ_n * H_plus n) (Γ_n * H_minus n) D_n

/-- **Non-Central All-Scales Dirac–Higgs Tower & Chiral Higgs Anomaly ($\mathcal{S}\mathcal{A}_4$)**:
Without assuming `hm_central`, any chirality-even Higgs sequence $\Gamma^{(n)} H_n^\pm = H_n^\pm \Gamma^{(n)}$
preserves $\{\mathcal{D}_N^{\mathrm{NC}}, \Gamma^{(N)}\} = 0$ for all $N \in \mathbb{N}$ and yields
$\mathrm{Str}_{2^{N+1}}((\mathcal{D}_{N+1}^{\mathrm{NC}})^2) = \mathrm{Str}_{2^N}(\⁅H_N^+, H_N^-⁆)$. -/
theorem noncentral_all_scales_dirac_higgs_tower_and_anomaly
    (D₀ γ₀ : B) (H_plus H_minus : ∀ n : ℕ, ClTower B n)
    (h_anti₀ : D₀ * γ₀ + γ₀ * D₀ = 0)
    (h_γ₀_sq : γ₀ * γ₀ = 1)
    (hH_plus_even : ∀ n : ℕ, kroneckerGamma γ₀ n * H_plus n = H_plus n * kroneckerGamma γ₀ n)
    (hH_minus_even : ∀ n : ℕ, kroneckerGamma γ₀ n * H_minus n = H_minus n * kroneckerGamma γ₀ n)
    (N : ℕ) :
    let D_N  := noncentralDiracTower D₀ γ₀ H_plus H_minus N
    let D_N1 := noncentralDiracTower D₀ γ₀ H_plus H_minus (N + 1)
    let Γ_N  := kroneckerGamma γ₀ N
    Γ_N * Γ_N = 1 ∧
    D_N * Γ_N + Γ_N * D_N = 0 ∧
    D_N1 * D_N1 =
      mat2 (D_N * D_N + H_plus N * H_minus N) (-Γ_N * ⁅D_N, H_plus N⁆)
           (-Γ_N * ⁅D_N, H_minus N⁆) (D_N * D_N + H_minus N * H_plus N) ∧
    superTrace γ₀ (D_N1 * D_N1) = superTrace γ₀ ⁅H_plus N, H_minus N⁆ := by
  intro D_N D_N1 Γ_N
  have h_anti_all : ∀ (n : ℕ),
      noncentralDiracTower D₀ γ₀ H_plus H_minus n * kroneckerGamma γ₀ n +
      kroneckerGamma γ₀ n * noncentralDiracTower D₀ γ₀ H_plus H_minus n = 0 := by
    intro n; induction' n with k ih
    · exact h_anti₀
    · have h_off1 : -(kroneckerGamma γ₀ k * H_plus k * kroneckerGamma γ₀ k) +
          kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_plus k) = 0 := by
        calc -(kroneckerGamma γ₀ k * H_plus k * kroneckerGamma γ₀ k) +
             kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_plus k)
          _ = -(kroneckerGamma γ₀ k * (H_plus k * kroneckerGamma γ₀ k)) +
              kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_plus k) := by noncomm_ring
          _ = 0 := by rw [← hH_plus_even k]; abel
      have h_off2 : kroneckerGamma γ₀ k * H_minus k * kroneckerGamma γ₀ k -
          kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k) = 0 := by
        calc kroneckerGamma γ₀ k * H_minus k * kroneckerGamma γ₀ k -
             kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k)
          _ = kroneckerGamma γ₀ k * (H_minus k * kroneckerGamma γ₀ k) -
              kroneckerGamma γ₀ k * (kroneckerGamma γ₀ k * H_minus k) := by noncomm_ring
          _ = 0 := by rw [← hH_minus_even k]; abel
      apply ext_fin2
      · simp [noncentralDiracTower, kroneckerGamma, ih]
      · simp [noncentralDiracTower, kroneckerGamma, h_off1]
      · simp [noncentralDiracTower, kroneckerGamma, h_off2]
      · simp [noncentralDiracTower, kroneckerGamma]
        calc -(noncentralDiracTower D₀ γ₀ H_plus H_minus k * kroneckerGamma γ₀ k) -
             kroneckerGamma γ₀ k * noncentralDiracTower D₀ γ₀ H_plus H_minus k
          _ = -(noncentralDiracTower D₀ γ₀ H_plus H_minus k * kroneckerGamma γ₀ k +
                kroneckerGamma γ₀ k * noncentralDiracTower D₀ γ₀ H_plus H_minus k) := by abel
          _ = 0 := by rw [ih, neg_zero]
  have hΓ_sq := kroneckerGamma_sq h_γ₀_sq N
  have hD_anti := h_anti_all N
  have hDΓ : D_N * Γ_N = -(Γ_N * D_N) := eq_neg_of_add_eq_zero_left hD_anti
  have h_prod : ∀ (X Y : ClTower B N), Γ_N * X = X * Γ_N →
      (Γ_N * X) * (Γ_N * Y) = X * Y := by
    intro X Y hX
    calc (Γ_N * X) * (Γ_N * Y) = Γ_N * (X * Γ_N) * Y := by noncomm_ring
      _ = Γ_N * (Γ_N * X) * Y := by rw [hX]
      _ = (Γ_N * Γ_N) * (X * Y) := by noncomm_ring
      _ = X * Y := by rw [hΓ_sq, one_mul]
  have h_cross : ∀ (X : ClTower B N),
      D_N * (Γ_N * X) + (Γ_N * X) * D_N = -Γ_N * ⁅D_N, X⁆ := by
    intro X; rw [Ring.lie_def]
    calc D_N * (Γ_N * X) + (Γ_N * X) * D_N
      _ = (D_N * Γ_N) * X + Γ_N * (X * D_N) := by noncomm_ring
      _ = -(Γ_N * D_N) * X + Γ_N * (X * D_N) := by rw [hDΓ]
      _ = -Γ_N * (D_N * X - X * D_N) := by noncomm_ring
  have h_sq : D_N1 * D_N1 =
      mat2 (D_N * D_N + H_plus N * H_minus N) (-Γ_N * ⁅D_N, H_plus N⁆)
           (-Γ_N * ⁅D_N, H_minus N⁆) (D_N * D_N + H_minus N * H_plus N) := by
    apply ext_fin2 <;>
      simp [D_N1, noncentralDiracTower, h_prod (H_plus N) (H_minus N) (hH_plus_even N),
            h_prod (H_minus N) (H_plus N) (hH_minus_even N),
            h_cross (H_plus N), h_cross (H_minus N)]
  refine ⟨hΓ_sq, hD_anti, h_sq, ?_⟩
  rw [h_sq]
  dsimp [superTrace, kroneckerGamma, towerTrace]
  simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
    mul_zero, zero_mul, add_zero, zero_add, neg_mul, ← towerTrace_add]
  congr 1
  rw [Ring.lie_def]
  noncomm_ring

end ArchetypeSA4_NonCentralAllScalesDiracHiggs

end NoncommutativeYangMillsHiggsSpectralAction
```

## Turn 0105, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeYangMillsKreinCantorSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {B : Type*} [Ring B]

@[simp] lemma mat2_00 (a b c d : B) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : B) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : B) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : B) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) B) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) B) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) B) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) B) 1 1 = 1 := rfl

@[simp] lemma ct2_00 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : Mᴴ 1 1 = star (M 1 1) := rfl

@[simp] lemma star2_00 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 [Star B] (M : Matrix (Fin 2) (Fin 2) B) : (star M) 1 1 = star (M 1 1) := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op   : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) B := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) B := mat2 0 (-1) 1 0
def P_plus     : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 0
def fiberEmbed (a : B) : Matrix (Fin 2) (Fin 2) B := mat2 a 0 0 a

def vecOp (u₁ u₂ u₃ : B) : Matrix (Fin 2) (Fin 2) B :=
  fiberEmbed u₁ * gamma1Op + fiberEmbed u₂ * sigmaOp + fiberEmbed u₃ * omegaOp

@[simp] lemma vecOp_00 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 0 = u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_01 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 1 = u₂ - u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]; rfl
@[simp] lemma vecOp_10 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 0 = u₂ + u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_11 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 1 = -u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end Matrix2Simp

/-!
## Inductive $\star$-Tower `ClTower B n` & Krein Fundamental Symmetry
-/

universe u

def ClTower (B : Type u) : ℕ → Type u
  | 0     => B
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower B n)

instance instRingClTower {B : Type u} [Ring B] : ∀ n : ℕ, Ring (ClTower B n)
  | 0     => inferInstanceAs (Ring B)
  | n + 1 => by
      letI : Ring (ClTower B n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower B n)))

instance instStarRingClTower {B : Type u} [Ring B] [StarRing B] :
    ∀ n : ℕ, StarRing (ClTower B n)
  | 0     => inferInstanceAs (StarRing B)
  | n + 1 => by
      letI : Ring (ClTower B n) := instRingClTower n
      letI : StarRing (ClTower B n) := instStarRingClTower n
      exact inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower B n)))

variable {B : Type u} [Ring B] [StarRing B]

def bottEmbed {n : ℕ} (X : ClTower B n) : ClTower B (n + 1) :=
  mat2 X 0 0 0

def cantorProj : ∀ (n : ℕ), ClTower B n
  | 0     => (1 : B)
  | n + 1 => bottEmbed (cantorProj n)

/-- The $n$-scale Krein fundamental symmetry $\Gamma^{(n)} \in \mathcal{C}\ell_n(B)$. -/
def chiralityOp : ∀ (n : ℕ), ClTower B n
  | 0     => (1 : B)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

/-- Indefinite Krein adjoint (Dirac bar) $X^{[\dagger]} = \Gamma^{(n)} X^\star \Gamma^{(n)}$ on $\mathcal{C}\ell_n(B)$. -/
def kreinAdjoint {n : ℕ} (X : ClTower B n) : ClTower B n :=
  chiralityOp n * star X * chiralityOp n

/-- Indefinite Krein sesquilinear pairing $\langle X, Y\rangle_{\mathrm{Krein}}^{(n)} = X^\star \Gamma^{(n)} Y$. -/
def kreinPairing {n : ℕ} (X Y : ClTower B n) : ClTower B n :=
  star X * chiralityOp n * Y

lemma chiralityOp_sq : ∀ (n : ℕ),
    (chiralityOp n : ClTower B n) * chiralityOp n = 1
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [chiralityOp, chiralityOp_sq n]

lemma chiralityOp_sa : ∀ (n : ℕ),
    star (chiralityOp n : ClTower B n) = chiralityOp n
  | 0     => star_one B
  | n + 1 => by apply ext_fin2 <;> simp [chiralityOp, chiralityOp_sa n]

lemma cantorProj_idem : ∀ (n : ℕ),
    (cantorProj n : ClTower B n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, bottEmbed, cantorProj_idem n]

lemma cantorProj_sa : ∀ (n : ℕ),
    star (cantorProj n : ClTower B n) = cantorProj n
  | 0     => star_one B
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, bottEmbed, cantorProj_sa n]

lemma chiralityOp_cantorProj : ∀ (n : ℕ),
    (chiralityOp n : ClTower B n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [chiralityOp, cantorProj, bottEmbed, chiralityOp_cantorProj n]

/-!
## Archetype $\mathcal{Y}\mathcal{K}_1$: Doubled Real Krein Space & Cantor Fractal Ghost Excision on `ClTower B n`
-/

section ArchetypeYK1_KreinSpaceAndCantorGhostExcision

/-- **Doubled Real Krein Space & Cantor Ghost Excision Theorem ($\mathcal{Y}\mathcal{K}_1$)**:
At every scale $n \in \mathbb{N}$ in $\mathcal{C}\ell_n(B)$:
1. $X \mapsto X^{[\dagger]}$ is an anti-multiplicative involution:
   $(X^{[\dagger]})^{[\dagger]} = X$ and $(X Y)^{[\dagger]} = Y^{[\dagger]} X^{[\dagger]}$,
2. Krein-Hermitian symmetry: $(\langle X, Y\rangle_{\mathrm{Krein}}^{(n)})^\star = \langle Y, X\rangle_{\mathrm{Krein}}^{(n)}$,
3. *Cantor Fractal Ghost Excision*: On any Cantor-projected physical state $\Pi_{\mathcal{C}_n} X$,
   the indefinite Krein pairing reduces identically to the positive-definite Hilbert pairing:
   $\langle \Pi_{\mathcal{C}_n} X, \Pi_{\mathcal{C}_n} Y\rangle_{\mathrm{Krein}}^{(n)} = (\Pi_{\mathcal{C}_n} X)^\star (\Pi_{\mathcal{C}_n} Y)$,
   and $\Pi_{\mathcal{C}_n} X^{[\dagger]} \Pi_{\mathcal{C}_n} = \Pi_{\mathcal{C}_n} X^\star \Pi_{\mathcal{C}_n}$. -/
theorem all_scales_krein_involution_and_cantor_positivity
    (n : ℕ) (X Y : ClTower B n) :
    let P_n := (cantorProj n : ClTower B n)
    kreinAdjoint (kreinAdjoint X) = X ∧
    kreinAdjoint (X * Y) = kreinAdjoint Y * kreinAdjoint X ∧
    star (kreinPairing X Y) = kreinPairing Y X ∧
    kreinPairing (P_n * X) (P_n * Y) = star (P_n * X) * (P_n * Y) ∧
    P_n * kreinAdjoint X * P_n = P_n * star X * P_n := by
  intro P_n
  have hΓ_sq := chiralityOp_sq (B := B) n
  have hΓ_sa := chiralityOp_sa (B := B) n
  have hP_sa := cantorProj_sa (B := B) n
  have hΓP   := chiralityOp_cantorProj (B := B) n
  have hPΓ : P_n * chiralityOp n = P_n := by
    calc P_n * chiralityOp n = star (chiralityOp n * P_n) := by
          rw [star_mul, hP_sa, hΓ_sa]
      _ = star P_n := by rw [hΓP]
      _ = P_n := hP_sa
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [kreinAdjoint]
    simp only [star_mul, star_star, hΓ_sa]
    calc chiralityOp n * (chiralityOp n * X * chiralityOp n) * chiralityOp n
      _ = (chiralityOp n * chiralityOp n) * X * (chiralityOp n * chiralityOp n) := by
          noncomm_ring
      _ = X := by rw [hΓ_sq]; noncomm_ring
  · dsimp [kreinAdjoint]
    simp only [star_mul]
    calc chiralityOp n * (star Y * star X) * chiralityOp n
      _ = chiralityOp n * star Y * 1 * star X * chiralityOp n := by noncomm_ring
      _ = chiralityOp n * star Y * (chiralityOp n * chiralityOp n) * star X * chiralityOp n := by
          rw [hΓ_sq]
      _ = (chiralityOp n * star Y * chiralityOp n) *
          (chiralityOp n * star X * chiralityOp n) := by noncomm_ring
  · dsimp [kreinPairing]
    simp only [star_mul, star_star, hΓ_sa, mul_assoc]
  · dsimp [kreinPairing]
    calc star (P_n * X) * chiralityOp n * (P_n * Y)
      _ = star (P_n * X) * (chiralityOp n * P_n) * Y := by noncomm_ring
      _ = star (P_n * X) * (P_n * Y) := by rw [hΓP]; noncomm_ring
  · dsimp [kreinAdjoint]
    calc P_n * (chiralityOp n * star X * chiralityOp n) * P_n
      _ = (P_n * chiralityOp n) * star X * (chiralityOp n * P_n) := by noncomm_ring
      _ = P_n * star X * P_n := by rw [hPΓ, hΓP]

end ArchetypeYK1_KreinSpaceAndCantorGhostExcision

/-!
## Archetype $\mathcal{Y}\mathcal{K}_2$: Algebraic Wick Rotation via the Krein Fundamental Symmetry $\Gamma_1$
-/

section ArchetypeYK2_AlgebraicWickRotation

/-- Lorentzian Krein-self-adjoint two-sheeted Dirac–Yang–Mills operator
$\mathcal{D}_{\mathrm{Krein}}(M, U) = \bigl(\begin{smallmatrix} M & U \\ -U^\star & -M \end{smallmatrix}\bigr) \in M_2(B)$. -/
def kreinDirac (M U : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2 M U (-star U) (-M)

/-- Wick-rotated Euclidean Hilbert-self-adjoint Dirac–Yang–Mills operator
$\mathcal{D}_{\mathrm{Eucl}}(M, U) = \Gamma_1 \mathcal{D}_{\mathrm{Krein}}(M, U) = \bigl(\begin{smallmatrix} M & U \\ U^\star & M \end{smallmatrix}\bigr)$. -/
def euclDirac (M U : B) : Matrix (Fin 2) (Fin 2) B :=
  gamma1Op * kreinDirac M U

/-- **Algebraic Wick Rotation Theorem ($\mathcal{Y}\mathcal{K}_2$)**:
For any self-adjoint $M^\star = M$ and arbitrary $U \in B$:
1. $\mathcal{D}_{\mathrm{Krein}}(M, U)$ is Krein-self-adjoint:
   $\Gamma_1 (\mathcal{D}_{\mathrm{Krein}}(M, U))^\dagger \Gamma_1 = \mathcal{D}_{\mathrm{Krein}}(M, U)$,
2. $\mathcal{D}_{\mathrm{Eucl}}(M, U) = \Gamma_1 \mathcal{D}_{\mathrm{Krein}}(M, U)$ is Hilbert-self-adjoint:
   $(\mathcal{D}_{\mathrm{Eucl}}(M, U))^\dagger = \mathcal{D}_{\mathrm{Eucl}}(M, U)$,
3. Whereas $(\mathcal{D}_{\mathrm{Krein}})^2$ has indefinite diagonal $M^2 - U U^\star$, the
   Wick-rotated square $(\mathcal{D}_{\mathrm{Eucl}})^2 = \mathcal{D}_{\mathrm{Krein}}^\dagger \mathcal{D}_{\mathrm{Krein}}$
   has positive-definite diagonal $M^2 + U U^\star$,
4. On the positive Cantor sheet $P_+$, $P_+ \mathcal{D}_{\mathrm{Eucl}}(M, U) = P_+ \mathcal{D}_{\mathrm{Krein}}(M, U)$. -/
theorem algebraic_wick_rotation_krein_to_hilbert_dirac
    {M : B} (U : B) (hM : star M = M) :
    let D_K := kreinDirac M U
    let D_E := euclDirac M U
    gamma1Op * D_Kᴴ * gamma1Op = D_K ∧
    D_Eᴴ = D_E ∧
    D_K * D_K = mat2 (M * M - U * star U) ⁅M, U⁆ (-⁅M, star U⁆) (M * M - star U * U) ∧
    D_E * D_E = D_Kᴴ * D_K ∧
    D_E * D_E = mat2 (M * M + U * star U) ⁅M, U⁆ (-⁅M, star U⁆) (M * M + star U * U) ∧
    P_plus * D_E = P_plus * D_K := by
  intro D_K D_E
  simp only [Ring.lie_def]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [D_K, kreinDirac, gamma1Op, hM]
  · apply ext_fin2 <;> simp [D_E, euclDirac, kreinDirac, gamma1Op, hM]
  · apply ext_fin2 <;> simp [D_K, kreinDirac] <;> noncomm_ring
  · apply ext_fin2 <;> simp [D_E, D_K, euclDirac, kreinDirac, gamma1Op, hM]
  · apply ext_fin2 <;> simp [D_E, euclDirac, kreinDirac, gamma1Op, hM] <;> noncomm_ring
  · apply ext_fin2 <;> simp [D_E, D_K, euclDirac, kreinDirac, gamma1Op, P_plus]

end ArchetypeYK2_AlgebraicWickRotation

/-!
## Archetype $\mathcal{Y}\mathcal{K}_3$: Indefinite Krein Yang–Mills Square vs. Positive-Definite Hilbert Yang–Mills Action
-/

section ArchetypeYK3_IndefiniteKreinVsPositiveHilbertYangMills

def ymFieldStrength (dᵢ dⱼ Aᵢ Aⱼ : B) : B :=
  ⁅dᵢ, Aⱼ⁆ - ⁅dⱼ, Aᵢ⁆ + ⁅Aᵢ, Aⱼ⁆

/-- **Indefinite Krein vs. Positive-Definite Hilbert Yang–Mills Action Theorem ($\mathcal{Y}\mathcal{K}_3$)**:
For any Yang–Mills field strength components $F_{23}, F_{31}, F_{12} \in B$:
1. The un-twisted Lorentzian / Krein trace $\mathrm{Tr}_2(\mathrm{vecOp}(F_{23}, F_{31}, -F_{12})^2)$
   has indefinite $(+, +, -)$ signature $2 \bullet (F_{23}^2 + F_{31}^2 - F_{12}^2)$,
2. The Hilbert–Schmidt / Wick-rotated trace $\mathrm{Tr}_2(\mathrm{vecOp}(F_{23}, F_{31}, -F_{12})^\dagger \mathrm{vecOp}(F_{23}, F_{31}, -F_{12}))$
   has positive-definite $(+, +, +)$ signature $2 \bullet (F_{23}^\star F_{23} + F_{31}^\star F_{31} + F_{12}^\star F_{12})$. -/
theorem indefinite_krein_vs_positive_hilbert_yang_mills_action
    (F₂₃ F₃₁ F₁₂ : B) :
    let 𝓕 := vecOp F₂₃ F₃₁ (-F₁₂)
    Matrix.trace (𝓕 * 𝓕) =
      2 • (F₂₃ * F₂₃ + F₃₁ * F₃₁ - F₁₂ * F₁₂) ∧
    Matrix.trace (𝓕ᴴ * 𝓕) =
      2 • (star F₂₃ * F₂₃ + star F₃₁ * F₃₁ + star F₁₂ * F₁₂) := by
  refine ⟨?_, ?_⟩
  · simp [two_smul]; noncomm_ring
  · simp [two_smul]; noncomm_ring

end ArchetypeYK3_IndefiniteKreinVsPositiveHilbertYangMills

/-!
## Archetype $\mathcal{Y}\mathcal{K}_4$: All-Scales Bott Colimit Krein Homomorphism
-/

section ArchetypeYK4_ColimitKreinHomomorphism

def bottEmbedIter : ∀ {n : ℕ} (k : ℕ), ClTower B n → ClTower B (n + k)
  | _, 0,     X => X
  | _, k + 1, X => bottEmbed (bottEmbedIter k X)

lemma bottEmbed_kreinAdjoint {n : ℕ} (X : ClTower B n) :
    kreinAdjoint (bottEmbed X) = bottEmbed (kreinAdjoint X) := by
  apply ext_fin2 <;> simp [kreinAdjoint, bottEmbed, chiralityOp]

lemma bottEmbed_kreinPairing {n : ℕ} (X Y : ClTower B n) :
    kreinPairing (bottEmbed X) (bottEmbed Y) = bottEmbed (kreinPairing X Y) := by
  apply ext_fin2 <;> simp [kreinPairing, bottEmbed, chiralityOp]

/-- **All-Scales Bott Colimit Krein Homomorphism Theorem ($\mathcal{Y}\mathcal{K}_4$)**:
Across any number of colimit steps $k \in \mathbb{N}$ from scale $n$ to scale $n + k$:
1. $(\iota_{\mathrm{Bott}}^{(k)}(X))^{[\dagger]} = \iota_{\mathrm{Bott}}^{(k)}(X^{[\dagger]})$,
2. $\langle \iota_{\mathrm{Bott}}^{(k)}(X), \iota_{\mathrm{Bott}}^{(k)}(Y)\rangle_{\mathrm{Krein}}^{(n+k)} =
    \iota_{\mathrm{Bott}}^{(k)}(\langle X, Y\rangle_{\mathrm{Krein}}^{(n)})$. -/
theorem all_scales_bott_colimit_krein_homomorphism
    {n : ℕ} (k : ℕ) (X Y : ClTower B n) :
    kreinAdjoint (bottEmbedIter k X) = bottEmbedIter k (kreinAdjoint X) ∧
    kreinPairing (bottEmbedIter k X) (bottEmbedIter k Y) =
      bottEmbedIter k (kreinPairing X Y) := by
  induction' k with m ih
  · exact ⟨rfl, rfl⟩
  · rcases ih with ⟨ih_adj, ih_pair⟩
    refine ⟨?_, ?_⟩
    · dsimp [bottEmbedIter]; rw [bottEmbed_kreinAdjoint, ih_adj]
    · dsimp [bottEmbedIter]; rw [bottEmbed_kreinPairing, ih_pair]

end ArchetypeYK4_ColimitKreinHomomorphism

end NoncommutativeYangMillsKreinCantorSynthesis
```

## Turn 0108, fence 002 — model; language `lean`

```lean
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

open Matrix

namespace NoncommutativeKitaevMajoranaThermalHallSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & 3D Zorn Vector Operators
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of ![![a, b], ![c, d]]

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {B : Type*} [Ring B]

@[simp] lemma mat2_00 (a b c d : B) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 (a b c d : B) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 (a b c d : B) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 (a b c d : B) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) B) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) B) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) B) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) B) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) B) 1 1 = 1 := rfl

@[simp] lemma trace_fin2 (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def gamma1Op   : Matrix (Fin 2) (Fin 2) B := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) B := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) B := mat2 0 (-1) 1 0
def fiberEmbed (a : B) : Matrix (Fin 2) (Fin 2) B := mat2 a 0 0 a
def kleinTwist (a : B) : Matrix (Fin 2) (Fin 2) B := mat2 a 0 0 (-a)

def vecOp (u₁ u₂ u₃ : B) : Matrix (Fin 2) (Fin 2) B :=
  fiberEmbed u₁ * gamma1Op + fiberEmbed u₂ * sigmaOp + fiberEmbed u₃ * omegaOp

@[simp] lemma vecOp_00 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 0 = u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_01 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 0 1 = u₂ - u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]; rfl
@[simp] lemma vecOp_10 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 0 = u₂ + u₃ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]
@[simp] lemma vecOp_11 (u₁ u₂ u₃ : B) : (vecOp u₁ u₂ u₃) 1 1 = -u₁ := by
  simp [vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end Matrix2Simp

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-!
## Archetype $\mathcal{K}\mathcal{M}_1$: Kitaev's 4-Majorana Spin Fractionalization & The Three-Spin Zeeman Identity
-/

section ArchetypeKM1_KitaevMajoranaFractionalization

variable {B : Type*} [Ring B]

/-- Itinerant matter Majorana $c = \Sigma_{\mathrm{outer}}$ and bond gauge Majoranas $b_1, b_2, b_3 \in M_2(M_2(B))$. -/
def majC  : NestedMat B := sigmaOp
def majB1 : NestedMat B := omegaOp
def majB2 : NestedMat B := kleinTwist sigmaOp
def majB3 : NestedMat B := kleinTwist omegaOp

/-- Kitaev's 4-Majorana gauge-fixing volume operator $D_{\mathrm{Kitaev}} = b_1 b_2 b_3 c$. -/
def kitaevGaugeD : NestedMat B := majB1 * majB2 * majB3 * majC

/-- Fractionalized Kitaev spin bilinears $S_\alpha = b_\alpha c$ ($\alpha = 1, 2, 3$). -/
def kitaevSpin1 : NestedMat B := majB1 * majC
def kitaevSpin2 : NestedMat B := majB2 * majC
def kitaevSpin3 : NestedMat B := majB3 * majC

/-- **Kitaev Majorana Fractionalization & Three-Spin Zeeman Identity Theorem ($\mathcal{K}\mathcal{M}_1$)**:
In $M_2(M_2(B))$ over any noncommutative ring $B$:
1. $D_{\mathrm{Kitaev}}^2 = 1$,
2. $D_{\mathrm{Kitaev}}$ commutes with all three fractionalized spin operators $S_1, S_2, S_3$,
3. *Bond Spin-to-Majorana Factorization*: $S_1 S_2 = -b_1 b_2$, $S_2 S_3 = -b_2 b_3$, $S_3 S_1 = -b_3 b_1$,
4. *Three-Spin Zeeman Identity*: $S_1 S_2 S_3 = -D_{\mathrm{Kitaev}}$. -/
theorem kitaev_majorana_fractionalization_and_three_spin_identity :
    (kitaevGaugeD : NestedMat B) * kitaevGaugeD = 1 ∧
    ⁅(kitaevGaugeD : NestedMat B), kitaevSpin1⁆ = 0 ∧
    ⁅(kitaevGaugeD : NestedMat B), kitaevSpin2⁆ = 0 ∧
    ⁅(kitaevGaugeD : NestedMat B), kitaevSpin3⁆ = 0 ∧
    (kitaevSpin1 : NestedMat B) * kitaevSpin2 = -(majB1 * majB2) ∧
    (kitaevSpin2 : NestedMat B) * kitaevSpin3 = -(majB2 * majB3) ∧
    (kitaevSpin3 : NestedMat B) * kitaevSpin1 = -(majB3 * majB1) ∧
    (kitaevSpin1 : NestedMat B) * kitaevSpin2 * kitaevSpin3 = -kitaevGaugeD := by
  simp only [Ring.lie_def]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply ext_fin2 <;> apply ext_fin2 <;>
      simp [kitaevGaugeD, kitaevSpin1, kitaevSpin2, kitaevSpin3,
            majC, majB1, majB2, majB3, kleinTwist, sigmaOp, omegaOp])

end ArchetypeKM1_KitaevMajoranaFractionalization

/-!
## Archetype $\mathcal{K}\mathcal{M}_2$: Hexagonal Plaquette Vison Holonomy $W_{\mathrm{hex}}$ & Lattice Gauge Invariance
-/

section ArchetypeKM2_HexagonalVisonPlaquette

variable {R : Type*} [Ring R]

/-- Hexagonal vison plaquette operator $W_{\mathrm{hex}} = U_{12} U_{23} U_{34} U_{45} U_{56} U_{61}$. -/
def hexPlaquette (U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁ : R) : R :=
  U₁₂ * U₂₃ * U₃₄ * U₄₅ * U₅₆ * U₆₁

/-- Directed link gauge transformation $U_{ij}^g = g_i U_{ij} g_j^{-1}$. -/
def linkGauge (gᵢ gⱼ : Rˣ) (Uᵢⱼ : R) : R :=
  (gᵢ : R) * Uᵢⱼ * (↑gⱼ⁻¹ : R)

/-- **Hexagonal Vison Plaquette Gauge Covariance & $\mathbb{Z}_2$ Invariance Theorem ($\mathcal{K}\mathcal{M}_2$)**:
1. Under any non-Abelian vertex gauge transformations $g_1, \dots, g_6 \in R^\times$, all intermediate
   vertex factors cancel around the hexagon: $W_{\mathrm{hex}}(U^g) = g_1 W_{\mathrm{hex}}(U) g_1^{-1}$,
2. When $g_1$ is central in $R$ (such as a $\mathbb{Z}_2$ gauge sign $g_1 = \pm 1$),
   $W_{\mathrm{hex}}(U^g) = W_{\mathrm{hex}}(U)$. -/
theorem hexagonal_vison_plaquette_gauge_covariance_and_invariance
    (g₁ g₂ g₃ g₄ g₅ g₆ : Rˣ) (U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁ : R)
    (hg₁_cent : ∀ X : R, (g₁ : R) * X = X * (g₁ : R)) :
    let W_g := hexPlaquette
      (linkGauge g₁ g₂ U₁₂) (linkGauge g₂ g₃ U₂₃) (linkGauge g₃ g₄ U₃₄)
      (linkGauge g₄ g₅ U₄₅) (linkGauge g₅ g₆ U₅₆) (linkGauge g₆ g₁ U₆₁)
    let W_0 := hexPlaquette U₁₂ U₂₃ U₃₄ U₄₅ U₅₆ U₆₁
    W_g = (g₁ : R) * W_0 * (↑g₁⁻¹ : R) ∧
    W_g = W_0 := by
  intro W_g W_0
  have h1 : (↑g₁⁻¹ : R) * (g₁ : R) = 1 := Units.inv_mul g₁
  have h2 : (↑g₂⁻¹ : R) * (g₂ : R) = 1 := Units.inv_mul g₂
  have h3 : (↑g₃⁻¹ : R) * (g₃ : R) = 1 := Units.inv_mul g₃
  have h4 : (↑g₄⁻¹ : R) * (g₄ : R) = 1 := Units.inv_mul g₄
  have h5 : (↑g₅⁻¹ : R) * (g₅ : R) = 1 := Units.inv_mul g₅
  have h6 : (↑g₆⁻¹ : R) * (g₆ : R) = 1 := Units.inv_mul g₆
  have h_cov : W_g = (g₁ : R) * W_0 * (↑g₁⁻¹ : R) := by
    dsimp [W_g, W_0, hexPlaquette, linkGauge]
    calc (g₁ : R) * U₁₂ * (↑g₂⁻¹ : R) * ((g₂ : R) * U₂₃ * (↑g₃⁻¹ : R)) *
         ((g₃ : R) * U₃₄ * (↑g₄⁻¹ : R)) * ((g₄ : R) * U₄₅ * (↑g₅⁻¹ : R)) *
         ((g₅ : R) * U₅₆ * (↑g₆⁻¹ : R)) * ((g₆ : R) * U₆₁ * (↑g₁⁻¹ : R))
      _ = (g₁ : R) * U₁₂ * ((↑g₂⁻¹ : R) * (g₂ : R)) * U₂₃ * ((↑g₃⁻¹ : R) * (g₃ : R)) *
          U₃₄ * ((↑g₄⁻¹ : R) * (g₄ : R)) * U₄₅ * ((↑g₅⁻¹ : R) * (g₅ : R)) *
          U₅₆ * ((↑g₆⁻¹ : R) * (g₆ : R)) * U₆₁ * (↑g₁⁻¹ : R) := by noncomm_ring
      _ = (g₁ : R) * (U₁₂ * U₂₃ * U₃₄ * U₄₅ * U₅₆ * U₆₁) * (↑g₁⁻¹ : R) := by
          rw [h2, h3, h4, h5, h6]; noncomm_ring
  refine ⟨h_cov, ?_⟩
  rw [h_cov, hg₁_cent W_0, mul_assoc, Units.mul_inv, mul_one]

end ArchetypeKM2_HexagonalVisonPlaquette

/-!
## Archetype $\mathcal{K}\mathcal{M}_3$: Gapless Dirac Cone, Magnetic Haldane–Kitaev Mass Gap & Thermal Hall Sign Reversal
-/

section ArchetypeKM3_DiracConeMagneticGapAndThermalHall

variable {B : Type*} [Ring B]

/-- Honeycomb Kitaev–Dirac–Zorn Hamiltonian with magnetic Haldane mass $\Delta_H$ and bond couplings $(K_1, K_2, K_3)$. -/
def kitaevHoneycombH (Δ_H K₁ K₂ K₃ : B) : NestedMat B :=
  mat2 (fiberEmbed Δ_H) (vecOp K₁ K₂ K₃) (vecOp K₁ K₂ K₃) (-fiberEmbed Δ_H)

/-- Sublattice chirality grading $\Gamma_{\mathrm{sub}} = \mathrm{diag}(1, -1)$ on the honeycomb bipartite lattice. -/
def sublatticeGamma : NestedMat B := mat2 1 0 0 (-1)

/-- Sublattice chiral supertrace $\mathrm{Str}_{\mathrm{sub}}(\mathbb{M}) = \mathrm{Tr}_2(\mathbb{M}_{00}) - \mathrm{Tr}_2(\mathbb{M}_{11})$. -/
def sublatticeSuperTrace (𝕄 : NestedMat B) : B :=
  Matrix.trace (𝕄 0 0) - Matrix.trace (𝕄 1 1)

lemma zorn_vec_sq (K₁ K₂ K₃ : B) :
    vecOp K₁ K₂ K₃ * vecOp K₁ K₂ K₃ =
      fiberEmbed (K₁ * K₁ + K₂ * K₂ - K₃ * K₃) +
      vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆) := by
  simp only [Ring.lie_def]
  apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring

/-- **Kitaev Honeycomb Dirac Cone, Magnetic Haldane Gap & Thermal Hall Sign Flip Theorem ($\mathcal{K}\mathcal{M}_3$)**:
1. *Zero-Field Chiral Symmetry*: $\mathcal{H}_{\mathrm{Kitaev}}(0, \mathbf{K})$ anticommutes with $\Gamma_{\mathrm{sub}}$,
2. *General Squared Hamiltonian*:
   $(\mathcal{H}_{\mathrm{Kitaev}}(\Delta_H, \mathbf{K}))^2 = \bigl(\begin{smallmatrix} \iota(\Delta_H^2 + K_1^2 + K_2^2 - K_3^2) + \mathrm{vecOp}(\⁅K_2, K_3⁆, \⁅K_3, K_1⁆, -\⁅K_1, K_2⁆) & \⁅\iota(\Delta_H), \mathrm{vecOp}(\mathbf{K})⁆ \\ -\⁅\iota(\Delta_H), \mathrm{vecOp}(\mathbf{K})⁆ & \iota(\Delta_H^2 + K_1^2 + K_2^2 - K_3^2) + \mathrm{vecOp}(\⁅K_2, K_3⁆, \⁅K_3, K_1⁆, -\⁅K_1, K_2⁆) \end{smallmatrix}\bigr)$,
3. *Magnetic Gap Opening at the Dirac Cone*: When $\⁅K_i, K_j⁆ = 0$, $\⁅\Delta_H, K_i⁆ = 0$, and
   $K_1^2 + K_2^2 - K_3^2 = 0$ (at the Dirac cone), $(\mathcal{H}_{\mathrm{Kitaev}}(0, \mathbf{K}))^2 = 0$,
   whereas $(\mathcal{H}_{\mathrm{Kitaev}}(\Delta_H, \mathbf{K}))^2 = \mathrm{diag}(\iota(\Delta_H^2), \iota(\Delta_H^2))$,
4. *Chiral Thermal Hall Sign Reversal*:
   $\mathrm{Str}_{\mathrm{sub}}(\mathcal{H}_{\mathrm{Kitaev}}(\Delta_H, \mathbf{K})) = 4 \bullet \Delta_H$ and
   $\mathrm{Str}_{\mathrm{sub}}(\mathcal{H}_{\mathrm{Kitaev}}(-\Delta_H, \mathbf{K})) = -\mathrm{Str}_{\mathrm{sub}}(\mathcal{H}_{\mathrm{Kitaev}}(\Delta_H, \mathbf{K}))$. -/
theorem kitaev_dirac_cone_magnetic_gap_and_hall_sign_flip
    (Δ_H K₁ K₂ K₃ : B)
    (h23 : ⁅K₂, K₃⁆ = 0) (h31 : ⁅K₃, K₁⁆ = 0) (h12 : ⁅K₁, K₂⁆ = 0)
    (hΔ1 : ⁅Δ_H, K₁⁆ = 0) (hΔ2 : ⁅Δ_H, K₂⁆ = 0) (hΔ3 : ⁅Δ_H, K₃⁆ = 0)
    (h_cone : K₁ * K₁ + K₂ * K₂ - K₃ * K₃ = 0) :
    let H_0 := kitaevHoneycombH 0 K₁ K₂ K₃
    let H_Δ := kitaevHoneycombH Δ_H K₁ K₂ K₃
    H_0 * sublatticeGamma + sublatticeGamma * H_0 = 0 ∧
    H_Δ * H_Δ =
      mat2
        (fiberEmbed (Δ_H * Δ_H + (K₁ * K₁ + K₂ * K₂ - K₃ * K₃)) +
         vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆))
        ⁅fiberEmbed Δ_H, vecOp K₁ K₂ K₃⁆
        (-⁅fiberEmbed Δ_H, vecOp K₁ K₂ K₃⁆)
        (fiberEmbed (Δ_H * Δ_H + (K₁ * K₁ + K₂ * K₂ - K₃ * K₃)) +
         vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆)) ∧
    H_0 * H_0 = 0 ∧
    H_Δ * H_Δ = mat2 (fiberEmbed (Δ_H * Δ_H)) 0 0 (fiberEmbed (Δ_H * Δ_H)) ∧
    sublatticeSuperTrace H_Δ = 4 • Δ_H ∧
    sublatticeSuperTrace (kitaevHoneycombH (-Δ_H) K₁ K₂ K₃) = -sublatticeSuperTrace H_Δ := by
  intro H_0 H_Δ
  have h_add_emb : ∀ (a b : B), fiberEmbed a + fiberEmbed b = fiberEmbed (a + b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_mul_emb : ∀ (a b : B), fiberEmbed a * fiberEmbed b = fiberEmbed (a * b) := by
    intro a b; apply ext_fin2 <;> simp [fiberEmbed]
  have h_sq_gen : ∀ (m : B),
      kitaevHoneycombH m K₁ K₂ K₃ * kitaevHoneycombH m K₁ K₂ K₃ =
      mat2
        (fiberEmbed (m * m + (K₁ * K₁ + K₂ * K₂ - K₃ * K₃)) +
         vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆))
        ⁅fiberEmbed m, vecOp K₁ K₂ K₃⁆
        (-⁅fiberEmbed m, vecOp K₁ K₂ K₃⁆)
        (fiberEmbed (m * m + (K₁ * K₁ + K₂ * K₂ - K₃ * K₃)) +
         vecOp ⁅K₂, K₃⁆ ⁅K₃, K₁⁆ (-⁅K₁, K₂⁆)) := by
    intro m
    rw [Ring.lie_def]
    apply ext_fin2
    · simp only [kitaevHoneycombH, mul2_00, mat2_00, mat2_01, mat2_10,
        h_mul_emb, zorn_vec_sq K₁ K₂ K₃, ← add_assoc, h_add_emb]
    · simp only [kitaevHoneycombH, mul2_01, mat2_00, mat2_01, mat2_11,
        mul_neg, sub_eq_add_neg]
    · simp only [kitaevHoneycombH, mul2_10, mat2_10, mat2_00, mat2_11, neg_mul]
      abel
    · simp only [kitaevHoneycombH, mul2_11, mat2_10, mat2_01, mat2_11,
        neg_mul_neg, h_mul_emb]
      rw [add_comm (vecOp K₁ K₂ K₃ * vecOp K₁ K₂ K₃),
          zorn_vec_sq K₁ K₂ K₃, ← add_assoc, h_add_emb]
  have h_vec_zero : vecOp (0 : B) 0 0 = 0 := by
    apply ext_fin2 <;> simp [fiberEmbed]
  have h_comm_Δ : ⁅fiberEmbed Δ_H, vecOp K₁ K₂ K₃⁆ = 0 := by
    have h_c : ⁅fiberEmbed Δ_H, vecOp K₁ K₂ K₃⁆ = vecOp ⁅Δ_H, K₁⁆ ⁅Δ_H, K₂⁆ ⁅Δ_H, K₃⁆ := by
      simp only [Ring.lie_def]
      apply ext_fin2 <;> simp [fiberEmbed] <;> noncomm_ring
    rw [h_c, hΔ1, hΔ2, hΔ3, h_vec_zero]
  have h_comm_0 : ⁅fiberEmbed (0 : B), vecOp K₁ K₂ K₃⁆ = 0 := by
    rw [Ring.lie_def]; apply ext_fin2 <;> simp [fiberEmbed]
  refine ⟨?_, h_sq_gen Δ_H, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [H_0, kitaevHoneycombH, sublatticeGamma, fiberEmbed]
  · dsimp [H_0]
    rw [h_sq_gen 0, h23, h31, h12, h_cone, h_comm_0, neg_zero, add_zero, mul_zero,
        h_vec_zero, add_zero]
    apply ext_fin2 <;> apply ext_fin2 <;> rfl
  · dsimp [H_Δ]
    rw [h_sq_gen Δ_H, h23, h31, h12, h_cone, h_comm_Δ, neg_zero, add_zero,
        h_vec_zero, add_zero]
  · dsimp [sublatticeSuperTrace, H_Δ, kitaevHoneycombH, fiberEmbed]
    simp only [trace_fin2, mat2_00, mat2_11, Matrix.neg_apply, nsmul_eq_mul, Nat.cast_ofNat]
    noncomm_ring
  · dsimp [sublatticeSuperTrace, H_Δ, kitaevHoneycombH, fiberEmbed]
    simp only [trace_fin2, mat2_00, mat2_11, Matrix.neg_apply]
    abel

end ArchetypeKM3_DiracConeMagneticGapAndThermalHall

/-!
## Archetype $\mathcal{K}\mathcal{M}_4$: All-Scales Half-Quantization of Chiral Majorana Modes on `ClTower B n`
-/

section ArchetypeKM4_HalfQuantizedMajoranaModes

universe u

def ClTower (B : Type u) : ℕ → Type u
  | 0     => B
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower B n)

instance instRingClTower {B : Type u} [Ring B] : ∀ n : ℕ, Ring (ClTower B n)
  | 0     => inferInstanceAs (Ring B)
  | n + 1 => by
      letI : Ring (ClTower B n) := instRingClTower n
      exact inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower B n)))

variable {B : Type u} [Ring B]

def cantorProj : ∀ (n : ℕ), ClTower B n
  | 0     => (1 : B)
  | n + 1 => mat2 (cantorProj n) 0 0 0

def towerTrace : ∀ {n : ℕ}, ClTower B n → B
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower B n) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace]
      rw [Matrix.zero_apply, Matrix.zero_apply, towerTrace_zero n, add_zero]

lemma towerTrace_cantorProj : ∀ (n : ℕ),
    towerTrace (cantorProj n : ClTower B n) = 1
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace, cantorProj]
      rw [mat2_00, mat2_11, towerTrace_zero n, add_zero, towerTrace_cantorProj n]

/-- Full doubled Dirac mode projection $D_{\mathrm{full}}^{(n+1)} = \mathrm{diag}(\Pi_{\mathcal{C}_n}, \Pi_{\mathcal{C}_n}) \in \mathcal{C}\ell_{n+1}(B)$. -/
def fullDiracModeProj (n : ℕ) : ClTower B (n + 1) :=
  mat2 (cantorProj n) 0 0 (cantorProj n)

/-- Positive and negative chiral Majorana mode projections $M_+^{(n+1)}, M_-^{(n+1)} \in \mathcal{C}\ell_{n+1}(B)$. -/
def majoranaPlusProj (n : ℕ) : ClTower B (n + 1) :=
  mat2 (cantorProj n) 0 0 0

def majoranaMinusProj (n : ℕ) : ClTower B (n + 1) :=
  mat2 0 0 0 (cantorProj n)

/-- **All-Scales Chiral Majorana Half-Quantization Theorem ($\mathcal{K}\mathcal{M}_4$)**:
At every scale $n \in \mathbb{N}$ in $\mathcal{C}\ell_{n+1}(B)$:
1. $M_+^{(n+1)} + M_-^{(n+1)} = D_{\mathrm{full}}^{(n+1)}$ and $M_+^{(n+1)} M_-^{(n+1)} = 0$,
2. $\mathrm{Tr}_{2^{n+1}}(D_{\mathrm{full}}^{(n+1)}) = 2 \bullet 1_B$, whereas
   $\mathrm{Tr}_{2^{n+1}}(M_+^{(n+1)}) = 1_B$ and $\mathrm{Tr}_{2^{n+1}}(M_-^{(n+1)}) = 1_B$,
3. $2 \bullet \mathrm{Tr}_{2^{n+1}}(M_+^{(n+1)}) = \mathrm{Tr}_{2^{n+1}}(D_{\mathrm{full}}^{(n+1)})$
   (exact half-quantization of a single chiral Majorana channel relative to a full Dirac channel). -/
theorem all_scales_chiral_majorana_half_quantization (n : ℕ) :
    let M_plus  := majoranaPlusProj (B := B) n
    let M_minus := majoranaMinusProj (B := B) n
    let D_full  := fullDiracModeProj (B := B) n
    M_plus + M_minus = D_full ∧
    M_plus * M_minus = 0 ∧
    towerTrace D_full = 2 • (1 : B) ∧
    towerTrace M_plus = 1 ∧
    towerTrace M_minus = 1 ∧
    2 • towerTrace M_plus = towerTrace D_full := by
  intro M_plus M_minus D_full
  have h_tr_P : towerTrace M_plus = (1 : B) := by
    dsimp [M_plus, majoranaPlusProj, towerTrace]
    rw [mat2_00, mat2_11, towerTrace_zero n, add_zero, towerTrace_cantorProj n]
  have h_tr_M : towerTrace M_minus = (1 : B) := by
    dsimp [M_minus, majoranaMinusProj, towerTrace]
    rw [mat2_00, mat2_11, towerTrace_zero n, zero_add, towerTrace_cantorProj n]
  have h_tr_D : towerTrace D_full = 2 • (1 : B) := by
    dsimp [D_full, fullDiracModeProj, towerTrace]
    rw [mat2_00, mat2_11, towerTrace_cantorProj n, two_smul]
  refine ⟨?_, ?_, h_tr_D, h_tr_P, h_tr_M, by rw [h_tr_P, h_tr_D]⟩
  · apply ext_fin2 <;> simp [M_plus, M_minus, D_full,
      majoranaPlusProj, majoranaMinusProj, fullDiracModeProj]
  · apply ext_fin2 <;> simp [M_plus, M_minus, majoranaPlusProj, majoranaMinusProj]

end ArchetypeKM4_HalfQuantizedMajoranaModes

end NoncommutativeKitaevMajoranaThermalHallSynthesis
```
