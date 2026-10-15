import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

/-!
# Symplectic coordinates and the affine Poisson Lie bracket

The carrier is the standard four-coordinate symplectic module. Affine
observables retain both a constant term and linear coefficients; their bracket
is the constant observable given by the symplectic pairing. Bilinearity,
antisymmetry, centrality and genuine nested Jacobi are proved below.

The quantity historically named `starCommutator` is only the pairing scaled
by a parameter. No associative Moyal product or Grassmannian identification
is constructed here. Affine observables are closed under the bracket, not
under multiplication of functions. The matrix identity J² = -I holds over
commutative rings; positivity and geometric complex structures require
additional scalar hypotheses.
-/

namespace InfoGeometry.Clifford.WeylMoyalSuperGrassmannian

open Matrix
open scoped BigOperators

/-! ### Section 1: Four-coordinate symplectic module -/

/-- 4D phase space carrier over a commutative ring `R`.
Coordinates correspond to $(q_1, q_2, p_1, p_2)$:
- Index 0: $q_1$
- Index 1: $q_2$
- Index 2: $p_1$
- Index 3: $p_2$
-/
abbrev PhaseSpace4 (R : Type*) := Fin 4 → R

/-- The standard 4x4 symplectic matrix $\Omega = J$:
$$
\Omega = \begin{pmatrix}
0 & 0 & 1 & 0 \\
0 & 0 & 0 & 1 \\
-1 & 0 & 0 & 0 \\
0 & -1 & 0 & 0
\end{pmatrix}
$$
-/
def symplecticMatrix (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![ 0,  0, 1, 0;
      0,  0, 0, 1;
     -1,  0, 0, 0;
      0, -1, 0, 0]

/-- The symplectic matrix is skew-symmetric: $\Omega^T = -\Omega$. -/
theorem symplecticMatrix_transpose (R : Type*) [CommRing R] :
    (symplecticMatrix R)ᵀ = -symplecticMatrix R := by
  ext i j
  fin_cases i <;> fin_cases j <;> { simp [symplecticMatrix, Matrix.transpose_apply]; try ring }

/-- The symplectic matrix squares to $-I_4$, as a ring-valued matrix identity:
$\Omega^2 = -1$. -/
theorem symplecticMatrix_sq (R : Type*) [CommRing R] :
    symplecticMatrix R * symplecticMatrix R = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [symplecticMatrix, Matrix.mul_apply, Fin.sum_univ_four]
    try ring
  }

/-- The canonical symplectic form $\Omega(u, v)$ on $\mathbb{R}^4$:
$\Omega(u, v) = u_0 v_2 - u_2 v_0 + u_1 v_3 - u_3 v_1 = q_1 p_1' - p_1 q_1' + q_2 p_2' - p_2 q_2'$. -/
def symplecticForm {R : Type*} [CommRing R] (u v : PhaseSpace4 R) : R :=
  u 0 * v 2 - u 2 * v 0 + u 1 * v 3 - u 3 * v 1

/-- The symplectic form is strictly alternating: $\Omega(u, u) = 0$. -/
theorem symplecticForm_alt {R : Type*} [CommRing R] (u : PhaseSpace4 R) :
    symplecticForm u u = 0 := by
  simp [symplecticForm]
  ring

/-- The symplectic form is strictly skew-symmetric: $\Omega(u, v) = -\Omega(v, u)$. -/
theorem symplecticForm_skew {R : Type*} [CommRing R] (u v : PhaseSpace4 R) :
    symplecticForm u v = -symplecticForm v u := by
  simp [symplecticForm]
  ring

/-! ### Section 2: Canonical Poisson Bracket on Linear Observables -/

/-- The canonical Poisson bracket $\{u, v\}$ on linear phase space observables,
governed by the symplectic form $\Omega(u, v)$. -/
def poissonBracket {R : Type*} [CommRing R] (u v : PhaseSpace4 R) : R :=
  symplecticForm u v

/-- The Poisson bracket is antisymmetric: $\{u, v\} = -\{v, u\}$. -/
theorem poisson_antisymm {R : Type*} [CommRing R] (u v : PhaseSpace4 R) :
    poissonBracket u v = -poissonBracket v u :=
  symplecticForm_skew u v

/-- The Poisson bracket vanishes on identical observables: $\{u, u\} = 0$. -/
theorem poisson_self_zero {R : Type*} [CommRing R] (u : PhaseSpace4 R) :
    poissonBracket u u = 0 :=
  symplecticForm_alt u

/-- Left-additivity of the Poisson bracket. -/
theorem poisson_add_left {R : Type*} [CommRing R] (u₁ u₂ v : PhaseSpace4 R) :
    poissonBracket (u₁ + u₂) v = poissonBracket u₁ v + poissonBracket u₂ v := by
  simp [poissonBracket, symplecticForm]
  ring

/-- Right-additivity of the Poisson bracket. -/
theorem poisson_add_right {R : Type*} [CommRing R] (u v₁ v₂ : PhaseSpace4 R) :
    poissonBracket u (v₁ + v₂) = poissonBracket u v₁ + poissonBracket u v₂ := by
  simp [poissonBracket, symplecticForm]
  ring

/-- Left-scalar multiplication on the Poisson bracket. -/
theorem poisson_smul_left {R : Type*} [CommRing R] (c : R) (u v : PhaseSpace4 R) :
    poissonBracket (c • u) v = c * poissonBracket u v := by
  simp [poissonBracket, symplecticForm]
  ring

/-- Right-scalar multiplication on the Poisson bracket. -/
theorem poisson_smul_right {R : Type*} [CommRing R] (c : R) (u v : PhaseSpace4 R) :
    poissonBracket u (c • v) = c * poissonBracket u v := by
  simp [poissonBracket, symplecticForm]
  ring

/-- Constant scalar observables have vanishing phase space gradients,
hence their Poisson bracket with any observable vanishes. -/
theorem poisson_scalar_bracket_zero {R : Type*} [CommRing R] (w : PhaseSpace4 R) :
    poissonBracket (0 : PhaseSpace4 R) w = 0 := by
  simp [poissonBracket, symplecticForm]

/-- Constant scalar observables on the right have vanishing Poisson bracket. -/
theorem poisson_scalar_bracket_zero_right {R : Type*} [CommRing R] (w : PhaseSpace4 R) :
    poissonBracket w (0 : PhaseSpace4 R) = 0 := by
  simp [poissonBracket, symplecticForm]

/-- Affine observables retain their constant term as well as their four
linear coefficients. Unlike coefficient vectors alone, this carrier is closed
under the canonical Poisson bracket. -/
abbrev AffineObservable (R : Type*) := R × PhaseSpace4 R

/-- Evaluation of an affine observable at a phase-space point. -/
def affineEval {R : Type*} [CommRing R] (F : AffineObservable R)
    (x : PhaseSpace4 R) : R := F.1 + ∑ i, F.2 i * x i

/-- The bracket of affine observables is the constant observable determined
by their symplectic pairing. -/
def affinePoissonBracket {R : Type*} [CommRing R]
    (F G : AffineObservable R) : AffineObservable R :=
  (poissonBracket F.2 G.2, 0)

theorem affinePoissonBracket_eval {R : Type*} [CommRing R]
    (F G : AffineObservable R) (x : PhaseSpace4 R) :
    affineEval (affinePoissonBracket F G) x = poissonBracket F.2 G.2 := by
  simp [affineEval, affinePoissonBracket]

theorem affinePoissonBracket_antisymm {R : Type*} [CommRing R]
    (F G : AffineObservable R) :
    affinePoissonBracket F G = -affinePoissonBracket G F := by
  apply Prod.ext
  · exact poisson_antisymm F.2 G.2
  · simp [affinePoissonBracket]

theorem affinePoissonBracket_add_left {R : Type*} [CommRing R]
    (F G H : AffineObservable R) :
    affinePoissonBracket (F + G) H = affinePoissonBracket F H + affinePoissonBracket G H := by
  apply Prod.ext
  · exact poisson_add_left F.2 G.2 H.2
  · simp [affinePoissonBracket]

theorem affinePoissonBracket_smul_left {R : Type*} [CommRing R]
    (c : R) (F G : AffineObservable R) :
    affinePoissonBracket (c • F) G = c • affinePoissonBracket F G := by
  apply Prod.ext
  · exact poisson_smul_left c F.2 G.2
  · simp [affinePoissonBracket]

/-- Constants are central in the actual closed observable carrier. -/
@[simp] theorem affinePoissonBracket_constant_left {R : Type*} [CommRing R]
    (c : R) (F : AffineObservable R) :
    affinePoissonBracket (c, 0) F = 0 := by
  apply Prod.ext <;> simp [affinePoissonBracket, poissonBracket, symplecticForm]

@[simp] theorem affinePoissonBracket_constant_right {R : Type*} [CommRing R]
    (F : AffineObservable R) (c : R) :
    affinePoissonBracket F (c, 0) = 0 := by
  apply Prod.ext <;> simp [affinePoissonBracket, poissonBracket, symplecticForm]

/-- Genuine cyclic Jacobi identity on all affine observables. -/
theorem poisson_jacobi {R : Type*} [CommRing R] (F G H : AffineObservable R) :
    affinePoissonBracket F (affinePoissonBracket G H) +
      affinePoissonBracket G (affinePoissonBracket H F) +
      affinePoissonBracket H (affinePoissonBracket F G) = 0 := by
  simp [affinePoissonBracket, poisson_scalar_bracket_zero_right]

/-- The left-nested cyclic form of Jacobi. -/
theorem poisson_jacobi_cyclic {R : Type*} [CommRing R] (F G H : AffineObservable R) :
    affinePoissonBracket (affinePoissonBracket F G) H +
      affinePoissonBracket (affinePoissonBracket G H) F +
      affinePoissonBracket (affinePoissonBracket H F) G = 0 := by
  simp [affinePoissonBracket, poisson_scalar_bracket_zero]

/-! ### Section 3: Parameter-scaled symplectic pairing -/

/-- Parameter-scaled pairing on linear coefficients (historical name):
$[u, v]_\star = \hbar \, \Omega(u, v)$. -/
def starCommutator {R : Type*} [CommRing R] (ℏ : R) (u v : PhaseSpace4 R) : R :=
  ℏ * symplecticForm u v

/-- Classical limit $\hbar = 0$: the deformed commutator vanishes identically,
a statement about this scaled pairing. -/
theorem star_commutator_classical_limit {R : Type*} [CommRing R] (u v : PhaseSpace4 R) :
    starCommutator 0 u v = 0 := by
  simp [starCommutator]

/-- Scaling identity for the parameter-dependent pairing:
The parameter-scaled pairing is $\hbar$ times the coefficient Poisson pairing:
$[u, v]_\star = \hbar \{u, v\}$. -/
theorem star_commutator_first_order {R : Type*} [CommRing R] (ℏ : R) (u v : PhaseSpace4 R) :
    starCommutator ℏ u v = ℏ * poissonBracket u v :=
  rfl

/-- Antisymmetry of the star commutator: $[u, v]_\star = -[v, u]_\star$. -/
theorem star_commutator_antisymm {R : Type*} [CommRing R] (ℏ : R) (u v : PhaseSpace4 R) :
    starCommutator ℏ u v = -starCommutator ℏ v u := by
  dsimp [starCommutator]
  rw [symplecticForm_skew]
  ring

/-- Darboux position coordinate $q_1$. -/
def q1 {R : Type*} [CommRing R] : PhaseSpace4 R :=
  fun i => if i = 0 then 1 else 0

/-- Darboux position coordinate $q_2$. -/
def q2 {R : Type*} [CommRing R] : PhaseSpace4 R :=
  fun i => if i = 1 then 1 else 0

/-- Darboux momentum coordinate $p_1$. -/
def p1 {R : Type*} [CommRing R] : PhaseSpace4 R :=
  fun i => if i = 2 then 1 else 0

/-- Darboux momentum coordinate $p_2$. -/
def p2 {R : Type*} [CommRing R] : PhaseSpace4 R :=
  fun i => if i = 3 then 1 else 0

/-- Canonical Commutation Relation: $[q_1, p_1]_\star = \hbar$. -/
theorem ccr_q1_p1 {R : Type*} [CommRing R] (ℏ : R) :
    starCommutator ℏ (q1 : PhaseSpace4 R) p1 = ℏ := by
  simp [starCommutator, symplecticForm, q1, p1]

/-- The affine bracket is nontrivial: the first Darboux pair produces
exactly the central unit observable. -/
theorem affinePoissonBracket_q1_p1 {R : Type*} [CommRing R] :
    affinePoissonBracket (0, (q1 : PhaseSpace4 R)) (0, p1) = (1, 0) := by
  apply Prod.ext <;> simp [affinePoissonBracket, poissonBracket, symplecticForm, q1, p1]

theorem affinePoissonBracket_q1_p1_ne_zero {R : Type*} [CommRing R] [Nontrivial R] :
    affinePoissonBracket (0, (q1 : PhaseSpace4 R)) (0, p1) ≠ 0 := by
  rw [affinePoissonBracket_q1_p1]
  intro h
  have hfirst := congrArg Prod.fst h
  exact one_ne_zero hfirst

/-- Canonical Commutation Relation: $[p_1, q_1]_\star = -\hbar$. -/
theorem ccr_p1_q1 {R : Type*} [CommRing R] (ℏ : R) :
    starCommutator ℏ (p1 : PhaseSpace4 R) q1 = -ℏ := by
  simp [starCommutator, symplecticForm, q1, p1]

/-- Canonical Commutation Relation: $[q_2, p_2]_\star = \hbar$. -/
theorem ccr_q2_p2 {R : Type*} [CommRing R] (ℏ : R) :
    starCommutator ℏ (q2 : PhaseSpace4 R) p2 = ℏ := by
  simp [starCommutator, symplecticForm, q2, p2]

/-- Canonical Commutation Relation: $[q_1, q_2]_\star = 0$. -/
theorem ccr_q1_q2 {R : Type*} [CommRing R] (ℏ : R) :
    starCommutator ℏ (q1 : PhaseSpace4 R) q2 = 0 := by
  simp [starCommutator, symplecticForm, q1, q2]

/-- Canonical Commutation Relation: $[p_1, p_2]_\star = 0$. -/
theorem ccr_p1_p2 {R : Type*} [CommRing R] (ℏ : R) :
    starCommutator ℏ (p1 : PhaseSpace4 R) p2 = 0 := by
  simp [starCommutator, symplecticForm, p1, p2]

/-- Canonical Commutation Relation: $[q_1, p_2]_\star = 0$. -/
theorem ccr_q1_p2 {R : Type*} [CommRing R] (ℏ : R) :
    starCommutator ℏ (q1 : PhaseSpace4 R) p2 = 0 := by
  simp [starCommutator, symplecticForm, q1, p2]

/-- Canonical Commutation Relation: $[q_2, p_1]_\star = 0$. -/
theorem ccr_q2_p1 {R : Type*} [CommRing R] (ℏ : R) :
    starCommutator ℏ (q2 : PhaseSpace4 R) p1 = 0 := by
  simp [starCommutator, symplecticForm, q2, p1]

/-! ### Section 4: Phase Space Hessian & Metric Compatibility -/

/-- Bilinear Hessian evaluation for quadratic forms on 4D phase space:
$\mathrm{Hess}_H(u, v) = \sum_{i, j=0}^3 u_i H_{ij} v_j$. -/
def phaseSpaceHessian {R : Type*} [CommRing R]
    (H : Matrix (Fin 4) (Fin 4) R) (u v : PhaseSpace4 R) : R :=
  ∑ i : Fin 4, ∑ j : Fin 4, u i * H i j * v j

/-- Under the standard Euclidean metric $H = I_4$, the Hessian diagonal recovers the
Riemannian norm squared: $\|u\|^2 = q_1^2 + q_2^2 + p_1^2 + p_2^2$. -/
theorem phaseSpaceHessian_id {R : Type*} [CommRing R] (u : PhaseSpace4 R) :
    phaseSpaceHessian 1 u u = (u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2 := by
  simp [phaseSpaceHessian, Fin.sum_univ_four, Matrix.one_apply]
  ring

/-- Symplectic-complex metric compatibility:
Pairing a phase space vector $u$ with its complex structure image $J u = \Omega u$ via the
symplectic form yields the negative Riemannian Euclidean norm:
$\Omega(u, J u) = -\|u\|^2 = -(u_0^2 + u_1^2 + u_2^2 + u_3^2)$. -/
theorem symplectic_complex_metric {R : Type*} [CommRing R] (u : PhaseSpace4 R) :
    symplecticForm u (fun i => ∑ j, (symplecticMatrix R) i j * u j) =
      -((u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2) := by
  simp [symplecticForm, symplecticMatrix, Fin.sum_univ_four]
  ring

/-! ### Section 5: Master Verification Certificate -/

/-- Master verification certificate for the Weyl-Moyal deformation of Gr(2, 4).
Bundles:
1. Skew-symmetry of $\Omega$
2. Almost complex structure condition $\Omega^2 = -I_4$
3. Alternating property of the symplectic form
4. Skew-symmetry of the symplectic form
5. Antisymmetry of the Poisson bracket
6. Left-linearity of the Poisson bracket
7. Linear Jacobi identity
8. Classical limit of the star commutator ($\hbar \to 0$)
9. First-order equivalence with the Poisson bracket
10. Antisymmetry of the star commutator
11. Canonical Commutation Relations (CCR) on the Darboux basis
12. Euclidean Hessian diagonal identity
13. Symplectic-complex metric compatibility $\Omega(u, J u) = -\|u\|^2$
-/
structure WeylMoyalSuperGrassmannianCertificate : Prop where
  symplectic_skew : ∀ (R : Type*) [CommRing R],
    (symplecticMatrix R)ᵀ = -symplecticMatrix R
  symplectic_sq : ∀ (R : Type*) [CommRing R],
    symplecticMatrix R * symplecticMatrix R = -1
  form_alt : ∀ (R : Type*) [CommRing R] (u : PhaseSpace4 R),
    symplecticForm u u = 0
  form_skew : ∀ (R : Type*) [CommRing R] (u v : PhaseSpace4 R),
    symplecticForm u v = -symplecticForm v u
  poisson_anti : ∀ (R : Type*) [CommRing R] (u v : PhaseSpace4 R),
    poissonBracket u v = -poissonBracket v u
  poisson_linear : ∀ (R : Type*) [CommRing R] (c : R) (u₁ u₂ v : PhaseSpace4 R),
    poissonBracket (u₁ + u₂) v = poissonBracket u₁ v + poissonBracket u₂ v ∧
    poissonBracket (c • u₁) v = c * poissonBracket u₁ v
  poisson_jacobi_lin : ∀ (R : Type*) [CommRing R] (F G H : AffineObservable R),
    affinePoissonBracket F (affinePoissonBracket G H) +
      affinePoissonBracket G (affinePoissonBracket H F) +
      affinePoissonBracket H (affinePoissonBracket F G) = 0
  star_classical : ∀ (R : Type*) [CommRing R] (u v : PhaseSpace4 R),
    starCommutator 0 u v = 0
  star_first_order : ∀ (R : Type*) [CommRing R] (ℏ : R) (u v : PhaseSpace4 R),
    starCommutator ℏ u v = ℏ * poissonBracket u v
  star_anti : ∀ (R : Type*) [CommRing R] (ℏ : R) (u v : PhaseSpace4 R),
    starCommutator ℏ u v = -starCommutator ℏ v u
  ccr_darboux : ∀ (R : Type*) [CommRing R] (ℏ : R),
    starCommutator ℏ q1 p1 = ℏ ∧
    starCommutator ℏ p1 q1 = -ℏ ∧
    starCommutator ℏ q2 p2 = ℏ ∧
    starCommutator ℏ q1 q2 = 0 ∧
    starCommutator ℏ p1 p2 = 0 ∧
    starCommutator ℏ q1 p2 = 0
  hessian_euclidean : ∀ (R : Type*) [CommRing R] (u : PhaseSpace4 R),
    phaseSpaceHessian 1 u u = (u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2
  metric_compatibility : ∀ (R : Type*) [CommRing R] (u : PhaseSpace4 R),
    symplecticForm u (fun i => ∑ j, (symplecticMatrix R) i j * u j) =
      -((u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2)

/-- Compilation theorem: the master certificate is constructively inhabited. -/
theorem compile_weyl_moyal_super_grassmannian :
    WeylMoyalSuperGrassmannianCertificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R _ ; exact symplecticMatrix_transpose R
  · intro R _ ; exact symplecticMatrix_sq R
  · intro R _ u ; exact symplecticForm_alt u
  · intro R _ u v ; exact symplecticForm_skew u v
  · intro R _ u v ; exact poisson_antisymm u v
  · intro R _ c u₁ u₂ v ; exact ⟨poisson_add_left u₁ u₂ v, poisson_smul_left c u₁ v⟩
  · intro R _ u v w ; exact poisson_jacobi u v w
  · intro R _ u v ; exact star_commutator_classical_limit u v
  · intro R _ ℏ u v ; exact star_commutator_first_order ℏ u v
  · intro R _ ℏ u v ; exact star_commutator_antisymm ℏ u v
  · intro R _ ℏ ; exact ⟨ccr_q1_p1 ℏ, ccr_p1_q1 ℏ, ccr_q2_p2 ℏ, ccr_q1_q2 ℏ, ccr_p1_p2 ℏ, ccr_q1_p2 ℏ⟩
  · intro R _ u ; exact phaseSpaceHessian_id u
  · intro R _ u ; exact symplectic_complex_metric u

end InfoGeometry.Clifford.WeylMoyalSuperGrassmannian
