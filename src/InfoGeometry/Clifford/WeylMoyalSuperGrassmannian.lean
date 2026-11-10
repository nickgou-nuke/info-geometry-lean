/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
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
def symplecticMatrix (R : Type*) [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  !![ 0,  0, 1, 0;
      0,  0, 0, 1;
     -1,  0, 0, 0;
      0, -1, 0, 0]

/-- Implicit-carrier alias of `symplecticMatrix R`. -/
def symplecticOmega {R : Type*} [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  symplecticMatrix R

/-- Symplectic parity reflection reversing momentum coordinates $p_i \mapsto -p_i$. -/
def symplecticReflection {R : Type*} [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  !![ 1, 0,  0,  0;
      0, 1,  0,  0;
      0, 0, -1,  0;
      0, 0,  0, -1]

/-- Exact anticommutation $\Omega \Sigma + \Sigma \Omega = 0$ in $M_4(R)$ over any `[Ring R]`. -/
theorem symplecticOmega_anticomm_reflection {R : Type*} [Ring R] :
    symplecticOmega (R := R) * symplecticReflection (R := R) +
      symplecticReflection (R := R) * symplecticOmega (R := R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symplecticOmega, symplecticMatrix, symplecticReflection, Matrix.mul_apply, Fin.sum_univ_four]

/-- The symplectic matrix is skew-symmetric: $\Omega^T = -\Omega$. -/
theorem symplecticMatrix_transpose (R : Type*) [Ring R] :
    (symplecticMatrix R)ᵀ = -symplecticMatrix R := by
  ext i j
  fin_cases i <;> fin_cases j <;> { simp [symplecticMatrix, Matrix.transpose_apply]; try ring }

/-- The symplectic matrix squares to $-I_4$, as a ring-valued matrix identity:
$\Omega^2 = -1$. -/
theorem symplecticMatrix_sq (R : Type*) [Ring R] :
    symplecticMatrix R * symplecticMatrix R = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [symplecticMatrix, Matrix.mul_apply, Fin.sum_univ_four]
    try ring
  }

/-- The canonical symplectic form $\Omega(u, v)$ on $\mathbb{R}^4$:
$\Omega(u, v) = u_0 v_2 - u_2 v_0 + u_1 v_3 - u_3 v_1 = q_1 p_1' - p_1 q_1' + q_2 p_2' - p_2 q_2'$. -/
def symplecticForm {R : Type*} [Ring R] (u v : PhaseSpace4 R) : R :=
  u 0 * v 2 - u 2 * v 0 + u 1 * v 3 - u 3 * v 1

/-- Over any non-commutative ring `[Ring R]`, the diagonal symplectic pairing $\Omega(u, u)$
equals the sum of the two canonical phase-space coordinate commutators
`[u 0, u 2] + [u 1, u 3]`. -/
theorem symplecticForm_self_noncomm {R : Type*} [Ring R] (u : PhaseSpace4 R) :
    symplecticForm u u = (u 0 * u 2 - u 2 * u 0) + (u 1 * u 3 - u 3 * u 1) := by
  simp [symplecticForm]
  abel

/-- Over any commutative ring, the symplectic form is strictly alternating: $\Omega(u, u) = 0$. -/
theorem symplecticForm_alt {R : Type*} [CommRing R] (u : PhaseSpace4 R) :
    symplecticForm u u = 0 := by
  simp [symplecticForm]
  ring

/-- Over any commutative ring, the symplectic form is strictly skew-symmetric:
$\Omega(u, v) = -\Omega(v, u)$. -/
theorem symplecticForm_skew {R : Type*} [CommRing R] (u v : PhaseSpace4 R) :
    symplecticForm u v = -symplecticForm v u := by
  simp [symplecticForm]
  ring

/-! ### Section 2: Canonical Poisson Bracket on Linear Observables -/

/-- The canonical Poisson bracket $\{u, v\}$ on linear phase space observables,
governed by the symplectic form $\Omega(u, v)$. -/
def poissonBracket {R : Type*} [Ring R] (u v : PhaseSpace4 R) : R :=
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
theorem poisson_add_left {R : Type*} [Ring R] (u₁ u₂ v : PhaseSpace4 R) :
    poissonBracket (u₁ + u₂) v = poissonBracket u₁ v + poissonBracket u₂ v := by
  simp [poissonBracket, symplecticForm]
  noncomm_ring

/-- Right-additivity of the Poisson bracket. -/
theorem poisson_add_right {R : Type*} [Ring R] (u v₁ v₂ : PhaseSpace4 R) :
    poissonBracket u (v₁ + v₂) = poissonBracket u v₁ + poissonBracket u v₂ := by
  simp [poissonBracket, symplecticForm]
  noncomm_ring

/-- Left-scalar multiplication on the Poisson bracket. -/
theorem poisson_smul_left {R : Type*} [Ring R] (c : R) (u v : PhaseSpace4 R) :
    poissonBracket (c • u) v = c * poissonBracket u v := by
  simp [poissonBracket, symplecticForm]
  noncomm_ring

/-- Right-scalar multiplication on the Poisson bracket. -/
theorem poisson_smul_right {R : Type*} [CommRing R] (c : R) (u v : PhaseSpace4 R) :
    poissonBracket u (c • v) = c * poissonBracket u v := by
  simp [poissonBracket, symplecticForm]
  ring

/-- Constant scalar observables have vanishing phase space gradients,
hence their Poisson bracket with any observable vanishes. -/
theorem poisson_scalar_bracket_zero {R : Type*} [Ring R] (w : PhaseSpace4 R) :
    poissonBracket (0 : PhaseSpace4 R) w = 0 := by
  simp [poissonBracket, symplecticForm]

/-- Constant scalar observables on the right have vanishing Poisson bracket. -/
theorem poisson_scalar_bracket_zero_right {R : Type*} [Ring R] (w : PhaseSpace4 R) :
    poissonBracket w (0 : PhaseSpace4 R) = 0 := by
  simp [poissonBracket, symplecticForm]

/-- Affine observables retain their constant term as well as their four
linear coefficients. Unlike coefficient vectors alone, this carrier is closed
under the canonical Poisson bracket. -/
abbrev AffineObservable (R : Type*) := R × PhaseSpace4 R

/-- Evaluation of an affine observable at a phase-space point. -/
def affineEval {R : Type*} [Ring R] (F : AffineObservable R)
    (x : PhaseSpace4 R) : R := F.1 + ∑ i, F.2 i * x i

/-- The bracket of affine observables is the constant observable determined
by their symplectic pairing. -/
def affinePoissonBracket {R : Type*} [Ring R]
    (F G : AffineObservable R) : AffineObservable R :=
  (poissonBracket F.2 G.2, 0)

theorem affinePoissonBracket_eval {R : Type*} [Ring R]
    (F G : AffineObservable R) (x : PhaseSpace4 R) :
    affineEval (affinePoissonBracket F G) x = poissonBracket F.2 G.2 := by
  simp [affineEval, affinePoissonBracket]

theorem affinePoissonBracket_antisymm {R : Type*} [CommRing R]
    (F G : AffineObservable R) :
    affinePoissonBracket F G = -affinePoissonBracket G F := by
  apply Prod.ext
  · exact poisson_antisymm F.2 G.2
  · simp [affinePoissonBracket]

theorem affinePoissonBracket_add_left {R : Type*} [Ring R]
    (F G H : AffineObservable R) :
    affinePoissonBracket (F + G) H = affinePoissonBracket F H + affinePoissonBracket G H := by
  apply Prod.ext
  · exact poisson_add_left F.2 G.2 H.2
  · simp [affinePoissonBracket]

theorem affinePoissonBracket_smul_left {R : Type*} [Ring R]
    (c : R) (F G : AffineObservable R) :
    affinePoissonBracket (c • F) G = c • affinePoissonBracket F G := by
  apply Prod.ext
  · exact poisson_smul_left c F.2 G.2
  · simp [affinePoissonBracket]

/-- Constants are central in the actual closed observable carrier. -/
@[simp] theorem affinePoissonBracket_constant_left {R : Type*} [Ring R]
    (c : R) (F : AffineObservable R) :
    affinePoissonBracket (c, 0) F = 0 := by
  apply Prod.ext <;> simp [affinePoissonBracket, poissonBracket, symplecticForm]

@[simp] theorem affinePoissonBracket_constant_right {R : Type*} [Ring R]
    (F : AffineObservable R) (c : R) :
    affinePoissonBracket F (c, 0) = 0 := by
  apply Prod.ext <;> simp [affinePoissonBracket, poissonBracket, symplecticForm]

/-- Genuine cyclic Jacobi identity on all affine observables. -/
theorem poisson_jacobi {R : Type*} [Ring R] (F G H : AffineObservable R) :
    affinePoissonBracket F (affinePoissonBracket G H) +
      affinePoissonBracket G (affinePoissonBracket H F) +
      affinePoissonBracket H (affinePoissonBracket F G) = 0 := by
  simp [affinePoissonBracket, poisson_scalar_bracket_zero_right]

/-- The left-nested cyclic form of Jacobi. -/
theorem poisson_jacobi_cyclic {R : Type*} [Ring R] (F G H : AffineObservable R) :
    affinePoissonBracket (affinePoissonBracket F G) H +
      affinePoissonBracket (affinePoissonBracket G H) F +
      affinePoissonBracket (affinePoissonBracket H F) G = 0 := by
  simp [affinePoissonBracket, poisson_scalar_bracket_zero]

/-! ### Section 3: Parameter-scaled symplectic pairing -/

/-- Parameter-scaled pairing on linear coefficients (historical name):
$[u, v]_\star = \hbar \, \Omega(u, v)$. -/
def starCommutator {R : Type*} [Ring R] (ℏ : R) (u v : PhaseSpace4 R) : R :=
  ℏ * symplecticForm u v

/-- Classical limit $\hbar = 0$: the deformed commutator vanishes identically,
a statement about this scaled pairing. -/
theorem star_commutator_classical_limit {R : Type*} [Ring R] (u v : PhaseSpace4 R) :
    starCommutator 0 u v = 0 := by
  simp [starCommutator]

/-- Scaling identity for the parameter-dependent pairing:
The parameter-scaled pairing is $\hbar$ times the coefficient Poisson pairing:
$[u, v]_\star = \hbar \{u, v\}$. -/
theorem star_commutator_first_order {R : Type*} [Ring R] (ℏ : R) (u v : PhaseSpace4 R) :
    starCommutator ℏ u v = ℏ * poissonBracket u v :=
  rfl

/-- Antisymmetry of the star commutator: $[u, v]_\star = -[v, u]_\star$. -/
theorem star_commutator_antisymm {R : Type*} [CommRing R] (ℏ : R) (u v : PhaseSpace4 R) :
    starCommutator ℏ u v = -starCommutator ℏ v u := by
  dsimp [starCommutator]
  rw [symplecticForm_skew]
  ring

/-- Darboux position coordinate $q_1$. -/
def q1 {R : Type*} [Ring R] : PhaseSpace4 R :=
  fun i => if i = 0 then 1 else 0

/-- Darboux position coordinate $q_2$. -/
def q2 {R : Type*} [Ring R] : PhaseSpace4 R :=
  fun i => if i = 1 then 1 else 0

/-- Darboux momentum coordinate $p_1$. -/
def p1 {R : Type*} [Ring R] : PhaseSpace4 R :=
  fun i => if i = 2 then 1 else 0

/-- Darboux momentum coordinate $p_2$. -/
def p2 {R : Type*} [Ring R] : PhaseSpace4 R :=
  fun i => if i = 3 then 1 else 0

/-- Canonical Commutation Relation: $[q_1, p_1]_\star = \hbar$. -/
theorem ccr_q1_p1 {R : Type*} [Ring R] (ℏ : R) :
    starCommutator ℏ (q1 : PhaseSpace4 R) p1 = ℏ := by
  simp [starCommutator, symplecticForm, q1, p1]

/-- The affine bracket is nontrivial: the first Darboux pair produces
exactly the central unit observable. -/
theorem affinePoissonBracket_q1_p1 {R : Type*} [Ring R] :
    affinePoissonBracket (0, (q1 : PhaseSpace4 R)) (0, p1) = (1, 0) := by
  apply Prod.ext <;> simp [affinePoissonBracket, poissonBracket, symplecticForm, q1, p1]

theorem affinePoissonBracket_q1_p1_ne_zero {R : Type*} [Ring R] [Nontrivial R] :
    affinePoissonBracket (0, (q1 : PhaseSpace4 R)) (0, p1) ≠ 0 := by
  rw [affinePoissonBracket_q1_p1]
  intro h
  have hfirst := congrArg Prod.fst h
  exact one_ne_zero hfirst

/-- Canonical Commutation Relation: $[p_1, q_1]_\star = -\hbar$. -/
theorem ccr_p1_q1 {R : Type*} [Ring R] (ℏ : R) :
    starCommutator ℏ (p1 : PhaseSpace4 R) q1 = -ℏ := by
  simp [starCommutator, symplecticForm, q1, p1]

/-- Canonical Commutation Relation: $[q_2, p_2]_\star = \hbar$. -/
theorem ccr_q2_p2 {R : Type*} [Ring R] (ℏ : R) :
    starCommutator ℏ (q2 : PhaseSpace4 R) p2 = ℏ := by
  simp [starCommutator, symplecticForm, q2, p2]

/-- Canonical Commutation Relation: $[q_1, q_2]_\star = 0$. -/
theorem ccr_q1_q2 {R : Type*} [Ring R] (ℏ : R) :
    starCommutator ℏ (q1 : PhaseSpace4 R) q2 = 0 := by
  simp [starCommutator, symplecticForm, q1, q2]

/-- Canonical Commutation Relation: $[p_1, p_2]_\star = 0$. -/
theorem ccr_p1_p2 {R : Type*} [Ring R] (ℏ : R) :
    starCommutator ℏ (p1 : PhaseSpace4 R) p2 = 0 := by
  simp [starCommutator, symplecticForm, p1, p2]

/-- Canonical Commutation Relation: $[q_1, p_2]_\star = 0$. -/
theorem ccr_q1_p2 {R : Type*} [Ring R] (ℏ : R) :
    starCommutator ℏ (q1 : PhaseSpace4 R) p2 = 0 := by
  simp [starCommutator, symplecticForm, q1, p2]

/-- Canonical Commutation Relation: $[q_2, p_1]_\star = 0$. -/
theorem ccr_q2_p1 {R : Type*} [Ring R] (ℏ : R) :
    starCommutator ℏ (q2 : PhaseSpace4 R) p1 = 0 := by
  simp [starCommutator, symplecticForm, q2, p1]

/-! ### Section 4: Phase Space Hessian & Metric Compatibility -/

/-- Bilinear Hessian evaluation for quadratic forms on 4D phase space:
$\mathrm{Hess}_H(u, v) = \sum_{i, j=0}^3 u_i H_{ij} v_j$. -/
def phaseSpaceHessian {R : Type*} [Ring R]
    (H : Matrix (Fin 4) (Fin 4) R) (u v : PhaseSpace4 R) : R :=
  ∑ i : Fin 4, ∑ j : Fin 4, u i * H i j * v j

/-- Under the standard Euclidean metric $H = I_4$, the Hessian diagonal recovers the
Riemannian norm squared: $\|u\|^2 = q_1^2 + q_2^2 + p_1^2 + p_2^2$. -/
theorem phaseSpaceHessian_id {R : Type*} [Ring R] (u : PhaseSpace4 R) :
    phaseSpaceHessian 1 u u = (u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2 := by
  simp [phaseSpaceHessian, Fin.sum_univ_four, Matrix.one_apply]
  noncomm_ring

/-- Symplectic-complex metric compatibility:
Pairing a phase space vector $u$ with its complex structure image $J u = \Omega u$ via the
symplectic form yields the negative Riemannian Euclidean norm:
$\Omega(u, J u) = -\|u\|^2 = -(u_0^2 + u_1^2 + u_2^2 + u_3^2)$. -/
theorem symplectic_complex_metric {R : Type*} [Ring R] (u : PhaseSpace4 R) :
    symplecticForm u (fun i => ∑ j, (symplecticMatrix R) i j * u j) =
      -((u 0)^2 + (u 1)^2 + (u 2)^2 + (u 3)^2) := by
  simp [symplecticForm, symplecticMatrix, Fin.sum_univ_four]
  noncomm_ring

/-! ### Section 5: Master Verification Synthesis -/

/-- Master verification synthesis for the Weyl-Moyal symplectic and affine Poisson algebra. -/
theorem compile_weyl_moyal_super_grassmannian
    {B : Type*} [Ring B] (cb ℏb : B) (ub₁ ub₂ vb : PhaseSpace4 B) (Fb Gb Hb : AffineObservable B)
    {R : Type*} [CommRing R] (ℏ : R) (u v : PhaseSpace4 R) :
    ((symplecticMatrix B)ᵀ = -symplecticMatrix B) ∧
    (symplecticMatrix B * symplecticMatrix B = -1) ∧
    (symplecticForm u u = 0) ∧
    (symplecticForm u v = -symplecticForm v u) ∧
    (poissonBracket u v = -poissonBracket v u) ∧
    (poissonBracket (ub₁ + ub₂) vb = poissonBracket ub₁ vb + poissonBracket ub₂ vb ∧
     poissonBracket (cb • ub₁) vb = cb * poissonBracket ub₁ vb) ∧
    (affinePoissonBracket Fb (affinePoissonBracket Gb Hb) +
      affinePoissonBracket Gb (affinePoissonBracket Hb Fb) +
      affinePoissonBracket Hb (affinePoissonBracket Fb Gb) = 0) ∧
    (starCommutator 0 ub₁ vb = 0) ∧
    (starCommutator ℏb ub₁ vb = ℏb * poissonBracket ub₁ vb) ∧
    (starCommutator ℏ u v = -starCommutator ℏ v u) ∧
    (starCommutator ℏb q1 p1 = ℏb ∧
     starCommutator ℏb p1 q1 = -ℏb ∧
     starCommutator ℏb q2 p2 = ℏb ∧
     starCommutator ℏb q1 q2 = 0 ∧
     starCommutator ℏb p1 p2 = 0 ∧
     starCommutator ℏb q1 p2 = 0) ∧
    (phaseSpaceHessian 1 ub₁ ub₁ = (ub₁ 0)^2 + (ub₁ 1)^2 + (ub₁ 2)^2 + (ub₁ 3)^2) ∧
    (symplecticForm ub₁ (fun i => ∑ j, (symplecticMatrix B) i j * ub₁ j) =
      -((ub₁ 0)^2 + (ub₁ 1)^2 + (ub₁ 2)^2 + (ub₁ 3)^2)) :=
  ⟨symplecticMatrix_transpose B,
   symplecticMatrix_sq B,
   symplecticForm_alt u,
   symplecticForm_skew u v,
   poisson_antisymm u v,
   ⟨poisson_add_left ub₁ ub₂ vb, poisson_smul_left cb ub₁ vb⟩,
   poisson_jacobi Fb Gb Hb,
   star_commutator_classical_limit ub₁ vb,
   star_commutator_first_order ℏb ub₁ vb,
   star_commutator_antisymm ℏ u v,
   ⟨ccr_q1_p1 ℏb, ccr_p1_q1 ℏb, ccr_q2_p2 ℏb, ccr_q1_q2 ℏb, ccr_p1_p2 ℏb, ccr_q1_p2 ℏb⟩,
   phaseSpaceHessian_id ub₁,
   symplectic_complex_metric ub₁⟩

end InfoGeometry.Clifford.WeylMoyalSuperGrassmannian
