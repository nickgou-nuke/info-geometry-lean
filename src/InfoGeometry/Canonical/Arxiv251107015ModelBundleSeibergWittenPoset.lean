/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# The Geometric View of Theories: Model Bundles, Quasi-Dualities, and Seiberg–Witten Monodromy

This module formalizes the mathematical archetypes of Sebastian De Haro,
*"The Geometric View of Theories"* (`arXiv:2511.07015`, *Synthese* 2026, 207:37),
translated into the native Mathlib 4 language of `info-geometry-lean`.

## Three-Bucket Audit Map

- BUCKET 1 (Keep and inline):
  - The independently proved state–quantity pairing, transition-cocycle, modular-monodromy,
    symplectic, holographic, and noncommutative Peirce results below. Their ordering in this file
    is organizational; no theorem claims that the full list forms a dependency poset.
  - `centralChargePairing`, `periodAction`, `chargeAction`, and
    `centralChargePairing_contragredient_invariance` formalizing the state–quantity bilinear
    pairing $Z(q, v) = n_m a_D + n_e a$ and its invariance under $v \mapsto M v$,
    $q \mapsto q M^{-1}$, together with `dualPropagatorConjugation_intertwines`.
  - `verticalQuasiDualityCocycle` and its Čech 1-cocycle laws (`_self`, `_symm`, `_comp`,
    `_transports_local_section`, and `globalDuality_iff_trivial_transition_cocycle`) on
    fiber local trivializations $\phi_{i,t} : F \simeq_R V$.
  - `modularGeneratorS`, `modularGeneratorT`, `modularGeneratorS_sq`, `modularGeneratorST_cubed`,
    and `effectiveCouplingRatio_modularGeneratorS` proving the vertical $S$-duality inversion
    $\tau = a_D / a \mapsto -1/\tau$.
  - `swMonodromyInf`, `swMonodromyPosLambda`, `swMonodromyNegLambda`, punctured-sphere
    factorization $M_\Lambda M_{-\Lambda} = M_\infty$, $S$-duality conjugacy
    $S T^2 S^{-1} = M_\Lambda$, parabolic Jordan nilpotency $(M \pm I_2)^2 = 0$,
    monopole/electron/dyon charge transport, massless BPS fixed vectors, and the mod-2
    $\Gamma(2)$ congruence obstruction proving $S \notin \Gamma(2)$.
  - `canonicalSymplecticForm` and `canonicalKahlerMetric` proving $\mathrm{SL}(2, R)$ symplectic
    invariance $\omega(M v, M w) = (\det M)\,\omega(v, w)$ and Kähler compatibility
    $g(v, w) = \omega(v, S w)$.
  - `holographicPartitionSecondOrder` and `connectedTwoPointFromMoments` proving the second-order
    Wheeler–DeWitt de Sitter CFT cumulant-to-moment inversion and linked-cluster factorization.
  - `modularDilation`, `quasiDualityJumpPlus`, `quasiDualityJumpMinus`,
    `parityInversionOperator`, `parabolicFiveGradedTower_decomposition`,
    `parabolicGrade_ad_modularDilation_eigenvalues`, and
    `maurerCartanCurvature_flat_iff_deformed_sq_zero` realizing De Haro's Model Bundle and
    "Theory of Theories" inside an associative non-commutative operator ring `[Ring B]` framed
    by three orthogonal horizons $1 = P_1 + P_0 + P_2$.
- BUCKET 2 (Replace and delete):
  - All informal prose claims, unverified transition diagrams, and wrapper-based representations
    are replaced by direct native Mathlib 4 definitions, lemmas, and theorems.
- BUCKET 3 (Preserve compatibility):
  - Coordinates with `InfoGeometry.Canonical.PSLDescent` and
    `InfoGeometry.Compatibility.MathlibModularShadow`.
-/

namespace InfoGeometry.Canonical.Arxiv251107015ModelBundleSeibergWittenPoset

open Matrix

/-! ## Proved Components

The sections below formalize distinct algebraic structures. They are not promoted to a causal
poset: a dependency edge requires an explicit theorem-level implication, and the literature's
conceptual sequence alone does not supply one. -/

/-! ## State–Quantity Contragredient Pairing & Dynamics Intertwining -/

section StateQuantityDuality

variable {R : Type*} [Ring R]

/-- The central charge / state–quantity evaluation pairing
$Z(q, v) = n_m a_D + n_e a = q_0 v_0 + q_1 v_1$ between a state charge vector $q = (n_m, n_e)$
and a period quantity vector $v = (a_D, a)^T$ (De Haro Sections 2.1, 3.1.1, and Eq. (6)). -/
def centralChargePairing (q v : Fin 2 → R) : R :=
  q 0 * v 0 + q 1 * v 1

/-- Covariant left action $v \mapsto M v$ of a $2 \times 2$ transition or monodromy matrix $M$
on the fiber period vector $v = (a_D, a)^T$. -/
def periodAction (M : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) : Fin 2 → R :=
  M.mulVec v

/-- Contragredient right action $q \mapsto q M^{-1}$ of an inverse transition or monodromy matrix
$M^{-1}$ on the state charge row vector $q = (n_m, n_e)$ (De Haro Eq. (8)). -/
def chargeAction (Minv : Matrix (Fin 2) (Fin 2) R) (q : Fin 2 → R) : Fin 2 → R :=
  Matrix.vecMul q Minv

/-- Explicit component evaluation of `periodAction M v`. -/
lemma periodAction_explicit (M : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) :
    periodAction M v = ![M 0 0 * v 0 + M 0 1 * v 1, M 1 0 * v 0 + M 1 1 * v 1] := by
  ext i
  fin_cases i <;>
    simp [periodAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Explicit component evaluation of `chargeAction Minv q`. -/
lemma chargeAction_explicit (Minv : Matrix (Fin 2) (Fin 2) R) (q : Fin 2 → R) :
    chargeAction Minv q = ![q 0 * Minv 0 0 + q 1 * Minv 1 0, q 0 * Minv 0 1 + q 1 * Minv 1 1] := by
  ext i
  fin_cases i <;>
    simp [chargeAction, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Explicit dot-product representation of `centralChargePairing q v`. -/
lemma centralChargePairing_eq_dotProduct (q v : Fin 2 → R) :
    centralChargePairing q v = dotProduct q v := by
  dsimp [centralChargePairing, dotProduct]
  rw [Fin.sum_univ_two]

/-- Contragredient duality invariance of the state–quantity pairing: whenever $M^{-1} M = I_2$,
transforming periods by $v \mapsto M v$ and charges contragrediently by $q \mapsto q M^{-1}$
strictly preserves the central charge pairing $Z(q M^{-1}, M v) = Z(q, v)$. -/
theorem centralChargePairing_contragredient_invariance
    (M Minv : Matrix (Fin 2) (Fin 2) R) (hInv : Minv * M = 1) (q v : Fin 2 → R) :
    centralChargePairing (chargeAction Minv q) (periodAction M v) =
      centralChargePairing q v := by
  rw [centralChargePairing_eq_dotProduct, centralChargePairing_eq_dotProduct]
  dsimp [chargeAction, periodAction]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hInv, Matrix.vecMul_one]

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- Duality conjugation $U_2 = d \circ U_1 \circ d^{-1}$ of a linear time-evolution or Hamiltonian
operator $U_1 : M_1 \to_R M_1$ across a state-space duality isomorphism $d : M_1 \simeq_R M_2$
(De Haro Section 2.1). -/
def dualPropagatorConjugation (d : M₁ ≃ₗ[R] M₂) (U₁ : M₁ →ₗ[R] M₁) : M₂ →ₗ[R] M₂ :=
  d.toLinearMap ∘ₗ U₁ ∘ₗ d.symm.toLinearMap

/-- The conjugated propagator $U_2 = d U_1 d^{-1}$ intertwines the duality isomorphism $d$:
$U_2(d(\psi)) = d(U_1(\psi))$. -/
theorem dualPropagatorConjugation_intertwines
    (d : M₁ ≃ₗ[R] M₂) (U₁ : M₁ →ₗ[R] M₁) (ψ : M₁) :
    dualPropagatorConjugation d U₁ (d ψ) = d (U₁ ψ) := by
  dsimp [dualPropagatorConjugation]
  rw [d.symm_apply_apply]

/-- Duality conjugation of dynamical propagators is functorial under operator composition. -/
theorem dualPropagatorConjugation_comp
    (d : M₁ ≃ₗ[R] M₂) (U₁ V₁ : M₁ →ₗ[R] M₁) :
    dualPropagatorConjugation d (U₁ ∘ₗ V₁) =
      (dualPropagatorConjugation d U₁) ∘ₗ (dualPropagatorConjugation d V₁) := by
  ext x
  dsimp [dualPropagatorConjugation]
  rw [d.symm_apply_apply]

end StateQuantityDuality

/-! ## Section 3: Archetype 2 — Model Bundle Transition Cocycles (Quasi-Dualities) -/

section ModelBundleCocycles

variable {R I B F V : Type*} [Ring R] [AddCommGroup F] [Module R F]
  [AddCommGroup V] [Module R V]

/-- Vertical fiber transition map (quasi-duality) $g_{ji}(t) = \phi_{j,t} \circ \phi_{i,t}^{-1}$
comparing local model bundle trivializations $\phi_{i,t}, \phi_{j,t} : F \simeq_R V$ over the
same base parameter $t \in B$ (De Haro Sections 3.1.1–3.1.2). -/
def verticalQuasiDualityCocycle
    (φ : I → B → (F ≃ₗ[R] V)) (j i : I) (t : B) : V ≃ₗ[R] V :=
  (φ i t).symm.trans (φ j t)

/-- Evaluation of the vertical quasi-duality transition $g_{ji}(t)$ on a fiber vector $v \in V$. -/
theorem verticalQuasiDualityCocycle_apply
    (φ : I → B → (F ≃ₗ[R] V)) (j i : I) (t : B) (v : V) :
    verticalQuasiDualityCocycle φ j i t v = φ j t ((φ i t).symm v) := by
  unfold verticalQuasiDualityCocycle
  rfl

/-- Čech 1-cocycle reflexivity: on a single chart $U_i$, the vertical transition map is the
identity isomorphism $g_{ii}(t) = \mathrm{id}_V$. -/
theorem verticalQuasiDualityCocycle_self
    (φ : I → B → (F ≃ₗ[R] V)) (i : I) (t : B) :
    verticalQuasiDualityCocycle φ i i t = LinearEquiv.refl R V := by
  ext v
  rw [verticalQuasiDualityCocycle_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- Čech 1-cocycle inversion: reversing the chart order inverts the quasi-duality transition map,
$g_{ji}(t)^{-1} = g_{ij}(t)$. -/
theorem verticalQuasiDualityCocycle_symm
    (φ : I → B → (F ≃ₗ[R] V)) (j i : I) (t : B) :
    (verticalQuasiDualityCocycle φ j i t).symm = verticalQuasiDualityCocycle φ i j t := by
  ext v
  unfold verticalQuasiDualityCocycle
  rfl

/-- Čech 1-cocycle triple-overlap law: on a triple overlap $U_i \cap U_j \cap U_k$, the vertical
quasi-duality transitions compose coherently as $g_{kj}(t) \circ g_{ji}(t) = g_{ki}(t)$. -/
theorem verticalQuasiDualityCocycle_comp
    (φ : I → B → (F ≃ₗ[R] V)) (k j i : I) (t : B) :
    (verticalQuasiDualityCocycle φ j i t).trans (verticalQuasiDualityCocycle φ k j t) =
      verticalQuasiDualityCocycle φ k i t := by
  ext v
  change verticalQuasiDualityCocycle φ k j t (verticalQuasiDualityCocycle φ j i t v) =
    verticalQuasiDualityCocycle φ k i t v
  rw [verticalQuasiDualityCocycle_apply, verticalQuasiDualityCocycle_apply,
    verticalQuasiDualityCocycle_apply, LinearEquiv.symm_apply_apply]

/-- Compatibility of local model sections: the quasi-duality $g_{ji}(t)$ transports the $i$-chart
representation $\phi_{i,t}(s(t))$ of a model section $s : B \to F$ to its $j$-chart representation
$\phi_{j,t}(s(t))$. -/
theorem verticalQuasiDualityCocycle_transports_local_section
    (φ : I → B → (F ≃ₗ[R] V)) (j i : I) (t : B) (s : B → F) :
    verticalQuasiDualityCocycle φ j i t (φ i t (s t)) = φ j t (s t) := by
  rw [verticalQuasiDualityCocycle_apply, LinearEquiv.symm_apply_apply]

/-- A local quasi-duality between charts $i$ and $j$ at base point $t$ reduces to the trivial
identity transition if and only if the two local trivializations coincide at $t$. -/
theorem globalDuality_iff_trivial_transition_cocycle
    (φ : I → B → (F ≃ₗ[R] V)) (j i : I) (t : B) :
    verticalQuasiDualityCocycle φ j i t = LinearEquiv.refl R V ↔ φ j t = φ i t := by
  constructor
  · intro h
    ext f
    have hf := congr_arg (fun e : V ≃ₗ[R] V => e (φ i t f)) h
    dsimp at hf
    rw [verticalQuasiDualityCocycle_apply, LinearEquiv.symm_apply_apply] at hf
    exact hf
  · intro h
    ext v
    rw [verticalQuasiDualityCocycle_apply, h, LinearEquiv.apply_symm_apply]
    rfl

/-- Structural Realism / Common-Core Invariance across Model-Bundle Charts (De Haro Sections 3.1 & 4):
if a local observable functional $E : V \to R$ is transported contravariantly from chart $i$ to
chart $j$ via the inverse transition cocycle $g_{ij}(t) = g_{ji}(t)^{-1}$, then evaluating the
transported observable on the $j$-chart representation $\phi_{j,t}(s(t))$ of any model section
$s : B \to F$ yields the exact same physical value as in chart $i$. -/
theorem modelBundle_common_core_observable_chart_invariant
    (φ : I → B → (F ≃ₗ[R] V)) (E : V → R) (j i : I) (t : B) (s : B → F) :
    E (verticalQuasiDualityCocycle φ i j t (φ j t (s t))) = E (φ i t (s t)) := by
  rw [verticalQuasiDualityCocycle_transports_local_section]

end ModelBundleCocycles

/-! ## Section 4: Archetype 3 — Torus Moduli & Vertical $S$-Duality Coupling Inversion -/

section ModularSDuality

variable {R : Type*} [Ring R]

/-- Left-ordered $2 \times 2$ matrix determinant $M_{00} M_{11} - M_{01} M_{10}$ over an arbitrary
(not necessarily commutative) ring $R$. -/
def det2x2 (M : Matrix (Fin 2) (Fin 2) R) : R :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

/-- The modular $S$-duality generator $S = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$
(De Haro Section 2.2 and Section 3.1.1). -/
def modularGeneratorS : Matrix (Fin 2) (Fin 2) R :=
  !![0, -1; 1, 0]

/-- The modular $T$-generator $T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$. -/
def modularGeneratorT : Matrix (Fin 2) (Fin 2) R :=
  !![1, 1; 0, 1]

/-- The inverse modular $T$-generator $T^{-1} = \begin{pmatrix} 1 & -1 \\ 0 & 1 \end{pmatrix}$. -/
def modularGeneratorTInv : Matrix (Fin 2) (Fin 2) R :=
  !![1, -1; 0, 1]

/-- $\det S = 1$. -/
theorem det_modularGeneratorS : det2x2 (modularGeneratorS (R := R)) = 1 := by
  dsimp [det2x2, modularGeneratorS]
  noncomm_ring

/-- $\det T = 1$. -/
theorem det_modularGeneratorT : det2x2 (modularGeneratorT (R := R)) = 1 := by
  dsimp [det2x2, modularGeneratorT]
  noncomm_ring

/-- $T T^{-1} = I_2$. -/
theorem modularGeneratorT_mul_inv :
    modularGeneratorT (R := R) * modularGeneratorTInv (R := R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularGeneratorT, modularGeneratorTInv, Matrix.mul_apply, Fin.sum_univ_two]

/-- $S^2 = -I_2$ in $\mathrm{SL}(2, R)$, which descends to $S^2 = 1$ in $\mathrm{PSL}(2, \mathbb{Z})$. -/
theorem modularGeneratorS_sq :
    (modularGeneratorS (R := R)) ^ 2 = -(1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularGeneratorS, Matrix.mul_apply, Fin.sum_univ_two]

/-- $S^4 = I_2$ in $\mathrm{SL}(2, R)$. -/
theorem modularGeneratorS_pow_four :
    (modularGeneratorS (R := R)) ^ 4 = (1 : Matrix (Fin 2) (Fin 2) R) := by
  calc
    (modularGeneratorS (R := R)) ^ 4
      = ((modularGeneratorS (R := R)) ^ 2) ^ 2 := by noncomm_ring
    _ = (-(1 : Matrix (Fin 2) (Fin 2) R)) ^ 2 := by rw [modularGeneratorS_sq]
    _ = (1 : Matrix (Fin 2) (Fin 2) R) := by noncomm_ring

/-- Non-commutativity of the modular generators $S$ and $T$ ($S T \neq T S$): the modular group
action on the torus fiber is strictly non-abelian. -/
theorem modularGeneratorS_mul_T_ne_T_mul_S [Nontrivial R] :
    modularGeneratorS (R := R) * modularGeneratorT (R := R) ≠
      modularGeneratorT (R := R) * modularGeneratorS (R := R) := by
  intro h
  have h00 : (modularGeneratorS (R := R) * modularGeneratorT (R := R)) 0 0 =
      (modularGeneratorT (R := R) * modularGeneratorS (R := R)) 0 0 :=
    congr_fun (congr_fun h 0) 0
  simp only [modularGeneratorS, modularGeneratorT, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, mul_zero, add_zero, zero_add] at h00
  exact zero_ne_one h00

/-- $(S T)^3 = -I_2$ in $\mathrm{SL}(2, R)$, descending to $(ST)^3 = 1$ in
$\mathrm{PSL}(2, \mathbb{Z})$ (De Haro Section 2.2). -/
theorem modularGeneratorST_cubed :
    (modularGeneratorS (R := R) * modularGeneratorT (R := R)) ^ 3 =
      -(1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularGeneratorS, modularGeneratorT, Matrix.mul_apply, Fin.sum_univ_two]

/-- Vertical action of $S$ on a period vector $(a_D, a)^T$ sends $(a_D, a)^T \mapsto (-a, a_D)^T$
within the fiber over a fixed point $u \in \mathcal{M}$ (De Haro Section 3.1.1). -/
theorem periodAction_modularGeneratorS (aD a : R) :
    periodAction (modularGeneratorS (R := R)) ![aD, a] = ![-a, aD] := by
  rw [periodAction_explicit]
  ext i
  fin_cases i <;> simp [modularGeneratorS]

/-- Contragredient action of $S^{-1} = -S$ on a charge vector $(n_m, n_e)$ exchanges electric and
magnetic charges up to sign: $(n_m, n_e) S^{-1} = (-n_e, n_m)$. -/
theorem chargeAction_modularGeneratorS_inv (nm ne : R) :
    chargeAction (-(modularGeneratorS (R := R))) ![nm, ne] = ![-ne, nm] := by
  rw [chargeAction_explicit]
  ext i
  fin_cases i <;> simp [modularGeneratorS]

/-- Effective coupling ratio $\tau(v) = v_0 / v_1 = a_D / a$ of a fiber period vector $v = (a_D, a)^T$. -/
def effectiveCouplingRatio {F : Type*} [Field F] (v : Fin 2 → F) : F :=
  v 0 / v 1

/-- Vertical $S$-duality inverts the effective coupling ratio:
$\tau(S \cdot (a_D, a)^T) = -a / a_D = -(a_D / a)^{-1} = -1/\tau$ (De Haro Section 3.1.1). -/
theorem effectiveCouplingRatio_modularGeneratorS {F : Type*} [Field F] (aD a : F) :
    effectiveCouplingRatio (periodAction (modularGeneratorS (R := F)) ![aD, a]) =
      -(effectiveCouplingRatio ![aD, a])⁻¹ := by
  rw [periodAction_modularGeneratorS]
  dsimp [effectiveCouplingRatio]
  rw [inv_div, neg_div]

end ModularSDuality

/-! ## Section 5: Archetype 4 — Seiberg–Witten $\mathcal{N}=2$ $\mathrm{SU}(2)$ Monodromies -/

section SeibergWittenMonodromy

variable {R : Type*} [Ring R]

/-- Semi-classical monodromy matrix around $u = \infty$ in the Seiberg–Witten $\mathcal{N}=2$
$\mathrm{SU}(2)$ gauge theory (De Haro Appendix A.2, Eq. (7)):
$M_\infty = \begin{pmatrix} -1 & 2 \\ 0 & -1 \end{pmatrix}$. -/
def swMonodromyInf : Matrix (Fin 2) (Fin 2) R :=
  !![-1, 2; 0, -1]

/-- Inverse semi-classical monodromy matrix at $u = \infty$ (De Haro Eq. (9)):
$M_\infty^{-1} = \begin{pmatrix} -1 & -2 \\ 0 & -1 \end{pmatrix}$. -/
def swMonodromyInfInv : Matrix (Fin 2) (Fin 2) R :=
  !![-1, -2; 0, -1]

/-- Strong-coupling magnetic monopole monodromy matrix around $u = \Lambda$ (De Haro Eq. (11)):
$M_\Lambda = \begin{pmatrix} 1 & 0 \\ -2 & 1 \end{pmatrix}$. -/
def swMonodromyPosLambda : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; -2, 1]

/-- Inverse monodromy matrix around $u = \Lambda$:
$M_\Lambda^{-1} = \begin{pmatrix} 1 & 0 \\ 2 & 1 \end{pmatrix}$. -/
def swMonodromyPosLambdaInv : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 2, 1]

/-- Strong-coupling dyon monodromy matrix around $u = -\Lambda$ (De Haro Eq. (12)):
$M_{-\Lambda} = \begin{pmatrix} -1 & 2 \\ -2 & 3 \end{pmatrix}$. -/
def swMonodromyNegLambda : Matrix (Fin 2) (Fin 2) R :=
  !![-1, 2; -2, 3]

/-- Inverse dyon monodromy matrix around $u = -\Lambda$:
$M_{-\Lambda}^{-1} = \begin{pmatrix} 3 & -2 \\ 2 & -1 \end{pmatrix}$. -/
def swMonodromyNegLambdaInv : Matrix (Fin 2) (Fin 2) R :=
  !![3, -2; 2, -1]

/-- $\det M_\infty = 1$. -/
theorem det_swMonodromyInf : det2x2 (swMonodromyInf (R := R)) = 1 := by
  dsimp [det2x2, swMonodromyInf]
  noncomm_ring

/-- $\det M_\Lambda = 1$. -/
theorem det_swMonodromyPosLambda : det2x2 (swMonodromyPosLambda (R := R)) = 1 := by
  dsimp [det2x2, swMonodromyPosLambda]
  noncomm_ring

/-- $\det M_{-\Lambda} = 1$. -/
theorem det_swMonodromyNegLambda : det2x2 (swMonodromyNegLambda (R := R)) = 1 := by
  dsimp [det2x2, swMonodromyNegLambda]
  simp only [← two_add_one_eq_three, ← one_add_one_eq_two]
  noncomm_ring

/-- $M_\infty^{-1} M_\infty = I_2$. -/
theorem swMonodromyInfInv_mul_self :
    swMonodromyInfInv (R := R) * swMonodromyInf (R := R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swMonodromyInfInv, swMonodromyInf, Matrix.mul_apply, Fin.sum_univ_two]

/-- $M_\Lambda^{-1} M_\Lambda = I_2$. -/
theorem swMonodromyPosLambdaInv_mul_self :
    swMonodromyPosLambdaInv (R := R) * swMonodromyPosLambda (R := R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swMonodromyPosLambdaInv, swMonodromyPosLambda, Matrix.mul_apply, Fin.sum_univ_two]

/-- $M_{-\Lambda}^{-1} M_{-\Lambda} = I_2$. -/
theorem swMonodromyNegLambdaInv_mul_self :
    swMonodromyNegLambdaInv (R := R) * swMonodromyNegLambda (R := R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [swMonodromyNegLambdaInv, swMonodromyNegLambda, Matrix.mul_apply, Fin.sum_univ_two];
      try (simp only [← two_add_one_eq_three, ← one_add_one_eq_two]; noncomm_ring))

/-- Topological punctured-sphere monodromy factorization on
$\mathcal{M} = \mathbb{C} \setminus \{\Lambda, -\Lambda\}$: the product of the monodromies around
$u = \Lambda$ and $u = -\Lambda$ equals the monodromy at infinity, $M_\Lambda M_{-\Lambda} = M_\infty$. -/
theorem swMonodromy_punctured_sphere_factorization :
    swMonodromyPosLambda (R := R) * swMonodromyNegLambda (R := R) =
      swMonodromyInf (R := R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [swMonodromyPosLambda, swMonodromyNegLambda, swMonodromyInf,
      Matrix.mul_apply, Fin.sum_univ_two];
      try (simp only [← two_add_one_eq_three, ← one_add_one_eq_two]; noncomm_ring))

/-- Non-commutativity of the strong-coupling Seiberg–Witten monopole and dyon monodromies over
$\mathbb{Z}$ ($M_\Lambda M_{-\Lambda} \neq M_{-\Lambda} M_\Lambda$). -/
theorem swMonodromy_posLambda_negLambda_noncomm :
    swMonodromyPosLambda (R := ℤ) * swMonodromyNegLambda (R := ℤ) ≠
      swMonodromyNegLambda (R := ℤ) * swMonodromyPosLambda (R := ℤ) := by
  intro h
  have h00 : (swMonodromyPosLambda (R := ℤ) * swMonodromyNegLambda (R := ℤ)) 0 0 =
      (swMonodromyNegLambda (R := ℤ) * swMonodromyPosLambda (R := ℤ)) 0 0 :=
    congr_fun (congr_fun h 0) 0
  revert h00
  decide

/-- The semi-classical inverse monodromy at $u = \infty$ is $-T^2$. -/
theorem swMonodromyInfInv_eq_neg_T_sq :
    swMonodromyInfInv (R := R) = -((modularGeneratorT (R := R)) ^ 2) := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [swMonodromyInfInv, modularGeneratorT];
      try (simp only [← one_add_one_eq_two]; abel))

/-- Exact $S$-duality conjugacy between the semi-classical shift $T^2 = -M_\infty^{-1}$ and the
strong-coupling magnetic monopole monodromy $M_\Lambda$: $S T^2 S^{-1} = M_\Lambda$. -/
theorem swMonodromyPosLambda_eq_S_conj_T_sq :
    modularGeneratorS (R := R) * ((modularGeneratorT (R := R)) ^ 2) *
        (-(modularGeneratorS (R := R))) =
      swMonodromyPosLambda (R := R) := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [modularGeneratorS, modularGeneratorT, swMonodromyPosLambda,
      Matrix.mul_apply, Fin.sum_univ_two];
      try (simp only [← one_add_one_eq_two]; abel))

/-- Parabolic Jordan nilpotency at $u = \infty$: $(M_\infty + I_2)^2 = 0$. -/
theorem swMonodromyInf_parabolic_nilpotent :
    (swMonodromyInf (R := R) + 1) ^ 2 = 0 := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swMonodromyInf, Matrix.mul_apply, Fin.sum_univ_two]

/-- Parabolic Jordan nilpotency at $u = \Lambda$: $(M_\Lambda - I_2)^2 = 0$. -/
theorem swMonodromyPosLambda_parabolic_nilpotent :
    (swMonodromyPosLambda (R := R) - 1) ^ 2 = 0 := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swMonodromyPosLambda, Matrix.mul_apply, Fin.sum_univ_two]

/-- Parabolic Jordan nilpotency at $u = -\Lambda$: $(M_{-\Lambda} - I_2)^2 = 0$. -/
theorem swMonodromyNegLambda_parabolic_nilpotent :
    (swMonodromyNegLambda (R := R) - 1) ^ 2 = 0 := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [swMonodromyNegLambda, Matrix.mul_apply, Fin.sum_univ_two];
      try (simp only [← two_add_one_eq_three, ← one_add_one_eq_two]; noncomm_ring))

/-- Charge vector $(1, 0)$ of a pure magnetic monopole (massless at $u = \Lambda$). -/
def pureMagneticMonopoleCharge : Fin 2 → R :=
  ![1, 0]

/-- Charge vector $(0, 1)$ of a pure electric state. -/
def pureElectricCharge : Fin 2 → R :=
  ![0, 1]

/-- Charge vector $(1, -1)$ of the massless dyon at $u = -\Lambda$. -/
def masslessDyonCharge : Fin 2 → R :=
  ![1, -1]

/-- Around $u = \infty$, a pure magnetic monopole $(1, 0)$ acquires electric charge and becomes
the dyon $(-1, -2)$ under $M_\infty^{-1}$ (De Haro Eq. (10)). -/
theorem pureMagneticMonopole_becomes_dyon_at_inf :
    chargeAction (swMonodromyInfInv (R := R)) (pureMagneticMonopoleCharge (R := R)) =
      ![-1, -2] := by
  rw [chargeAction_explicit]
  ext i
  fin_cases i <;> simp [pureMagneticMonopoleCharge, swMonodromyInfInv]

/-- Around $u = \Lambda$, the pure magnetic monopole $(1, 0)$ is a fixed left eigenvector of
$M_\Lambda^{-1}$ with eigenvalue $+1$ (massless BPS monopole at $a_D(\Lambda) = 0$). -/
theorem pureMagneticMonopole_fixed_at_posLambda :
    chargeAction (swMonodromyPosLambdaInv (R := R)) (pureMagneticMonopoleCharge (R := R)) =
      pureMagneticMonopoleCharge (R := R) := by
  rw [chargeAction_explicit]
  ext i
  fin_cases i <;> simp [pureMagneticMonopoleCharge, swMonodromyPosLambdaInv]

/-- Around $u = \Lambda$, a pure electric state $(0, 1)$ acquires magnetic charge and becomes
the dyon $(2, 1)$ under $M_\Lambda^{-1}$ (De Haro Appendix A.2, p. 31). -/
theorem pureElectric_acquires_magnetic_charge_at_posLambda :
    chargeAction (swMonodromyPosLambdaInv (R := R)) (pureElectricCharge (R := R)) =
      ![2, 1] := by
  rw [chargeAction_explicit]
  ext i
  fin_cases i <;> simp [pureElectricCharge, swMonodromyPosLambdaInv]

/-- Around $u = -\Lambda$, the $(1, -1)$ dyon is a fixed left eigenvector of $M_{-\Lambda}^{-1}$
with eigenvalue $+1$ (massless BPS dyon at $a_D(-\Lambda) = a(-\Lambda)$). -/
theorem masslessDyon_fixed_at_negLambda :
    chargeAction (swMonodromyNegLambdaInv (R := R)) (masslessDyonCharge (R := R)) =
      masslessDyonCharge (R := R) := by
  rw [chargeAction_explicit]
  ext i
  fin_cases i <;>
    (simp [masslessDyonCharge, swMonodromyNegLambdaInv];
      try (simp only [← two_add_one_eq_three, ← one_add_one_eq_two]; abel))

/-- Exact invariance of the Seiberg–Witten central charge $Z = n_m a_D + n_e a$ under all three
Coulomb-branch monodromies $M_\infty, M_\Lambda, M_{-\Lambda}$ (De Haro Appendix A.2). -/
theorem centralChargePairing_invariant_all_swMonodromies (q v : Fin 2 → R) :
    centralChargePairing (chargeAction (swMonodromyInfInv (R := R)) q)
        (periodAction (swMonodromyInf (R := R)) v) = centralChargePairing q v ∧
      centralChargePairing (chargeAction (swMonodromyPosLambdaInv (R := R)) q)
        (periodAction (swMonodromyPosLambda (R := R)) v) = centralChargePairing q v ∧
      centralChargePairing (chargeAction (swMonodromyNegLambdaInv (R := R)) q)
        (periodAction (swMonodromyNegLambda (R := R)) v) = centralChargePairing q v := by
  refine ⟨?_, ?_, ?_⟩
  · exact centralChargePairing_contragredient_invariance
      (swMonodromyInf (R := R)) (swMonodromyInfInv (R := R)) swMonodromyInfInv_mul_self q v
  · exact centralChargePairing_contragredient_invariance
      (swMonodromyPosLambda (R := R)) (swMonodromyPosLambdaInv (R := R))
      swMonodromyPosLambdaInv_mul_self q v
  · exact centralChargePairing_contragredient_invariance
      (swMonodromyNegLambda (R := R)) (swMonodromyNegLambdaInv (R := R))
      swMonodromyNegLambdaInv_mul_self q v

/-- Mod-2 $\Gamma(2)$ congruence obstruction: over $\mathbb{Z}/2\mathbb{Z}$, all three global
Seiberg–Witten monodromy generators $M_\infty, M_\Lambda, M_{-\Lambda}$ reduce to the identity
matrix $I_2$, whereas the $S$-duality generator $S$ does not ($S \not\equiv I_2 \pmod 2$).
Consequently, $S$-duality lies outside the global monodromy group $\Gamma(2)$ and is strictly a
local vertical quasi-duality between chart trivializations (De Haro Section 3.1.1 & Appendix A.2). -/
theorem swMonodromy_mod_two_congruence_and_S_obstruction :
    swMonodromyInf (R := ZMod 2) = 1 ∧
      swMonodromyPosLambda (R := ZMod 2) = 1 ∧
      swMonodromyNegLambda (R := ZMod 2) = 1 ∧
      modularGeneratorS (R := ZMod 2) ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · intro hS
    have h00 : modularGeneratorS (R := ZMod 2) 0 0 = (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 :=
      congr_fun (congr_fun hS 0) 0
    revert h00
    decide

end SeibergWittenMonodromy

/-! ## Section 6: Archetype 5 — Symplectic & Kähler Compatibility of the Model Fiber -/

section SymplecticKahlerFiber

variable {R : Type*} [Ring R]

/-- Operator commutator $[x, y] = x y - y x$ in an arbitrary ring $R$. -/
def opComm (x y : R) : R :=
  x * y - y * x

/-- The canonical symplectic bilinear form $\omega(v, w) = v_0 w_1 - v_1 w_0$ on the
Seiberg–Witten period fiber (De Haro Appendix A.3–A.4, Eq. (16)). -/
def canonicalSymplecticForm (v w : Fin 2 → R) : R :=
  v 0 * w 1 - v 1 * w 0

/-- Over a non-commutative ring $R$, the self-pairing $\omega(v, v) = v_0 v_1 - v_1 v_0$ equals
the operator commutator $[v_0, v_1]$. -/
theorem canonicalSymplecticForm_alternating (v : Fin 2 → R) :
    canonicalSymplecticForm v v = opComm (v 0) (v 1) := by
  dsimp [canonicalSymplecticForm, opComm]

/-- Over a non-commutative ring $R$, the symplectic form satisfies skew-symmetry up to the
commutator defect $[v_0, w_1] - [v_1, w_0]$. -/
theorem canonicalSymplecticForm_skew (v w : Fin 2 → R) :
    canonicalSymplecticForm v w =
      -canonicalSymplecticForm w v + opComm (v 0) (w 1) - opComm (v 1) (w 0) := by
  dsimp [canonicalSymplecticForm, opComm]
  noncomm_ring

/-- Every modular & Seiberg–Witten generator ($S$, $T$, $M_\infty$, $M_\Lambda$, and $M_{-\Lambda}$)
preserves the fiber symplectic structure $\omega(v, w) = v_0 w_1 - v_1 w_0$ identically over an
arbitrary non-commutative ring `[Ring R]` with zero commutator anomaly. -/
theorem canonicalSymplecticForm_modular_and_swMonodromy_invariant (v w : Fin 2 → R) :
    canonicalSymplecticForm (periodAction (modularGeneratorS (R := R)) v)
        (periodAction (modularGeneratorS (R := R)) w) = canonicalSymplecticForm v w ∧
      canonicalSymplecticForm (periodAction (modularGeneratorT (R := R)) v)
        (periodAction (modularGeneratorT (R := R)) w) = canonicalSymplecticForm v w ∧
      canonicalSymplecticForm (periodAction (swMonodromyInf (R := R)) v)
        (periodAction (swMonodromyInf (R := R)) w) = canonicalSymplecticForm v w ∧
      canonicalSymplecticForm (periodAction (swMonodromyPosLambda (R := R)) v)
        (periodAction (swMonodromyPosLambda (R := R)) w) = canonicalSymplecticForm v w ∧
      canonicalSymplecticForm (periodAction (swMonodromyNegLambda (R := R)) v)
        (periodAction (swMonodromyNegLambda (R := R)) w) = canonicalSymplecticForm v w := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [periodAction_explicit, periodAction_explicit];
      dsimp [canonicalSymplecticForm, modularGeneratorS, modularGeneratorT,
        swMonodromyInf, swMonodromyPosLambda, swMonodromyNegLambda];
      noncomm_ring)

/-- The Kähler metric $g(v, w) = \omega(v, S w)$ induced on the fiber by compatibility of the
symplectic form $\omega$ with the complex-structure operator $S$ ($S^2 = -I_2$). -/
def canonicalKahlerMetric (v w : Fin 2 → R) : R :=
  canonicalSymplecticForm v (periodAction (modularGeneratorS (R := R)) w)

/-- Explicit Euclidean evaluation of the Kähler metric: $g(v, w) = v_0 w_0 + v_1 w_1$. -/
theorem canonicalKahlerMetric_explicit (v w : Fin 2 → R) :
    canonicalKahlerMetric v w = v 0 * w 0 + v 1 * w 1 := by
  dsimp [canonicalKahlerMetric, canonicalSymplecticForm]
  rw [periodAction_explicit]
  dsimp [modularGeneratorS]
  noncomm_ring

/-- Over an arbitrary non-commutative ring `[Ring R]`, the Kähler metric $g(v, w) = \omega(v, S w)$
is strictly $S$-invariant ($g(S v, S w) = g(v, w)$) and symmetric up to the commutator anomaly
$[v_0, w_0] + [v_1, w_1]$. -/
theorem canonicalKahlerMetric_symm_and_S_isometry (v w : Fin 2 → R) :
    canonicalKahlerMetric v w =
        canonicalKahlerMetric w v + opComm (v 0) (w 0) + opComm (v 1) (w 1) ∧
      canonicalKahlerMetric (periodAction (modularGeneratorS (R := R)) v)
        (periodAction (modularGeneratorS (R := R)) w) = canonicalKahlerMetric v w := by
  constructor
  · rw [canonicalKahlerMetric_explicit, canonicalKahlerMetric_explicit]
    dsimp [opComm]
    noncomm_ring
  · rw [canonicalKahlerMetric_explicit, canonicalKahlerMetric_explicit,
      periodAction_explicit, periodAction_explicit]
    dsimp [modularGeneratorS]
    noncomm_ring

end SymplecticKahlerFiber

/-! ## Section 7: Archetype 6 — Wheeler–DeWitt Asymptotic de Sitter Holographic Cumulants -/

section WheelerDeWittHolography

variable {R : Type*} [Ring R] [Invertible (2 : R)]

/-- Second-order formal expansion in $\kappa = 8\pi G_N$ of the asymptotic de Sitter CFT partition
function $Z(\kappa) = \exp(\kappa \mathcal{G}_1 + \kappa^2 \mathcal{G}_2 + O(\kappa^3))$ appearing
in the Wheeler–DeWitt wave-functional $\Psi[g] = e^{i S[g]} Z[g]$ (De Haro Appendix B, Eqs. (17)–(20)):
$Z_2(\kappa) = 1 + \kappa \mathcal{G}_1 + \kappa^2 (\mathcal{G}_2 + \tfrac{1}{2} \mathcal{G}_1^2)$. -/
def holographicPartitionSecondOrder (G₁ G₂ κ : R) : R :=
  1 + κ * G₁ + κ ^ 2 * (G₂ + ⅟(2 : R) * G₁ ^ 2)

/-- Connected 2-point CFT stress-energy correlator (second cumulant) $\mathcal{G}_2 = M_2 - \tfrac{1}{2} M_1^2$
extracted from the first and second partition-function moments $M_1, M_2$ (De Haro Eq. (20)). -/
def connectedTwoPointFromMoments (M₁ M₂ : R) : R :=
  M₂ - ⅟(2 : R) * M₁ ^ 2

/-- At zero gravitational coupling $\kappa = 0$, the normalized holographic partition expansion
equals $1$. -/
theorem holographicPartitionSecondOrder_zero (G₁ G₂ : R) :
    holographicPartitionSecondOrder G₁ G₂ (0 : R) = 1 := by
  dsimp [holographicPartitionSecondOrder]
  noncomm_ring

/-- The cumulant extraction formula recovers the connected 2-point CFT stress-energy functional
$\mathcal{G}_2$ from the second-order coefficient $M_2 = \mathcal{G}_2 + \tfrac{1}{2} \mathcal{G}_1^2$
of $Z_2(\kappa)$. -/
theorem connectedTwoPointFromMoments_recovers_cumulant (G₁ G₂ : R) :
    connectedTwoPointFromMoments G₁ (G₂ + ⅟(2 : R) * G₁ ^ 2) = G₂ := by
  dsimp [connectedTwoPointFromMoments]
  noncomm_ring

/-- Non-commutative linked-cluster expansion at unit coupling $\kappa = 1$ over `[Ring R]`:
multiplying two second-order holographic partition expansions $Z_2(\mathcal{G}_1, \mathcal{G}_2; 1)$
and $Z_2(\mathcal{H}_1, \mathcal{H}_2; 1)$ differs from the sum expansion
$Z_2(\mathcal{G}_1 + \mathcal{H}_1, \mathcal{G}_2 + \mathcal{H}_2; 1)$ by the second-order
non-commutative ordering defect $\mathcal{G}_1 \mathcal{H}_1 - \tfrac{1}{2}(\mathcal{G}_1 \mathcal{H}_1 + \mathcal{H}_1 \mathcal{G}_1) = \tfrac{1}{2}[\mathcal{G}_1, \mathcal{H}_1]$
plus the cubic and quartic cumulant cross-terms. -/
theorem holographicPartitionSecondOrder_linked_cluster
    (G₁ G₂ H₁ H₂ : R) :
    holographicPartitionSecondOrder G₁ G₂ 1 * holographicPartitionSecondOrder H₁ H₂ 1 -
        holographicPartitionSecondOrder (G₁ + H₁) (G₂ + H₂) 1 =
      (G₁ * H₁ - ⅟(2 : R) * (G₁ * H₁ + H₁ * G₁)) +
        (G₁ * (H₂ + ⅟(2 : R) * H₁ ^ 2) + (G₂ + ⅟(2 : R) * G₁ ^ 2) * H₁) +
        (G₂ + ⅟(2 : R) * G₁ ^ 2) * (H₂ + ⅟(2 : R) * H₁ ^ 2) := by
  dsimp [holographicPartitionSecondOrder]
  noncomm_ring

end WheelerDeWittHolography

section WheelerDeWittLinearity

variable {R W : Type*} [Ring R] [AddCommGroup W] [Module R W]

/-- The vector subspace of Wheeler–DeWitt physical wave-functionals $\ker \mathcal{H}_{\mathrm{WDW}}$
annihilated by the linear Wheeler–DeWitt Hamiltonian constraint operator
$\mathcal{H}_{\mathrm{WDW}} : W \to_R W$ (De Haro Appendix B, p. 33). -/
def wheelerDeWittSolutionSubmodule (H_wdw : W →ₗ[R] W) : Submodule R W :=
  LinearMap.ker H_wdw

/-- Linear superposition of Wheeler–DeWitt solutions: any $R$-linear combination
$c_1 \Psi_1 + c_2 \Psi_2$ of physical wave-functionals satisfying $\mathcal{H}_{\mathrm{WDW}} \Psi_i = 0$
again satisfies the Wheeler–DeWitt constraint $\mathcal{H}_{\mathrm{WDW}}(c_1 \Psi_1 + c_2 \Psi_2) = 0$. -/
theorem wheelerDeWitt_superposition_closed
    (H_wdw : W →ₗ[R] W) (c₁ c₂ : R) (Ψ₁ Ψ₂ : W)
    (h₁ : Ψ₁ ∈ wheelerDeWittSolutionSubmodule H_wdw)
    (h₂ : Ψ₂ ∈ wheelerDeWittSolutionSubmodule H_wdw) :
    c₁ • Ψ₁ + c₂ • Ψ₂ ∈ wheelerDeWittSolutionSubmodule H_wdw := by
  unfold wheelerDeWittSolutionSubmodule at h₁ h₂ ⊢
  exact Submodule.add_mem _ (Submodule.smul_mem _ c₁ h₁) (Submodule.smul_mem _ c₂ h₂)

end WheelerDeWittLinearity

/-! ## Section 8: Archetype 7 — Non-Commutative `[Ring B]` Realization of the Model Bundle &
  5-Graded Parabolic "Theory of Theories" -/

section NonCommutativeRingModelBundle

variable {B : Type*} [Ring B]

/-- The modular dilation / grading generator $H = P_1 - P_2$ associated with a three-horizon
projective frame $1 = P_1 + P_0 + P_2$ ($P_1 = \infty$, $P_0 = 1$ [waist], $P_2 = 0$). -/
def modularDilation (P₁ P₂ : B) : B :=
  P₁ - P₂

/-- For orthogonal idempotents $P_1, P_2 \in B$, the square of the modular dilation $H = P_1 - P_2$
is the horizon sum $H^2 = P_1 + P_2$. -/
theorem modularDilation_sq
    (P₁ P₂ : B) (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) :
    (modularDilation P₁ P₂) ^ 2 = P₁ + P₂ := by
  dsimp [modularDilation]
  calc
    (P₁ - P₂) ^ 2
      = P₁ * P₁ - P₁ * P₂ - P₂ * P₁ + P₂ * P₂ := by noncomm_ring
    _ = P₁ - 0 - 0 + P₂ := by rw [h1, h12, h21, h2]
    _ = P₁ + P₂ := by noncomm_ring

/-- Cubic tripotent law $H^3 = H$ of the modular dilation $H = P_1 - P_2$ over orthogonal
idempotents $P_1, P_2 \in B$. -/
theorem modularDilation_cubed_eq_self
    (P₁ P₂ : B) (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) :
    (modularDilation P₁ P₂) ^ 3 = modularDilation P₁ P₂ := by
  have hsq : (modularDilation P₁ P₂) ^ 2 = P₁ + P₂ :=
    modularDilation_sq P₁ P₂ h1 h2 h12 h21
  calc
    (modularDilation P₁ P₂) ^ 3
      = (modularDilation P₁ P₂) ^ 2 * modularDilation P₁ P₂ := by noncomm_ring
    _ = (P₁ + P₂) * (P₁ - P₂) := by rw [hsq]; rfl
    _ = P₁ * P₁ - P₁ * P₂ + P₂ * P₁ - P₂ * P₂ := by noncomm_ring
    _ = P₁ - 0 + 0 - P₂ := by rw [h1, h12, h21, h2]
    _ = modularDilation P₁ P₂ := by
        dsimp [modularDilation]
        noncomm_ring

/-- Off-diagonal positive boundary jump (local quasi-duality transition) $N_+ = P_1 X P_0$
connecting the waist condensate $P_0$ to the source horizon $P_1$. -/
def quasiDualityJumpPlus (P₁ P₀ X : B) : B :=
  P₁ * X * P₀

/-- Off-diagonal negative boundary jump (local quasi-duality transition) $N_- = P_0 Y P_2$
connecting the sink horizon $P_2$ to the waist condensate $P_0$. -/
def quasiDualityJumpMinus (P₀ P₂ Y : B) : B :=
  P₀ * Y * P₂

/-- Square-zero nilpotency $N_+^2 = 0$ of the local quasi-duality jump $N_+ = P_1 X P_0$. -/
theorem quasiDualityJumpPlus_sq_zero
    (P₁ P₀ X : B) (h01 : P₀ * P₁ = 0) :
    (quasiDualityJumpPlus P₁ P₀ X) ^ 2 = 0 := by
  dsimp [quasiDualityJumpPlus]
  calc
    (P₁ * X * P₀) ^ 2
      = P₁ * X * (P₀ * P₁) * X * P₀ := by noncomm_ring
    _ = P₁ * X * 0 * X * P₀ := by rw [h01]
    _ = 0 := by noncomm_ring

/-- Square-zero nilpotency $N_-^2 = 0$ of the local quasi-duality jump $N_- = P_0 Y P_2$. -/
theorem quasiDualityJumpMinus_sq_zero
    (P₀ P₂ Y : B) (h20 : P₂ * P₀ = 0) :
    (quasiDualityJumpMinus P₀ P₂ Y) ^ 2 = 0 := by
  dsimp [quasiDualityJumpMinus]
  calc
    (P₀ * Y * P₂) ^ 2
      = P₀ * Y * (P₂ * P₀) * Y * P₂ := by noncomm_ring
    _ = P₀ * Y * 0 * Y * P₂ := by rw [h20]
    _ = 0 := by noncomm_ring

/-- Two-step quasi-duality transition across the waist $P_0$: composing $N_+ = P_1 X P_0$ and
$N_- = P_0 Y P_2$ produces a grade-$+2$ source-to-sink transport $P_1 (X P_0 Y) P_2$. -/
theorem quasiDualityJump_two_step_composition
    (P₁ P₀ P₂ X Y : B) (h0 : P₀ * P₀ = P₀) :
    quasiDualityJumpPlus P₁ P₀ X * quasiDualityJumpMinus P₀ P₂ Y =
      P₁ * (X * P₀ * Y) * P₂ := by
  dsimp [quasiDualityJumpPlus, quasiDualityJumpMinus]
  calc
    (P₁ * X * P₀) * (P₀ * Y * P₂)
      = P₁ * X * (P₀ * P₀) * Y * P₂ := by noncomm_ring
    _ = P₁ * X * P₀ * Y * P₂ := by rw [h0]
    _ = P₁ * (X * P₀ * Y) * P₂ := by noncomm_ring

/-- Parity reflection / exact duality involution $S_{\mathrm{par}} = 1 - 2 P_0$ across the waist
projector $P_0$. -/
def parityInversionOperator (P₀ : B) : B :=
  1 - 2 * P₀

/-- Under the 3-horizon decomposition $P_1 + P_0 + P_2 = 1$, the parity reflection operator
$S_{\mathrm{par}} = 1 - 2 P_0$ equals $2 H^2 - 1$. -/
theorem parityInversionOperator_eq_two_modularDilation_sq_sub_one
    (P₁ P₀ P₂ : B) (hSum : P₁ + P₀ + P₂ = 1)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) :
    2 * (modularDilation P₁ P₂) ^ 2 - 1 = parityInversionOperator P₀ := by
  rw [modularDilation_sq P₁ P₂ h1 h2 h12 h21]
  dsimp [parityInversionOperator]
  have hP12 : P₁ + P₂ = 1 - P₀ := by
    calc
      P₁ + P₂ = (P₁ + P₀ + P₂) - P₀ := by noncomm_ring
      _ = 1 - P₀ := by rw [hSum]
  calc
    2 * (P₁ + P₂) - 1 = 2 * (1 - P₀) - 1 := by rw [hP12]
    _ = 1 - 2 * P₀ := by noncomm_ring

/-- Exact involution property $S_{\mathrm{par}}^2 = 1$ of the parity reflection operator for any
idempotent waist projector $P_0^2 = P_0$. -/
theorem parityInversionOperator_sq_eq_one
    (P₀ : B) (h0 : P₀ * P₀ = P₀) :
    (parityInversionOperator P₀) ^ 2 = 1 := by
  dsimp [parityInversionOperator]
  calc
    (1 - 2 * P₀) ^ 2
      = 1 - 4 * P₀ + 4 * (P₀ * P₀) := by noncomm_ring
    _ = 1 - 4 * P₀ + 4 * P₀ := by rw [h0]
    _ = 1 := by noncomm_ring

/-- Exact duality invariance of an on-leaf fiber model $V = P_1 X P_1$: conjugating by
$S_{\mathrm{par}} = 1 - 2 P_0$ leaves every diagonal fiber operator invariant,
$S_{\mathrm{par}} (P_1 X P_1) S_{\mathrm{par}} = P_1 X P_1$. -/
theorem parityInversionOperator_preserves_fiber_corner
    (P₁ P₀ X : B) (h10 : P₁ * P₀ = 0) (h01 : P₀ * P₁ = 0) :
    parityInversionOperator P₀ * (P₁ * X * P₁) * parityInversionOperator P₀ =
      P₁ * X * P₁ := by
  dsimp [parityInversionOperator]
  calc
    (1 - 2 * P₀) * (P₁ * X * P₁) * (1 - 2 * P₀)
      = P₁ * X * P₁ - 2 * (P₀ * P₁) * X * P₁ - 2 * P₁ * X * (P₁ * P₀) +
          4 * (P₀ * P₁) * X * (P₁ * P₀) := by noncomm_ring
    _ = P₁ * X * P₁ - 2 * 0 * X * P₁ - 2 * P₁ * X * 0 + 4 * 0 * X * 0 := by
        rw [h01, h10]
    _ = P₁ * X * P₁ := by noncomm_ring

/-- Odd parity transformation of a cross-leaf quasi-duality jump $N_+ = P_1 X P_0$: conjugating by
$S_{\mathrm{par}} = 1 - 2 P_0$ reverses the sign of $N_+$,
$S_{\mathrm{par}} N_+ S_{\mathrm{par}} = -N_+$. -/
theorem parityInversionOperator_negates_quasiDualityJumpPlus
    (P₁ P₀ X : B) (h0 : P₀ * P₀ = P₀) (h01 : P₀ * P₁ = 0) :
    parityInversionOperator P₀ * quasiDualityJumpPlus P₁ P₀ X * parityInversionOperator P₀ =
      -quasiDualityJumpPlus P₁ P₀ X := by
  dsimp [parityInversionOperator, quasiDualityJumpPlus]
  calc
    (1 - 2 * P₀) * (P₁ * X * P₀) * (1 - 2 * P₀)
      = P₁ * X * P₀ - 2 * P₁ * X * (P₀ * P₀) - 2 * (P₀ * P₁) * X * P₀ +
          4 * (P₀ * P₁) * X * (P₀ * P₀) := by noncomm_ring
    _ = P₁ * X * P₀ - 2 * P₁ * X * P₀ - 2 * 0 * X * P₀ + 4 * 0 * X * P₀ := by
        rw [h0, h01]
    _ = -(P₁ * X * P₀) := by noncomm_ring

/-- Grade $-2$ component $\mathcal{G}_{-2}(X) = P_2 X P_1$ of the 5-graded parabolic tower. -/
def parabolicGradeNegTwo (P₁ P₂ X : B) : B :=
  P₂ * X * P₁

/-- Grade $-1$ component $\mathcal{G}_{-1}(X) = P_0 X P_1 + P_2 X P_0$ of the 5-graded parabolic tower. -/
def parabolicGradeNegOne (P₁ P₀ P₂ X : B) : B :=
  P₀ * X * P₁ + P₂ * X * P₀

/-- Grade $0$ component $\mathcal{G}_0(X) = P_1 X P_1 + P_0 X P_0 + P_2 X P_2$ (direct sum of the
three model fibers) of the 5-graded parabolic tower. -/
def parabolicGradeZero (P₁ P₀ P₂ X : B) : B :=
  P₁ * X * P₁ + P₀ * X * P₀ + P₂ * X * P₂

/-- Grade $+1$ component $\mathcal{G}_{+1}(X) = P_1 X P_0 + P_0 X P_2$ (local quasi-duality jumps)
of the 5-graded parabolic tower. -/
def parabolicGradePosOne (P₁ P₀ P₂ X : B) : B :=
  P₁ * X * P₀ + P₀ * X * P₂

/-- Grade $+2$ component $\mathcal{G}_{+2}(X) = P_1 X P_2$ of the 5-graded parabolic tower. -/
def parabolicGradePosTwo (P₁ P₂ X : B) : B :=
  P₁ * X * P₂

/-- Completeness of the 5-Graded Parabolic "Theory of Theories" Tower
$\mathcal{G} = \mathcal{G}_{-2} \oplus \mathcal{G}_{-1} \oplus \mathcal{G}_0 \oplus \mathcal{G}_{+1} \oplus \mathcal{G}_{+2}$:
for any three-horizon partition of unity $P_1 + P_0 + P_2 = 1$, every operator $X \in B$
decomposes canonically as the sum of its five parabolic grades. -/
theorem parabolicFiveGradedTower_decomposition
    (P₁ P₀ P₂ X : B) (hSum : P₁ + P₀ + P₂ = 1) :
    parabolicGradeNegTwo P₁ P₂ X + parabolicGradeNegOne P₁ P₀ P₂ X +
        parabolicGradeZero P₁ P₀ P₂ X + parabolicGradePosOne P₁ P₀ P₂ X +
        parabolicGradePosTwo P₁ P₂ X = X := by
  dsimp [parabolicGradeNegTwo, parabolicGradeNegOne, parabolicGradeZero,
    parabolicGradePosOne, parabolicGradePosTwo]
  calc
    P₂ * X * P₁ + (P₀ * X * P₁ + P₂ * X * P₀) +
        (P₁ * X * P₁ + P₀ * X * P₀ + P₂ * X * P₂) +
        (P₁ * X * P₀ + P₀ * X * P₂) + P₁ * X * P₂
      = (P₁ + P₀ + P₂) * X * (P₁ + P₀ + P₂) := by noncomm_ring
    _ = 1 * X * 1 := by rw [hSum]
    _ = X := by noncomm_ring

/-- Associative ring commutator $[A, X] = A X - X A$. -/
def ringCommutator (A X : B) : B :=
  A * X - X * A

/-- Exact $\mathrm{ad}_H$ eigenvalue laws on the 5-graded parabolic tower: under commutator with
the modular dilation $H = P_1 - P_2$, the fiber diagonal $\mathcal{G}_0(X)$ has grade $0$, the
local quasi-duality jumps $\mathcal{G}_{+1}(X)$ have grade $+1$, and the source-to-sink transport
$\mathcal{G}_{+2}(X)$ has grade $+2$. -/
theorem parabolicGrade_ad_modularDilation_eigenvalues
    (P₁ P₀ P₂ X : B)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h10 : P₁ * P₀ = 0) (h01 : P₀ * P₁ = 0)
    (h20 : P₂ * P₀ = 0) (h02 : P₀ * P₂ = 0)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) :
    ringCommutator (modularDilation P₁ P₂) (parabolicGradeZero P₁ P₀ P₂ X) = 0 ∧
      ringCommutator (modularDilation P₁ P₂) (parabolicGradePosOne P₁ P₀ P₂ X) =
        parabolicGradePosOne P₁ P₀ P₂ X ∧
      ringCommutator (modularDilation P₁ P₂) (parabolicGradePosTwo P₁ P₂ X) =
        2 * parabolicGradePosTwo P₁ P₂ X := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [ringCommutator, modularDilation, parabolicGradeZero]
    calc
      (P₁ - P₂) * (P₁ * X * P₁ + P₀ * X * P₀ + P₂ * X * P₂) -
          (P₁ * X * P₁ + P₀ * X * P₀ + P₂ * X * P₂) * (P₁ - P₂)
        = (P₁ * P₁) * X * P₁ - P₁ * X * (P₁ * P₁) +
            (P₁ * P₀) * X * P₀ - P₀ * X * (P₀ * P₁) +
            (P₁ * P₂) * X * P₂ + P₂ * X * (P₂ * P₂) -
            (P₂ * P₁) * X * P₁ - (P₂ * P₀) * X * P₀ -
            (P₂ * P₂) * X * P₂ + P₁ * X * (P₁ * P₂) +
            P₀ * X * (P₀ * P₂) - P₂ * X * (P₂ * P₁) := by noncomm_ring
      _ = P₁ * X * P₁ - P₁ * X * P₁ + 0 * X * P₀ - P₀ * X * 0 +
            0 * X * P₂ + P₂ * X * P₂ - 0 * X * P₁ - 0 * X * P₀ -
            P₂ * X * P₂ + P₁ * X * 0 + P₀ * X * 0 - P₂ * X * 0 := by
          rw [h1, h2, h10, h01, h12, h21, h20, h02]
      _ = 0 := by noncomm_ring
  · dsimp [ringCommutator, modularDilation, parabolicGradePosOne]
    calc
      (P₁ - P₂) * (P₁ * X * P₀ + P₀ * X * P₂) -
          (P₁ * X * P₀ + P₀ * X * P₂) * (P₁ - P₂)
        = (P₁ * P₁) * X * P₀ + (P₁ * P₀) * X * P₂ -
            (P₂ * P₁) * X * P₀ - (P₂ * P₀) * X * P₂ -
            P₁ * X * (P₀ * P₁) + P₁ * X * (P₀ * P₂) -
            P₀ * X * (P₂ * P₁) + P₀ * X * (P₂ * P₂) := by noncomm_ring
      _ = P₁ * X * P₀ + 0 * X * P₂ - 0 * X * P₀ - 0 * X * P₂ -
            P₁ * X * 0 + P₁ * X * 0 - P₀ * X * 0 + P₀ * X * P₂ := by
          rw [h1, h2, h10, h01, h20, h02, h21]
      _ = P₁ * X * P₀ + P₀ * X * P₂ := by noncomm_ring
  · dsimp [ringCommutator, modularDilation, parabolicGradePosTwo]
    calc
      (P₁ - P₂) * (P₁ * X * P₂) - (P₁ * X * P₂) * (P₁ - P₂)
        = (P₁ * P₁) * X * P₂ - (P₂ * P₁) * X * P₂ -
            P₁ * X * (P₂ * P₁) + P₁ * X * (P₂ * P₂) := by noncomm_ring
      _ = P₁ * X * P₂ - 0 * X * P₂ - P₁ * X * 0 + P₁ * X * P₂ := by
          rw [h1, h2, h21]
      _ = 2 * (P₁ * X * P₂) := by noncomm_ring

/-- Maurer–Cartan curvature operator $\mathcal{F}_Q(\theta_L) = D_Q(\theta_L) + \theta_L^2$
associated with an odd differential $Q \in B$ ($D_Q(\theta_L) = Q \theta_L + \theta_L Q$) and a
connection 1-form $\theta_L \in B$. -/
def maurerCartanCurvature (Q θ : B) : B :=
  (Q * θ + θ * Q) + θ ^ 2

/-- Algebraic factorization of the Maurer–Cartan curvature:
$D_Q(\theta_L) + \theta_L^2 = (Q + \theta_L)^2 - Q^2$. -/
theorem maurerCartanCurvature_eq_deformed_sq_sub_sq (Q θ : B) :
    maurerCartanCurvature Q θ = (Q + θ) ^ 2 - Q ^ 2 := by
  dsimp [maurerCartanCurvature]
  noncomm_ring

/-- Maurer–Cartan structural flatness theorem: for any square-zero differential $Q^2 = 0$, the
Maurer–Cartan equation $D_Q(\theta_L) + \theta_L^2 = 0$ holds if and only if the deformed
connection operator $Q + \theta_L$ is square-zero, $(Q + \theta_L)^2 = 0$. -/
theorem maurerCartanCurvature_flat_iff_deformed_sq_zero
    (Q θ : B) (hQ : Q ^ 2 = 0) :
    maurerCartanCurvature Q θ = 0 ↔ (Q + θ) ^ 2 = 0 := by
  rw [maurerCartanCurvature_eq_deformed_sq_sub_sq, hQ, sub_zero]

/-- Brockett double-commutator dissipation operator
$\mathcal{L}_{\mathrm{irr}}(\Phi, J) = -[\Phi, [\Phi, J]]$ in the non-commutative ring $B$. -/
def brockettDoubleCommutator (Φ J : B) : B :=
  -ringCommutator Φ (ringCommutator Φ J)

/-- Explicit expansion of the Brockett double commutator:
$\mathcal{L}_{\mathrm{irr}}(\Phi, J) = -\Phi^2 J + 2 \Phi J \Phi - J \Phi^2$. -/
theorem brockettDoubleCommutator_expansion (Φ J : B) :
    brockettDoubleCommutator Φ J = -(Φ ^ 2 * J) + 2 * (Φ * J * Φ) - J * Φ ^ 2 := by
  dsimp [brockettDoubleCommutator, ringCommutator]
  noncomm_ring

/-- Internal vs. External Interpretation Split (De Haro Section 4): for any idempotent horizon
projector $P^2 = P$, the negative Brockett double commutator $-[P, [P, J]]$ vanishes identically on
any internal fiber model $J = P X P$ and acts as the exact negative projection onto the external
off-diagonal quasi-duality jumps $P J (1 - P) + (1 - P) J P$. -/
theorem brockettDoubleCommutator_internal_vs_external_split
    (P X J : B) (hP : P * P = P) :
    brockettDoubleCommutator P (P * X * P) = 0 ∧
      brockettDoubleCommutator P J = -(P * J * (1 - P) + (1 - P) * J * P) := by
  have hP2 : P ^ 2 = P := by
    rw [sq, hP]
  constructor
  · rw [brockettDoubleCommutator_expansion, hP2]
    calc
      -(P * (P * X * P)) + 2 * (P * (P * X * P) * P) - (P * X * P) * P
        = -((P * P) * X * P) + 2 * ((P * P) * X * (P * P)) - P * X * (P * P) := by noncomm_ring
      _ = -(P * X * P) + 2 * (P * X * P) - P * X * P := by rw [hP]
      _ = 0 := by noncomm_ring
  · rw [brockettDoubleCommutator_expansion, hP2]
    noncomm_ring

/-- Structural Realism & Cyclic Trace Invariance of the Common Core: for any additive functional
$\tau : B \to A$ satisfying cyclic trace symmetry $\tau(X Y) = \tau(Y X)$, the expectation value of
any commutator $[V, P]$ vanishes identically ($\tau([V, P]) = 0$) and $\tau$ is invariant under any
invertible duality conjugation $X \mapsto g X g^{-1}$ ($g^{-1} g = 1$). -/
theorem commonCore_trace_invariance_of_commutator_and_duality
    {A : Type*} [AddCommGroup A] (τ : B →+ A)
    (hCyclic : ∀ x y : B, τ (x * y) = τ (y * x))
    (V P g ginv X : B) (hInv : ginv * g = 1) :
    τ (ringCommutator V P) = 0 ∧ τ (g * X * ginv) = τ X := by
  constructor
  · dsimp [ringCommutator]
    rw [map_sub, hCyclic V P, sub_self]
  · calc
      τ (g * X * ginv) = τ (ginv * (g * X)) := hCyclic (g * X) ginv
      _ = τ ((ginv * g) * X) := by rw [mul_assoc]
      _ = τ (1 * X) := by rw [hInv]
      _ = τ X := by rw [one_mul]

/-- Model fiber over idempotent point $P_i$: $\mathcal{F}_i(Z) = P_i Z P_i$ ($\mathfrak{DH}_2$). -/
def ModelFiber (P_i Z : B) : B :=
  P_i * Z * P_i

/-- Off-diagonal quasi-duality transition between model $j$ and model $i$:
$N_{ij}(X) = P_i X P_j$ ($\mathfrak{DH}_3$). -/
def QuasiDuality (P_i P_j X : B) : B :=
  P_i * X * P_j

/-- Return holonomy (exact two-hop duality operator inside fiber $i$):
$Q_{ij}(X, Y) = N_{ij}(X) N_{ji}(Y) = (P_i X P_j)(P_j Y P_i)$ ($\mathfrak{DH}_5$). -/
def ExactDualityHolonomy (P_i P_j X Y : B) : B :=
  QuasiDuality P_i P_j X * QuasiDuality P_j P_i Y

/-- Complementary waist projector $P_0 = 1 - P_1 - P_2$ of two orthogonal horizon projectors
$P_1, P_2 \in B$. -/
def waistProjector (P1 P2 : B) : B :=
  1 - P1 - P2

/-- Orthogonality and idempotency of the complementary waist projector $P_0 = 1 - P_1 - P_2$. -/
lemma waistProjector_orthogonal_idempotent
    (P1 P2 : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    P1 * waistProjector P1 P2 = 0 ∧
      waistProjector P1 P2 * P1 = 0 ∧
      P2 * waistProjector P1 P2 = 0 ∧
      waistProjector P1 P2 * P2 = 0 ∧
      waistProjector P1 P2 * waistProjector P1 P2 = waistProjector P1 P2 := by
  dsimp [waistProjector]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc
      P1 * (1 - P1 - P2) = P1 - P1 * P1 - P1 * P2 := by noncomm_ring
      _ = P1 - P1 - 0 := by rw [h1, h12]
      _ = 0 := by noncomm_ring
  · calc
      (1 - P1 - P2) * P1 = P1 - P1 * P1 - P2 * P1 := by noncomm_ring
      _ = P1 - P1 - 0 := by rw [h1, h21]
      _ = 0 := by noncomm_ring
  · calc
      P2 * (1 - P1 - P2) = P2 - P2 * P1 - P2 * P2 := by noncomm_ring
      _ = P2 - 0 - P2 := by rw [h21, h2]
      _ = 0 := by noncomm_ring
  · calc
      (1 - P1 - P2) * P2 = P2 - P1 * P2 - P2 * P2 := by noncomm_ring
      _ = P2 - 0 - P2 := by rw [h12, h2]
      _ = 0 := by noncomm_ring
  · calc
      (1 - P1 - P2) * (1 - P1 - P2)
        = 1 - 2 * P1 - 2 * P2 + P1 * P1 + P1 * P2 + P2 * P1 + P2 * P2 := by noncomm_ring
      _ = 1 - 2 * P1 - 2 * P2 + P1 + 0 + 0 + P2 := by rw [h1, h12, h21, h2]
      _ = 1 - P1 - P2 := by noncomm_ring

/-- **Theorem 1 ($\mathfrak{DH}_1 \prec \mathfrak{DH}_2$: Base Moduli Completeness & Model Fiber Closure)**:
Given two orthogonal idempotent horizon anchors $P_1, P_2 \in B$, the complementary waist projector
$P_0 = 1 - P_1 - P_2$ completes the 3-point partition of unity $P_1 + P_0 + P_2 = 1$, is pairwise
orthogonal to $P_1$ and $P_2$, and makes all three model fibers $\mathcal{F}_i(Z) = P_i Z P_i$
idempotently self-contained ($P_i \mathcal{F}_i(Z) P_i = \mathcal{F}_i(Z)$). -/
theorem base_moduli_and_model_fibers
    (P1 P2 Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := waistProjector P1 P2
    let F1 := ModelFiber P1 Z
    let F0 := ModelFiber P0 Z
    let F2 := ModelFiber P2 Z
    P1 + P0 + P2 = 1 ∧
      P1 * P0 = 0 ∧ P0 * P1 = 0 ∧
      P2 * P0 = 0 ∧ P0 * P2 = 0 ∧
      P1 * F1 * P1 = F1 ∧
      P0 * F0 * P0 = F0 ∧
      P2 * F2 * P2 = F2 := by
  rcases waistProjector_orthogonal_idempotent P1 P2 h1 h2 h12 h21 with
    ⟨h10, h01, h20, h02, h0⟩
  refine ⟨?_, h10, h01, h20, h02, ?_, ?_, ?_⟩
  · dsimp [waistProjector]
    noncomm_ring
  · dsimp [ModelFiber]
    calc
      P1 * (P1 * Z * P1) * P1 = (P1 * P1) * Z * (P1 * P1) := by noncomm_ring
      _ = P1 * Z * P1 := by rw [h1]
  · dsimp [ModelFiber]
    calc
      waistProjector P1 P2 * (waistProjector P1 P2 * Z * waistProjector P1 P2) *
          waistProjector P1 P2
        = (waistProjector P1 P2 * waistProjector P1 P2) * Z *
            (waistProjector P1 P2 * waistProjector P1 P2) := by noncomm_ring
      _ = waistProjector P1 P2 * Z * waistProjector P1 P2 := by rw [h0]
  · dsimp [ModelFiber]
    calc
      P2 * (P2 * Z * P2) * P2 = (P2 * P2) * Z * (P2 * P2) := by noncomm_ring
      _ = P2 * Z * P2 := by rw [h2]

/-- **Theorem 2 ($\mathfrak{DH}_3 \prec \mathfrak{DH}_4$: Quasi-Duality Nilpotency & Transitive Seiberg–Witten Monodromy)**:
1. Local quasi-dualities $N_{10} = P_1 X P_0$ and $N_{02} = P_0 Y P_2$ are square-zero nilpotent
   ($N_{10}^2 = 0$, $N_{02}^2 = 0$).
2. Transitive Monodromy across the waist $P_0$: their commutator $[N_{10}, N_{02}]$ equals the
   contact-grade cross-horizon transport $N_{12} = P_1 X P_0 Y P_2 \in P_1 B P_2$. -/
theorem quasi_duality_nilpotency_and_transitive_monodromy
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := waistProjector P1 P2
    let N10 := QuasiDuality P1 P0 X
    let N02 := QuasiDuality P0 P2 Y
    let N12 := P1 * X * P0 * Y * P2
    N10 * N10 = 0 ∧
      N02 * N02 = 0 ∧
      ringCommutator N10 N02 = N12 ∧
      P1 * N12 * P2 = N12 := by
  rcases waistProjector_orthogonal_idempotent P1 P2 h1 h2 h12 h21 with
    ⟨_h10, h01, h20, _h02, h0⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [QuasiDuality]
    calc
      (P1 * X * waistProjector P1 P2) * (P1 * X * waistProjector P1 P2)
        = P1 * X * (waistProjector P1 P2 * P1) * X * waistProjector P1 P2 := by noncomm_ring
      _ = P1 * X * 0 * X * waistProjector P1 P2 := by rw [h01]
      _ = 0 := by noncomm_ring
  · dsimp [QuasiDuality]
    calc
      (waistProjector P1 P2 * Y * P2) * (waistProjector P1 P2 * Y * P2)
        = waistProjector P1 P2 * Y * (P2 * waistProjector P1 P2) * Y * P2 := by noncomm_ring
      _ = waistProjector P1 P2 * Y * 0 * Y * P2 := by rw [h20]
      _ = 0 := by noncomm_ring
  · dsimp [ringCommutator, QuasiDuality]
    calc
      (P1 * X * waistProjector P1 P2) * (waistProjector P1 P2 * Y * P2) -
          (waistProjector P1 P2 * Y * P2) * (P1 * X * waistProjector P1 P2)
        = P1 * X * (waistProjector P1 P2 * waistProjector P1 P2) * Y * P2 -
            waistProjector P1 P2 * Y * (P2 * P1) * X * waistProjector P1 P2 := by noncomm_ring
      _ = P1 * X * waistProjector P1 P2 * Y * P2 -
            waistProjector P1 P2 * Y * 0 * X * waistProjector P1 P2 := by rw [h0, h21]
      _ = P1 * X * waistProjector P1 P2 * Y * P2 := by noncomm_ring
  · calc
      P1 * (P1 * X * waistProjector P1 P2 * Y * P2) * P2
        = (P1 * P1) * X * waistProjector P1 P2 * Y * (P2 * P2) := by noncomm_ring
      _ = P1 * X * waistProjector P1 P2 * Y * P2 := by rw [h1, h2]

/-- **Theorem 3 ($\mathfrak{DH}_5$: Exact Duality Holonomy & Theoretical Equivalence)**:
1. The two-hop return holonomy $Q_{10} = N_{10} N_{01}$ lives strictly inside Model Fiber 1
   ($\mathcal{F}_1(Q_{10}) = Q_{10}$), and $Q_{01} = N_{01} N_{10}$ lives strictly inside Model Fiber 0
   ($\mathcal{F}_0(Q_{01}) = Q_{01}$).
2. Under any cyclic trace $\tau : B \to_+ A$ ($\tau(x y) = \tau(y x)$), the two dual fibers share
   identical physical invariants: $\tau(Q_{10}) = \tau(Q_{01})$. -/
theorem exact_duality_and_theoretical_equivalence
    {A : Type*} [AddCommGroup A] (τ : B →+ A)
    (hCyclic : ∀ x y : B, τ (x * y) = τ (y * x))
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := waistProjector P1 P2
    let Q10 := ExactDualityHolonomy P1 P0 X Y
    let Q01 := ExactDualityHolonomy P0 P1 Y X
    ModelFiber P1 Q10 = Q10 ∧
      ModelFiber P0 Q01 = Q01 ∧
      τ Q10 = τ Q01 := by
  rcases waistProjector_orthogonal_idempotent P1 P2 h1 h2 h12 h21 with
    ⟨_h10, _h01, _h20, _h02, h0⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp [ModelFiber, ExactDualityHolonomy, QuasiDuality]
    calc
      P1 * ((P1 * X * waistProjector P1 P2) * (waistProjector P1 P2 * Y * P1)) * P1
        = (P1 * P1) * X * waistProjector P1 P2 *
            (waistProjector P1 P2 * Y * (P1 * P1)) := by noncomm_ring
      _ = (P1 * X * waistProjector P1 P2) * (waistProjector P1 P2 * Y * P1) := by
          rw [h1]
  · dsimp [ModelFiber, ExactDualityHolonomy, QuasiDuality]
    calc
      waistProjector P1 P2 *
          ((waistProjector P1 P2 * Y * P1) * (P1 * X * waistProjector P1 P2)) *
          waistProjector P1 P2
        = (waistProjector P1 P2 * waistProjector P1 P2) * Y * P1 *
            (P1 * X * (waistProjector P1 P2 * waistProjector P1 P2)) := by noncomm_ring
      _ = (waistProjector P1 P2 * Y * P1) * (P1 * X * waistProjector P1 P2) := by
          rw [h0]
  · dsimp [ExactDualityHolonomy]
    exact hCyclic (QuasiDuality P1 (waistProjector P1 P2) X)
      (QuasiDuality (waistProjector P1 P2) P1 Y)

/-- Monopole holonomy generator $Q_{10} = P_1 X P_0 Y P_1 \in \mathcal{F}_1$ ($\mathfrak{SW}_1$). -/
def Q10_monopole (P1 P2 X Y : B) : B :=
  P1 * X * waistProjector P1 P2 * Y * P1

/-- Dyon holonomy generator $Q_{20} = P_2 Y P_0 X P_2 \in \mathcal{F}_2$ ($\mathfrak{SW}_1$). -/
def Q20_dyon (P1 P2 X Y : B) : B :=
  P2 * Y * waistProjector P1 P2 * X * P2

/-- Semiclassical intermediate waist metric
$V_0 = P_0 Y P_1 X P_0 + P_0 X P_2 Y P_0 \in \mathcal{F}_0$ ($\mathfrak{SW}_3$). -/
def V0_semiclassical (P1 P2 X Y : B) : B :=
  waistProjector P1 P2 * Y * P1 * X * waistProjector P1 P2 +
    waistProjector P1 P2 * X * P2 * Y * waistProjector P1 P2

/-- **Theorem 4 ($\mathfrak{SW}_1 \prec \mathfrak{SW}_2$: Local Fiber Confinement & Strict Generator Orthogonality)**:
The monopole and dyon return holonomy generators $Q_{10} \in \mathcal{F}_1$ and
$Q_{20} \in \mathcal{F}_2$ are strictly confined to their respective model fibers and mutually
annihilate each other's products identically ($Q_{10} Q_{20} = Q_{20} Q_{10} = 0$,
$[Q_{10}, Q_{20}] = 0$). -/
theorem monopole_dyon_orthogonality
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let Q10 := Q10_monopole P1 P2 X Y
    let Q20 := Q20_dyon P1 P2 X Y
    P1 * Q10 * P1 = Q10 ∧
      P2 * Q20 * P2 = Q20 ∧
      Q10 * Q20 = 0 ∧
      Q20 * Q10 = 0 ∧
      ringCommutator Q10 Q20 = 0 := by
  have hA : Q10_monopole P1 P2 X Y * Q20_dyon P1 P2 X Y = 0 := by
    dsimp [Q10_monopole, Q20_dyon]
    calc
      (P1 * X * waistProjector P1 P2 * Y * P1) * (P2 * Y * waistProjector P1 P2 * X * P2)
        = P1 * X * waistProjector P1 P2 * Y * (P1 * P2) * Y *
            waistProjector P1 P2 * X * P2 := by noncomm_ring
      _ = P1 * X * waistProjector P1 P2 * Y * 0 * Y *
            waistProjector P1 P2 * X * P2 := by rw [h12]
      _ = 0 := by noncomm_ring
  have hB : Q20_dyon P1 P2 X Y * Q10_monopole P1 P2 X Y = 0 := by
    dsimp [Q10_monopole, Q20_dyon]
    calc
      (P2 * Y * waistProjector P1 P2 * X * P2) * (P1 * X * waistProjector P1 P2 * Y * P1)
        = P2 * Y * waistProjector P1 P2 * X * (P2 * P1) * X *
            waistProjector P1 P2 * Y * P1 := by noncomm_ring
      _ = P2 * Y * waistProjector P1 P2 * X * 0 * X *
            waistProjector P1 P2 * Y * P1 := by rw [h21]
      _ = 0 := by noncomm_ring
  refine ⟨?_, ?_, hA, hB, ?_⟩
  · dsimp [Q10_monopole]
    calc
      P1 * (P1 * X * waistProjector P1 P2 * Y * P1) * P1
        = (P1 * P1) * X * waistProjector P1 P2 * Y * (P1 * P1) := by noncomm_ring
      _ = P1 * X * waistProjector P1 P2 * Y * P1 := by rw [h1]
  · dsimp [Q20_dyon]
    calc
      P2 * (P2 * Y * waistProjector P1 P2 * X * P2) * P2
        = (P2 * P2) * Y * waistProjector P1 P2 * X * (P2 * P2) := by noncomm_ring
      _ = P2 * Y * waistProjector P1 P2 * X * P2 := by rw [h2]
  · dsimp [ringCommutator]
    rw [hA, hB, sub_self]

/-- **Theorem 5 ($\mathfrak{SW}_3$: Waist Metric Confinement & Modular Scale Invariance)**:
The semiclassical waist metric $V_0 = Q_{01} + Q_{02}$ is strictly confined to the waist fiber
$\mathcal{F}_0$ ($P_0 V_0 P_0 = V_0$) and commutes with the modular dilation generator
$H = P_1 - P_2$ ($[H, V_0] = 0$). -/
theorem semiclassical_waist_invariance
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := waistProjector P1 P2
    let H  := modularDilation P1 P2
    let V0 := V0_semiclassical P1 P2 X Y
    P0 * V0 * P0 = V0 ∧
      ringCommutator H V0 = 0 := by
  rcases waistProjector_orthogonal_idempotent P1 P2 h1 h2 h12 h21 with
    ⟨h10, h01, h20, h02, h0⟩
  refine ⟨?_, ?_⟩
  · dsimp [V0_semiclassical]
    calc
      waistProjector P1 P2 *
          (waistProjector P1 P2 * Y * P1 * X * waistProjector P1 P2 +
            waistProjector P1 P2 * X * P2 * Y * waistProjector P1 P2) *
          waistProjector P1 P2
        = (waistProjector P1 P2 * waistProjector P1 P2) * Y * P1 * X *
            (waistProjector P1 P2 * waistProjector P1 P2) +
          (waistProjector P1 P2 * waistProjector P1 P2) * X * P2 * Y *
            (waistProjector P1 P2 * waistProjector P1 P2) := by noncomm_ring
      _ = waistProjector P1 P2 * Y * P1 * X * waistProjector P1 P2 +
            waistProjector P1 P2 * X * P2 * Y * waistProjector P1 P2 := by rw [h0]
  · dsimp [ringCommutator, modularDilation, V0_semiclassical]
    calc
      (P1 - P2) *
          (waistProjector P1 P2 * Y * P1 * X * waistProjector P1 P2 +
            waistProjector P1 P2 * X * P2 * Y * waistProjector P1 P2) -
        (waistProjector P1 P2 * Y * P1 * X * waistProjector P1 P2 +
            waistProjector P1 P2 * X * P2 * Y * waistProjector P1 P2) *
          (P1 - P2)
        = (P1 * waistProjector P1 P2) * Y * P1 * X * waistProjector P1 P2 +
            (P1 * waistProjector P1 P2) * X * P2 * Y * waistProjector P1 P2 -
            (P2 * waistProjector P1 P2) * Y * P1 * X * waistProjector P1 P2 -
            (P2 * waistProjector P1 P2) * X * P2 * Y * waistProjector P1 P2 -
            waistProjector P1 P2 * Y * P1 * X * (waistProjector P1 P2 * P1) -
            waistProjector P1 P2 * X * P2 * Y * (waistProjector P1 P2 * P1) +
            waistProjector P1 P2 * Y * P1 * X * (waistProjector P1 P2 * P2) +
            waistProjector P1 P2 * X * P2 * Y * (waistProjector P1 P2 * P2) := by noncomm_ring
      _ = 0 * Y * P1 * X * waistProjector P1 P2 +
            0 * X * P2 * Y * waistProjector P1 P2 -
            0 * Y * P1 * X * waistProjector P1 P2 -
            0 * X * P2 * Y * waistProjector P1 P2 -
            waistProjector P1 P2 * Y * P1 * X * 0 -
            waistProjector P1 P2 * X * P2 * Y * 0 +
            waistProjector P1 P2 * Y * P1 * X * 0 +
            waistProjector P1 P2 * X * P2 * Y * 0 := by rw [h10, h20, h01, h02]
      _ = 0 := by noncomm_ring

/-- **Theorem 6 ($\mathfrak{SW}_4 \prec \mathfrak{SW}_5$: Unipotent Monodromy Shear & Contact Wormhole Generation)**:
The unipotent boundary shear $M_{10} = 1 + N_{10}$ ($N_{10} = P_1 X P_0$) acting on the dual
boundary jump $N_{02} = P_0 Y P_2$ generates the cross-horizon contact wormhole
$N_{12} = P_1 X P_0 Y P_2 \in \mathcal{G}_{+2}$ ($M_{10} N_{02} = N_{02} + N_{12}$,
$[N_{10}, N_{02}] = N_{12}$), terminates at second order ($N_{10} N_{12} = 0$), and the monopole
holonomy $Q_{10}$ decouples from $N_{02}$ ($Q_{10} N_{02} = 0$). -/
theorem unipotent_monodromy_wormhole_flow
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0  := waistProjector P1 P2
    let N10 := QuasiDuality P1 P0 X
    let N02 := QuasiDuality P0 P2 Y
    let N12 := P1 * X * P0 * Y * P2
    let M10 := 1 + N10
    let Q10 := Q10_monopole P1 P2 X Y
    M10 * N02 = N02 + N12 ∧
      ringCommutator N10 N02 = N12 ∧
      N10 * N12 = 0 ∧
      Q10 * N02 = 0 := by
  rcases waistProjector_orthogonal_idempotent P1 P2 h1 h2 h12 h21 with
    ⟨h10, h01, _h20, _h02, h0⟩
  have hN10_N02 :
      QuasiDuality P1 (waistProjector P1 P2) X *
          QuasiDuality (waistProjector P1 P2) P2 Y =
        P1 * X * waistProjector P1 P2 * Y * P2 := by
    dsimp [QuasiDuality]
    calc
      (P1 * X * waistProjector P1 P2) * (waistProjector P1 P2 * Y * P2)
        = P1 * X * (waistProjector P1 P2 * waistProjector P1 P2) * Y * P2 := by noncomm_ring
      _ = P1 * X * waistProjector P1 P2 * Y * P2 := by rw [h0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (1 + QuasiDuality P1 (waistProjector P1 P2) X) *
          QuasiDuality (waistProjector P1 P2) P2 Y
        = QuasiDuality (waistProjector P1 P2) P2 Y +
            QuasiDuality P1 (waistProjector P1 P2) X *
              QuasiDuality (waistProjector P1 P2) P2 Y := by noncomm_ring
      _ = QuasiDuality (waistProjector P1 P2) P2 Y +
            P1 * X * waistProjector P1 P2 * Y * P2 := by rw [hN10_N02]
  · exact (quasi_duality_nilpotency_and_transitive_monodromy P1 P2 X Y h1 h2 h12 h21).2.2.1
  · dsimp [QuasiDuality]
    calc
      (P1 * X * waistProjector P1 P2) * (P1 * X * waistProjector P1 P2 * Y * P2)
        = P1 * X * (waistProjector P1 P2 * P1) * X * waistProjector P1 P2 * Y * P2 := by
            noncomm_ring
      _ = P1 * X * 0 * X * waistProjector P1 P2 * Y * P2 := by rw [h01]
      _ = 0 := by noncomm_ring
  · dsimp [Q10_monopole, QuasiDuality]
    calc
      (P1 * X * waistProjector P1 P2 * Y * P1) * (waistProjector P1 P2 * Y * P2)
        = P1 * X * waistProjector P1 P2 * Y * (P1 * waistProjector P1 P2) * Y * P2 := by
            noncomm_ring
      _ = P1 * X * waistProjector P1 P2 * Y * 0 * Y * P2 := by rw [h10]
      _ = 0 := by noncomm_ring

/-- Three-corner scaling operator
$U(r, r^{-1}) = P_1 r P_1 + P_0 + P_2 r^{-1} P_2$ for the Peirce partition
$1 = P_1 + P_0 + P_2$. This algebraic operator does not itself construct a crossed product. -/
def threeHorizonCornerScaling (P1 P2 r rinv : B) : B :=
  P1 * r * P1 + waistProjector P1 P2 + P2 * rinv * P2

/-- A right inverse for the three-corner scaling operator across the 3-horizon
partition of unity: $U(r, r^{-1}) \, U(r^{-1}, r) = 1$ whenever $P_1 r P_1 r^{-1} P_1 = P_1$ and
$P_2 r^{-1} P_2 r P_2 = P_2$. -/
theorem threeHorizonCornerScaling_mul_right_inverse
    (P1 P2 r rinv : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0)
    (hr1 : P1 * r * P1 * rinv * P1 = P1)
    (hr2 : P2 * rinv * P2 * r * P2 = P2) :
    threeHorizonCornerScaling P1 P2 r rinv *
        threeHorizonCornerScaling P1 P2 rinv r = 1 := by
  rcases waistProjector_orthogonal_idempotent P1 P2 h1 h2 h12 h21 with
    ⟨h10, h01, h20, h02, h0⟩
  dsimp [threeHorizonCornerScaling]
  have h11 : (P1 * r * P1) * (P1 * rinv * P1) = P1 := by
    calc
      (P1 * r * P1) * (P1 * rinv * P1)
        = P1 * r * (P1 * P1) * rinv * P1 := by noncomm_ring
      _ = P1 * r * P1 * rinv * P1 := by rw [h1]
      _ = P1 := hr1
  have h22 : (P2 * rinv * P2) * (P2 * r * P2) = P2 := by
    calc
      (P2 * rinv * P2) * (P2 * r * P2)
        = P2 * rinv * (P2 * P2) * r * P2 := by noncomm_ring
      _ = P2 * rinv * P2 * r * P2 := by rw [h2]
      _ = P2 := hr2
  calc
    (P1 * r * P1 + waistProjector P1 P2 + P2 * rinv * P2) *
        (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2)
      = (P1 * r * P1) * (P1 * rinv * P1) +
          P1 * r * (P1 * waistProjector P1 P2) +
          P1 * r * (P1 * P2) * r * P2 +
          (waistProjector P1 P2 * P1) * rinv * P1 +
          waistProjector P1 P2 * waistProjector P1 P2 +
          (waistProjector P1 P2 * P2) * r * P2 +
          P2 * rinv * (P2 * P1) * rinv * P1 +
          P2 * rinv * (P2 * waistProjector P1 P2) +
          (P2 * rinv * P2) * (P2 * r * P2) := by noncomm_ring
    _ = P1 + P1 * r * 0 + P1 * r * 0 * r * P2 +
          0 * rinv * P1 + waistProjector P1 P2 + 0 * r * P2 +
          P2 * rinv * 0 * rinv * P1 + P2 * rinv * 0 + P2 := by
        rw [h11, h10, h12, h01, h0, h02, h21, h20, h22]
    _ = P1 + waistProjector P1 P2 + P2 := by noncomm_ring
    _ = 1 := by
        dsimp [waistProjector]
        noncomm_ring

/-- The reverse multiplication order is a left inverse when the two horizon-corner
products occur in the reverse order. -/
theorem threeHorizonCornerScaling_mul_left_inverse
    (P1 P2 r rinv : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0)
    (hr1 : P1 * rinv * P1 * r * P1 = P1)
    (hr2 : P2 * r * P2 * rinv * P2 = P2) :
    threeHorizonCornerScaling P1 P2 rinv r *
        threeHorizonCornerScaling P1 P2 r rinv = 1 := by
  rcases waistProjector_orthogonal_idempotent P1 P2 h1 h2 h12 h21 with
    ⟨h10, h01, h20, h02, h0⟩
  dsimp [threeHorizonCornerScaling]
  have h11 : (P1 * rinv * P1) * (P1 * r * P1) = P1 := by
    calc
      (P1 * rinv * P1) * (P1 * r * P1)
        = P1 * rinv * (P1 * P1) * r * P1 := by noncomm_ring
      _ = P1 * rinv * P1 * r * P1 := by rw [h1]
      _ = P1 := hr1
  have h22 : (P2 * r * P2) * (P2 * rinv * P2) = P2 := by
    calc
      (P2 * r * P2) * (P2 * rinv * P2)
        = P2 * r * (P2 * P2) * rinv * P2 := by noncomm_ring
      _ = P2 * r * P2 * rinv * P2 := by rw [h2]
      _ = P2 := hr2
  calc
    (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2) *
        (P1 * r * P1 + waistProjector P1 P2 + P2 * rinv * P2)
      = (P1 * rinv * P1) * (P1 * r * P1) +
          P1 * rinv * (P1 * waistProjector P1 P2) +
          P1 * rinv * (P1 * P2) * rinv * P2 +
          (waistProjector P1 P2 * P1) * r * P1 +
          waistProjector P1 P2 * waistProjector P1 P2 +
          (waistProjector P1 P2 * P2) * rinv * P2 +
          P2 * r * (P2 * P1) * r * P1 +
          P2 * r * (P2 * waistProjector P1 P2) +
          (P2 * r * P2) * (P2 * rinv * P2) := by noncomm_ring
    _ = P1 + P1 * rinv * 0 + P1 * rinv * 0 * rinv * P2 +
          0 * r * P1 + waistProjector P1 P2 + 0 * rinv * P2 +
          P2 * r * 0 * r * P1 + P2 * r * 0 + P2 := by
        rw [h11, h10, h12, h01, h0, h02, h21, h20, h22]
    _ = P1 + waistProjector P1 P2 + P2 := by noncomm_ring
    _ = 1 := by
        dsimp [waistProjector]
        noncomm_ring

/-- Conjugation by the three-corner scaling operator
$U(r, r^{-1}) = P_1 r P_1 + P_0 + P_2 r^{-1} P_2$ leaves every waist corner
$\mathcal{F}_0(W) = P_0 W P_0$ strictly invariant, scales the quasi-duality jump
$N_{10} = P_1 X P_0$ by $P_1 r P_1$ on the left, and scales the contact wormhole
$N_{12} = P_1 Z P_2$ by $P_1 r P_1$ on the left and $P_2 r P_2$ on the right. -/
theorem threeHorizonCornerScaling_transition_action
    (P1 P2 r rinv W X Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0 := waistProjector P1 P2
    let U := threeHorizonCornerScaling P1 P2 r rinv
    let Uinv := threeHorizonCornerScaling P1 P2 rinv r
    U * (P0 * W * P0) * Uinv = P0 * W * P0 ∧
      U * (P1 * X * P0) * Uinv = P1 * r * P1 * X * P0 ∧
      U * (P1 * Z * P2) * Uinv = P1 * r * P1 * Z * P2 * r * P2 := by
  rcases waistProjector_orthogonal_idempotent P1 P2 h1 h2 h12 h21 with
    ⟨h10, h01, h20, h02, h0⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp [threeHorizonCornerScaling]
    calc
      (P1 * r * P1 + waistProjector P1 P2 + P2 * rinv * P2) *
          (waistProjector P1 P2 * W * waistProjector P1 P2) *
          (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2)
        = (P1 * r * (P1 * waistProjector P1 P2) * W * waistProjector P1 P2 +
            (waistProjector P1 P2 * waistProjector P1 P2) * W * waistProjector P1 P2 +
            P2 * rinv * (P2 * waistProjector P1 P2) * W * waistProjector P1 P2) *
            (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2) := by noncomm_ring
      _ = (P1 * r * 0 * W * waistProjector P1 P2 +
            waistProjector P1 P2 * W * waistProjector P1 P2 +
            P2 * rinv * 0 * W * waistProjector P1 P2) *
            (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2) := by rw [h10, h0, h20]
      _ = waistProjector P1 P2 * W * (waistProjector P1 P2 * P1) * rinv * P1 +
            waistProjector P1 P2 * W * (waistProjector P1 P2 * waistProjector P1 P2) +
            waistProjector P1 P2 * W * (waistProjector P1 P2 * P2) * r * P2 := by noncomm_ring
      _ = waistProjector P1 P2 * W * 0 * rinv * P1 +
            waistProjector P1 P2 * W * waistProjector P1 P2 +
            waistProjector P1 P2 * W * 0 * r * P2 := by rw [h01, h0, h02]
      _ = waistProjector P1 P2 * W * waistProjector P1 P2 := by noncomm_ring
  · dsimp [threeHorizonCornerScaling]
    calc
      (P1 * r * P1 + waistProjector P1 P2 + P2 * rinv * P2) *
          (P1 * X * waistProjector P1 P2) *
          (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2)
        = (P1 * r * (P1 * P1) * X * waistProjector P1 P2 +
            (waistProjector P1 P2 * P1) * X * waistProjector P1 P2 +
            P2 * rinv * (P2 * P1) * X * waistProjector P1 P2) *
            (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2) := by noncomm_ring
      _ = (P1 * r * P1 * X * waistProjector P1 P2 +
            0 * X * waistProjector P1 P2 +
            P2 * rinv * 0 * X * waistProjector P1 P2) *
            (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2) := by rw [h1, h01, h21]
      _ = P1 * r * P1 * X * (waistProjector P1 P2 * P1) * rinv * P1 +
            P1 * r * P1 * X * (waistProjector P1 P2 * waistProjector P1 P2) +
            P1 * r * P1 * X * (waistProjector P1 P2 * P2) * r * P2 := by noncomm_ring
      _ = P1 * r * P1 * X * 0 * rinv * P1 +
            P1 * r * P1 * X * waistProjector P1 P2 +
            P1 * r * P1 * X * 0 * r * P2 := by rw [h01, h0, h02]
      _ = P1 * r * P1 * X * waistProjector P1 P2 := by noncomm_ring
  · dsimp [threeHorizonCornerScaling]
    calc
      (P1 * r * P1 + waistProjector P1 P2 + P2 * rinv * P2) *
          (P1 * Z * P2) *
          (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2)
        = (P1 * r * (P1 * P1) * Z * P2 +
            (waistProjector P1 P2 * P1) * Z * P2 +
            P2 * rinv * (P2 * P1) * Z * P2) *
            (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2) := by noncomm_ring
      _ = (P1 * r * P1 * Z * P2 + 0 * Z * P2 + P2 * rinv * 0 * Z * P2) *
            (P1 * rinv * P1 + waistProjector P1 P2 + P2 * r * P2) := by rw [h1, h01, h21]
      _ = P1 * r * P1 * Z * (P2 * P1) * rinv * P1 +
            P1 * r * P1 * Z * (P2 * waistProjector P1 P2) +
            P1 * r * P1 * Z * (P2 * P2) * r * P2 := by noncomm_ring
      _ = P1 * r * P1 * Z * 0 * rinv * P1 +
            P1 * r * P1 * Z * 0 +
            P1 * r * P1 * Z * P2 * r * P2 := by rw [h21, h20, h2]
      _ = P1 * r * P1 * Z * P2 * r * P2 := by noncomm_ring

/-- The three-horizon Peirce partition determines the stated tripotent relations and commutator
weights. Under a cyclic additive functional, transitions have zero trace and the waist trace equals
the sum of the two return-corner traces. This algebraic result does not construct a continuous
modular flow or a crossed-product algebra:
1. **Discrete-to-Continuous Frame Reconstruction:**
   $H^2 + H = 2 P_1$, $H^2 - H = 2 P_2$, and $1 - H^2 = P_0$.
2. **Modular Scaling Eigenvalues & Exact Commutator Generation:**
   $[H, \mathcal{F}_0(Z)] = 0$, $[H, N_{10}] = N_{10}$, $[H, N_{02}] = N_{02}$,
   $[H, N_{12}] = 2 N_{12}$, and $[P_1, N_{12}] = N_{12}$.
3. **Crossed-Product Trace Neutrality & Waist Holonomy Conservation:**
   Under any cyclic trace $\tau : B \to_+ A$, all off-diagonal quasi-dualities and wormholes have
   identically zero trace ($\tau(N_{10}) = 0$, $\tau(N_{02}) = 0$, $\tau(N_{12}) = 0$), and the
   semiclassical waist metric trace $\tau(V_0)$ equals the sum of the monopole and dyon fiber
   holonomy traces $\tau(Q_{10}) + \tau(Q_{20})$. -/
theorem three_horizon_modular_weights_and_cyclic_trace_balance
    {A : Type*} [AddCommGroup A] (τ : B →+ A)
    (hCyclic : ∀ x y : B, τ (x * y) = τ (y * x))
    (P1 P2 X Y Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let P0  := waistProjector P1 P2
    let H   := modularDilation P1 P2
    let F0  := ModelFiber P0 Z
    let N10 := QuasiDuality P1 P0 X
    let N02 := QuasiDuality P0 P2 Y
    let N12 := P1 * X * P0 * Y * P2
    let Q10 := Q10_monopole P1 P2 X Y
    let Q20 := Q20_dyon P1 P2 X Y
    let V0  := V0_semiclassical P1 P2 X Y
    H ^ 2 + H = 2 * P1 ∧
      H ^ 2 - H = 2 * P2 ∧
      1 - H ^ 2 = P0 ∧
      ringCommutator H F0 = 0 ∧
      ringCommutator H N10 = N10 ∧
      ringCommutator H N02 = N02 ∧
      ringCommutator H N12 = 2 * N12 ∧
      ringCommutator P1 N12 = N12 ∧
      τ N10 = 0 ∧
      τ N02 = 0 ∧
      τ N12 = 0 ∧
      τ V0 = τ Q10 + τ Q20 := by
  rcases waistProjector_orthogonal_idempotent P1 P2 h1 h2 h12 h21 with
    ⟨h10, h01, h20, h02, _h0⟩
  have hsq : (modularDilation P1 P2) ^ 2 = P1 + P2 :=
    modularDilation_sq P1 P2 h1 h2 h12 h21
  have h_comm_N10 :
      ringCommutator (modularDilation P1 P2) (QuasiDuality P1 (waistProjector P1 P2) X) =
        QuasiDuality P1 (waistProjector P1 P2) X := by
    dsimp [ringCommutator, modularDilation, QuasiDuality]
    calc
      (P1 - P2) * (P1 * X * waistProjector P1 P2) -
          (P1 * X * waistProjector P1 P2) * (P1 - P2)
        = (P1 * P1) * X * waistProjector P1 P2 -
            (P2 * P1) * X * waistProjector P1 P2 -
            P1 * X * (waistProjector P1 P2 * P1) +
            P1 * X * (waistProjector P1 P2 * P2) := by noncomm_ring
      _ = P1 * X * waistProjector P1 P2 - 0 * X * waistProjector P1 P2 -
            P1 * X * 0 + P1 * X * 0 := by rw [h1, h21, h01, h02]
      _ = P1 * X * waistProjector P1 P2 := by noncomm_ring
  have h_comm_N02 :
      ringCommutator (modularDilation P1 P2) (QuasiDuality (waistProjector P1 P2) P2 Y) =
        QuasiDuality (waistProjector P1 P2) P2 Y := by
    dsimp [ringCommutator, modularDilation, QuasiDuality]
    calc
      (P1 - P2) * (waistProjector P1 P2 * Y * P2) -
          (waistProjector P1 P2 * Y * P2) * (P1 - P2)
        = (P1 * waistProjector P1 P2) * Y * P2 -
            (P2 * waistProjector P1 P2) * Y * P2 -
            waistProjector P1 P2 * Y * (P2 * P1) +
            waistProjector P1 P2 * Y * (P2 * P2) := by noncomm_ring
      _ = 0 * Y * P2 - 0 * Y * P2 - waistProjector P1 P2 * Y * 0 +
            waistProjector P1 P2 * Y * P2 := by rw [h10, h20, h21, h2]
      _ = waistProjector P1 P2 * Y * P2 := by noncomm_ring
  have h_comm_N12 :
      ringCommutator (modularDilation P1 P2) (P1 * X * waistProjector P1 P2 * Y * P2) =
        2 * (P1 * X * waistProjector P1 P2 * Y * P2) := by
    dsimp [ringCommutator, modularDilation]
    calc
      (P1 - P2) * (P1 * X * waistProjector P1 P2 * Y * P2) -
          (P1 * X * waistProjector P1 P2 * Y * P2) * (P1 - P2)
        = (P1 * P1) * X * waistProjector P1 P2 * Y * P2 -
            (P2 * P1) * X * waistProjector P1 P2 * Y * P2 -
            P1 * X * waistProjector P1 P2 * Y * (P2 * P1) +
            P1 * X * waistProjector P1 P2 * Y * (P2 * P2) := by noncomm_ring
      _ = P1 * X * waistProjector P1 P2 * Y * P2 -
            0 * X * waistProjector P1 P2 * Y * P2 -
            P1 * X * waistProjector P1 P2 * Y * 0 +
            P1 * X * waistProjector P1 P2 * Y * P2 := by rw [h1, h21, h2]
      _ = 2 * (P1 * X * waistProjector P1 P2 * Y * P2) := by noncomm_ring
  have h_P1_N12 :
      ringCommutator P1 (P1 * X * waistProjector P1 P2 * Y * P2) =
        P1 * X * waistProjector P1 P2 * Y * P2 := by
    dsimp [ringCommutator]
    calc
      P1 * (P1 * X * waistProjector P1 P2 * Y * P2) -
          (P1 * X * waistProjector P1 P2 * Y * P2) * P1
        = (P1 * P1) * X * waistProjector P1 P2 * Y * P2 -
            P1 * X * waistProjector P1 P2 * Y * (P2 * P1) := by noncomm_ring
      _ = P1 * X * waistProjector P1 P2 * Y * P2 -
            P1 * X * waistProjector P1 P2 * Y * 0 := by rw [h1, h21]
      _ = P1 * X * waistProjector P1 P2 * Y * P2 := by noncomm_ring
  have h_tr_comm : ∀ a b : B, τ (ringCommutator a b) = 0 := fun a b => by
    dsimp [ringCommutator]
    rw [map_sub, hCyclic a b, sub_self]
  refine ⟨?_, ?_, ?_, ?_, h_comm_N10, h_comm_N02, h_comm_N12, h_P1_N12, ?_, ?_, ?_, ?_⟩
  · rw [hsq]
    dsimp [modularDilation]
    noncomm_ring
  · rw [hsq]
    dsimp [modularDilation]
    noncomm_ring
  · rw [hsq]
    dsimp [waistProjector]
    noncomm_ring
  · dsimp [ringCommutator, modularDilation, ModelFiber]
    calc
      (P1 - P2) * (waistProjector P1 P2 * Z * waistProjector P1 P2) -
          (waistProjector P1 P2 * Z * waistProjector P1 P2) * (P1 - P2)
        = (P1 * waistProjector P1 P2) * Z * waistProjector P1 P2 -
            (P2 * waistProjector P1 P2) * Z * waistProjector P1 P2 -
            waistProjector P1 P2 * Z * (waistProjector P1 P2 * P1) +
            waistProjector P1 P2 * Z * (waistProjector P1 P2 * P2) := by noncomm_ring
      _ = 0 * Z * waistProjector P1 P2 - 0 * Z * waistProjector P1 P2 -
            waistProjector P1 P2 * Z * 0 + waistProjector P1 P2 * Z * 0 := by
          rw [h10, h20, h01, h02]
      _ = 0 := by noncomm_ring
  · rw [← h_comm_N10]
    exact h_tr_comm _ _
  · rw [← h_comm_N02]
    exact h_tr_comm _ _
  · rw [← h_P1_N12]
    exact h_tr_comm _ _
  · dsimp [V0_semiclassical, Q10_monopole, Q20_dyon]
    rw [map_add]
    congr 1
    · calc
        τ (waistProjector P1 P2 * Y * P1 * X * waistProjector P1 P2)
          = τ ((waistProjector P1 P2 * Y * P1) * (P1 * X * waistProjector P1 P2)) := by
              congr 1
              calc
                waistProjector P1 P2 * Y * P1 * X * waistProjector P1 P2
                  = waistProjector P1 P2 * Y * (P1 * P1) * X * waistProjector P1 P2 := by rw [h1]
                _ = (waistProjector P1 P2 * Y * P1) * (P1 * X * waistProjector P1 P2) := by
                      noncomm_ring
        _ = τ ((P1 * X * waistProjector P1 P2) * (waistProjector P1 P2 * Y * P1)) :=
              hCyclic _ _
        _ = τ (P1 * X * waistProjector P1 P2 * Y * P1) := by
              congr 1
              calc
                (P1 * X * waistProjector P1 P2) * (waistProjector P1 P2 * Y * P1)
                  = P1 * X * (waistProjector P1 P2 * waistProjector P1 P2) * Y * P1 := by
                      noncomm_ring
                _ = P1 * X * waistProjector P1 P2 * Y * P1 := by rw [_h0]
    · calc
        τ (waistProjector P1 P2 * X * P2 * Y * waistProjector P1 P2)
          = τ ((waistProjector P1 P2 * X * P2) * (P2 * Y * waistProjector P1 P2)) := by
              congr 1
              calc
                waistProjector P1 P2 * X * P2 * Y * waistProjector P1 P2
                  = waistProjector P1 P2 * X * (P2 * P2) * Y * waistProjector P1 P2 := by rw [h2]
                _ = (waistProjector P1 P2 * X * P2) * (P2 * Y * waistProjector P1 P2) := by
                      noncomm_ring
        _ = τ ((P2 * Y * waistProjector P1 P2) * (waistProjector P1 P2 * X * P2)) :=
              hCyclic _ _
        _ = τ (P2 * Y * waistProjector P1 P2 * X * P2) := by
              congr 1
              calc
                (P2 * Y * waistProjector P1 P2) * (waistProjector P1 P2 * X * P2)
                  = P2 * Y * (waistProjector P1 P2 * waistProjector P1 P2) * X * P2 := by
                      noncomm_ring
                _ = P2 * Y * waistProjector P1 P2 * X * P2 := by rw [_h0]

end NonCommutativeRingModelBundle

end InfoGeometry.Canonical.Arxiv251107015ModelBundleSeibergWittenPoset
