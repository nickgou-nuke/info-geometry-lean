/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-!
# GKSL Semigroup, Gibbs Relaxation, Spin Cumulants & Spohn Entropy Production ($\mathcal{G}_1$–$\mathcal{G}_7$)

This module formalizes the bounded acyclic causal poset $(\mathcal{G}, \preceq)$ unifying
algebraic GKSL dissipation, the two-state Witt CAR thermal Lindblad semigroup on $M_2(\mathbb{C})$,
the dually flat spin cumulant Legendre–BKM manifold, diagonal binary KL / qubit Umegaki relative
entropy, and Spohn's entropy production identity:

* $\mathcal{G}_1$: Algebraic $\star$-ring GKSL generator `gkslGen2`, dual `heisenbergDissipator2`,
  $\star$-preservation, unitality,
  Lindblad's quantum carré du champ defect `2 * (star ⁅L, A⁆ * ⁅L, A⁆)`, and cyclic trace zero.
* $\mathcal{G}_2$: Witt CAR ladder $F_\pm$, Pauli grading $\Gamma_1$, Boltzmann weights $p_\pm(\theta)$,
  KMS detailed balance $\gamma_+ e^{-\theta} = \gamma_- e^\theta$, operator-level generator
  `thermalLindbladianOp` equal to `thermalLindbladianC`, and unique unit-trace Gibbs stationary
  state $\rho_{\mathrm{Gibbs}}(\theta)$.
* $\mathcal{G}_3$: Exact Quantum Markov Semigroup $T_t$ on $M_2(\mathbb{C})$ with explicit 4-channel
  trace-preserving Kraus representation (`∑ k, K_k† K_k = 1` for $\gamma, t \ge 0$), semigroup law
  $T_s \circ T_t = T_{s+t}$, Gibbs invariance, trace preservation, and longitudinal spin readout
  `Tr(T_t(ρ) Γ₁).re = etaTraj`.
* $\mathcal{G}_4$–$\mathcal{G}_5$: Spin cumulant hierarchy ($\kappa_1, \kappa_2, \kappa_3$) of
  $\psi(\theta) = \log(e^\theta + e^{-\theta})$ and dually flat Legendre–Fenchel reciprocity with
  the binary Boltzmann negentropy $\phi(\eta)$ and Fisher metric inversion $\psi'' \cdot \phi'' = 1$.
* $\mathcal{G}_6$: Binary KL / diagonal qubit Umegaki Bregman divergence $D_\phi(\eta_1 \| \eta_2)$,
  duality with $D_\psi$, nonnegativity & equality characterization, Jeffreys symmetrization, and the
  dually flat generalized Pythagorean theorem.
* $\mathcal{G}_7$: Master thermodynamic synthesis — affine $m$-geodesic invariance $\eta(t) \in (-1, 1)$,
  relaxation ODE, Spohn's exact entropy production identity
  $\frac{d}{dt} D_\phi(\eta(t) \| \eta_\theta) = -\gamma(D_\phi(\eta(t)\|\eta_\theta) + D_\phi(\eta_\theta\|\eta(t))) \le 0$,
  asymptotic spin limit $\eta(t) \to \eta_\theta$, and asymptotic free-energy limit $D_\phi(\eta(t)\|\eta_\theta) \to 0$.

Scope note: `bregmanPhi` models the two-state binary KL / diagonal qubit Umegaki relative entropy
in the longitudinal spin polarization coordinate $\eta \in (-1, 1)$ (equivalently diagonal density
matrices in the $\Gamma_1$-eigenbasis), while full off-diagonal matrix dynamics on $M_2(\mathbb{C})$
are carried by `thermalLindbladianOp` and `thermalSemigroupC`.
-/

open Matrix BigOperators Filter Topology

noncomputable section

namespace InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants

attribute [local instance 100] LieRing.ofAssociativeRing

/-!
## Causal Poset of Archetypes $(\mathcal{G}, \preceq)$
-/

section CausalPoset

/-- Nodes of the bounded acyclic causal poset $(\mathcal{G}, \preceq)$ for the GKSL–Spohn synthesis. -/
inductive GKSLSpohnArchetype
  | G1
  | G2
  | G3
  | G4
  | G5
  | G6
  | G7
  deriving DecidableEq, Repr, Inhabited

/-- Reachability relation matching the Hasse diagram:
`G1 ≤ G2 ≤ G3 ≤ G7` and `G4 ≤ G5 ≤ G6 ≤ G7`. -/
def gkslPosetLE : GKSLSpohnArchetype → GKSLSpohnArchetype → Prop
  | .G1, .G1 => True
  | .G1, .G2 => True
  | .G1, .G3 => True
  | .G1, .G7 => True
  | .G2, .G2 => True
  | .G2, .G3 => True
  | .G2, .G7 => True
  | .G3, .G3 => True
  | .G3, .G7 => True
  | .G4, .G4 => True
  | .G4, .G5 => True
  | .G4, .G6 => True
  | .G4, .G7 => True
  | .G5, .G5 => True
  | .G5, .G6 => True
  | .G5, .G7 => True
  | .G6, .G6 => True
  | .G6, .G7 => True
  | .G7, .G7 => True
  | _, _ => False

instance : DecidableRel gkslPosetLE := fun a b => by
  cases a <;> cases b <;> simp only [gkslPosetLE] <;> infer_instance

instance : PartialOrder GKSLSpohnArchetype where
  le := gkslPosetLE
  le_refl a := by cases a <;> simp [gkslPosetLE]
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp_all [gkslPosetLE]
  le_antisymm a b hab hba := by
    cases a <;> cases b <;> simp_all [gkslPosetLE]

/-- `G7` is the supremum of all nodes: every node lies below it, and any common
upper bound of all nodes lies above `G7`. -/
theorem gkslPoset_G7_is_supremum :
    (∀ g : GKSLSpohnArchetype, g ≤ .G7) ∧
    (∀ h : GKSLSpohnArchetype, (∀ g : GKSLSpohnArchetype, g ≤ h) → .G7 ≤ h) := by
  constructor
  · intro g
    cases g <;> change True <;> exact True.intro
  · intro h hh
    exact hh .G7

end CausalPoset

/-!
## Archetype $\mathcal{G}_1$: Noncommutative $\star$-Ring GKSL Generator & Lindblad Carré du Champ Dissipation
-/

section ArchetypeG1_AlgebraicGKSLAndDissipation

/-- Division-free (2-scaled) Lindblad dissipator $\mathcal{D}_2(L, \rho) = 2 L \rho L^\star - (L^\star L \rho + \rho L^\star L)$
over any noncommutative $\star$-ring `B`. -/
def lindbladDissipator2 {B : Type*} [Ring B] [StarRing B] (L ρ : B) : B :=
  2 * (L * ρ * star L) - (star L * L * ρ + ρ * (star L * L))

/-- Full division-free GKSL generator $\mathcal{L}_2(J, L, \rho) = \⁅J, \rho⁆ + \mathcal{D}_2(L, \rho)$
for skew-adjoint coherent generator $J^\star = -J$ ($J = -i H$). -/
def gkslGen2 {B : Type*} [Ring B] [StarRing B] (J L ρ : B) : B :=
  ⁅J, ρ⁆ + lindbladDissipator2 L ρ

/-- Dual Heisenberg dissipator $\mathcal{D}_2^\dagger(L, A) = 2 L^\star A L - (L^\star L A + A L^\star L)$. -/
def heisenbergDissipator2 {B : Type*} [Ring B] [StarRing B] (L A : B) : B :=
  2 * (star L * A * L) - (star L * L * A + A * (star L * L))

/-- Real `2 × 2` matrix constructor. -/
def mat2 {α : Type*} (a b c d : α) : Matrix (Fin 2) (Fin 2) α :=
  Matrix.of ![![a, b], ![c, d]]

-- theorem-class: witness
/-- Noncommutativity witness on the complex spin-`1/2` matrix carrier and on real `2 × 2` matrices,
ensuring the algebraic GKSL carrier is genuinely noncommutative. -/
theorem matrix_carriers_noncommutative :
    InfoGeometry.Algebra.FiniteSpin.J_plus * InfoGeometry.Algebra.FiniteSpin.J_minus ≠
      InfoGeometry.Algebra.FiniteSpin.J_minus * InfoGeometry.Algebra.FiniteSpin.J_plus ∧
    mat2 (0 : ℝ) 1 0 0 * mat2 0 0 1 0 ≠ mat2 0 0 1 0 * mat2 0 1 0 0 := by
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simp [InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus,
      Matrix.mul_apply, Fin.sum_univ_two] at h00
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simp [mat2, Matrix.mul_apply, Fin.sum_univ_two] at h00

-- theorem-class: bridge
/-- **Universal Algebraic GKSL Properties over any Noncommutative $\star$-Ring `B`**:
1. Owner identification with `InfoGeometry.Modular.GKSL.dissipatorTerm2`.
2. Hermiticity ($\star$-structure) preservation: $(\mathcal{L}_2(J, L, \rho))^\star = \mathcal{L}_2(J, L, \rho^\star)$ when $J^\star = -J$.
3. Heisenberg unitality: $\mathcal{D}_2^\dagger(L, 1) = 0$.
4. **Lindblad's Exact Algebraic Dissipation (Quantum Carré du Champ) Identity**:
   $\mathcal{D}_2^\dagger(L, A^\star A) - (\mathcal{D}_2^\dagger(L, A^\star) A + A^\star \mathcal{D}_2^\dagger(L, A)) = 2 \⁅L, A⁆^\star \⁅L, A⁆$. -/
@[rep_depth operator]
theorem algebraic_gksl_star_unital_and_carre_du_champ
    {B : Type*} [Ring B] [StarRing B] {J : B} (hJ : star J = -J) (L ρ A : B) :
    star (gkslGen2 J L ρ) = gkslGen2 J L (star ρ) ∧
    heisenbergDissipator2 L (1 : B) = 0 ∧
    heisenbergDissipator2 L (star A * A) -
      (heisenbergDissipator2 L (star A) * A + star A * heisenbergDissipator2 L A) =
      2 * (star ⁅L, A⁆ * ⁅L, A⁆) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [gkslGen2, lindbladDissipator2]
    simp only [Ring.lie_def, star_add, star_sub, star_mul, star_star, star_ofNat, hJ]
    noncomm_ring
  · dsimp [heisenbergDissipator2]; noncomm_ring
  · dsimp [heisenbergDissipator2]
    simp only [Ring.lie_def, star_sub, star_mul]
    noncomm_ring

-- theorem-class: conservation
/-- Cyclic-trace conservation of the matrix GKSL dissipator over any `[Ring B] [StarRing B]`. -/
@[rep_depth operator]
theorem gksl_matrix_cyclic_trace_zero
    {B G : Type*} [Ring B] [StarRing B] [AddCommGroup G]
    (τ : B →+ G) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    {r : ℕ} (L ρ : Matrix (Fin r) (Fin r) B) :
    τ (∑ i : Fin r, lindbladDissipator2 L ρ i i) = 0 := by
  have h_mat_cyc : ∀ X Y : Matrix (Fin r) (Fin r) B,
      τ (∑ i : Fin r, (X * Y) i i) = τ (∑ i : Fin r, (Y * X) i i) := by
    intro X Y
    simp only [Matrix.mul_apply, map_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h_cyc (X j i) (Y i j)))
  dsimp [lindbladDissipator2]
  simp only [two_mul, Matrix.add_apply, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, map_sub, map_add]
  have h1 : τ (∑ i : Fin r, (L * ρ * star L) i i) = τ (∑ i : Fin r, (star L * (L * ρ)) i i) :=
    h_mat_cyc (L * ρ) (star L)
  have h2 : τ (∑ i : Fin r, (ρ * (star L * L)) i i) = τ (∑ i : Fin r, (star L * L * ρ) i i) :=
    h_mat_cyc ρ (star L * L)
  rw [← Matrix.mul_assoc] at h1
  rw [h1, h2]
  abel

end ArchetypeG1_AlgebraicGKSLAndDissipation

/-!
## Archetype $\mathcal{G}_4$ & $\mathcal{G}_5$: Spin Cumulant Hierarchy & Dually Flat Legendre–BKM Geometry
-/

section ArchetypeG4_G5_SpinCumulantsAndLegendreDuality

/-- Canonical partition function $Z(\theta) = \operatorname{Tr}(e^{\theta \Gamma_1}) = e^\theta + e^{-\theta} > 0$. -/
def partitionZ (θ : ℝ) : ℝ := Real.exp θ + Real.exp (-θ)

/-- Primal log-partition / cumulant generating potential $\psi(\theta) = \log(e^\theta + e^{-\theta})$. -/
def cumulantPsi (θ : ℝ) : ℝ := Real.log (partitionZ θ)

/-- First spin cumulant (equilibrium magnetization) $\kappa_1(\theta) = \psi'(\theta) = \tanh\theta \in (-1, 1)$. -/
def meanSpin (θ : ℝ) : ℝ := (Real.exp θ - Real.exp (-θ)) / partitionZ θ

/-- Second spin cumulant (spin variance / Fisher–BKM metric) $\kappa_2(\theta) = \psi''(\theta) = 4 / Z(\theta)^2$. -/
def varSpin (θ : ℝ) : ℝ := 4 / (partitionZ θ) ^ 2

/-- Third spin cumulant (Amari–Chentsov skewness) $\kappa_3(\theta) = \psi'''(\theta) = -2 \eta(\theta) \kappa_2(\theta)$. -/
def skewSpin (θ : ℝ) : ℝ := -2 * meanSpin θ * varSpin θ

/-- Dual von Neumann negentropy potential $\phi(\eta) = \frac{1+\eta}{2}\log\frac{1+\eta}{2} + \frac{1-\eta}{2}\log\frac{1-\eta}{2}$. -/
def negEntropyPhi (η : ℝ) : ℝ :=
  ((1 + η) / 2) * Real.log ((1 + η) / 2) + ((1 - η) / 2) * Real.log ((1 - η) / 2)

/-- Inverse canonical map $\theta(\eta) = \frac{1}{2}\log\frac{1 + \eta}{1 - \eta}$ on $\eta \in (-1, 1)$. -/
def canonicalTheta (η : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log ((1 + η) / (1 - η))

lemma partitionZ_pos (θ : ℝ) : 0 < partitionZ θ := by
  dsimp [partitionZ]; positivity

lemma exp_mul_exp_neg (θ : ℝ) : Real.exp θ * Real.exp (-θ) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

lemma one_add_meanSpin (θ : ℝ) : 1 + meanSpin θ = 2 * Real.exp θ / partitionZ θ := by
  have hZ : partitionZ θ ≠ 0 := ne_of_gt (partitionZ_pos θ)
  dsimp [meanSpin, partitionZ]; field_simp; ring

lemma one_sub_meanSpin (θ : ℝ) : 1 - meanSpin θ = 2 * Real.exp (-θ) / partitionZ θ := by
  have hZ : partitionZ θ ≠ 0 := ne_of_gt (partitionZ_pos θ)
  dsimp [meanSpin, partitionZ]; field_simp; ring

-- theorem-class: bound
/-- Equilibrium magnetization satisfies $-1 < \eta(\theta) < 1$ for every inverse temperature $\theta \in \mathbb{R}$. -/
theorem meanSpin_mem_Ioo (θ : ℝ) : -1 < meanSpin θ ∧ meanSpin θ < 1 := by
  have hZ : 0 < partitionZ θ := partitionZ_pos θ
  have h1 : 0 < 1 + meanSpin θ := by rw [one_add_meanSpin]; positivity
  have h2 : 0 < 1 - meanSpin θ := by rw [one_sub_meanSpin]; positivity
  constructor <;> linarith

-- theorem-class: identity
/-- Spin variance satisfies $\kappa_2(\theta) = 1 - \eta(\theta)^2 > 0$. -/
theorem varSpin_eq_one_sub_sq (θ : ℝ) : varSpin θ = 1 - (meanSpin θ) ^ 2 ∧ 0 < varSpin θ := by
  have hZ : 0 < partitionZ θ := partitionZ_pos θ
  have hZ_ne : partitionZ θ ≠ 0 := ne_of_gt hZ
  refine ⟨?_, by dsimp [varSpin]; positivity⟩
  dsimp [varSpin, meanSpin, partitionZ]
  field_simp
  calc (4 : ℝ) = 4 * (Real.exp θ * Real.exp (-θ)) := by rw [exp_mul_exp_neg, mul_one]
    _ = (Real.exp θ + Real.exp (-θ)) ^ 2 - (Real.exp θ - Real.exp (-θ)) ^ 2 := by ring

-- theorem-class: analytic
/-- **Archetype $\mathcal{G}_4$: Exact Spin Cumulant Hierarchy ($\kappa_1, \kappa_2, \kappa_3$)** via `HasDerivAt`. -/
@[rep_depth thermo]
theorem spin_cumulant_hierarchy_derivatives (θ : ℝ) :
    HasDerivAt cumulantPsi (meanSpin θ) θ ∧
    HasDerivAt meanSpin (varSpin θ) θ ∧
    HasDerivAt varSpin (skewSpin θ) θ := by
  have hZ_pos : 0 < partitionZ θ := partitionZ_pos θ
  have hZ_ne : partitionZ θ ≠ 0 := ne_of_gt hZ_pos
  have hd_neg : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-θ)) θ :=
    ((Real.hasDerivAt_exp (-θ)).comp θ (hasDerivAt_neg θ)).congr_deriv (by ring)
  have hd_Z : HasDerivAt partitionZ (Real.exp θ - Real.exp (-θ)) θ := by
    unfold partitionZ
    exact ((Real.hasDerivAt_exp θ).fun_add hd_neg).congr_deriv (by ring)
  have hd_num : HasDerivAt (fun x : ℝ => Real.exp x - Real.exp (-x)) (partitionZ θ) θ := by
    have h := (Real.hasDerivAt_exp θ).fun_sub hd_neg
    exact h.congr_deriv (by dsimp [partitionZ]; ring)
  have hd_psi : HasDerivAt cumulantPsi (meanSpin θ) θ := by
    unfold cumulantPsi
    exact hd_Z.log hZ_ne
  have hd_mean : HasDerivAt meanSpin (varSpin θ) θ := by
    unfold meanSpin
    have hq := hd_num.fun_div hd_Z hZ_ne
    have h_eq : (partitionZ θ * partitionZ θ -
        (Real.exp θ - Real.exp (-θ)) * (Real.exp θ - Real.exp (-θ))) / partitionZ θ ^ 2 =
        varSpin θ := by
      dsimp [varSpin, partitionZ]
      congr 1
      calc (Real.exp θ + Real.exp (-θ)) * (Real.exp θ + Real.exp (-θ)) -
            (Real.exp θ - Real.exp (-θ)) * (Real.exp θ - Real.exp (-θ))
        _ = 4 * (Real.exp θ * Real.exp (-θ)) := by ring
        _ = 4 := by rw [exp_mul_exp_neg, mul_one]
    exact hq.congr_deriv h_eq
  have hd_var : HasDerivAt varSpin (skewSpin θ) θ := by
    have h_fn : varSpin = fun x => 1 - meanSpin x * meanSpin x := by
      ext x; rw [(varSpin_eq_one_sub_sq x).1, pow_two]
    rw [h_fn]
    have hp := (hasDerivAt_const θ (1 : ℝ)).fun_sub (hd_mean.fun_mul hd_mean)
    exact hp.congr_deriv (by dsimp [skewSpin]; ring)
  exact ⟨hd_psi, hd_mean, hd_var⟩

-- theorem-class: duality
/-- **Archetype $\mathcal{G}_5$: Dually Flat Legendre–Fenchel Reciprocity & Fisher–BKM Metric Inversion**. -/
@[rep_depth thermo]
theorem dually_flat_legendre_reciprocity_and_metric_inversion :
    (∀ θ : ℝ, canonicalTheta (meanSpin θ) = θ) ∧
    (∀ η : ℝ, -1 < η → η < 1 → meanSpin (canonicalTheta η) = η) ∧
    (∀ θ : ℝ, cumulantPsi θ + negEntropyPhi (meanSpin θ) = θ * meanSpin θ) ∧
    (∀ η : ℝ, -1 < η → η < 1 → HasDerivAt negEntropyPhi (canonicalTheta η) η) ∧
    (∀ η : ℝ, -1 < η → η < 1 → HasDerivAt canonicalTheta (1 / (1 - η ^ 2)) η) ∧
    (∀ θ : ℝ, varSpin θ * (1 / (1 - (meanSpin θ) ^ 2)) = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ
    have hZ_ne : partitionZ θ ≠ 0 := ne_of_gt (partitionZ_pos θ)
    have h_exp_neg_ne : Real.exp (-θ) ≠ 0 := ne_of_gt (Real.exp_pos (-θ))
    dsimp [canonicalTheta]
    rw [one_add_meanSpin, one_sub_meanSpin]
    have h_div : (2 * Real.exp θ / partitionZ θ) / (2 * Real.exp (-θ) / partitionZ θ) =
        Real.exp (2 * θ) := by
      have h1 : (2 * Real.exp θ / partitionZ θ) / (2 * Real.exp (-θ) / partitionZ θ) =
          Real.exp θ / Real.exp (-θ) := by field_simp
      rw [h1, ← Real.exp_sub]
      congr 1; ring
    rw [h_div, Real.log_exp]; ring
  · intro η h_lo h_hi
    have h1 : 0 < 1 + η := by linarith
    have h2 : 0 < 1 - η := by linarith
    have hr : 0 < (1 + η) / (1 - η) := div_pos h1 h2
    let s := Real.sqrt ((1 + η) / (1 - η))
    have hs_pos : 0 < s := Real.sqrt_pos.mpr hr
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    have h_th : canonicalTheta η = Real.log s := by
      dsimp [canonicalTheta, s]; rw [Real.log_sqrt (le_of_lt hr)]; ring
    have hexp_pos : Real.exp (canonicalTheta η) = s := by
      rw [h_th, Real.exp_log hs_pos]
    have hexp_neg : Real.exp (-canonicalTheta η) = s⁻¹ := by
      rw [Real.exp_neg, hexp_pos]
    dsimp [meanSpin, partitionZ]
    rw [hexp_pos, hexp_neg]
    have h_alg : (s - s⁻¹) / (s + s⁻¹) = (s ^ 2 - 1) / (s ^ 2 + 1) := by
      have h_denom : s + s⁻¹ ≠ 0 := ne_of_gt (add_pos hs_pos (inv_pos.mpr hs_pos))
      have h_denom2 : s ^ 2 + 1 ≠ 0 := by positivity
      field_simp
    rw [h_alg, Real.sq_sqrt (le_of_lt hr)]
    field_simp; ring
  · intro θ
    have hZ_pos : 0 < partitionZ θ := partitionZ_pos θ
    have hp1 : (1 + meanSpin θ) / 2 = Real.exp θ / partitionZ θ := by
      rw [one_add_meanSpin]; ring
    have hp2 : (1 - meanSpin θ) / 2 = Real.exp (-θ) / partitionZ θ := by
      rw [one_sub_meanSpin]; ring
    dsimp [negEntropyPhi, cumulantPsi]
    rw [hp1, hp2,
        Real.log_div (ne_of_gt (Real.exp_pos θ)) (ne_of_gt hZ_pos),
        Real.log_div (ne_of_gt (Real.exp_pos (-θ))) (ne_of_gt hZ_pos),
        Real.log_exp, Real.log_exp]
    dsimp [meanSpin, partitionZ]
    have hZ_ne : Real.exp θ + Real.exp (-θ) ≠ 0 := ne_of_gt hZ_pos
    field_simp; ring
  · intro η h_lo h_hi
    have hp1 : 0 < (1 + η) / 2 := by linarith
    have hp2 : 0 < (1 - η) / 2 := by linarith
    have hxlog : ∀ {x : ℝ}, x ≠ 0 → HasDerivAt (fun u : ℝ => u * Real.log u) (Real.log x + 1) x := by
      intro x hx
      have h := (hasDerivAt_id x).fun_mul (Real.hasDerivAt_log hx)
      exact h.congr_deriv (by simp [hx])
    have hf1 : HasDerivAt (fun u : ℝ => (1 + u) / 2) (1 / 2) η :=
      (((hasDerivAt_const η (1 : ℝ)).fun_add (hasDerivAt_id η)).div_const 2).congr_deriv (by ring)
    have hf2 : HasDerivAt (fun u : ℝ => (1 - u) / 2) (-1 / 2) η :=
      (((hasDerivAt_const η (1 : ℝ)).fun_sub (hasDerivAt_id η)).div_const 2).congr_deriv (by ring)
    have hd1 := (hxlog (ne_of_gt hp1)).comp η hf1
    have hd2 := (hxlog (ne_of_gt hp2)).comp η hf2
    have hsum : HasDerivAt (fun u : ℝ => ((1 + u) / 2) * Real.log ((1 + u) / 2) +
        ((1 - u) / 2) * Real.log ((1 - u) / 2))
        ((Real.log ((1 + η) / 2) + 1) * (1 / 2) + (Real.log ((1 - η) / 2) + 1) * (-1 / 2)) η :=
      hd1.fun_add hd2
    have h_val : (Real.log ((1 + η) / 2) + 1) * (1 / 2) +
        (Real.log ((1 - η) / 2) + 1) * (-1 / 2) = canonicalTheta η := by
      have h_eq_div : ((1 + η) / 2) / ((1 - η) / 2) = (1 + η) / (1 - η) := by
        have : 1 - η ≠ 0 := by linarith
        field_simp
      dsimp [canonicalTheta]
      rw [← h_eq_div, Real.log_div (ne_of_gt hp1) (ne_of_gt hp2)]
      ring
    unfold negEntropyPhi
    exact hsum.congr_deriv h_val
  · intro η h_lo h_hi
    have h1 : 1 + η ≠ 0 := by linarith
    have h2 : 1 - η ≠ 0 := by linarith
    have h_fn : ∀ᶠ u in 𝓝 η, canonicalTheta u = (1 / 2 : ℝ) * (Real.log (1 + u) - Real.log (1 - u)) := by
      have h_open : IsOpen { u : ℝ | -1 < u ∧ u < 1 } := isOpen_lt continuous_const continuous_id |>.inter
        (isOpen_lt continuous_id continuous_const)
      filter_upwards [h_open.mem_nhds ⟨h_lo, h_hi⟩] with u ⟨hu1, hu2⟩
      dsimp [canonicalTheta]
      rw [Real.log_div (by linarith) (by linarith)]
    have hd1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + η)) η := by
      have h := (Real.hasDerivAt_log h1).comp η ((hasDerivAt_const η (1 : ℝ)).fun_add (hasDerivAt_id η))
      exact h.congr_deriv (by ring)
    have hd2 : HasDerivAt (fun u : ℝ => Real.log (1 - u)) (-1 / (1 - η)) η := by
      have h := (Real.hasDerivAt_log h2).comp η ((hasDerivAt_const η (1 : ℝ)).fun_sub (hasDerivAt_id η))
      exact h.congr_deriv (by ring)
    have hd_diff := (hd1.fun_sub hd2).const_mul (1 / 2 : ℝ)
    have h_alg : (1 / 2 : ℝ) * (1 / (1 + η) - -1 / (1 - η)) = 1 / (1 - η ^ 2) := by
      have h_sq : 1 - η ^ 2 ≠ 0 := by nlinarith
      field_simp; ring
    rw [h_alg] at hd_diff
    exact hd_diff.congr_of_eventuallyEq h_fn
  · intro θ
    rcases varSpin_eq_one_sub_sq θ with ⟨h_eq, h_pos⟩
    rw [h_eq] at h_pos
    rw [h_eq]
    exact mul_one_div_cancel (ne_of_gt h_pos)

end ArchetypeG4_G5_SpinCumulantsAndLegendreDuality

/-!
## Archetype $\mathcal{G}_6$: Bregman–Umegaki Relative Entropy, Strict Positivity & Pythagorean Theorem
-/

section ArchetypeG6_BregmanUmegakiAndPythagoras

/-- Primal Bregman divergence $D_\psi(\theta_1 \| \theta_2) = \psi(\theta_1) - \psi(\theta_2) - \eta(\theta_2)(\theta_1 - \theta_2)$. -/
def bregmanPsi (θ₁ θ₂ : ℝ) : ℝ :=
  cumulantPsi θ₁ - cumulantPsi θ₂ - meanSpin θ₂ * (θ₁ - θ₂)

/-- Dual Bregman / diagonal two-state Umegaki relative entropy
$D_\phi(\eta_1 \| \eta_2) = \phi(\eta_1) - \phi(\eta_2) - \theta(\eta_2)(\eta_1 - \eta_2)$. -/
def bregmanPhi (η₁ η₂ : ℝ) : ℝ :=
  negEntropyPhi η₁ - negEntropyPhi η₂ - canonicalTheta η₂ * (η₁ - η₂)

-- theorem-class: divergence
/-- **Archetype $\mathcal{G}_6$: Bregman Duality, Strict Gibbs Positivity, Jeffreys Symmetrization & Pythagorean Theorem**. -/
@[rep_depth thermo]
theorem bregman_umegaki_positivity_and_pythagorean_theorem :
    (∀ θ₁ θ₂ : ℝ, bregmanPsi θ₂ θ₁ = bregmanPhi (meanSpin θ₁) (meanSpin θ₂) ∧
      bregmanPhi (meanSpin θ₁) (meanSpin θ₂) =
        cumulantPsi θ₂ + negEntropyPhi (meanSpin θ₁) - θ₂ * meanSpin θ₁) ∧
    (∀ η₁ η₂ : ℝ, -1 < η₁ → η₁ < 1 → -1 < η₂ → η₂ < 1 →
      0 ≤ bregmanPhi η₁ η₂ ∧ (bregmanPhi η₁ η₂ = 0 ↔ η₁ = η₂)) ∧
    (∀ η₁ η₂ : ℝ, bregmanPhi η₁ η₂ + bregmanPhi η₂ η₁ =
      (canonicalTheta η₁ - canonicalTheta η₂) * (η₁ - η₂)) ∧
    (∀ η₁ η₂ η₃ : ℝ,
      bregmanPhi η₁ η₃ = bregmanPhi η₁ η₂ + bregmanPhi η₂ η₃ +
        (η₁ - η₂) * (canonicalTheta η₂ - canonicalTheta η₃)) := by
  rcases dually_flat_legendre_reciprocity_and_metric_inversion with
    ⟨h_th_mean, _, h_young, _, _, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ₁ θ₂
    have hy1 := h_young θ₁
    have hy2 := h_young θ₂
    have ht2 := h_th_mean θ₂
    dsimp [bregmanPsi, bregmanPhi]
    rw [ht2]
    constructor <;> linarith
  · intro η₁ η₂ h1_lo h1_hi h2_lo h2_hi
    let p₁ := (1 + η₁) / 2
    let p₂ := (1 - η₁) / 2
    let q₁ := (1 + η₂) / 2
    let q₂ := (1 - η₂) / 2
    have hp₁ : 0 < p₁ := by dsimp [p₁]; linarith
    have hp₂ : 0 < p₂ := by dsimp [p₂]; linarith
    have hq₁ : 0 < q₁ := by dsimp [q₁]; linarith
    have hq₂ : 0 < q₂ := by dsimp [q₂]; linarith
    have h_kl : bregmanPhi η₁ η₂ = p₁ * Real.log (p₁ / q₁) + p₂ * Real.log (p₂ / q₂) := by
      have h_div2 : q₁ / q₂ = (1 + η₂) / (1 - η₂) := by
        dsimp [q₁, q₂]; have : 1 - η₂ ≠ 0 := by linarith
        field_simp
      have h_th2 : canonicalTheta η₂ = (1 / 2 : ℝ) * (Real.log q₁ - Real.log q₂) := by
        dsimp [canonicalTheta]; rw [← h_div2, Real.log_div (ne_of_gt hq₁) (ne_of_gt hq₂)]
      dsimp [bregmanPhi, negEntropyPhi, p₁, p₂, q₁, q₂] at h_th2 ⊢
      rw [h_th2,
          Real.log_div (ne_of_gt hp₁) (ne_of_gt hq₁),
          Real.log_div (ne_of_gt hp₂) (ne_of_gt hq₂)]
      ring
    rw [h_kl]
    have h_term : ∀ {p q : ℝ} (hp : 0 < p) (hq : 0 < q),
        p - q ≤ p * Real.log (p / q) := by
      intro p q hp hq
      have h_ineq := Real.add_one_le_exp (Real.log (q / p))
      rw [Real.exp_log (div_pos hq hp)] at h_ineq
      have h_mul := mul_le_mul_of_nonneg_left h_ineq (le_of_lt hp)
      have h_rhs : p * (q / p) = q := mul_div_cancel₀ q (ne_of_gt hp)
      have h_log_swap : Real.log (q / p) = -Real.log (p / q) := by
        rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp),
            Real.log_div (ne_of_gt hp) (ne_of_gt hq)]; ring
      rw [h_rhs, h_log_swap] at h_mul
      linarith
    have h_nonneg : 0 ≤ p₁ * Real.log (p₁ / q₁) + p₂ * Real.log (p₂ / q₂) := by
      have b1 := h_term hp₁ hq₁
      have b2 := h_term hp₂ hq₂
      have h_sum : (p₁ - q₁) + (p₂ - q₂) = 0 := by dsimp [p₁, p₂, q₁, q₂]; ring
      linarith
    refine ⟨h_nonneg, ?_⟩
    constructor
    · intro h_eq0
      by_contra h_ne
      have hp1_ne : q₁ / p₁ ≠ 1 := by
        intro h1
        have hpq : q₁ = p₁ := (div_eq_one_iff_eq (ne_of_gt hp₁)).mp h1
        dsimp [p₁, q₁] at hpq
        exact h_ne (by linarith)
      have hlog_ne : Real.log (q₁ / p₁) ≠ 0 := by
        intro h0
        have := congr_arg Real.exp h0
        rw [Real.exp_log (div_pos hq₁ hp₁), Real.exp_zero] at this
        exact hp1_ne this
      have h_strict := Real.add_one_lt_exp hlog_ne
      rw [Real.exp_log (div_pos hq₁ hp₁)] at h_strict
      have h_mul1 := mul_lt_mul_of_pos_left h_strict hp₁
      rw [mul_div_cancel₀ q₁ (ne_of_gt hp₁)] at h_mul1
      have h_log_swap1 : Real.log (q₁ / p₁) = -Real.log (p₁ / q₁) := by
        rw [Real.log_div (ne_of_gt hq₁) (ne_of_gt hp₁),
            Real.log_div (ne_of_gt hp₁) (ne_of_gt hq₁)]; ring
      rw [h_log_swap1] at h_mul1
      have b2 := h_term hp₂ hq₂
      have h_sum : (p₁ - q₁) + (p₂ - q₂) = 0 := by dsimp [p₁, p₂, q₁, q₂]; ring
      linarith
    · rintro rfl
      rw [show q₁ = p₁ from rfl, show q₂ = p₂ from rfl, div_self (ne_of_gt hp₁),
        div_self (ne_of_gt hp₂), Real.log_one]
      ring
  · intro η₁ η₂
    dsimp [bregmanPhi]; ring
  · intro η₁ η₂ η₃
    dsimp [bregmanPhi]; ring

end ArchetypeG6_BregmanUmegakiAndPythagoras

/-!
## Archetype $\mathcal{G}_2, \mathcal{G}_3$ & $\mathcal{G}_7$: Witt CAR Thermal GKSL Semigroup, Gibbs Limit & Spohn's Law
-/

section ArchetypeG2_G3_G7_ThermalGKSLSemigroupAndSpohnSynthesis

lemma ext_mat2 {α : Type*} {M N : Matrix (Fin 2) (Fin 2) α}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

@[simp] lemma mat2_00 {α : Type*} (a b c d : α) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 {α : Type*} (a b c d : α) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 {α : Type*} (a b c d : α) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 {α : Type*} (a b c d : α) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 {α : Type*} [Ring α] (M N : Matrix (Fin 2) (Fin 2) α) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 {α : Type*} [Ring α] (M N : Matrix (Fin 2) (Fin 2) α) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 {α : Type*} [Ring α] (M N : Matrix (Fin 2) (Fin 2) α) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 {α : Type*} [Ring α] (M N : Matrix (Fin 2) (Fin 2) α) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma trace_fin2 {α : Type*} [AddCommMonoid α] (M : Matrix (Fin 2) (Fin 2) α) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

/-- Witt CAR creation ladder $F_+ = \bigl(\begin{smallmatrix} 0 & 1 \\ 0 & 0 \end{smallmatrix}\bigr)$ via `FiniteSpin.J_plus`. -/
def wittFPlus : InfoGeometry.Algebra.FiniteSpin.Mat2C :=
  InfoGeometry.Algebra.FiniteSpin.J_plus

/-- Witt CAR annihilation ladder $F_- = F_+^\dagger = \bigl(\begin{smallmatrix} 0 & 0 \\ 1 & 0 \end{smallmatrix}\bigr)$ via `FiniteSpin.J_minus`. -/
def wittFMinus : InfoGeometry.Algebra.FiniteSpin.Mat2C :=
  InfoGeometry.Algebra.FiniteSpin.J_minus

/-- Pauli grading $\Gamma_1 = \operatorname{diag}(1, -1) = 2 J_z$ via `FiniteSpin.J_zero`. -/
def pauliGamma1 : InfoGeometry.Algebra.FiniteSpin.Mat2C :=
  (2 : ℂ) • InfoGeometry.Algebra.FiniteSpin.J_zero

-- theorem-class: structure
/-- Explicit noncommutativity witness for every nontrivial coefficient ring's
full two-by-two matrix algebra. The two matrix units multiply in opposite
orders to different diagonal matrix units. -/
theorem mat2_noncommutative {α : Type*} [Ring α] [Nontrivial α] :
    ∃ A B : Matrix (Fin 2) (Fin 2) α, A * B ≠ B * A := by
  refine ⟨mat2 (0 : α) 1 0 0, mat2 (0 : α) 0 1 0, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) α => M 0 0) h
  simp only [mul2_00, mat2_00, mat2_01, mat2_10, mul_zero, add_zero, zero_add, one_mul] at h00
  exact one_ne_zero h00

-- theorem-class: structure
/-- The thermal ladder operators fail to commute on their actual carrier
`Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem wittCAR_ladder_noncommutative :
    wittFPlus * wittFMinus ≠ wittFMinus * wittFPlus := by
  intro h
  have h00 : (wittFPlus * wittFMinus) 0 0 = (wittFMinus * wittFPlus) 0 0 :=
    congrArg (fun M => M 0 0) h
  simp only [mul2_00, wittFPlus, wittFMinus, InfoGeometry.Algebra.FiniteSpin.J_plus,
    InfoGeometry.Algebra.FiniteSpin.J_minus, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, add_zero, zero_add, one_mul] at h00
  exact one_ne_zero h00

/-- Equilibrium Boltzmann probabilities $p_\pm(\theta) = \frac{1 \pm \eta(\theta)}{2} = \frac{e^{\pm\theta}}{Z(\theta)}$. -/
def boltzmannPlus (θ : ℝ) : ℝ := (1 + meanSpin θ) / 2
def boltzmannMinus (θ : ℝ) : ℝ := (1 - meanSpin θ) / 2

/-- KMS upward and downward transition rates $\gamma_\pm(\gamma, \theta) = \gamma\,p_\pm(\theta)$. -/
def ratePlus (γ θ : ℝ) : ℝ := γ * boltzmannPlus θ
def rateMinus (γ θ : ℝ) : ℝ := γ * boltzmannMinus θ

/-- Canonical Gibbs density matrix $\rho_{\mathrm{Gibbs}}(\theta) = \mathrm{diag}(p_+(\theta), p_-(\theta)) \in M_2(\mathbb{C})$. -/
def gibbsDensityC (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  mat2 (boltzmannPlus θ : ℂ) 0 0 (boltzmannMinus θ : ℂ)

/-- Operator-algebraic Witt CAR thermal GKSL generator
$\mathcal{L}_{\gamma,\omega,\theta}(\rho) = -\frac{i\omega}{2}[\Gamma_1, \rho] + \frac{\gamma_+}{2}\mathcal{D}_2(F_+, \rho) + \frac{\gamma_-}{2}\mathcal{D}_2(F_-, \rho)$. -/
def thermalLindbladianOp (γ ω θ : ℝ) (ρ : InfoGeometry.Algebra.FiniteSpin.Mat2C) :
    InfoGeometry.Algebra.FiniteSpin.Mat2C :=
  (-(Complex.I * (ω : ℂ) / 2)) • ⁅pauliGamma1, ρ⁆ +
    (((ratePlus γ θ : ℂ) / 2) • lindbladDissipator2 wittFPlus ρ +
     ((rateMinus γ θ : ℂ) / 2) • lindbladDissipator2 wittFMinus ρ)

/-- Thermal Witt CAR Lindbladian $\mathcal{L}_{\gamma, \omega, \theta}(\rho)$ in explicit coordinates on $M_2(\mathbb{C})$. -/
def thermalLindbladianC (γ ω θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let g_plus  : ℂ := ratePlus γ θ
  let g_minus : ℂ := rateMinus γ θ
  let dec_p   : ℂ := (γ / 2 : ℝ) + Complex.I * ω
  let dec_m   : ℂ := (γ / 2 : ℝ) - Complex.I * ω
  mat2 (-g_minus * ρ 0 0 + g_plus * ρ 1 1) (-dec_p * ρ 0 1)
       (-dec_m * ρ 1 0) (g_minus * ρ 0 0 - g_plus * ρ 1 1)

/-- Integrated Quantum Markov Semigroup $T_t(\gamma, \omega, \theta, \rho)$ on $M_2(\mathbb{C})$. -/
def thermalSemigroupC (γ ω θ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let tr_ρ  : ℂ := ρ 0 0 + ρ 1 1
  let p_p   : ℂ := boltzmannPlus θ
  let p_m   : ℂ := boltzmannMinus θ
  let e_pop : ℂ := Real.exp (-γ * t)
  let e_coh : ℂ := Real.exp (-(γ / 2) * t)
  let ph_p  : ℂ := Complex.exp (-Complex.I * ω * t)
  let ph_m  : ℂ := Complex.exp (Complex.I * ω * t)
  mat2 (p_p * tr_ρ + e_pop * (ρ 0 0 - p_p * tr_ρ)) (e_coh * ph_p * ρ 0 1)
       (e_coh * ph_m * ρ 1 0) (p_m * tr_ρ + e_pop * (ρ 1 1 - p_m * tr_ρ))

/-- Four Choi–Kraus operators realizing $T_t(\gamma, \omega, \theta, \cdot)$ as a completely
positive trace-preserving channel for all $\gamma \ge 0$ and $t \ge 0$. -/
def thermalKraus (γ ω θ t : ℝ) : Fin 4 → InfoGeometry.Algebra.FiniteSpin.Mat2C
  | 0 =>
      mat2 ((Real.sqrt (boltzmannPlus θ) : ℂ) *
              Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)))
           0 0
           ((Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (Real.exp (-γ * t)) : ℂ) *
              Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)))
  | 1 =>
      mat2 0 ((Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (1 - Real.exp (-γ * t)) : ℂ)) 0 0
  | 2 =>
      mat2 ((Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (Real.exp (-γ * t)) : ℂ) *
              Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)))
           0 0
           ((Real.sqrt (boltzmannMinus θ) : ℂ) *
              Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)))
  | 3 =>
      mat2 0 0 ((Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (1 - Real.exp (-γ * t)) : ℂ)) 0

/-- Affine $m$-geodesic spin expectation trajectory $\eta(t) = \eta(\theta) + e^{-\gamma t}(\eta_0 - \eta(\theta))$. -/
def etaTraj (γ θ η₀ t : ℝ) : ℝ :=
  meanSpin θ + Real.exp (-γ * t) * (η₀ - meanSpin θ)

lemma boltzmann_sum_and_diff (θ : ℝ) :
    boltzmannPlus θ + boltzmannMinus θ = 1 ∧
    boltzmannPlus θ - boltzmannMinus θ = meanSpin θ := by
  dsimp [boltzmannPlus, boltzmannMinus]
  constructor <;> ring

lemma boltzmann_nonneg (θ : ℝ) : 0 < boltzmannPlus θ ∧ 0 < boltzmannMinus θ := by
  rcases meanSpin_mem_Ioo θ with ⟨h_lo, h_hi⟩
  dsimp [boltzmannPlus, boltzmannMinus]
  constructor <;> linarith

-- theorem-class: identity
/-- The operator-algebraic Witt CAR Lindbladian `thermalLindbladianOp` equals the coordinate
matrix operator `thermalLindbladianC` everywhere on $M_2(\mathbb{C})$. -/
@[rep_depth transport]
theorem thermalLindbladianOp_eq_thermalLindbladianC
    (γ ω θ : ℝ) (ρ : InfoGeometry.Algebra.FiniteSpin.Mat2C) :
    thermalLindbladianOp γ ω θ ρ = thermalLindbladianC γ ω θ ρ := by
  have h_bsum : (boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ) = 1 := by
    exact_mod_cast (boltzmann_sum_and_diff θ).1
  have h_rate_sum : (ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ) = (γ : ℂ) := by
    dsimp [ratePlus, rateMinus]
    push_cast
    calc (γ : ℂ) * boltzmannPlus θ + (γ : ℂ) * boltzmannMinus θ
      _ = (γ : ℂ) * (boltzmannPlus θ + boltzmannMinus θ) := by ring
      _ = (γ : ℂ) := by rw [h_bsum, mul_one]
  dsimp [thermalLindbladianOp, thermalLindbladianC, pauliGamma1, wittFPlus, wittFMinus,
    lindbladDissipator2, Ring.lie_def]
  apply ext_mat2 <;>
    simp only [mat2_00, mat2_01, mat2_10, mat2_11,
      InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus,
      InfoGeometry.Algebra.FiniteSpin.J_zero, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, two_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      star_zero, star_one, mul_zero, zero_mul, add_zero, zero_add]
  · ring
  · push_cast
    linear_combination -(ρ 0 1 / 2) * h_rate_sum
  · push_cast
    linear_combination -(ρ 1 0 / 2) * h_rate_sum
  · ring

-- theorem-class: structure
/-- **Explicit CPTP Kraus Representation of $T_t(\gamma, \omega, \theta, \cdot)$**:
For all $\gamma \ge 0$ and $t \ge 0$, the semigroup propagator equals the 4-channel operator-sum
`∑ k : Fin 4, K_k * ρ * star (K_k)` with exact trace-preserving completeness
`∑ k : Fin 4, star (K_k) * K_k = 1`. -/
@[rep_depth transport]
theorem thermalSemigroupC_kraus_sum_and_unital
    {γ ω θ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    (∀ ρ : InfoGeometry.Algebra.FiniteSpin.Mat2C,
      thermalSemigroupC γ ω θ t ρ =
        ∑ k : Fin 4, thermalKraus γ ω θ t k * ρ * star (thermalKraus γ ω θ t k)) ∧
    (∑ k : Fin 4, star (thermalKraus γ ω θ t k) * thermalKraus γ ω θ t k = 1) := by
  rcases boltzmann_nonneg θ with ⟨hp_pos, hm_pos⟩
  have he_nonneg : 0 ≤ Real.exp (-γ * t) := le_of_lt (Real.exp_pos _)
  have he_le1 : Real.exp (-γ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h1e_nonneg : 0 ≤ 1 - Real.exp (-γ * t) := sub_nonneg.mpr he_le1
  have h_bp_sq : (Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (boltzmannPlus θ) : ℂ) =
      (boltzmannPlus θ : ℂ) := by
    norm_cast; exact Real.mul_self_sqrt (le_of_lt hp_pos)
  have h_bm_sq : (Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (boltzmannMinus θ) : ℂ) =
      (boltzmannMinus θ : ℂ) := by
    norm_cast; exact Real.mul_self_sqrt (le_of_lt hm_pos)
  have h_ep_sq : (Real.sqrt (Real.exp (-γ * t)) : ℂ) * (Real.sqrt (Real.exp (-γ * t)) : ℂ) =
      (Real.exp (-γ * t) : ℂ) := by
    norm_cast; exact Real.mul_self_sqrt he_nonneg
  have h_1e_sq : (Real.sqrt (1 - Real.exp (-γ * t)) : ℂ) * (Real.sqrt (1 - Real.exp (-γ * t)) : ℂ) =
      (1 - Real.exp (-γ * t) : ℂ) := by
    norm_cast; exact Real.mul_self_sqrt h1e_nonneg
  have h_sqrt_ep_eq_ecoh : (Real.sqrt (Real.exp (-γ * t)) : ℂ) = (Real.exp (-(γ / 2) * t) : ℂ) := by
    norm_cast
    rw [← Real.exp_half (-γ * t)]
    congr 1; ring
  have h_bsum : (boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ) = 1 := by
    exact_mod_cast (boltzmann_sum_and_diff θ).1
  have hα_star : star (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) =
      Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [map_mul, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  have hαc_star : star (Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) =
      Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [map_mul, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  have hα_mul_αc : Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
      Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have h0 : -Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ) +
        Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ) = 0 := by ring
    rw [h0, Complex.exp_zero]
  have hα_sq : Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
      Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) =
      Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hαc_sq : Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
      Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) =
      Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h_star_real : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => by
    simp [Complex.conj_ofReal]
  refine ⟨?_, ?_⟩
  · intro ρ
    rw [Fin.sum_univ_four]
    dsimp [thermalSemigroupC, thermalKraus]
    apply ext_mat2
    · simp only [Matrix.add_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_two, mat2_00, mat2_01, star_mul, star_zero,
        mul_zero, zero_mul, add_zero, zero_add, h_star_real, hα_star]
      trans ((Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (boltzmannPlus θ) : ℂ)) *
          (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
            Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) * ρ 0 0 +
          ((Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (boltzmannPlus θ) : ℂ)) *
            ((Real.sqrt (1 - Real.exp (-γ * t)) : ℂ) * (Real.sqrt (1 - Real.exp (-γ * t)) : ℂ)) * ρ 1 1 +
          ((Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (boltzmannMinus θ) : ℂ)) *
            ((Real.sqrt (Real.exp (-γ * t)) : ℂ) * (Real.sqrt (Real.exp (-γ * t)) : ℂ)) *
            (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
              Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) * ρ 0 0
      · rw [h_bp_sq, h_bm_sq, h_ep_sq, h_1e_sq, hα_mul_αc, mul_one, mul_one]
        rw [eq_sub_of_add_eq' h_bsum]
        ring
      · ring
    · simp only [Matrix.add_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_two, mat2_00, mat2_01, mat2_10, mat2_11,
        star_mul, star_zero, mul_zero, zero_mul, add_zero, zero_add, h_star_real, hαc_star]
      trans (((Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (boltzmannPlus θ) : ℂ)) +
          ((Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (boltzmannMinus θ) : ℂ))) *
          (Real.sqrt (Real.exp (-γ * t)) : ℂ) *
          (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
            Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) * ρ 0 1
      · rw [h_bp_sq, h_bm_sq, h_bsum, one_mul, h_sqrt_ep_eq_ecoh, hα_sq]
      · ring
    · simp only [Matrix.add_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_two, mat2_00, mat2_01, mat2_10, mat2_11,
        star_mul, star_zero, mul_zero, zero_mul, add_zero, zero_add, h_star_real, hα_star]
      trans (((Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (boltzmannPlus θ) : ℂ)) +
          ((Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (boltzmannMinus θ) : ℂ))) *
          (Real.sqrt (Real.exp (-γ * t)) : ℂ) *
          (Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
            Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) * ρ 1 0
      · rw [h_bp_sq, h_bm_sq, h_bsum, one_mul, h_sqrt_ep_eq_ecoh, hαc_sq]
      · ring
    · simp only [Matrix.add_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_two, mat2_10, mat2_11, star_mul, star_zero,
        mul_zero, zero_mul, add_zero, zero_add, h_star_real, hαc_star]
      trans ((Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (boltzmannPlus θ) : ℂ)) *
          ((Real.sqrt (Real.exp (-γ * t)) : ℂ) * (Real.sqrt (Real.exp (-γ * t)) : ℂ)) *
          (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
            Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) * ρ 1 1 +
          ((Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (boltzmannMinus θ) : ℂ)) *
            (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
              Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) * ρ 1 1 +
          ((Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (boltzmannMinus θ) : ℂ)) *
            ((Real.sqrt (1 - Real.exp (-γ * t)) : ℂ) * (Real.sqrt (1 - Real.exp (-γ * t)) : ℂ)) * ρ 0 0
      · rw [h_bp_sq, h_bm_sq, h_ep_sq, h_1e_sq, hα_mul_αc, mul_one, mul_one]
        rw [eq_sub_of_add_eq h_bsum]
        ring
      · ring
  · rw [Fin.sum_univ_four]
    dsimp [thermalKraus]
    apply ext_mat2
    · simp only [Matrix.add_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_two, mat2_00, mat2_10, star_mul, star_zero,
        mul_zero, add_zero, zero_add, h_star_real, hα_star, Matrix.one_apply, ite_true]
      trans ((Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (boltzmannPlus θ) : ℂ)) *
          (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
            Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) +
          ((Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (boltzmannMinus θ) : ℂ)) *
            (((Real.sqrt (Real.exp (-γ * t)) : ℂ) * (Real.sqrt (Real.exp (-γ * t)) : ℂ)) *
              (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
                Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) +
              ((Real.sqrt (1 - Real.exp (-γ * t)) : ℂ) * (Real.sqrt (1 - Real.exp (-γ * t)) : ℂ)))
      · ring
      · rw [h_bp_sq, h_bm_sq, h_ep_sq, h_1e_sq, hα_mul_αc, mul_one, mul_one,
          add_sub_cancel, mul_one, h_bsum]
    · simp [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [Matrix.add_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_two, mat2_01, mat2_11, star_mul, star_zero,
        mul_zero, add_zero, zero_add, h_star_real, hαc_star, Matrix.one_apply, ite_true]
      trans ((Real.sqrt (boltzmannPlus θ) : ℂ) * (Real.sqrt (boltzmannPlus θ) : ℂ)) *
          (((Real.sqrt (Real.exp (-γ * t)) : ℂ) * (Real.sqrt (Real.exp (-γ * t)) : ℂ)) *
            (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
              Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ))) +
            ((Real.sqrt (1 - Real.exp (-γ * t)) : ℂ) * (Real.sqrt (1 - Real.exp (-γ * t)) : ℂ))) +
          ((Real.sqrt (boltzmannMinus θ) : ℂ) * (Real.sqrt (boltzmannMinus θ) : ℂ)) *
            (Complex.exp (-Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)) *
              Complex.exp (Complex.I * ((ω / 2 : ℝ) : ℂ) * (t : ℂ)))
      · ring
      · rw [h_bp_sq, h_bm_sq, h_ep_sq, h_1e_sq, hα_mul_αc, mul_one, mul_one,
          add_sub_cancel, mul_one, h_bsum]

-- theorem-class: bridge
/-- **Longitudinal Spin Readout Bridge**: For every unit-trace density matrix $\rho \in M_2(\mathbb{C})$,
the $\Gamma_1$-spin expectation along $T_t(\rho)$ equals `etaTraj γ θ (Tr(ρ Γ₁)).re t`. -/
@[rep_depth transport]
theorem spinReadout_thermalSemigroupC_eq_etaTraj
    (γ ω θ t : ℝ) (ρ : InfoGeometry.Algebra.FiniteSpin.Mat2C) (h_tr1 : Matrix.trace ρ = 1) :
    (Matrix.trace (thermalSemigroupC γ ω θ t ρ * pauliGamma1)).re =
      etaTraj γ θ ((Matrix.trace (ρ * pauliGamma1)).re) t := by
  have h_tr_entries : ρ 0 0 + ρ 1 1 = 1 := by
    rw [trace_fin2] at h_tr1
    exact h_tr1
  have h_read_rho : (Matrix.trace (ρ * pauliGamma1)).re = (ρ 0 0).re - (ρ 1 1).re := by
    dsimp [pauliGamma1]
    simp [InfoGeometry.Algebra.FiniteSpin.J_zero, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h_read_Tt : (Matrix.trace (thermalSemigroupC γ ω θ t ρ * pauliGamma1)).re =
      ((thermalSemigroupC γ ω θ t ρ) 0 0).re - ((thermalSemigroupC γ ω θ t ρ) 1 1).re := by
    dsimp [pauliGamma1]
    simp [InfoGeometry.Algebra.FiniteSpin.J_zero, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h_t00 : (thermalSemigroupC γ ω θ t ρ) 0 0 =
      (boltzmannPlus θ : ℂ) + (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ)) := by
    change (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
      (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) = _
    rw [h_tr_entries, mul_one]
  have h_t11 : (thermalSemigroupC γ ω θ t ρ) 1 1 =
      (boltzmannMinus θ : ℂ) + (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ)) := by
    change (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
      (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)) = _
    rw [h_tr_entries, mul_one]
  have h_diff : (boltzmannPlus θ : ℂ) - (boltzmannMinus θ : ℂ) = (meanSpin θ : ℂ) := by
    exact_mod_cast (boltzmann_sum_and_diff θ).2
  have h_sub_C : ((thermalSemigroupC γ ω θ t ρ) 0 0) - ((thermalSemigroupC γ ω θ t ρ) 1 1) =
      (meanSpin θ : ℂ) + (Real.exp (-γ * t) : ℂ) * ((ρ 0 0 - ρ 1 1) - (meanSpin θ : ℂ)) := by
    rw [h_t00, h_t11]
    linear_combination h_diff - (Real.exp (-γ * t) : ℂ) * h_diff
  have h_re := congr_arg Complex.re h_sub_C
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h_re
  rw [h_read_Tt, h_read_rho]
  exact h_re

-- theorem-class: conservation
/-- **Archetype $\mathcal{G}_2$ & $\mathcal{G}_3$: KMS Detailed Balance, Unique Gibbs Equilibrium & Exact Semigroup Law**. -/
@[rep_depth transport]
theorem kms_detailed_balance_unique_gibbs_and_semigroup_law
    (γ ω θ s t : ℝ) (hγ : γ ≠ 0) (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (h_tr1 : Matrix.trace ρ = 1) :
    -- 0. Operator-algebraic Witt CAR generator coincides with coordinate form:
    thermalLindbladianOp γ ω θ ρ = thermalLindbladianC γ ω θ ρ ∧
    -- 1. KMS detailed balance identity γ₊ e^{-θ} = γ₋ e^θ and rate sum γ₊ + γ₋ = γ:
    ratePlus γ θ * Real.exp (-θ) = rateMinus γ θ * Real.exp θ ∧
    ratePlus γ θ + rateMinus γ θ = γ ∧
    -- 2. Unique unit-trace stationary state L(ρ) = 0 ↔ ρ = ρ_Gibbs(θ):
    (thermalLindbladianC γ ω θ ρ = 0 ↔ ρ = gibbsDensityC θ) ∧
    -- 3. Exact Quantum Markov Semigroup properties (T_0 = id, Tr(T_t ρ) = Tr ρ, T_s ∘ T_t = T_{s+t}, T_t(ρ_Gibbs) = ρ_Gibbs):
    thermalSemigroupC γ ω θ 0 ρ = ρ ∧
    Matrix.trace (thermalSemigroupC γ ω θ t ρ) = Matrix.trace ρ ∧
    thermalSemigroupC γ ω θ s (thermalSemigroupC γ ω θ t ρ) =
      thermalSemigroupC γ ω θ (s + t) ρ ∧
    thermalSemigroupC γ ω θ t (gibbsDensityC θ) = gibbsDensityC θ := by
  have h_bp : boltzmannPlus θ = Real.exp θ / partitionZ θ := by
    dsimp [boltzmannPlus]; rw [one_add_meanSpin]; ring
  have h_bm : boltzmannMinus θ = Real.exp (-θ) / partitionZ θ := by
    dsimp [boltzmannMinus]; rw [one_sub_meanSpin]; ring
  have h_bsum : (boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ) = 1 := by
    exact_mod_cast (boltzmann_sum_and_diff θ).1
  refine ⟨thermalLindbladianOp_eq_thermalLindbladianC γ ω θ ρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [ratePlus, rateMinus]; rw [h_bp, h_bm]; ring
  · dsimp [ratePlus, rateMinus]
    calc γ * boltzmannPlus θ + γ * boltzmannMinus θ
      _ = γ * (boltzmannPlus θ + boltzmannMinus θ) := by ring
      _ = γ := by rw [(boltzmann_sum_and_diff θ).1, mul_one]
  · constructor
    · intro hL
      have h00 : -(rateMinus γ θ : ℂ) * ρ 0 0 + (ratePlus γ θ : ℂ) * ρ 1 1 = 0 :=
        congr_fun (congr_fun hL 0) 0
      have h01 : -((γ / 2 : ℝ) + Complex.I * ω) * ρ 0 1 = 0 :=
        congr_fun (congr_fun hL 0) 1
      have h10 : -((γ / 2 : ℝ) - Complex.I * ω) * ρ 1 0 = 0 :=
        congr_fun (congr_fun hL 1) 0
      have h_dec_p_ne : -(((γ / 2 : ℝ) : ℂ) + Complex.I * (ω : ℂ)) ≠ 0 := by
        intro h0
        have h_re := congr_arg Complex.re h0
        simp at h_re
        exact hγ h_re
      have h_dec_m_ne : -(((γ / 2 : ℝ) : ℂ) - Complex.I * (ω : ℂ)) ≠ 0 := by
        intro h0
        have h_re := congr_arg Complex.re h0
        simp at h_re
        exact hγ h_re
      have h_ρ01 : ρ 0 1 = 0 := (mul_eq_zero.mp h01).resolve_left h_dec_p_ne
      have h_ρ10 : ρ 1 0 = 0 := (mul_eq_zero.mp h10).resolve_left h_dec_m_ne
      rw [trace_fin2] at h_tr1
      have h_γC_ne : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
      have h_rate_sum : (ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ) = (γ : ℂ) := by
        dsimp [ratePlus, rateMinus]; push_cast
        calc (γ : ℂ) * boltzmannPlus θ + (γ : ℂ) * boltzmannMinus θ
          _ = (γ : ℂ) * (boltzmannPlus θ + boltzmannMinus θ) := by ring
          _ = (γ : ℂ) := by rw [h_bsum, mul_one]
      have h_ρ00 : ρ 0 0 = (boltzmannPlus θ : ℂ) := by
        have h_comb : (γ : ℂ) * ρ 0 0 = (γ : ℂ) * (boltzmannPlus θ : ℂ) := by
          calc (γ : ℂ) * ρ 0 0
            _ = ((ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ)) * ρ 0 0 +
                (-(rateMinus γ θ : ℂ) * ρ 0 0 + (ratePlus γ θ : ℂ) * ρ 1 1) := by
                rw [h_rate_sum, h00, add_zero]
            _ = (ratePlus γ θ : ℂ) * (ρ 0 0 + ρ 1 1) := by ring
            _ = (γ : ℂ) * (boltzmannPlus θ : ℂ) := by
                rw [h_tr1, mul_one]; dsimp [ratePlus]; push_cast; rfl
        exact mul_left_cancel₀ h_γC_ne h_comb
      have h_ρ11 : ρ 1 1 = (boltzmannMinus θ : ℂ) := by
        calc ρ 1 1 = (ρ 0 0 + ρ 1 1) - ρ 0 0 := by ring
          _ = 1 - (boltzmannPlus θ : ℂ) := by rw [h_tr1, h_ρ00]
          _ = ((boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ)) - (boltzmannPlus θ : ℂ) := by
              rw [h_bsum]
          _ = (boltzmannMinus θ : ℂ) := by ring
      apply ext_mat2
      · exact h_ρ00
      · exact h_ρ01
      · exact h_ρ10
      · exact h_ρ11
    · rintro rfl
      apply ext_mat2 <;>
        simp [thermalLindbladianC, gibbsDensityC, ratePlus, rateMinus] <;> ring
  · apply ext_mat2 <;> simp [thermalSemigroupC]
  · dsimp [thermalSemigroupC]
    simp only [trace_fin2, mat2_00, mat2_11]
    calc (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
         (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) +
         ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)))
      _ = ((boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ)) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) *
            ((ρ 0 0 + ρ 1 1) - ((boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ)) * (ρ 0 0 + ρ 1 1)) := by
          ring
      _ = ρ 0 0 + ρ 1 1 := by rw [h_bsum]; ring
  · have h_tr_step : (thermalSemigroupC γ ω θ t ρ) 0 0 + (thermalSemigroupC γ ω θ t ρ) 1 1 =
        ρ 0 0 + ρ 1 1 := by
      dsimp [thermalSemigroupC]
      calc (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
           (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) +
           ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
            (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)))
        _ = ((boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ)) * (ρ 0 0 + ρ 1 1) +
            (Real.exp (-γ * t) : ℂ) *
              ((ρ 0 0 + ρ 1 1) - ((boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ)) * (ρ 0 0 + ρ 1 1)) := by
            ring
        _ = ρ 0 0 + ρ 1 1 := by rw [h_bsum]; ring
    have h_exp1 : (Real.exp (-γ * s) : ℂ) * (Real.exp (-γ * t) : ℂ) =
        (Real.exp (-γ * (s + t)) : ℂ) := by
      norm_cast; rw [← Real.exp_add]; congr 1; ring
    have h_exp2 : (Real.exp (-(γ / 2) * s) : ℂ) * (Real.exp (-(γ / 2) * t) : ℂ) =
        (Real.exp (-(γ / 2) * (s + t)) : ℂ) := by
      norm_cast; rw [← Real.exp_add]; congr 1; ring
    have h_ph_p : Complex.exp (-Complex.I * (ω : ℂ) * (s : ℂ)) *
                  Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ)) =
                  Complex.exp (-Complex.I * (ω : ℂ) * ((s + t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have h_ph_m : Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ)) *
                  Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) =
                  Complex.exp (Complex.I * (ω : ℂ) * ((s + t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    apply ext_mat2
    · calc (thermalSemigroupC γ ω θ s (thermalSemigroupC γ ω θ t ρ)) 0 0
        _ = (boltzmannPlus θ : ℂ) *
              ((thermalSemigroupC γ ω θ t ρ) 0 0 + (thermalSemigroupC γ ω θ t ρ) 1 1) +
            (Real.exp (-γ * s) : ℂ) * ((thermalSemigroupC γ ω θ t ρ) 0 0 -
              (boltzmannPlus θ : ℂ) *
                ((thermalSemigroupC γ ω θ t ρ) 0 0 + (thermalSemigroupC γ ω θ t ρ) 1 1)) := rfl
        _ = (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
            (Real.exp (-γ * s) : ℂ) * ((boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
              (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) -
              (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := by
            rw [h_tr_step]; rfl
        _ = (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
            ((Real.exp (-γ * s) : ℂ) * (Real.exp (-γ * t) : ℂ)) *
              (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := by ring
        _ = (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
            (Real.exp (-γ * (s + t)) : ℂ) *
              (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := by rw [h_exp1]
    · calc (thermalSemigroupC γ ω θ s (thermalSemigroupC γ ω θ t ρ)) 0 1
        _ = (Real.exp (-(γ / 2) * s) : ℂ) * Complex.exp (-Complex.I * ω * s) *
            ((Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (-Complex.I * ω * t) * ρ 0 1) := rfl
        _ = ((Real.exp (-(γ / 2) * s) : ℂ) * (Real.exp (-(γ / 2) * t) : ℂ)) *
            (Complex.exp (-Complex.I * ω * s) * Complex.exp (-Complex.I * ω * t)) * ρ 0 1 := by ring
        _ = (Real.exp (-(γ / 2) * (s + t)) : ℂ) *
            Complex.exp (-Complex.I * ω * ((s + t : ℝ) : ℂ)) * ρ 0 1 := by rw [h_exp2, h_ph_p]
    · calc (thermalSemigroupC γ ω θ s (thermalSemigroupC γ ω θ t ρ)) 1 0
        _ = (Real.exp (-(γ / 2) * s) : ℂ) * Complex.exp (Complex.I * ω * s) *
            ((Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (Complex.I * ω * t) * ρ 1 0) := rfl
        _ = ((Real.exp (-(γ / 2) * s) : ℂ) * (Real.exp (-(γ / 2) * t) : ℂ)) *
            (Complex.exp (Complex.I * ω * s) * Complex.exp (Complex.I * ω * t)) * ρ 1 0 := by ring
        _ = (Real.exp (-(γ / 2) * (s + t)) : ℂ) *
            Complex.exp (Complex.I * ω * ((s + t : ℝ) : ℂ)) * ρ 1 0 := by rw [h_exp2, h_ph_m]
    · calc (thermalSemigroupC γ ω θ s (thermalSemigroupC γ ω θ t ρ)) 1 1
        _ = (boltzmannMinus θ : ℂ) *
              ((thermalSemigroupC γ ω θ t ρ) 0 0 + (thermalSemigroupC γ ω θ t ρ) 1 1) +
            (Real.exp (-γ * s) : ℂ) * ((thermalSemigroupC γ ω θ t ρ) 1 1 -
              (boltzmannMinus θ : ℂ) *
                ((thermalSemigroupC γ ω θ t ρ) 0 0 + (thermalSemigroupC γ ω θ t ρ) 1 1)) := rfl
        _ = (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
            (Real.exp (-γ * s) : ℂ) * ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
              (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)) -
              (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := by
            rw [h_tr_step]; rfl
        _ = (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
            ((Real.exp (-γ * s) : ℂ) * (Real.exp (-γ * t) : ℂ)) *
              (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := by ring
        _ = (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
            (Real.exp (-γ * (s + t)) : ℂ) *
              (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := by rw [h_exp1]
  · apply ext_mat2 <;> simp [thermalSemigroupC, gibbsDensityC, h_bsum]

-- theorem-class: capstone
/-- **Archetype $\mathcal{G}_7$: Master Thermodynamic Synthesis — Affine $m$-Geodesic Spin Relaxation,
Spohn's Entropy Production Law, Asymptotic Spin Limit & Free-Energy Convergence**. -/
@[rep_depth thermo, capstone]
theorem master_spohn_entropy_production_and_gibbs_relaxation
    {γ θ η₀ t : ℝ} (hγ : 0 < γ) (ht : 0 ≤ t) (h0_lo : -1 < η₀) (h0_hi : η₀ < 1) :
    let η_t := etaTraj γ θ η₀ t
    let η_eq := meanSpin θ
    -- 1. Affine m-geodesic domain invariance η(t) ∈ (-1, 1):
    (-1 < η_t ∧ η_t < 1) ∧
    -- 2. Exact relaxation ODE d/dt η(t) = -γ (η(t) - η(θ)):
    HasDerivAt (etaTraj γ θ η₀) (-γ * (η_t - η_eq)) t ∧
    -- 3. Spohn's Exact Quantum Entropy Production Identity:
    HasDerivAt (fun s => bregmanPhi (etaTraj γ θ η₀ s) η_eq)
      (-γ * (bregmanPhi η_t η_eq + bregmanPhi η_eq η_t)) t ∧
    -- 4. Non-positiveness of entropy production (Lyapunov decay d/dt D_φ ≤ 0):
    -γ * (bregmanPhi η_t η_eq + bregmanPhi η_eq η_t) ≤ 0 ∧
    -- 5. Asymptotic spin relaxation limit lim_{s → +∞} η(s) = η(θ):
    Tendsto (etaTraj γ θ η₀) atTop (𝓝 η_eq) ∧
    -- 6. Asymptotic relative free-energy limit lim_{s → +∞} D_φ(η(s) ‖ η(θ)) = 0:
    Tendsto (fun s => bregmanPhi (etaTraj γ θ η₀ s) η_eq) atTop (𝓝 0) := by
  intro η_t η_eq
  rcases meanSpin_mem_Ioo θ with ⟨heq_lo, heq_hi⟩
  rcases dually_flat_legendre_reciprocity_and_metric_inversion with
    ⟨h_th_mean, _, _, h_deriv_phi, _, _⟩
  rcases bregman_umegaki_positivity_and_pythagorean_theorem with
    ⟨_, h_breg_pos, h_jeffreys, _⟩
  have hexp_pos : 0 < Real.exp (-γ * t) := Real.exp_pos (-γ * t)
  have hexp_le1 : Real.exp (-γ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h_conv : η_t = (1 - Real.exp (-γ * t)) * η_eq + Real.exp (-γ * t) * η₀ := by
    dsimp [η_t, η_eq, etaTraj]; ring
  have h_in_Ioo : -1 < η_t ∧ η_t < 1 := by
    rw [h_conv]
    constructor <;> nlinarith
  have hd_eta : HasDerivAt (etaTraj γ θ η₀) (-γ * (η_t - η_eq)) t := by
    have hd_lin : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t :=
      (((hasDerivAt_const t (-γ)).fun_mul (hasDerivAt_id t))).congr_deriv (by ring)
    have hd_exp : HasDerivAt (fun s : ℝ => Real.exp (-γ * s)) (Real.exp (-γ * t) * (-γ)) t :=
      (Real.hasDerivAt_exp (-γ * t)).comp t hd_lin
    have hd_mul := (hasDerivAt_const t η_eq).fun_add (hd_exp.mul_const (η₀ - η_eq))
    have h_alg : 0 + Real.exp (-γ * t) * (-γ) * (η₀ - η_eq) = -γ * (η_t - η_eq) := by
      dsimp [η_t, η_eq, etaTraj]; ring
    unfold etaTraj
    exact hd_mul.congr_deriv h_alg
  have hd_breg_at : ∀ u : ℝ, -1 < u → u < 1 →
      HasDerivAt (fun v => bregmanPhi v η_eq) (canonicalTheta u - θ) u := by
    intro u hu_lo hu_hi
    have hd_phi := h_deriv_phi u hu_lo hu_hi
    have hd_sub1 := hd_phi.fun_sub (hasDerivAt_const u (negEntropyPhi η_eq))
    have hd_lin2 : HasDerivAt (fun v : ℝ => canonicalTheta η_eq * (v - η_eq))
        (canonicalTheta η_eq) u :=
      (((hasDerivAt_id u).fun_sub (hasDerivAt_const u η_eq)).const_mul
        (canonicalTheta η_eq)).congr_deriv (by ring)
    have hd_tot := hd_sub1.fun_sub hd_lin2
    have h_th_eq : canonicalTheta η_eq = θ := h_th_mean θ
    unfold bregmanPhi
    simp only [h_th_eq] at hd_tot ⊢
    exact hd_tot.congr_deriv (by ring)
  have hd_breg_u := hd_breg_at η_t h_in_Ioo.1 h_in_Ioo.2
  have hd_spohn := hd_breg_u.comp t hd_eta
  have h_spohn_eq : (canonicalTheta η_t - θ) * (-γ * (η_t - η_eq)) =
      -γ * (bregmanPhi η_t η_eq + bregmanPhi η_eq η_t) := by
    have hj := h_jeffreys η_t η_eq
    have h_th_eq : canonicalTheta η_eq = θ := h_th_mean θ
    rw [h_th_eq] at hj
    rw [hj]; ring
  rw [h_spohn_eq] at hd_spohn
  have h_prod_nonpos : -γ * (bregmanPhi η_t η_eq + bregmanPhi η_eq η_t) ≤ 0 := by
    have hb1 := (h_breg_pos η_t η_eq h_in_Ioo.1 h_in_Ioo.2 heq_lo heq_hi).1
    have hb2 := (h_breg_pos η_eq η_t heq_lo heq_hi h_in_Ioo.1 h_in_Ioo.2).1
    nlinarith
  have h_tendsto_pos : Tendsto (fun s : ℝ => γ * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hγ).mpr tendsto_id
  have h_tendsto_atBot : Tendsto (fun s : ℝ => -γ * s) atTop atBot := by
    simpa [neg_mul] using tendsto_neg_atBot_iff.mpr h_tendsto_pos
  have h_tendsto_exp : Tendsto (fun s : ℝ => Real.exp (-γ * s)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h_tendsto_atBot
  have h_tendsto_mul : Tendsto (fun s : ℝ => Real.exp (-γ * s) * (η₀ - η_eq)) atTop (𝓝 0) := by
    have h0 := h_tendsto_exp.mul_const (η₀ - η_eq)
    rwa [zero_mul] at h0
  have h_tendsto_eta : Tendsto (etaTraj γ θ η₀) atTop (𝓝 η_eq) := by
    unfold etaTraj
    have h1 := (tendsto_const_nhds (x := η_eq)).add h_tendsto_mul
    rwa [add_zero] at h1
  have h_cont_breg : ContinuousAt (fun u => bregmanPhi u η_eq) η_eq :=
    (hd_breg_at η_eq heq_lo heq_hi).continuousAt
  have h_breg_zero : bregmanPhi η_eq η_eq = 0 :=
    ((h_breg_pos η_eq η_eq heq_lo heq_hi heq_lo heq_hi).2).2 rfl
  have h_tendsto_breg : Tendsto (fun s => bregmanPhi (etaTraj γ θ η₀ s) η_eq) atTop (𝓝 0) := by
    rw [← h_breg_zero]
    exact h_cont_breg.tendsto.comp h_tendsto_eta
  exact ⟨h_in_Ioo, hd_eta, hd_spohn, h_prod_nonpos, h_tendsto_eta, h_tendsto_breg⟩

end ArchetypeG2_G3_G7_ThermalGKSLSemigroupAndSpohnSynthesis

/-!
## Typed Archetype Registrations (`InfoGeometry.MetaCompiler.TypedArchetype`)
-/

section TypedArchetypeRegistrations

open InfoGeometry.MetaCompiler

/-- Typed archetype $\mathcal{G}_1$: Algebraic GKSL $\star$-preservation, unitality, and carré du champ. -/
def gkslCarreDuChampArchetype (B : Type) [Ring B] [StarRing B] : TypedArchetype Unit .proved where
  name := `gkslCarreDuChampArchetype
  phase := 1
  claim := fun _ =>
    ∀ {J : B}, star J = -J → ∀ L ρ A : B,
      star (gkslGen2 J L ρ) = gkslGen2 J L (star ρ) ∧
      heisenbergDissipator2 L (1 : B) = 0 ∧
      heisenbergDissipator2 L (star A * A) -
        (heisenbergDissipator2 L (star A) * A + star A * heisenbergDissipator2 L A) =
        2 * (star ⁅L, A⁆ * ⁅L, A⁆)
  evidence := fun _ _ hJ L ρ A => algebraic_gksl_star_unital_and_carre_du_champ hJ L ρ A

/-- Concrete `Mat2C` instance of `gkslCarreDuChampArchetype` audited at compile time. -/
def gkslCarreDuChampMat2CArchetype : TypedArchetype Unit .proved :=
  gkslCarreDuChampArchetype InfoGeometry.Algebra.FiniteSpin.Mat2C

#register_archetype gkslCarreDuChampMat2CArchetype
#audit_archetype gkslCarreDuChampMat2CArchetype

/-- Typed archetype $\mathcal{G}_2$–$\mathcal{G}_3$: Witt CAR detailed balance, Kraus CPTP sum & semigroup law. -/
def wittCarThermalSemigroupArchetype : TypedArchetype Unit .proved where
  name := `wittCarThermalSemigroupArchetype
  phase := 2
  claim := fun _ =>
    ∀ (γ ω θ s t : ℝ), γ ≠ 0 → 0 ≤ γ → 0 ≤ t →
      ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, Matrix.trace ρ = 1 →
        (thermalLindbladianOp γ ω θ ρ = thermalLindbladianC γ ω θ ρ ∧
         ratePlus γ θ * Real.exp (-θ) = rateMinus γ θ * Real.exp θ ∧
         ratePlus γ θ + rateMinus γ θ = γ ∧
         (thermalLindbladianC γ ω θ ρ = 0 ↔ ρ = gibbsDensityC θ) ∧
         thermalSemigroupC γ ω θ 0 ρ = ρ ∧
         Matrix.trace (thermalSemigroupC γ ω θ t ρ) = Matrix.trace ρ ∧
         thermalSemigroupC γ ω θ s (thermalSemigroupC γ ω θ t ρ) =
           thermalSemigroupC γ ω θ (s + t) ρ ∧
         thermalSemigroupC γ ω θ t (gibbsDensityC θ) = gibbsDensityC θ) ∧
        (thermalSemigroupC γ ω θ t ρ =
          ∑ k : Fin 4, thermalKraus γ ω θ t k * ρ * star (thermalKraus γ ω θ t k) ∧
         ∑ k : Fin 4, star (thermalKraus γ ω θ t k) * thermalKraus γ ω θ t k = 1)
  evidence := fun _ γ ω θ s t hγ hγ0 ht0 ρ htr =>
    ⟨kms_detailed_balance_unique_gibbs_and_semigroup_law γ ω θ s t hγ ρ htr,
     ⟨(thermalSemigroupC_kraus_sum_and_unital hγ0 ht0).1 ρ,
      (thermalSemigroupC_kraus_sum_and_unital hγ0 ht0).2⟩⟩

#register_archetype wittCarThermalSemigroupArchetype
#audit_archetype wittCarThermalSemigroupArchetype

/-- Typed archetype $\mathcal{G}_4$–$\mathcal{G}_6$: Spin cumulants, Legendre–BKM inversion & Bregman Pythagoras. -/
def duallyFlatSpinCumulantArchetype : TypedArchetype Unit .proved where
  name := `duallyFlatSpinCumulantArchetype
  phase := 3
  claim := fun _ =>
    (∀ θ : ℝ,
      HasDerivAt cumulantPsi (meanSpin θ) θ ∧
      HasDerivAt meanSpin (varSpin θ) θ ∧
      HasDerivAt varSpin (skewSpin θ) θ) ∧
    ((∀ θ : ℝ, canonicalTheta (meanSpin θ) = θ) ∧
     (∀ η : ℝ, -1 < η → η < 1 → meanSpin (canonicalTheta η) = η) ∧
     (∀ θ : ℝ, cumulantPsi θ + negEntropyPhi (meanSpin θ) = θ * meanSpin θ) ∧
     (∀ η : ℝ, -1 < η → η < 1 → HasDerivAt negEntropyPhi (canonicalTheta η) η) ∧
     (∀ η : ℝ, -1 < η → η < 1 → HasDerivAt canonicalTheta (1 / (1 - η ^ 2)) η) ∧
     (∀ θ : ℝ, varSpin θ * (1 / (1 - (meanSpin θ) ^ 2)) = 1)) ∧
    ((∀ θ₁ θ₂ : ℝ, bregmanPsi θ₂ θ₁ = bregmanPhi (meanSpin θ₁) (meanSpin θ₂) ∧
       bregmanPhi (meanSpin θ₁) (meanSpin θ₂) =
         cumulantPsi θ₂ + negEntropyPhi (meanSpin θ₁) - θ₂ * meanSpin θ₁) ∧
     (∀ η₁ η₂ : ℝ, -1 < η₁ → η₁ < 1 → -1 < η₂ → η₂ < 1 →
       0 ≤ bregmanPhi η₁ η₂ ∧ (bregmanPhi η₁ η₂ = 0 ↔ η₁ = η₂)) ∧
     (∀ η₁ η₂ : ℝ, bregmanPhi η₁ η₂ + bregmanPhi η₂ η₁ =
       (canonicalTheta η₁ - canonicalTheta η₂) * (η₁ - η₂)) ∧
     (∀ η₁ η₂ η₃ : ℝ,
       bregmanPhi η₁ η₃ = bregmanPhi η₁ η₂ + bregmanPhi η₂ η₃ +
         (η₁ - η₂) * (canonicalTheta η₂ - canonicalTheta η₃)))
  evidence := fun _ =>
    ⟨spin_cumulant_hierarchy_derivatives,
     dually_flat_legendre_reciprocity_and_metric_inversion,
     bregman_umegaki_positivity_and_pythagorean_theorem⟩

#register_archetype duallyFlatSpinCumulantArchetype
#audit_archetype duallyFlatSpinCumulantArchetype

/-- Typed archetype $\mathcal{G}_7$: Master thermodynamic Spohn entropy production & Gibbs relaxation synthesis. -/
def masterSpohnGibbsSynthesisArchetype : TypedArchetype Unit .proved where
  name := `masterSpohnGibbsSynthesisArchetype
  phase := 4
  claim := fun _ =>
    ∀ {γ θ η₀ t : ℝ}, 0 < γ → 0 ≤ t → -1 < η₀ → η₀ < 1 →
      let η_t := etaTraj γ θ η₀ t
      let η_eq := meanSpin θ
      (-1 < η_t ∧ η_t < 1) ∧
      HasDerivAt (etaTraj γ θ η₀) (-γ * (η_t - η_eq)) t ∧
      HasDerivAt (fun s => bregmanPhi (etaTraj γ θ η₀ s) η_eq)
        (-γ * (bregmanPhi η_t η_eq + bregmanPhi η_eq η_t)) t ∧
      -γ * (bregmanPhi η_t η_eq + bregmanPhi η_eq η_t) ≤ 0 ∧
      Tendsto (etaTraj γ θ η₀) atTop (𝓝 η_eq) ∧
      Tendsto (fun s => bregmanPhi (etaTraj γ θ η₀ s) η_eq) atTop (𝓝 0)
  evidence := fun _ {_ _ _ _} hγ ht h0_lo h0_hi =>
    master_spohn_entropy_production_and_gibbs_relaxation hγ ht h0_lo h0_hi

#register_archetype masterSpohnGibbsSynthesisArchetype
#audit_archetype masterSpohnGibbsSynthesisArchetype

end TypedArchetypeRegistrations

end InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
